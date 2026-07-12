// Tests for the NATIVE-HASH single-matrix FRI verifier flow: the native-Go
// reference (fri_verify_native_ref.go) and the circuit gadget
// (fri_verify_native.go), cross-checked against each other via the gnark test
// engine — the same discipline as fri_verify_test.go, with the two wrap swaps
// (MultiField transcript, native BN254 Merkle) in place. All tests run by
// DEFAULT `go test` (no build tags, no skips).
//
// The VALID fixture is built by DRIVING the reference MultiField challenger
// exactly as the flow reads it: commit each folded codeword to a NATIVE BN254
// Merkle tree, observe its root as a native digest, sample the beta
// in-transcript, fold; grind a real query PoW witness for the live transcript;
// sample each query index from that same challenger and read off its openings.
//
// THE MEASUREMENT (TestWrapNativeHashConstraintMeasurement) is the payoff of
// this lane: compile VerifyFriNative AND the emulated VerifyFri at the
// ir2_leaf_wrap_config shape (19 queries, ~the real FRI depth) and report the
// constraint swing plus the hashing-vs-fold-residual breakdown — the empirical
// validation of the ~1-6M native-path premise in
// docs/deos/WRAP-NATIVE-HASH-DECISION.md.
package friverifier

import (
	"math/big"
	"math/rand"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// ---------------------------------------------------------------------------
// Fixture builder: drive the reference MultiField challenger exactly as
// verifyFriNativeRef reads it, producing a VALID native-hash FRI proof.
// ---------------------------------------------------------------------------

func buildValidFriNativeProof(R int, cfg friConfigRef, numQueries int, prefix []uint32, seed int64) *friNativeProofRef {
	rng := rand.New(rand.NewSource(seed))
	lane := func() uint32 { return uint32(rng.Uint64() % BabyBearP) }
	ext := func() bbExtRef { return bbExtRef{lane(), lane(), lane(), lane()} }

	// Initial codeword f0 (size 2^R).
	N := 1 << R
	f0 := make([]bbExtRef, N)
	for i := range f0 {
		f0[i] = ext()
	}

	c := newMultiFieldChallengerRef()
	c.observeBabyBearSlice(prefix)

	// Commit phase driven by the transcript: NATIVE-commit f_r, observe the
	// BN254 root digest, sample beta, fold. The fold is the same BabyBear
	// arithmetic as the emulated fixture (foldVectorRef) — only the hash moved.
	fs := [][]bbExtRef{f0}
	roots := make([]fr.Element, R)
	layersByRound := make([][][]fr.Element, R)
	for r := 0; r < R; r++ {
		root, layers := merkleCommitBn254Ref(fs[r])
		roots[r] = root
		layersByRound[r] = layers
		c.observeBn254Digest([]fr.Element{root})
		if !c.checkWitness(cfg.CommitPowBits, 0) { // 0 bits: no-op, no advance
			panic("commit PoW check failed for 0 bits")
		}
		beta := c.sampleExt()
		fs = append(fs, foldVectorRef(fs[r], beta, R, r))
	}
	finalPoly := []bbExtRef{fs[R][0]} // log_final_poly_len == 0: one constant

	// Observe the final poly + arity schedule (same order the verifier reads).
	for _, coeff := range finalPoly {
		c.observeBabyBearSlice(coeff[:])
	}
	for r := 0; r < R; r++ {
		c.observeBabyBear(1)
	}

	// Grind a REAL query PoW witness for the live MultiField transcript, then
	// advance the challenger through the check exactly as the verifier will.
	powWitness := mfGrindRef(c, cfg.QueryPowBits)
	if !c.checkWitness(cfg.QueryPowBits, powWitness) {
		panic("mfGrindRef produced a witness its own check rejects")
	}

	logGlobalMaxHeight := R + cfg.LogBlowup + cfg.LogFinalPolyLen
	queries := make([]friNativeQueryOpeningRef, numQueries)
	for q := 0; q < numQueries; q++ {
		index := uint(c.sampleBits(logGlobalMaxHeight + cfg.ExtraQueryIndexBits))
		domainIndex := index >> uint(cfg.ExtraQueryIndexBits)

		var op friNativeQueryOpeningRef
		op.InitialEval = fs[0][domainIndex]
		for r := 0; r < R; r++ {
			parent := domainIndex >> uint(r+1)
			op.MerkleProofs = append(op.MerkleProofs, merkleOpenBn254Ref(layersByRound[r], int(parent)))
			bR := (domainIndex >> uint(r)) & 1
			op.Siblings = append(op.Siblings, fs[r][2*parent+(1-bR)])
		}
		queries[q] = op
	}

	return &friNativeProofRef{R: R, CommitRoots: roots, FinalPoly: finalPoly,
		PowWitness: powWitness, Queries: queries}
}

// freshMfRefChallenger returns a MultiField reference challenger positioned at
// the commit phase (prefix observed as BabyBear values).
func freshMfRefChallenger(prefix []uint32) *multiFieldChallengerRef {
	c := newMultiFieldChallengerRef()
	c.observeBabyBearSlice(prefix)
	return c
}

// ---------------------------------------------------------------------------
// gnark wrapper circuit for the native-hash flow.
// ---------------------------------------------------------------------------

type friVerifyNativeCircuit struct {
	// Structural (unexported so the gnark schema walker ignores them).
	r    int
	cfg  FriConfig
	swap bool

	Prefix      []frontend.Variable
	CommitRoots []frontend.Variable
	FinalPoly   []BBExt
	PowWitness  frontend.Variable
	Queries     []FriNativeQueryOpening
}

func (c *friVerifyNativeCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallenger(bb)
	ch.ObserveBabyBearSlice(c.Prefix)
	verifyFriNativeImpl(bb, c.cfg, c.r, c.CommitRoots, c.FinalPoly, c.PowWitness,
		c.Queries, ch, c.swap)
	return nil
}

// allocFriVerifyNativeCircuit allocates a circuit shell with the exact slice
// sizes of the proof (same shape for compiled template and assignment).
func allocFriVerifyNativeCircuit(R, prefixLen, numQueries int, cfg FriConfig, swap bool) *friVerifyNativeCircuit {
	c := &friVerifyNativeCircuit{r: R, cfg: cfg, swap: swap}
	c.Prefix = make([]frontend.Variable, prefixLen)
	c.CommitRoots = make([]frontend.Variable, R)
	c.FinalPoly = make([]BBExt, 1<<cfg.LogFinalPolyLen)
	c.Queries = make([]FriNativeQueryOpening, numQueries)
	for q := range c.Queries {
		c.Queries[q].Siblings = make([]BBExt, R)
		c.Queries[q].MerkleProofs = make([][]frontend.Variable, R)
		for r := 0; r < R; r++ {
			c.Queries[q].MerkleProofs[r] = make([]frontend.Variable, R-r-1)
		}
	}
	return c
}

func frToBig(e fr.Element) *big.Int { return e.BigInt(new(big.Int)) }

// assignFriVerifyNativeCircuit fills an allocated circuit with a proof + prefix.
func assignFriVerifyNativeCircuit(p *friNativeProofRef, prefix []uint32, cfg FriConfig, swap bool) *friVerifyNativeCircuit {
	c := allocFriVerifyNativeCircuit(p.R, len(prefix), len(p.Queries), cfg, swap)
	for i, v := range prefix {
		c.Prefix[i] = v
	}
	for r := 0; r < p.R; r++ {
		c.CommitRoots[r] = frToBig(p.CommitRoots[r])
	}
	for i := range p.FinalPoly {
		c.FinalPoly[i] = extToVars(p.FinalPoly[i])
	}
	c.PowWitness = p.PowWitness
	for q := range p.Queries {
		op := p.Queries[q]
		c.Queries[q].InitialEval = extToVars(op.InitialEval)
		for r := 0; r < p.R; r++ {
			c.Queries[q].Siblings[r] = extToVars(op.Siblings[r])
			for l := range op.MerkleProofs[r] {
				c.Queries[q].MerkleProofs[r][l] = frToBig(op.MerkleProofs[r][l])
			}
		}
	}
	return c
}

// ---------------------------------------------------------------------------
// ACCEPT: a valid native-hash proof verifies in BOTH the ref AND the gadget.
// ---------------------------------------------------------------------------

func TestFriVerifyNativeAcceptsRefAndGadget(t *testing.T) {
	const R = 3
	const numQueries = 3
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()

	for iter := 0; iter < 3; iter++ {
		p := buildValidFriNativeProof(R, cfgRef, numQueries, prefix, 700+int64(iter))

		if !verifyFriNativeRef(freshMfRefChallenger(prefix), cfgRef, p) {
			t.Fatalf("iter %d: valid native-hash proof REJECTED by reference", iter)
		}
		tmpl := allocFriVerifyNativeCircuit(R, len(prefix), numQueries, cfg, false)
		if err := test.IsSolved(tmpl, assignFriVerifyNativeCircuit(p, prefix, cfg, false), field); err != nil {
			t.Fatalf("iter %d: valid native-hash proof rejected by gadget: %v", iter, err)
		}
	}
}

// ---------------------------------------------------------------------------
// TRANSCRIPT-ORDER CANARY: a VALID proof fed through the observe/sample-SWAPPED
// commit-phase order must FAIL in both the ref and the gadget — the MultiField
// transcript binds the observe-root-THEN-sample-beta interleave exactly as the
// emulated one does.
// ---------------------------------------------------------------------------

func TestFriVerifyNativeWrongBetaOrderCanary(t *testing.T) {
	const R = 3
	const numQueries = 2
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()

	p := buildValidFriNativeProof(R, cfgRef, numQueries, prefix, 8484)

	// Guard (non-vacuity): the correct order ACCEPTS this proof, ref and gadget.
	if !verifyFriNativeRefImpl(freshMfRefChallenger(prefix), cfgRef, p, false) {
		t.Fatal("guard: correct-order reference rejected a valid proof")
	}
	tmplOK := allocFriVerifyNativeCircuit(R, len(prefix), numQueries, cfg, false)
	if err := test.IsSolved(tmplOK, assignFriVerifyNativeCircuit(p, prefix, cfg, false), field); err != nil {
		t.Fatalf("guard: correct-order gadget rejected a valid proof: %v", err)
	}

	// Canary: the swapped order REJECTS the same proof, ref and gadget.
	if verifyFriNativeRefImpl(freshMfRefChallenger(prefix), cfgRef, p, true) {
		t.Fatal("swapped-order reference ACCEPTED a valid proof — interleave not load-bearing")
	}
	tmplSwap := allocFriVerifyNativeCircuit(R, len(prefix), numQueries, cfg, true)
	if err := test.IsSolved(tmplSwap, assignFriVerifyNativeCircuit(p, prefix, cfg, true), field); err == nil {
		t.Fatal("swapped-order gadget ACCEPTED a valid proof — interleave not load-bearing")
	}
}

// ---------------------------------------------------------------------------
// REJECT (ref-guarded, non-vacuous): each single tamper must FAIL in both the
// reference and the gadget.
// ---------------------------------------------------------------------------

func TestFriVerifyNativeRejectsTampers(t *testing.T) {
	const R = 3
	const numQueries = 2
	const seed = 1717
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()

	one := fr.One()

	cases := []struct {
		name   string
		tamper func(p *friNativeProofRef)
	}{
		{
			// Bad grinding witness: the query PoW check fails (fail-closed).
			name: "bad-grinding-witness",
			tamper: func(p *friNativeProofRef) {
				p.PowWitness = p.PowWitness ^ 1 // stays canonical (< p, p odd)
			},
		},
		{
			// Tampered leaf data: a corrupted sibling eval breaks the round-0
			// NATIVE Merkle check for that query (the packed-leaf binding).
			name: "tampered-leaf",
			tamper: func(p *friNativeProofRef) {
				p.Queries[0].Siblings[0][0] = bbAddRef(p.Queries[0].Siblings[0][0], 1)
			},
		},
		{
			// Tampered NATIVE commit root: diverges the sampled beta AND the
			// Merkle check against that root.
			name: "tampered-commit-root",
			tamper: func(p *friNativeProofRef) {
				p.CommitRoots[0].Add(&p.CommitRoots[0], &one)
			},
		},
		{
			// Tampered native path node: the opening no longer reconstructs
			// the committed root.
			name: "tampered-merkle-path",
			tamper: func(p *friNativeProofRef) {
				p.Queries[0].MerkleProofs[0][0].Add(&p.Queries[0].MerkleProofs[0][0], &one)
			},
		},
		{
			// Wrong final polynomial: shifts the transcript (it is observed)
			// and the final-eval target.
			name: "wrong-final-poly",
			tamper: func(p *friNativeProofRef) {
				p.FinalPoly[0][0] = bbAddRef(p.FinalPoly[0][0], 1)
			},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// Ref-guard: the untampered proof passes.
			base := buildValidFriNativeProof(R, cfgRef, numQueries, prefix, seed)
			if !verifyFriNativeRef(freshMfRefChallenger(prefix), cfgRef, base) {
				t.Fatalf("%s: base proof rejected — guard broken", tc.name)
			}
			// Tamper and require reference rejection (non-vacuous).
			p := buildValidFriNativeProof(R, cfgRef, numQueries, prefix, seed)
			tc.tamper(p)
			if verifyFriNativeRef(freshMfRefChallenger(prefix), cfgRef, p) {
				t.Fatalf("%s: reference ACCEPTED a tampered proof (vacuous reject)", tc.name)
			}
			// The gadget must also reject.
			tmpl := allocFriVerifyNativeCircuit(R, len(prefix), numQueries, cfg, false)
			if err := test.IsSolved(tmpl, assignFriVerifyNativeCircuit(p, prefix, cfg, false), field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED a tampered proof", tc.name)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Differential: gadget and reference agree (accept/reject) over random valid
// proofs and single-lane tampers.
// ---------------------------------------------------------------------------

func TestFriVerifyNativeDifferentialRefVsGadget(t *testing.T) {
	const R = 3
	const numQueries = 2
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(2077))
	one := fr.One()

	agree := func(p *friNativeProofRef, label string) {
		refOK := verifyFriNativeRef(freshMfRefChallenger(prefix), cfgRef, p)
		tmpl := allocFriVerifyNativeCircuit(R, len(prefix), numQueries, cfg, false)
		err := test.IsSolved(tmpl, assignFriVerifyNativeCircuit(p, prefix, cfg, false), field)
		gadgetOK := err == nil
		if refOK != gadgetOK {
			t.Fatalf("%s: ref=%v gadget=%v (disagree); gadget err=%v", label, refOK, gadgetOK, err)
		}
	}

	for iter := 0; iter < 4; iter++ {
		p := buildValidFriNativeProof(R, cfgRef, numQueries, prefix, int64(5000+iter))
		agree(p, "valid")

		bad := buildValidFriNativeProof(R, cfgRef, numQueries, prefix, int64(5000+iter))
		switch rng.Intn(4) {
		case 0:
			bad.PowWitness = bad.PowWitness ^ (1 + uint32(rng.Intn(7)))
			if bad.PowWitness >= uint32(BabyBearP) {
				bad.PowWitness %= uint32(BabyBearP)
			}
		case 1:
			r := rng.Intn(R)
			bad.Queries[0].Siblings[r][rng.Intn(4)] = bbAddRef(bad.Queries[0].Siblings[r][rng.Intn(4)], 1)
		case 2:
			r := rng.Intn(R)
			bad.CommitRoots[r].Add(&bad.CommitRoots[r], &one)
		case 3:
			bad.FinalPoly[0][rng.Intn(4)] = bbAddRef(bad.FinalPoly[0][rng.Intn(4)], 1)
		}
		agree(bad, "tampered")
	}
}

// ---------------------------------------------------------------------------
// THE MEASUREMENT — the payoff of this lane.
//
// Compile three circuits at the ir2_leaf_wrap_config shape (19 queries,
// QueryPowBits 16, R = 18 arity-2 commit rounds — max_log_arity is 1 in the
// wrap config, so ~18 rounds ≈ the real FRI depth; round-r Merkle depth is
// R-r-1, i.e. 17 levels at the deepest) and report R1CS constraint counts:
//
//   1. VerifyFriNative  — native-hash transcript + native Merkle (this lane).
//   2. fold-residual    — ONLY the per-query BabyBear fold arithmetic (the
//      same friFoldRowArity2 path both verifiers share), with betas/index bits
//      as direct witnesses: the part the hash swap does NOT touch.
//   3. VerifyFri        — the emulated-hash verifier at the same shape.
//
// hashing+transcript(native)   = (1) - (2)
// hashing+transcript(emulated) = (3) - (2)
// and the swing (3)/(1) is the empirical check of the ~30-70M-emulated vs
// ~1-6M-native premise of docs/deos/WRAP-NATIVE-HASH-DECISION.md.
//
// Compilation only — no witness solving, so no 2^16 grind is needed.
// ---------------------------------------------------------------------------

// friFoldResidualCircuit is the fold-arithmetic-only shape: per query the
// sibling-group reconstruction + friFoldRowArity2 chain + final check, with
// the SAME fail-closed canonicity/boolean ingestion as VerifyFriQueryNative,
// but betas and index bits as direct witnesses and NO Merkle/challenger.
type friFoldResidualCircuit struct {
	r int

	Betas       []BBExt
	FinalEval   BBExt
	InitialEval []BBExt
	Siblings    [][]BBExt
	IndexBits   [][]frontend.Variable
}

func (c *friFoldResidualCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	R := c.r
	for q := range c.InitialEval {
		for i := range c.IndexBits[q] {
			api.AssertIsBoolean(c.IndexBits[q][i])
		}
		bb.ExtAssertIsCanonical(c.InitialEval[q])
		bb.ExtAssertIsCanonical(c.FinalEval)
		folded := c.InitialEval[q]
		for r := 0; r < R; r++ {
			bb.ExtAssertIsCanonical(c.Betas[r])
			bb.ExtAssertIsCanonical(c.Siblings[q][r])
			lfh := R - r - 1
			bR := c.IndexBits[q][r]
			var e0, e1 BBExt
			for i := 0; i < 4; i++ {
				e0[i] = api.Select(bR, c.Siblings[q][r][i], folded[i])
				e1[i] = api.Select(bR, folded[i], c.Siblings[q][r][i])
			}
			folded = friFoldRowArity2(bb, e0, e1, c.Betas[r], c.IndexBits[q][r+1:r+1+lfh])
		}
		bb.ExtAssertIsEqual(folded, c.FinalEval)
	}
	return nil
}

func allocFriFoldResidualCircuit(R, numQueries int) *friFoldResidualCircuit {
	c := &friFoldResidualCircuit{r: R}
	c.Betas = make([]BBExt, R)
	c.InitialEval = make([]BBExt, numQueries)
	c.Siblings = make([][]BBExt, numQueries)
	c.IndexBits = make([][]frontend.Variable, numQueries)
	for q := 0; q < numQueries; q++ {
		c.Siblings[q] = make([]BBExt, R)
		c.IndexBits[q] = make([]frontend.Variable, R)
	}
	return c
}

func TestWrapNativeHashConstraintMeasurement(t *testing.T) {
	// ir2_leaf_wrap_config shape: 19 queries, query_proof_of_work_bits = 16,
	// commit PoW 0, and R = 18 arity-2 commit rounds (max_log_arity = 1 in the
	// wrap config → ~17-19 rounds; deepest Merkle path = R-1 = 17 levels).
	// LogBlowup/LogFinalPolyLen are 0 in this single-round-set scope; R stands
	// in for log_global_max_height so the Merkle depths match the real shape.
	const R = 18
	const numQueries = 19
	const prefixLen = 9
	cfg := FriConfig{QueryPowBits: 16, CommitPowBits: 0,
		ExtraQueryIndexBits: 0, LogBlowup: 0, LogFinalPolyLen: 0}
	field := ecc.BN254.ScalarField()

	compile := func(name string, circuit frontend.Circuit) int {
		start := time.Now()
		cs, err := frontend.Compile(field, r1cs.NewBuilder, circuit)
		if err != nil {
			t.Fatalf("%s: compile failed: %v", name, err)
		}
		n := cs.GetNbConstraints()
		t.Logf("%-28s %12d R1CS constraints  (compiled in %s)", name, n, time.Since(start).Round(time.Millisecond))
		return n
	}

	// (2) the fold-arithmetic residual — untouched by the hash swap.
	foldN := compile("fold-residual (shared)", allocFriFoldResidualCircuit(R, numQueries))

	// (1) the native-hash verifier (this lane).
	nativeN := compile("VerifyFriNative (native)", allocFriVerifyNativeCircuit(R, prefixLen, numQueries, cfg, false))

	// (3) the emulated verifier at the same shape.
	emulatedN := compile("VerifyFri (emulated)", allocFriVerifyCircuit(R, prefixLen, numQueries, cfg, false))

	nativeHash := nativeN - foldN
	emulatedHash := emulatedN - foldN
	t.Logf("hashing+transcript, native:   %12d R1CS (= native - fold-residual)", nativeHash)
	t.Logf("hashing+transcript, emulated: %12d R1CS (= emulated - fold-residual)", emulatedHash)
	t.Logf("fold-arithmetic residual:     %12d R1CS (identical code path in both)", foldN)
	t.Logf("SWING total:   %.1fx  (%d -> %d)", float64(emulatedN)/float64(nativeN), emulatedN, nativeN)
	t.Logf("SWING hashing: %.1fx  (%d -> %d)", float64(emulatedHash)/float64(nativeHash), emulatedHash, nativeHash)

	// The premise this measurement validates (WRAP-NATIVE-HASH-DECISION.md):
	// the native-hash FRI verifier lands in the ~1-6M band while the emulated
	// twin sits in the ~30-70M band. Assert loosely so the test documents the
	// band without flaking on constraint-count drift; a violation means the
	// wrap plan needs revising, which SHOULD fail loudly here.
	if nativeN >= 10_000_000 {
		t.Fatalf("native-hash verifier = %d R1CS, far above the ~1-6M premise — the wrap plan needs revising", nativeN)
	}
	if emulatedN <= nativeN*5 {
		t.Fatalf("emulated/native swing only %.1fx — the native-hash premise did not materialize", float64(emulatedN)/float64(nativeN))
	}
}
