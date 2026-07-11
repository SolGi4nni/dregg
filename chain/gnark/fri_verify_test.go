// Tests for the assembled single-matrix FRI verifier flow: the native-Go
// reference (fri_verify_ref.go) and the circuit gadget (fri_verify.go),
// cross-checked against each other via the gnark test engine. All tests run by
// DEFAULT `go test` (no build tags, no feature gates, no skips).
//
// The flow draws the folding betas and the query indices FROM the challenger in
// fork-faithful transcript order (fri/src/verifier.rs verify_fri, Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec — see fri_verify_ref.go for the full
// file:line map). The VALID fixture is built by DRIVING the reference challenger
// exactly as the flow reads it: commit each folded codeword, observe its root,
// sample the beta in-transcript, fold; then grind a real query PoW witness for
// the live transcript; then sample each query index from that same challenger
// and read off its openings. So the proof is honest and non-vacuous — the same
// challenger the verifier re-derives betas/index from produced them.
//
// The transcript-order canary (TestFriVerifyWrongBetaOrderCanary) is THE point
// of this lane: it feeds a VALID proof through the observe/sample-SWAPPED order
// and requires a REJECT in both the reference and the gadget, proving the
// assembled flow binds the observe-root-THEN-sample-beta interleave.
package friverifier

import (
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// friVerifyPrefix is a canonical non-trivial transcript prefix standing in for
// the pre-commit-phase state (the batch-combination alpha sample + input
// openings, which are the reduced-opening residual) at which VerifyFri is
// entered. Both the reference and the gadget observe it before the commit phase.
func friVerifyPrefix() []uint32 {
	return []uint32{7, 14, 21, 28, 35, 42, 49, 56, 63}
}

// testFriConfigRef / testFriConfig are the single-round-set scope: arity-2,
// log_blowup = log_final_poly_len = 0 (final domain is a point), commit PoW off,
// extra query index bits 0. QueryPowBits is 12 here (ir2_leaf_wrap_config uses
// 16) so the brute-force grind in the fixture builder stays fast; the grinding
// PATH is identical.
const testQueryPowBits = 12

func testFriConfigRef() friConfigRef {
	return friConfigRef{QueryPowBits: testQueryPowBits, CommitPowBits: 0,
		ExtraQueryIndexBits: 0, LogBlowup: 0, LogFinalPolyLen: 0}
}

func testFriConfig() FriConfig {
	return FriConfig{QueryPowBits: testQueryPowBits, CommitPowBits: 0,
		ExtraQueryIndexBits: 0, LogBlowup: 0, LogFinalPolyLen: 0}
}

// ---------------------------------------------------------------------------
// Fixture builder: drive the reference challenger exactly as verify_fri reads
// it, producing a VALID single-matrix FRI proof whose betas and query indices
// the verifier re-derives from the same transcript.
// ---------------------------------------------------------------------------

func buildValidFriProof(R int, cfg friConfigRef, numQueries int, prefix []uint32, seed int64) *friProofRef {
	rng := rand.New(rand.NewSource(seed))
	lane := func() uint32 { return uint32(rng.Uint64() % BabyBearP) }
	ext := func() bbExtRef { return bbExtRef{lane(), lane(), lane(), lane()} }

	// Initial codeword f0 (size 2^R).
	N := 1 << R
	f0 := make([]bbExtRef, N)
	for i := range f0 {
		f0[i] = ext()
	}

	c := newChallengerRef()
	c.observeSlice(prefix)

	// Commit phase driven by the transcript: commit f_r, observe root, sample
	// beta, fold. Keep every round's Merkle layers for later opening.
	fs := [][]bbExtRef{f0}
	roots := make([][8]uint32, R)
	layersByRound := make([][][][8]uint32, R)
	for r := 0; r < R; r++ {
		root, layers := merkleCommitRef(fs[r])
		roots[r] = root
		layersByRound[r] = layers
		c.observeSlice(root[:])
		if !c.checkWitness(cfg.CommitPowBits, 0) { // 0 bits: no-op, no advance
			panic("commit PoW check failed for 0 bits")
		}
		beta := c.sampleExt()
		fs = append(fs, foldVectorRef(fs[r], beta, R, r))
	}
	finalPoly := []bbExtRef{fs[R][0]} // log_final_poly_len == 0: one constant

	// Observe the final poly + arity schedule (same order verify_fri reads).
	for _, coeff := range finalPoly {
		c.observeSlice(coeff[:])
	}
	for r := 0; r < R; r++ {
		c.observe(1)
	}

	// Grind a real query PoW witness for the live transcript, then advance the
	// challenger through the check exactly as the verifier will.
	powWitness := grindRef(c, cfg.QueryPowBits)
	if !c.checkWitness(cfg.QueryPowBits, powWitness) {
		panic("grindRef produced a witness its own check rejects")
	}

	logGlobalMaxHeight := R + cfg.LogBlowup + cfg.LogFinalPolyLen
	queries := make([]friQueryOpeningRef, numQueries)
	for q := 0; q < numQueries; q++ {
		index := c.sampleBits(logGlobalMaxHeight + cfg.ExtraQueryIndexBits)
		domainIndex := index >> uint(cfg.ExtraQueryIndexBits)

		var op friQueryOpeningRef
		op.InitialEval = fs[0][domainIndex]
		for r := 0; r < R; r++ {
			parent := domainIndex >> uint(r+1)
			op.MerkleProofs = append(op.MerkleProofs, merkleOpenRef(layersByRound[r], int(parent)))
			bR := (domainIndex >> uint(r)) & 1
			op.Siblings = append(op.Siblings, fs[r][2*parent+(1-bR)])
		}
		queries[q] = op
	}

	return &friProofRef{R: R, CommitRoots: roots, FinalPoly: finalPoly,
		PowWitness: powWitness, Queries: queries}
}

// freshRefChallenger returns a native challenger positioned at the commit phase
// (prefix observed), the same start state both the reference verifier and the
// gadget use.
func freshRefChallenger(prefix []uint32) *challengerRef {
	c := newChallengerRef()
	c.observeSlice(prefix)
	return c
}

// ---------------------------------------------------------------------------
// gnark wrapper circuit for the assembled flow.
// ---------------------------------------------------------------------------

type friVerifyCircuit struct {
	// Structural (unexported so the gnark schema walker ignores them).
	r    int
	cfg  FriConfig
	swap bool

	Prefix      []frontend.Variable
	CommitRoots [][DigestWidth]frontend.Variable
	FinalPoly   []BBExt
	PowWitness  frontend.Variable
	Queries     []FriQueryOpening
}

func (c *friVerifyCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewChallenger(bb)
	ch.ObserveSlice(c.Prefix)
	verifyFriImpl(bb, c.cfg, c.r, c.CommitRoots, c.FinalPoly, c.PowWitness,
		c.Queries, ch, c.swap)
	return nil
}

// allocFriVerifyCircuit allocates a circuit shell with the exact slice sizes of
// the proof (same shape used for both the compiled template and the assignment).
func allocFriVerifyCircuit(R, prefixLen, numQueries int, cfg FriConfig, swap bool) *friVerifyCircuit {
	c := &friVerifyCircuit{r: R, cfg: cfg, swap: swap}
	c.Prefix = make([]frontend.Variable, prefixLen)
	c.CommitRoots = make([][DigestWidth]frontend.Variable, R)
	c.FinalPoly = make([]BBExt, 1<<cfg.LogFinalPolyLen)
	c.Queries = make([]FriQueryOpening, numQueries)
	for q := range c.Queries {
		c.Queries[q].Siblings = make([]BBExt, R)
		c.Queries[q].MerkleProofs = make([][][DigestWidth]frontend.Variable, R)
		for r := 0; r < R; r++ {
			c.Queries[q].MerkleProofs[r] = make([][DigestWidth]frontend.Variable, R-r-1)
		}
	}
	return c
}

// assignFriVerifyCircuit fills an allocated circuit with a proof + prefix.
func assignFriVerifyCircuit(p *friProofRef, prefix []uint32, cfg FriConfig, swap bool) *friVerifyCircuit {
	c := allocFriVerifyCircuit(p.R, len(prefix), len(p.Queries), cfg, swap)
	for i, v := range prefix {
		c.Prefix[i] = v
	}
	for r := 0; r < p.R; r++ {
		for i := 0; i < DigestWidth; i++ {
			c.CommitRoots[r][i] = p.CommitRoots[r][i]
		}
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
				for i := 0; i < DigestWidth; i++ {
					c.Queries[q].MerkleProofs[r][l][i] = op.MerkleProofs[r][l][i]
				}
			}
		}
	}
	return c
}

// ---------------------------------------------------------------------------
// ACCEPT: a valid proof verifies in BOTH the native reference AND the gadget.
// ---------------------------------------------------------------------------

func TestFriVerifyAcceptsRefAndGadget(t *testing.T) {
	const R = 3
	const numQueries = 3
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()

	for iter := 0; iter < 4; iter++ {
		p := buildValidFriProof(R, cfgRef, numQueries, prefix, 500+int64(iter))

		if !verifyFriRef(freshRefChallenger(prefix), cfgRef, p) {
			t.Fatalf("iter %d: valid proof REJECTED by reference", iter)
		}
		tmpl := allocFriVerifyCircuit(R, len(prefix), numQueries, cfg, false)
		if err := test.IsSolved(tmpl, assignFriVerifyCircuit(p, prefix, cfg, false), field); err != nil {
			t.Fatalf("iter %d: valid proof rejected by gadget: %v", iter, err)
		}
	}
}

// ---------------------------------------------------------------------------
// TRANSCRIPT-ORDER CANARY: a VALID proof fed through the observe/sample-SWAPPED
// commit-phase order must FAIL in both the reference and the gadget. This is the
// load-bearing proof that the assembled flow binds the interleave — a wrong
// order draws different betas and the whole fold chain diverges.
// ---------------------------------------------------------------------------

func TestFriVerifyWrongBetaOrderCanary(t *testing.T) {
	const R = 3
	const numQueries = 2
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()

	p := buildValidFriProof(R, cfgRef, numQueries, prefix, 4242)

	// Guard (non-vacuity): the correct order ACCEPTS this proof, ref and gadget.
	if !verifyFriRefImpl(freshRefChallenger(prefix), cfgRef, p, false) {
		t.Fatal("guard: correct-order reference rejected a valid proof")
	}
	tmplOK := allocFriVerifyCircuit(R, len(prefix), numQueries, cfg, false)
	if err := test.IsSolved(tmplOK, assignFriVerifyCircuit(p, prefix, cfg, false), field); err != nil {
		t.Fatalf("guard: correct-order gadget rejected a valid proof: %v", err)
	}

	// Canary: the swapped order REJECTS the same proof, ref and gadget.
	if verifyFriRefImpl(freshRefChallenger(prefix), cfgRef, p, true) {
		t.Fatal("swapped-order reference ACCEPTED a valid proof — interleave not load-bearing")
	}
	tmplSwap := allocFriVerifyCircuit(R, len(prefix), numQueries, cfg, true)
	if err := test.IsSolved(tmplSwap, assignFriVerifyCircuit(p, prefix, cfg, true), field); err == nil {
		t.Fatal("swapped-order gadget ACCEPTED a valid proof — interleave not load-bearing")
	}
}

// ---------------------------------------------------------------------------
// REJECT (load-bearing): each single tamper must FAIL in both the reference and
// the gadget. Every case is ref-guarded (untampered passes, tampered fails the
// reference) so the gadget reject is non-vacuous.
// ---------------------------------------------------------------------------

func TestFriVerifyRejectsTampers(t *testing.T) {
	const R = 3
	const numQueries = 2
	const seed = 909
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()

	cases := []struct {
		name   string
		tamper func(p *friProofRef)
	}{
		{
			// Bad grinding witness: the query PoW check fails (fail-closed).
			name: "bad-grinding-witness",
			tamper: func(p *friProofRef) {
				p.PowWitness = p.PowWitness ^ 1 // stays canonical (< p, p odd)
			},
		},
		{
			// Tampered query opening: a corrupted sibling eval breaks the
			// round-0 Merkle check for that query.
			name: "tampered-query-opening",
			tamper: func(p *friProofRef) {
				p.Queries[0].Siblings[0][0] = bbAddRef(p.Queries[0].Siblings[0][0], 1)
			},
		},
		{
			// Tampered commit root: diverges the sampled beta AND the Merkle
			// check against that root.
			name: "tampered-commit-root",
			tamper: func(p *friProofRef) {
				p.CommitRoots[0][0] = bbAddRef(p.CommitRoots[0][0], 1)
			},
		},
		{
			// Wrong final polynomial: shifts the transcript (it is observed) and
			// the final-eval target — the fold chain no longer lands on it.
			name: "wrong-final-poly",
			tamper: func(p *friProofRef) {
				p.FinalPoly[0][0] = bbAddRef(p.FinalPoly[0][0], 1)
			},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			// Ref-guard: the untampered proof passes.
			base := buildValidFriProof(R, cfgRef, numQueries, prefix, seed)
			if !verifyFriRef(freshRefChallenger(prefix), cfgRef, base) {
				t.Fatalf("%s: base proof rejected — guard broken", tc.name)
			}
			// Tamper and require reference rejection (non-vacuous).
			p := buildValidFriProof(R, cfgRef, numQueries, prefix, seed)
			tc.tamper(p)
			if verifyFriRef(freshRefChallenger(prefix), cfgRef, p) {
				t.Fatalf("%s: reference ACCEPTED a tampered proof (vacuous reject)", tc.name)
			}
			// The gadget must also reject.
			tmpl := allocFriVerifyCircuit(R, len(prefix), numQueries, cfg, false)
			if err := test.IsSolved(tmpl, assignFriVerifyCircuit(p, prefix, cfg, false), field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED a tampered proof", tc.name)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Differential: gadget and reference agree (accept/reject) over several random
// valid proofs and single-lane tampers.
// ---------------------------------------------------------------------------

func TestFriVerifyDifferentialRefVsGadget(t *testing.T) {
	const R = 3
	const numQueries = 2
	prefix := friVerifyPrefix()
	cfgRef := testFriConfigRef()
	cfg := testFriConfig()
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(2026))

	agree := func(p *friProofRef, label string) {
		refOK := verifyFriRef(freshRefChallenger(prefix), cfgRef, p)
		tmpl := allocFriVerifyCircuit(R, len(prefix), numQueries, cfg, false)
		err := test.IsSolved(tmpl, assignFriVerifyCircuit(p, prefix, cfg, false), field)
		gadgetOK := err == nil
		if refOK != gadgetOK {
			t.Fatalf("%s: ref=%v gadget=%v (disagree); gadget err=%v", label, refOK, gadgetOK, err)
		}
	}

	for iter := 0; iter < 6; iter++ {
		p := buildValidFriProof(R, cfgRef, numQueries, prefix, int64(3000+iter))
		agree(p, "valid")

		bad := buildValidFriProof(R, cfgRef, numQueries, prefix, int64(3000+iter))
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
			bad.CommitRoots[r][rng.Intn(DigestWidth)] = bbAddRef(bad.CommitRoots[r][rng.Intn(DigestWidth)], 1)
		case 3:
			bad.FinalPoly[0][rng.Intn(4)] = bbAddRef(bad.FinalPoly[0][rng.Intn(4)], 1)
		}
		agree(bad, "tampered")
	}
}

// RESIDUAL — what this lane does NOT cover, for the next FRI wrap milestone (the
// single-matrix assembly is complete; these are the batch-STARK residuals):
//
//   - reduced openings / alpha batching (open_input, fri/src/verifier.rs:271):
//     the per-query InitialEval seed is provided directly. The full batch-STARK
//     forms it by alpha-batching (f(z)-f(x))/(z-x) across every opened matrix,
//     with the batch-combination alpha sampled at verifier.rs:143 (the caller's
//     pre-commit-phase transcript step this flow enters after) and lower-height
//     reduced openings rolled in at their fold round with a beta^arity factor
//     (verifier.rs:477). That is the multi-height, per-table degree_bits work.
//   - higher arity: ir2_leaf_wrap_config has max_log_arity 3. Arity 2^k folds
//     decompose into k sequential arity-2 folds (two_adic_pcs.rs:160).
//   - realistic blowup + multi-coefficient final poly: this scope uses
//     log_blowup = log_final_poly_len = 0 (final domain is a point), so the final
//     check is a direct equality. A production shape needs a real coset IDFT so
//     final_poly has length 2^log_final_poly_len and the Horner evaluation at
//     x = g^rev(domain_index) (verifier.rs:311-321, finalPolyEvalRef here) is
//     exercised over a sampled index with spare bits.
//   - the logup interaction bus and the four non-primitive op tables
//     (Poseidon2-w16/w24, recompose, expose_claim).
