// THE DIFFERENTIAL GATE, MADE RUNNABLE.
//
// emitted_verifier_full.go's VerifierFullCircuit is the emit-driven structural
// skeleton (canonicity, FRI fold ext-muls, commit-phase Merkle openings, the REAL
// multi-height MMCS input-open batch openings, batch-STARK DAG instances, the
// LogUp balance, the query-PoW sample, and the 25-lane segment binding). It now
// EXPOSES the same 25-lane public settlement statement (Publics) the hand-Go
// SettlementCircuit does, and this file makes the gate RUNNABLE: assignVerifierFull
// ingests the REAL fixture proof (fixtures/apex_shrink_fri_real.json) into the
// skeleton's flat witness bank W, using the hand-Go SettlementCircuit assignment
// path (assignSettlementCircuit in stark_algebra_real_fixture_test.go) as the
// reference for which proof field feeds which witness.
//
// Block 2b (input-open) BINDS the real proof: its openings are replayed through
// the Lean-emitted batchData templates (one per input-round shape), so the
// emit-driven circuit clears every input-batch opening on real data. Block 3 now
// BINDS TOO: the batch-table constraint eval is fed the REAL opened rows/columns
// at zeta (assignVerifierFull -> starkInstanceWitness) and evaluated through the
// emitted constraint DAG (stark_constraint_interp.go, READ-ONLY); the folded value
// is bound to quotient(zeta)·Z_H IN-CIRCUIT by bindBlockZeta tooth 3 (transcript
// path, TestEmittedVerifierFullTranscriptRederivesChallenges) over the
// transcript-observed opened chunks, and the global LogUp balance runs on real
// data — replacing the former all-zero inert feed and the free-`out` placeholder.
// The DAG SOURCE
// (fixtures/shrink_symbolic_constraints.json) is Rust-emitted from the AIRs'
// symbolic path (emit_shrink_symbolic.rs), NOT Lean — a NAMED residual (the
// stark-kill convergence); the emit-driven verifier CHECKS it, it does not
// re-author it.
//
// TestEmittedVerifierFullDifferential runs BOTH circuits on the real fixture via
// test.IsSolved and records the RAW result of each; the hand-Go circuit is
// asserted to accept (a sanity floor). TestEmittedVerifierFullBlock3BindsRealProof
// is the block-3 gate: the honest proof SOLVES the whole emit-driven circuit and a
// block-3 tamper is rejected.
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	fr "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// realRoundMerkle is one commit-phase Merkle opening of the REAL proof, in the
// exact (leaf, siblings, pathBits, root) shape VerifyMerklePathBn254 checks —
// the reference verifier's per-round tuple (fri_verify_native_ref.go
// verifyFriNativeRefImpl / merkleRootFromOpeningBn254Ref).
type realRoundMerkle struct {
	leaf *big.Int
	sibs []*big.Int          // lfh sibling nodes (== depths[r] == logMax-r-1)
	bits []frontend.Variable // lfh path bits (indexBits[r+1 : r+1+lfh])
	root *big.Int
}

// realQueryMerkle caches one query's per-round commit-phase Merkle openings and
// its final-poly evaluation (the FRI closure value).
type realQueryMerkle struct {
	rounds    []realRoundMerkle
	finalEval bbExtRef
}

// computeRealQueryMerkle replays the REAL FRI fold chain for query qi (a copy of
// verifyFriNativeRefImpl's per-query loop, driven by the fixture's pinned betas
// and expected index), materializing each round's REAL Merkle-opening tuple. It
// self-checks each round natively (merkleRootFromOpeningBn254Ref must reproduce
// the committed root) so a replication bug here fails LOUDLY as a test error,
// never masquerading as an emit-driven-circuit divergence.
func computeRealQueryMerkle(t *testing.T, fx *shrinkRealFixture, qi int) realQueryMerkle {
	t.Helper()
	q := fx.Queries[qi]
	R := fx.Fri.Rounds
	cfg := shrinkCfgRef(fx)
	logMax := fx.Fri.LogGlobalMaxHeight

	domainIndex := uint(q.ExpectedIndex) >> uint(cfg.ExtraQueryIndexBits)
	indexBits := make([]uint32, logMax)
	for i := 0; i < logMax; i++ {
		indexBits[i] = uint32((domainIndex >> uint(i)) & 1)
	}

	folded := bbExtRef(q.InitialEval)
	ri := 0
	out := realQueryMerkle{}
	for r := 0; r < R; r++ {
		lfh := logMax - r - 1
		var e0, e1 bbExtRef
		if indexBits[r] == 1 {
			e0, e1 = bbExtRef(q.Siblings[r]), folded
		} else {
			e0, e1 = folded, bbExtRef(q.Siblings[r])
		}

		pathBits := indexBits[r+1 : r+1+lfh]
		sibElems := make([]fr.Element, lfh)
		sibBigs := make([]*big.Int, lfh)
		for l := 0; l < lfh; l++ {
			sibElems[l] = parseBn254Hex(t, q.MerklePaths[r][l])
			sibBigs[l] = frToBig(sibElems[l])
		}
		leaf := merkleLeafHashBn254Ref(e0, e1)
		root := parseBn254Hex(t, fx.CommitRoots[r])

		// Native self-check: the emitted skeleton's in-circuit
		// ComputeMerkleRootBn254 is the documented twin of this walk, so if the
		// native recomputation matches the committed root, the in-circuit block
		// must accept these values. Guard against a replication bug.
		if got := merkleRootFromOpeningBn254Ref(e0, e1, pathBits, sibElems); !got.Equal(&root) {
			t.Fatalf("query %d round %d: native Merkle recomputation != committed root — "+
				"fold-chain replication bug (NOT an emit-circuit divergence)", qi, r)
		}

		bits := make([]frontend.Variable, lfh)
		for l := 0; l < lfh; l++ {
			bits[l] = pathBits[l]
		}
		out.rounds = append(out.rounds, realRoundMerkle{
			leaf: frToBig(leaf), sibs: sibBigs, bits: bits, root: frToBig(root),
		})

		parent := indexFromBits(indexBits, r+1, lfh)
		folded = friFoldCoreRef(e0, e1, bbExtRef(fx.ExpectedBetas[r]), invSFromParentRef(parent, lfh, R, r))
		if ri < len(fx.RollInRounds) && fx.RollInRounds[ri] == r {
			betaSq := bbExtMulRef(bbExtRef(fx.ExpectedBetas[r]), bbExtRef(fx.ExpectedBetas[r]))
			folded = bbExtAddRef(folded, bbExtMulRef(betaSq, bbExtRef(q.RollIns[ri])))
			ri++
		}
	}
	out.finalEval = finalPolyEvalRef([]bbExtRef{bbExtRef(fx.FinalPoly[0])}, domainIndex, logMax)
	return out
}

// appendExtVars appends an ext residue tuple as 4 witness values (base lanes).
func appendExtVars(e bbExtRef, w *[]frontend.Variable) {
	for i := 0; i < 4; i++ {
		*w = append(*w, e[i])
	}
}

// assignVerifierFull maps the REAL fixture proof into the emit-driven skeleton's
// flat witness bank W, in the EXACT order VerifierFullCircuit.Define consumes it
// (a single walk over vf.Gadgets mirroring §4 of emitted_verifier_full.go). It
// reuses the hand-Go SettlementCircuit assignment path as the reference for which
// proof field feeds which witness:
//
//   - block 0 (canonicity): a real claim lane (SettlementCircuit's AssertIsCanonical
//     over the public statement);
//   - block 1 (fri_fold): the round-0 fold-beta operand (ExpectedBetas[0], the
//     transcript-link carrier); the fold ARITHMETIC is the Lean-emitted friFoldData
//     template replayed over the separate FriFoldWitness bank (fillFriFoldWitness);
//   - block 1 (ext-eq): per query, both operands = the real final-poly evaluation
//     (the FRI closure value the reference verifier checks folded == finalEval);
//   - block 2 (commit Merkle): the REAL per-query per-round openings (leaf via the
//     replayed fold chain, real path nodes, real index bits, real commit root) —
//     the values the reference verifier's verifyFriNativeRefImpl walks;
//   - block 2b (input-open batch): the REAL multi-height MMCS batch openings —
//     the class-concatenated (tallest-first) opened row limbs, the committed
//     input root, and the per-step path node + index bit, per (query, round) —
//     bound into the Lean-emitted batchData template (ReplayClosed solves the
//     per-class MultiField leaf hashes + injection-interleaved path walk and
//     keeps the recomputed-root == root check). A native openInputBatchRootRef
//     self-check guarantees these values reproduce the committed root, so a
//     circuit rejection here is a real divergence, never a wiring bug;
//   - block 3 (batch-STARK DAG): the REAL opened trace/preprocessed/permutation
//     rows at zeta, evaluated through the emitted constraint DAG; the folded value
//     is bound to quotient(zeta)·Z_H IN-CIRCUIT (bindBlockZeta tooth 3, transcript
//     path) over the transcript-observed opened chunks — starkInstanceWitness
//     natively self-checks the same identity; (LogUp) per-instance partial
//     cumulative sums whose total is the real global balance == 0;
//   - block 4 (query-PoW sample / pow-bits-zero): the real query index sample;
//   - block 5 (segment): the real 25 claim lanes, equated against the EXPOSED
//     public statement (assignSettlementPublics' pinned order).
//
// Block 2b BINDS the real proof with Lean-authored constraints (see
// emitted_input_batch_real_test.go for the isolated accept + tamper-reject
// teeth). Block 3 now BINDS the real proof too: the batch-table DAG is evaluated
// on the real opened values at zeta and the quotient identity + LogUp balance are
// checked in-circuit (replacing the former zero fill). The named residual is that
// the quotient recomposition + selector derivation are host-side inputs here (the
// emit-driven skeleton's structural abstraction, seam #2), and the DAG SOURCE is
// Rust-emitted (the stark-kill convergence), not Lean.
func assignVerifierFull(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *VerifierFullCircuit {
	t.Helper()
	vf := loadVerifierFullT(t)
	c, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc emit-driven circuit: %v", err)
	}

	// The pinned 25-lane public statement = the real expose_claim channel.
	claim := fx.TablePublics[fx.ClaimInstance]
	assignVerifierFullPublics(c, claim)

	// Bake the VK pins (the twins of allocSettlementCircuit's) so Define's shrink-VK
	// and apex-VK pins solve against the real proof; the block-2b self-check below
	// uses c.vkPreprocessedRoot.
	bakeVerifierFullVkPins(t, c, fx, ex)

	// Precompute the real per-query commit-phase Merkle openings + final evals.
	qms := make([]realQueryMerkle, len(fx.Queries))
	for qi := range fx.Queries {
		qms[qi] = computeRealQueryMerkle(t, fx, qi)
	}

	// Block 3 consumes the per-instance opened-value spans (the deployed
	// stark_verify_native.go slicing — buildStarkOpenedSpans, the exact order
	// verify_batch builds coms_to_verify) to feed the batch-table constraint DAG
	// the REAL opened rows/columns at zeta.
	spans, _ := buildStarkOpenedSpans(ex.shapes)
	if len(spans) != len(sym.Instances) {
		t.Fatalf("shape has %d instances, symbolic DAG has %d", len(spans), len(sym.Instances))
	}

	logMax := fx.Fri.LogGlobalMaxHeight
	w := make([]frontend.Variable, 0, len(c.W))

	for _, g := range vf.Gadgets {
		switch g.Gadget {

		case "AssertIsCanonical":
			// block 0 — a real canonical public-statement lane.
			for i := 0; i < g.Count; i++ {
				w = append(w, claim[0])
			}

		case "FriFoldRowArity2":
			// block 1 — the round-0 fold-beta operand (the transcript-link carrier
			// block1FoldBeta pins to ExpectedBetas[0]). The fold ARITHMETIC no longer
			// rides the flat bank: it is the Lean-emitted friFoldData template replayed
			// over the separate FriFoldWitness bank (fillFriFoldWitness, below).
			appendExtVars(bbExtRef(fx.ExpectedBetas[0]), &w)

		case "ExtAssertIsEqual":
			// block 1 — per query, a == b == the real final-poly evaluation.
			for i := 0; i < g.Count; i++ {
				fe := qms[i].finalEval
				appendExtVars(fe, &w) // a
				appendExtVars(fe, &w) // b
			}

		case "VerifyMerklePathBn254":
			// block 2 — the REAL commit-phase openings, in merklePath order:
			// leaf, sibs..., bits..., root.
			for qi := 0; qi < g.Count; qi++ {
				for _, rm := range qms[qi].rounds {
					w = append(w, rm.leaf)
					for _, s := range rm.sibs {
						w = append(w, s)
					}
					w = append(w, rm.bits...)
					w = append(w, rm.root)
				}
			}

		case "VerifyMerklePathBn254InputOpen":
			// block 2b — the REAL multi-height MMCS batch openings. For each
			// (query, input-round): the class-concatenated (tallest-first) opened
			// row limbs (== batchData var 0..R-1), the committed input root (var
			// R), then per path step the sibling node (var R+1+2s) and the index
			// bit (var R+1+2s+1). This is the exact witness the Lean-emitted
			// batchData template binds. The native openInputBatchRootRef
			// self-check below guarantees these values reproduce the committed
			// input root, so a circuit rejection is a REAL divergence, never a
			// wiring bug masquerading as one.
			rw, maxLh, werr := inputOpenRoundWidths(g)
			if werr != nil {
				t.Fatalf("input-open round widths: %v", werr)
			}
			nq := firstParam(g, "num_queries")
			roots := shrinkInputRootsRef(t, fx, ex.loc)
			shapes := make([]OpenInputRoundShape, len(fx.InputRounds))
			for ri, rr := range fx.InputRounds {
				for _, m := range rr.Matrices {
					shapes[ri].Matrices = append(shapes[ri].Matrices,
						OpenInputMatrixShape{m.LogHeight, m.Width, m.NumPoints, m.NextPointBits})
				}
			}
			if len(rw) != len(shapes) {
				t.Fatalf("descriptor carries %d input rounds, fixture has %d", len(rw), len(shapes))
			}
			for q := 0; q < nq; q++ {
				for ri := range rw {
					round := shapes[ri]
					groups := openInputHeightGroupsOf(round)
					opRef := shrinkInputOpeningsRef(t, fx, q)[ri]
					gotRoot, rerr := openInputBatchRootRef(round, opRef,
						fx.Queries[q].ExpectedIndex, logMax)
					if rerr != nil {
						t.Fatalf("query %d round %d: native batch root: %v", q, ri, rerr)
					}
					if !gotRoot.Equal(&roots[ri]) {
						t.Fatalf("query %d round %d: native batch root != committed input root "+
							"(row-order/fold replication bug, NOT an emit-circuit divergence)", q, ri)
					}
					// R row limbs, class-concatenated tallest-first (batchData var 0..R-1).
					nRows := 0
					for _, grp := range groups {
						for _, mi := range grp.mats {
							for _, v := range fx.Queries[q].InputOpenings[ri].Rows[mi] {
								w = append(w, big.NewInt(int64(v)))
								nRows++
							}
						}
					}
					if nRows != sumInts(rw[ri]) {
						t.Fatalf("query %d round %d: %d opened row limbs != descriptor width sum %d",
							q, ri, nRows, sumInts(rw[ri]))
					}
					// committed input root (batchData var R). NATIVE SELF-CHECK: the
					// preprocessed-round root the shrink-VK pin binds must equal the baked
					// constant, so a circuit rejection of the pin is a REAL divergence.
					if ri == preprocessedPcsRound {
						if got := frToBig(roots[ri]); got.Cmp(c.vkPreprocessedRoot) != 0 {
							t.Fatalf("query %d: preprocessed-round (PCS round %d) input root != baked "+
								"shrink-VK pin constant — extraction bug, NOT an emit-circuit divergence", q, ri)
						}
					}
					w = append(w, frToBig(roots[ri]))
					// (sibling, path bit) per step (batchData var R+1+2s / +1).
					reduced := fx.Queries[q].ExpectedIndex >> uint(logMax-maxLh)
					path := fx.Queries[q].InputOpenings[ri].Path
					if len(path) != maxLh {
						t.Fatalf("query %d round %d: path depth %d != maxLh %d",
							q, ri, len(path), maxLh)
					}
					for s := 0; s < maxLh; s++ {
						w = append(w, frToBig(parseBn254Hex(t, path[s])))
						w = append(w, uint32((reduced>>uint(s))&1))
					}
				}
			}

		case "BatchTableInstance":
			// block 3 — the batch-STARK constraint algebra, REAL. For each of the
			// 6 instances, the opened trace/preprocessed/permutation rows at the
			// sampled zeta are evaluated through the emitted constraint DAG
			// (VerifierFullCircuit.starkInstance -> evalSymbolicFoldedNative,
			// stark_constraint_interp.go, READ-ONLY) and the folded value recorded.
			// The quotient identity itself is asserted IN-CIRCUIT by bindBlockZeta
			// tooth 3 (transcript path): folded == quotient(zeta)·Z_H recomposed from
			// the transcript-observed opened chunks — no `out` witness is fed here.
			// Which fixture field feeds which DAG input mirrors the deployed
			// stark_verify_native.go assignment (shrinkSymInputsNative /
			// VerifyShrinkStarkAlgebra). starkInstanceWitness natively self-checks
			// that identity per instance (a wiring/extraction bug fails LOUDLY
			// there, never as a silent emit-circuit divergence).
			for i := range spans {
				w = append(w, starkInstanceWitness(t, ex, sym, spans, i)...)
			}

		case "LogUpBalance":
			// block 3 — the global WitnessChecks balance (mod.rs:623-643),
			// decomposed per instance: slot i is instance i's PARTIAL cumulative
			// sum (the sum of its own global lookups' cumulative sums), so the
			// NumInstances-wide in-circuit sum equals the true global sum == 0.
			// Real and with teeth (tampering any cumulative sum breaks its
			// instance's partial and the total). Native self-check: the real
			// cumulative sums must already balance globally.
			globalSum := bbExtRef{}
			for _, cs := range ex.cumSums {
				globalSum = bbExtAddRef(globalSum, cs)
			}
			if globalSum != (bbExtRef{}) {
				t.Fatalf("block 3 LogUp: real cumulative sums do not balance natively (%v) — "+
					"extraction bug, NOT an emit-circuit divergence", globalSum)
			}
			for i := 0; i < c.vf.Shape.NumInstances; i++ {
				partial := bbExtRef{}
				if i < len(spans) {
					sp := spans[i]
					for k := 0; k < sp.cumSums.len; k++ {
						partial = bbExtAddRef(partial, ex.cumSums[sp.cumSums.off+k])
					}
				}
				appendExtVars(partial, &w)
			}

		case "SampleBitsDecomposed":
			// block 4 — the real query index sample (< 2^logMax < 2^31).
			for i := 0; i < g.Count; i++ {
				w = append(w, uint32(fx.Queries[0].ExpectedIndex))
			}

		case "AssertPowBitsZero":
			// block 4 — a value whose low pow_bits are zero. The real grinding
			// sample is not a standalone fixture lane; 0 satisfies the shape.
			for i := 0; i < g.Count; i++ {
				w = append(w, big.NewInt(0))
			}

		case "AssertIsEqual":
			// block 5 — NO witness consumed. Define binds the block-3 ExposeClaim
			// claim channel (captured during block 3, ExposeClaimAir-bound to the
			// committed trace) to the exposed public statement; the claim lanes live
			// in block 3's public-value feed, not a fresh bank slot, so nothing is
			// appended here (WitnessLen agrees: block 5 draws zero variables).
		}
	}

	if len(w) != len(c.W) {
		t.Fatalf("assignVerifierFull produced %d witness values, bank needs %d "+
			"(consumption drift vs Define)", len(w), len(c.W))
	}
	c.W = w

	// Block 1's fold arithmetic is a replay of the Lean-emitted friFoldData template
	// over the separate FriFoldWitness bank — fed the committed honest fold witness
	// (fri_fold_witness.json), a self-consistent round-0 fold at β=ExpectedBetas[0].
	fillFriFoldWitness(t, c)
	return c
}

// fillFriFoldWitness threads the HONEST fold-consistency witness into block 1's
// replay bank (VerifierFullCircuit.FriFoldWitness). Its values are the Lean-generated
// assignment friFoldAsg (FriFoldEmit.lean) — the same object friFold_leaf_refines
// quantifies over — dumped var-index-ordered to emitted/fri_fold_witness.json. The
// bank layout mirrors friFoldReplay: the len(PublicInputs) boundary limbs
// (public-input order) followed by the friFoldClass.Witness free witnesses.
func fillFriFoldWitness(t *testing.T, c *VerifierFullCircuit) {
	t.Helper()
	if c.friFoldTpl == nil {
		return
	}
	vals, err := loadWitnessValues(friFoldWitnessPath())
	if err != nil {
		t.Fatalf("load %s: %v", friFoldWitnessPath(), err)
	}
	if len(vals) != c.friFoldTpl.NumVars() {
		t.Fatalf("%s: %d witness values, fold template has %d variables",
			friFoldWitnessPath(), len(vals), c.friFoldTpl.NumVars())
	}
	nb := len(c.friFoldTpl.PublicInputs)
	bank := make([]frontend.Variable, nb+len(c.friFoldClass.Witness))
	for i, p := range c.friFoldTpl.PublicInputs {
		bank[i] = vals[p.Var]
	}
	for k, idx := range c.friFoldClass.Witness {
		bank[nb+k] = vals[idx]
	}
	c.FriFoldWitness = bank
}

// bakeVerifierFullVkPins sets the shrink-VK + apex-VK pin constants on an
// emit-driven circuit — the twins of allocSettlementCircuit's vkPreprocessedRoot /
// apexPreprocessedCommit. The shrink-VK constant is the fixture's preprocessed
// (VK-core) commitment root (shrinkPreprocessedRoot); the apex-VK constants are
// the DERIVED deployed apex identity (apexPreprocessedCommitConstants →
// loadApexVkIdentity, whose RecursionVk fingerprint is asserted equal to the
// governance-pinned DreggApexRecursionVk anchor at load — NOT read from the proof
// fixture). Both the structural (compiled) circuit and the witness circuit carry
// them (test.IsSolved compiles the first arg), so the pins are compiled in and
// solved against the real proof.
func bakeVerifierFullVkPins(t *testing.T, c *VerifierFullCircuit, fx *shrinkRealFixture, ex *shrinkStarkExtract) {
	t.Helper()
	c.vkPreprocessedRoot = shrinkPreprocessedRoot(t, fx, ex.loc)
	c.apexPreprocessedCommit = apexPreprocessedCommitConstants(t)
	c.rootVkSpine = rootVkSpineConstants(t)
}

// assignVerifierFullPublics fills the exposed 25-lane statement in the pinned
// genesis8 ++ final8 ++ numTurns ++ chainDigest8 order (the twin of
// assignSettlementPublics for the emit-driven circuit).
func assignVerifierFullPublics(c *VerifierFullCircuit, claim []uint32) {
	k := 0
	for i := 0; i < DigestWidth; i++ {
		c.GenesisRoot[i] = claim[k]
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		c.FinalRoot[i] = claim[k]
		k++
	}
	c.NumTurns = claim[k]
	k++
	for i := 0; i < DigestWidth; i++ {
		c.ChainDigest[i] = claim[k]
		k++
	}
}

// starkInstanceWitness produces block 3's REAL per-instance witness feed for one
// batch-STARK instance, in the EXACT order VerifierFullCircuit.starkInstance
// consumes it (TraceLocal, TraceNext, PreLocal, PreNext, PermLocal, PermNext,
// Challenges, PermValues, selectors, PublicValues, alpha, out). It reuses the
// deployed stark_verify_native.go assignment shape (shrinkSymInputsNative /
// VerifyShrinkStarkAlgebra) for which fixture field feeds which DAG input:
//
//   - trace/preprocessed local rows = the real opened values at zeta
//     (openedEF sliced by the instance's spans); the NEXT rows are the real
//     opened next-row values when the AIR opens them, else the verifier's ZERO
//     substitution (mod.rs:563-581);
//   - permutation columns = the opened flattened columns recomposed on the ext
//     basis (bbExtFromBasisRef, mod.rs:543-556);
//   - challenges = the shared WitnessChecks bus (permAlpha, permBeta) repeated
//     per lookup (transcript.rs:86-101);
//   - PermValues = the instance's global cumulative sums;
//   - selectors = the Lagrange selectors at zeta (computeStarkSelectorsRef);
//   - PublicValues = the real claim lanes (base-field; only expose_claim);
//   - alpha = the constraint-folding alpha. There is NO `out` slot: the quotient
//     identity RHS is no longer a free witness (see below).
//
// It NATIVELY self-checks the quotient identity (host folded == quotient·Z_H)
// so a wiring/extraction bug fails LOUDLY here, never masquerading as an
// emit-circuit divergence — mirroring computeRealQueryMerkle's Merkle self-check
// and expandInputOpenBatch's openInputBatchRootRef self-check.
//
// QUOTIENT IDENTITY — now IN-CIRCUIT (was named seam #2's zeta-quotient reduction):
// bindBlockZeta tooth 3 recomposes quotient(zeta) from the transcript-observed
// opened chunks (recomposeQuotientNative) and asserts folded == quotient·Z_H(zeta),
// with Z_H derived by EF glue from the Lean-emitted selectors. The old placeholder
// fed this RHS as the free `out` witness (vacuous); it is gone. What REMAINS of
// seam #2 is the low-degree half of the DEEP/PCS argument (FRI over the batch-
// combined quotient — that the opened chunks ARE the committed poly's evaluations).
// The constraint DAG SOURCE itself (fixtures/shrink_symbolic_constraints.json) is
// Rust-emitted from the AIRs' symbolic path (emit_shrink_symbolic.rs), NOT
// Lean-emitted — the stark-kill convergence residual. The emit-driven verifier here
// CHECKS that DAG on the real proof; it does not re-author it.
func starkInstanceWitness(t *testing.T, ex *shrinkStarkExtract, sym *SymbolicConstraints,
	spans []starkInstanceSpans, i int) []frontend.Variable {
	t.Helper()
	sh := ex.shapes[i]
	sp := spans[i]
	inst := &sym.Instances[i]
	slice := func(s efSpan) []bbExtRef { return ex.openedEF[s.off : s.off+s.len] }

	sel, err := computeStarkSelectorsRef(ex.ch.zeta, sh.DegreeBits)
	if err != nil {
		t.Fatalf("instance %d selectors: %v", i, err)
	}

	// Native self-check: the quotient identity must hold on the real openings.
	chunks := make([][4]bbExtRef, len(sp.quotientChunks))
	for c, qs := range sp.quotientChunks {
		copy(chunks[c][:], slice(qs))
	}
	quotient := recomposeQuotientRef(sel.zetaPow2Db, chunks,
		shrinkQuotientDomainConsts(sh.DegreeBits, sh.NumQuotientChunks))
	rhs := bbExtMulRef(quotient, sel.zH)
	folded, ferr := evalSymbolicFoldedRef(inst,
		shrinkSymInputsRef(sh, sp, slice, ex.cumSums, ex.pubVals[i], ex.ch, sel), ex.ch.alpha)
	if ferr != nil {
		t.Fatalf("instance %d: host symbolic eval: %v", i, ferr)
	}
	if folded != rhs {
		t.Fatalf("instance %d (%s): native quotient identity FAILED "+
			"(folded %v != quotient·Z_H %v) — extraction/DAG bug, NOT an emit divergence",
			i, inst.Name, folded, rhs)
	}

	w := make([]frontend.Variable, 0)
	appendExts := func(es []bbExtRef) {
		for _, e := range es {
			appendExtVars(e, &w)
		}
	}
	appendZeroExts := func(n int) {
		for k := 0; k < n; k++ {
			appendExtVars(bbExtRef{}, &w)
		}
	}
	recompose := func(flat []bbExtRef) []bbExtRef {
		out := make([]bbExtRef, len(flat)/4)
		for c := range out {
			out[c] = bbExtFromBasisRef([4]bbExtRef(flat[4*c : 4*c+4]))
		}
		return out
	}

	// TraceLocal / TraceNext / PreLocal / PreNext (zero-substituted when the AIR
	// opens no next row, matching the verifier's mod.rs:563-581).
	appendExts(slice(sp.traceLocal))
	if sh.HasTraceNext {
		appendExts(slice(sp.traceNext))
	} else {
		appendZeroExts(sh.Width)
	}
	appendExts(slice(sp.preLocal))
	if sh.HasPreNext {
		appendExts(slice(sp.preNext))
	} else {
		appendZeroExts(sh.PreWidth)
	}
	// PermLocal / PermNext (recomposed ext columns).
	appendExts(recompose(slice(sp.permLocal)))
	appendExts(recompose(slice(sp.permNext)))
	// Challenges: the WitnessChecks bus (alpha, beta) repeated per lookup.
	for l := 0; l < sh.NumLookups; l++ {
		appendExtVars(ex.ch.permAlpha, &w)
		appendExtVars(ex.ch.permBeta, &w)
	}
	// PermValues: the instance's global cumulative sums.
	appendExts(ex.cumSums[sp.cumSums.off : sp.cumSums.off+sp.cumSums.len])
	// Selectors at zeta.
	appendExtVars(sel.isFirstRow, &w)
	appendExtVars(sel.isLastRow, &w)
	appendExtVars(sel.isTransition, &w)
	// Public values (base-field claim lanes; only expose_claim has them).
	for _, v := range ex.pubVals[i] {
		w = append(w, v)
	}
	// alpha. There is NO `out` slot any more: the in-circuit quotient identity
	// (bindBlockZeta tooth 3) recomposes quotient(zeta)·Z_H from the transcript-
	// observed opened chunks and asserts folded == quotient·Z_H, so the RHS is no
	// longer fed as a free witness. `rhs` above is retained only as the NATIVE
	// self-check that the real openings satisfy that identity.
	appendExtVars(ex.ch.alpha, &w)
	return w
}

// TestEmittedVerifierFullDifferential runs the emit-driven skeleton and the
// hand-Go SettlementCircuit on the SAME real fixture proof via test.IsSolved and
// records the raw result of each. The hand-Go circuit must accept (sanity floor);
// the emit-driven result is measured, not gated.
func TestEmittedVerifierFullDifferential(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()

	// --- hand-Go reference (the deployed-shape verifier) ---
	handErr := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym),
		assignSettlementCircuit(t, fx, ex, sym), field)
	if handErr != nil {
		t.Fatalf("SANITY FLOOR VIOLATED: hand-Go SettlementCircuit rejected the real "+
			"proof + correct statement: %v", handErr)
	}
	t.Logf("hand-Go SettlementCircuit on real proof: ACCEPT")

	// --- emit-driven skeleton (structural ~20%) ---
	emitAlloc, err := AllocVerifierFullCircuit(loadVerifierFullT(t), sym)
	if err != nil {
		t.Fatalf("alloc emit-driven circuit: %v", err)
	}
	// Bake the VK pins onto the STRUCTURAL circuit (test.IsSolved compiles the first
	// arg) so the shrink-VK + apex-VK pins are part of the compiled constraint system.
	bakeVerifierFullVkPins(t, emitAlloc, fx, ex)
	emitErr := test.IsSolved(emitAlloc, assignVerifierFull(t, fx, ex, sym), field)
	if emitErr == nil {
		t.Logf("emit-driven VerifierFullCircuit on real proof: ACCEPT")
	} else {
		t.Logf("emit-driven VerifierFullCircuit on real proof: REJECT — %v", emitErr)
	}

	// --- canary datapoint: a wrong public statement (num_turns tampered) ---
	// On a circuit that already rejects the honest assignment this is vacuous,
	// so we RECORD it rather than assert it.
	canary := assignVerifierFull(t, fx, ex, sym)
	canary.NumTurns = uint32(fx.TablePublics[fx.ClaimInstance][2*DigestWidth]) + 1
	canaryErr := test.IsSolved(emitAlloc, canary, field)
	if canaryErr == nil {
		t.Logf("emit-driven on TAMPERED statement (num_turns+1): ACCEPT (canary NOT caught)")
	} else {
		t.Logf("emit-driven on TAMPERED statement (num_turns+1): REJECT — %v", canaryErr)
	}
}

// TestEmittedVerifierFullBlock3BindsRealProof is the block-3 gate. Block 3 (the
// batch-table STARK constraint eval) is fed the REAL opened rows/columns at zeta
// through the emitted constraint DAG (replacing the former all-zero inert feed),
// and its quotient identity is bound IN-CIRCUIT by bindBlockZeta (the transcript
// stage) — so this gate runs on the transcript circuit, NOT the structural-only
// skeleton. On the structural skeleton block 3's folded value is unconstrained (the
// former free `out` placeholder is gone); the identity has teeth only where the
// opened chunks ARE the transcript-observed stream.
//
//  1. ACCEPT: the honest proof SOLVES the whole emit-driven circuit — the quotient
//     identity folded == quotient(zeta)·Z_H(zeta) holds for all 6 instances (tooth 3,
//     over the transcript-observed opened chunks) and the per-instance partial
//     cumulative sums balance to zero;
//  2. REJECT: flipping one felt of block 3's first opened trace value diverges it
//     from the transcript-observed opened stream (tooth 2) AND makes the in-circuit
//     folded diverge from quotient·Z_H (tooth 3), so the constraint fires — proving
//     block 3 genuinely binds the DAG evaluation to the committed openings, not a
//     tautology over a free output.
//
// The tamper flips the assembled witness bank directly (past starkInstanceWitness's
// native self-check), which is the point: the CIRCUIT, not the host, must reject.
func TestEmittedVerifierFullBlock3BindsRealProof(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()
	vf := loadVerifierFullT(t)

	alloc := allocVerifierFullWithTranscript(t, fx, sym)

	// ACCEPT: block 3 (and every block) clears on the real proof, with the quotient
	// identity now asserted in-circuit over the transcript-observed chunks.
	if err := test.IsSolved(alloc, assignVerifierFullWithTranscript(t, fx, ex, sym), field); err != nil {
		t.Fatalf("emit-driven circuit REJECTED the honest proof after wiring block 3: %v", err)
	}

	// Locate the start of the block-3 BatchTableInstance feed in the flat bank:
	// the exact witness budget of every gadget the interpreter consumes BEFORE
	// BatchTableInstance (WitnessLen over the truncated descriptor).
	prefix := &VerifierFull{Schema: vf.Schema, Shape: vf.Shape}
	for _, g := range vf.Gadgets {
		if g.Gadget == "BatchTableInstance" {
			break
		}
		prefix.Gadgets = append(prefix.Gadgets, g)
	}
	block3Start, err := prefix.WitnessLen(sym)
	if err != nil {
		t.Fatalf("block-3 offset: %v", err)
	}

	// CANARY: flip the first felt of block 3's first opened trace value. The
	// transcript path binds it to the observed opened stream (tooth 2) and feeds it
	// into the quotient identity (tooth 3), so a lone-flipped opened value is UNSAT.
	canary := assignVerifierFullWithTranscript(t, fx, ex, sym)
	orig, ok := canary.W[block3Start].(uint32)
	if !ok {
		t.Fatalf("block-3 witness slot %d is not a base-field felt (%T)", block3Start, canary.W[block3Start])
	}
	canary.W[block3Start] = bbAddRef(orig, 1)
	if err := test.IsSolved(alloc, canary, field); err == nil {
		t.Fatal("emit-driven circuit ACCEPTED a tampered block-3 opened value — the " +
			"openings bind / quotient identity does not bind the DAG evaluation")
	}
}

// TestEmittedVerifierFullStatementAndVkPinsBind is the LAST-BLOCK gate: block 5's
// 25-lane settlement statement bind and the shrink-VK + apex-VK fingerprint pins
// now bind the REAL proof, and each is load-bearing (not the fresh-wire /
// tautology / absent form the cycle-1 measure found). Three mutation teeth, each
// with every OTHER block honest:
//
//  1. STATEMENT (block 5): a public statement that disagrees with the proof's
//     exposed claim (num_turns+1) is REJECTED. Block 5 equates the block-3
//     ExposeClaim claim channel — not a forgeable fresh witness (block 5 draws
//     ZERO bank variables) — against the public lanes, so a settled statement the
//     proof does not attest cannot pass.
//  2. SHRINK-VK pin (tooth 1): a WRONG baked preprocessed-commitment root rejects
//     the honest proof — the block-2b preprocessed-round root the pin binds is the
//     real proof's VK-core, so the pin genuinely constrains it (were the pin absent,
//     a wrong constant would be inert and the proof would still ACCEPT).
//  3. APEX-VK pin (tooth 2): a WRONG baked apex VK-core lane rejects the honest
//     proof — the claim channel's re-exposed VK-core lanes (25..33) are bound to
//     the pinned apex commitment, so a same-shape non-deployed apex cannot settle.
//
// The floor (honest proof + honest pins ACCEPTs) is asserted by
// TestEmittedVerifierFullBlock3BindsRealProof; here the teeth are the point.
func TestEmittedVerifierFullStatementAndVkPinsBind(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()
	vf := loadVerifierFullT(t)

	// --- tooth 1: statement bind. Honest structural circuit; tampered public. ---
	stmtAlloc, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc: %v", err)
	}
	bakeVerifierFullVkPins(t, stmtAlloc, fx, ex)
	badStmt := assignVerifierFull(t, fx, ex, sym)
	badStmt.NumTurns = uint32(fx.TablePublics[fx.ClaimInstance][2*DigestWidth]) + 1
	if err := test.IsSolved(stmtAlloc, badStmt, field); err == nil {
		t.Fatal("STATEMENT BIND: a public statement (num_turns+1) the proof does not attest " +
			"was ACCEPTED — block 5 does not bind the exposed-claim channel to the public lanes")
	}

	// --- tooth 2: shrink-VK pin. Wrong baked preprocessed root; honest witness. ---
	vkAlloc, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc: %v", err)
	}
	bakeVerifierFullVkPins(t, vkAlloc, fx, ex)
	vkAlloc.vkPreprocessedRoot = new(big.Int).Add(vkAlloc.vkPreprocessedRoot, big.NewInt(1))
	if err := test.IsSolved(vkAlloc, assignVerifierFull(t, fx, ex, sym), field); err == nil {
		t.Fatal("SHRINK-VK PIN: a WRONG baked preprocessed-commitment root ACCEPTED the honest " +
			"proof — the shrink-VK pin is absent or does not constrain the block-2b preprocessed root")
	}

	// --- tooth 3: apex-VK pin. Wrong baked apex VK-core lane; honest witness. ---
	apexAlloc, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc: %v", err)
	}
	bakeVerifierFullVkPins(t, apexAlloc, fx, ex)
	apexAlloc.apexPreprocessedCommit[0] = new(big.Int).Add(apexAlloc.apexPreprocessedCommit[0], big.NewInt(1))
	if err := test.IsSolved(apexAlloc, assignVerifierFull(t, fx, ex, sym), field); err == nil {
		t.Fatal("APEX-VK PIN: a WRONG baked apex VK-core lane ACCEPTED the honest proof — the " +
			"apex-VK pin is absent or does not bind the claim channel's re-exposed VK-core lanes")
	}

	// --- tooth 4: VK-SPINE (subtree) pin. Wrong baked spine lane; honest witness. ---
	//
	// Its own tooth because it fails for a reason tooth 3 cannot reach: the apex
	// RecursionVk fingerprint is content-independent and does NOT move when a child
	// circuit is substituted, so a foreign subtree under an honest apex passes tooth 3
	// and is caught only here.
	spineAlloc, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc: %v", err)
	}
	bakeVerifierFullVkPins(t, spineAlloc, fx, ex)
	spineAlloc.rootVkSpine[0] = new(big.Int).Add(spineAlloc.rootVkSpine[0], big.NewInt(1))
	if err := test.IsSolved(spineAlloc, assignVerifierFull(t, fx, ex, sym), field); err == nil {
		t.Fatal("VK-SPINE PIN: a WRONG baked root VK-spine lane ACCEPTED the honest proof — the " +
			"subtree pin is absent or does not bind the claim channel's re-exposed spine lanes")
	}
}
