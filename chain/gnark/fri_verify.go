// Single-matrix FRI verifier flow as a gnark circuit gadget — the assembly that
// turns the landed pieces (challenger.go, grinding.go, fri_query.go) into one
// in-circuit verify_fri. This is the integration the FRI-query lane named as its
// residual ("betas/index arrive pre-sampled here; the assembly wires
// challenger.go around this gadget"). Here the folding betas and the query
// indices are DRAWN FROM THE CHALLENGER, not passed as pre-sampled arguments.
//
// Ground truth: fri/src/verifier.rs verify_fri at the workspace-pinned Plonky3
// rev 82cfad73cd734d37a0d51953094f970c531817ec. The observe/sample interleave is
// the load-bearing soundness component — the same transcript order as the Rust
// verifier, cite-mapped in fri_verify_ref.go (the plain-Go twin this gadget is
// differentially tested against):
//
//   commit phase (verifier.rs:214-227): per round, Observe the commit root, run
//   the commit-PoW check (0 bits in ir2_leaf_wrap_config -> no-op), then Sample
//   the folding beta. Every beta depends on every prior observed root, so a
//   wrong order silently diverges the whole fold chain (the wrong-order canary
//   in fri_verify_test.go proves this).
//   then: ObserveExt the final-poly coefficients (verifier.rs:238); Observe the
//   arity schedule (verifier.rs:249-251); CheckWitness the query grinding
//   (verifier.rs:254); and per query SampleBits the index (verifier.rs:268) and
//   run VerifyFriQuery (the per-query fold chain, verifier.rs:298).
//
// SCOPE. Single-matrix (single-round-set), arity-2, log_final_poly_len = 0 (the
// final domain is a single point, so the final polynomial is one constant). The
// per-query initial reduced opening is provided directly (InitialEval); the
// alpha-batched multi-height reduced openings (open_input, verifier.rs:271),
// higher arity, realistic blowup, the logup interaction bus and the four NPO
// tables are the named residual (see the RESIDUAL note at the bottom of
// fri_verify_test.go). The challenger enters VerifyFri already positioned past
// the pre-commit-phase steps (the batch-combination alpha sample at
// verifier.rs:143 and the input openings) — those belong to the reduced-opening
// residual.
package friverifier

import "github.com/consensys/gnark/frontend"

// FriConfig carries the FRI parameters this flow reads. For ir2_leaf_wrap_config
// (fri/src/config.rs:76-84): QueryPowBits = 16, CommitPowBits = 0, LogBlowup = 1,
// LogFinalPolyLen = 0, ExtraQueryIndexBits = 0. This single-matrix assembly runs
// at LogBlowup = LogFinalPolyLen = 0.
type FriConfig struct {
	QueryPowBits        int
	CommitPowBits       int
	ExtraQueryIndexBits int
	LogBlowup           int
	LogFinalPolyLen     int
}

// FriQueryOpening is one query's opening data (the in-circuit twin of
// friQueryOpeningRef): the initial reduced-opening seed and, per commit round,
// the sibling evaluation + Merkle path. The query index is drawn from the
// challenger inside VerifyFri, not carried here.
type FriQueryOpening struct {
	InitialEval  BBExt
	Siblings     []BBExt
	MerkleProofs [][][DigestWidth]frontend.Variable
}

// VerifyFri constrains the single-matrix FRI verifier flow in-circuit, drawing
// the betas and query indices from `ch` in fork-faithful transcript order and
// reusing the landed gadgets verbatim (NewChallenger/Observe/Sample,
// CheckWitness, VerifyFriQuery). `ch` is the challenger positioned at the commit
// phase. A tampered root/opening/witness/final-poly, or a divergent transcript,
// yields an unsatisfiable constraint system (fail-closed).
func VerifyFri(
	bb *BBApi,
	cfg FriConfig,
	R int,
	commitRoots [][DigestWidth]frontend.Variable,
	finalPoly []BBExt,
	powWitness frontend.Variable,
	queries []FriQueryOpening,
	ch *Challenger,
) {
	verifyFriImpl(bb, cfg, R, commitRoots, finalPoly, powWitness, queries, ch, false)
}

// verifyFriImpl is VerifyFri with a test-only order flag. swapOrder=false is the
// shipped, fork-faithful order (Observe root at verifier.rs:221 THEN Sample beta
// at :225). swapOrder=true samples the beta BEFORE observing the root; the
// transcript-order canary (fri_verify_test.go) feeds a VALID proof through
// swapOrder=true and requires the constraint system to be UNSATISFIABLE, proving
// the observe/sample interleave is load-bearing. Only the commit-phase
// interleave differs.
func verifyFriImpl(
	bb *BBApi,
	cfg FriConfig,
	R int,
	commitRoots [][DigestWidth]frontend.Variable,
	finalPoly []BBExt,
	powWitness frontend.Variable,
	queries []FriQueryOpening,
	ch *Challenger,
	swapOrder bool,
) {
	if len(finalPoly) != (1 << cfg.LogFinalPolyLen) {
		panic("VerifyFri: len(finalPoly) must equal 2^LogFinalPolyLen")
	}
	if cfg.LogFinalPolyLen != 0 {
		// Single-round-set scope: the final domain is one point, so the final
		// polynomial is one constant and the final check is a direct equality.
		// A multi-coefficient final poly needs the Horner evaluation at
		// x = g^rev(domain_index) over the sampled index (verifier.rs:311-321),
		// which is the realistic-blowup residual.
		panic("VerifyFri: single-round-set scope requires LogFinalPolyLen==0")
	}

	// Commit phase (verifier.rs:214-227). Betas are built in-transcript.
	betas := make([]BBExt, R)
	for r := 0; r < R; r++ {
		if swapOrder {
			betas[r] = ch.SampleExt()
			ch.ObserveSlice(commitRoots[r][:])
		} else {
			ch.ObserveSlice(commitRoots[r][:])                     // verifier.rs:221
			CheckWitness(ch, cfg.CommitPowBits, frontend.Variable(0)) // :222 (0 bits: no-op)
			betas[r] = ch.SampleExt()                              // verifier.rs:225
		}
	}

	// verifier.rs:238 observe_algebra_slice(&final_poly).
	for _, coeff := range finalPoly {
		ch.ObserveExt(coeff)
	}

	// verifier.rs:249-251 observe the arity schedule (log_arity 1 per arity-2 round).
	for r := 0; r < R; r++ {
		ch.Observe(frontend.Variable(1))
	}

	// verifier.rs:254 query PoW grinding (fail-closed on a bad witness).
	CheckWitness(ch, cfg.QueryPowBits, powWitness)

	// Per query: sample the index from the challenger, run the fold chain.
	numIndexBits := R + cfg.LogBlowup + cfg.LogFinalPolyLen + cfg.ExtraQueryIndexBits
	finalEval := finalPoly[0] // LogFinalPolyLen==0: the final domain is a point.
	for _, q := range queries {
		// verifier.rs:268 index = sample_bits(log_global_max_height + extra).
		idxBits := ch.SampleBitsDecomposed(numIndexBits)
		// verifier.rs:287 domain_index = index >> extra: drop the low extra bits.
		domainBits := idxBits[cfg.ExtraQueryIndexBits:]
		VerifyFriQuery(bb, R, commitRoots, betas, q.Siblings, q.MerkleProofs,
			domainBits, q.InitialEval, finalEval) // verifier.rs:298 verify_query
	}
}
