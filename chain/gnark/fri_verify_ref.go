// Plain-Go (non-circuit) reference twin of the assembled single-matrix FRI
// verifier flow: the whole-transcript wrapper that turns the landed pieces
// (challenger_ref.go, grinding_ref.go, fri_query_ref.go) into one verify_fri
// call. The circuit gadget in fri_verify.go is differentially tested against
// this reference, and this reference is pinned lane-for-lane to the fork FRI
// verifier at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec:
//
//   - fri/src/verifier.rs:113  verify_fri — the top-level flow this assembles.
//   - THE OBSERVE/SAMPLE INTERLEAVE (the load-bearing transcript order):
//       * verifier.rs:214-227  the commit-phase loop: for each round
//         challenger.observe(comm) (:221), check_witness(commit PoW) (:222),
//         then challenger.sample_algebra_element() -> beta (:225). The betas
//         are built IN-TRANSCRIPT: each beta depends on every prior observed
//         root. Swapping observe/sample makes every beta diverge -> the fold
//         chain diverges -> a silent soundness break. The wrong-order canary in
//         fri_verify_test.go proves this interleave is binding.
//       * verifier.rs:238  challenger.observe_algebra_slice(&final_poly) — the
//         final polynomial coefficients are absorbed after the beta loop.
//       * verifier.rs:249-251  challenger.observe(Val::from_usize(log_arity))
//         per round — the arity schedule is bound before query grinding
//         (log_arity == 1 for the arity-2 single-round-set folding here).
//       * verifier.rs:254  challenger.check_witness(query_proof_of_work_bits,
//         proof.query_pow_witness) — the query grinding check (grinding_ref.go).
//       * verifier.rs:267-268  index = challenger.sample_bits(
//         log_global_max_height + extra_query_index_bits) — the query index is
//         drawn from the challenger, NOT a pre-sampled argument.
//       * verifier.rs:287  domain_index = index >> extra_query_index_bits.
//       * verifier.rs:298  verify_query — the per-query fold chain
//         (verifyFriQueryRef, fri_query_ref.go).
//
// SCOPE. This is the SINGLE-MATRIX (single-round-set) assembly: one input
// codeword committed at the global max height, arity-2 folding, and the
// challenger-driven betas + grinding + query indices wrapped around the landed
// per-query fold gadget. The initial reduced opening (open_input, verifier.rs
// :271) is provided directly per query (InitialEval); the alpha-batched
// multi-height reduced openings, higher arity, realistic blowup, the logup bus
// and the four NPO tables are the named residual (see the RESIDUAL note at the
// bottom of fri_verify_test.go). Accordingly the challenger enters this wrapper
// already positioned past the pre-commit-phase steps (the batch-combination
// alpha sample at verifier.rs:143 and the input openings) — those belong to the
// reduced-opening residual.
package friverifier

// friConfigRef carries the FRI parameters this flow reads from the transcript
// schedule. Values for ir2_leaf_wrap_config (fri/src/config.rs:76-84):
// query_proof_of_work_bits = 16, commit_proof_of_work_bits = 0, log_blowup = 1,
// log_final_poly_len = 0; extra_query_index_bits = 0 for TwoAdicFriFolding
// (fri/src/two_adic_pcs.rs:105). This single-matrix assembly is exercised at
// log_blowup = log_final_poly_len = 0 (final domain is a single point), the same
// scope as the landed per-query fold fixture.
type friConfigRef struct {
	QueryPowBits        int // params.query_proof_of_work_bits (verifier.rs:254)
	CommitPowBits       int // params.commit_proof_of_work_bits (verifier.rs:222)
	ExtraQueryIndexBits int // folding.extra_query_index_bits() (two_adic_pcs.rs:105)
	LogBlowup           int // params.log_blowup
	LogFinalPolyLen     int // params.log_final_poly_len
}

// friQueryOpeningRef is one query's opening data: the initial reduced-opening
// seed f0[index] and, per commit round, the sibling evaluation + Merkle path.
// The query INDEX is NOT carried here — it is drawn from the challenger during
// verification (verifier.rs:268), which is the whole point of the assembly.
type friQueryOpeningRef struct {
	InitialEval  bbExtRef        // f0[domain_index] (open_input result, provided)
	Siblings     []bbExtRef      // [R] one arity-2 partner per round
	MerkleProofs [][][8]uint32   // [R][lfh_r][8] bottom-up sibling digests
}

// friProofRef is the single-matrix FRI proof the flow verifies: the commit-phase
// Merkle roots, the final polynomial (length 2^LogFinalPolyLen; a single
// constant in this scope), the query grinding witness, and the per-query
// openings. R = number of commit rounds. The betas and query indices are absent
// by design — the verifier re-derives them from the transcript.
type friProofRef struct {
	R           int
	CommitRoots [][8]uint32          // [R]
	FinalPoly   []bbExtRef           // [2^LogFinalPolyLen]
	PowWitness  uint32               // query_pow_witness
	Queries     []friQueryOpeningRef // params.num_queries of them
}

// verifyFriRef drives the transcript exactly as verify_fri (verifier.rs:113) for
// the arity-2 single-round-set case, then runs the per-query fold chain. `c` is
// the challenger positioned at the commit phase (see the SCOPE note). Returns
// true iff every query's fold chain verifies against the transcript-derived
// betas + index and the grinding check passes.
func verifyFriRef(c *challengerRef, cfg friConfigRef, p *friProofRef) bool {
	return verifyFriRefImpl(c, cfg, p, false)
}

// verifyFriRefImpl is verifyFriRef with a test-only order flag. swapOrder=false
// is the shipped, fork-faithful order (observe root THEN sample beta,
// verifier.rs:221 then :225). swapOrder=true samples beta BEFORE observing the
// root — the transcript-order canary in fri_verify_test.go feeds a VALID proof
// through swapOrder=true and requires a REJECT, proving the interleave is
// load-bearing. Only the commit-phase interleave differs; every other step is
// identical, so the canary isolates exactly the observe/sample order.
func verifyFriRefImpl(c *challengerRef, cfg friConfigRef, p *friProofRef, swapOrder bool) bool {
	R := p.R

	// Commit phase (verifier.rs:214-227): observe root_r, check the commit PoW
	// (0 bits in ir2 -> no-op, no transcript advance), sample beta_r. Betas are
	// built in-transcript.
	betas := make([]bbExtRef, R)
	for r := 0; r < R; r++ {
		if swapOrder {
			// WRONG order (canary): sample before observing -> divergent betas.
			betas[r] = c.sampleExt()
			c.observeSlice(p.CommitRoots[r][:])
		} else {
			c.observeSlice(p.CommitRoots[r][:]) // verifier.rs:221 observe(comm)
			if !c.checkWitness(cfg.CommitPowBits, 0) {
				return false // verifier.rs:222-224 (0 bits: always true)
			}
			betas[r] = c.sampleExt() // verifier.rs:225 sample_algebra_element
		}
	}

	// verifier.rs:238 observe_algebra_slice(&final_poly): absorb each coefficient's
	// base coordinates in order.
	for _, coeff := range p.FinalPoly {
		c.observeSlice(coeff[:])
	}

	// verifier.rs:249-251 observe the arity schedule (log_arity 1 per arity-2 round).
	for r := 0; r < R; r++ {
		c.observe(1)
	}

	// verifier.rs:254 query PoW grinding.
	if !c.checkWitness(cfg.QueryPowBits, p.PowWitness) {
		return false
	}

	logGlobalMaxHeight := R + cfg.LogBlowup + cfg.LogFinalPolyLen
	for _, q := range p.Queries {
		// verifier.rs:268 index = sample_bits(log_global_max_height + extra).
		index := c.sampleBits(logGlobalMaxHeight + cfg.ExtraQueryIndexBits)
		// verifier.rs:287 domain_index = index >> extra.
		domainIndex := index >> uint(cfg.ExtraQueryIndexBits)

		fx := &friQueryFixture{
			R:            R,
			CommitRoots:  p.CommitRoots,
			Betas:        betas,
			Siblings:     q.Siblings,
			MerkleProofs: q.MerkleProofs,
			InitialEval:  q.InitialEval,
			// verifier.rs:311-321 final-poly Horner at x = g^rev(domain_index).
			FinalEval: finalPolyEvalRef(p.FinalPoly, domainIndex, logGlobalMaxHeight),
		}
		fx.IndexBits = make([]uint32, R)
		for i := 0; i < R; i++ {
			fx.IndexBits[i] = uint32((domainIndex >> uint(i)) & 1)
		}
		if !verifyFriQueryRef(fx) { // verifier.rs:298 verify_query
			return false
		}
	}
	return true
}

// finalPolyEvalRef evaluates the final polynomial at
// x = two_adic_generator(logGlobalMaxHeight)^reverse_bits_len(domainIndex, .)
// by Horner (verifier.rs:311-321). In this lane's scope log_final_poly_len = 0,
// so final_poly has length 1 and this collapses to final_poly[0] independent of
// x (Horner on a single coefficient). The general form is kept faithful so the
// realistic-blowup residual only needs a longer final_poly, not a rewrite.
func finalPolyEvalRef(finalPoly []bbExtRef, domainIndex uint, logGlobalMaxHeight int) bbExtRef {
	g := twoAdicGeneratorsRef[logGlobalMaxHeight]
	x := bbPowRef(g, uint64(reverseBitsRef(domainIndex, logGlobalMaxHeight)))
	var eval bbExtRef
	for i := len(finalPoly) - 1; i >= 0; i-- {
		eval = bbExtAddRef(bbExtScaleRef(x, eval), finalPoly[i])
	}
	return eval
}
