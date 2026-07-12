// NATIVE-HASH single-matrix FRI verifier flow — the first assembled piece of
// the re-architected wrap (docs/deos/WRAP-NATIVE-HASH-DECISION.md) and the
// measured empirical check of its ~1-6M-constraint premise (see
// TestWrapNativeHashConstraintMeasurement in fri_verify_native_test.go).
//
// This is the native-hash TWIN of VerifyFri (fri_verify.go): the SAME flow and
// the SAME fork-faithful observe/sample transcript ORDER (per commit round
// observe root -> commit-PoW -> sample beta; then final poly; arity schedule;
// query grinding; per query sample index -> verify query), with exactly the
// two swaps the wrap decision names:
//
//   - TRANSCRIPT: the emulated BabyBear DuplexChallenger (challenger.go, one
//     emulated Poseidon2W16 per duplexing, ~16,837 R1CS) is replaced by the
//     MultiFieldChallenger (multifield_challenger.go): a NATIVE BN254 width-3
//     duplex sponge (~243 R1CS/permutation) with the fork's MultiField32
//     pack/split adapter. Commit roots are observed as native BN254 digests;
//     betas and query indices are sampled as BabyBear.
//   - MERKLE: the emulated Poseidon2-w16 commit openings (friMerkleLeafHash /
//     friMerkleCompressStep in fri_query.go) are replaced by native BN254
//     Poseidon2 openings (VerifyMerklePathBn254, merkle_bn254.go) — one node =
//     one BN254 element, one level = one ~243-R1CS native compression.
//
// The FOLD ARITHMETIC does NOT move: it is BabyBear field arithmetic (not
// hashing), so it stays on the emulated BabyBear ext-field gadget — literally
// the same code path (friFoldRowArity2, fri_query.go) the emulated verifier
// runs. This is the arithmetic RESIDUAL WRAP-NATIVE-HASH-DECISION.md names as
// untouched by the hash swap.
//
// LEAF PACKING. A commit-phase leaf row (two extension evals = 8 canonical
// BabyBear coordinates) enters the native tree as
// Poseidon2Bn254Compress(pack(e0), pack(e1)), where pack is the injective
// little-endian radix-2^31 packing of 4 canonical coordinates into one BN254
// word (a pure linear combination, zero constraints; injective because each
// canonical coordinate is < 2^31 and 4·31 = 124 < 254 bits). Canonicity of
// every packed coordinate is asserted at the boundary — canonicity is what
// makes the packing injective, hence the leaf binding. The production leaf
// layout is the Rust shrink layer's to define (the named followup in
// merkle_bn254.go); this packing is the measurement-faithful stand-in: one
// native permutation per leaf, matching the one-perm PaddingFreeSponge leaf
// hash of the emulated path.
//
// HONEST SCOPE (mirrors the fri_verify.go scope, plus the shrink-layer gap):
// single-matrix, arity-2, LogFinalPolyLen = 0. This gadget MEASURES the
// native-hash wrap verifier and validates the constraint premise against a
// SYNTHETIC native-hash FRI instance built by the tests — it does NOT yet
// verify a real dregg apex. A real apex verify awaits the Rust shrink layer
// (DreggOuterConfig: re-prove the apex with a BN254-native-hash MMCS +
// MultiField32Challenger, currently blocked in circuit-prove); the measurement
// does not need the shrink layer, the end-to-end real-apex verify does.
package friverifier

import "github.com/consensys/gnark/frontend"

// FriNativeQueryOpening is one query's opening data for the native-hash flow:
// the initial reduced-opening seed and, per commit round, the sibling
// evaluation (BabyBear ext, folded natively) plus the NATIVE Merkle path
// (one BN254 sibling node per level, bottom-up). The query index is drawn from
// the challenger inside VerifyFriNative, not carried here.
type FriNativeQueryOpening struct {
	InitialEval  BBExt
	Siblings     []BBExt
	MerkleProofs [][]frontend.Variable // [R][lfh_r] native sibling nodes
}

// packBBExtToBn254 packs the 4 canonical BabyBear coordinates of one extension
// element into a single native BN254 word, little-endian radix 2^31 — the same
// injective packing discipline as the MultiField absorb (reduce_packed,
// multifield_challenger.go). Pure linear combination: zero constraints.
// Callers must have asserted every coordinate canonical (injectivity).
func packBBExtToBn254(api frontend.API, e BBExt) frontend.Variable {
	acc := frontend.Variable(0)
	base := uint64(1) << mfAbsorbRadixBits
	for i := 3; i >= 0; i-- {
		acc = api.Add(api.Mul(acc, base), e[i])
	}
	return acc
}

// friMerkleLeafHashNative hashes a commit-phase leaf row of two extension
// evals into ONE native BN254 node: compress(pack(e0), pack(e1)) — one native
// permutation, the native twin of friMerkleLeafHash (fri_query.go).
func friMerkleLeafHashNative(api frontend.API, e0, e1 BBExt) frontend.Variable {
	return Poseidon2Bn254Compress(api, packBBExtToBn254(api, e0), packBBExtToBn254(api, e1))
}

// VerifyFriQueryNative constrains one FRI query's fold chain with NATIVE
// Merkle openings — the native-hash twin of VerifyFriQuery (fri_query.go).
// The sibling-group reconstruction, the fold (friFoldRowArity2 — the SAME code
// path as the emulated verifier), and the final-poly check are identical; only
// the commitment opening swaps to VerifyMerklePathBn254.
func VerifyFriQueryNative(
	bb *BBApi,
	R int,
	commitRoots []frontend.Variable, // [R] native BN254 roots
	betas []BBExt,
	siblings []BBExt,
	merkleProofs [][]frontend.Variable, // [R][lfh_r] native sibling nodes
	indexBits []frontend.Variable,
	initialEval BBExt,
	finalEval BBExt,
) {
	api := bb.API()

	// Fail-closed witness ingestion (mirrors VerifyFriQuery). The BabyBear
	// values must be canonical — for the packed leaf, canonicity IS the
	// injectivity of the packing. Native digests need no canonicity: every
	// representable BN254 witness value is canonical.
	for i := range indexBits {
		api.AssertIsBoolean(indexBits[i])
	}
	bb.ExtAssertIsCanonical(initialEval)
	bb.ExtAssertIsCanonical(finalEval)
	for r := 0; r < R; r++ {
		bb.ExtAssertIsCanonical(betas[r])
		bb.ExtAssertIsCanonical(siblings[r])
	}

	folded := initialEval
	for r := 0; r < R; r++ {
		lfh := R - r - 1
		bR := indexBits[r]

		// Reconstruct the arity-2 sibling group (verifier.rs:422-433): the
		// carried value sits at position index_in_group = b_r.
		var e0, e1 BBExt
		for i := 0; i < 4; i++ {
			e0[i] = api.Select(bR, siblings[r][i], folded[i])
			e1[i] = api.Select(bR, folded[i], siblings[r][i])
		}

		// NATIVE Merkle opening against the round's committed root: one leaf
		// permutation + lfh native compressions (the emulated path pays one
		// ~16,837-R1CS emulated permutation per step; this pays ~243).
		leaf := friMerkleLeafHashNative(api, e0, e1)
		VerifyMerklePathBn254(api, leaf, merkleProofs[r], indexBits[r+1:r+1+lfh], commitRoots[r])

		// Fold with beta — the shared emulated-BabyBear fold path (the
		// arithmetic residual; the hash swap does not touch it).
		folded = friFoldRowArity2(bb, e0, e1, betas[r], indexBits[r+1:r+1+lfh])
	}

	// Final-polynomial check (LogFinalPolyLen == 0 scope: a single constant).
	bb.ExtAssertIsEqual(folded, finalEval)
}

// CheckWitnessNative enforces the FRI grinding check over the MultiField
// transcript — the native twin of CheckWitness (grinding.go), mirroring
// GrindingChallenger::check_witness (grinding_challenger.rs:40-46): 0 bits is
// a no-op (no observe, no transcript advance); otherwise absorb the witness
// and assert the low powBits bits of the next BabyBear sample are all zero.
func CheckWitnessNative(c *MultiFieldChallenger, powBits int, witness frontend.Variable) {
	if powBits == 0 {
		return
	}
	c.ObserveBabyBear(witness)
	bits := c.SampleBitsDecomposed(powBits)
	for _, b := range bits {
		c.api.AssertIsEqual(b, 0)
	}
}

// VerifyFriNative constrains the single-matrix FRI verifier flow with the
// NATIVE-HASH transcript and commitments, drawing the betas and query indices
// from `ch` in the SAME fork-faithful transcript order as VerifyFri. `ch` is
// the MultiField challenger positioned at the commit phase. A tampered
// root/opening/witness/final-poly, or a divergent transcript, yields an
// unsatisfiable constraint system (fail-closed).
func VerifyFriNative(
	bb *BBApi,
	cfg FriConfig,
	R int,
	commitRoots []frontend.Variable, // [R] native BN254 roots
	finalPoly []BBExt,
	powWitness frontend.Variable,
	queries []FriNativeQueryOpening,
	ch *MultiFieldChallenger,
) {
	verifyFriNativeImpl(bb, cfg, R, commitRoots, finalPoly, powWitness, queries, ch, false)
}

// verifyFriNativeImpl is VerifyFriNative with the same test-only order flag as
// verifyFriImpl: swapOrder=true samples the beta BEFORE observing the root, and
// the transcript-order canary requires that to be UNSATISFIABLE on a valid
// proof — the native transcript binds the observe/sample interleave exactly as
// the emulated one does.
func verifyFriNativeImpl(
	bb *BBApi,
	cfg FriConfig,
	R int,
	commitRoots []frontend.Variable,
	finalPoly []BBExt,
	powWitness frontend.Variable,
	queries []FriNativeQueryOpening,
	ch *MultiFieldChallenger,
	swapOrder bool,
) {
	if len(finalPoly) != (1 << cfg.LogFinalPolyLen) {
		panic("VerifyFriNative: len(finalPoly) must equal 2^LogFinalPolyLen")
	}
	if cfg.LogFinalPolyLen != 0 {
		panic("VerifyFriNative: single-round-set scope requires LogFinalPolyLen==0")
	}

	// Commit phase (verifier.rs:214-227): the root is observed as a NATIVE
	// BN254 digest (multi_field_challenger.rs:181 — no PF->F repack detour);
	// the beta is sampled as BabyBear limbs through the MultiField split.
	betas := make([]BBExt, R)
	for r := 0; r < R; r++ {
		if swapOrder {
			betas[r] = ch.SampleBabyBearExt()
			ch.ObserveBn254Digest([]frontend.Variable{commitRoots[r]})
		} else {
			ch.ObserveBn254Digest([]frontend.Variable{commitRoots[r]})     // verifier.rs:221
			CheckWitnessNative(ch, cfg.CommitPowBits, frontend.Variable(0)) // :222 (0 bits: no-op)
			betas[r] = ch.SampleBabyBearExt()                               // verifier.rs:225
		}
	}

	// verifier.rs:238 observe_algebra_slice(&final_poly).
	for _, coeff := range finalPoly {
		ch.ObserveBabyBearExt(coeff)
	}

	// verifier.rs:249-251 observe the arity schedule (log_arity 1 per round).
	for r := 0; r < R; r++ {
		ch.ObserveBabyBear(frontend.Variable(1))
	}

	// verifier.rs:254 query PoW grinding (fail-closed on a bad witness).
	CheckWitnessNative(ch, cfg.QueryPowBits, powWitness)

	// Per query: sample the index, run the native-hash fold chain.
	numIndexBits := R + cfg.LogBlowup + cfg.LogFinalPolyLen + cfg.ExtraQueryIndexBits
	finalEval := finalPoly[0] // LogFinalPolyLen==0: the final domain is a point.
	for _, q := range queries {
		// verifier.rs:268 index = sample_bits(log_global_max_height + extra).
		idxBits := ch.SampleBitsDecomposed(numIndexBits)
		// verifier.rs:287 domain_index = index >> extra: drop the low extra bits.
		domainBits := idxBits[cfg.ExtraQueryIndexBits:]
		VerifyFriQueryNative(bb, R, commitRoots, betas, q.Siblings, q.MerkleProofs,
			domainBits, q.InitialEval, finalEval) // verifier.rs:298 verify_query
	}
}
