// FRI query-phase verification as a gnark circuit gadget — the core low-degree
// test of the native ETH-wrap verifier (tooth 2c of Define, fri_verifier.go).
// For one query it walks the FRI commit rounds: at each round it reconstructs
// the arity-2 sibling group, verifies its Poseidon2 Merkle opening against the
// round's committed root, folds the pair with beta using the fork's exact fold
// formula, steps the index down one bit, and finally asserts the folded value
// equals the claimed final-polynomial evaluation.
//
// This gadget is the in-circuit twin of verifyFriQueryRef (fri_query_ref.go);
// the two are differentially tested. Both are derived from the fork verifier at
// Plonky3 rev 82cfad73cd734d37a0d51953094f970c531817ec — see fri_query_ref.go
// for the full file:line ground-truth map (fold formula: fri/src/two_adic_pcs.rs
// :109 fold_row; Merkle arity: MerkleTreeMmcs<..,2,8> binary + 8-elem digest,
// leaf PaddingFreeSponge<Perm,16,8,8>, node TruncatedPermutation<Perm,2,8,16>;
// query loop: fri/src/verifier.rs:363 verify_query).
//
// SCOPE. This is the SINGLE-ROUND-SET FRI low-degree test: one input matrix
// committed at the global max height, arity-2 (binary) folding, and the fork's
// Merkle-opening + fold + final-poly check. It is the cryptographic core shared
// by every FRI instance. It does NOT yet assemble the full batch-STARK query:
// the per-table degree_bits, the alpha-batched reduced openings across multiple
// heights with beta^arity roll-ins (verifier.rs:271 open_input, :477 roll-in),
// the logup interaction bus, and the four non-primitive op tables. Those are the
// named residual for the next lane (see the RESIDUAL note at the bottom of
// fri_query_test.go). Higher-arity folding (max_log_arity 3 in
// ir2_leaf_wrap_config) reduces to sequential arity-2 folds (two_adic_pcs.rs:160
// fold_matrix else-branch) and is the immediate arity extension.
package friverifier

import "github.com/consensys/gnark/frontend"

// twoAdicGenInvGadget[bits] = inverse of BabyBear::two_adic_generator(bits), the
// same canonical residues as twoAdicGenInvRef, used as circuit CONSTANTS in the
// bit-selected product that forms the fold divisor inv(2s) without any runtime
// field inversion.
var twoAdicGenInvGadget = &twoAdicGenInvRef

// VerifyFriQuery constrains one FRI query's fold chain in-circuit.
//
// Parameters (the pre-sampled query view, matching verify_query's arguments —
// betas and the query index arrive already drawn from the challenger, as in the
// Rust verifier where verify_query receives betas and domain_index):
//   - R: number of commit rounds (structural).
//   - commitRoots[r]: the round-r commit-phase Merkle root (8 BabyBear lanes).
//   - betas[r]: the round-r folding challenge (extension element).
//   - siblings[r]: the round-r sibling evaluation (the one arity-2 partner of
//     the carried value).
//   - merkleProofs[r][l]: the round-r Merkle authentication path (sibling
//     digests, bottom-up); len = lfh_r = R-r-1.
//   - indexBits: the query index, LSB-first, R booleans.
//   - initialEval: the reduced-opening seed f0[index] (Merkle-checked at round 0
//     as one member of that round's sibling group).
//   - finalEval: the claimed final-polynomial value (a single constant for the
//     log_final_poly_len=0 scope).
//
// Every ingested witness is asserted canonical/boolean at the boundary
// (fail-closed). A tampered leaf, sibling digest, beta, or final value yields an
// unsatisfiable constraint system.
func VerifyFriQuery(
	bb *BBApi,
	R int,
	commitRoots [][DigestWidth]frontend.Variable,
	betas []BBExt,
	siblings []BBExt,
	merkleProofs [][][DigestWidth]frontend.Variable,
	indexBits []frontend.Variable,
	initialEval BBExt,
	finalEval BBExt,
) {
	api := bb.api

	// Fail-closed witness ingestion.
	for i := range indexBits {
		api.AssertIsBoolean(indexBits[i])
	}
	bb.ExtAssertIsCanonical(initialEval)
	bb.ExtAssertIsCanonical(finalEval)
	for r := 0; r < R; r++ {
		bb.ExtAssertIsCanonical(betas[r])
		bb.ExtAssertIsCanonical(siblings[r])
		for i := 0; i < DigestWidth; i++ {
			bb.AssertIsCanonical(commitRoots[r][i])
		}
		for l := range merkleProofs[r] {
			for i := 0; i < DigestWidth; i++ {
				bb.AssertIsCanonical(merkleProofs[r][l][i])
			}
		}
	}

	folded := initialEval
	for r := 0; r < R; r++ {
		lfh := R - r - 1
		bR := indexBits[r]

		// Reconstruct the arity-2 sibling group (verifier.rs:422-433). The
		// carried value sits at position index_in_group = b_r; the sibling
		// fills the other slot. e0 = eval at xs[0]=s, e1 = eval at xs[1]=-s.
		var e0, e1 BBExt
		for i := 0; i < 4; i++ {
			e0[i] = api.Select(bR, siblings[r][i], folded[i])
			e1[i] = api.Select(bR, folded[i], siblings[r][i])
		}

		// Verify the Merkle opening against the round's committed root
		// (verifier.rs:447 mmcs.verify_batch).
		digest := friMerkleLeafHash(bb, e0, e1)
		for l := 0; l < lfh; l++ {
			digest = friMerkleCompressStep(bb, digest, merkleProofs[r][l], indexBits[r+1+l])
		}
		for i := 0; i < DigestWidth; i++ {
			api.AssertIsEqual(digest[i], commitRoots[r][i])
		}

		// Fold with beta (verifier.rs:458 fold_row).
		folded = friFoldRowArity2(bb, e0, e1, betas[r], indexBits[r+1:r+1+lfh])
	}

	// Final-polynomial check (verifier.rs:311-324): for the log_final_poly_len=0
	// scope the final domain has size 1 (x = g^0 = 1), so the Horner evaluation
	// collapses to the single constant coefficient.
	bb.ExtAssertIsEqual(folded, finalEval)
}

// friFoldRowArity2 folds one reconstructed arity-2 sibling group with beta —
// the fork's fold_row (fri/src/two_adic_pcs.rs:109) closed form
//
//	folded = (e0 + e1)/2 + beta*(e0 - e1) * inv(2s)
//
// where parentBits are the query-index bits ABOVE this round (indexBits[r+1..]),
// so inv(s) is the bit-selected product of inverse generator constants and
// inv(2s) = (1/2)*inv(s) — no runtime field inversion. This is the SINGLE fold
// code path shared by the emulated verifier (VerifyFriQuery) and the native-hash
// verifier (VerifyFriQueryNative, fri_verify_native.go): the fold is BabyBear
// field arithmetic, untouched by the hash swap.
func friFoldRowArity2(bb *BBApi, e0, e1, beta BBExt, parentBits []frontend.Variable) BBExt {
	api := bb.api
	invS := frontend.Variable(1)
	for j := range parentBits {
		factor := api.Select(parentBits[j], twoAdicGenInvGadget[2+j], 1)
		invS = bb.Mul(invS, factor)
	}
	halfInvS := bb.MulConst(bbInv2, invS) // (1/2)*inv(s)
	sum := bb.ExtAdd(e0, e1)
	diff := bb.ExtSub(e0, e1)
	betaTerm := bb.ExtMul(beta, diff)
	return bb.ExtAdd(
		bb.ExtMulBase(frontend.Variable(bbInv2), sum),
		bb.ExtMulBase(halfInvS, betaTerm),
	)
}

// friMerkleLeafHash hashes a commit-phase leaf row of two extension evals into
// an 8-lane digest via the real width-16 Poseidon2 permutation:
// PaddingFreeSponge<Perm,16,8,8> over the 8 flattened base coordinates
// [e0[0..4], e1[0..4]] with a zero capacity (one full rate-8 block).
func friMerkleLeafHash(bb *BBApi, e0, e1 BBExt) [DigestWidth]frontend.Variable {
	var st [16]frontend.Variable
	for i := 0; i < 4; i++ {
		st[i] = e0[i]
		st[4+i] = e1[i]
	}
	for i := 8; i < 16; i++ {
		st[i] = frontend.Variable(0)
	}
	bb.Poseidon2W16(&st)
	var d [DigestWidth]frontend.Variable
	copy(d[:], st[0:DigestWidth])
	return d
}

// friMerkleCompressStep compresses the running node digest with a sibling digest
// for one Merkle level: TruncatedPermutation<Perm,2,8,16> with the queried node
// at pos_in_group = bit (bit 0 => [node, sibling], bit 1 => [sibling, node]).
func friMerkleCompressStep(
	bb *BBApi,
	node [DigestWidth]frontend.Variable,
	sibling [DigestWidth]frontend.Variable,
	bit frontend.Variable,
) [DigestWidth]frontend.Variable {
	api := bb.api
	var st [16]frontend.Variable
	for i := 0; i < DigestWidth; i++ {
		st[i] = api.Select(bit, sibling[i], node[i])
		st[DigestWidth+i] = api.Select(bit, node[i], sibling[i])
	}
	bb.Poseidon2W16(&st)
	var d [DigestWidth]frontend.Variable
	copy(d[:], st[0:DigestWidth])
	return d
}
