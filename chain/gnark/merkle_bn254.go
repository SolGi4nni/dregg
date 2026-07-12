// Native-BN254 Merkle-path opening gadget — the first real code of the wrap
// re-architecture (docs/deos/WRAP-NATIVE-HASH-DECISION.md). It is the native
// twin of the emulated commit-opening walk in fri_query.go
// (friMerkleCompressStep): one level costs one native Poseidon2Bn254Compress
// (~243 R1CS, poseidon2_bn254.go) instead of one emulated Poseidon2W16
// permutation (~16,837 R1CS) — the measured ~69x hashing swing that motivates
// the re-architecture.
//
// Shape: a depth-D binary authentication path. The running node starts at the
// leaf; at level i the path bit steers which side the node sits on
// (bit==0 => node is the LEFT child, sibling right; bit==1 => swapped), and
// the 2-to-1 native compression produces the parent. The final node must equal
// the committed root. This matches the emulated friMerkleCompressStep
// bit-steering convention (pos_in_group = bit) so a port of the FRI query walk
// is a drop-in.
//
// The BabyBear-leaf -> BN254-node packing at the leaf boundary (how a row of
// BabyBear evals becomes the BN254 leaf element) is defined by the Rust shrink
// layer's MMCS leaf hash and implemented by friMerkleLeafHashNative
// (fri_verify_native.go; KATs in fri_leaf_hash_kat_test.go); this gadget takes
// the leaf as a native field element.
package friverifier

import "github.com/consensys/gnark/frontend"

// ComputeMerkleRootBn254 walks a depth-D authentication path bottom-up and
// returns the reconstructed root.
//
//   - leaf: the opened leaf (a native BN254 element).
//   - siblings[i]: the level-i sibling node, bottom-up.
//   - pathBits[i]: the level-i index bit (LSB-first — bit i of the leaf index).
//     Each is CONSTRAINED boolean here (fail-closed witness ingestion): a
//     non-boolean "bit" would otherwise let a prover blend node and sibling.
//
// len(siblings) must equal len(pathBits); the mismatch is structural (a
// circuit-construction bug, not a witness), so it panics at compile time.
func ComputeMerkleRootBn254(
	api frontend.API,
	leaf frontend.Variable,
	siblings []frontend.Variable,
	pathBits []frontend.Variable,
) frontend.Variable {
	if len(siblings) != len(pathBits) {
		panic("ComputeMerkleRootBn254: siblings/pathBits length mismatch")
	}
	node := leaf
	for i := range siblings {
		api.AssertIsBoolean(pathBits[i])
		// bit==0: node is the left child; bit==1: swapped.
		left := api.Select(pathBits[i], siblings[i], node)
		right := api.Select(pathBits[i], node, siblings[i])
		node = Poseidon2Bn254Compress(api, left, right)
	}
	return node
}

// VerifyMerklePathBn254 constrains a depth-D opening: the path reconstruction
// from (leaf, siblings, pathBits) must equal root. A tampered leaf, a wrong
// sibling, a flipped path bit, or a corrupted root each make the constraint
// system unsatisfiable.
func VerifyMerklePathBn254(
	api frontend.API,
	leaf frontend.Variable,
	siblings []frontend.Variable,
	pathBits []frontend.Variable,
	root frontend.Variable,
) {
	api.AssertIsEqual(ComputeMerkleRootBn254(api, leaf, siblings, pathBits), root)
}
