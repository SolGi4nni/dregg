// Plain-Go reference implementation of the BabyBear Poseidon2 width-24
// permutation. Reuses the width-generic reference engine (poseidon2PermuteRef)
// from poseidon2_w16_ref.go with the width-24 parameters; anchored to the
// fork's known-answer vector in poseidon2_w24_test.go. See poseidon2_w24.go for
// the plonky3 ground-truth citations.
package friverifier

// poseidon2W24Ref applies the width-24 permutation in place (inputs must be
// canonical).
func poseidon2W24Ref(state *[24]uint32) {
	poseidon2PermuteRef(state[:], poseidon2W24Params)
}
