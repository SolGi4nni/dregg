// Plain-Go reference implementation of the BabyBear Poseidon2 width-16
// permutation. Mirrors poseidon2_w16.go step for step; anchored to the fork's
// known-answer vector in poseidon2_w16_test.go. See poseidon2_w16.go for the
// plonky3 ground-truth citations.
package friverifier

// poseidon2W16Ref applies the width-16 permutation in place (inputs must be
// canonical).
func poseidon2W16Ref(state *[16]uint32) {
	poseidon2PermuteRef(state[:], poseidon2W16Params)
}

func poseidon2PermuteRef(state []uint32, p *poseidon2Params) {
	if len(state) != p.width || p.width%4 != 0 {
		panic("poseidon2PermuteRef: bad state width")
	}
	mdsLightRef(state)
	for _, rcs := range p.rcExternalInitial {
		externalRoundRef(state, rcs)
	}
	for _, rc := range p.rcInternal {
		internalRoundRef(state, rc, p.diag)
	}
	for _, rcs := range p.rcExternalFinal {
		externalRoundRef(state, rcs)
	}
}

func externalRoundRef(state []uint32, rcs []uint32) {
	for i := range state {
		state[i] = bbPow7Ref(bbAddRef(state[i], rcs[i]))
	}
	mdsLightRef(state)
}

func internalRoundRef(state []uint32, rc uint32, diag []uint32) {
	state[0] = bbPow7Ref(bbAddRef(state[0], rc))
	var partSum uint32
	for i := 1; i < len(state); i++ {
		partSum = bbAddRef(partSum, state[i])
	}
	fullSum := bbAddRef(partSum, state[0])
	state[0] = bbSubRef(partSum, state[0]) // V[0] = -2
	for i := 1; i < len(state); i++ {
		state[i] = bbAddRef(bbMulRef(diag[i], state[i]), fullSum)
	}
}

func mdsLightRef(state []uint32) {
	w := len(state)
	for c := 0; c+4 <= w; c += 4 {
		mat4Ref(state[c : c+4])
	}
	var sums [4]uint32
	for k := 0; k < 4; k++ {
		s := uint32(0)
		for j := k; j < w; j += 4 {
			s = bbAddRef(s, state[j])
		}
		sums[k] = s
	}
	for i := range state {
		state[i] = bbAddRef(state[i], sums[i%4])
	}
}

// mat4Ref multiplies a 4-slice by M4 = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]].
func mat4Ref(x []uint32) {
	t01 := bbAddRef(x[0], x[1])
	t23 := bbAddRef(x[2], x[3])
	t0123 := bbAddRef(t01, t23)
	t01123 := bbAddRef(t0123, x[1])
	t01233 := bbAddRef(t0123, x[3])
	x3 := bbAddRef(t01233, bbAddRef(x[0], x[0]))
	x1 := bbAddRef(t01123, bbAddRef(x[2], x[2]))
	x0 := bbAddRef(t01123, t01)
	x2 := bbAddRef(t01233, t23)
	x[0], x[1], x[2], x[3] = x0, x1, x2, x3
}
