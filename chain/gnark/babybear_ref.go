// Plain-Go (non-circuit) reference implementation of BabyBear field
// arithmetic. The circuit gadgets in babybear.go are differentially tested
// against these, and these against math/big.
package friverifier

// bbAddRef returns a + b mod p (inputs canonical).
func bbAddRef(a, b uint32) uint32 {
	s := uint64(a) + uint64(b)
	if s >= BabyBearP {
		s -= BabyBearP
	}
	return uint32(s)
}

// bbSubRef returns a - b mod p (inputs canonical).
func bbSubRef(a, b uint32) uint32 {
	s := uint64(a) + BabyBearP - uint64(b)
	if s >= BabyBearP {
		s -= BabyBearP
	}
	return uint32(s)
}

// bbMulRef returns a · b mod p (inputs canonical; product < 2^62 fits u64).
func bbMulRef(a, b uint32) uint32 {
	return uint32(uint64(a) * uint64(b) % BabyBearP)
}

// bbNegRef returns -a mod p.
func bbNegRef(a uint32) uint32 {
	if a == 0 {
		return 0
	}
	return uint32(BabyBearP) - a
}

// bbPow7Ref returns a^7 mod p — the Poseidon2 S-box
// (BABYBEAR_S_BOX_DEGREE = 7, plonky3 baby-bear/src/poseidon1.rs:38).
func bbPow7Ref(a uint32) uint32 {
	a2 := bbMulRef(a, a)
	a3 := bbMulRef(a2, a)
	a6 := bbMulRef(a3, a3)
	return bbMulRef(a6, a)
}
