// Plain-Go reference implementation of the degree-4 BabyBear extension
// (X^4 = 11). Mirrors babybear_ext.go; see that file for the plonky3 ground
// truth citations.
package friverifier

// bbExtRef is a degree-4 extension element, coefficients little-endian in X.
type bbExtRef [4]uint32

func bbExtAddRef(a, b bbExtRef) bbExtRef {
	var r bbExtRef
	for i := range r {
		r[i] = bbAddRef(a[i], b[i])
	}
	return r
}

func bbExtSubRef(a, b bbExtRef) bbExtRef {
	var r bbExtRef
	for i := range r {
		r[i] = bbSubRef(a[i], b[i])
	}
	return r
}

func bbExtMulRef(a, b bbExtRef) bbExtRef {
	// Accumulate in uint64: each product < 2^62 is pre-reduced by bbMulRef to
	// < 2^31, so sums stay far below 2^64.
	var acc [4]uint64
	for i := 0; i < 4; i++ {
		for j := 0; j < 4; j++ {
			t := uint64(bbMulRef(a[i], b[j]))
			if i+j >= 4 {
				acc[i+j-4] += t * uint64(BBExtW)
			} else {
				acc[i+j] += t
			}
		}
	}
	var r bbExtRef
	for i := range r {
		r[i] = uint32(acc[i] % BabyBearP)
	}
	return r
}
