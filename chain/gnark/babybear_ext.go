// Degree-4 binomial extension of BabyBear: BabyBear[X] / (X^4 - W) with
// W = 11.
//
// Ground truth (the plonky3 rev pinned by /Users/ember/dev/plonky3-recursion,
// Plonky3 rev 82cfad73cd734d37a0d51953094f970c531817ec):
//   - baby-bear/src/baby_bear.rs:65-66:
//     impl BinomialExtensionData<4> for BabyBearParameters {
//     const W: BabyBear = BabyBear::new(11);
//   - field/src/extension/binomial_extension.rs:677 (binomial_mul):
//     res[i+j]   += a_i * b_j        for i+j <  D
//     res[i+j-D] += a_i * W * b_j    for i+j >= D
//
// i.e. schoolbook multiplication with the wraparound X^4 = W = 11.
package friverifier

import "github.com/consensys/gnark/frontend"

// BBExtW is the binomial constant: X^4 = 11.
const BBExtW = uint32(11)

// BBExt is a degree-4 extension element, coefficients little-endian in X
// (e[0] + e[1]·X + e[2]·X² + e[3]·X³), each a canonical BabyBear variable.
type BBExt [4]frontend.Variable

// ExtFromBase embeds a base-field element as a constant-tail extension element.
func (bb *BBApi) ExtFromBase(a frontend.Variable) BBExt {
	return BBExt{a, 0, 0, 0}
}

// ExtAdd returns a + b coefficient-wise.
func (bb *BBApi) ExtAdd(a, b BBExt) BBExt {
	var r BBExt
	for i := range r {
		r[i] = bb.Add(a[i], b[i])
	}
	return r
}

// ExtSub returns a - b coefficient-wise.
func (bb *BBApi) ExtSub(a, b BBExt) BBExt {
	var r BBExt
	for i := range r {
		r[i] = bb.Sub(a[i], b[i])
	}
	return r
}

// ExtMulBase returns s·a for a base-field scalar s (canonical).
func (bb *BBApi) ExtMulBase(s frontend.Variable, a BBExt) BBExt {
	var r BBExt
	for i := range r {
		r[i] = bb.Mul(s, a[i])
	}
	return r
}

// ExtMul returns a · b in BabyBear[X]/(X^4 - 11), schoolbook:
//
//	c0 = a0·b0 + W·(a1·b3 + a2·b2 + a3·b1)
//	c1 = a0·b1 + a1·b0 + W·(a2·b3 + a3·b2)
//	c2 = a0·b2 + a1·b1 + a2·b0 + W·(a3·b3)
//	c3 = a0·b3 + a1·b2 + a2·b1 + a3·b0
//
// Raw products of canonicals are < 2^62; the widest accumulation is
// c0 < 2^62 + 11·3·2^62 = 34·2^62 < 2^68, so one ReduceBounded(·, 68) per
// coefficient.
func (bb *BBApi) ExtMul(a, b BBExt) BBExt {
	api := bb.api
	var p [4][4]frontend.Variable
	for i := 0; i < 4; i++ {
		for j := 0; j < 4; j++ {
			p[i][j] = api.Mul(a[i], b[j])
		}
	}
	c0 := api.Add(p[0][0], api.Mul(BBExtW, api.Add(p[1][3], p[2][2], p[3][1])))
	c1 := api.Add(p[0][1], p[1][0], api.Mul(BBExtW, api.Add(p[2][3], p[3][2])))
	c2 := api.Add(p[0][2], p[1][1], p[2][0], api.Mul(BBExtW, p[3][3]))
	c3 := api.Add(p[0][3], p[1][2], p[2][1], p[3][0])
	return BBExt{
		bb.ReduceBounded(c0, 68),
		bb.ReduceBounded(c1, 68),
		bb.ReduceBounded(c2, 68),
		bb.ReduceBounded(c3, 68),
	}
}

// ExtAssertIsCanonical constrains every coefficient canonical (fail-closed
// witness ingestion for extension elements).
func (bb *BBApi) ExtAssertIsCanonical(a BBExt) {
	for i := range a {
		bb.AssertIsCanonical(a[i])
	}
}

// ExtAssertIsEqual constrains a == b coefficient-wise.
func (bb *BBApi) ExtAssertIsEqual(a, b BBExt) {
	for i := range a {
		bb.api.AssertIsEqual(a[i], b[i])
	}
}
