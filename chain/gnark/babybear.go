// BabyBear field gadget over the BN254 scalar field.
//
// Each BabyBear element is carried as ONE BN254 witness variable holding its
// canonical residue (< BabyBearP). This is the favorable "small modulus inside
// a big field" regime (docs/deos/ETH-NATIVE-WRAP.md §2b): a BN254 product of
// two canonical operands is < 2^62 ≪ 2^254, so reduction is a hinted (q, r)
// decomposition x = q·p + r with r range-checked canonical and q range-checked
// small — no limb decomposition of the host field.
//
// Soundness of ReduceBounded: with q < 2^qBits (qBits ≤ 38 here) and r < p,
// q·p + r < 2^69 ≪ the BN254 modulus, so the constraint x == q·p + r cannot
// wrap and pins (q, r) to the unique Euclidean decomposition of x.
package friverifier

import (
	"errors"
	"math/big"

	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/rangecheck"
)

// BabyBearP is the prime p = 2^31 - 2^27 + 1 = 2013265921.
const BabyBearP = uint64(2013265921)

var bbPBig = new(big.Int).SetUint64(BabyBearP)

func init() {
	solver.RegisterHint(bbDivModHint)
}

// bbDivModHint computes (q, r) with in = q·BabyBearP + r, 0 ≤ r < BabyBearP.
// The hint output is UNTRUSTED; ReduceBounded constrains it.
func bbDivModHint(_ *big.Int, inputs, outputs []*big.Int) error {
	if len(inputs) != 1 || len(outputs) != 2 {
		return errors.New("bbDivModHint: expected 1 input, 2 outputs")
	}
	if inputs[0].Sign() < 0 {
		return errors.New("bbDivModHint: negative input")
	}
	q, r := new(big.Int).DivMod(inputs[0], bbPBig, new(big.Int))
	outputs[0].Set(q)
	outputs[1].Set(r)
	return nil
}

// BBApi provides BabyBear field arithmetic over a gnark frontend.API.
// All exported ops take and return CANONICAL residues (< BabyBearP).
type BBApi struct {
	api frontend.API
	rc  frontend.Rangechecker
}

// NewBBApi builds the BabyBear gadget context for one circuit.
func NewBBApi(api frontend.API) *BBApi {
	return &BBApi{api: api, rc: rangecheck.New(api)}
}

// API returns the underlying frontend.API (for raw, bound-tracked arithmetic).
func (bb *BBApi) API() frontend.API { return bb.api }

// AssertIsCanonical constrains v < BabyBearP (fail-closed: a witness holding
// p, or anything in [p, 2^31), or anything larger, is rejected).
//
// Both checks are needed: v < 2^31 alone admits [p, 2^31); (p-1)-v ∈ [0, 2^31)
// alone admits huge v near the BN254 modulus where the subtraction wraps back
// into range. Together they pin v ∈ [0, p).
func (bb *BBApi) AssertIsCanonical(v frontend.Variable) {
	bb.rc.Check(v, 31)
	bb.rc.Check(bb.api.Sub(BabyBearP-1, v), 31)
}

// FromCanonicalU32 is the witness-ingestion helper: it asserts v < BabyBearP
// (2013265921) and returns v as a canonical BabyBear element.
func (bb *BBApi) FromCanonicalU32(v frontend.Variable) frontend.Variable {
	bb.AssertIsCanonical(v)
	return v
}

// ReduceBounded canonicalizes x mod BabyBearP, given the STATIC caller
// obligation that x < 2^boundBits by construction (the caller tracks bounds of
// raw sums/products; every call site in this package documents its bound).
// boundBits must be ≤ 100 (we never get close; products of canonicals are
// < 2^62 and our widest accumulation is < 2^68).
func (bb *BBApi) ReduceBounded(x frontend.Variable, boundBits uint) frontend.Variable {
	if boundBits < 31 {
		boundBits = 31
	}
	if boundBits > 100 {
		panic("ReduceBounded: bound too large; audit the call site")
	}
	res, err := bb.api.Compiler().NewHint(bbDivModHint, 2, x)
	if err != nil {
		panic(err)
	}
	q, r := res[0], res[1]
	// x == q*p + r, with q,r range-pinned below. No BN254 wrap possible:
	// q < 2^(boundBits-30) ≤ 2^70 and r < 2^31, so q*p + r < 2^102 ≪ 2^254.
	bb.api.AssertIsEqual(x, bb.api.Add(bb.api.Mul(q, BabyBearP), r))
	bb.AssertIsCanonical(r)
	if boundBits <= 31 {
		// x < 2^31 < 2p ⇒ q ∈ {0, 1}.
		bb.api.AssertIsBoolean(q)
	} else {
		// q = ⌊x/p⌋ < 2^boundBits / 2^30 = 2^(boundBits-30).
		bb.rc.Check(q, int(boundBits-30))
	}
	return r
}

// Add returns a + b mod p (inputs canonical).
func (bb *BBApi) Add(a, b frontend.Variable) frontend.Variable {
	return bb.ReduceBounded(bb.api.Add(a, b), 32)
}

// Sub returns a - b mod p (inputs canonical): a + (p - b) < 2p + p ≤ 2^32.
func (bb *BBApi) Sub(a, b frontend.Variable) frontend.Variable {
	return bb.ReduceBounded(bb.api.Add(a, bb.api.Sub(BabyBearP, b)), 32)
}

// Mul returns a · b mod p (inputs canonical; raw product < 2^62).
func (bb *BBApi) Mul(a, b frontend.Variable) frontend.Variable {
	return bb.ReduceBounded(bb.api.Mul(a, b), 62)
}

// MulConst returns c · a mod p for a fixed canonical constant c.
func (bb *BBApi) MulConst(c uint32, a frontend.Variable) frontend.Variable {
	if uint64(c) >= BabyBearP {
		panic("MulConst: constant not canonical")
	}
	return bb.ReduceBounded(bb.api.Mul(c, a), 62)
}
