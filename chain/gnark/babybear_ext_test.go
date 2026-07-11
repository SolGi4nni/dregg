package friverifier

import (
	"math/big"
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// bigExtMul is an independent big.Int model of BabyBear[X]/(X^4 - 11):
// schoolbook polynomial multiplication, wraparound X^4 = 11, coefficients
// mod p.
func bigExtMul(a, b bbExtRef) bbExtRef {
	p := new(big.Int).SetUint64(BabyBearP)
	acc := make([]*big.Int, 4)
	for i := range acc {
		acc[i] = new(big.Int)
	}
	w := big.NewInt(int64(BBExtW))
	for i := 0; i < 4; i++ {
		for j := 0; j < 4; j++ {
			t := new(big.Int).Mul(
				new(big.Int).SetUint64(uint64(a[i])),
				new(big.Int).SetUint64(uint64(b[j])),
			)
			if i+j >= 4 {
				t.Mul(t, w)
				acc[i+j-4].Add(acc[i+j-4], t)
			} else {
				acc[i+j].Add(acc[i+j], t)
			}
		}
	}
	var r bbExtRef
	for i := range r {
		r[i] = uint32(acc[i].Mod(acc[i], p).Uint64())
	}
	return r
}

func randExt(rng *rand.Rand) bbExtRef {
	var e bbExtRef
	for i := range e {
		e[i] = uint32(rng.Uint64() % BabyBearP)
	}
	return e
}

func TestBBExtRefVsMathBig(t *testing.T) {
	rng := rand.New(rand.NewSource(3))
	for i := 0; i < 1000; i++ {
		a, b := randExt(rng), randExt(rng)
		if got, want := bbExtMulRef(a, b), bigExtMul(a, b); got != want {
			t.Fatalf("extMul(%v,%v) = %v, want %v", a, b, got, want)
		}
	}
}

// Known answer pinning the binomial: X^3 · X^3 = X^6 = W·X^2 = 11·X^2.
func TestBBExtBinomialWraparound(t *testing.T) {
	x3 := bbExtRef{0, 0, 0, 1}
	if got := bbExtMulRef(x3, x3); got != (bbExtRef{0, 0, 11, 0}) {
		t.Fatalf("X^3·X^3 = %v, want [0 0 11 0] (X^4 = 11)", got)
	}
	// one · a = a
	one := bbExtRef{1, 0, 0, 0}
	a := bbExtRef{5, 6, 7, 8}
	if got := bbExtMulRef(one, a); got != a {
		t.Fatalf("1·a = %v, want %v", got, a)
	}
}

func TestBBExtRefAddSub(t *testing.T) {
	rng := rand.New(rand.NewSource(4))
	for i := 0; i < 200; i++ {
		a, b := randExt(rng), randExt(rng)
		s := bbExtAddRef(a, b)
		if got := bbExtSubRef(s, b); got != a {
			t.Fatalf("(a+b)-b = %v, want %v", got, a)
		}
		// commutativity of mul
		if bbExtMulRef(a, b) != bbExtMulRef(b, a) {
			t.Fatalf("extMul not commutative on %v, %v", a, b)
		}
	}
}

// --- circuit vs reference ---

type extMulCircuit struct {
	A, B, Want [4]frontend.Variable
}

func (c *extMulCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	a, b := BBExt(c.A), BBExt(c.B)
	bb.ExtAssertIsCanonical(a)
	bb.ExtAssertIsCanonical(b)
	got := bb.ExtMul(a, b)
	bb.ExtAssertIsEqual(got, BBExt(c.Want))
	return nil
}

type extAddSubCircuit struct {
	A, B, WantAdd, WantSub [4]frontend.Variable
}

func (c *extAddSubCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	a, b := BBExt(c.A), BBExt(c.B)
	bb.ExtAssertIsCanonical(a)
	bb.ExtAssertIsCanonical(b)
	bb.ExtAssertIsEqual(bb.ExtAdd(a, b), BBExt(c.WantAdd))
	bb.ExtAssertIsEqual(bb.ExtSub(a, b), BBExt(c.WantSub))
	return nil
}

func toVars(e bbExtRef) [4]frontend.Variable {
	var v [4]frontend.Variable
	for i := range v {
		v[i] = e[i]
	}
	return v
}

func TestBBExtCircuitMatchesReference(t *testing.T) {
	rng := rand.New(rand.NewSource(5))
	field := ecc.BN254.ScalarField()
	cases := []bbExtRef{
		{0, 0, 0, 0},
		{1, 0, 0, 0},
		{0, 0, 0, 1},
		{uint32(BabyBearP) - 1, uint32(BabyBearP) - 1, uint32(BabyBearP) - 1, uint32(BabyBearP) - 1},
	}
	for i := 0; i < 8; i++ {
		cases = append(cases, randExt(rng))
	}
	for i := 0; i+1 < len(cases); i++ {
		a, b := cases[i], cases[i+1]
		w := &extMulCircuit{A: toVars(a), B: toVars(b), Want: toVars(bbExtMulRef(a, b))}
		if err := test.IsSolved(&extMulCircuit{}, w, field); err != nil {
			t.Fatalf("extMul circuit vs ref (%v,%v): %v", a, b, err)
		}
		w2 := &extAddSubCircuit{
			A: toVars(a), B: toVars(b),
			WantAdd: toVars(bbExtAddRef(a, b)),
			WantSub: toVars(bbExtSubRef(a, b)),
		}
		if err := test.IsSolved(&extAddSubCircuit{}, w2, field); err != nil {
			t.Fatalf("extAdd/Sub circuit vs ref (%v,%v): %v", a, b, err)
		}
	}
}

// REJECT polarity: a tampered coefficient and a non-canonical input
// coefficient must both fail.
func TestBBExtCircuitRejects(t *testing.T) {
	field := ecc.BN254.ScalarField()
	a := bbExtRef{123, 456, 789, 1011}
	b := bbExtRef{2021, 2223, 2425, 2627}
	want := bbExtMulRef(a, b)

	tampered := toVars(want)
	tampered[2] = bbAddRef(want[2], 1)
	if err := test.IsSolved(&extMulCircuit{}, &extMulCircuit{A: toVars(a), B: toVars(b), Want: tampered}, field); err == nil {
		t.Fatal("extMul accepted a tampered coefficient")
	}

	badA := toVars(a)
	badA[0] = BabyBearP // non-canonical coefficient
	if err := test.IsSolved(&extMulCircuit{}, &extMulCircuit{A: badA, B: toVars(b), Want: toVars(want)}, field); err == nil {
		t.Fatal("extMul accepted a non-canonical input coefficient")
	}
}
