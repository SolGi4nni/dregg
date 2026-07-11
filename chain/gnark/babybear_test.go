package friverifier

import (
	"math/big"
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// --- reference vs math/big ---

func TestBBRefVsMathBig(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	p := new(big.Int).SetUint64(BabyBearP)
	for i := 0; i < 5000; i++ {
		a := uint32(rng.Uint64() % BabyBearP)
		b := uint32(rng.Uint64() % BabyBearP)
		ba := new(big.Int).SetUint64(uint64(a))
		bb := new(big.Int).SetUint64(uint64(b))

		wantAdd := new(big.Int).Add(ba, bb)
		wantAdd.Mod(wantAdd, p)
		if got := bbAddRef(a, b); uint64(got) != wantAdd.Uint64() {
			t.Fatalf("add(%d,%d) = %d, want %d", a, b, got, wantAdd)
		}

		wantSub := new(big.Int).Sub(ba, bb)
		wantSub.Mod(wantSub, p)
		if got := bbSubRef(a, b); uint64(got) != wantSub.Uint64() {
			t.Fatalf("sub(%d,%d) = %d, want %d", a, b, got, wantSub)
		}

		wantMul := new(big.Int).Mul(ba, bb)
		wantMul.Mod(wantMul, p)
		if got := bbMulRef(a, b); uint64(got) != wantMul.Uint64() {
			t.Fatalf("mul(%d,%d) = %d, want %d", a, b, got, wantMul)
		}

		wantPow7 := new(big.Int).Exp(ba, big.NewInt(7), p)
		if got := bbPow7Ref(a); uint64(got) != wantPow7.Uint64() {
			t.Fatalf("pow7(%d) = %d, want %d", a, got, wantPow7)
		}
	}
}

// --- circuit gadgets vs reference, via the gnark test engine ---

type bbCanonicalCircuit struct {
	X frontend.Variable
}

func (c *bbCanonicalCircuit) Define(api frontend.API) error {
	NewBBApi(api).FromCanonicalU32(c.X)
	return nil
}

func TestBBFromCanonicalU32Accepts(t *testing.T) {
	for _, x := range []uint64{0, 1, 1 << 27, BabyBearP - 1} {
		if err := test.IsSolved(&bbCanonicalCircuit{}, &bbCanonicalCircuit{X: x}, ecc.BN254.ScalarField()); err != nil {
			t.Fatalf("canonical %d rejected: %v", x, err)
		}
	}
}

// REJECT polarity: p itself, the [p, 2^31) gap, 2^31, and a huge BN254 value
// whose (p-1)-x wraps back small must all fail the range check.
func TestBBFromCanonicalU32Rejects(t *testing.T) {
	huge := new(big.Int).Sub(ecc.BN254.ScalarField(), big.NewInt(5))
	cases := []interface{}{
		BabyBearP,         // exactly p
		BabyBearP + 12345, // in [p, 2^31)
		uint64(1) << 31,   // 2^31
		uint64(1) << 40,   // far out
		huge,              // BN254-modulus - 5: (p-1)-x wraps to p+4 < 2^31
	}
	for _, x := range cases {
		if err := test.IsSolved(&bbCanonicalCircuit{}, &bbCanonicalCircuit{X: x}, ecc.BN254.ScalarField()); err == nil {
			t.Fatalf("non-canonical %v was ACCEPTED", x)
		}
	}
}

type bbAddCircuit struct {
	A, B, Want frontend.Variable
}

func (c *bbAddCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	got := bb.Add(bb.FromCanonicalU32(c.A), bb.FromCanonicalU32(c.B))
	api.AssertIsEqual(got, c.Want)
	return nil
}

type bbSubCircuit struct {
	A, B, Want frontend.Variable
}

func (c *bbSubCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	got := bb.Sub(bb.FromCanonicalU32(c.A), bb.FromCanonicalU32(c.B))
	api.AssertIsEqual(got, c.Want)
	return nil
}

type bbMulCircuit struct {
	A, B, Want frontend.Variable
}

func (c *bbMulCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	got := bb.Mul(bb.FromCanonicalU32(c.A), bb.FromCanonicalU32(c.B))
	api.AssertIsEqual(got, c.Want)
	return nil
}

func TestBBCircuitOpsMatchReference(t *testing.T) {
	rng := rand.New(rand.NewSource(2))
	field := ecc.BN254.ScalarField()
	// boundary-heavy corpus + random
	pairs := [][2]uint32{
		{0, 0}, {0, 1}, {1, 0},
		{uint32(BabyBearP) - 1, uint32(BabyBearP) - 1},
		{uint32(BabyBearP) - 1, 1}, {1, uint32(BabyBearP) - 1},
	}
	for i := 0; i < 25; i++ {
		pairs = append(pairs, [2]uint32{
			uint32(rng.Uint64() % BabyBearP), uint32(rng.Uint64() % BabyBearP),
		})
	}
	for _, pr := range pairs {
		a, b := pr[0], pr[1]
		if err := test.IsSolved(&bbAddCircuit{}, &bbAddCircuit{A: a, B: b, Want: bbAddRef(a, b)}, field); err != nil {
			t.Fatalf("add(%d,%d): %v", a, b, err)
		}
		if err := test.IsSolved(&bbSubCircuit{}, &bbSubCircuit{A: a, B: b, Want: bbSubRef(a, b)}, field); err != nil {
			t.Fatalf("sub(%d,%d): %v", a, b, err)
		}
		if err := test.IsSolved(&bbMulCircuit{}, &bbMulCircuit{A: a, B: b, Want: bbMulRef(a, b)}, field); err != nil {
			t.Fatalf("mul(%d,%d): %v", a, b, err)
		}
	}
}

// REJECT polarity: a wrong result must not satisfy the circuit; in particular
// the NON-canonical representative want+p of the true result must be rejected
// (this is exactly what the canonical-reduction gadget is for).
func TestBBCircuitOpsRejectWrongAndNonCanonicalResults(t *testing.T) {
	field := ecc.BN254.ScalarField()
	a, b := uint32(BabyBearP)-2, uint32(BabyBearP)-3

	wrongAdd := uint64(bbAddRef(a, b)) + 1
	if err := test.IsSolved(&bbAddCircuit{}, &bbAddCircuit{A: a, B: b, Want: wrongAdd}, field); err == nil {
		t.Fatal("add accepted a wrong result")
	}
	// want + p: same residue class, non-canonical representative.
	aliasAdd := uint64(bbAddRef(a, b)) + BabyBearP
	if err := test.IsSolved(&bbAddCircuit{}, &bbAddCircuit{A: a, B: b, Want: aliasAdd}, field); err == nil {
		t.Fatal("add accepted a non-canonical alias of the result")
	}
	wrongMul := uint64(bbMulRef(a, b)) + 1
	if err := test.IsSolved(&bbMulCircuit{}, &bbMulCircuit{A: a, B: b, Want: wrongMul}, field); err == nil {
		t.Fatal("mul accepted a wrong result")
	}
	aliasMul := uint64(bbMulRef(a, b)) + BabyBearP
	if err := test.IsSolved(&bbMulCircuit{}, &bbMulCircuit{A: a, B: b, Want: aliasMul}, field); err == nil {
		t.Fatal("mul accepted a non-canonical alias of the result")
	}
	wrongSub := uint64(bbSubRef(a, b)) + 1
	if err := test.IsSolved(&bbSubCircuit{}, &bbSubCircuit{A: a, B: b, Want: wrongSub}, field); err == nil {
		t.Fatal("sub accepted a wrong result")
	}
}

// REJECT polarity: non-canonical OPERANDS are refused by FromCanonicalU32
// even when the asserted result would be arithmetically consistent mod p.
func TestBBCircuitOpsRejectNonCanonicalOperands(t *testing.T) {
	field := ecc.BN254.ScalarField()
	// a = p ≡ 0, so a*b ≡ 0: result is consistent mod p, but the operand is
	// not canonical and must be rejected.
	if err := test.IsSolved(&bbMulCircuit{}, &bbMulCircuit{A: BabyBearP, B: 7, Want: 0}, field); err == nil {
		t.Fatal("mul accepted a non-canonical operand")
	}
	if err := test.IsSolved(&bbAddCircuit{}, &bbAddCircuit{A: BabyBearP, B: 7, Want: 7}, field); err == nil {
		t.Fatal("add accepted a non-canonical operand")
	}
}
