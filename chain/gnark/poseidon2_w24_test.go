package friverifier

import (
	"math/big"
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// Known-answer vector for default_babybear_poseidon2_24, copied verbatim from
// the plonky3 rev the recursion fork pins:
// baby-bear/src/poseidon2.rs:600-619 (test_default_babybear_poseidon2_width_24)
// at Plonky3 rev 82cfad73cd734d37a0d51953094f970c531817ec.
//
// NOTE: the fork's input[20] = 2026927696 is > p (BabyBear::new_array reduces
// mod p when constructing the field element). We reduce it to its canonical
// residue here so the gadget-boundary canonicality assertion holds; the field
// element — and therefore the expected output — is unchanged.
var poseidon2W24KATInputRaw = [24]uint32{
	886409618, 1327899896, 1902407911, 591953491, 648428576, 1844789031, 1198336108,
	355597330, 1799586834, 59617783, 790334801, 1968791836, 559272107, 31054313,
	1042221543, 474748436, 135686258, 263665994, 1962340735, 1741539604, 2026927696,
	449439011, 1131357108, 50869465,
}

var poseidon2W24KATExpected = [24]uint32{
	882297297, 1264077610, 512812497, 782602970, 867738552, 1251075457, 309180082,
	340784773, 524041877, 351272188, 404451680, 15001466, 322926653, 1773004150,
	1718440818, 674682955, 1154713225, 1719133502, 324232301, 1005243141, 443371079,
	268735940, 770060019, 718377682,
}

func poseidon2W24KATInput() [24]uint32 {
	in := poseidon2W24KATInputRaw
	for i := range in {
		in[i] = uint32(uint64(in[i]) % BabyBearP)
	}
	return in
}

// The reference permutation must reproduce the fork's known-answer vector
// exactly — this pins the round constants, diagonal, S-box, and layer order all
// at once.
func TestPoseidon2W24RefMatchesForkKAT(t *testing.T) {
	state := poseidon2W24KATInput()
	poseidon2W24Ref(&state)
	if state != poseidon2W24KATExpected {
		t.Fatalf("reference permutation diverges from the fork KAT:\n got %v\nwant %v",
			state, poseidon2W24KATExpected)
	}
}

// REJECT-polarity for the reference itself: the KAT must be able to fail (guard
// against a vacuous comparison).
func TestPoseidon2W24RefKATBites(t *testing.T) {
	state := poseidon2W24KATInput()
	state[0] = bbAddRef(state[0], 1)
	poseidon2W24Ref(&state)
	if state == poseidon2W24KATExpected {
		t.Fatal("tampered input still produced the KAT output")
	}
}

// --- independent math/big recompute of the whole permutation ---

// w24DiagSpec mirrors the V vector at baby-bear/src/poseidon2.rs:405 as
// (signed numerator, power-of-two denominator exponent). Used to derive the
// diagonal residues independently of the poseidon2W24Diag literals, so a
// mistyped literal is caught even without the fork KAT.
var w24DiagSpec = [24]struct {
	num int64
	e   uint
}{
	{-2, 0}, {1, 0}, {2, 0}, {1, 1}, {3, 0}, {4, 0}, {-1, 1}, {-3, 0}, {-4, 0},
	{1, 8}, {1, 2}, {1, 3}, {1, 4}, {1, 7}, {1, 9}, {1, 27},
	{-1, 8}, {-1, 2}, {-1, 3}, {-1, 4}, {-1, 5}, {-1, 6}, {-1, 7}, {-1, 27},
}

func w24DiagBig(pBig *big.Int) [24]*big.Int {
	var d [24]*big.Int
	for i, s := range w24DiagSpec {
		num := big.NewInt(s.num)
		num.Mod(num, pBig)
		if s.e > 0 {
			pow := new(big.Int).Lsh(big.NewInt(1), s.e) // 2^e
			pow.ModInverse(pow, pBig)
			num.Mul(num, pow)
			num.Mod(num, pBig)
		}
		d[i] = num
	}
	return d
}

// poseidon2W24Big is a numerically independent (math/big) reimplementation of
// the width-24 permutation, sharing no code with poseidon2W24Ref beyond the
// hex RC tables. Used as a differential oracle.
func poseidon2W24Big(state *[24]uint32) {
	pBig := new(big.Int).SetUint64(BabyBearP)
	diag := w24DiagBig(pBig)
	s := make([]*big.Int, 24)
	for i := range s {
		s[i] = new(big.Int).SetUint64(uint64(state[i]))
	}
	mod := func(x *big.Int) *big.Int { return x.Mod(x, pBig) }
	addC := func(a *big.Int, c uint32) *big.Int {
		return mod(new(big.Int).Add(a, new(big.Int).SetUint64(uint64(c))))
	}
	pow7 := func(a *big.Int) *big.Int {
		r := new(big.Int).Set(a)
		for k := 0; k < 6; k++ {
			r.Mul(r, a)
			mod(r)
		}
		return r
	}
	mat4 := func(x []*big.Int) {
		row := func(c0, c1, c2, c3 int64) *big.Int {
			r := new(big.Int)
			r.Add(r, new(big.Int).Mul(x[0], big.NewInt(c0)))
			r.Add(r, new(big.Int).Mul(x[1], big.NewInt(c1)))
			r.Add(r, new(big.Int).Mul(x[2], big.NewInt(c2)))
			r.Add(r, new(big.Int).Mul(x[3], big.NewInt(c3)))
			return mod(r)
		}
		// M4 = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]
		y0 := row(2, 3, 1, 1)
		y1 := row(1, 2, 3, 1)
		y2 := row(1, 1, 2, 3)
		y3 := row(3, 1, 1, 2)
		x[0], x[1], x[2], x[3] = y0, y1, y2, y3
	}
	mdsLight := func() {
		for c := 0; c+4 <= 24; c += 4 {
			mat4(s[c : c+4])
		}
		var sums [4]*big.Int
		for k := 0; k < 4; k++ {
			acc := new(big.Int)
			for j := k; j < 24; j += 4 {
				acc.Add(acc, s[j])
			}
			sums[k] = mod(acc)
		}
		for i := 0; i < 24; i++ {
			s[i] = mod(new(big.Int).Add(s[i], sums[i%4]))
		}
	}
	external := func(rcs []uint32) {
		for i := 0; i < 24; i++ {
			s[i] = pow7(addC(s[i], rcs[i]))
		}
		mdsLight()
	}
	internal := func(rc uint32) {
		s[0] = pow7(addC(s[0], rc))
		full := new(big.Int)
		for i := 0; i < 24; i++ {
			full.Add(full, s[i])
		}
		mod(full)
		for i := 0; i < 24; i++ {
			t := new(big.Int).Mul(diag[i], s[i])
			t.Add(t, full)
			s[i] = mod(t)
		}
	}

	mdsLight()
	for r := 0; r < 4; r++ {
		external(poseidon2W24RCExternalInitial[r][:])
	}
	for r := 0; r < 21; r++ {
		internal(poseidon2W24RCInternal[r])
	}
	for r := 0; r < 4; r++ {
		external(poseidon2W24RCExternalFinal[r][:])
	}
	for i := range state {
		state[i] = uint32(s[i].Uint64())
	}
}

func TestPoseidon2W24RefMatchesBigInt(t *testing.T) {
	rng := rand.New(rand.NewSource(24))
	for k := 0; k < 8; k++ {
		var in [24]uint32
		for i := range in {
			in[i] = uint32(rng.Uint64() % BabyBearP)
		}
		got := in
		want := in
		poseidon2W24Ref(&got)
		poseidon2W24Big(&want)
		if got != want {
			t.Fatalf("ref diverges from math/big on %v:\n ref %v\n big %v", in, got, want)
		}
	}
	// The big oracle must itself reproduce the fork KAT (proves the oracle is
	// not co-broken with the ref).
	kat := poseidon2W24KATInput()
	poseidon2W24Big(&kat)
	if kat != poseidon2W24KATExpected {
		t.Fatalf("math/big oracle diverges from the fork KAT:\n got %v\nwant %v", kat, poseidon2W24KATExpected)
	}
}

// The internal diagonal in poseidon2W24Diag must equal the residues derived
// from the V spec (guards the hand-transcribed literals directly).
func TestPoseidon2W24DiagResidues(t *testing.T) {
	pBig := new(big.Int).SetUint64(BabyBearP)
	want := w24DiagBig(pBig)
	for i := range poseidon2W24Diag {
		if uint64(poseidon2W24Diag[i]) != want[i].Uint64() {
			t.Fatalf("diag[%d] = %d, spec says %d", i, poseidon2W24Diag[i], want[i].Uint64())
		}
	}
}

// --- circuit vs reference ---

type poseidon2W24Circuit struct {
	In  [24]frontend.Variable
	Out [24]frontend.Variable
}

func (c *poseidon2W24Circuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	state := c.In
	bb.Poseidon2W24(&state)
	for i := range state {
		api.AssertIsEqual(state[i], c.Out[i])
	}
	return nil
}

func p2W24Witness(in [24]uint32) *poseidon2W24Circuit {
	out := in
	poseidon2W24Ref(&out)
	w := &poseidon2W24Circuit{}
	for i := range in {
		w.In[i] = in[i]
		w.Out[i] = out[i]
	}
	return w
}

func TestPoseidon2W24CircuitMatchesKATAndRef(t *testing.T) {
	field := ecc.BN254.ScalarField()

	// The KAT through the circuit: In = fork input (canonicalized), Out = fork
	// expected.
	katIn := poseidon2W24KATInput()
	w := &poseidon2W24Circuit{}
	for i := range katIn {
		w.In[i] = katIn[i]
		w.Out[i] = poseidon2W24KATExpected[i]
	}
	if err := test.IsSolved(&poseidon2W24Circuit{}, w, field); err != nil {
		t.Fatalf("circuit rejects the fork KAT: %v", err)
	}

	// Randomized differential vs the reference.
	rng := rand.New(rand.NewSource(2400))
	for k := 0; k < 4; k++ {
		var in [24]uint32
		for i := range in {
			in[i] = uint32(rng.Uint64() % BabyBearP)
		}
		if err := test.IsSolved(&poseidon2W24Circuit{}, p2W24Witness(in), field); err != nil {
			t.Fatalf("circuit diverges from reference on %v: %v", in, err)
		}
	}

	// Boundary state: all lanes p-1.
	var edge [24]uint32
	for i := range edge {
		edge[i] = uint32(BabyBearP) - 1
	}
	if err := test.IsSolved(&poseidon2W24Circuit{}, p2W24Witness(edge), field); err != nil {
		t.Fatalf("circuit diverges from reference on all-(p-1): %v", err)
	}

	// Boundary state: all lanes zero.
	var zero [24]uint32
	if err := test.IsSolved(&poseidon2W24Circuit{}, p2W24Witness(zero), field); err != nil {
		t.Fatalf("circuit diverges from reference on all-zero: %v", err)
	}
}

// REJECT polarity: a tampered output lane must fail.
func TestPoseidon2W24CircuitRejectsTamperedOutput(t *testing.T) {
	field := ecc.BN254.ScalarField()
	w := p2W24Witness(poseidon2W24KATInput())
	w.Out[13] = bbAddRef(poseidon2W24KATExpected[13], 1)
	if err := test.IsSolved(&poseidon2W24Circuit{}, w, field); err == nil {
		t.Fatal("circuit accepted a tampered permutation output")
	}
}

// REJECT polarity: a non-canonical input lane must fail the gadget-boundary
// canonicality assertion even if the rest of the witness is self-consistent.
func TestPoseidon2W24CircuitRejectsNonCanonicalInput(t *testing.T) {
	field := ecc.BN254.ScalarField()
	// Out matches the reference on (p ≡ 0) — the arithmetic story is consistent
	// mod p — but In[0] = p is not canonical.
	var in [24]uint32
	in[0] = 0
	w := p2W24Witness(in)
	w.In[0] = BabyBearP
	if err := test.IsSolved(&poseidon2W24Circuit{}, w, field); err == nil {
		t.Fatal("circuit accepted a non-canonical input lane")
	}
}

// The permutation circuit compiles to R1CS (the Groth16 target shape).
func TestPoseidon2W24Compiles(t *testing.T) {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &poseidon2W24Circuit{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	t.Logf("Poseidon2-w24 permutation circuit: %d constraints", cs.GetNbConstraints())
}
