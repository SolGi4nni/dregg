package friverifier

import (
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// Known-answer vector for default_babybear_poseidon2_16, copied verbatim from
// the plonky3 rev the recursion fork pins:
// baby-bear/src/poseidon2.rs:580-597 (test_default_babybear_poseidon2_width_16)
// at Plonky3 rev 82cfad73cd734d37a0d51953094f970c531817ec.
var poseidon2W16KATInput = [16]uint32{
	894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
	120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
	1783754913,
}

var poseidon2W16KATExpected = [16]uint32{
	516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906,
	563338433, 319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758,
	1052633829, 1344246938,
}

// The reference permutation must reproduce the fork's known-answer vector
// exactly — this pins the round constants, diagonal, S-box, and layer order
// all at once.
func TestPoseidon2W16RefMatchesForkKAT(t *testing.T) {
	state := poseidon2W16KATInput
	poseidon2W16Ref(&state)
	if state != poseidon2W16KATExpected {
		t.Fatalf("reference permutation diverges from the fork KAT:\n got %v\nwant %v",
			state, poseidon2W16KATExpected)
	}
}

// REJECT-polarity for the reference itself: the KAT must be able to fail
// (guard against a vacuous comparison).
func TestPoseidon2W16RefKATBites(t *testing.T) {
	state := poseidon2W16KATInput
	state[0] = bbAddRef(state[0], 1)
	poseidon2W16Ref(&state)
	if state == poseidon2W16KATExpected {
		t.Fatal("tampered input still produced the KAT output")
	}
}

// --- circuit vs reference ---

type poseidon2W16Circuit struct {
	In  [16]frontend.Variable
	Out [16]frontend.Variable
}

func (c *poseidon2W16Circuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	state := c.In
	bb.Poseidon2W16(&state)
	for i := range state {
		api.AssertIsEqual(state[i], c.Out[i])
	}
	return nil
}

func p2Witness(in [16]uint32) *poseidon2W16Circuit {
	out := in
	poseidon2W16Ref(&out)
	w := &poseidon2W16Circuit{}
	for i := range in {
		w.In[i] = in[i]
		w.Out[i] = out[i]
	}
	return w
}

func TestPoseidon2W16CircuitMatchesKATAndRef(t *testing.T) {
	field := ecc.BN254.ScalarField()

	// The KAT through the circuit: In = fork input, Out = fork expected.
	w := &poseidon2W16Circuit{}
	for i := range poseidon2W16KATInput {
		w.In[i] = poseidon2W16KATInput[i]
		w.Out[i] = poseidon2W16KATExpected[i]
	}
	if err := test.IsSolved(&poseidon2W16Circuit{}, w, field); err != nil {
		t.Fatalf("circuit rejects the fork KAT: %v", err)
	}

	// Randomized differential vs the reference.
	rng := rand.New(rand.NewSource(6))
	for k := 0; k < 4; k++ {
		var in [16]uint32
		for i := range in {
			in[i] = uint32(rng.Uint64() % BabyBearP)
		}
		if err := test.IsSolved(&poseidon2W16Circuit{}, p2Witness(in), field); err != nil {
			t.Fatalf("circuit diverges from reference on %v: %v", in, err)
		}
	}

	// Boundary state: all lanes p-1.
	var edge [16]uint32
	for i := range edge {
		edge[i] = uint32(BabyBearP) - 1
	}
	if err := test.IsSolved(&poseidon2W16Circuit{}, p2Witness(edge), field); err != nil {
		t.Fatalf("circuit diverges from reference on all-(p-1): %v", err)
	}
}

// REJECT polarity: a tampered output lane must fail.
func TestPoseidon2W16CircuitRejectsTamperedOutput(t *testing.T) {
	field := ecc.BN254.ScalarField()
	w := p2Witness(poseidon2W16KATInput)
	w.Out[7] = bbAddRef(poseidon2W16KATExpected[7], 1)
	if err := test.IsSolved(&poseidon2W16Circuit{}, w, field); err == nil {
		t.Fatal("circuit accepted a tampered permutation output")
	}
}

// REJECT polarity: a non-canonical input lane must fail the gadget-boundary
// canonicality assertion even if the rest of the witness is self-consistent.
func TestPoseidon2W16CircuitRejectsNonCanonicalInput(t *testing.T) {
	field := ecc.BN254.ScalarField()
	// Build a witness whose Out matches the reference on (p ≡ 0) — i.e. the
	// arithmetic story is consistent mod p — but In[0] = p is not canonical.
	var in [16]uint32
	in[0] = 0
	w := p2Witness(in)
	w.In[0] = BabyBearP
	if err := test.IsSolved(&poseidon2W16Circuit{}, w, field); err == nil {
		t.Fatal("circuit accepted a non-canonical input lane")
	}
}

// The permutation circuit compiles to R1CS (the Groth16 target shape).
func TestPoseidon2W16Compiles(t *testing.T) {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &poseidon2W16Circuit{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	t.Logf("Poseidon2-w16 permutation circuit: %d constraints", cs.GetNbConstraints())
}
