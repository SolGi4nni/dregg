package friverifier

import (
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// matchedCircuitWitness builds a Circuit witness whose ExposedSegment matches
// the publics lane for lane in the pinned 25-lane order.
func matchedCircuitWitness(rng *rand.Rand) *Circuit {
	w := &Circuit{}
	lane := func() uint32 { return uint32(rng.Uint64() % BabyBearP) }
	k := 0
	for i := 0; i < DigestWidth; i++ {
		v := lane()
		w.GenesisRoot[i] = v
		w.Root.ExposedSegment[k] = v
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		v := lane()
		w.FinalRoot[i] = v
		w.Root.ExposedSegment[k] = v
		k++
	}
	nt := lane()
	w.NumTurns = nt
	w.Root.ExposedSegment[k] = nt
	k++
	for i := 0; i < DigestWidth; i++ {
		v := lane()
		w.ChainDigest[i] = v
		w.Root.ExposedSegment[k] = v
		k++
	}
	return w
}

// The compiled circuit exposes EXACTLY the pinned 25 public-input lanes
// (plus gnark's constant ONE wire).
func TestCircuitPublicInputCountIsPinned25(t *testing.T) {
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &Circuit{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	// R1CS counts the constant ONE wire as a public variable.
	if got, want := cs.GetNbPublicVariables(), NumPublicInputs+1; got != want {
		t.Fatalf("public variables = %d, want %d (25 lanes + ONE wire)", got, want)
	}
}

func TestSegmentToothAccepts(t *testing.T) {
	rng := rand.New(rand.NewSource(7))
	w := matchedCircuitWitness(rng)
	if err := test.IsSolved(&Circuit{}, w, ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("matched exposed segment rejected: %v", err)
	}
}

// REJECT polarity: any single-lane mismatch between the exposed segment and
// the publics must fail (tooth 3), across all three regions of the pinned
// order.
func TestSegmentToothRejectsMismatch(t *testing.T) {
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(8))
	for _, lane := range []int{0, DigestWidth, 2 * DigestWidth, 2*DigestWidth + 1, NumPublicInputs - 1} {
		w := matchedCircuitWitness(rng)
		orig := w.Root.ExposedSegment[lane].(uint32)
		w.Root.ExposedSegment[lane] = bbAddRef(orig, 1)
		if err := test.IsSolved(&Circuit{}, w, field); err == nil {
			t.Fatalf("mismatch at lane %d was ACCEPTED", lane)
		}
	}
}

// REJECT polarity: a public lane holding a non-canonical residue (p itself)
// must fail the fail-closed canonicality check even when the exposed segment
// matches it exactly.
func TestPublicsRejectNonCanonicalLane(t *testing.T) {
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(9))

	w := matchedCircuitWitness(rng)
	w.GenesisRoot[0] = BabyBearP
	w.Root.ExposedSegment[0] = BabyBearP
	if err := test.IsSolved(&Circuit{}, w, field); err == nil {
		t.Fatal("non-canonical genesis_root lane was ACCEPTED")
	}

	w = matchedCircuitWitness(rng)
	w.NumTurns = uint64(1) << 33
	w.Root.ExposedSegment[2*DigestWidth] = uint64(1) << 33
	if err := test.IsSolved(&Circuit{}, w, field); err == nil {
		t.Fatal("non-canonical num_turns lane was ACCEPTED")
	}
}
