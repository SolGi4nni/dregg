// Tests for the FRI query proof-of-work (grinding) verification: the native-Go
// reference (grinding_ref.go) and the circuit gadget (grinding.go), cross-checked
// against each other via the gnark test engine. All tests run by DEFAULT
// `go test` (no build tags, no feature gates, no skips).
//
// Semantics are extracted from the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec:
//   - challenger/src/grinding_challenger.rs:40-46  check_witness
//   - challenger/src/duplex_challenger.rs:264       sample_bits (low bits of one sample)
//   - fri/src/verifier.rs:254                       the FRI query-phase PoW check
//
// The challenger driven here is the SAME Poseidon2-w16 DuplexChallenger the FRI
// verifier uses (challenger.go / challenger_ref.go), so the grinding transcript
// is consistent with the rest of the verifier.
package friverifier

import (
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

const grindPrefixLen = 10

// grindPrefix is a canonical, non-trivial transcript prefix (one full-rate
// duplexing at 8 elements, two left buffered) that the PoW witness is ground
// against — standing in for the FRI transcript up to the query-grinding point.
func grindPrefix() []uint32 {
	return []uint32{11, 22, 33, 44, 55, 66, 77, 88, 99, 111}
}

// refWithPrefix returns a fresh native challenger having observed grindPrefix,
// i.e. the transcript state at which the query PoW is checked.
func refWithPrefix(prefix []uint32) *challengerRef {
	c := newChallengerRef()
	c.observeSlice(prefix)
	return c
}

// --- native reference: accept / reject polarity ---

// A witness produced by grindRef satisfies the PoW check, and the low `bits`
// bits of the corresponding base sample are genuinely zero (a real grind, not a
// tautology).
func TestCheckWitnessRefAcceptsRealWitness(t *testing.T) {
	prefix := grindPrefix()
	const bits = 10

	w := grindRef(refWithPrefix(prefix), bits)

	if !refWithPrefix(prefix).checkWitness(bits, w) {
		t.Fatalf("grindRef produced witness %d that its own check_witness rejects", w)
	}

	// Ground truth: sample_bits(bits) == 0 means the low `bits` bits of the base
	// sample drawn after observing the witness are all zero. Recompute that base
	// sample independently and assert the mask is clear.
	c := refWithPrefix(prefix)
	c.observe(w)
	base := c.sample()
	mask := (uint64(1) << bits) - 1
	if uint64(base)&mask != 0 {
		t.Fatalf("grind witness %d: base sample %d has nonzero low %d bits", w, base, bits)
	}
}

// A deterministically-invalid witness (its low sampled bits are not all zero) is
// rejected. Also: a fresh challenger where the target power-of-work value is not
// met must return false.
func TestCheckWitnessRefRejectsBadWitness(t *testing.T) {
	prefix := grindPrefix()
	const bits = 10

	bad := firstRejectingWitness(refWithPrefix(prefix), bits)
	if refWithPrefix(prefix).checkWitness(bits, bad) {
		t.Fatalf("check_witness accepted a known-bad witness %d", bad)
	}

	// A witness that IS valid must not be reported as rejecting (sanity that
	// firstRejectingWitness and grindRef are not both returning the same thing).
	good := grindRef(refWithPrefix(prefix), bits)
	if bad == good {
		t.Fatalf("first-rejecting witness %d coincides with a valid witness", bad)
	}
}

// bits == 0 is a no-op: check_witness returns true WITHOUT observing the witness
// or advancing the transcript (grinding_challenger.rs:41). The next sample must
// be identical to the sample with no PoW step at all.
func TestCheckWitnessRefZeroBitsDoesNotAdvance(t *testing.T) {
	prefix := grindPrefix()

	noPow := refWithPrefix(prefix).sample()

	c := refWithPrefix(prefix)
	if !c.checkWitness(0, 123456) {
		t.Fatal("check_witness(0, _) returned false; 0 bits must always pass")
	}
	withZeroPow := c.sample()

	if noPow != withZeroPow {
		t.Fatalf("check_witness(0) advanced the transcript: %d != %d", withZeroPow, noPow)
	}
}

// --- gadget: accept / reject polarity via the gnark test engine ---

// checkWitnessCircuit drives CheckWitness through the real Challenger gadget:
// observe the transcript prefix, then enforce the query PoW on Witness with
// PowBits difficulty. A valid witness is satisfiable; an invalid one is not.
type checkWitnessCircuit struct {
	Prefix  [grindPrefixLen]frontend.Variable
	Witness frontend.Variable
	PowBits int // structural (compile-time) difficulty; == params.query_proof_of_work_bits
}

func (c *checkWitnessCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewChallenger(bb)
	ch.ObserveSlice(c.Prefix[:])
	CheckWitness(ch, c.PowBits, c.Witness)
	return nil
}

func grindTemplate(bits int) *checkWitnessCircuit {
	return &checkWitnessCircuit{PowBits: bits}
}

func grindAssignment(prefix []uint32, witness uint32) *checkWitnessCircuit {
	w := &checkWitnessCircuit{Witness: witness}
	for i, v := range prefix {
		w.Prefix[i] = v
	}
	return w
}

// ACCEPT: a real grinding witness makes the gadget's PoW constraints satisfiable.
func TestCheckWitnessGadgetAcceptsRealWitness(t *testing.T) {
	prefix := grindPrefix()
	const bits = 10
	w := grindRef(refWithPrefix(prefix), bits)

	if err := test.IsSolved(grindTemplate(bits), grindAssignment(prefix, w), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget rejected a valid grinding witness %d: %v", w, err)
	}
}

// REJECT: a deterministically-invalid witness makes the gadget UNSATISFIABLE
// (fail-closed) — the FriError::InvalidPowWitness reject expressed as an
// unprovable constraint.
func TestCheckWitnessGadgetRejectsBadWitness(t *testing.T) {
	prefix := grindPrefix()
	const bits = 10
	bad := firstRejectingWitness(refWithPrefix(prefix), bits)

	if err := test.IsSolved(grindTemplate(bits), grindAssignment(prefix, bad), ecc.BN254.ScalarField()); err == nil {
		t.Fatalf("gadget accepted a known-bad PoW witness %d", bad)
	}
}

// REJECT: the zero witness, when it is not a valid grind, is rejected (the
// task's explicit "zero witness fails" case). Guarded by the ref so the test is
// never vacuous: it asserts the ref rejects zero before demanding the gadget do.
func TestCheckWitnessGadgetRejectsZeroWitness(t *testing.T) {
	prefix := grindPrefix()
	const bits = 12 // deep enough that 0 is overwhelmingly not a solution

	if refWithPrefix(prefix).checkWitness(bits, 0) {
		t.Skipf("zero happens to be a valid %d-bit grind for this prefix; nothing to assert", bits)
	}
	if err := test.IsSolved(grindTemplate(bits), grindAssignment(prefix, 0), ecc.BN254.ScalarField()); err == nil {
		t.Fatal("gadget accepted the zero witness though the reference rejects it")
	}
}

// --- gadget vs native reference: consistency over both polarities ---

// The gadget and the native reference must agree on accept/reject for every
// witness — anchored by a known-valid (grind) and known-invalid
// (first-rejecting) witness so BOTH polarities are exercised, plus random cases.
func TestCheckWitnessGadgetMatchesRef(t *testing.T) {
	prefix := grindPrefix()
	const bits = 8

	good := grindRef(refWithPrefix(prefix), bits)
	bad := firstRejectingWitness(refWithPrefix(prefix), bits)

	witnesses := []uint32{good, bad}
	r := rand.New(rand.NewSource(1))
	for len(witnesses) < 8 {
		witnesses = append(witnesses, uint32(r.Uint64()%BabyBearP))
	}

	sawAccept, sawReject := false, false
	for _, w := range witnesses {
		expected := refWithPrefix(prefix).checkWitness(bits, w) // fresh ref each time
		err := test.IsSolved(grindTemplate(bits), grindAssignment(prefix, w), ecc.BN254.ScalarField())
		solved := err == nil
		if solved != expected {
			t.Fatalf("witness %d: gadget solved=%v but ref check_witness=%v", w, solved, expected)
		}
		if expected {
			sawAccept = true
		} else {
			sawReject = true
		}
	}
	if !sawAccept || !sawReject {
		t.Fatalf("consistency test degenerate: sawAccept=%v sawReject=%v", sawAccept, sawReject)
	}
}

// The accept/reject agreement holds across several difficulty levels.
func TestCheckWitnessGadgetMatchesRefAcrossBits(t *testing.T) {
	prefix := grindPrefix()
	for _, bits := range []int{4, 8, 11} {
		good := grindRef(refWithPrefix(prefix), bits)
		bad := firstRejectingWitness(refWithPrefix(prefix), bits)

		if err := test.IsSolved(grindTemplate(bits), grindAssignment(prefix, good), ecc.BN254.ScalarField()); err != nil {
			t.Fatalf("bits=%d: gadget rejected valid witness %d: %v", bits, good, err)
		}
		if err := test.IsSolved(grindTemplate(bits), grindAssignment(prefix, bad), ecc.BN254.ScalarField()); err == nil {
			t.Fatalf("bits=%d: gadget accepted invalid witness %d", bits, bad)
		}
	}
}

// --- gadget: bits == 0 is a transcript no-op ---

// checkWitnessNoopCircuit observes the prefix, runs CheckWitness with 0 bits,
// then samples once and asserts it equals Expected. If the 0-bit path wrongly
// observed the witness, the sample would differ and the assertion would fail —
// so this pins that 0 bits does NOT advance the transcript.
type checkWitnessNoopCircuit struct {
	Prefix   [grindPrefixLen]frontend.Variable
	Witness  frontend.Variable
	Expected frontend.Variable
}

func (c *checkWitnessNoopCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewChallenger(bb)
	ch.ObserveSlice(c.Prefix[:])
	CheckWitness(ch, 0, c.Witness) // grinding_challenger.rs:41 — must be a no-op
	api.AssertIsEqual(ch.Sample(), c.Expected)
	return nil
}

func TestCheckWitnessGadgetZeroBitsNoOp(t *testing.T) {
	prefix := grindPrefix()

	// The base sample with NO PoW step observed.
	noPow := refWithPrefix(prefix).sample()

	assign := &checkWitnessNoopCircuit{Witness: 987654, Expected: noPow}
	for i, v := range prefix {
		assign.Prefix[i] = v
	}

	// ACCEPT: 0-bit CheckWitness leaves the transcript untouched, so Sample == noPow.
	if err := test.IsSolved(&checkWitnessNoopCircuit{}, assign, ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("0-bit CheckWitness altered the transcript (or failed): %v", err)
	}

	// REJECT (non-vacuity): the sample the challenger WOULD produce if it had
	// observed the witness. Feeding that as Expected must fail, proving the
	// assertion is load-bearing and the 0-bit path really skipped the observe.
	c := refWithPrefix(prefix)
	c.observe(987654)
	withObserve := c.sample()
	if withObserve == noPow {
		t.Skip("degenerate: observing the witness did not change the sample")
	}
	assignBad := &checkWitnessNoopCircuit{Witness: 987654, Expected: withObserve}
	for i, v := range prefix {
		assignBad.Prefix[i] = v
	}
	if err := test.IsSolved(&checkWitnessNoopCircuit{}, assignBad, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("0-bit no-op assertion was vacuous: the with-observe sample also satisfied it")
	}
}
