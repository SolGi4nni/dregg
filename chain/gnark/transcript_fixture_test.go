// Fixture integration: the Rust transcript emitter vs the Go Poseidon2 side.
//
// fixtures/transcript_w16.json is emitted by the Rust lane from the EXACT
// challenger the dregg verifier uses (p3_challenger::DuplexChallenger<BabyBear,
// Poseidon2BabyBear<16>, WIDTH=16, RATE=8> at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec). This file replays the fixture's
// absorb/squeeze protocol through BOTH the plain-Go reference permutation and
// the circuit gadget (gnark test engine) and demands byte-for-byte equality
// with the Rust-emitted challenges. This is the load-bearing transcript
// fidelity check of ETH-NATIVE-WRAP §4: the Rust fixture is the ORACLE; on a
// mismatch the Go side is what gets fixed.
//
// Duplex protocol ground truth (challenger/src/duplex_challenger.rs at the
// pinned rev): observe clears the output buffer and pushes to the input
// buffer; when RATE inputs are buffered a duplexing fires — the inputs
// OVERWRITE state[0..RATE] (capacity untouched), the width-16 permutation is
// applied, and the output buffer becomes state[0..RATE]; sample duplexes iff
// the input buffer is non-empty or the output buffer is empty, then POPS FROM
// THE END of the output buffer.
package friverifier

import (
	"encoding/json"
	"os"
	"strconv"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

const transcriptFixturePath = "fixtures/transcript_w16.json"

type transcriptFixture struct {
	Field            string   `json:"field"`
	Modulus          string   `json:"modulus"`
	Width            int      `json:"width"`
	Rate             int      `json:"rate"`
	Absorbed         []string `json:"absorbed"`
	Challenges       []string `json:"challenges"`
	FinalSpongeState []string `json:"final_sponge_state"`
}

// loadTranscriptFixture parses the fixture fail-closed: a missing file, a
// non-canonical value, or an off-contract shape is a test FAILURE, never a
// skip.
func loadTranscriptFixture(t *testing.T) *transcriptFixture {
	t.Helper()
	raw, err := os.ReadFile(transcriptFixturePath)
	if err != nil {
		t.Fatalf("transcript fixture must exist (Rust lane emits it): %v", err)
	}
	fx := &transcriptFixture{}
	if err := json.Unmarshal(raw, fx); err != nil {
		t.Fatalf("fixture JSON: %v", err)
	}
	if fx.Field != "BabyBear" || fx.Modulus != strconv.FormatUint(BabyBearP, 10) {
		t.Fatalf("fixture field/modulus mismatch: field=%q modulus=%q", fx.Field, fx.Modulus)
	}
	if fx.Width != 16 || fx.Rate != 8 {
		t.Fatalf("fixture sponge shape mismatch: width=%d rate=%d (want 16/8)", fx.Width, fx.Rate)
	}
	if len(fx.Absorbed) != 16 || len(fx.Challenges) != 8 || len(fx.FinalSpongeState) != 16 {
		t.Fatalf("fixture lengths: absorbed=%d challenges=%d final_state=%d (want 16/8/16)",
			len(fx.Absorbed), len(fx.Challenges), len(fx.FinalSpongeState))
	}
	return fx
}

// parseCanonical parses a decimal fixture value and asserts it is a canonical
// BabyBear residue (fail-closed on the fixture itself).
func parseCanonical(t *testing.T, s string) uint32 {
	t.Helper()
	v, err := strconv.ParseUint(s, 10, 64)
	if err != nil {
		t.Fatalf("fixture value %q: %v", s, err)
	}
	if v >= BabyBearP {
		t.Fatalf("fixture value %s is not a canonical BabyBear residue (p = %d)", s, BabyBearP)
	}
	return uint32(v)
}

func parseCanonicalSlice(t *testing.T, ss []string) []uint32 {
	t.Helper()
	out := make([]uint32, len(ss))
	for i, s := range ss {
		out[i] = parseCanonical(t, s)
	}
	return out
}

// --- plain-Go duplex challenger replay (mirrors duplex_challenger.rs) ---

type duplexChallengerRef struct {
	state  [16]uint32
	inBuf  []uint32
	outBuf []uint32
}

const duplexRate = 8

func (d *duplexChallengerRef) duplexing() {
	if len(d.inBuf) > duplexRate {
		panic("duplexing: input buffer overflow")
	}
	// Inputs OVERWRITE state[0..len(inBuf)]; capacity lanes untouched.
	copy(d.state[:], d.inBuf)
	d.inBuf = d.inBuf[:0]
	poseidon2W16Ref(&d.state)
	d.outBuf = append(d.outBuf[:0], d.state[:duplexRate]...)
}

func (d *duplexChallengerRef) observe(v uint32) {
	d.outBuf = d.outBuf[:0] // any buffered output is now invalid
	d.inBuf = append(d.inBuf, v)
	if len(d.inBuf) == duplexRate {
		d.duplexing()
	}
}

func (d *duplexChallengerRef) sample() uint32 {
	if len(d.inBuf) > 0 || len(d.outBuf) == 0 {
		d.duplexing()
	}
	v := d.outBuf[len(d.outBuf)-1]
	d.outBuf = d.outBuf[:len(d.outBuf)-1]
	return v
}

// replayTranscriptRef runs the fixture protocol: observe every absorbed value,
// then sample n challenges. Returns the challenges and the final sponge state.
func replayTranscriptRef(absorbed []uint32, n int) ([]uint32, [16]uint32) {
	d := &duplexChallengerRef{}
	for _, v := range absorbed {
		d.observe(v)
	}
	out := make([]uint32, n)
	for i := range out {
		out[i] = d.sample()
	}
	return out, d.state
}

// The reference replay must reproduce the Rust-emitted challenges AND the full
// final sponge state (capacity lanes included) byte for byte.
func TestTranscriptFixtureRefReplayMatchesRust(t *testing.T) {
	fx := loadTranscriptFixture(t)
	absorbed := parseCanonicalSlice(t, fx.Absorbed)
	wantChal := parseCanonicalSlice(t, fx.Challenges)
	wantState := parseCanonicalSlice(t, fx.FinalSpongeState)

	gotChal, gotState := replayTranscriptRef(absorbed, len(wantChal))
	for i := range wantChal {
		if gotChal[i] != wantChal[i] {
			t.Errorf("challenge[%d]: go=%d rust=%d", i, gotChal[i], wantChal[i])
		}
	}
	for i := range wantState {
		if gotState[i] != wantState[i] {
			t.Errorf("final_sponge_state[%d]: go=%d rust=%d", i, gotState[i], wantState[i])
		}
	}
}

// Internal-consistency pin: the fixture's own challenges must be the reversed
// tail of its final rate section (sample pops from the END of the output
// buffer). Catches a Rust emitter whose two fields drift apart.
func TestTranscriptFixtureChallengesAreReversedRate(t *testing.T) {
	fx := loadTranscriptFixture(t)
	chal := parseCanonicalSlice(t, fx.Challenges)
	state := parseCanonicalSlice(t, fx.FinalSpongeState)
	for i := range chal {
		if chal[i] != state[duplexRate-1-i] {
			t.Errorf("challenges[%d]=%d != final_sponge_state[%d]=%d",
				i, chal[i], duplexRate-1-i, state[duplexRate-1-i])
		}
	}
}

// REJECT canary: the comparison must be able to fail — a tampered absorbed
// value may NOT still produce the Rust challenges.
func TestTranscriptFixtureRefReplayBites(t *testing.T) {
	fx := loadTranscriptFixture(t)
	absorbed := parseCanonicalSlice(t, fx.Absorbed)
	wantChal := parseCanonicalSlice(t, fx.Challenges)

	absorbed[0] = bbAddRef(absorbed[0], 1)
	gotChal, _ := replayTranscriptRef(absorbed, len(wantChal))
	same := true
	for i := range wantChal {
		if gotChal[i] != wantChal[i] {
			same = false
			break
		}
	}
	if same {
		t.Fatal("tampered absorb still reproduced the Rust challenges (vacuous comparison)")
	}
}

// --- circuit replay (gnark test engine) ---

// transcriptW16Circuit replays the fixture protocol in-circuit: two duplexing
// steps (16 observes at rate 8) through the Poseidon2W16 gadget, then asserts
// the sampled challenges (reversed rate section) and the FULL final sponge
// state — capacity lanes included — equal the Rust-emitted values.
type transcriptW16Circuit struct {
	Absorbed   [16]frontend.Variable
	Challenges [8]frontend.Variable
	FinalState [16]frontend.Variable
}

func (c *transcriptW16Circuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	var state [16]frontend.Variable
	for i := range state {
		state[i] = 0 // fresh challenger: sponge_state = [0; 16]
	}
	for block := 0; block < 2; block++ {
		// Duplexing: the 8 buffered observes OVERWRITE state[0..8]; capacity
		// state[8..16] carries over. Poseidon2W16 asserts every lane canonical
		// (fail-closed on non-canonical absorbed witnesses).
		for i := 0; i < duplexRate; i++ {
			state[i] = c.Absorbed[block*duplexRate+i]
		}
		bb.Poseidon2W16(&state)
	}
	// sample() pops from the end of the output buffer = state[0..8].
	for i := 0; i < duplexRate; i++ {
		api.AssertIsEqual(state[duplexRate-1-i], c.Challenges[i])
	}
	for i := range state {
		api.AssertIsEqual(state[i], c.FinalState[i])
	}
	return nil
}

func transcriptWitnessFromFixture(t *testing.T, fx *transcriptFixture) *transcriptW16Circuit {
	t.Helper()
	w := &transcriptW16Circuit{}
	for i, v := range parseCanonicalSlice(t, fx.Absorbed) {
		w.Absorbed[i] = v
	}
	for i, v := range parseCanonicalSlice(t, fx.Challenges) {
		w.Challenges[i] = v
	}
	for i, v := range parseCanonicalSlice(t, fx.FinalSpongeState) {
		w.FinalState[i] = v
	}
	return w
}

// The circuit gadget must accept the Rust fixture verbatim.
func TestTranscriptFixtureCircuitMatchesRust(t *testing.T) {
	fx := loadTranscriptFixture(t)
	w := transcriptWitnessFromFixture(t, fx)
	if err := test.IsSolved(&transcriptW16Circuit{}, w, ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("circuit transcript replay diverges from the Rust challenger: %v", err)
	}
}

// REJECT polarity: a tampered challenge lane must fail in-circuit.
func TestTranscriptFixtureCircuitRejectsTamperedChallenge(t *testing.T) {
	fx := loadTranscriptFixture(t)
	w := transcriptWitnessFromFixture(t, fx)
	w.Challenges[0] = bbAddRef(parseCanonical(t, fx.Challenges[0]), 1)
	if err := test.IsSolved(&transcriptW16Circuit{}, w, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("circuit accepted a tampered challenge")
	}
}

// REJECT polarity: a tampered CAPACITY lane of the final state must fail —
// the capacity is what chains transcript security between duplexings.
func TestTranscriptFixtureCircuitRejectsTamperedCapacity(t *testing.T) {
	fx := loadTranscriptFixture(t)
	w := transcriptWitnessFromFixture(t, fx)
	w.FinalState[15] = bbAddRef(parseCanonical(t, fx.FinalSpongeState[15]), 1)
	if err := test.IsSolved(&transcriptW16Circuit{}, w, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("circuit accepted a tampered capacity lane")
	}
}

// REJECT polarity: a non-canonical absorbed lane (p ≡ 0 mod p, arithmetically
// consistent with the fixture's absorbed[0] = 0) must be rejected by the
// gadget-boundary canonicality assertion.
func TestTranscriptFixtureCircuitRejectsNonCanonicalAbsorb(t *testing.T) {
	fx := loadTranscriptFixture(t)
	if parseCanonical(t, fx.Absorbed[0]) != 0 {
		t.Fatalf("fixture absorbed[0] = %s; this reject test aliases 0 with p and needs it to be 0",
			fx.Absorbed[0])
	}
	w := transcriptWitnessFromFixture(t, fx)
	w.Absorbed[0] = BabyBearP
	if err := test.IsSolved(&transcriptW16Circuit{}, w, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("circuit accepted a non-canonical absorbed lane")
	}
}

// --- gnark_witness_minimal.json: the 25-lane public-input contract ---

type minimalWitnessFixture struct {
	Version         int    `json:"version"`
	EnvelopeVersion int    `json:"envelope_version"`
	VkAnchorHex     string `json:"vk_anchor_hex"`
	Publics         struct {
		GenesisRoot []uint64 `json:"genesis_root"`
		FinalRoot   []uint64 `json:"final_root"`
		NumTurns    uint64   `json:"num_turns"`
		ChainDigest []uint64 `json:"chain_digest"`
	} `json:"publics"`
	PublicInputVector []string `json:"public_input_vector"`
}

// The Rust-emitted flat vector must equal the pinned 25-lane order
// genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8],
// with every lane a canonical BabyBear residue. This is the same order the
// Publics struct (fri_verifier.go) and the Solidity ABI pin.
func TestMinimalWitnessFixturePinnedLaneOrder(t *testing.T) {
	raw, err := os.ReadFile("fixtures/gnark_witness_minimal.json")
	if err != nil {
		t.Fatalf("minimal witness fixture must exist (Rust lane emits it): %v", err)
	}
	fx := &minimalWitnessFixture{}
	if err := json.Unmarshal(raw, fx); err != nil {
		t.Fatalf("fixture JSON: %v", err)
	}
	if len(fx.Publics.GenesisRoot) != 8 || len(fx.Publics.FinalRoot) != 8 || len(fx.Publics.ChainDigest) != 8 {
		t.Fatalf("digest widths: genesis=%d final=%d chain=%d (want 8/8/8)",
			len(fx.Publics.GenesisRoot), len(fx.Publics.FinalRoot), len(fx.Publics.ChainDigest))
	}
	want := make([]uint64, 0, 25)
	want = append(want, fx.Publics.GenesisRoot...)
	want = append(want, fx.Publics.FinalRoot...)
	want = append(want, fx.Publics.NumTurns)
	want = append(want, fx.Publics.ChainDigest...)

	if len(fx.PublicInputVector) != 25 {
		t.Fatalf("public_input_vector has %d lanes; the pinned contract is 25", len(fx.PublicInputVector))
	}
	if NumPublicInputs != 25 {
		t.Fatalf("NumPublicInputs = %d; the pinned contract is 25", NumPublicInputs)
	}
	for i, s := range fx.PublicInputVector {
		v := uint64(parseCanonical(t, s))
		if v != want[i] {
			t.Errorf("lane %d: flat vector=%d, pinned order says %d", i, v, want[i])
		}
	}
}
