// THE WRAP END-TO-END (FRI core): gnark verifies a REAL dregg apex's
// BN254-native SHRINK PROOF's FRI layer against the REAL transcript.
//
// fixtures/apex_shrink_fri_real.json is emitted by the Rust lane
// (circuit-prove/tests/apex_shrink_gnark_fixture.rs →
// circuit-prove/src/apex_shrink_gnark_export.rs) from a real 2-turn rotated
// chain folded to an ir2_leaf_wrap apex and re-proven under DreggOuterConfig.
// The Rust exporter SELF-CHECKS before emitting: the real p3 pcs.verify must
// accept from the mirrored transcript state, and the full FRI core must
// re-verify host-side over exactly the exported data. Here the SAME data goes
// through the Go reference twin and the gnark circuit gadget:
//
//  1. the pre-FRI transcript prefix is replayed event-for-event through the
//     MultiField challenger, with every sampled challenge PINNED to the
//     Rust-emitted value (in-circuit AssertIsEqual — transcript agreement on
//     live data, not just KAT vectors);
//  2. VerifyFriNative draws the betas and every query index live and verifies
//     every commit round per query: native BN254 Merkle openings, the arity-2
//     fold, the multi-height roll-ins, the 16-bit query PoW, and the
//     final-polynomial check. (The blowup/query split is read from the
//     fixture — the Rust side owns that rebalance — and must clear the
//     130-conjectured-bit bar.)
//
// HONEST SCOPE (same statement as fri_verify_native.go): this FILE verifies
// the FRI CORE of the real shrink proof — the transcript, commitments, fold
// and grinding — with the reduced openings as fold-seed witnesses. Their
// commitment binding (the open_input derivation) is closed by
// stark_open_input.go and verified in apex_shrink_open_input_test.go; the
// assembled circuit in stark_algebra_real_fixture_test.go wires all layers.
package friverifier

import (
	"encoding/json"
	"math/big"
	"os"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

const shrinkRealFixturePath = "fixtures/apex_shrink_fri_real.json"

// --- fixture schema (mirrors apex_shrink_gnark_export.rs) -------------------

type shrinkFixtureEvent struct {
	Kind   string   `json:"kind"`             // observe_bb | observe_digest | sample_bb
	Values []uint32 `json:"values,omitempty"` // observe_bb / sample_bb
	Words  []string `json:"words,omitempty"`  // observe_digest
}

type shrinkFriShape struct {
	LogBlowup           int `json:"log_blowup"`
	LogFinalPolyLen     int `json:"log_final_poly_len"`
	MaxLogArity         int `json:"max_log_arity"`
	NumQueries          int `json:"num_queries"`
	CommitPowBits       int `json:"commit_pow_bits"`
	QueryPowBits        int `json:"query_pow_bits"`
	ExtraQueryIndexBits int `json:"extra_query_index_bits"`
	Rounds              int `json:"rounds"`
	LogGlobalMaxHeight  int `json:"log_global_max_height"`
}

type shrinkFixtureInputMatrix struct {
	LogHeight     int `json:"log_height"`
	Width         int `json:"width"`
	NumPoints     int `json:"num_points"`
	NextPointBits int `json:"next_point_bits"`
}

type shrinkFixtureInputRound struct {
	Matrices []shrinkFixtureInputMatrix `json:"matrices"`
}

type shrinkFixtureInputBatch struct {
	Rows [][]uint32 `json:"rows"`
	Path []string   `json:"path"`
}

type shrinkFixtureQuery struct {
	ExpectedIndex uint64                    `json:"expected_index"`
	InitialEval   [4]uint32                 `json:"initial_eval"`
	RollIns       [][4]uint32               `json:"roll_ins"`
	Siblings      [][4]uint32               `json:"siblings"`
	MerklePaths   [][]string                `json:"merkle_paths"`
	InputOpenings []shrinkFixtureInputBatch `json:"input_openings"`
}

type shrinkRealFixture struct {
	Version     int    `json:"version"`
	Description string `json:"description"`
	DegreeBits  []int  `json:"degree_bits"`
	// Per-instance table public values (the expose_claim instance carries the
	// re-exposed apex claim — the 25-lane settlement segment ++ the 8-lane
	// root VK spine — FOLLOWED BY the 8 apex VK-core lanes; every other
	// instance is empty).
	TablePublics  [][]uint32 `json:"table_publics"`
	ClaimInstance int        `json:"claim_instance"`
	// The apex's preprocessed commitment (the deployed dregg apex's
	// VK-identity core) — a labeled copy of the claim channel's tail 8 lanes,
	// cross-checked in the loader. This is the value the SettlementCircuit
	// bakes as apexPreprocessedCommit.
	ApexPreprocessedCommit []uint32 `json:"apex_preprocessed_commit"`
	// The turn-chain root's VK spine — a labeled copy of the claim channel's
	// MIDDLE 8 lanes (25..33), cross-checked in the loader. This is the value
	// the SettlementCircuit bakes as rootVkSpine (tooth 3).
	RootVkSpine []uint32       `json:"root_vk_spine"`
	Fri         shrinkFriShape `json:"fri"`
	PrefixEvents    []shrinkFixtureEvent      `json:"prefix_events"`
	CommitRoots     []string                  `json:"commit_roots"`
	ExpectedBetas   [][4]uint32               `json:"expected_betas"`
	FinalPoly       [][4]uint32               `json:"final_poly"`
	QueryPowWitness uint32                    `json:"query_pow_witness"`
	RollInRounds    []int                     `json:"roll_in_rounds"`
	InputRounds     []shrinkFixtureInputRound `json:"input_rounds"`
	Queries         []shrinkFixtureQuery      `json:"queries"`
}

// --- fail-closed loader ------------------------------------------------------

func parseBn254Hex(t *testing.T, s string) fr.Element {
	t.Helper()
	v, ok := new(big.Int).SetString(s, 0)
	if !ok || v.Sign() < 0 || v.Cmp(fr.Modulus()) >= 0 {
		t.Fatalf("fixture BN254 word %q is not a canonical field element", s)
	}
	var e fr.Element
	e.SetBigInt(v)
	return e
}

func requireCanonicalBB(t *testing.T, v uint32, what string) {
	t.Helper()
	if uint64(v) >= BabyBearP {
		t.Fatalf("fixture %s value %d is not a canonical BabyBear residue", what, v)
	}
}

func loadShrinkRealFixture(t *testing.T) *shrinkRealFixture {
	t.Helper()
	raw, err := os.ReadFile(shrinkRealFixturePath)
	if err != nil {
		t.Fatalf("real shrink fixture must exist (Rust lane emits it via "+
			"apex_shrink_gnark_fixture.rs): %v", err)
	}
	fx := &shrinkRealFixture{}
	if err := json.Unmarshal(raw, fx); err != nil {
		t.Fatalf("fixture JSON: %v", err)
	}
	if fx.Version != 5 {
		t.Fatalf("fixture version %d (want 5: exposed 25-lane segment + 8 VK-spine lanes + "+
			"8 apex VK-core lanes)", fx.Version)
	}
	// The settlement claim channel: the expose_claim instance's 25 canonical
	// claim lanes, in the pinned genesis8 ++ final8 ++ numTurns ++
	// chainDigest8 order (fri_verifier.go Publics), followed by the 8 apex
	// VK-core lanes (the apex's preprocessed commitment).
	if len(fx.TablePublics) != len(fx.DegreeBits) {
		t.Fatalf("table_publics has %d instances, degree_bits %d",
			len(fx.TablePublics), len(fx.DegreeBits))
	}
	if fx.ClaimInstance < 0 || fx.ClaimInstance >= len(fx.TablePublics) {
		t.Fatalf("claim_instance %d out of range", fx.ClaimInstance)
	}
	if len(fx.TablePublics[fx.ClaimInstance]) != ExposedShrinkClaimLanes {
		t.Fatalf("claim instance carries %d lanes (want the pinned %d segment + %d VK spine + "+
			"%d apex VK-core = %d)", len(fx.TablePublics[fx.ClaimInstance]),
			NumPublicInputs, VkSpineLanes, ApexVkLanes, ExposedShrinkClaimLanes)
	}
	// The labeled apex VK-core copy IS the claim channel's tail (fail-closed:
	// the value the settlement circuit pins is the one the transcript absorbed
	// and the ExposeClaimAir binds).
	if len(fx.ApexPreprocessedCommit) != ApexVkLanes {
		t.Fatalf("apex_preprocessed_commit has %d lanes (want %d)",
			len(fx.ApexPreprocessedCommit), ApexVkLanes)
	}
	for i, v := range fx.ApexPreprocessedCommit {
		requireCanonicalBB(t, v, "apex VK-core lane")
		// ⚠ offset ApexClaimLanes: the VK core is the channel's TAIL, after the apex's whole
		// claim. At NumPublicInputs this compared the labeled VK core against the SPINE block.
		if got := fx.TablePublics[fx.ClaimInstance][ApexClaimLanes+i]; got != v {
			t.Fatalf("apex_preprocessed_commit[%d] = %d diverges from claim-channel lane %d = %d",
				i, v, ApexClaimLanes+i, got)
		}
	}
	// The labeled root VK-spine copy IS the claim channel's middle block, on the same
	// fail-closed terms as the tail.
	if len(fx.RootVkSpine) != VkSpineLanes {
		t.Fatalf("root_vk_spine has %d lanes (want %d) — a v4 fixture carries none; "+
			"re-export via export_real_shrink_fri_fixture_for_gnark",
			len(fx.RootVkSpine), VkSpineLanes)
	}
	for i, v := range fx.RootVkSpine {
		requireCanonicalBB(t, v, "root VK-spine lane")
		if got := fx.TablePublics[fx.ClaimInstance][NumPublicInputs+i]; got != v {
			t.Fatalf("root_vk_spine[%d] = %d diverges from claim-channel lane %d = %d",
				i, v, NumPublicInputs+i, got)
		}
	}
	for i, pv := range fx.TablePublics {
		for _, v := range pv {
			requireCanonicalBB(t, v, "table public value")
		}
		if i != fx.ClaimInstance && len(pv) != 0 {
			t.Fatalf("instance %d carries unexpected public values (only the claim channel may)", i)
		}
	}
	f := fx.Fri
	// The DreggOuterConfig invariants. The blowup/query split is read from the
	// fixture (the Rust side owns the rebalance) but must clear the 130
	// conjectured-bit bar of the wrap configs.
	if f.LogFinalPolyLen != 0 || f.MaxLogArity != 1 || f.CommitPowBits != 0 ||
		f.QueryPowBits != 16 || f.ExtraQueryIndexBits != 0 || f.LogBlowup < 1 {
		t.Fatalf("fixture FRI shape %+v violates the DreggOuterConfig invariants", f)
	}
	if bits := f.LogBlowup*f.NumQueries + f.QueryPowBits; bits < 130 {
		t.Fatalf("fixture FRI shape yields %d conjectured bits (< 130): %+v", bits, f)
	}
	if f.LogGlobalMaxHeight != f.Rounds+f.LogBlowup+f.LogFinalPolyLen {
		t.Fatalf("log_global_max_height %d != rounds %d + blowup %d",
			f.LogGlobalMaxHeight, f.Rounds, f.LogBlowup)
	}
	if len(fx.CommitRoots) != f.Rounds || len(fx.ExpectedBetas) != f.Rounds {
		t.Fatalf("commit roots/betas length: %d/%d (want %d)",
			len(fx.CommitRoots), len(fx.ExpectedBetas), f.Rounds)
	}
	if len(fx.FinalPoly) != 1 {
		t.Fatalf("final poly length %d (want 1: log_final_poly_len 0)", len(fx.FinalPoly))
	}
	if len(fx.Queries) != f.NumQueries {
		t.Fatalf("query count %d (want %d)", len(fx.Queries), f.NumQueries)
	}
	requireCanonicalBB(t, fx.QueryPowWitness, "pow witness")
	for i, r := range fx.RollInRounds {
		if r < 0 || r >= f.Rounds || (i > 0 && r <= fx.RollInRounds[i-1]) {
			t.Fatalf("roll_in_rounds %v not strictly ascending in [0,%d)", fx.RollInRounds, f.Rounds)
		}
	}
	for qi, q := range fx.Queries {
		if q.ExpectedIndex >= 1<<uint(f.LogGlobalMaxHeight) {
			t.Fatalf("query %d expected index %d out of range", qi, q.ExpectedIndex)
		}
		if len(q.Siblings) != f.Rounds || len(q.MerklePaths) != f.Rounds {
			t.Fatalf("query %d: siblings/paths %d/%d (want %d)",
				qi, len(q.Siblings), len(q.MerklePaths), f.Rounds)
		}
		if len(q.RollIns) != len(fx.RollInRounds) {
			t.Fatalf("query %d: %d roll-ins for %d scheduled rounds",
				qi, len(q.RollIns), len(fx.RollInRounds))
		}
		for r, path := range q.MerklePaths {
			if len(path) != f.LogGlobalMaxHeight-r-1 {
				t.Fatalf("query %d round %d: path depth %d (want %d)",
					qi, r, len(path), f.LogGlobalMaxHeight-r-1)
			}
		}
	}
	for _, ev := range fx.PrefixEvents {
		switch ev.Kind {
		case "observe_bb", "sample_bb":
			for _, v := range ev.Values {
				requireCanonicalBB(t, v, "prefix "+ev.Kind)
			}
			if len(ev.Words) != 0 {
				t.Fatalf("prefix %s event carries digest words", ev.Kind)
			}
		case "observe_digest":
			if len(ev.Words) == 0 || len(ev.Values) != 0 {
				t.Fatal("prefix observe_digest event malformed")
			}
		default:
			t.Fatalf("unknown prefix event kind %q", ev.Kind)
		}
	}
	for _, b := range fx.ExpectedBetas {
		for _, v := range b {
			requireCanonicalBB(t, v, "beta")
		}
	}
	// Input-batch openings (fixture v2, the open_input seam).
	if len(fx.InputRounds) != 4 {
		t.Fatalf("input rounds: %d (want 4: trace, quotient, preprocessed, permutation)",
			len(fx.InputRounds))
	}
	for ri, r := range fx.InputRounds {
		if len(r.Matrices) == 0 {
			t.Fatalf("input round %d has no matrices", ri)
		}
		for mi, m := range r.Matrices {
			if m.LogHeight <= 0 || m.LogHeight > f.LogGlobalMaxHeight {
				t.Fatalf("input round %d matrix %d: log height %d outside (0, %d]",
					ri, mi, m.LogHeight, f.LogGlobalMaxHeight)
			}
			if m.Width <= 0 || (m.NumPoints != 1 && m.NumPoints != 2) {
				t.Fatalf("input round %d matrix %d: width %d / points %d malformed",
					ri, mi, m.Width, m.NumPoints)
			}
			// NextPointBits == 0 is legitimate for a height-1 trace (the
			// expose_claim table: two_adic_generator(0) = 1, zeta_next = zeta).
			if m.NumPoints == 2 && (m.NextPointBits < 0 || m.NextPointBits >= 28) {
				t.Fatalf("input round %d matrix %d: next-point bits %d outside BabyBear two-adicity",
					ri, mi, m.NextPointBits)
			}
		}
	}
	for qi, q := range fx.Queries {
		if len(q.InputOpenings) != len(fx.InputRounds) {
			t.Fatalf("query %d: %d input openings for %d rounds",
				qi, len(q.InputOpenings), len(fx.InputRounds))
		}
		for ri, b := range q.InputOpenings {
			mats := fx.InputRounds[ri].Matrices
			if len(b.Rows) != len(mats) {
				t.Fatalf("query %d input round %d: %d rows for %d matrices",
					qi, ri, len(b.Rows), len(mats))
			}
			maxLh := 0
			for mi, row := range b.Rows {
				if len(row) != mats[mi].Width {
					t.Fatalf("query %d input round %d matrix %d: row width %d != %d",
						qi, ri, mi, len(row), mats[mi].Width)
				}
				for _, v := range row {
					requireCanonicalBB(t, v, "input row")
				}
				if mats[mi].LogHeight > maxLh {
					maxLh = mats[mi].LogHeight
				}
			}
			if len(b.Path) != maxLh {
				t.Fatalf("query %d input round %d: path depth %d != tree height %d",
					qi, ri, len(b.Path), maxLh)
			}
		}
	}
	return fx
}

// --- shared conversions -------------------------------------------------------

func shrinkCfgRef(fx *shrinkRealFixture) friConfigRef {
	return friConfigRef{QueryPowBits: fx.Fri.QueryPowBits, CommitPowBits: fx.Fri.CommitPowBits,
		ExtraQueryIndexBits: fx.Fri.ExtraQueryIndexBits, LogBlowup: fx.Fri.LogBlowup,
		LogFinalPolyLen: fx.Fri.LogFinalPolyLen}
}

func shrinkCfg(fx *shrinkRealFixture) FriConfig {
	return FriConfig{QueryPowBits: fx.Fri.QueryPowBits, CommitPowBits: fx.Fri.CommitPowBits,
		ExtraQueryIndexBits: fx.Fri.ExtraQueryIndexBits, LogBlowup: fx.Fri.LogBlowup,
		LogFinalPolyLen: fx.Fri.LogFinalPolyLen}
}

// replayShrinkPrefixRef drives the reference MultiField challenger through the
// fixture's pre-FRI transcript. Sampled values are compared against the
// Rust-emitted expectations — the native-Go transcript pin.
func replayShrinkPrefixRef(t *testing.T, c *multiFieldChallengerRef, fx *shrinkRealFixture) {
	t.Helper()
	for ei, ev := range fx.PrefixEvents {
		switch ev.Kind {
		case "observe_bb":
			c.observeBabyBearSlice(ev.Values)
		case "observe_digest":
			words := make([]fr.Element, len(ev.Words))
			for i, w := range ev.Words {
				words[i] = parseBn254Hex(t, w)
			}
			c.observeBn254Digest(words)
		case "sample_bb":
			for k, want := range ev.Values {
				if got := c.sampleBabyBear(); got != want {
					t.Fatalf("prefix event %d sample %d: go=%d rust=%d "+
						"(transcript prefix diverges)", ei, k, got, want)
				}
			}
		}
	}
}

// shrinkFixtureToNativeProofRef builds the reference proof object.
func shrinkFixtureToNativeProofRef(t *testing.T, fx *shrinkRealFixture) *friNativeProofRef {
	t.Helper()
	p := &friNativeProofRef{
		R:                fx.Fri.Rounds,
		FinalPoly:        []bbExtRef{fx.FinalPoly[0]},
		PowWitness:       fx.QueryPowWitness,
		RollInAfterRound: append([]int(nil), fx.RollInRounds...),
	}
	p.CommitRoots = make([]fr.Element, fx.Fri.Rounds)
	for r, root := range fx.CommitRoots {
		p.CommitRoots[r] = parseBn254Hex(t, root)
	}
	p.Queries = make([]friNativeQueryOpeningRef, len(fx.Queries))
	for qi, q := range fx.Queries {
		op := friNativeQueryOpeningRef{InitialEval: q.InitialEval}
		for _, ri := range q.RollIns {
			op.RollIns = append(op.RollIns, bbExtRef(ri))
		}
		for r := 0; r < fx.Fri.Rounds; r++ {
			op.Siblings = append(op.Siblings, bbExtRef(q.Siblings[r]))
			path := make([]fr.Element, len(q.MerklePaths[r]))
			for l, node := range q.MerklePaths[r] {
				path[l] = parseBn254Hex(t, node)
			}
			op.MerkleProofs = append(op.MerkleProofs, path)
		}
		p.Queries[qi] = op
	}
	return p
}

// --- native-Go checks ---------------------------------------------------------

// The reference verifier accepts the REAL shrink proof's FRI layer, and the
// live-derived betas + query indices match the Rust-emitted expectations
// (walked explicitly here so a transcript divergence names the exact lane).
func TestApexShrinkRealFixtureRefAcceptsAndPinsTranscript(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	cfgRef := shrinkCfgRef(fx)

	// Explicit transcript walk: betas and indices.
	c := newMultiFieldChallengerRef()
	replayShrinkPrefixRef(t, c, fx)
	for r := 0; r < fx.Fri.Rounds; r++ {
		c.observeBn254Digest([]fr.Element{parseBn254Hex(t, fx.CommitRoots[r])})
		beta := c.sampleExt()
		if beta != bbExtRef(fx.ExpectedBetas[r]) {
			t.Fatalf("round %d: beta %v != rust %v", r, beta, fx.ExpectedBetas[r])
		}
	}
	for _, coeff := range fx.FinalPoly {
		c.observeBabyBearSlice(coeff[:])
	}
	for r := 0; r < fx.Fri.Rounds; r++ {
		c.observeBabyBear(1)
	}
	if !c.checkWitness(fx.Fri.QueryPowBits, fx.QueryPowWitness) {
		t.Fatal("query PoW witness rejected by the reference challenger")
	}
	for qi, q := range fx.Queries {
		idx := c.sampleBits(fx.Fri.LogGlobalMaxHeight)
		if idx != q.ExpectedIndex {
			t.Fatalf("query %d: index %d != rust %d", qi, idx, q.ExpectedIndex)
		}
	}

	// Full reference verify (fresh challenger).
	c2 := newMultiFieldChallengerRef()
	replayShrinkPrefixRef(t, c2, fx)
	if !verifyFriNativeRef(c2, cfgRef, shrinkFixtureToNativeProofRef(t, fx)) {
		t.Fatal("reference verifier REJECTED the real shrink proof's FRI layer")
	}
}

// REJECT canaries, reference side: each single tamper must fail (the accept
// above is not vacuous).
func TestApexShrinkRealFixtureRefRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	cfgRef := shrinkCfgRef(fx)
	one := fr.One()

	cases := []struct {
		name   string
		tamper func(p *friNativeProofRef)
	}{
		{"tampered-commit-root", func(p *friNativeProofRef) {
			p.CommitRoots[0].Add(&p.CommitRoots[0], &one)
		}},
		{"tampered-sibling", func(p *friNativeProofRef) {
			p.Queries[0].Siblings[3][0] = bbAddRef(p.Queries[0].Siblings[3][0], 1)
		}},
		{"tampered-merkle-node", func(p *friNativeProofRef) {
			p.Queries[0].MerkleProofs[0][0].Add(&p.Queries[0].MerkleProofs[0][0], &one)
		}},
		{"tampered-initial-eval", func(p *friNativeProofRef) {
			p.Queries[0].InitialEval[0] = bbAddRef(p.Queries[0].InitialEval[0], 1)
		}},
		{"tampered-roll-in", func(p *friNativeProofRef) {
			if len(p.Queries[0].RollIns) == 0 {
				panic("real fixture must have roll-ins (multi-height batch)")
			}
			p.Queries[0].RollIns[0][0] = bbAddRef(p.Queries[0].RollIns[0][0], 1)
		}},
		{"tampered-pow-witness", func(p *friNativeProofRef) {
			p.PowWitness ^= 1
		}},
		{"tampered-final-poly", func(p *friNativeProofRef) {
			p.FinalPoly[0][0] = bbAddRef(p.FinalPoly[0][0], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p := shrinkFixtureToNativeProofRef(t, fx)
			tc.tamper(p)
			c := newMultiFieldChallengerRef()
			replayShrinkPrefixRef(t, c, fx)
			if verifyFriNativeRef(c, shrinkCfgRef(fx), p) {
				t.Fatalf("%s: reference ACCEPTED a tampered real proof", tc.name)
			}
			_ = cfgRef
		})
	}
}

// --- the gnark circuit ---------------------------------------------------------

// (shrinkPrefixOp lives in settlement_circuit.go, shared with the assembled
// SettlementCircuit.)

// apexShrinkRealCircuit replays the real pre-FRI transcript through the
// MultiFieldChallenger gadget (pinning every sampled challenge) and then runs
// VerifyFriNative over the real shrink proof's FRI data.
type apexShrinkRealCircuit struct {
	// Structural (unexported: ignored by the schema walker).
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int

	PrefixObs     []frontend.Variable // observe_bb values, flattened in order
	PrefixDigests []frontend.Variable // observe_digest words, flattened in order
	PrefixSamples []frontend.Variable // expected sample_bb values, flattened
	CommitRoots   []frontend.Variable
	FinalPoly     []BBExt
	PowWitness    frontend.Variable
	Queries       []FriNativeQueryOpening
}

func (c *apexShrinkRealCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallenger(bb)
	io, id, is := 0, 0, 0
	for _, op := range c.script {
		switch op.kind {
		case "observe_bb":
			ch.ObserveBabyBearSlice(c.PrefixObs[io : io+op.n])
			io += op.n
		case "observe_digest":
			// One event = ONE native absorb call (its own length tag).
			ch.ObserveBn254Digest(c.PrefixDigests[id : id+op.n])
			id += op.n
		case "sample_bb":
			for k := 0; k < op.n; k++ {
				api.AssertIsEqual(ch.SampleBabyBear(), c.PrefixSamples[is])
				is++
			}
		}
	}
	VerifyFriNative(bb, c.cfg, c.r, c.CommitRoots, c.FinalPoly, c.PowWitness,
		c.Queries, c.rollInAfterRound, ch)
	return nil
}

// allocApexShrinkRealCircuit builds the shape template from the fixture.
func allocApexShrinkRealCircuit(fx *shrinkRealFixture) *apexShrinkRealCircuit {
	c := &apexShrinkRealCircuit{cfg: shrinkCfg(fx), r: fx.Fri.Rounds,
		rollInAfterRound: append([]int(nil), fx.RollInRounds...)}
	nObs, nDig, nSamp := 0, 0, 0
	for _, ev := range fx.PrefixEvents {
		switch ev.Kind {
		case "observe_bb":
			c.script = append(c.script, shrinkPrefixOp{"observe_bb", len(ev.Values)})
			nObs += len(ev.Values)
		case "observe_digest":
			c.script = append(c.script, shrinkPrefixOp{"observe_digest", len(ev.Words)})
			nDig += len(ev.Words)
		case "sample_bb":
			c.script = append(c.script, shrinkPrefixOp{"sample_bb", len(ev.Values)})
			nSamp += len(ev.Values)
		}
	}
	c.PrefixObs = make([]frontend.Variable, nObs)
	c.PrefixDigests = make([]frontend.Variable, nDig)
	c.PrefixSamples = make([]frontend.Variable, nSamp)
	c.CommitRoots = make([]frontend.Variable, fx.Fri.Rounds)
	c.FinalPoly = make([]BBExt, 1)
	c.Queries = make([]FriNativeQueryOpening, len(fx.Queries))
	for qi := range c.Queries {
		c.Queries[qi].RollIns = make([]BBExt, len(fx.RollInRounds))
		c.Queries[qi].Siblings = make([]BBExt, fx.Fri.Rounds)
		c.Queries[qi].MerkleProofs = make([][]frontend.Variable, fx.Fri.Rounds)
		for r := 0; r < fx.Fri.Rounds; r++ {
			c.Queries[qi].MerkleProofs[r] =
				make([]frontend.Variable, fx.Fri.LogGlobalMaxHeight-r-1)
		}
	}
	return c
}

func extVars(e [4]uint32) BBExt {
	return BBExt{e[0], e[1], e[2], e[3]}
}

// assignApexShrinkRealCircuit fills the witness from the fixture.
func assignApexShrinkRealCircuit(t *testing.T, fx *shrinkRealFixture) *apexShrinkRealCircuit {
	t.Helper()
	c := allocApexShrinkRealCircuit(fx)
	io, id, is := 0, 0, 0
	for _, ev := range fx.PrefixEvents {
		switch ev.Kind {
		case "observe_bb":
			for _, v := range ev.Values {
				c.PrefixObs[io] = v
				io++
			}
		case "observe_digest":
			for _, w := range ev.Words {
				e := parseBn254Hex(t, w)
				c.PrefixDigests[id] = frToBig(e)
				id++
			}
		case "sample_bb":
			for _, v := range ev.Values {
				c.PrefixSamples[is] = v
				is++
			}
		}
	}
	for r, root := range fx.CommitRoots {
		e := parseBn254Hex(t, root)
		c.CommitRoots[r] = frToBig(e)
	}
	c.FinalPoly[0] = extVars(fx.FinalPoly[0])
	c.PowWitness = fx.QueryPowWitness
	for qi, q := range fx.Queries {
		c.Queries[qi].InitialEval = extVars(q.InitialEval)
		for i, ri := range q.RollIns {
			c.Queries[qi].RollIns[i] = extVars(ri)
		}
		for r := 0; r < fx.Fri.Rounds; r++ {
			c.Queries[qi].Siblings[r] = extVars(q.Siblings[r])
			for l, node := range q.MerklePaths[r] {
				e := parseBn254Hex(t, node)
				c.Queries[qi].MerkleProofs[r][l] = frToBig(e)
			}
		}
	}
	return c
}

// ACCEPT: the gnark gadget verifies the REAL shrink proof's FRI layer with the
// full live transcript (every prefix challenge pinned in-circuit).
func TestApexShrinkRealFixtureGadgetAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	if err := test.IsSolved(allocApexShrinkRealCircuit(fx), assignApexShrinkRealCircuit(t, fx),
		ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget rejected the REAL shrink proof's FRI layer: %v", err)
	}
}

// REJECT canaries, gadget side: the accept above must be falsifiable on the
// same real data.
func TestApexShrinkRealFixtureGadgetRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	field := ecc.BN254.ScalarField()
	one := fr.One()

	cases := []struct {
		name   string
		tamper func(c *apexShrinkRealCircuit)
	}{
		{"tampered-commit-root", func(c *apexShrinkRealCircuit) {
			e := parseBn254Hex(t, fx.CommitRoots[0])
			e.Add(&e, &one)
			c.CommitRoots[0] = frToBig(e)
		}},
		{"tampered-roll-in", func(c *apexShrinkRealCircuit) {
			c.Queries[0].RollIns[0][0] = bbAddRef(fx.Queries[0].RollIns[0][0], 1)
		}},
		{"tampered-prefix-sample", func(c *apexShrinkRealCircuit) {
			// Break the transcript pin: the first expected challenge lane.
			var first uint32
			for _, ev := range fx.PrefixEvents {
				if ev.Kind == "sample_bb" {
					first = ev.Values[0]
					break
				}
			}
			c.PrefixSamples[0] = bbAddRef(first, 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			w := assignApexShrinkRealCircuit(t, fx)
			tc.tamper(w)
			if err := test.IsSolved(allocApexShrinkRealCircuit(fx), w, field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED tampered real data", tc.name)
			}
		})
	}
}
