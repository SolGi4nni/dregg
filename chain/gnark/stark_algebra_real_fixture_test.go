// THE WRAP END-TO-END (STARK-algebra layer): gnark verifies the batch-STARK
// algebra of the REAL shrink proof — quotient identities at zeta with FULL
// in-circuit constraint evaluation for all 6 instances (via the emitted
// symbolic AIR DAGs) — on top of the SAME transcript replay + FRI core the
// existing real-fixture test drives, and — since the EXPOSED shrink — the
// 25-lane settlement claim binding (the expose_claim instance's public
// values, absorbed into the transcript AND constrained by its AIR).
//
// The fixture (fixtures/apex_shrink_fri_real.json, v3) carries the whole
// STARK-algebra input: the pre-FRI transcript prefix contains the observed
// per-instance public values (verify_batch observes them right after the
// main commitment), the opened values at zeta (pcs.verify observes every
// opened value before sampling the FRI alpha — two_adic_pcs.rs:687-694,
// mirrored by the exporter at apex_shrink_gnark_export.rs) and every sampled
// challenge (perm alpha/beta, the constraint-folding alpha, zeta). This file
// locates them by the ANCHORED head+tail structure of the event stream and
// slices them by the pinned 6-instance shape (see stark_verify_native.go
// ShrinkVk).
//
// HONEST SCOPE: see stark_verify_native.go — the constraint evaluation and
// quotient identity are REAL checks for all 6 instances (the former hand
// mode, whose heavy instances were witnessed and vacuously satisfied, was
// REMOVED), and the open_input seam is CLOSED: the assembled circuit below
// Merkle-opens the input batches against the transcript-observed commitments
// and re-derives the FRI reduced openings from the opened columns
// (stark_open_input.go), binding the fold seeds to the committed trace.
package friverifier

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// ----------------------------------------------------------------------------
// Anchored prefix location + shape decoding
// ----------------------------------------------------------------------------

// locateShrinkStarkPrefix walks the fixture's event stream and anchors the
// STARK-algebra events by the HEAD structure (binding block, main commitment,
// publics+widths block) and the TAIL structure of verify_batch's transcript
// (batch-stark verifier/mod.rs:288-300 + pcs.verify observes + FRI alpha):
//
//	observe_bb(binding block), observe_digest(main cap),
//	observe_bb(per-instance PUBLIC VALUES ++ preprocessed widths),
//	observe_digest(preprocessed cap),
//	..., sample(perm challenges), observe_digest(perm cap),
//	observe_bb(cumulative sums), sample(alpha), observe_digest(quotient cap),
//	sample(zeta), observe_bb(opened values), sample(FRI alpha)
//
// Fail-closed on any kind/length mismatch, including the publics block not
// matching the fixture's table_publics values byte-for-byte.
func locateShrinkStarkPrefix(fx *shrinkRealFixture) (shrinkStarkPrefixLoc, error) {
	evs := fx.PrefixEvents
	n := len(evs)
	if n < 8 {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("prefix has only %d events", n)
	}
	// Cumulative flat offsets per event.
	obsOff := make([]int, n)
	sampOff := make([]int, n)
	digOff := make([]int, n)
	var digEvents []int
	obs, samp, dig := 0, 0, 0
	for i, ev := range evs {
		obsOff[i] = obs
		sampOff[i] = samp
		digOff[i] = dig
		switch ev.Kind {
		case "observe_bb":
			obs += len(ev.Values)
		case "sample_bb":
			samp += len(ev.Values)
		case "observe_digest":
			dig += len(ev.Words)
			digEvents = append(digEvents, i)
		}
	}
	check := func(i int, kind string, vals int) error {
		if evs[i].Kind != kind {
			return fmt.Errorf("event %d: kind %q, want %q", i, evs[i].Kind, kind)
		}
		if vals >= 0 && len(evs[i].Values) != vals {
			return fmt.Errorf("event %d: %d values, want %d", i, len(evs[i].Values), vals)
		}
		return nil
	}
	for _, e := range []error{
		check(n-1, "sample_bb", 4),      // FRI batch-combination alpha
		check(n-2, "observe_bb", -1),    // opened values at zeta
		check(n-3, "sample_bb", 4),      // zeta
		check(n-4, "observe_digest", 0), // quotient commitment
		check(n-5, "sample_bb", 4),      // constraint-folding alpha
		check(n-6, "observe_bb", -1),    // cumulative sums
		check(n-7, "observe_digest", 0), // permutation commitment
		check(n-8, "sample_bb", 8),      // WitnessChecks (alpha, beta)
	} {
		if e != nil {
			return shrinkStarkPrefixLoc{}, e
		}
	}
	if len(evs[n-2].Values)%4 != 0 || len(evs[n-6].Values)%4 != 0 {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("opened/cum streams not EF-aligned")
	}
	// HEAD anchoring: binding block, main cap, publics ++ widths.
	nInst := len(fx.DegreeBits)
	totalPv := 0
	pubLens := make([]int, nInst)
	if len(fx.TablePublics) != nInst {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("table_publics has %d instances, want %d",
			len(fx.TablePublics), nInst)
	}
	for i, pv := range fx.TablePublics {
		pubLens[i] = len(pv)
		totalPv += len(pv)
	}
	for _, e := range []error{
		check(0, "observe_bb", 4+16*nInst), // instance count + per-instance binding
		check(1, "observe_digest", 0),      // main commitment
		check(2, "observe_bb", totalPv+4*nInst),
	} {
		if e != nil {
			return shrinkStarkPrefixLoc{}, e
		}
	}
	// The publics block IS the fixture's table_publics, flattened in instance
	// order (fail-closed cross-check: the claim channel the circuit binds is
	// the one the transcript absorbed).
	flat := evs[2].Values[:totalPv]
	k := 0
	for i, pv := range fx.TablePublics {
		for _, v := range pv {
			if flat[k] != v {
				return shrinkStarkPrefixLoc{}, fmt.Errorf(
					"instance %d publics diverge between transcript and table_publics", i)
			}
			k++
		}
	}
	// The four commitment digests, in OBSERVE order main, preprocessed,
	// permutation, quotient (verify_batch's transcript); the permutation and
	// quotient anchors were already pinned above. Each cap is one root
	// (cap height 0), one BN254 word.
	if len(digEvents) != 4 {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("%d digest events (want 4 commitment caps)", len(digEvents))
	}
	if digEvents[0] != 1 || digEvents[2] != n-7 || digEvents[3] != n-4 {
		return shrinkStarkPrefixLoc{}, fmt.Errorf("digest events %v do not anchor main/perm/quotient", digEvents)
	}
	for _, i := range digEvents {
		if len(evs[i].Words) != 1 {
			return shrinkStarkPrefixLoc{}, fmt.Errorf("event %d: cap has %d words (want 1)", i, len(evs[i].Words))
		}
	}
	return shrinkStarkPrefixLoc{
		permChSampleOff: sampOff[n-8],
		alphaSampleOff:  sampOff[n-5],
		zetaSampleOff:   sampOff[n-3],
		friAlphaOff:     sampOff[n-1],
		openedObsOff:    obsOff[n-2],
		openedObsLen:    len(evs[n-2].Values),
		cumObsOff:       obsOff[n-6],
		cumObsLen:       len(evs[n-6].Values),
		// PCS round order: trace(main), quotient, preprocessed, permutation.
		inputRootDigOff: [4]int{
			digOff[digEvents[0]], digOff[digEvents[3]],
			digOff[digEvents[1]], digOff[digEvents[2]],
		},
		pubObsOff: obsOff[2],
		pubLens:   pubLens,
		preDigOff: digOff[digEvents[1]],
	}, nil
}

// shrinkShapesFromFixture decodes the transcript-bound binding block
// (event 0: instance count + per-instance ext_db/base_db/width/n_chunks,
// each usize-lifted to [v,0,0,0]) and the preprocessed widths (event 2, after
// the publics block) and merges them with the pinned VK flags. Fail-closed on
// any drift.
func shrinkShapesFromFixture(t *testing.T, fx *shrinkRealFixture) []StarkInstanceShape {
	t.Helper()
	evs := fx.PrefixEvents
	if len(evs) < 3 || evs[0].Kind != "observe_bb" || evs[2].Kind != "observe_bb" {
		t.Fatal("prefix head structure drifted (binding block / publics+widths block)")
	}
	e0 := evs[0].Values
	lift := func(off int, what string) int {
		if off+4 > len(e0) {
			t.Fatalf("binding block truncated reading %s", what)
		}
		if e0[off+1] != 0 || e0[off+2] != 0 || e0[off+3] != 0 {
			t.Fatalf("binding block %s is not a usize lift: %v", what, e0[off:off+4])
		}
		return int(e0[off])
	}
	nInst := lift(0, "instance count")
	if nInst != ShrinkNumInstances || len(e0) != 4+16*nInst {
		t.Fatalf("binding block: %d instances / %d values (want %d / %d)",
			nInst, len(e0), ShrinkNumInstances, 4+16*ShrinkNumInstances)
	}
	totalPv := 0
	for _, pv := range fx.TablePublics {
		totalPv += len(pv)
	}
	e2 := evs[2].Values
	if len(e2) != totalPv+4*nInst {
		t.Fatalf("publics+widths block has %d values (want %d publics + %d widths)",
			len(e2), totalPv, 4*nInst)
	}
	widths := e2[totalPv:]
	if fx.ClaimInstance != ShrinkVk.ClaimInstance ||
		len(fx.TablePublics[fx.ClaimInstance]) != ShrinkVk.ClaimLen {
		t.Fatalf("claim channel drifted from the pinned VK (instance %d/%d, %d lanes/%d)",
			fx.ClaimInstance, ShrinkVk.ClaimInstance,
			len(fx.TablePublics[fx.ClaimInstance]), ShrinkVk.ClaimLen)
	}
	shapes := make([]StarkInstanceShape, nInst)
	for i := 0; i < nInst; i++ {
		extDb := lift(4+16*i, "ext_db")
		baseDb := lift(8+16*i, "base_db")
		width := lift(12+16*i, "width")
		nChunks := lift(16+16*i, "n_chunks")
		if extDb != baseDb || extDb != fx.DegreeBits[i] {
			t.Fatalf("instance %d: degree bits %d/%d vs fixture %d",
				i, extDb, baseDb, fx.DegreeBits[i])
		}
		if widths[4*i+1] != 0 || widths[4*i+2] != 0 || widths[4*i+3] != 0 {
			t.Fatalf("preprocessed width %d is not a usize lift", i)
		}
		if len(fx.TablePublics[i]) != ShrinkVk.NumPublicValues[i] {
			t.Fatalf("instance %d: %d public values vs pinned VK %d",
				i, len(fx.TablePublics[i]), ShrinkVk.NumPublicValues[i])
		}
		shapes[i] = StarkInstanceShape{
			DegreeBits:        extDb,
			Width:             width,
			PreWidth:          int(widths[4*i]),
			NumQuotientChunks: nChunks,
			NumLookups:        ShrinkVk.NumLookups[i],
			NumGlobalLookups:  ShrinkVk.NumLookups[i],
			NumPublicValues:   ShrinkVk.NumPublicValues[i],
			HasTraceNext:      ShrinkVk.TraceNext[i],
			HasPreNext:        ShrinkVk.PreNext[i],
		}
	}
	return shapes
}

// shrinkStarkExtract is the host-side extraction of the algebra inputs.
type shrinkStarkExtract struct {
	shapes   []StarkInstanceShape
	loc      shrinkStarkPrefixLoc
	openedEF []bbExtRef
	cumSums  []bbExtRef
	pubVals  [][]uint32 // per-instance public values (the claim channel)
	friAlpha bbExtRef   // the FRI batch-combination alpha (open_input)
	ch       shrinkStarkChallengesRef
}

func extractShrinkStark(t *testing.T, fx *shrinkRealFixture) *shrinkStarkExtract {
	t.Helper()
	loc, err := locateShrinkStarkPrefix(fx)
	if err != nil {
		t.Fatalf("anchored prefix location failed: %v", err)
	}
	shapes := shrinkShapesFromFixture(t, fx)
	_, totalEF := buildStarkOpenedSpans(shapes)
	if loc.openedObsLen != 4*totalEF {
		t.Fatalf("opened-values stream: %d values, pinned shape requires %d "+
			"(the 6-instance shape accounting must be EXACT)", loc.openedObsLen, 4*totalEF)
	}
	if want := 4 * totalGlobalLookups(shapes); loc.cumObsLen != want {
		t.Fatalf("cumulative-sums stream: %d values, want %d", loc.cumObsLen, want)
	}

	// Flatten the observe/sample streams.
	var obs, samp []uint32
	for _, ev := range fx.PrefixEvents {
		switch ev.Kind {
		case "observe_bb":
			obs = append(obs, ev.Values...)
		case "sample_bb":
			samp = append(samp, ev.Values...)
		}
	}
	groupEF := func(vals []uint32) []bbExtRef {
		out := make([]bbExtRef, len(vals)/4)
		for i := range out {
			copy(out[i][:], vals[4*i:4*i+4])
		}
		return out
	}
	ext := func(off int) bbExtRef {
		var e bbExtRef
		copy(e[:], samp[off:off+4])
		return e
	}
	pubVals := make([][]uint32, len(shapes))
	for i := range shapes {
		off := loc.pubObsOffOf(i)
		pubVals[i] = append([]uint32(nil), obs[off:off+loc.pubLens[i]]...)
	}
	return &shrinkStarkExtract{
		shapes:   shapes,
		loc:      loc,
		openedEF: groupEF(obs[loc.openedObsOff : loc.openedObsOff+loc.openedObsLen]),
		cumSums:  groupEF(obs[loc.cumObsOff : loc.cumObsOff+loc.cumObsLen]),
		pubVals:  pubVals,
		friAlpha: ext(loc.friAlphaOff),
		ch: shrinkStarkChallengesRef{
			permAlpha: ext(loc.permChSampleOff),
			permBeta:  ext(loc.permChSampleOff + 4),
			alpha:     ext(loc.alphaSampleOff),
			zeta:      ext(loc.zetaSampleOff),
		},
	}
}

// ----------------------------------------------------------------------------
// Host-reference checks on the REAL proof
// ----------------------------------------------------------------------------

const shrinkSymbolicConstraintsPath = "fixtures/shrink_symbolic_constraints.json"

func loadShrinkSymbolicConstraints(t *testing.T) *SymbolicConstraints {
	t.Helper()
	sym, err := LoadSymbolicConstraints(shrinkSymbolicConstraintsPath)
	if err != nil {
		t.Fatalf("emitted symbolic constraints must load (emit via "+
			"plonky3-recursion/circuit-prover/tests/emit_shrink_symbolic.rs): %v", err)
	}
	return sym
}

// ACCEPT: with the interpreted (emitted, not hand-coded) constraints, the
// quotient identity holds on the REAL shrink proof for ALL SIX instances —
// including Alu (146 constraints), Poseidon2 (337) and ExposeClaim (100, the
// claim channel with its pv == v_0 binding), and the global WitnessChecks
// sums balance. A wrong emitted tree, wrong AIR knob, or wrong interpreter
// semantics cannot pass this (~124-bit equation per instance on real data).
func TestApexShrinkRealFixtureStarkAlgebraRefAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	if err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.pubVals, ex.ch, sym); err != nil {
		t.Fatalf("reference STARK algebra REJECTED the real shrink proof: %v", err)
	}
}

// REJECT canaries, reference side: single tampers of the real openings (and
// of the CLAIM lanes) must fail the identity or the balance (the accept above
// is not vacuous). The heavy-instance tampers are the audit tooth: before the
// hand-mode removal, an Alu/Poseidon2 trace tamper PASSED the sym==nil path.
func TestApexShrinkRealFixtureStarkAlgebraRefRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	base := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	spans, _ := buildStarkOpenedSpans(base.shapes)
	claimInst := ShrinkVk.ClaimInstance

	cases := []struct {
		name   string
		tamper func(ex *shrinkStarkExtract)
	}{
		{"tampered-const-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[0].traceLocal.off][0] =
				bbAddRef(ex.openedEF[spans[0].traceLocal.off][0], 1)
		}},
		{"tampered-const-quotient-chunk", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[0].quotientChunks[0].off][2] =
				bbAddRef(ex.openedEF[spans[0].quotientChunks[0].off][2], 1)
		}},
		{"tampered-public-perm-column", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[1].permLocal.off][1] =
				bbAddRef(ex.openedEF[spans[1].permLocal.off][1], 1)
		}},
		{"tampered-recompose-pre-mult", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[4].preLocal.off+1][0] =
				bbAddRef(ex.openedEF[spans[4].preLocal.off+1][0], 1)
		}},
		{"tampered-const-cum-sum", func(ex *shrinkStarkExtract) {
			ex.cumSums[spans[0].cumSums.off][0] =
				bbAddRef(ex.cumSums[spans[0].cumSums.off][0], 1)
		}},
		{"tampered-alu-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[2].traceLocal.off+10][0] =
				bbAddRef(ex.openedEF[spans[2].traceLocal.off+10][0], 1)
		}},
		{"tampered-alu-trace-next", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[2].traceNext.off+3][2] =
				bbAddRef(ex.openedEF[spans[2].traceNext.off+3][2], 1)
		}},
		{"tampered-alu-preprocessed", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[2].preLocal.off+5][1] =
				bbAddRef(ex.openedEF[spans[2].preLocal.off+5][1], 1)
		}},
		{"tampered-alu-cum-sum", func(ex *shrinkStarkExtract) {
			ex.cumSums[spans[2].cumSums.off+4][0] =
				bbAddRef(ex.cumSums[spans[2].cumSums.off+4][0], 1)
		}},
		{"tampered-poseidon2-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[3].traceLocal.off+123][0] =
				bbAddRef(ex.openedEF[spans[3].traceLocal.off+123][0], 1)
		}},
		{"tampered-poseidon2-perm-column", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[3].permLocal.off+8][3] =
				bbAddRef(ex.openedEF[spans[3].permLocal.off+8][3], 1)
		}},
		{"tampered-poseidon2-quotient-chunk", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[3].quotientChunks[1].off][1] =
				bbAddRef(ex.openedEF[spans[3].quotientChunks[1].off][1], 1)
		}},
		{"tampered-zeta", func(ex *shrinkStarkExtract) {
			ex.ch.zeta[0] = bbAddRef(ex.ch.zeta[0], 1)
		}},
		{"tampered-perm-beta", func(ex *shrinkStarkExtract) {
			ex.ch.permBeta[3] = bbAddRef(ex.ch.permBeta[3], 1)
		}},
		// THE CLAIM TEETH: a forged claim lane must fail the ExposeClaimAir
		// pv == v_0 identity against the committed expose_claim trace.
		{"tampered-claim-genesis-lane", func(ex *shrinkStarkExtract) {
			ex.pubVals[claimInst][0] = bbAddRef(ex.pubVals[claimInst][0], 1)
		}},
		{"tampered-claim-final-root-lane", func(ex *shrinkStarkExtract) {
			ex.pubVals[claimInst][8] = bbAddRef(ex.pubVals[claimInst][8], 1)
		}},
		{"tampered-claim-num-turns", func(ex *shrinkStarkExtract) {
			ex.pubVals[claimInst][16] = bbAddRef(ex.pubVals[claimInst][16], 1)
		}},
		{"tampered-expose-claim-trace-value", func(ex *shrinkStarkExtract) {
			ex.openedEF[spans[claimInst].traceLocal.off][0] =
				bbAddRef(ex.openedEF[spans[claimInst].traceLocal.off][0], 1)
		}},
		{"tampered-expose-claim-cum-sum", func(ex *shrinkStarkExtract) {
			ex.cumSums[spans[claimInst].cumSums.off][0] =
				bbAddRef(ex.cumSums[spans[claimInst].cumSums.off][0], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			ex := extractShrinkStark(t, fx)
			tc.tamper(ex)
			if err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.pubVals, ex.ch, sym); err == nil {
				t.Fatalf("%s: reference ACCEPTED tampered real openings", tc.name)
			}
		})
	}
}

// DIFFERENTIAL: for the three simple instances the interpreted folded value
// must equal the INDEPENDENT hand-derived LogUp evaluation — two disjoint
// paths (emitted-DAG interpreter vs hand-ported logup.rs algebra) agreeing
// on real data. (The hand path is host-side cross-check ONLY; the circuit
// path is always the interpreter.)
func TestApexShrinkRealFixtureSymbolicVsHandFolded(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	spans, _ := buildStarkOpenedSpans(ex.shapes)
	slice := func(s efSpan) []bbExtRef { return ex.openedEF[s.off : s.off+s.len] }
	for i, spec := range ShrinkVk.SimpleSpecs {
		sh := ex.shapes[i]
		sp := spans[i]
		sel, err := computeStarkSelectorsRef(ex.ch.zeta, sh.DegreeBits)
		if err != nil {
			t.Fatal(err)
		}
		pre := slice(sp.preLocal)
		trace := slice(sp.traceLocal)
		perm := slice(sp.permLocal)
		permNext := slice(sp.permNext)
		elems := append([]bbExtRef{pre[spec.idxPreCol]}, trace...)
		hand := evalWitnessBusFoldedRef(
			sel, ex.ch.alpha, ex.ch.permAlpha, ex.ch.permBeta,
			elems, pre[spec.multPreCol],
			bbExtFromBasisRef([4]bbExtRef(perm[0:4])),
			bbExtFromBasisRef([4]bbExtRef(permNext[0:4])),
			ex.cumSums[sp.cumSums.off],
		)
		interp, err := evalSymbolicFoldedRef(&sym.Instances[i],
			shrinkSymInputsRef(sh, sp, slice, ex.cumSums, ex.pubVals[i], ex.ch, sel), ex.ch.alpha)
		if err != nil {
			t.Fatalf("instance %d: %v", i, err)
		}
		if hand != interp {
			t.Fatalf("instance %d (%s): hand-derived folded %v != interpreted %v",
				i, sym.Instances[i].Name, hand, interp)
		}
	}
}

// ----------------------------------------------------------------------------
// The gnark gadget, algebra layer in isolation (raw witnesses)
// ----------------------------------------------------------------------------

// shrinkStarkAlgebraCircuit feeds VerifyShrinkStarkAlgebra from raw witness
// arrays (canonicity asserted at ingestion), isolating the algebra teeth
// from the transcript binding (which the SettlementCircuit covers).
type shrinkStarkAlgebraCircuit struct {
	shapes []StarkInstanceShape // structural
	sym    *SymbolicConstraints // structural (required)

	OpenedEF  []BBExt
	CumSums   []BBExt
	PubVals   [][]frontend.Variable
	PermAlpha BBExt
	PermBeta  BBExt
	Alpha     BBExt
	Zeta      BBExt
}

func (c *shrinkStarkAlgebraCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	for i := range c.OpenedEF {
		bb.ExtAssertIsCanonical(c.OpenedEF[i])
	}
	for i := range c.CumSums {
		bb.ExtAssertIsCanonical(c.CumSums[i])
	}
	for i := range c.PubVals {
		for _, v := range c.PubVals[i] {
			bb.AssertIsCanonical(v)
		}
	}
	for _, e := range []BBExt{c.PermAlpha, c.PermBeta, c.Alpha, c.Zeta} {
		bb.ExtAssertIsCanonical(e)
	}
	VerifyShrinkStarkAlgebra(bb, c.shapes, c.OpenedEF, c.CumSums, c.PubVals,
		ShrinkStarkChallenges{
			PermAlpha: c.PermAlpha, PermBeta: c.PermBeta,
			Alpha: c.Alpha, Zeta: c.Zeta,
		},
		c.sym)
	return nil
}

func allocShrinkStarkAlgebraCircuit(ex *shrinkStarkExtract, sym *SymbolicConstraints) *shrinkStarkAlgebraCircuit {
	c := &shrinkStarkAlgebraCircuit{
		shapes:   ex.shapes,
		sym:      sym,
		OpenedEF: make([]BBExt, len(ex.openedEF)),
		CumSums:  make([]BBExt, len(ex.cumSums)),
		PubVals:  make([][]frontend.Variable, len(ex.pubVals)),
	}
	for i := range ex.pubVals {
		c.PubVals[i] = make([]frontend.Variable, len(ex.pubVals[i]))
	}
	return c
}

func assignShrinkStarkAlgebraCircuit(t *testing.T, ex *shrinkStarkExtract, sym *SymbolicConstraints) *shrinkStarkAlgebraCircuit {
	t.Helper()
	if err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.pubVals, ex.ch, sym); err != nil {
		t.Fatalf("host reference must accept before circuit assignment: %v", err)
	}
	c := allocShrinkStarkAlgebraCircuit(ex, sym)
	for i, e := range ex.openedEF {
		c.OpenedEF[i] = extToVars(e)
	}
	for i, e := range ex.cumSums {
		c.CumSums[i] = extToVars(e)
	}
	for i := range ex.pubVals {
		for k, v := range ex.pubVals[i] {
			c.PubVals[i][k] = v
		}
	}
	c.PermAlpha = extToVars(ex.ch.permAlpha)
	c.PermBeta = extToVars(ex.ch.permBeta)
	c.Alpha = extToVars(ex.ch.alpha)
	c.Zeta = extToVars(ex.ch.zeta)
	return c
}

// ACCEPT: the in-circuit interpreter evaluates ALL SIX instances' constraints
// on the real proof (claim lanes included).
func TestApexShrinkRealFixtureStarkAlgebraGadgetAccepts(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	if err := test.IsSolved(allocShrinkStarkAlgebraCircuit(ex, sym),
		assignShrinkStarkAlgebraCircuit(t, ex, sym), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget rejected the REAL shrink proof's STARK algebra: %v", err)
	}
}

// REJECT canaries, gadget side (heavy instances AND claim lanes included —
// exactly the tampers the removed hand mode let through).
func TestApexShrinkRealFixtureStarkAlgebraGadgetRejectsTampers(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	field := ecc.BN254.ScalarField()
	baseEx := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	spans, _ := buildStarkOpenedSpans(baseEx.shapes)
	claimInst := ShrinkVk.ClaimInstance

	cases := []struct {
		name   string
		tamper func(c *shrinkStarkAlgebraCircuit)
	}{
		{"tampered-const-quotient-chunk", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[0].quotientChunks[0].off][0] =
				bbAddRef(baseEx.openedEF[spans[0].quotientChunks[0].off][0], 1)
		}},
		{"tampered-public-perm-column", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[1].permLocal.off][2] =
				bbAddRef(baseEx.openedEF[spans[1].permLocal.off][2], 1)
		}},
		{"tampered-recompose-trace-value", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[4].traceLocal.off][0] =
				bbAddRef(baseEx.openedEF[spans[4].traceLocal.off][0], 1)
		}},
		{"tampered-alu-trace-value", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[2].traceLocal.off+10][0] =
				bbAddRef(baseEx.openedEF[spans[2].traceLocal.off+10][0], 1)
		}},
		{"tampered-alu-cum-sum-balance", func(c *shrinkStarkAlgebraCircuit) {
			c.CumSums[spans[2].cumSums.off][0] =
				bbAddRef(baseEx.cumSums[spans[2].cumSums.off][0], 1)
		}},
		{"tampered-poseidon2-perm-column", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[3].permLocal.off+8][3] =
				bbAddRef(baseEx.openedEF[spans[3].permLocal.off+8][3], 1)
		}},
		{"tampered-claim-lane", func(c *shrinkStarkAlgebraCircuit) {
			c.PubVals[claimInst][0] = bbAddRef(baseEx.pubVals[claimInst][0], 1)
		}},
		{"tampered-expose-claim-trace-value", func(c *shrinkStarkAlgebraCircuit) {
			c.OpenedEF[spans[claimInst].traceLocal.off][0] =
				bbAddRef(baseEx.openedEF[spans[claimInst].traceLocal.off][0], 1)
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			ex := extractShrinkStark(t, fx)
			w := assignShrinkStarkAlgebraCircuit(t, ex, sym)
			tc.tamper(w)
			if err := test.IsSolved(allocShrinkStarkAlgebraCircuit(ex, sym), w, field); err == nil {
				t.Fatalf("%s: gadget ACCEPTED tampered real openings", tc.name)
			}
		})
	}
}

// ----------------------------------------------------------------------------
// The assembled SettlementCircuit: transcript replay + STARK algebra + FRI
// core + open_input + THE 25-LANE PUBLIC STATEMENT BINDING
// ----------------------------------------------------------------------------

func allocSettlementCircuit(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *SettlementCircuit {
	t.Helper()
	inner := allocApexShrinkRealCircuit(fx)
	return &SettlementCircuit{
		script:                 inner.script,
		cfg:                    inner.cfg,
		r:                      inner.r,
		rollInAfterRound:       inner.rollInAfterRound,
		shapes:                 ex.shapes,
		loc:                    ex.loc,
		sym:                    sym,
		inputRounds:            shrinkInputRoundsFromFixture(t, fx, ex.shapes),
		claimInstance:          fx.ClaimInstance,
		vkPreprocessedRoot:     shrinkPreprocessedRoot(t, fx, ex.loc),
		apexPreprocessedCommit: apexPreprocessedCommitConstants(t),
		PrefixObs:              inner.PrefixObs,
		PrefixDigests:          inner.PrefixDigests,
		PrefixSamples:          inner.PrefixSamples,
		CommitRoots:            inner.CommitRoots,
		FinalPoly:              inner.FinalPoly,
		Queries:                inner.Queries,
		InputOpenings:          allocShrinkInputOpenings(fx),
	}
}

func assignSettlementCircuit(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, sym *SymbolicConstraints) *SettlementCircuit {
	t.Helper()
	if err := verifyShrinkStarkAlgebraRef(ex.shapes, ex.openedEF, ex.cumSums, ex.pubVals, ex.ch, sym); err != nil {
		t.Fatalf("host reference must accept before circuit assignment: %v", err)
	}
	inner := assignApexShrinkRealCircuit(t, fx)
	c := &SettlementCircuit{
		script:                 inner.script,
		cfg:                    inner.cfg,
		r:                      inner.r,
		rollInAfterRound:       inner.rollInAfterRound,
		shapes:                 ex.shapes,
		loc:                    ex.loc,
		sym:                    sym,
		inputRounds:            shrinkInputRoundsFromFixture(t, fx, ex.shapes),
		claimInstance:          fx.ClaimInstance,
		vkPreprocessedRoot:     shrinkPreprocessedRoot(t, fx, ex.loc),
		apexPreprocessedCommit: apexPreprocessedCommitConstants(t),
		PrefixObs:              inner.PrefixObs,
		PrefixDigests:          inner.PrefixDigests,
		PrefixSamples:          inner.PrefixSamples,
		CommitRoots:            inner.CommitRoots,
		FinalPoly:              inner.FinalPoly,
		PowWitness:             inner.PowWitness,
		Queries:                inner.Queries,
		InputOpenings:          assignShrinkInputOpenings(t, fx),
	}
	assignSettlementPublics(c, fx.TablePublics[fx.ClaimInstance])
	return c
}

// apexVkIdentity is the DERIVED deployed-apex VK identity artifact
// (fixtures/apex_vk_identity.json), minted by the Rust derivation lane —
// apex_shrink_gnark_fixture.rs derive_deployed_apex_vk_identity_and_check_fixture
// — from a FRESH fold of the apex circuit at HEAD, NOT from the proof
// fixture. RecursionVkHex is the blake3-32 RecursionVk fingerprint, and it is
// ASSERTED equal to the governance-pinned DreggApexRecursionVk constant at
// load (checkApexVkIdentityAnchor, fail-closed) — the weak-subjectivity
// anchor check. The fingerprint hashes the preprocessed commitment as a
// labeled component, so the (fingerprint, lanes) pair is self-binding: the
// Rust derivation lane asserts the same pin on the freshly derived
// fingerprint before emitting, which — with blake3 collision resistance —
// ties the lanes to the pinned anchor
// (circuit-prove/src/apex_shrink_gnark_export.rs ApexVkIdentity /
// DREGG_APEX_RECURSION_VK document the collision-resistance argument).
type apexVkIdentity struct {
	Version                int      `json:"version"`
	RecursionVkHex         string   `json:"recursion_vk_hex"`
	ApexPreprocessedCommit []uint32 `json:"apex_preprocessed_commit"`
	Description            string   `json:"description"`
}

const apexVkIdentityPath = "fixtures/apex_vk_identity.json"

// checkApexVkIdentityAnchor is THE governance-anchor check (fail-closed): the
// identity's RecursionVk fingerprint must equal the governance-pinned
// DreggApexRecursionVk constant (settlement_circuit.go). Before this check
// existed, recursion_vk_hex was validated only as 32-byte hex and used in
// error messages — a decorative field; now a doctored/stale identity REJECTS
// at load instead of being trusted because it sits at HEAD.
func checkApexVkIdentityAnchor(id *apexVkIdentity) error {
	if id.RecursionVkHex != DreggApexRecursionVk {
		return fmt.Errorf(
			"apex VK identity recursion_vk_hex %s != governance-pinned DreggApexRecursionVk %s — "+
				"either the identity artifact is doctored/stale, or the apex circuit changed and "+
				"governance has not re-pinned the anchor (re-derive via the Rust lane "+
				"derive_deployed_apex_vk_identity_and_check_fixture, then update the constant in "+
				"settlement_circuit.go AND apex_shrink_gnark_export.rs)",
			id.RecursionVkHex, DreggApexRecursionVk)
	}
	return nil
}

func loadApexVkIdentity(t *testing.T) *apexVkIdentity {
	t.Helper()
	raw, err := os.ReadFile(apexVkIdentityPath)
	if err != nil {
		t.Fatalf("derived apex VK identity must exist (Rust lane emits it via "+
			"apex_shrink_gnark_fixture.rs derive_deployed_apex_vk_identity_and_check_fixture): %v", err)
	}
	id := &apexVkIdentity{}
	if err := json.Unmarshal(raw, id); err != nil {
		t.Fatalf("apex VK identity JSON: %v", err)
	}
	if id.Version != 1 {
		t.Fatalf("apex VK identity version %d (want 1)", id.Version)
	}
	if b, err := hex.DecodeString(id.RecursionVkHex); err != nil || len(b) != 32 {
		t.Fatalf("recursion_vk_hex %q is not a 32-byte hex fingerprint", id.RecursionVkHex)
	}
	// THE ANCHOR CHECK: the fingerprint must be the governance-pinned one.
	if err := checkApexVkIdentityAnchor(id); err != nil {
		t.Fatalf("%v", err)
	}
	if len(id.ApexPreprocessedCommit) != ApexVkLanes {
		t.Fatalf("derived apex VK-core has %d lanes (want %d)",
			len(id.ApexPreprocessedCommit), ApexVkLanes)
	}
	for _, v := range id.ApexPreprocessedCommit {
		requireCanonicalBB(t, v, "derived apex VK-core lane")
	}
	return id
}

// apexPreprocessedCommitConstants bakes the settlement circuit's apex-VK pin
// from the DERIVED deployed identity (loadApexVkIdentity — whose RecursionVk
// fingerprint is asserted equal to the governance-pinned DreggApexRecursionVk
// anchor at load) — NOT from the proof fixture. The fixture's own apex
// VK-core lanes are separately asserted equal to this derived value
// (TestApexPinFixtureMatchesDerivedDeployedIdentity), and the accept test
// closes the loop end-to-end (a fixture minted over any other apex fails the
// pin these constants bake).
func apexPreprocessedCommitConstants(t *testing.T) []*big.Int {
	id := loadApexVkIdentity(t)
	out := make([]*big.Int, len(id.ApexPreprocessedCommit))
	for i, v := range id.ApexPreprocessedCommit {
		out[i] = new(big.Int).SetUint64(uint64(v))
	}
	return out
}

// THE FIXTURE↔DEPLOYED DIFFERENTIAL (gnark half; the Rust half re-derives the
// deployed value from a fresh fold at HEAD): the proof fixture's apex VK-core
// — the claim channel's tail lanes, loader-verified against the labeled copy
// — equals the independently derived deployed identity the settlement
// circuit bakes. A proof fixture minted over a same-shape NON-deployed apex
// is self-consistent (its own claim tail matches its own apex), so THIS
// cross-artifact check, not fixture-internal consistency, is what ties the
// baked pin's value to the deployed apex.
func TestApexPinFixtureMatchesDerivedDeployedIdentity(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	id := loadApexVkIdentity(t)
	if err := apexVkLanesDifferentialErr(fx, id); err != nil {
		t.Fatalf("%v", err)
	}
}

// apexVkLanesDifferentialErr is the cross-artifact lane differential the test
// above enforces: the proof fixture's apex VK-core must equal the derived
// (anchor-checked) identity's lanes, lane for lane.
func apexVkLanesDifferentialErr(fx *shrinkRealFixture, id *apexVkIdentity) error {
	if len(fx.ApexPreprocessedCommit) != len(id.ApexPreprocessedCommit) {
		return fmt.Errorf("fixture apex VK-core has %d lanes, derived deployed identity %d",
			len(fx.ApexPreprocessedCommit), len(id.ApexPreprocessedCommit))
	}
	for i, want := range id.ApexPreprocessedCommit {
		if got := fx.ApexPreprocessedCommit[i]; got != want {
			return fmt.Errorf("fixture apex VK-core lane %d = %d != derived deployed lane %d "+
				"(recursion_vk %s) — the proof fixture was NOT minted over the deployed apex, "+
				"or one artifact is stale; regenerate both via the Rust lanes "+
				"(derive_deployed_apex_vk_identity_and_check_fixture + "+
				"export_real_shrink_fri_fixture_for_gnark)",
				i, got, want, id.RecursionVkHex)
		}
	}
	return nil
}

// THE ANCHOR-CHECK CANARY (gnark half; the Rust half is
// apex_vk_identity_pin_rejects_mismatched_fingerprint): the governance-pinned
// DreggApexRecursionVk anchor is a REAL fail-closed check, not a decorative
// field —
//
//  1. ACCEPT: the honest deployed identity (fixtures/apex_vk_identity.json)
//     passes the anchor check (and loadApexVkIdentity itself enforces it, so
//     every consumer inherits the gate);
//  2. REJECT (fingerprint): an identity carrying a DIFFERENT recursion_vk_hex
//     — one flipped nibble, still a valid 32-byte fingerprint shape — fails
//     checkApexVkIdentityAnchor, i.e. rejects at load;
//  3. REJECT (lanes): an identity carrying lanes the pinned fingerprint does
//     not hash fails the cross-artifact differential
//     (apexVkLanesDifferentialErr) against the loader-verified proof fixture.
//     The Go side cannot recompute the blake3 lane↔fingerprint tie itself
//     (recursion_vk_fingerprint hashes VK shape material beyond the lanes);
//     that tie is enforced in the Rust derivation lane, which computes
//     fingerprint and lanes from the SAME gp.commitment and asserts the
//     fingerprint against the same pin before emitting — this differential is
//     the Go-side tooth that doctored lanes cannot pass.
func TestApexVkIdentityAnchorRejectsMismatchedFingerprint(t *testing.T) {
	honest := loadApexVkIdentity(t) // the load path itself enforces the anchor
	if err := checkApexVkIdentityAnchor(honest); err != nil {
		t.Fatalf("the honest deployed identity must match the governance pin: %v", err)
	}

	t.Run("doctored-fingerprint-rejects-at-load", func(t *testing.T) {
		doctored := *honest
		b := []byte(doctored.RecursionVkHex)
		if b[0] == '0' {
			b[0] = '1'
		} else {
			b[0] = '0'
		}
		doctored.RecursionVkHex = string(b)
		if err := checkApexVkIdentityAnchor(&doctored); err == nil {
			t.Fatal("an identity with a NON-pinned recursion_vk_hex was ACCEPTED — " +
				"the governance anchor is decorative")
		}
	})

	t.Run("doctored-lanes-reject-the-fixture-differential", func(t *testing.T) {
		fx := loadShrinkRealFixture(t)
		doctored := *honest
		doctored.ApexPreprocessedCommit = append([]uint32(nil), honest.ApexPreprocessedCommit...)
		doctored.ApexPreprocessedCommit[0]++
		if err := apexVkLanesDifferentialErr(fx, &doctored); err == nil {
			t.Fatal("an identity with lanes the pinned fingerprint does not hash passed the " +
				"cross-artifact differential — doctored lanes under an honest fingerprint " +
				"would go undetected")
		}
	})
}

// shrinkDigestWordAt returns the flat digest-stream word at `off` (the same
// flattening the loc offsets index).
func shrinkDigestWordAt(t *testing.T, fx *shrinkRealFixture, off int) fr.Element {
	t.Helper()
	var words []fr.Element
	for _, ev := range fx.PrefixEvents {
		if ev.Kind == "observe_digest" {
			for _, w := range ev.Words {
				words = append(words, parseBn254Hex(t, w))
			}
		}
	}
	if off < 0 || off >= len(words) {
		t.Fatalf("digest word offset %d out of range (%d words)", off, len(words))
	}
	return words[off]
}

// shrinkPreprocessedRoot extracts the preprocessed (VK-core) commitment
// digest from the transcript prefix — the constant the settlement circuit
// pins (the shrink-VK pin).
func shrinkPreprocessedRoot(t *testing.T, fx *shrinkRealFixture, loc shrinkStarkPrefixLoc) *big.Int {
	t.Helper()
	e := shrinkDigestWordAt(t, fx, loc.preDigOff)
	return frToBig(e)
}

// assignSettlementPublics fills the 25 public lanes in the pinned order
// genesis8 ++ final8 ++ numTurns ++ chainDigest8.
func assignSettlementPublics(c *SettlementCircuit, claim []uint32) {
	k := 0
	for i := 0; i < DigestWidth; i++ {
		c.GenesisRoot[i] = claim[k]
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		c.FinalRoot[i] = claim[k]
		k++
	}
	c.NumTurns = claim[k]
	k++
	for i := 0; i < DigestWidth; i++ {
		c.ChainDigest[i] = claim[k]
		k++
	}
}

// ACCEPT: the assembled circuit verifies the REAL shrink proof end to end
// WITH the correct 25-lane public statement.
func TestSettlementCircuitAcceptsRealProofWithCorrectStatement(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym),
		assignSettlementCircuit(t, fx, ex, sym), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("assembled circuit rejected the REAL shrink proof + correct statement: %v", err)
	}
}

// THE DECISIVE CANARY: a WRONG public root lane must FAIL — a proof must not
// settle a root it doesn't attest. Three escalation levels:
//
//  1. wrong public input, honest transcript — the claim equality tooth fires;
//  2. wrong public input + matching tampered transcript pv lane — the
//     Fiat-Shamir sample pins fire (the absorbed claim seeds every challenge);
//  3. wrong public input + tampered pv lane + ALL samples re-derived through
//     the reference challenger (a fully self-consistent forged transcript) —
//     the proof data itself (Merkle openings, fold chains, quotient
//     identities) no longer verifies against the forged challenges. This is
//     the "re-prove or fail" floor: only a genuine proof FOR the forged
//     statement could pass, and the prover doesn't have one.
func TestSettlementCircuitRejectsWrongStatement(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()
	claim := fx.TablePublics[fx.ClaimInstance]
	claimObsOff := ex.loc.pubObsOffOf(fx.ClaimInstance)

	t.Run("wrong-genesis-lane-public-only", func(t *testing.T) {
		w := assignSettlementCircuit(t, fx, ex, sym)
		w.GenesisRoot[0] = bbAddRef(claim[0], 1)
		if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w, field); err == nil {
			t.Fatal("circuit ACCEPTED a genesis root the proof does not attest")
		}
	})
	t.Run("wrong-final-root-lane-public-only", func(t *testing.T) {
		w := assignSettlementCircuit(t, fx, ex, sym)
		w.FinalRoot[3] = bbAddRef(claim[8+3], 1)
		if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w, field); err == nil {
			t.Fatal("circuit ACCEPTED a final root the proof does not attest")
		}
	})
	t.Run("wrong-num-turns-public-only", func(t *testing.T) {
		w := assignSettlementCircuit(t, fx, ex, sym)
		w.NumTurns = bbAddRef(claim[16], 1)
		if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w, field); err == nil {
			t.Fatal("circuit ACCEPTED a turn count the proof does not attest")
		}
	})

	t.Run("wrong-root-with-matching-transcript-lane", func(t *testing.T) {
		w := assignSettlementCircuit(t, fx, ex, sym)
		forged := bbAddRef(claim[0], 1)
		w.GenesisRoot[0] = forged
		w.PrefixObs[claimObsOff] = forged // consistent absorb — FS pins fire
		if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w, field); err == nil {
			t.Fatal("circuit ACCEPTED a forged claim with a matching transcript lane")
		}
	})

	t.Run("wrong-root-with-fully-rederived-transcript", func(t *testing.T) {
		w := assignSettlementCircuit(t, fx, ex, sym)
		forged := bbAddRef(claim[0], 1)
		w.GenesisRoot[0] = forged
		w.PrefixObs[claimObsOff] = forged
		// Re-derive EVERY sampled challenge through the reference challenger
		// over the forged observe stream, so the transcript replay is fully
		// self-consistent — the residual inconsistency is the PROOF DATA
		// itself (commitments, openings, fold chains, identities).
		c := newMultiFieldChallengerRef()
		io, is := 0, 0
		for _, ev := range fx.PrefixEvents {
			switch ev.Kind {
			case "observe_bb":
				vals := make([]uint32, len(ev.Values))
				for k := range ev.Values {
					v, ok := w.PrefixObs[io+k].(uint32)
					if !ok {
						t.Fatalf("prefix obs %d is not a uint32 witness", io+k)
					}
					vals[k] = v
				}
				c.observeBabyBearSlice(vals)
				io += len(ev.Values)
			case "observe_digest":
				words := make([]fr.Element, len(ev.Words))
				for k, wd := range ev.Words {
					words[k] = parseBn254Hex(t, wd)
				}
				c.observeBn254Digest(words)
			case "sample_bb":
				for range ev.Values {
					w.PrefixSamples[is] = c.sampleBabyBear()
					is++
				}
			}
		}
		if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w, field); err == nil {
			t.Fatal("circuit ACCEPTED a forged claim with a fully re-derived transcript " +
				"(the proof data should not verify against forged challenges)")
		}
	})
}

// BINDING canary: tampering an opened trace value INSIDE the transcript
// stream must fail — the algebra layer consumes the same variables the
// challenger absorbed, so the transcript pin catches in-stream tampering.
func TestSettlementCircuitBindsOpenings(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	w := assignSettlementCircuit(t, fx, ex, sym)
	tampered := ex.loc.openedObsOff // first coordinate of the first opened value
	w.PrefixObs[tampered] = bbAddRef(ex.openedEF[0][0], 1)
	if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w,
		ecc.BN254.ScalarField()); err == nil {
		t.Fatal("assembled circuit ACCEPTED a tampered in-transcript opened value")
	}
}

// APEX-VK-PIN CANARY (tooth 2 — THE FORGERY CLOSURE): a same-shape malicious
// apex is, from this circuit's viewpoint, a shrink whose re-exposed apex
// VK-core lanes differ from the DEPLOYED dregg apex's baked constants. Both
// directions must reject:
//
//  1. witness lanes ≠ baked constant (the attacker's exposed VK core differs
//     from the deployed pin) — the pin fires; note the tampered lane is also
//     transcript-absorbed, so the FS pins fire too (defense in depth);
//  2. baked constant ≠ honest witness (ISOLATES the pin: every other
//     constraint — transcript, algebra, FRI, open_input, claim binding — is
//     satisfied by the honest fixture, so the ONLY failing assert is the
//     apex-VK pin; this proves the pin constraint exists and binds).
//
// The honest fixture (the REAL dregg apex) still ACCEPTS — that is
// TestSettlementCircuitAcceptsRealProofWithCorrectStatement, which runs with
// the pin set.
func TestSettlementCircuitPinsApexPreprocessedCommitment(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	field := ecc.BN254.ScalarField()
	claimObsOff := ex.loc.pubObsOffOf(fx.ClaimInstance)

	for lane := 0; lane < ApexVkLanes; lane += ApexVkLanes - 1 { // first and last lane
		t.Run(fmt.Sprintf("witness-vk-lane-%d-differs-from-deployed-constant", lane), func(t *testing.T) {
			w := assignSettlementCircuit(t, fx, ex, sym)
			honest := fx.ApexPreprocessedCommit[lane]
			w.PrefixObs[claimObsOff+NumPublicInputs+lane] = bbAddRef(honest, 1)
			if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w, field); err == nil {
				t.Fatal("circuit ACCEPTED an apex VK-core lane that differs from the deployed " +
					"apex's preprocessed commitment (the same-shape-apex forgery is OPEN)")
			}
		})
	}

	t.Run("baked-constant-differs-isolates-the-pin", func(t *testing.T) {
		c := allocSettlementCircuit(t, fx, ex, sym)
		// Doctor the BAKED constant: simulate this circuit having been pinned
		// to a different (deployed) apex than the one the proof verifies. The
		// honest witness satisfies EVERYTHING else, so a reject here is
		// attributable to the apex-VK pin alone.
		c.apexPreprocessedCommit[0] = new(big.Int).Add(c.apexPreprocessedCommit[0], big.NewInt(1))
		if err := test.IsSolved(c, assignSettlementCircuit(t, fx, ex, sym), field); err == nil {
			t.Fatal("circuit with a different deployed-apex pin ACCEPTED the honest witness — " +
				"the apex-VK pin assert is not binding")
		}
	})

	t.Run("unpinned-control-accepts", func(t *testing.T) {
		// Control: with the apex pin REMOVED (and everything else identical),
		// the honest witness still accepts — so the rejects above are the
		// pin's teeth, not shape drift.
		c := allocSettlementCircuit(t, fx, ex, sym)
		c.apexPreprocessedCommit = nil
		w := assignSettlementCircuit(t, fx, ex, sym)
		w.apexPreprocessedCommit = nil
		if err := test.IsSolved(c, w, field); err != nil {
			t.Fatalf("unpinned control rejected the honest witness (shape drift?): %v", err)
		}
	})
}

// VK-pin canary: a witness carrying a DIFFERENT preprocessed (VK-core)
// commitment digest must fail the baked constant pin.
func TestSettlementCircuitPinsShrinkVkPreprocessedRoot(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	w := assignSettlementCircuit(t, fx, ex, sym)
	// The preprocessed digest is PrefixDigests[loc.preDigOff].
	e := shrinkDigestWordAt(t, fx, ex.loc.preDigOff)
	one := fr.One()
	e.Add(&e, &one)
	w.PrefixDigests[ex.loc.preDigOff] = frToBig(e)
	if err := test.IsSolved(allocSettlementCircuit(t, fx, ex, sym), w,
		ecc.BN254.ScalarField()); err == nil {
		t.Fatal("assembled circuit ACCEPTED a proof under a different shrink VK core")
	}
}
