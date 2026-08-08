// R1CS PROFILE of the SettlementCircuit — attribute the ~12.87M constraints
// across the Define's phases (transcript replay + pins, STARK algebra, FRI
// core, open_input) and, inside the algebra phase, per instance.
//
// METHOD: phase-stripped compiles. settlementProfileCircuit replicates the
// SettlementCircuit Define body EXACTLY (same gadget calls, same order) with
// an early return after each phase; the per-phase R1CS is the delta between
// consecutive compiles. DRIFT CANARY: the full-phase profile compile must
// count EXACTLY the real SettlementCircuit's compile — if the replicated body
// drifts from settlement_circuit.go, the profile test fails rather than
// reporting stale numbers.
//
// Heavy (minutes of compile): run with
//
//	cd chain/gnark && DREGG_PROFILE=1 go test -run TestSettlementR1CSProfile -v -timeout 120m
package friverifier

import (
	"os"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

// Profile phases, cumulative: each compile includes all previous phases.
const (
	profPhaseTranscript = 1 // hygiene + transcript replay + claim binding + VK pins
	profPhaseAlgebra    = 2 // + VerifyShrinkStarkAlgebra
	profPhaseFri        = 3 // + VerifyFriNative
	profPhaseFull       = 4 // + open_input == the real SettlementCircuit
)

// settlementProfileCircuit is the phase-stripped twin. The Define body below
// is a LINE-FOR-LINE copy of SettlementCircuit.Define (settlement_circuit.go)
// with early returns; the drift canary in TestSettlementR1CSProfile pins the
// full variant to the real circuit's constraint count.
type settlementProfileCircuit struct {
	SettlementCircuit
	phases int
}

func (c *settlementProfileCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallenger(bb)

	if c.sym == nil {
		panic("settlementProfileCircuit: emitted symbolic constraints are required")
	}

	// ---- Phase 1: public-statement hygiene + transcript replay + claim
	// binding + VK pins.
	for i := 0; i < DigestWidth; i++ {
		bb.AssertIsCanonical(c.GenesisRoot[i])
		bb.AssertIsCanonical(c.FinalRoot[i])
		bb.AssertIsCanonical(c.ChainDigest[i])
	}
	bb.AssertIsCanonical(c.NumTurns)

	io, id, is := 0, 0, 0
	for _, op := range c.script {
		switch op.kind {
		case "observe_bb":
			ch.ObserveBabyBearSlice(c.PrefixObs[io : io+op.n])
			io += op.n
		case "observe_digest":
			ch.ObserveBn254Digest(c.PrefixDigests[id : id+op.n])
			id += op.n
		case "sample_bb":
			for k := 0; k < op.n; k++ {
				api.AssertIsEqual(ch.SampleBabyBear(), c.PrefixSamples[is])
				is++
			}
		}
	}

	claim := c.PrefixObs[c.loc.pubObsOffOf(c.claimInstance) : c.loc.pubObsOffOf(c.claimInstance)+
		c.loc.pubLens[c.claimInstance]]
	if len(claim) != ExposedShrinkClaimLanes {
		panic("settlementProfileCircuit: claim channel is not the pinned statement")
	}
	k := 0
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(claim[k], c.GenesisRoot[i])
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(claim[k], c.FinalRoot[i])
		k++
	}
	api.AssertIsEqual(claim[k], c.NumTurns)
	k++
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(claim[k], c.ChainDigest[i])
		k++
	}

	if c.vkPreprocessedRoot != nil {
		api.AssertIsEqual(c.PrefixDigests[c.loc.preDigOff], c.vkPreprocessedRoot)
	}
	if c.apexPreprocessedCommit != nil {
		if len(c.apexPreprocessedCommit) != ApexVkLanes {
			panic("settlementProfileCircuit: apexPreprocessedCommit lane count")
		}
		for i, want := range c.apexPreprocessedCommit {
			api.AssertIsEqual(claim[ApexClaimLanes+i], want)
		}
	}
	if c.rootVkSpine != nil {
		if len(c.rootVkSpine) != VkSpineLanes {
			panic("settlementProfileCircuit: rootVkSpine lane count")
		}
		for i, want := range c.rootVkSpine {
			api.AssertIsEqual(claim[NumPublicInputs+i], want)
		}
	}
	if c.phases == profPhaseTranscript {
		return nil
	}

	// ---- Phase 2: STARK-algebra layer.
	groupEF := func(vars []frontend.Variable) []BBExt {
		out := make([]BBExt, len(vars)/4)
		for i := range out {
			copy(out[i][:], vars[4*i:4*i+4])
		}
		return out
	}
	sampleExt := func(off int) BBExt {
		var e BBExt
		copy(e[:], c.PrefixSamples[off:off+4])
		return e
	}
	openedEF := groupEF(c.PrefixObs[c.loc.openedObsOff : c.loc.openedObsOff+c.loc.openedObsLen])
	zeta := sampleExt(c.loc.zetaSampleOff)
	pubVals := make([][]frontend.Variable, len(c.shapes))
	for i := range c.shapes {
		off := c.loc.pubObsOffOf(i)
		pubVals[i] = c.PrefixObs[off : off+c.loc.pubLens[i]]
	}
	VerifyShrinkStarkAlgebra(bb, c.shapes,
		openedEF,
		groupEF(c.PrefixObs[c.loc.cumObsOff:c.loc.cumObsOff+c.loc.cumObsLen]),
		pubVals,
		ShrinkStarkChallenges{
			PermAlpha: sampleExt(c.loc.permChSampleOff),
			PermBeta:  sampleExt(c.loc.permChSampleOff + 4),
			Alpha:     sampleExt(c.loc.alphaSampleOff),
			Zeta:      zeta,
		},
		c.sym)
	if c.phases == profPhaseAlgebra {
		return nil
	}

	// ---- Phase 3: FRI core.
	queryBits := VerifyFriNative(bb, c.cfg, c.r, c.CommitRoots, c.FinalPoly, c.PowWitness,
		c.Queries, c.rollInAfterRound, ch)
	if c.phases == profPhaseFri {
		return nil
	}

	// ---- Phase 4: open_input.
	roots := make([]frontend.Variable, len(c.loc.inputRootDigOff))
	for i, off := range c.loc.inputRootDigOff {
		roots[i] = c.PrefixDigests[off]
	}
	pre := NewOpenInputPrecomp(bb, c.inputRounds, zeta, sampleExt(c.loc.friAlphaOff),
		openedEF, c.r+c.cfg.LogBlowup+c.cfg.LogFinalPolyLen)
	for qi := range c.Queries {
		BindOpenInputToFriSeedsNative(bb, c.inputRounds, pre, queryBits[qi], roots,
			c.InputOpenings[qi], c.Queries[qi], c.rollInAfterRound)
	}
	return nil
}

func requireProfileEnv(t *testing.T) {
	t.Helper()
	if os.Getenv("DREGG_PROFILE") == "" {
		t.Skip("R1CS profiling (multi-minute compiles); run with DREGG_PROFILE=1")
	}
}

func compileCount(t *testing.T, c frontend.Circuit) int {
	t.Helper()
	t0 := time.Now()
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, c)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	n := cs.GetNbConstraints()
	t.Logf("    compiled %d constraints in %s", n, time.Since(t0).Round(time.Millisecond))
	return n
}

// TestSettlementR1CSProfile compiles the phase-stripped variants and reports
// the per-phase R1CS table. The full variant is pinned to the REAL
// SettlementCircuit compile (drift canary).
func TestSettlementR1CSProfile(t *testing.T) {
	requireProfileEnv(t)
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)

	counts := map[int]int{}
	for _, ph := range []int{profPhaseTranscript, profPhaseAlgebra, profPhaseFri, profPhaseFull} {
		t.Logf("compiling phases <= %d ...", ph)
		counts[ph] = compileCount(t, &settlementProfileCircuit{
			SettlementCircuit: *allocSettlementCircuit(t, fx, ex, sym),
			phases:            ph,
		})
	}

	t.Logf("compiling the REAL SettlementCircuit (drift canary) ...")
	real := compileCount(t, allocSettlementCircuit(t, fx, ex, sym))
	if real != counts[profPhaseFull] {
		t.Fatalf("DRIFT: profile full variant %d constraints != real SettlementCircuit %d — "+
			"settlementProfileCircuit.Define no longer mirrors settlement_circuit.go",
			counts[profPhaseFull], real)
	}

	total := float64(real)
	phase := func(name string, n int) {
		t.Logf("%-28s %10d  %5.1f%%", name, n, 100*float64(n)/total)
	}
	t.Logf("=== SettlementCircuit R1CS breakdown (total %d) ===", real)
	phase("transcript replay + pins", counts[profPhaseTranscript])
	phase("STARK algebra (constraint eval)", counts[profPhaseAlgebra]-counts[profPhaseTranscript])
	phase("FRI core", counts[profPhaseFri]-counts[profPhaseAlgebra])
	phase("open_input", counts[profPhaseFull]-counts[profPhaseFri])
}

// ---------------------------------------------------------------------------
// Per-instance constraint-eval sub-compiles (the algebra phase, split)
// ---------------------------------------------------------------------------

// symEvalProfileCircuit isolates ONE instance's symbolic-DAG evaluation: all
// inputs enter as witness (no canonicity/transcript costs — those are counted
// in the transcript phase), the folded value is bound to a witness output.
type symEvalProfileCircuit struct {
	sym   *SymbolicConstraints
	inst  int
	shape StarkInstanceShape

	TraceLocal   []BBExt
	TraceNext    []BBExt
	PreLocal     []BBExt
	PreNext      []BBExt
	PermLocal    []BBExt
	PermNext     []BBExt
	Challenges   []BBExt
	PermValues   []BBExt
	PublicValues []frontend.Variable
	SelFirst     BBExt
	SelLast      BBExt
	SelTrans     BBExt
	Alpha        BBExt
	Out          BBExt
}

func allocSymEvalProfileCircuit(sym *SymbolicConstraints, inst int, sh StarkInstanceShape) *symEvalProfileCircuit {
	c := &symEvalProfileCircuit{
		sym:        sym,
		inst:       inst,
		shape:      sh,
		TraceLocal: make([]BBExt, sh.Width),
		PreLocal:   make([]BBExt, sh.PreWidth),
		PermLocal:  make([]BBExt, sh.NumLookups),
		PermNext:   make([]BBExt, sh.NumLookups),
		Challenges: make([]BBExt, 2*sh.NumLookups),
		PermValues: make([]BBExt, sh.NumGlobalLookups),
	}
	if sh.HasTraceNext {
		c.TraceNext = make([]BBExt, sh.Width)
	}
	if sh.HasPreNext {
		c.PreNext = make([]BBExt, sh.PreWidth)
	}
	if sh.NumPublicValues > 0 {
		c.PublicValues = make([]frontend.Variable, sh.NumPublicValues)
	}
	return c
}

func (c *symEvalProfileCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	in := symEvalInputsNative{
		TraceLocal: c.TraceLocal,
		PreLocal:   c.PreLocal,
		PermLocal:  c.PermLocal,
		PermNext:   c.PermNext,
		Challenges: c.Challenges,
		PermValues: c.PermValues,
		Sel: starkSelectorsNative{
			isFirstRow:   c.SelFirst,
			isLastRow:    c.SelLast,
			isTransition: c.SelTrans,
		},
	}
	if c.shape.HasTraceNext {
		in.TraceNext = c.TraceNext
	}
	if c.shape.HasPreNext {
		in.PreNext = c.PreNext
	}
	if c.shape.NumPublicValues > 0 {
		in.PublicValues = make([]BBExt, len(c.PublicValues))
		for k, v := range c.PublicValues {
			in.PublicValues[k] = BBExt{v, 0, 0, 0}
		}
	}
	folded := evalSymbolicFoldedNative(bb, &c.sym.Instances[c.inst], in, c.Alpha)
	bb.ExtAssertIsEqual(folded, c.Out)
	return nil
}

// TestSettlementEvalInstanceR1CSProfile compiles each instance's DAG eval in
// isolation and reports its R1CS.
func TestSettlementEvalInstanceR1CSProfile(t *testing.T) {
	requireProfileEnv(t)
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)

	t.Logf("=== per-instance constraint-eval R1CS (inputs as free witness) ===")
	for i := range sym.Instances {
		inst := &sym.Instances[i]
		n := compileCount(t, allocSymEvalProfileCircuit(sym, i, ex.shapes[i]))
		t.Logf("%-18s nodes=%5d constraints=%4d  R1CS=%8d",
			inst.Name, len(inst.Nodes), len(inst.Constraints), n)
	}
}

// ---------------------------------------------------------------------------
// Marginal gadget costs (chained-op deltas; fixed rangecheck-table costs
// cancel in the subtraction)
// ---------------------------------------------------------------------------

type extOpChainCircuit struct {
	op   string
	n    int
	A, B BBExt
}

func (c *extOpChainCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	x := c.A
	for i := 0; i < c.n; i++ {
		switch c.op {
		case "mul":
			x = bb.ExtMul(x, c.B)
		case "add":
			x = bb.ExtAdd(x, c.B)
		case "sub":
			x = bb.ExtSub(x, c.B)
		}
	}
	bb.ExtAssertIsEqual(x, c.B)
	return nil
}

type baseOpChainCircuit struct {
	op   string
	n    int
	A, B frontend.Variable
}

func (c *baseOpChainCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	x := c.A
	for i := 0; i < c.n; i++ {
		switch c.op {
		case "mul":
			x = bb.Mul(x, c.B)
		case "add":
			x = bb.Add(x, c.B)
		case "canon":
			bb.AssertIsCanonical(x)
			x = c.B
		}
	}
	api.AssertIsEqual(x, c.B)
	return nil
}

type poseidonChainCircuit struct {
	n    int
	A, B frontend.Variable
}

func (c *poseidonChainCircuit) Define(api frontend.API) error {
	x := c.A
	for i := 0; i < c.n; i++ {
		x = Poseidon2Bn254Compress(api, x, c.B)
	}
	api.AssertIsEqual(x, c.B)
	return nil
}

// TestSettlementGadgetMarginalCosts reports the per-op marginal R1CS of the
// primitives the phases are built from.
func TestSettlementGadgetMarginalCosts(t *testing.T) {
	requireProfileEnv(t)
	marginal := func(name string, mk func(n int) frontend.Circuit) {
		t.Helper()
		lo, hi := 64, 192
		a := compileCount(t, mk(lo))
		b := compileCount(t, mk(hi))
		t.Logf("%-24s marginal %.2f R1CS/op", name, float64(b-a)/float64(hi-lo))
	}
	marginal("BBExt ExtMul", func(n int) frontend.Circuit { return &extOpChainCircuit{op: "mul", n: n} })
	marginal("BBExt ExtAdd", func(n int) frontend.Circuit { return &extOpChainCircuit{op: "add", n: n} })
	marginal("BBExt ExtSub", func(n int) frontend.Circuit { return &extOpChainCircuit{op: "sub", n: n} })
	marginal("BB Mul (reduce 62)", func(n int) frontend.Circuit { return &baseOpChainCircuit{op: "mul", n: n} })
	marginal("BB Add (reduce 32)", func(n int) frontend.Circuit { return &baseOpChainCircuit{op: "add", n: n} })
	marginal("BB AssertIsCanonical", func(n int) frontend.Circuit { return &baseOpChainCircuit{op: "canon", n: n} })
	marginal("Poseidon2Bn254Compress", func(n int) frontend.Circuit { return &poseidonChainCircuit{n: n} })
}
