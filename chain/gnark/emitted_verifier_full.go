// GENERIC interpreter for the COMPACT full-verifier descriptor
// (schema "dregg.gnark.verifier_full.v1", emitted by
// Dregg2/Circuit/Emit/GnarkVerifier/EmitJson.lean `emitVerifierFullJson`,
// byte-pinned by #guard against chain/gnark/emitted/verifier_full.json).
//
// Unlike the flat toy grammar (emitted_interp.go: every constraint is an
// op-DAG node), this descriptor is the SIX-leaf `emitVerifier` composition
// (EmitVerifier.lean, one leaf per `verifyAlgoO` conjunct in disjoint
// `Nat.pair` variable blocks) tagged with the deployed apex-shrink fixture
// MULTIPLICITIES. The heavy constraint content is DEFERRED to interp time:
// this file materializes each gadget record by invoking the SAME hand-Go
// gadget the settlement circuit uses (Poseidon2Bn254 compress, BabyBear
// reduce/mul, the degree-4 extension mul, the Merkle-path walk, 31-bit range
// checks, and — for the batch-STARK block — the emitted symbolic-DAG
// evaluator), replicated `count` times over FRESH witness variables and
// wired per the emitted structure. Compiling the result to an R1CS confirms
// the whole op-set expands and lets us count the materialized constraints.
//
// Faithfulness posture (named, not silent). The Lean side is explicit
// (EmitJson.lean §4): the compact descriptor is NOT covered by
// `emit_faithful`; the interpreter's per-gadget expansion is the obligation,
// and the `derived` block is the parity oracle (fold_rows,
// commit/input_merkle_compressions, segment_lane_asserts). This interpreter
// asserts that parity before building (Plan.checkDerivedParity).
//
// TWO NAMED SEAMS surfaced by this expansion (see the report / block 3 + the
// scope note on ExpandBlock):
//
//  1. The "stark_constraint_dag" / "logup_sum" records (block 3) are NOT
//     self-contained in verifier_full.json — the manifest carries only the
//     per-instance degree_bits, not the constraint DAG. Their faithful
//     expansion requires the COMPANION emitted artifact
//     fixtures/shrink_symbolic_constraints.json (the same file
//     stark_constraint_interp.go loads + validates), supplied as `sym`. With
//     sym==nil block 3 fail-closes with a clear error rather than fabricating
//     a constraint DAG.
//
//  2. The compact descriptor models the composed `emitVerifier` (the six
//     refinement leaves), which is a STRUCTURAL abstraction of the verifier —
//     it does NOT carry the SettlementCircuit's full transcript-replay
//     challenger duplex, the native FRI fold arithmetic beyond the fold-row
//     ext-muls, or the open_input seed binding. So the materialized total is
//     the emitVerifier-leaf budget (dominated by the 8436 Merkle Poseidon2
//     compressions), which is SMALLER than the hand-Go SettlementCircuit's
//     ~12.87M; the delta is exactly those un-modeled settlement phases. The
//     report states the measured number and this gap plainly.
package friverifier

import (
	"encoding/json"
	"errors"
	"fmt"
	"math/big"
	"os"
	"sort"

	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/rangecheck"
)

func init() {
	solver.RegisterHint(queryPowBitsHint)
}

// queryPowDecompBits is the fixed ToBinary width of the Lean QueryPow template
// (`queryPowCircuit`: `rangeAsserts (.var 0) 1 31`, QueryPowEmit.lean §1) — the
// canonical BabyBear-value decomposition width (`< p < 2^31`).
const queryPowDecompBits = 31

// queryPowBitsHint decomposes one field element into its low 31 little-endian bits
// (values only — NO constraints). The QueryPow template the replay drives imposes
// booleanity (`bit·bit = bit`) and recomposition (`Σ bitᵢ·2ⁱ = value`) on these
// bits, so a wrong decomposition is UNSATISFIABLE: the hint bears on completeness
// (the honest fill exists iff value < 2^31), never on soundness. bit `i` of the
// value lands on template variable `1+i` (`powAsg v (1+i) = value.val / 2^i % 2`).
func queryPowBitsHint(_ *big.Int, inputs, outputs []*big.Int) error {
	if len(inputs) != 1 || len(outputs) != queryPowDecompBits {
		return errors.New("queryPowBitsHint: expected 1 input, 31 outputs")
	}
	v := inputs[0]
	for i := range outputs {
		outputs[i].SetUint64(uint64(v.Bit(i)))
	}
	return nil
}

// ---------------------------------------------------------------------------
// §1  The v1 descriptor grammar (Go mirror of emitVerifierFullJson's JSON).
// ---------------------------------------------------------------------------

// VFShape is the fixture-shape block.
type VFShape struct {
	LogBlowup           int `json:"log_blowup"`
	NumQueries          int `json:"num_queries"`
	Rounds              int `json:"rounds"`
	LogFinalPolyLen     int `json:"log_final_poly_len"`
	MaxLogArity         int `json:"max_log_arity"`
	QueryPowBits        int `json:"query_pow_bits"`
	CommitPowBits       int `json:"commit_pow_bits"`
	ExtraQueryIndexBits int `json:"extra_query_index_bits"`
	LogGlobalMaxHeight  int `json:"log_global_max_height"`
	DigestWidth         int `json:"digest_width"`
	NumPublicLanes      int `json:"num_public_lanes"`
	ExtDegree           int `json:"ext_degree"`
	FoldArity           int `json:"fold_arity"`
	NumInstances        int `json:"num_instances"`
	InputRounds         int `json:"input_rounds"`
}

// VFVarBlock is one composition block (its Nat.pair key + verifyAlgoO role).
type VFVarBlock struct {
	Block   int    `json:"block"`
	PairKey int    `json:"pair_key"`
	Role    string `json:"role"`
}

// VFGadget is one compact gadget-invocation record: the composition block, the
// gnark gadget NAME (the leaf's own .gadgets name), the primitive the
// interpreter EXPANDS it through, the fixture-shape MULTIPLICITY, and the
// integer params the expansion needs (flat map key -> int list).
type VFGadget struct {
	Block  int              `json:"block"`
	Gadget string           `json:"gadget"`
	Expand string           `json:"expand"`
	Count  int              `json:"count"`
	Params map[string][]int `json:"params"`
}

// VFDerived is the parity oracle for the interpreter's unroll.
type VFDerived struct {
	FoldRows                 int `json:"fold_rows"`
	CommitMerkleCompressions int `json:"commit_merkle_compressions"`
	InputMerkleCompressions  int `json:"input_merkle_compressions"`
	SegmentLaneAsserts       int `json:"segment_lane_asserts"`
}

// VerifierFull is the parsed compact descriptor.
type VerifierFull struct {
	Schema    string       `json:"schema"`
	Name      string       `json:"name"`
	Fixture   string       `json:"fixture"`
	Source    string       `json:"source"`
	Shape     VFShape      `json:"shape"`
	VarBlocks []VFVarBlock `json:"var_blocks"`
	Gadgets   []VFGadget   `json:"gadgets"`
	Derived   VFDerived    `json:"derived"`
}

const verifierFullSchema = "dregg.gnark.verifier_full.v1"

// knownVFGadgets are the (gadget, expand) pairs this interpreter carries. A
// record naming anything else fail-closes: an unknown pair would mean an
// emitter recording an expansion this replayer does not implement.
var knownVFGadgets = map[[2]string]bool{
	{"AssertIsCanonical", "rangecheck"}:                            true,
	{"FriFoldRowArity2", "babybear_ext_mul"}:                       true,
	{"ExtAssertIsEqual", "babybear_ext_eq"}:                        true,
	{"VerifyMerklePathBn254", "poseidon2_bn254_compress"}:          true,
	{"VerifyMerklePathBn254InputOpen", "poseidon2_bn254_compress"}: true,
	{"BatchTableInstance", "stark_constraint_dag"}:                 true,
	{"LogUpBalance", "logup_sum"}:                                  true,
	{"SampleBitsDecomposed", "rangecheck"}:                         true,
	{"AssertPowBitsZero", "zero_low_bits"}:                         true,
	{"AssertIsEqual", "wire_eq"}:                                   true,
}

// inputBatchTemplatePaths maps a round's per-class row-width signature to the
// committed Lean-emitted multi-height MMCS batch-opening template
// (InputOpenBatchEmit.lean `batchData widths 19 katMask`, §12). The apex-shrink
// fixture's four input rounds (trace / quotient / preprocessed / permutation)
// share the height classes {19,18,12,3} and the {0,6,15} injection schedule but
// differ in per-class row widths; each shape has its own emitted template. Round
// 1 ([8,16,16,8]) is the originally-committed template; the other three shapes
// are emitted from the SAME `batchData` (proven by `inputOpenBatch_refines`,
// parametric over widths) at the deployed round widths.
var inputBatchTemplatePaths = map[string]string{
	"8,16,16,8":    "emitted/inputopen_batch_template.json",
	"76,304,8,164": "emitted/inputopen_batch_r0.json",
	"59,26,8,82":   "emitted/inputopen_batch_r2.json",
	"72,32,8,164":  "emitted/inputopen_batch_r3.json",
}

// widthsSig is the comma-joined per-class width signature used to key the batch
// templates and the descriptor round shapes.
func widthsSig(widths []int) string {
	s := ""
	for i, w := range widths {
		if i > 0 {
			s += ","
		}
		s += fmt.Sprintf("%d", w)
	}
	return s
}

// inputOpenRoundWidths reads the per-round per-class row widths from the
// input-open gadget's descriptor params: `round_widths` is the class widths of
// every input round flattened in round order, `class_heights` gives the shared
// (tallest-first) height classes — so its length is the per-round class count and
// its head is the batch-tree max log-height (maxLh = path depth). Returns
// [round][class] widths and maxLh.
func inputOpenRoundWidths(g VFGadget) ([][]int, int, error) {
	classHeights := g.Params["class_heights"]
	if len(classHeights) == 0 {
		return nil, 0, fmt.Errorf("VerifyMerklePathBn254InputOpen: missing class_heights param " +
			"(descriptor not extended with per-round height-class + row widths)")
	}
	nClasses := len(classHeights)
	maxLh := classHeights[0]
	flat := g.Params["round_widths"]
	if len(flat) == 0 || len(flat)%nClasses != 0 {
		return nil, 0, fmt.Errorf("VerifyMerklePathBn254InputOpen: round_widths length %d "+
			"is not a positive multiple of the class count %d", len(flat), nClasses)
	}
	nr := len(flat) / nClasses
	rw := make([][]int, nr)
	for r := 0; r < nr; r++ {
		rw[r] = flat[r*nClasses : (r+1)*nClasses]
	}
	return rw, maxLh, nil
}

// checkBatchTemplateShape fail-closes if a loaded batch template's own gadget
// provenance / boundary does not match the round it is being used for: the
// template's `VerifyOpenInputBatchBn254 [R, maxLh]` record and its single root
// boundary at var R must agree with the descriptor's round widths sum R and
// maxLh. This ties the emitted artifact to the shape the interpreter replays it
// at (an emitter/interpreter drift would be caught here, not silently wired).
func checkBatchTemplateShape(tpl *Template, R, maxLh int) error {
	if len(tpl.Gadgets) != 1 || tpl.Gadgets[0].Gadget != "VerifyOpenInputBatchBn254" {
		return fmt.Errorf("batch template %q: unexpected gadget provenance %v "+
			"(want a single VerifyOpenInputBatchBn254)", tpl.Name, tpl.Gadgets)
	}
	args := tpl.Gadgets[0].Args
	if len(args) != 2 || args[0] != R || args[1] != maxLh {
		return fmt.Errorf("batch template %q gadget args %v != expected [R=%d, maxLh=%d]",
			tpl.Name, args, R, maxLh)
	}
	if len(tpl.PublicInputs) != 1 || tpl.PublicInputs[0].Var != R {
		return fmt.Errorf("batch template %q: root boundary %v != single root at var %d",
			tpl.Name, tpl.PublicInputs, R)
	}
	return nil
}

// loadInputBatchTemplates loads (once per distinct round-widths shape) the
// Lean-emitted batch templates block 2b replays, cross-checking each against the
// descriptor's round shape.
func loadInputBatchTemplates(vf *VerifierFull) (map[string]*Template, error) {
	g, ok := vf.gadget("VerifyMerklePathBn254InputOpen")
	if !ok {
		return nil, nil
	}
	rw, maxLh, err := inputOpenRoundWidths(g)
	if err != nil {
		return nil, err
	}
	out := map[string]*Template{}
	for _, widths := range rw {
		sig := widthsSig(widths)
		if _, done := out[sig]; done {
			continue
		}
		path, ok := inputBatchTemplatePaths[sig]
		if !ok {
			return nil, fmt.Errorf("no emitted batch template for input-round widths [%s] "+
				"(emit batchData %v 18 katMask from InputOpenBatchEmit.lean)", sig, widths)
		}
		tpl, err := LoadTemplate(path)
		if err != nil {
			return nil, fmt.Errorf("load batch template %s: %w", path, err)
		}
		if err := checkBatchTemplateShape(tpl, sumInts(widths), maxLh); err != nil {
			return nil, err
		}
		out[sig] = tpl
	}
	return out, nil
}

// LoadVerifierFull reads and fail-closed-validates the compact descriptor.
func LoadVerifierFull(path string) (*VerifierFull, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	vf := &VerifierFull{}
	if err := json.Unmarshal(raw, vf); err != nil {
		return nil, err
	}
	if err := vf.Validate(); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	return vf, nil
}

// Validate fail-closes on schema drift, unknown (gadget, expand) pairs,
// negative counts, and derived-parity violations against the gadget records.
func (vf *VerifierFull) Validate() error {
	if vf.Schema != verifierFullSchema {
		return fmt.Errorf("schema %q != %q", vf.Schema, verifierFullSchema)
	}
	for _, g := range vf.Gadgets {
		if !knownVFGadgets[[2]string{g.Gadget, g.Expand}] {
			return fmt.Errorf("unknown gadget/expand %q/%q (fail-closed: this replayer does not carry it)",
				g.Gadget, g.Expand)
		}
		if g.Count < 0 {
			return fmt.Errorf("gadget %q: negative count %d", g.Gadget, g.Count)
		}
	}
	return vf.checkDerivedParity()
}

// commitMerkleDepths reconstructs the per-round commit-phase Merkle depths from
// the VerifyMerklePathBn254 record's `depths` param (the emitter's
// [logGlobalMaxHeight-1-r]).
func (vf *VerifierFull) commitMerkleDepths() ([]int, error) {
	for _, g := range vf.Gadgets {
		if g.Gadget == "VerifyMerklePathBn254" {
			d := g.Params["depths"]
			if len(d) == 0 {
				return nil, fmt.Errorf("VerifyMerklePathBn254: empty depths param")
			}
			return d, nil
		}
	}
	return nil, fmt.Errorf("no VerifyMerklePathBn254 record")
}

func sumInts(xs []int) int {
	s := 0
	for _, x := range xs {
		s += x
	}
	return s
}

// checkDerivedParity asserts the descriptor's `derived` multiplicities equal
// what the interpreter will unroll from the gadget records + shape — the
// contract the Lean `derivedJson` comment names as the parity oracle.
func (vf *VerifierFull) checkDerivedParity() error {
	s := vf.Shape
	if got, want := vf.Derived.FoldRows, s.NumQueries*s.Rounds; got != want {
		return fmt.Errorf("derived fold_rows %d != num_queries*rounds %d", got, want)
	}
	depths, err := vf.commitMerkleDepths()
	if err != nil {
		return err
	}
	if got, want := vf.Derived.CommitMerkleCompressions, s.NumQueries*sumInts(depths); got != want {
		return fmt.Errorf("derived commit_merkle_compressions %d != num_queries*sum(depths) %d", got, want)
	}
	if got, want := vf.Derived.InputMerkleCompressions, s.NumQueries*s.InputRounds*s.LogGlobalMaxHeight; got != want {
		return fmt.Errorf("derived input_merkle_compressions %d != num_queries*input_rounds*log_global_max_height %d", got, want)
	}
	if got, want := vf.Derived.SegmentLaneAsserts, s.NumPublicLanes; got != want {
		return fmt.Errorf("derived segment_lane_asserts %d != num_public_lanes %d", got, want)
	}
	return nil
}

func (vf *VerifierFull) gadget(name string) (VFGadget, bool) {
	for _, g := range vf.Gadgets {
		if g.Gadget == name {
			return g, true
		}
	}
	return VFGadget{}, false
}

// ---------------------------------------------------------------------------
// §2  Witness bank + fresh-variable cursor.
// ---------------------------------------------------------------------------

// varCursor hands out the next fresh frontend variable from the flat witness
// bank the gadget expansion wires against. (For a COMPILE the concrete values
// are irrelevant; only the structure — how the gadgets are wired — determines
// the R1CS.)
type varCursor struct {
	w   []frontend.Variable
	pos int
}

func (c *varCursor) next() frontend.Variable {
	v := c.w[c.pos]
	c.pos++
	return v
}

func (c *varCursor) nextExt() BBExt {
	var e BBExt
	for i := range e {
		e[i] = c.next()
	}
	return e
}

// ---------------------------------------------------------------------------
// §3  Per-gadget witness budgets (kept in exact lock-step with §4's cursor
// consumption — Define asserts pos == len(w) at the end).
// ---------------------------------------------------------------------------

// symInstanceVars is the witness budget of one batch-STARK instance's DAG
// evaluation (all rows opened as fresh witness: TraceLocal/Next, PreLocal/Next,
// PermLocal/Next, Challenges, PermValues, 3 selectors, PublicValues, alpha).
// There is NO longer an `out` slot: the folded value is bound to the
// quotient(zeta)·Z_H(zeta) recomposed from the transcript-observed opened
// chunks (bindBlockZeta tooth 3), not to a fresh witness output.
func symInstanceVars(inst *SymInstance) int {
	ext := 2*inst.Width + 2*inst.PreWidth + inst.NumLookups /*PermLocal*/ +
		inst.NumLookups /*PermNext*/ + 2*inst.NumLookups /*Challenges*/ +
		inst.NumLookups /*PermValues*/ + 3 /*selectors*/ + 1 /*alpha*/
	return 4*ext + inst.NumPublicValues
}

// WitnessLen is the exact number of fresh variables Define consumes for this
// descriptor (+ the companion sym DAG for block 3).
func (vf *VerifierFull) WitnessLen(sym *SymbolicConstraints) (int, error) {
	n := 0
	for _, g := range vf.Gadgets {
		switch g.Gadget {
		case "AssertIsCanonical":
			n += g.Count * 1
		case "FriFoldRowArity2":
			// the round-0 fold-beta operand (one ext) — the transcript-link carrier
			// bindBlockChallengesToTranscript pins to the sponge squeeze. The fold
			// ARITHMETIC no longer rides the flat bank: it is a replay of the
			// Lean-emitted friFoldData template over the separate FriFoldWitness bank.
			n += 4
		case "ExtAssertIsEqual":
			n += g.Count * 8 // fresh (a,b) ext pair per equality
		case "VerifyMerklePathBn254":
			depths := g.Params["depths"]
			for q := 0; q < g.Count; q++ {
				for _, d := range depths {
					n += 2 + 2*d // leaf + root + d siblings + d bits
				}
			}
		case "VerifyMerklePathBn254InputOpen":
			// Block 2b: one Lean-emitted multi-height MMCS batch opening per
			// (query, input-round). Each binds R = sum(round widths) opened row
			// limbs, the input root, and maxLh (sibling, path-bit) pairs; the
			// Poseidon leaf hashes + path walk are SOLVED by ReplayClosed (not in
			// the bank). Rounds have different widths, so sum per round.
			rw, maxLh, err := inputOpenRoundWidths(g)
			if err != nil {
				return 0, err
			}
			nq := firstParam(g, "num_queries")
			for q := 0; q < nq; q++ {
				for r := range rw {
					n += sumInts(rw[r]) + 1 + 2*maxLh
				}
			}
		case "BatchTableInstance":
			if sym == nil {
				return 0, errBlock3NeedsSym
			}
			for i := range sym.Instances {
				n += symInstanceVars(&sym.Instances[i])
			}
		case "LogUpBalance":
			// global cumulative-sum balance: one fresh ext per instance,
			// summed to zero.
			n += 4 * vf.Shape.NumInstances
		case "SampleBitsDecomposed":
			n += g.Count * 1
		case "AssertPowBitsZero":
			n += g.Count * 1
		case "AssertIsEqual":
			// block 5: the settlement segment bind consumes NO fresh witness — Define
			// equates the block-3 ExposeClaim claim channel (captured during block 3)
			// against the exposed public statement, so no bank variable is drawn here.
		}
	}
	return n, nil
}

func firstParam(g VFGadget, key string) int {
	if v := g.Params[key]; len(v) > 0 {
		return v[0]
	}
	return 0
}

var errBlock3NeedsSym = fmt.Errorf("block 3 (BatchTableInstance/stark_constraint_dag + LogUpBalance) " +
	"is NOT self-contained in verifier_full.json: it carries only degree_bits, not the constraint DAG. " +
	"Supply the companion emitted artifact fixtures/shrink_symbolic_constraints.json as `sym` " +
	"(the same file stark_constraint_interp.go loads)")

// ---------------------------------------------------------------------------
// §4  The circuit — replay each gadget record through the hand-Go gadget.
// ---------------------------------------------------------------------------

// preprocessedPcsRound is the PCS round index carrying the shrink proof's
// preprocessed (VK-core / op-list) commitment. The input-open rounds are emitted
// in PCS round order — trace(main)=0, quotient=1, preprocessed=2, permutation=3 —
// the SAME order shrinkInputRootsRef reads the anchored inputRootDigOff and the
// descriptor's round_widths list (EmitJson.lean apexShrinkShape.inputRoundWidths:
// trace [76,304,8,164], quotient [8,16,16,8], preprocessed [59,26,8,82],
// permutation [72,32,8,164]). So block 2b's opened root at THIS round is the
// shrink proof's preprocessed commitment — the value SettlementCircuit pins as
// c.PrefixDigests[c.loc.preDigOff] (settlement_circuit.go:268-270), which the
// shrink-VK pin asserts equals the baked vkPreprocessedRoot.
const preprocessedPcsRound = 2

// VerifierFullCircuit materializes the compact descriptor. It EXPOSES the same
// 25-lane public settlement statement the hand-Go SettlementCircuit does
// (Publics: genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8],
// the pinned order shared with DreggSettlement.sol) — so the emit-driven circuit
// carries a public statement and block 5's segment binding equates the
// transcript-absorbed claim lanes against it, exactly as SettlementCircuit.Define
// does. W is the flat witness bank (all secret) the expansion wires against;
// vf/sym are structural (unexported: ignored by the gnark schema walker).
type VerifierFullCircuit struct {
	Publics

	W []frontend.Variable

	vf  *VerifierFull
	sym *SymbolicConstraints

	// batchTpls holds the Lean-emitted multi-height MMCS batch-opening templates
	// (InputOpenBatchEmit.lean `batchData`) keyed by a round's per-class
	// row-width signature. Block 2b replays these through ReplayClosed to bind
	// the real input openings to the committed input roots. Loaded by
	// AllocVerifierFullCircuit from the committed emitted/ artifacts.
	batchTpls map[string]*Template

	// merkleTpls holds the Lean-emitted commit-phase Merkle-path templates
	// (MerkleEmit.lean `merklePathData`) keyed by path depth. Block 2 replays
	// these through ReplayClosed to bind each real commit-phase opening
	// (leaf/siblings/bits) to its round root — the deployed merkleBn254RefRoot
	// walk authored in Lean (merkle_path_refines), NOT the hand-Go
	// VerifyMerklePathBn254 (retained as the differential oracle in
	// emitted_verifier_full_diff_test.go). Loaded by AllocVerifierFullCircuit
	// from the committed emitted/ artifacts.
	merkleTpls map[int]*Template

	// friFoldTpl / friFoldClass hold the Lean-emitted FRI arity-2 fold-consistency
	// template (FriFoldEmit.lean `friFoldData`, ∀-refined by `friFold_leaf_refines`:
	// `gHolds (friFoldData …) (friFoldAsg …) ↔ foldCheckV … = true`) and its
	// input/free-witness classification (ClassifyVars over the 16-limb
	// sibling0/sibling1/beta/claimed boundary). Block 1 replays this via
	// ReplayTemplateWithWitness — the Lean-authored deployed fold
	// `(e0+e1)/2 + β(e0−e1)inv(2s)` as REAL R1CS, in place of the hand-Go ExtMul
	// cost chain. The hand-Go friFoldRowArity2 (fri_query.go) survives ONLY as the
	// differential oracle (fri_verify_native.go + emitted_verifier_full_diff_test.go).
	// Loaded by AllocVerifierFullCircuit from the committed emitted/ artifact.
	friFoldTpl   *Template
	friFoldClass *TemplateVarClass

	// queryRangeTpl / queryRangeWit hold the Lean-emitted QueryPow range template
	// (emitQueryPow 0, QueryPowEmit.lean, ∀-refined by `queryPow_refines` at n=0:
	// `gHolds (emitQueryPow 0) (powAsg v) ↔ v.val < 2^31` — a bare 31-bit ToBinary
	// range check, since `v.val % 2^0 = 0`) and its 31 free-witness bit indices
	// (ClassifyVars(1).Witness). Block 0 (AssertIsCanonical, on v and on p-1-v) and
	// block 4 (SampleBitsDecomposed query-index range) replay it via
	// ReplayTemplateWithWitness — the Lean-authored replacement for the hand-Go
	// bb.AssertIsCanonical / rc.Check(·,31) on the emit path (the hand-Go survives
	// as the differential oracle in emitted_verifier_full_diff_test.go).
	queryRangeTpl *Template
	queryRangeWit []int

	// queryPowTpl / queryPowWit / queryPowN hold the Lean-emitted QueryPow grinding
	// template (emitQueryPow pow_bits, ∀-refined by `queryPow_refines` /
	// `queryPow_refines_native`: `gHolds ↔ v.val < 2^31 ∧ v.val % 2^n = 0`, the
	// deployed p3 `check_witness` accept), its 31 free-witness bit indices, and the
	// template's baked zero-pin count. Block 4 (AssertPowBitsZero) replays it — the
	// Lean-authored replacement for the hand-Go ToBinary+AssertIsEqual grinding pin
	// (grinding.go, retained as the differential oracle). Loaded by
	// AllocVerifierFullCircuit from the committed emitted/ artifacts.
	queryPowTpl *Template
	queryPowWit []int
	queryPowN   int

	// --- Optional emitted-permutation transcript re-derivation stage. ---
	//
	// The compact descriptor's blocks (1/3/4) consume their challenges as
	// host-fed witness (assignVerifierFull maps fx.ExpectedBetas / ex.ch.* into
	// the flat bank W) — the fixture-pinned feed. This stage, when attached,
	// ADDS an in-circuit re-derivation of every one of those challenges: it
	// drives the deployed MultiField transcript adapter through the LEAN-EMITTED
	// Poseidon2 permutation (emitted_challenger.go) over the REAL transcript and
	// binds each squeezed challenge (PermAlpha/PermBeta/alpha/zeta/FRI-alpha, the
	// per-round FRI betas, the per-query indices) to the commitment roots — so a
	// prover can no longer supply an arbitrary challenge for given roots.
	//
	// txMeta is nil (stage OFF) in the plain structural skeleton
	// (AllocVerifierFullCircuit); AllocVerifierFullCircuitWithTranscript attaches
	// it. All witness content lives in the exported Tx* SLICES, empty by default,
	// so the schema of the stage-off circuit is byte-identical to before.
	txMeta        *shrinkTranscriptMeta
	TxPrefixObs   []frontend.Variable
	TxPrefixDig   []frontend.Variable
	TxPrefixSamp  []frontend.Variable
	TxCommitRoots []frontend.Variable
	TxPow         []frontend.Variable // 0 or 1 element (the query-PoW witness)
	TxFinalPoly   []BBExt
	TxQueries     []FriNativeQueryOpening

	// --- LOAD-BEARING LINK capture (the arbitrary-challenge hole closure). ---
	//
	// The descriptor blocks consume their challenges as FRESH witness off the flat
	// bank W (assignVerifierFull feeds the real ones). With the transcript stage
	// attached, expand() records the exact challenge witnesses each block consumed
	// so Define can AssertIsEqual them against the transcript-re-derived challenge
	// (bindBlockChallengesToTranscript). Without these links a prover could satisfy
	// the transcript stage with the real challenges AND the blocks with favorable,
	// unlinked ones; with them, no block can consume a challenge that is not the
	// sponge squeeze of the real roots. Captured unconditionally (cheap); only USED
	// when txMeta != nil, so the stage-off skeleton is unperturbed.
	block1FoldBeta   *BBExt              // block 1 FriFoldRowArity2 fold-beta operand
	block3Challenges [][]BBExt           // block 3 per-instance WitnessChecks bus (permAlpha,permBeta per lookup)
	block3Alpha      []BBExt             // block 3 per-instance constraint-folding alpha
	block4QueryIdx   []frontend.Variable // block 4 SampleBitsDecomposed query-index witness

	// --- THE ZETA BIND capture (block 3's zeta-derived inputs). ---
	//
	// Block 3 never consumes zeta as a challenge witness: zeta enters through the
	// Lagrange SELECTORS and the OPENINGS AT ZETA. So the challenge link above has
	// no zeta slot to equate — the bind is a RE-DERIVATION instead. expand()
	// records, per instance, the three selector witnesses (+ that instance's trace
	// degree_bits, the descriptor's `degree_bits` param) and the opened-value /
	// cumulative-sum / public-value witnesses it consumed; Define (bindBlockZeta)
	// re-derives the selectors from the transcript-squeezed zeta by REPLAYING the
	// Lean-emitted selector template (replaySelectorsWitness — the SAME rational form
	// the deployed VerifyShrinkStarkAlgebra runs, now authored in Lean) and asserts
	// equality, and equates the opened values against the transcript-observed stream.
	// Captured unconditionally; only USED when txMeta != nil.
	block3Selectors []block3SelectorSlot
	block3Opened    []block3OpenedSlot

	// --- THE ζ-SELECTOR REPLAY (Lean-emitted, not hand-Go). ---
	//
	// bindBlockZeta re-derives the Lagrange selectors at the transcript-squeezed ζ
	// NOT by calling the hand-Go computeStarkSelectorsNative, but by REPLAYING the
	// Lean-emitted selector template (SelectorEmit.lean, emitted/selectors_db{N}.json)
	// through ReplayTemplateWithWitness: ζ (4 limbs) is the input boundary, the free
	// internal witnesses (the honest selector-derivation intermediate bits — the
	// 31-bit canonicity decompositions, the two ExtInv hinted inverses, the minted
	// ζ-squaring products) are supplied from the assignment in SelectorWitness, and
	// the replay SOLVES {isFirstRow,isLastRow,isTransition} as its output boundary.
	// So no constraint in the ζ-selector path is authored in Go — Go allocates the
	// emitted template's witnesses and replays its asserts.
	//
	// selectorReplay is the per-db layout (template + free-witness indices + offset
	// into SelectorWitness), keyed by trace degree_bits; nil (replay OFF) unless the
	// transcript stage is attached (AllocVerifierFullCircuitWithTranscript builds it).
	// SelectorWitness is the flat prover-supplied secret witness bank, one block per
	// distinct db in the plan's layout order; empty on the plain skeleton.
	selectorReplay  *selectorReplayPlan
	SelectorWitness []frontend.Variable

	// --- THE FRI FOLD REPLAY (Lean-emitted, not hand-Go). ---
	//
	// Block 1's FriFoldRowArity2 case replays the Lean-emitted fold-consistency
	// template (friFoldTpl, above) through ReplayTemplateWithWitness: the
	// sibling0/sibling1/beta/claimed 16-limb boundary is bound from this bank, the
	// free internal witnesses (the 31-bit canonicity decompositions, the parent
	// index bits, the reduce quotient/remainder hints) are supplied from it too,
	// and the replay SOLVES the fold define-chain and KEEPS the claimed==fold
	// equality — so no constraint in the block-1 fold path is authored in Go.
	//
	// FriFoldWitness is a self-consistent honest fold fixture (siblings + the
	// deployed fold at β = the real fixture expected_betas[0], 17 parent bits),
	// Lean-dumped var-index-ordered to emitted/fri_fold_witness.json — the same
	// honest assignment friFold_leaf_refines quantifies over. Layout: the
	// len(PublicInputs) boundary values (public-input order) followed by the
	// friFoldClass.Witness free witnesses. Sized (empty on values) on the plain
	// compile path; filled by the assignment (fillFriFoldWitness). The round-0
	// fold-beta operand the transcript link binds (block1FoldBeta) is a SEPARATE
	// flat-bank carrier — this replay exercises the fold ARITHMETIC, unfused from
	// the transcript so the block1-fold-beta canary keeps its inert-block premise.
	FriFoldWitness []frontend.Variable

	// --- THE STATEMENT BIND + VK PINS (settlement_circuit.go:241-285). ---
	//
	// claimChannel is the block-3 ExposeClaim instance's public-value lanes — the
	// 25 settlement claim lanes ++ the 8 VK-spine lanes ++ the 8 apex VK-core
	// lanes (ExposedShrinkClaimLanes) — captured (base-field) during block 3's DAG evaluation, where
	// the ExposeClaimAir `public_value[lane] == v_0` identity binds each lane to
	// the COMMITTED expose_claim trace cell (through the quotient identity at
	// zeta). Block 5 equates lanes 0..NumPublicInputs against the exposed public
	// statement (publicLane), the subtree pin equates lanes
	// NumPublicInputs..ApexClaimLanes against rootVkSpine, and the apex-VK pin
	// equates the tail lanes against apexPreprocessedCommit — so the statement, the
	// folded subtree's identity AND the apex VK-core are all bound
	// to the REAL proof's exposed-claim channel, not to fresh, proof-free witness.
	claimChannel []frontend.Variable
	// preprocessedRoots are block 2b's opened input roots of the preprocessed PCS
	// round (preprocessedPcsRound), one per query — the shrink proof's VK-core
	// commitment (each is constrained by that query's ReplayClosed recomputed-root
	// == root check). The shrink-VK pin asserts each equals vkPreprocessedRoot.
	preprocessedRoots []frontend.Variable
	// vkPreprocessedRoot, when non-nil, bakes the shrink proof's preprocessed
	// (op-list) commitment root as a circuit CONSTANT (shrink-VK pin, tooth 1) —
	// the twin of SettlementCircuit.vkPreprocessedRoot (settlement_circuit.go:268).
	vkPreprocessedRoot *big.Int
	// apexPreprocessedCommit, when non-nil, bakes the DEPLOYED apex's preprocessed
	// commitment (ApexVkLanes lanes) as circuit constants against the claim
	// channel's re-exposed VK-core lanes (apex-VK pin, tooth 2) — the twin of
	// SettlementCircuit.apexPreprocessedCommit (settlement_circuit.go:278).
	apexPreprocessedCommit []*big.Int
	// rootVkSpine, when non-nil, bakes the deployed root's VK SPINE (VkSpineLanes
	// lanes) as circuit constants against the claim channel's re-exposed spine
	// block (subtree pin, tooth 3) — the twin of SettlementCircuit.rootVkSpine.
	rootVkSpine []*big.Int
}

// publicLane returns the i-th lane of the pinned 25-lane public statement in the
// genesis8 ++ final8 ++ numTurns ++ chainDigest8 order (i in [0, NumPublicInputs)).
func (c *VerifierFullCircuit) publicLane(i int) frontend.Variable {
	switch {
	case i < DigestWidth:
		return c.GenesisRoot[i]
	case i < 2*DigestWidth:
		return c.FinalRoot[i-DigestWidth]
	case i == 2*DigestWidth:
		return c.NumTurns
	default:
		return c.ChainDigest[i-2*DigestWidth-1]
	}
}

// AllocVerifierFullCircuit builds a compile-ready template (W sized to the
// exact witness budget). sym is REQUIRED for block 3; pass the loaded
// fixtures/shrink_symbolic_constraints.json.
func AllocVerifierFullCircuit(vf *VerifierFull, sym *SymbolicConstraints) (*VerifierFullCircuit, error) {
	n, err := vf.WitnessLen(sym)
	if err != nil {
		return nil, err
	}
	batchTpls, err := loadInputBatchTemplates(vf)
	if err != nil {
		return nil, err
	}
	merkleTpls, err := loadMerkleTemplates(vf)
	if err != nil {
		return nil, err
	}
	friFoldTpl, friFoldClass, err := loadFriFoldTemplate(vf)
	if err != nil {
		return nil, err
	}
	qp, err := loadQueryPowTemplates(vf)
	if err != nil {
		return nil, err
	}
	c := &VerifierFullCircuit{
		W:             make([]frontend.Variable, n),
		vf:            vf,
		sym:           sym,
		batchTpls:     batchTpls,
		merkleTpls:    merkleTpls,
		friFoldTpl:    friFoldTpl,
		friFoldClass:  friFoldClass,
		queryRangeTpl: qp.rangeTpl,
		queryRangeWit: qp.rangeWit,
		queryPowTpl:   qp.powTpl,
		queryPowWit:   qp.powWit,
		queryPowN:     qp.powN,
	}
	if friFoldTpl != nil {
		// The block-1 fold replay's witness bank: the 16 boundary limbs (public-input
		// order) ++ the free internal witnesses. Sized here so the plain compile path's
		// schema matches; the assignment fills the honest values (fillFriFoldWitness).
		c.FriFoldWitness = make([]frontend.Variable, len(friFoldTpl.PublicInputs)+len(friFoldClass.Witness))
	}
	return c, nil
}

func (c *VerifierFullCircuit) Define(api frontend.API) error {
	if c.vf == nil {
		return fmt.Errorf("VerifierFullCircuit: descriptor not attached")
	}
	bb := NewBBApi(api)
	rc := rangecheck.New(api)
	cur := &varCursor{w: c.W}

	for _, g := range c.vf.Gadgets {
		if err := c.expand(api, bb, rc, cur, g); err != nil {
			return err
		}
	}
	if cur.pos != len(c.W) {
		return fmt.Errorf("witness-budget drift: Define consumed %d, bank has %d", cur.pos, len(c.W))
	}

	// THE VK PINS (settlement_circuit.go:266-285): the shrink-VK and apex-VK
	// fingerprint pins, asserted against the baked constants over the values block
	// 2b / block 3 already bound to the real proof. Nil-guarded (skipped on the
	// plain compile path), exactly as SettlementCircuit.Define guards them.
	if err := c.bindVkPins(api); err != nil {
		return err
	}

	// Emitted-permutation transcript re-derivation stage (off when unattached).
	// Re-derives EVERY challenge the verifier consumes in-circuit through the
	// Lean-emitted Poseidon2 permutation and binds it to the commitment roots —
	// replacing the "trust the fixture-pinned challenge" posture of the blocks
	// above with "the challenge IS the sponge squeeze of the real roots".
	if c.txMeta != nil {
		var pow frontend.Variable = frontend.Variable(0)
		if len(c.TxPow) > 0 {
			pow = c.TxPow[0]
		}
		betas, queryIdxBits := c.txMeta.rederive(bb, &shrinkTranscriptInputs{
			PrefixObs:     c.TxPrefixObs,
			PrefixDigests: c.TxPrefixDig,
			PrefixSamples: c.TxPrefixSamp,
			CommitRoots:   c.TxCommitRoots,
			FinalPoly:     c.TxFinalPoly,
			PowWitness:    pow,
			Queries:       c.TxQueries,
		})
		// THE LOAD-BEARING LINK: bind every challenge the descriptor blocks consumed
		// (captured during expand) to the transcript-re-derived challenge. After this,
		// no block can use a challenge that is not the sponge squeeze of the real roots.
		c.bindBlockChallengesToTranscript(bb, betas, queryIdxBits)
		// THE ZETA BIND: block 3 consumes zeta only through its zeta-DERIVED inputs,
		// so the link above cannot reach it. Re-derive the Lagrange selectors
		// in-circuit from the squeeze-asserted zeta and force block 3's supplied
		// selectors to equal them, and equate the openings-at-zeta against the
		// transcript-observed opened stream.
		if err := c.bindBlockZeta(bb); err != nil {
			return err
		}
	}
	return nil
}

// bindVkPins asserts the shrink-VK and apex-VK fingerprint pins against the baked
// constants — the emit-driven twins of SettlementCircuit.Define:266-285:
//
//   - shrink-VK (tooth 1): the block-2b preprocessed-round input root (the shrink
//     proof's preprocessed / op-list commitment, its VK-core) equals the baked
//     vkPreprocessedRoot — asserted for EVERY query's opened root, since the emit
//     skeleton opens each (query, round) against its own root variable (the
//     structural-abstraction residual, seam #2, replaces the deployed circuit's
//     single transcript-observed cap). A shrink proof from a DIFFERENT circuit
//     carries a different preprocessed commitment and fails here.
//   - subtree/VK-spine (tooth 3): the claim channel's re-exposed spine lanes
//     (NumPublicInputs..ApexClaimLanes) equal rootVkSpine — the apex RecursionVk
//     fingerprint is content-independent and does not move when a child circuit is
//     substituted, so tooth 2 alone certifies nothing about WHAT was folded.
//   - apex-VK (tooth 2): the claim channel's re-exposed VK-core lanes
//     (ApexClaimLanes..ExposedShrinkClaimLanes) equal apexPreprocessedCommit
//     — a shrink minted over a NON-deployed apex has different VK-core lanes (they
//     are transcript-absorbed + ExposeClaimAir-bound in block 3), and cannot be
//     swapped without re-proving.
//
// Both pins are nil-guarded (skipped on the plain compile path
// AllocVerifierFullCircuit, which leaves the constants unset), materializing only
// when the assignment bakes the deployed constants — exactly as the settlement
// circuit's `if c.vkPreprocessedRoot != nil` / `if c.apexPreprocessedCommit != nil`.
func (c *VerifierFullCircuit) bindVkPins(api frontend.API) error {
	if c.vkPreprocessedRoot != nil {
		if len(c.preprocessedRoots) == 0 {
			return fmt.Errorf("shrink-VK pin set but no block-2b preprocessed-round (PCS round %d) "+
				"root was captured (the descriptor's input rounds do not reach it)", preprocessedPcsRound)
		}
		for _, root := range c.preprocessedRoots {
			api.AssertIsEqual(root, c.vkPreprocessedRoot)
		}
	}
	if c.apexPreprocessedCommit != nil {
		if len(c.apexPreprocessedCommit) != ApexVkLanes {
			return fmt.Errorf("apex-VK pin must carry exactly ApexVkLanes (%d) lanes, got %d",
				ApexVkLanes, len(c.apexPreprocessedCommit))
		}
		if len(c.claimChannel) != ExposedShrinkClaimLanes {
			return fmt.Errorf("apex-VK pin: claim channel has %d lanes, want %d "+
				"(the 25 statement lanes ++ the 8 VK-spine lanes ++ the 8 apex VK-core lanes — "+
				"block 3 ExposeClaim capture)",
				len(c.claimChannel), ExposedShrinkClaimLanes)
		}
		for i, want := range c.apexPreprocessedCommit {
			api.AssertIsEqual(c.claimChannel[ApexClaimLanes+i], want)
		}
	}
	if c.rootVkSpine != nil {
		if len(c.rootVkSpine) != VkSpineLanes {
			return fmt.Errorf("VK-spine pin must carry exactly VkSpineLanes (%d) lanes, got %d",
				VkSpineLanes, len(c.rootVkSpine))
		}
		if len(c.claimChannel) != ExposedShrinkClaimLanes {
			return fmt.Errorf("VK-spine pin: claim channel has %d lanes, want %d",
				len(c.claimChannel), ExposedShrinkClaimLanes)
		}
		for i, want := range c.rootVkSpine {
			api.AssertIsEqual(c.claimChannel[NumPublicInputs+i], want)
		}
	}
	return nil
}

// bindBlockChallengesToTranscript closes the arbitrary-challenge hole end-to-end:
// it AssertIsEquals each challenge the descriptor blocks consumed as fresh witness
// against the matching transcript-re-derived challenge. The prefix challenges
// (permAlpha/permBeta/alpha) are already bound onto c.TxPrefixSamp by the stage
// (rederiveShrinkChallenges squeeze-asserts), so binding a block witness to
// c.TxPrefixSamp[off] transitively binds it to the squeeze; the FRI fold betas and
// the query index are drawn live inside the stage and threaded out here.
//
//   - block 1 (fri_fold): the fold-beta operand == the transcript round-0 fold beta;
//   - block 3 (batch_table): every instance's WitnessChecks bus (permAlpha, permBeta
//     per lookup) == the transcript's, and its constraint-folding alpha == the
//     transcript alpha — so the DAG folded == quotient·Z_H identity is evaluated at
//     the transcript-sampled challenges, not favorable free ones;
//   - block 4 (query_pow): the range-checked query index == the transcript's
//     live-sampled query index.
//
// ZETA is handled SEPARATELY, by bindBlockZeta: block 3 does not consume zeta as a
// challenge WITNESS — zeta enters only through the Lagrange selectors and the
// openings-at-zeta — so there is no zeta slot to equate here. That function binds it
// by RE-DERIVATION instead (selectors recomputed in-circuit at the squeezed zeta) plus
// an equality against the transcript-observed opened stream. The scope is the pinned
// fixture shape (extra_query_index_bits == 0, so the sampled domain index is the full
// query index block 4 range-checks).
func (c *VerifierFullCircuit) bindBlockChallengesToTranscript(bb *BBApi, betas []BBExt,
	queryIdxBits [][]frontend.Variable) {
	api := bb.API()
	m := c.txMeta
	txExt := func(off int) BBExt {
		var e BBExt
		for i := 0; i < 4; i++ {
			e[i] = c.TxPrefixSamp[off+i]
		}
		return e
	}

	// block 1 — the FRI fold beta operand == the transcript round-0 fold beta.
	if c.block1FoldBeta != nil && len(betas) > 0 {
		bb.ExtAssertIsEqual(*c.block1FoldBeta, betas[0])
	}

	// block 3 — the WitnessChecks bus (permAlpha, permBeta) and the folding alpha.
	permAlpha := txExt(m.permChSampleOff)
	permBeta := txExt(m.permChSampleOff + 4)
	alpha := txExt(m.alphaSampleOff)
	for _, chs := range c.block3Challenges {
		// chs is [permAlpha, permBeta, permAlpha, permBeta, ...] per lookup.
		for l := 0; 2*l+1 < len(chs); l++ {
			bb.ExtAssertIsEqual(chs[2*l], permAlpha)
			bb.ExtAssertIsEqual(chs[2*l+1], permBeta)
		}
	}
	for _, a := range c.block3Alpha {
		bb.ExtAssertIsEqual(a, alpha)
	}

	// block 4 — the range-checked query index == the transcript's live-sampled
	// query index (extra_query_index_bits == 0: the domain bits ARE the full index).
	if len(c.block4QueryIdx) > 0 && len(queryIdxBits) > 0 {
		idx := api.FromBinary(queryIdxBits[0]...)
		for _, v := range c.block4QueryIdx {
			api.AssertIsEqual(v, idx)
		}
	}
}

// bindBlockZeta closes the zeta residual the challenge link above names: block 3
// consumes zeta only INDIRECTLY, so there is no zeta witness to equate. Two teeth,
// both against the transcript stage's own bound streams:
//
//   - THE SELECTOR DERIVATION (m.zetaSampleOff). zeta is the prefix squeeze the
//     stage already squeeze-asserts onto TxPrefixSamp. This re-derives the Lagrange
//     selectors IN-CIRCUIT at that zeta by REPLAYING the Lean-emitted selector
//     template (SelectorEmit.lean, emitted/selectors_db{N}.json) through
//     ReplayTemplateWithWitness (replaySelectorsWitness): ζ is the emitted template's
//     4-limb input boundary, the honest selector-derivation intermediate bits (the
//     31-bit canonicity decompositions, the two ExtInv hinted inverses, the minted
//     ζ-squaring products) ride in SelectorWitness, and the replay SOLVES the emitted
//     output boundary {isFirstRow,isLastRow,isTransition}. The emitted template
//     computes the SAME rational form the deployed VerifyShrinkStarkAlgebra runs
//     (domain.rs:262-271): E = zeta^(2^db), Z_H = E - 1, isTransition = zeta - g^{-1},
//     isFirstRow = Z_H·(zeta-1)^{-1}, isLastRow = Z_H·isTransition^{-1} — and this
//     asserts the block's three supplied selector witnesses equal the replayed
//     outputs, per instance, at that instance's degree_bits. A selector set at ANY
//     other point is UNSAT: the favorable-zeta forgery (pick a zeta the transcript
//     never sampled, supply the matching selectors and the matching `out`) has no
//     satisfying assignment. Replays are memoized per degree_bits (the fixture's 6
//     instances carry 4 distinct trace degrees), so each emitted template is replayed
//     once, shared across instances. Note the emitted ExtInv pins: the template
//     constrains inv·x == 1, so zeta == 1 or zeta == g^{-1} (the degenerate points
//     where the multiplicative form would leave a selector free) are themselves UNSAT
//     rather than silently unconstrained.
//
//   - THE OPENINGS BIND (m.openedObsOff / cumObsOff / pubObsOff). The values block 3
//     evaluates the DAG on were free witness. The transcript ABSORBS them: the
//     prefix event stream is `sample(zeta), observe_bb(opened values at zeta),
//     sample(FRI alpha)` (locateShrinkStarkPrefix), plus `observe_bb(cumulative
//     sums)` before the folding alpha and the publics block at the head. This slices
//     the flat opened stream with buildStarkOpenedSpans — the SAME layout walk the
//     deployed verifier uses — and equates every opened-value witness with its
//     transcript-observed felt: trace/preprocessed rows directly, the permutation
//     columns through ExtFromBasisCoefficients (the verifier's basis recomposition,
//     mod.rs:543-556), and the verifier's ZERO SUBSTITUTION for AIRs that open no
//     next row (mod.rs:563-581) as an assert-zero. So block 3 evaluates the openings
//     the transcript committed to — the ones zeta and every downstream challenge were
//     drawn over — not a favorable re-authored set.
//
// THE SUBSTRATE, SAID OUT LOUD — the two teeth now sit at DIFFERENT resolutions:
//
//   - The SELECTOR tooth is LEAN-EMITTED. Its constraints are no longer authored in
//     Go: replaySelectorsWitness allocates the emitted template's witnesses and
//     replays its asserts (ReplayTemplateWithWitness), the same generic replayer the
//     Poseidon2 / input-open / challenger leaves use. The template is SelectorEmit.lean
//     (`emitSelectors db`), byte-pinned there (§8 #guard length + FNV-1a), and it
//     carries a machine-checked refinement over the ACTUAL emitted object:
//     `selectorTemplate_refines` (both polarities, #assert_axioms-clean) proves
//     gHolds(selectorsData db …) ↔ the selector triple is the true Lagrange derivation
//     at ζ, and `selectorTemplate_refines_emitted` lifts it to the serialized wire
//     form. So the wrong-zeta selector forgery is now closed by a Lean-authored AIR,
//     not a hand-Go gadget. computeStarkSelectorsNative (stark_verify_native.go:379)
//     is NO LONGER on this emit path — it survives only as the differential ORACLE +
//     KAT reference (its *_ref twin computeStarkSelectorsRef pins the replay outputs
//     bit-exact in emitted_gadget_replay_witness_test.go).
//
//   - The OPENINGS tooth (below) is still GO-SIDE, hand-written — not emitted from
//     Lean. It equates the opened-value / cumulative-sum / public-value witnesses with
//     the transcript-observed stream through hand-Go ExtAssertIsEqual /
//     ExtFromBasisCoefficients. That is the remaining debt of this function; it carries
//     the hand-Go verifier lane's posture, NOT the machine-checked refinement, and
//     proves nothing about all inputs beyond what the canaries in
//     emitted_challenger_full_test.go exercise. Lifting it is the transcript-bind
//     composition seam BatchTablesSingleAir.lean §272 item 3 names.
//
// TOOTH 3 — the DEEP quotient identity — CLOSES the constraint/quotient reduction:
// folded == quotient(zeta)·Z_H(zeta), with quotient(zeta) recomposed IN-CIRCUIT
// (recomposeQuotientNative — pure EF-basis linear glue) from the transcript-OBSERVED
// opened quotient chunks and Z_H(zeta) = zeta^(2^db) - 1 derived by EF glue from the
// Lean-emitted, transcript-zeta-bound selectors (isLastRow·isTransition = zH). The
// former placeholder bound folded to a FRESH `out` witness — vacuous. So the openings
// no longer merely FEED an unconstrained evaluator: the constraint algebra is forced
// to equal the recomposed quotient over the committed chunks.
//
// NAMED RESIDUAL, at current resolution: this binds the openings to the TRANSCRIPT
// and now enforces the zeta-quotient identity over them, but not the remaining half
// of the DEEP/PCS argument — that this transcript-consistent chunk set IS the
// low-degree committed quotient polynomial's evaluation (FRI over the batch-combined
// quotient). The emit skeleton models the FRI fold rows and the input-batch Merkle
// openings but not that low-degree reduction, so "the opened chunks are the true
// committed evaluations at zeta" remains seam #2. What is CLOSED here is the
// wrong-zeta selector forgery, the free-openings forgery, and the free-folded
// (quotient-identity) forgery; what is OPEN is the low-degree/commitment-consistency
// of a transcript-consistent opening set.
func (c *VerifierFullCircuit) bindBlockZeta(bb *BBApi) error {
	api := bb.API()
	m := c.txMeta
	if m.zetaSampleOff < 0 {
		return nil // zeta bind off (the constraint-cost differential; never a deployed path)
	}
	zeta := BBExt{}
	for i := 0; i < 4; i++ {
		zeta[i] = c.TxPrefixSamp[m.zetaSampleOff+i]
	}

	// --- tooth 1: the selectors ARE the derivation at the transcript zeta. ---
	// The derivation is the WITNESS-AWARE REPLAY of the Lean-emitted selector template
	// (selectorReplay / replaySelectorsWitness), NOT the hand-Go computeStarkSelectorsNative:
	// ζ is the emitted template's input boundary, the honest selector-derivation
	// intermediate bits ride in SelectorWitness, and the replay SOLVES the three
	// selectors as its output boundary. Memoized per db (one replay per distinct trace
	// degree, shared across instances) exactly as the native derivation was.
	if c.selectorReplay == nil {
		return fmt.Errorf("zeta bind: the ζ-selector replay plan is not attached " +
			"(AllocVerifierFullCircuitWithTranscript builds it; the bind cannot re-derive the selectors)")
	}
	derived := make(map[int]starkSelectorsNative, len(c.block3Selectors))
	for _, s := range c.block3Selectors {
		d, ok := derived[s.db]
		if !ok {
			var err error
			if d, err = c.replaySelectorsWitness(bb, zeta, s.db); err != nil {
				return err
			}
			derived[s.db] = d
		}
		bb.ExtAssertIsEqual(s.sel.isFirstRow, d.isFirstRow)
		bb.ExtAssertIsEqual(s.sel.isLastRow, d.isLastRow)
		bb.ExtAssertIsEqual(s.sel.isTransition, d.isTransition)
	}

	// --- tooth 2: the openings ARE the transcript-observed stream. ---
	if m.shapes == nil {
		return nil // openings bind off (structural probes that carry no shape list)
	}
	if len(m.shapes) != len(c.block3Opened) {
		return fmt.Errorf("zeta bind: %d instance shapes for %d block-3 instances", len(m.shapes), len(c.block3Opened))
	}
	spans, totalEF := buildStarkOpenedSpans(m.shapes)
	if want := m.openedObsOff + 4*totalEF; want > len(c.TxPrefixObs) {
		return fmt.Errorf("zeta bind: opened stream needs %d observed felts, prefix has %d", want, len(c.TxPrefixObs))
	}
	// obsExt reads EF element j of the flat opened stream (4 base felts per EF).
	obsExt := func(j int) BBExt {
		var e BBExt
		for i := 0; i < 4; i++ {
			e[i] = c.TxPrefixObs[m.openedObsOff+4*j+i]
		}
		return e
	}
	zero := BBExt{0, 0, 0, 0}
	bindRow := func(w []BBExt, sp efSpan, opened bool) error {
		if !opened {
			// The AIR opens no next row: the verifier substitutes ZERO.
			for _, v := range w {
				bb.ExtAssertIsEqual(v, zero)
			}
			return nil
		}
		if len(w) != sp.len {
			return fmt.Errorf("zeta bind: %d witness exts for a span of %d", len(w), sp.len)
		}
		for k, v := range w {
			bb.ExtAssertIsEqual(v, obsExt(sp.off+k))
		}
		return nil
	}
	// bindPerm equates each permutation column against the BASIS RECOMPOSITION of
	// its 4 flattened opened EF values (mod.rs:543-556).
	bindPerm := func(w []BBExt, sp efSpan) error {
		if 4*len(w) != sp.len {
			return fmt.Errorf("zeta bind: %d perm columns for a flattened span of %d", len(w), sp.len)
		}
		for k, v := range w {
			var basis [4]BBExt
			for b := 0; b < 4; b++ {
				basis[b] = obsExt(sp.off + 4*k + b)
			}
			bb.ExtAssertIsEqual(v, bb.ExtFromBasisCoefficients(basis))
		}
		return nil
	}
	for _, o := range c.block3Opened {
		sh, sp := m.shapes[o.inst], spans[o.inst]
		// tooth 2's opened-value / cumulative-sum equality binds. Skipped under the
		// isolateQuotientIdentity structural probe so a folded-side tamper is caught
		// by tooth 3 (the quotient identity) alone; on the deployed lane it always runs.
		if !m.isolateQuotientIdentity {
			for _, e := range []error{
				bindRow(o.traceLocal, sp.traceLocal, true),
				bindRow(o.traceNext, sp.traceNext, sh.HasTraceNext),
				bindRow(o.preLocal, sp.preLocal, sh.PreWidth > 0),
				bindRow(o.preNext, sp.preNext, sh.PreWidth > 0 && sh.HasPreNext),
				bindPerm(o.permLocal, sp.permLocal),
				bindPerm(o.permNext, sp.permNext),
			} {
				if e != nil {
					return fmt.Errorf("instance %d openings: %w", o.inst, e)
				}
			}
			// The LogUp cumulative sums block 3 folds are the ones the transcript absorbed
			// before the constraint-folding alpha was drawn.
			if m.cumObsOff >= 0 {
				if len(o.permValues) != sp.cumSums.len {
					return fmt.Errorf("instance %d: %d cumulative-sum witnesses for a stream span of %d",
						o.inst, len(o.permValues), sp.cumSums.len)
				}
				for k, v := range o.permValues {
					var e BBExt
					for i := 0; i < 4; i++ {
						e[i] = c.TxPrefixObs[m.cumObsOff+4*(sp.cumSums.off+k)+i]
					}
					bb.ExtAssertIsEqual(v, e)
				}
			}
		}

		// --- tooth 3: the DEEP quotient identity folded == quotient(zeta)·Z_H(zeta). ---
		// The former placeholder bound folded to a fresh `out` witness — vacuous, since a
		// prover could set out := folded and the recomposed quotient never entered the
		// circuit. Here folded (evalSymbolicFoldedNative over the emitted DAG, recorded in
		// starkInstance) is asserted equal to quotient(zeta)·Z_H(zeta), where the quotient
		// is recomposed IN-CIRCUIT (recomposeQuotientNative, uni-stark verifier.rs:59-96 —
		// pure EF-basis linear glue over already-opened values, no crypto/hint gadget) from
		// the REAL opened quotient chunks. Those chunks are the transcript-OBSERVED opened
		// stream (obsExt over buildStarkOpenedSpans' quotient-round span — the same flat
		// stream zeta and every downstream challenge were drawn over), so folded is now a
		// bound quantity, not free. Z_H(zeta) and zeta^(2^db) are derived by EF glue from the
		// LEAN-EMITTED, transcript-zeta-bound selectors this bind already replayed
		// (SelectorEmit.lean): isLastRow = zH·isTransition^{-1}, so zH = isLastRow·isTransition
		// and zeta^(2^db) = zH + 1 (computeStarkSelectorsRef, stark_verify_native_ref.go:65-86).
		// This mirrors the deployed VerifyShrinkStarkAlgebra per-instance quotient block
		// (stark_verify_native.go:567-594), sourcing the chunks from the transcript instead
		// of a fresh witness. Quotient-domain constants (kPow / zpsConst) are baked host-side
		// (shrinkQuotientDomainConsts). The residual DEEP step — that this transcript-
		// consistent opening set IS the committed polynomials' low-degree evaluation (FRI
		// over the batch-combined quotient) — is orthogonal and stays open (seam #2 below).
		// db is the trace degree the selectors were REPLAYED at (block3Selectors is
		// instance-ordered, parallel to the caller's starkInstance loop), so derived[db]
		// is guaranteed populated by tooth 1 and the quotient-domain constants share the
		// exact degree the selectors (hence zetaPow2Db) were derived at.
		db := c.block3Selectors[o.inst].db
		d := derived[db] // Lean-emitted selectors at the squeeze-asserted zeta
		one := BBExt{1, 0, 0, 0}
		zH := bb.ExtMul(d.isLastRow, d.isTransition)
		zetaPow2Db := bb.ExtAdd(zH, one)
		chunks := make([][4]BBExt, len(sp.quotientChunks))
		for cIdx, qs := range sp.quotientChunks {
			if qs.len != 4 {
				return fmt.Errorf("instance %d: quotient chunk %d span len %d != 4", o.inst, cIdx, qs.len)
			}
			for b := 0; b < 4; b++ {
				chunks[cIdx][b] = obsExt(qs.off + b)
			}
		}
		quotient := recomposeQuotientNative(bb, zetaPow2Db, chunks,
			shrinkQuotientDomainConsts(db, sh.NumQuotientChunks))
		bb.ExtAssertIsEqual(o.folded, bb.ExtMul(quotient, zH))
	}
	// The per-instance public values (base-field), flattened in instance order in the
	// head publics block — the claim channel block 5 and the apex-VK pin ride on.
	// Part of tooth 2; skipped under the isolateQuotientIdentity probe.
	if m.pubObsOff >= 0 && !m.isolateQuotientIdentity {
		flat := m.pubObsOff
		for i, sh := range m.shapes {
			for k := 0; k < sh.NumPublicValues; k++ {
				if k < len(c.block3Opened[i].publicVals) {
					api.AssertIsEqual(c.block3Opened[i].publicVals[k][0], c.TxPrefixObs[flat+k])
				}
			}
			flat += sh.NumPublicValues
		}
	}
	return nil
}

// AllocVerifierFullCircuitWithTranscript builds the emit-driven circuit WITH the
// emitted-permutation transcript re-derivation stage attached: alongside the
// compact-descriptor blocks it re-derives every consumed challenge in-circuit
// through the Lean-emitted Poseidon2 permutation and binds it to the real
// commitment roots. `meta` carries the structural replay script + the emitted
// permutation template; the Tx* witness slices are sized to the fixture shape and
// filled by the caller. The plain AllocVerifierFullCircuit leaves the stage OFF.
func AllocVerifierFullCircuitWithTranscript(vf *VerifierFull, sym *SymbolicConstraints,
	meta *shrinkTranscriptMeta, nPrefixObs, nPrefixDig, nPrefixSamp, rounds, nQueries, logMax int) (*VerifierFullCircuit, error) {
	c, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		return nil, err
	}
	// The ζ-selector replay plan: the Lean-emitted selector templates + the flat
	// free-witness bank the zeta bind replays instead of calling the hand-Go
	// computeStarkSelectorsNative. Only present with the transcript stage attached
	// (the zeta bind is off otherwise).
	plan, err := loadSelectorReplayPlan(vf)
	if err != nil {
		return nil, err
	}
	c.selectorReplay = plan
	c.SelectorWitness = make([]frontend.Variable, plan.total)
	// Attach the FRI-stage template-replay context to the transcript meta: with the
	// stage attached, the per-round commit-phase leaf-hash / Merkle path / arity-2
	// fold run the committed Lean-emitted templates (emitted_fri_stage_replay.go), not
	// the hand-Go friMerkleLeafHashNative / VerifyMerklePathBn254 / friFoldRowArity2.
	if meta != nil {
		fs, err := newFriStageReplay(c.merkleTpls, c.friFoldTpl)
		if err != nil {
			return nil, err
		}
		meta.friStage = fs
	}
	c.txMeta = meta
	c.TxPrefixObs = make([]frontend.Variable, nPrefixObs)
	c.TxPrefixDig = make([]frontend.Variable, nPrefixDig)
	c.TxPrefixSamp = make([]frontend.Variable, nPrefixSamp)
	c.TxCommitRoots = make([]frontend.Variable, rounds)
	c.TxPow = make([]frontend.Variable, 1)
	c.TxFinalPoly = make([]BBExt, 1)
	c.TxQueries = make([]FriNativeQueryOpening, nQueries)
	for qi := range c.TxQueries {
		c.TxQueries[qi].RollIns = make([]BBExt, len(meta.rollInAfterRound))
		c.TxQueries[qi].Siblings = make([]BBExt, rounds)
		c.TxQueries[qi].MerkleProofs = make([][]frontend.Variable, rounds)
		for r := 0; r < rounds; r++ {
			c.TxQueries[qi].MerkleProofs[r] = make([]frontend.Variable, logMax-r-1)
		}
	}
	return c, nil
}

func (c *VerifierFullCircuit) expand(api frontend.API, bb *BBApi, rc frontend.Rangechecker,
	cur *varCursor, g VFGadget) error {
	switch g.Gadget {

	// block 0 — canonicity / VK-shape pin: v ∈ [0, p), i.e. the two 31-bit range
	// checks v < 2^31 AND (p-1-v) < 2^31 (babybear.go AssertIsCanonical). Each is a
	// REPLAY of the Lean-emitted QueryPow range template (emitQueryPow 0,
	// QueryPowEmit.lean, ∀-refined by queryPow_refines at n=0: gHolds ↔ value.val <
	// 2^31) via ReplayTemplateWithWitness (queryPowReplay) — NOT the hand-Go
	// bb.AssertIsCanonical / rc.Check(·,31) (retained as the differential oracle:
	// babybear.go / emitted_verifier_full_diff_test.go).
	case "AssertIsCanonical":
		for i := 0; i < g.Count; i++ {
			v := cur.next()
			if err := c.queryPowReplay(api, c.queryRangeTpl, c.queryRangeWit, v); err != nil {
				return fmt.Errorf("block 0 canonicity (v < 2^31): %w", err)
			}
			if err := c.queryPowReplay(api, c.queryRangeTpl, c.queryRangeWit,
				api.Sub(BabyBearP-1, v)); err != nil {
				return fmt.Errorf("block 0 canonicity (p-1-v < 2^31): %w", err)
			}
		}

	// block 1 — FRI commit-phase fold. The fold ARITHMETIC is the Lean-emitted
	// friFoldData template (FriFoldEmit.lean, ∀-refined by friFold_leaf_refines)
	// REPLAYED as real R1CS via ReplayTemplateWithWitness (friFoldReplay): the
	// deployed fold `(e0+e1)/2 + β(e0−e1)inv(2s)` and its claimed==fold check,
	// authored in Lean — NOT the hand-Go friFoldRowArity2 ExtMul cost chain (which
	// survives only as the differential oracle: fri_query.go / fri_verify_native.go
	// / emitted_verifier_full_diff_test.go). The block still reads the round-0
	// fold-beta operand off the flat bank for the transcript link (unchanged glue).
	case "FriFoldRowArity2":
		// LOAD-BEARING LINK (UNCHANGED glue): `b` is the block's fold-beta operand
		// (assignment feeds ExpectedBetas[0]); record it so Define binds it to the
		// transcript's round-0 fold beta (the sponge squeeze), not a free witness.
		b := cur.nextExt()
		beta := b
		c.block1FoldBeta = &beta
		if err := c.friFoldReplay(bb); err != nil {
			return fmt.Errorf("block 1 FRI fold replay: %w", err)
		}

	// block 1 — the fold's claimed==folded equality: `count` extension
	// equalities (babybear_ext.go ExtAssertIsEqual).
	case "ExtAssertIsEqual":
		for i := 0; i < g.Count; i++ {
			a := cur.nextExt()
			b := cur.nextExt()
			bb.ExtAssertIsEqual(a, b)
		}

	// block 2 — commit-phase Merkle openings: for each of `count` queries, a
	// depth-d authentication-path verification per round depth d. Each opening
	// REPLAYS the Lean-emitted `merklePathData d` template (MerkleEmit.lean) via
	// ReplayClosed — the deployed merkleBn254RefRoot walk authored in Lean
	// (merkle_path_refines), not the hand-Go VerifyMerklePathBn254. Materializes
	// derived.commit_merkle_compressions = count*sum(depths).
	case "VerifyMerklePathBn254":
		depths := g.Params["depths"]
		for q := 0; q < g.Count; q++ {
			for _, d := range depths {
				if err := c.merklePath(api, cur, d); err != nil {
					return fmt.Errorf("query %d: %w", q, err)
				}
			}
		}

	// block 2b — input-batch openings, the REAL deployed multi-height MMCS batch
	// tree (verifyOpenInputBatchNative). For each (query, input-round) this
	// replays the Lean-emitted `batchData` template (InputOpenBatchEmit.lean) via
	// ReplayClosed: it binds the class-concatenated opened row limbs, the
	// committed input root, and the (sibling, path-bit) pairs by the template's
	// index layout, and the replay SOLVES the per-class MultiField leaf hashes +
	// the injection-interleaved arity-2 path walk and KEEPS the real
	// recomputed-root == root check. This is the Lean-authored input-open AIR,
	// NOT the placeholder-leaf plain path the skeleton previously carried.
	case "VerifyMerklePathBn254InputOpen":
		return c.expandInputOpenBatch(api, cur, g)

	// block 3 — batch-STARK constraint algebra: for each of the `count`
	// instances, evaluate the emitted symbolic DAG at zeta and bind the folded
	// value (stark_constraint_interp.go evalSymbolicFoldedNative — the SAME
	// evaluator VerifyShrinkStarkAlgebra drives). NEEDS the companion DAG.
	case "BatchTableInstance":
		if c.sym == nil {
			return errBlock3NeedsSym
		}
		if len(c.sym.Instances) != g.Count {
			return fmt.Errorf("BatchTableInstance count %d != companion DAG instances %d",
				g.Count, len(c.sym.Instances))
		}
		// The descriptor's `degree_bits` param is the per-instance trace degree —
		// the VK-side datum the Lagrange selectors are derived from. Fail-closed:
		// the zeta bind cannot re-derive a selector whose domain it does not know.
		dbs := g.Params["degree_bits"]
		if len(dbs) != g.Count {
			return fmt.Errorf("BatchTableInstance carries %d degree_bits for %d instances — "+
				"the zeta bind needs one trace degree per instance", len(dbs), g.Count)
		}
		for i := range c.sym.Instances {
			c.starkInstance(bb, cur, &c.sym.Instances[i], i, dbs[i])
		}

	// block 3 — global LogUp balance: all cumulative sums add to zero
	// (stark_verify_native.go global WitnessChecks balance). Modeled as the
	// ext-sum-to-zero over one accumulator per instance — the assignment feeds
	// each instance's PARTIAL cumulative sum, so this NumInstances-wide sum is
	// the true global balance (assignVerifierFull, block 3).
	case "LogUpBalance":
		sum := BBExt{0, 0, 0, 0}
		for i := 0; i < c.vf.Shape.NumInstances; i++ {
			sum = bb.ExtAdd(sum, cur.nextExt())
		}
		bb.ExtAssertIsEqual(sum, BBExt{0, 0, 0, 0})

	// block 4 — grinding-PoW query index sample: a 31-bit range check (challenger
	// SampleBitsDecomposed's canonical-decomposition cost). REPLAYS the Lean-emitted
	// QueryPow range template (emitQueryPow 0) via ReplayTemplateWithWitness
	// (queryPowReplay) — NOT the hand-Go rc.Check(idx, bits) (retained as the
	// differential oracle). The template's fixed 31-bit width is enforced at load
	// (loadQueryPowTemplates asserts the descriptor's bits == 31).
	case "SampleBitsDecomposed":
		for i := 0; i < g.Count; i++ {
			idx := cur.next()
			// LOAD-BEARING LINK: record the query-index witness so Define binds it to
			// the transcript's live-sampled query index (the sponge squeeze), not a
			// free witness.
			c.block4QueryIdx = append(c.block4QueryIdx, idx)
			if err := c.queryPowReplay(api, c.queryRangeTpl, c.queryRangeWit, idx); err != nil {
				return fmt.Errorf("block 4 query-index range: %w", err)
			}
		}

	// block 4 — the PoW target: the low `pow_bits` bits of the grinding sample are
	// zero (grinding.go CheckWitness's sample_bits(bits)==0). REPLAYS the Lean-emitted
	// QueryPow grinding template (emitQueryPow pow_bits, ∀-refined by queryPow_refines /
	// queryPow_refines_native: gHolds ↔ value.val < 2^31 ∧ value.val % 2^n = 0 — the
	// deployed p3 check_witness accept) via ReplayTemplateWithWitness (queryPowReplay):
	// the 31-bit ToBinary decomposition + the low-n zero-pins, NOT the hand-Go
	// api.ToBinary + AssertIsEqual (retained as the differential oracle). The template's
	// baked n is pinned == pow_bits at load.
	case "AssertPowBitsZero":
		powBits := firstParam(g, "pow_bits")
		if powBits != c.queryPowN {
			return fmt.Errorf("block 4: AssertPowBitsZero pow_bits=%d but the loaded QueryPow "+
				"template pins %d bits", powBits, c.queryPowN)
		}
		for i := 0; i < g.Count; i++ {
			if err := c.queryPowReplay(api, c.queryPowTpl, c.queryPowWit, cur.next()); err != nil {
				return fmt.Errorf("block 4 grinding zero-pins: %w", err)
			}
		}

	// block 5 — settlement segment bind: `count` = num_public_lanes wire
	// equalities (segmentData's AssertIsEqual per lane). Each claim lane is the
	// block-3 ExposeClaim channel (captured in starkInstance where the
	// ExposeClaimAir pv==v_0 identity binds it to the committed expose_claim trace),
	// equated against the corresponding EXPOSED public-statement lane in the pinned
	// genesis8 ++ final8 ++ numTurns ++ chainDigest8 order — the SettlementCircuit
	// 25-lane binding (settlement_circuit.go:251-264). This draws NO fresh witness:
	// the LHS is the real, proof-bound claim channel, so it is a binding and not a
	// claim-vs-claim tautology over an unconstrained wire.
	case "AssertIsEqual":
		if len(c.claimChannel) < g.Count {
			return fmt.Errorf("block 5: claim channel has %d lanes, need >= %d "+
				"(block 3 ExposeClaim capture missing — is block 3 before block 5?)",
				len(c.claimChannel), g.Count)
		}
		for i := 0; i < g.Count; i++ {
			api.AssertIsEqual(c.claimChannel[i], c.publicLane(i))
		}
	}
	return nil
}

// expandInputOpenBatch replays the Lean-emitted multi-height MMCS batch-opening
// template for every (query, input-round). It consumes the flat witness bank in
// lock-step with WitnessLen and assignVerifierFull: per (query, round), R row
// limbs (class-concatenated, tallest-first), then the root, then maxLh
// (sibling, path-bit) pairs. Each opening is bound into its round's template BY
// INDEX (rows at 0..R-1, root at R, sibling s at R+1+2s, bit s at R+1+2s+1 —
// InputOpenBatchEmit.lean §9) and ReplayClosed solves the Poseidon internals and
// keeps the batch-walk recomputed-root == root check.
func (c *VerifierFullCircuit) expandInputOpenBatch(api frontend.API, cur *varCursor, g VFGadget) error {
	rw, maxLh, err := inputOpenRoundWidths(g)
	if err != nil {
		return err
	}
	nq := firstParam(g, "num_queries")
	for q := 0; q < nq; q++ {
		for r := range rw {
			R := sumInts(rw[r])
			tpl := c.batchTpls[widthsSig(rw[r])]
			if tpl == nil {
				return fmt.Errorf("no batch template loaded for input-round widths [%s]", widthsSig(rw[r]))
			}
			b := make(map[int]frontend.Variable, R+1+2*maxLh)
			for i := 0; i < R; i++ {
				b[i] = cur.next() // opened row limb i (class-concatenated)
			}
			root := cur.next() // committed input root
			b[R] = root
			// SHRINK-VK CAPTURE: the preprocessed PCS round's opened root is the
			// shrink proof's VK-core commitment; record it so bindVkPins asserts it
			// equals the baked vkPreprocessedRoot (settlement_circuit.go:268-270).
			if r == preprocessedPcsRound {
				c.preprocessedRoots = append(c.preprocessedRoots, root)
			}
			for s := 0; s < maxLh; s++ {
				b[R+1+2*s] = cur.next()   // sibling s
				b[R+1+2*s+1] = cur.next() // path bit s
			}
			if err := ReplayClosed(api, *tpl, b); err != nil {
				return fmt.Errorf("query %d input-round %d batch open (Lean template %q): %w",
					q, r, tpl.Name, err)
			}
		}
	}
	return nil
}

// merklePath verifies one depth-d commit-phase authentication path by REPLAYING
// the Lean-emitted `merklePathData d` template (MerkleEmit.lean), proven by
// `merkle_path_refines`: gHolds (merklePathData d) (pathAsg leaf root sibs bits) ↔
// refRoot leaf (sibs.zip bits) = root — the deployed merkleBn254RefRoot walk
// (bottom-up 2-to-1 Poseidon2 compress), quantified over every leaf/root/sibling/
// bit. It consumes the flat witness bank in the SAME order as before (leaf,
// sibs…, bits…, root — the diff-oracle layout in emitted_verifier_full_diff_test.go)
// and binds each into the template's canonical layout: leaf@0, root@1, sibling i
// @2+2i, path bit i @2+2i+1 (MerkleEmit.lean §5). ReplayClosed solves the Poseidon
// internals from the define-chain and keeps the REAL checks the emitted R1CS
// carries — the per-level booleanity `bit·bit = bit` and the final recomputed-root
// == root. The hand-Go VerifyMerklePathBn254 (merkle_bn254.go) is retained as the
// differential oracle; it is no longer on this emit path.
func (c *VerifierFullCircuit) merklePath(api frontend.API, cur *varCursor, d int) error {
	tpl := c.merkleTpls[d]
	if tpl == nil {
		return fmt.Errorf("no Lean-emitted Merkle-path template for depth %d "+
			"(emit merklePathData %d from MerkleEmit.lean via scripts/gen_merkle_templates.lean)", d, d)
	}
	b := make(map[int]frontend.Variable, 2+2*d)
	b[0] = cur.next() // leaf → template var 0
	sibs := make([]frontend.Variable, d)
	for i := 0; i < d; i++ {
		sibs[i] = cur.next()
	}
	bits := make([]frontend.Variable, d)
	for i := 0; i < d; i++ {
		bits[i] = cur.next()
	}
	b[1] = cur.next() // root → template var 1
	for i := 0; i < d; i++ {
		b[2+2*i] = sibs[i]   // sibling i → template var 2+2i
		b[2+2*i+1] = bits[i] // path bit i → template var 2+2i+1
	}
	if err := ReplayClosed(api, *tpl, b); err != nil {
		return fmt.Errorf("commit-phase depth-%d Merkle open (Lean template %q): %w", d, tpl.Name, err)
	}
	return nil
}

// merkleTemplatePath is the committed Lean-emitted commit-phase Merkle-path
// template for depth d (emitGnarkJson (Merkle.merklePathData d), MerkleEmit.lean;
// regenerated by metatheory/scripts/gen_merkle_templates.lean).
func merkleTemplatePath(d int) string {
	return fmt.Sprintf("emitted/merkle_path_bn254_d%d.json", d)
}

// checkMerkleTemplateShape fail-closes if a loaded merkle-path template does not
// match the depth it is replayed at: its gadget provenance must be a single
// VerifyMerklePathBn254 over [leaf, root], its boundary the two public inputs
// (leaf@0, root@1), and its structural signature the depth-d merklePathData —
// 241*d multiplication gates (240 per Poseidon2Bn254 compression + one per-level
// booleanity) over 437*d+2 variables. This ties the emitted artifact to the depth
// the interpreter binds it at, so an emitter/interpreter drift is caught here, not
// silently wired.
func checkMerkleTemplateShape(tpl *Template, d int) error {
	if len(tpl.Gadgets) != 1 || tpl.Gadgets[0].Gadget != "VerifyMerklePathBn254" {
		return fmt.Errorf("merkle template %q: unexpected gadget provenance %v "+
			"(want a single VerifyMerklePathBn254)", tpl.Name, tpl.Gadgets)
	}
	if len(tpl.PublicInputs) != 2 ||
		tpl.PublicInputs[0].Var != 0 || tpl.PublicInputs[1].Var != 1 {
		return fmt.Errorf("merkle template %q: boundary %v != [leaf@0, root@1]",
			tpl.Name, tpl.PublicInputs)
	}
	if got := tpl.NumMulGates(); got != 241*d {
		return fmt.Errorf("merkle template %q: %d mul gates != expected 241*%d=%d "+
			"(not the depth-%d merklePathData shape)", tpl.Name, got, d, 241*d, d)
	}
	if got := tpl.NumVars(); got != 437*d+2 {
		return fmt.Errorf("merkle template %q: %d vars != expected 437*%d+2=%d",
			tpl.Name, got, d, 437*d+2)
	}
	return nil
}

// loadMerkleTemplates loads (once per distinct depth) the Lean-emitted
// commit-phase Merkle-path templates block 2 replays, cross-checking each against
// the depth it is used at.
func loadMerkleTemplates(vf *VerifierFull) (map[int]*Template, error) {
	g, ok := vf.gadget("VerifyMerklePathBn254")
	if !ok {
		return nil, nil
	}
	out := map[int]*Template{}
	for _, d := range g.Params["depths"] {
		if _, done := out[d]; done {
			continue
		}
		path := merkleTemplatePath(d)
		tpl, err := LoadTemplate(path)
		if err != nil {
			return nil, fmt.Errorf("load merkle template %s: %w", path, err)
		}
		if err := checkMerkleTemplateShape(tpl, d); err != nil {
			return nil, err
		}
		out[d] = tpl
	}
	return out, nil
}

// friFoldTemplatePath is the committed Lean-emitted FRI arity-2 fold-consistency
// template (emitGnarkJson (FriFold.friFoldData …), FriFoldEmit.lean; regenerated
// by metatheory/scripts/gen_fri_fold_template.lean, alongside its honest witness
// dump fri_fold_witness.json).
func friFoldTemplatePath() string { return "emitted/fri_fold_template.json" }

func friFoldWitnessPath() string { return "emitted/fri_fold_witness.json" }

// friFoldParentBits is the parent-index-bit count the committed template is emitted
// at — the apex-shrink round-0 fold's |parentBits| = logGlobalMaxHeight − 1
// (= 19 − 1). It fixes the invS selection chain length, hence the template shape.
const friFoldParentBits = 18

// checkFriFoldTemplateShape fail-closes if the loaded fold template does not match
// the friFoldData shape: its gadget provenance must be [FriFoldRowArity2,
// ExtAssertIsEqual], its boundary the 16 sibling0/sibling1/beta/claimed limbs in
// that order, one api.Select per parent bit (the invS bit-selection chain), and its
// var/mul counts the friFoldParentBits-parameterized friFoldData counts. This ties
// the emitted artifact to the shape the interpreter binds it at, so an
// emitter/interpreter drift is caught here, not silently wired.
func checkFriFoldTemplateShape(tpl *Template) error {
	if len(tpl.Gadgets) != 2 ||
		tpl.Gadgets[0].Gadget != "FriFoldRowArity2" || tpl.Gadgets[1].Gadget != "ExtAssertIsEqual" {
		return fmt.Errorf("fri fold template %q: unexpected gadget provenance %v "+
			"(want [FriFoldRowArity2, ExtAssertIsEqual])", tpl.Name, tpl.Gadgets)
	}
	if len(tpl.PublicInputs) != 16 {
		return fmt.Errorf("fri fold template %q: %d public inputs != 16 "+
			"(sibling0/sibling1/beta/claimed, 4 limbs each)", tpl.Name, len(tpl.PublicInputs))
	}
	wantNames := []string{
		"sibling0_0", "sibling0_1", "sibling0_2", "sibling0_3",
		"sibling1_0", "sibling1_1", "sibling1_2", "sibling1_3",
		"beta_0", "beta_1", "beta_2", "beta_3",
		"folded_claim_0", "folded_claim_1", "folded_claim_2", "folded_claim_3",
	}
	for i, want := range wantNames {
		if tpl.PublicInputs[i].Name != want {
			return fmt.Errorf("fri fold template %q: public input %d is %q, want %q",
				tpl.Name, i, tpl.PublicInputs[i].Name, want)
		}
	}
	nSel := 0
	for i := range tpl.Gates {
		if tpl.Gates[i].Op == "select" {
			nSel++
		}
	}
	if nSel != friFoldParentBits {
		return fmt.Errorf("fri fold template %q: %d select gates != %d parent bits "+
			"(the invS bit-selection chain length)", tpl.Name, nSel, friFoldParentBits)
	}
	// Deterministic friFoldData shape at friFoldParentBits=18 (the committed emit).
	if got := tpl.NumVars(); got != 4818 {
		return fmt.Errorf("fri fold template %q: %d vars != 4818 (not the |bits|=%d "+
			"friFoldData shape)", tpl.Name, got, friFoldParentBits)
	}
	if got := tpl.NumMulGates(); got != 9566 {
		return fmt.Errorf("fri fold template %q: %d mul gates != 9566 (not the |bits|=%d "+
			"friFoldData shape)", tpl.Name, got, friFoldParentBits)
	}
	return nil
}

// loadFriFoldTemplate loads the Lean-emitted FRI fold-consistency template block 1
// replays, shape-checks it, and classifies its 16-limb boundary into inputs /
// free witnesses (ClassifyVars(16)). Returns (nil, nil, nil) if the descriptor
// carries no FriFoldRowArity2 gadget (nothing to replay).
func loadFriFoldTemplate(vf *VerifierFull) (*Template, *TemplateVarClass, error) {
	if _, ok := vf.gadget("FriFoldRowArity2"); !ok {
		return nil, nil, nil
	}
	tpl, err := LoadTemplate(friFoldTemplatePath())
	if err != nil {
		return nil, nil, fmt.Errorf("load fri fold template %s: %w", friFoldTemplatePath(), err)
	}
	if err := checkFriFoldTemplateShape(tpl); err != nil {
		return nil, nil, err
	}
	cls, err := tpl.ClassifyVars(len(tpl.PublicInputs))
	if err != nil {
		return nil, nil, fmt.Errorf("fri fold template: classify: %w", err)
	}
	if len(cls.Inputs) != 16 {
		return nil, nil, fmt.Errorf("fri fold template: %d classified inputs, want 16 "+
			"(the sibling0/sibling1/beta/claimed boundary)", len(cls.Inputs))
	}
	return tpl, cls, nil
}

// friFoldReplay instantiates the Lean-emitted FRI arity-2 fold-consistency template
// as real R1CS: it binds the 16-limb sibling0/sibling1/beta/claimed boundary and the
// free internal witnesses (canonicity bit decompositions, parent index bits, reduce
// quotient/remainder hints) from FriFoldWitness, and replays every assert — the fold
// define-chain SOLVES the intermediates, and the per-parent-bit booleanity + the
// 31-bit canonicity range checks + the claimed==fold equality all bite. This is the
// Lean-authored replacement for the hand-Go friFoldRowArity2 on the emit path (that
// routine survives as the differential oracle).
func (c *VerifierFullCircuit) friFoldReplay(bb *BBApi) error {
	if c.friFoldTpl == nil || c.friFoldClass == nil {
		return fmt.Errorf("block 1: FriFoldRowArity2 gadget present but no fold template loaded")
	}
	tpl := c.friFoldTpl
	nb := len(tpl.PublicInputs)
	want := nb + len(c.friFoldClass.Witness)
	if len(c.FriFoldWitness) != want {
		return fmt.Errorf("block 1: FriFoldWitness has %d entries, want %d "+
			"(%d boundary limbs + %d free witnesses)",
			len(c.FriFoldWitness), want, nb, len(c.friFoldClass.Witness))
	}
	in := make([]frontend.Variable, nb)
	for i := 0; i < nb; i++ {
		in[i] = c.FriFoldWitness[i]
	}
	wmap := make(map[int]frontend.Variable, len(c.friFoldClass.Witness))
	for k, idx := range c.friFoldClass.Witness {
		wmap[idx] = c.FriFoldWitness[nb+k]
	}
	if _, err := ReplayTemplateWithWitness(bb.API(), *tpl, in, wmap); err != nil {
		return fmt.Errorf("fri fold template %q replay: %w", tpl.Name, err)
	}
	return nil
}

// queryPowTemplatePath is the committed Lean-emitted QueryPow template for zero-pin
// count n (emitGnarkJson (emitQueryPow n), QueryPowEmit.lean; regenerated by
// metatheory/scripts/gen_query_pow_templates.lean). n=0 is the bare 31-bit range
// check; n=pow_bits (deployed 16) adds the low-n grinding zero-pins.
func queryPowTemplatePath(n int) string {
	return fmt.Sprintf("emitted/query_pow_n%d.json", n)
}

// queryPowZeroPinCount reads the zero-pin count the template BAKES in — the arg count
// of its AssertPowBitsZero gadget (emitQueryPow n records `(List.range n).map (1+·)`),
// so the Go side can fail-close if the loaded template's n disagrees with the
// descriptor's pow_bits.
func queryPowZeroPinCount(tpl *Template) int {
	for i := range tpl.Gadgets {
		if tpl.Gadgets[i].Gadget == "AssertPowBitsZero" {
			return len(tpl.Gadgets[i].Args)
		}
	}
	return 0
}

// loadQueryPowTemplate loads the QueryPow template for zero-pin count n, classifies its
// single-value input boundary + 31 free-witness ToBinary bits (ClassifyVars(1)), and
// shape-checks it fail-closed: exactly 1 input (the checked value, public var 0),
// exactly 31 free-witness bits (the ToBinary decomposition the queryPowBitsHint
// supplies), and a baked zero-pin count equal to n. Returns the template and its
// ascending free-witness bit indices (var 1+k holds bit k).
func loadQueryPowTemplate(n int) (*Template, []int, error) {
	tpl, err := LoadTemplate(queryPowTemplatePath(n))
	if err != nil {
		return nil, nil, fmt.Errorf("load query-pow template %s: %w", queryPowTemplatePath(n), err)
	}
	cls, err := tpl.ClassifyVars(1)
	if err != nil {
		return nil, nil, fmt.Errorf("query-pow template n%d: classify: %w", n, err)
	}
	if len(cls.Inputs) != 1 {
		return nil, nil, fmt.Errorf("query-pow template n%d: %d input variables, want 1 "+
			"(the checked value, public var 0)", n, len(cls.Inputs))
	}
	if len(cls.Witness) != queryPowDecompBits {
		return nil, nil, fmt.Errorf("query-pow template n%d: %d free-witness bits, want %d "+
			"(the 31-bit ToBinary decomposition)", n, len(cls.Witness), queryPowDecompBits)
	}
	if got := queryPowZeroPinCount(tpl); got != n {
		return nil, nil, fmt.Errorf("query-pow template n%d pins %d low bits (AssertPowBitsZero gadget), want %d",
			n, got, n)
	}
	return tpl, cls.Witness, nil
}

// queryPowTemplates is the per-descriptor QueryPow replay layout: the n=0 range
// template (block 0 canonicity + block 4 query-index range) and the n=pow_bits PoW
// template (block 4 grinding). Either half is nil if the descriptor carries no gadget
// that needs it.
type queryPowTemplates struct {
	rangeTpl *Template
	rangeWit []int
	powTpl   *Template
	powWit   []int
	powN     int
}

// loadQueryPowTemplates loads the Lean-emitted QueryPow templates the descriptor needs:
// the n=0 range template if AssertIsCanonical (block 0) or SampleBitsDecomposed (block
// 4) is present, and the n=pow_bits PoW template if AssertPowBitsZero (block 4) is
// present. It fail-closes if a needed template is missing or misshapen, or if the
// descriptor's SampleBitsDecomposed range is not the template's fixed 31-bit width.
func loadQueryPowTemplates(vf *VerifierFull) (*queryPowTemplates, error) {
	qp := &queryPowTemplates{}
	_, needCanon := vf.gadget("AssertIsCanonical")
	rangeG, needRange := vf.gadget("SampleBitsDecomposed")
	if needRange {
		if bits := firstParam(rangeG, "bits"); bits != queryPowDecompBits {
			return nil, fmt.Errorf("block 4: SampleBitsDecomposed bits=%d, but the QueryPow "+
				"template is a fixed %d-bit range check", bits, queryPowDecompBits)
		}
	}
	if needCanon || needRange {
		tpl, wit, err := loadQueryPowTemplate(0)
		if err != nil {
			return nil, err
		}
		qp.rangeTpl, qp.rangeWit = tpl, wit
	}
	if powG, ok := vf.gadget("AssertPowBitsZero"); ok {
		powBits := firstParam(powG, "pow_bits")
		tpl, wit, err := loadQueryPowTemplate(powBits)
		if err != nil {
			return nil, err
		}
		qp.powTpl, qp.powWit, qp.powN = tpl, wit, powBits
	}
	return qp, nil
}

// queryPowReplay instantiates a Lean-emitted QueryPow template (emitQueryPow n,
// QueryPowEmit.lean) as real R1CS at `value`: it hint-decomposes value into its low 31
// bits (queryPowBitsHint — values only), binds value as the single template input and
// the bits as the template's free internal witnesses (`wit`, by variable index), and
// replays every assert through the generic ReplayTemplateWithWitness. The template's
// booleanity + recomposition PIN the bits (the ∀-refinement `queryPow_refines`: the
// system is satisfiable iff value.val < 2^31 and — for the PoW template — its low n
// bits are zero), so this carries the range/canonicity/grinding constraint content
// with NO hand-Go range check, ToBinary, or AssertIsCanonical on the emit path.
func (c *VerifierFullCircuit) queryPowReplay(api frontend.API, tpl *Template, wit []int,
	value frontend.Variable) error {
	if tpl == nil {
		return fmt.Errorf("query-pow replay: template not loaded")
	}
	bitsVals, err := api.Compiler().NewHint(queryPowBitsHint, queryPowDecompBits, value)
	if err != nil {
		return fmt.Errorf("query-pow bit hint: %w", err)
	}
	wmap := make(map[int]frontend.Variable, len(wit))
	for k, idx := range wit {
		// wit is ascending [1..31]; wit[k] = 1+k holds bit k (powAsg), and bitsVals[k]
		// is bit k — so the k-th witness index takes the k-th hint output.
		wmap[idx] = bitsVals[k]
	}
	if _, err := ReplayTemplateWithWitness(api, *tpl, []frontend.Variable{value}, wmap); err != nil {
		return fmt.Errorf("query-pow template %q replay: %w", tpl.Name, err)
	}
	return nil
}

// block3SelectorSlot is one instance's Lagrange-selector witness triple paired
// with the trace degree_bits that determines the vanishing polynomial — the input
// to the zeta bind's in-circuit re-derivation.
type block3SelectorSlot struct {
	db  int
	sel starkSelectorsNative
}

// selectorReplayEntry is one distinct trace degree_bits' slice of the ζ-selector
// replay: the parsed Lean-emitted template (emitted/selectors_db{db}.json), the free
// internal witness variable indices ClassifyVars(4).Witness names (the honest
// selector-derivation intermediate bits the prover supplies), and the offset of this
// db's witness block in the flat SelectorWitness bank.
type selectorReplayEntry struct {
	tpl        *Template
	witnessIdx []int
	offset     int
}

// selectorReplayPlan is the per-db ζ-selector replay layout (see the field doc on
// VerifierFullCircuit.selectorReplay). entries is keyed by db; total is the sum of
// every db's free-witness count — the length of SelectorWitness.
type selectorReplayPlan struct {
	entries map[int]*selectorReplayEntry
	total   int
}

// selectorTemplatePath is the committed Lean-emitted selector template for degree
// bits db (SelectorEmit.lean §8, byte-pinned there).
func selectorTemplatePath(db int) string {
	return fmt.Sprintf("emitted/selectors_db%d.json", db)
}

// loadSelectorReplayPlan reads the Lean-emitted selector templates for every distinct
// trace degree_bits the descriptor's BatchTableInstance carries, classifies each into
// its ζ inputs / free witnesses / solved outputs (ClassifyVars with the 4-limb ζ input
// boundary), and lays out the flat SelectorWitness bank. It fail-closes if a template
// is missing, does not classify to exactly 4 ζ input variables, or a db repeats — the
// same posture as loadInputBatchTemplates for the batch-opening leaves.
func loadSelectorReplayPlan(vf *VerifierFull) (*selectorReplayPlan, error) {
	seen := map[int]bool{}
	var dbs []int
	for i := range vf.Gadgets {
		g := &vf.Gadgets[i]
		if g.Gadget != "BatchTableInstance" {
			continue
		}
		for _, db := range g.Params["degree_bits"] {
			if !seen[db] {
				seen[db] = true
				dbs = append(dbs, db)
			}
		}
	}
	sort.Ints(dbs)
	plan := &selectorReplayPlan{entries: make(map[int]*selectorReplayEntry, len(dbs))}
	for _, db := range dbs {
		path := selectorTemplatePath(db)
		tpl, err := LoadTemplate(path)
		if err != nil {
			return nil, fmt.Errorf("load selector template %s: %w", path, err)
		}
		cls, err := tpl.ClassifyVars(4)
		if err != nil {
			return nil, fmt.Errorf("selector template db%d: classify: %w", db, err)
		}
		if len(cls.Inputs) != 4 {
			return nil, fmt.Errorf("selector template db%d: %d ζ input variables, want 4 "+
				"(the emitted boundary is [zeta] over 4 limbs)", db, len(cls.Inputs))
		}
		plan.entries[db] = &selectorReplayEntry{tpl: tpl, witnessIdx: cls.Witness, offset: plan.total}
		plan.total += len(cls.Witness)
	}
	return plan, nil
}

// replaySelectorsWitness replays the Lean-emitted selector template for trace degree
// bits db at the transcript-squeezed ζ, feeding the honest free-witness bits this db's
// SelectorWitness block carries, and packs the three solved output extension elements
// into a starkSelectorsNative. It is the Lean-authored replacement for the hand-Go
// computeStarkSelectorsNative on the EMIT path (that routine survives as the
// differential oracle + KAT reference, stark_verify_native.go / the *_ref twin).
func (c *VerifierFullCircuit) replaySelectorsWitness(bb *BBApi, zeta BBExt, db int) (starkSelectorsNative, error) {
	e, ok := c.selectorReplay.entries[db]
	if !ok {
		return starkSelectorsNative{}, fmt.Errorf("zeta bind: no emitted selector template loaded for "+
			"degree_bits %d (the replay plan does not cover this instance's trace degree)", db)
	}
	wmap := make(map[int]frontend.Variable, len(e.witnessIdx))
	for k, idx := range e.witnessIdx {
		wmap[idx] = c.SelectorWitness[e.offset+k]
	}
	outs, err := ReplayTemplateWithWitness(bb.API(), *e.tpl, zeta[:], wmap)
	if err != nil {
		return starkSelectorsNative{}, fmt.Errorf("zeta bind: selector template db%d replay: %w", db, err)
	}
	if len(outs) != 12 {
		return starkSelectorsNative{}, fmt.Errorf("zeta bind: selector template db%d solved %d outputs, "+
			"want 12 (3 extension selectors)", db, len(outs))
	}
	// outs = [isFirstRow_0..3, isLastRow_0..3, isTransition_0..3] — the emitted output
	// boundary order (SelectorEmit.lean selectorsData).
	return starkSelectorsNative{
		isFirstRow:   BBExt{outs[0], outs[1], outs[2], outs[3]},
		isLastRow:    BBExt{outs[4], outs[5], outs[6], outs[7]},
		isTransition: BBExt{outs[8], outs[9], outs[10], outs[11]},
	}, nil
}

// block3OpenedSlot is one instance's openings-at-zeta witness feed, in the order
// starkInstance consumed it. `inst` indexes the shape list so the binder can slice
// the flat transcript-observed opened stream with buildStarkOpenedSpans.
type block3OpenedSlot struct {
	inst                                                          int
	traceLocal, traceNext, preLocal, preNext, permLocal, permNext []BBExt
	permValues                                                    []BBExt
	publicVals                                                    []BBExt
	// folded is this instance's alpha-folded constraint value at zeta
	// (evalSymbolicFoldedNative over the emitted DAG). The zeta bind's quotient
	// identity (bindBlockZeta tooth 3) asserts it equals quotient(zeta)·Z_H(zeta)
	// recomposed from the transcript-observed opened chunks — so folded is no
	// longer bound to a fresh, prover-chosen output.
	folded BBExt
}

// starkInstance materializes one batch-STARK instance's DAG evaluation over
// fresh witness inputs and RECORDS the alpha-folded constraint value at zeta —
// the same shape as settlement_profile_test.go's symEvalProfileCircuit, driven
// by the emitted symbolic DAG (stark_constraint_interp.go). It no longer binds
// folded to a fresh `out` witness (which left the quotient identity vacuous —
// any prover could set out := folded). The bind is now the DEEP quotient
// identity in bindBlockZeta tooth 3: folded == quotient(zeta)·Z_H(zeta),
// recomposed from the transcript-observed opened quotient chunks. So this
// function captures folded; the identity is asserted where the real openings
// live.
// `db` is the instance's trace degree_bits (the descriptor's BatchTableInstance
// `degree_bits` param) — recorded with the selector witnesses so the zeta bind can
// re-derive Z_H(zeta) and the Lagrange selectors at the transcript zeta.
func (c *VerifierFullCircuit) starkInstance(bb *BBApi, cur *varCursor, inst *SymInstance, idx, db int) {
	extVec := func(n int) []BBExt {
		out := make([]BBExt, n)
		for i := range out {
			out[i] = cur.nextExt()
		}
		return out
	}
	in := symEvalInputsNative{
		TraceLocal: extVec(inst.Width),
		TraceNext:  extVec(inst.Width),
		PreLocal:   extVec(inst.PreWidth),
		PreNext:    extVec(inst.PreWidth),
		PermLocal:  extVec(inst.NumLookups),
		PermNext:   extVec(inst.NumLookups),
		Challenges: extVec(2 * inst.NumLookups),
		PermValues: extVec(inst.NumLookups),
		Sel: starkSelectorsNative{
			isFirstRow:   cur.nextExt(),
			isLastRow:    cur.nextExt(),
			isTransition: cur.nextExt(),
		},
	}
	if inst.NumPublicValues > 0 {
		pv := make([]BBExt, inst.NumPublicValues)
		for i := range pv {
			pv[i] = BBExt{cur.next(), 0, 0, 0} // base-field public value lifted
		}
		in.PublicValues = pv
		// CLAIM-CHANNEL CAPTURE: the ExposeClaim instance is the ONLY one carrying
		// public values, and it carries exactly the 25 settlement claim lanes ++ the
		// 8 VK-spine lanes ++ the 8 apex VK-core lanes. Record them (base-field) as the
		// claim channel: block 5 binds lanes 0..25 to the public statement, the subtree
		// pin binds lanes 25..33 to the deployed root spine, and the apex-VK pin binds
		// lanes 33..41 to the pinned apex commitment. The eval below (evalSymbolicFoldedNative)
		// runs the ExposeClaimAir `pv == v_0` identity, binding each captured lane to
		// the committed expose_claim trace cell — so these are proof-bound, not free.
		if inst.NumPublicValues == ExposedShrinkClaimLanes {
			lanes := make([]frontend.Variable, inst.NumPublicValues)
			for i := range pv {
				lanes[i] = pv[i][0]
			}
			c.claimChannel = lanes
		}
	}
	alpha := cur.nextExt()
	// The alpha-folded constraint value at zeta over the emitted DAG. Recorded (not
	// bound to a fresh output here) so bindBlockZeta tooth 3 can assert it equals the
	// quotient(zeta)·Z_H(zeta) recomposed from the transcript-observed opened chunks.
	folded := evalSymbolicFoldedNative(bb, inst, in, alpha)
	// LOAD-BEARING LINK: record this instance's WitnessChecks bus (permAlpha/permBeta
	// per lookup) and constraint-folding alpha so Define binds each to the
	// transcript-re-derived challenge (TxPrefixSamp at permChSampleOff / alphaSampleOff).
	// Without this, the DAG folded == quotient·Z_H identity could be satisfied with a
	// favorable alpha/permAlpha/permBeta the transcript never sampled.
	c.block3Challenges = append(c.block3Challenges, in.Challenges)
	c.block3Alpha = append(c.block3Alpha, alpha)
	// THE ZETA BIND capture: the three Lagrange selectors (+ this instance's
	// degree_bits) and every value the instance opened AT zeta, so Define can force
	// the selectors to BE the Lean-emitted selector template's replayed outputs at the
	// transcript zeta (replaySelectorsWitness, db) and the openings to BE the
	// transcript-observed opened stream.
	c.block3Selectors = append(c.block3Selectors, block3SelectorSlot{db: db, sel: in.Sel})
	c.block3Opened = append(c.block3Opened, block3OpenedSlot{
		inst:       idx,
		traceLocal: in.TraceLocal,
		traceNext:  in.TraceNext,
		preLocal:   in.PreLocal,
		preNext:    in.PreNext,
		permLocal:  in.PermLocal,
		permNext:   in.PermNext,
		permValues: in.PermValues,
		publicVals: in.PublicValues,
		folded:     folded,
	})
}
