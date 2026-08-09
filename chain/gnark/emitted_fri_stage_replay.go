// FRI-STAGE emit-path replay — the per-round commit-phase leaf-hash / Merkle
// opening / arity-2 fold of the native FRI verifier (fri_verify_native.go
// VerifyFriQueryNative), driven by the SAME committed Lean-emitted templates the
// block path (emitted_verifier_full.go) wired in cycle 12, in place of the hand-Go
// friMerkleLeafHashNative / VerifyMerklePathBn254 / friFoldRowArity2.
//
// SUBSTRATE, said out loud. The nonlinear crypto content of the per-round FRI
// loop — the MMCS leaf hash, the bottom-up 2-to-1 Poseidon2 path compression, and
// the BabyBear-extension fold `(e0+e1)/2 + β(e0−e1)inv(2s)` with its canonicity /
// reduce range checks — is the Lean-authored, ∀-refined R1CS:
//
//   - leaf hash: leafhash_template.json (MerkleEmit.lean `MultiField32LeafHash`),
//     replayed through the generic ReplayTemplate (8 canonical row limbs → the
//     BN254 leaf node; no free witnesses — a pure define-chain);
//   - Merkle path: merkle_path_bn254_d{d}.json (MerkleEmit.lean `merklePathData d`,
//     proven by `merkle_path_refines`), replayed through ReplayClosed (leaf/root/
//     siblings/path-bits bound by index; the Poseidon internals solved, the
//     per-level booleanity + recomputed-root==root kept);
//   - fold: fri_fold_template.json (FriFoldEmit.lean `friFoldData`, proven by
//     `friFold_leaf_refines`), replayed through ReplayTemplateWithWitness (the 12
//     sibling0/sibling1/beta limbs bound, folded_claim SOLVED and returned, the
//     4705 internal reduce/canonicity/parent-bit free witnesses supplied).
//
// This is the SPLIT emit entry (fri_verify_native.go `verifyFriNativeImpl` takes a
// `*friStageReplay`): the DEPLOYED hand-Go SettlementCircuit lane
// (settlement_circuit.go → VerifyFriNative → nil replay) keeps the oracle path
// untouched. friMerkleLeafHashNative / VerifyMerklePathBn254 / friFoldRowArity2
// survive ONLY as the differential oracle (fri_leaf_hash_kat_test.go,
// merkle_bn254_test.go, fri_verify_native_test.go); the emit path no longer calls
// them.
//
// THE FOLD WITNESS. The fold template carries 4705 free internal witnesses — the
// honest hint fill the Lean `friFold_leaf_refines` theorem quantifies over (the
// reduce quotient/remainder hints, the 31-bit canonicity bit decompositions, and
// the 18 parent-index bits). On the block path those came from a committed round-0
// fixture (fri_fold_witness.json); on the FRI-stage path the siblings/beta are LIVE
// per-round in-circuit values, so the fill is materialized by a gnark HINT
// (friFoldWitnessHint) that natively SOLVES the emitted template from the bound
// inputs + the parent bits — a witness SOURCE (the analog of queryPowBitsHint), not
// a constraint author. The solver is validated to reproduce fri_fold_witness.json
// byte-for-byte (TestFriFoldWitnessSolverMatchesLeanFixture) — i.e. it reproduces
// the exact object the ∀-theorem covers. The parent-bit witnesses are then
// OVERRIDDEN in the replay wmap by the REAL query-index-bit Variables (indexBits,
// zero-padded to the template's fixed 17), so the fold's invS is bound to the
// actual sampled query index and not a prover-chosen one; every other free witness
// is pinned by the template's own constraints relative to the bound inputs.
//
// PARENT-BIT PADDING. Round r's fold has |parentBits| = logMaxHeight−r−1, which
// decreases per round; the committed fold template is emitted at the maximum (17).
// A zero parent bit selects `1` in the invS product (Select(0, ginv, 1) = 1), a
// no-op, so zero-padding the high parent bits reproduces invSFromParentRef exactly
// — the single 17-bit template serves every round. (The Merkle path, by contrast,
// cannot be padded — each level compresses a real sibling — so its per-depth
// templates d3..d17 are all committed.)
package friverifier

import (
	"fmt"
	"math/big"
	"sync"

	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
)

func init() { solver.RegisterHint(friFoldWitnessHint) }

// ---------------------------------------------------------------------------
// §1  The generic emitted-template WITNESS SOLVER (hint side).
// ---------------------------------------------------------------------------
//
// Given a Lean-emitted template and concrete values for its bound variables (a
// prefix of the public inputs) plus its genuine free INPUTS (the parent bits — the
// only free witnesses not pinned to a bound input), the solver reconstructs every
// remaining variable the honest hint fill would mint: it walks the emitted asserts
// to a fixpoint, recognizing exactly the three idioms the BabyBearFr builder emits —
//
//   - single define:  a bare `var v` == a determined expression → v is that value;
//   - reduce:         `x == q·p + r` (q, r fresh) → q = x/p, r = x%p;
//   - recomposition:  `w == Σ 2^i·b_i` (w determined, b_i fresh booleans) →
//                     b_i = bit i of w.
//
// It knows nothing template-specific; it is validated against the committed
// fri_fold_witness.json (the object friFold_leaf_refines quantifies over). Values
// are the UNTRUSTED hint fill; the Lean-authored template constraints, replayed as
// real R1CS, are what pin them.

type templateSolver struct {
	tpl     *Template
	modulus *big.Int
	vars    []*big.Int
	varSet  []bool
	wireV   []*big.Int
	wireOK  []bool
}

func newTemplateSolver(tpl *Template, mod *big.Int) *templateSolver {
	return &templateSolver{
		tpl: tpl, modulus: new(big.Int).Set(mod),
		vars: make([]*big.Int, tpl.NumVars()), varSet: make([]bool, tpl.NumVars()),
		wireV: make([]*big.Int, len(tpl.Gates)), wireOK: make([]bool, len(tpl.Gates)),
	}
}

func (s *templateSolver) bind(v int, val *big.Int) {
	s.vars[v] = new(big.Int).Mod(val, s.modulus)
	s.varSet[v] = true
}

// evalWire returns (value, true) if wire w is fully determined by the currently
// bound variables, else (nil, false). Never memoizes failure — a wire can become
// determined on a later pass.
func (s *templateSolver) evalWire(w int) (*big.Int, bool) {
	if s.wireOK[w] {
		return s.wireV[w], true
	}
	g := &s.tpl.Gates[w]
	switch g.Op {
	case "var":
		v, err := templateArgInt(g.Args[0])
		if err != nil || !s.varSet[v] {
			return nil, false
		}
		s.wireV[w], s.wireOK[w] = s.vars[v], true
		return s.vars[v], true
	case "const":
		k, ok := new(big.Int).SetString(g.Args[0].String(), 10)
		if !ok {
			return nil, false
		}
		s.wireV[w], s.wireOK[w] = k, true
		return k, true
	}
	vals := make([]*big.Int, len(g.Args))
	for i, a := range g.Args {
		wi, err := templateArgInt(a)
		if err != nil {
			return nil, false
		}
		v, ok := s.evalWire(wi)
		if !ok {
			return nil, false
		}
		vals[i] = v
	}
	var out *big.Int
	switch g.Op {
	case "add":
		out = new(big.Int).Add(vals[0], vals[1])
	case "sub":
		out = new(big.Int).Sub(vals[0], vals[1])
	case "neg":
		out = new(big.Int).Neg(vals[0])
	case "mul":
		out = new(big.Int).Mul(vals[0], vals[1])
	case "select":
		if vals[0].Sign() == 0 {
			out = new(big.Int).Set(vals[2])
		} else {
			out = new(big.Int).Set(vals[1])
		}
	default:
		return nil, false
	}
	out.Mod(out, s.modulus)
	s.wireV[w], s.wireOK[w] = out, true
	return out, true
}

func (s *templateSolver) bareVar(w int) (int, bool) {
	g := &s.tpl.Gates[w]
	if g.Op != "var" {
		return 0, false
	}
	v, err := templateArgInt(g.Args[0])
	if err != nil {
		return 0, false
	}
	return v, true
}

// trySingleDefine: a bare undetermined `var v` on this side takes the target value.
func (s *templateSolver) trySingleDefine(side int, target *big.Int) bool {
	if v, ok := s.bareVar(side); ok && !s.varSet[v] {
		s.bind(v, target)
		return true
	}
	return false
}

// tryReduce: side == add(mul(qVar, constP), rVar) with q, r fresh → q, r from target.
func (s *templateSolver) tryReduce(side int, target *big.Int) bool {
	g := &s.tpl.Gates[side]
	if g.Op != "add" {
		return false
	}
	aw, err1 := templateArgInt(g.Args[0])
	bw, err2 := templateArgInt(g.Args[1])
	if err1 != nil || err2 != nil {
		return false
	}
	ga := &s.tpl.Gates[aw]
	if ga.Op != "mul" {
		return false
	}
	qw, e3 := templateArgInt(ga.Args[0])
	pw, e4 := templateArgInt(ga.Args[1])
	if e3 != nil || e4 != nil || s.tpl.Gates[pw].Op != "const" {
		return false
	}
	qv, qok := s.bareVar(qw)
	rv, rok := s.bareVar(bw)
	if !qok || !rok || (s.varSet[qv] && s.varSet[rv]) {
		return false
	}
	P, ok := new(big.Int).SetString(s.tpl.Gates[pw].Args[0].String(), 10)
	if !ok || P.Sign() == 0 {
		return false
	}
	s.bind(qv, new(big.Int).Div(target, P))
	s.bind(rv, new(big.Int).Mod(target, P))
	return true
}

// collectLinear accumulates the (coeff·var) terms and constant of an add/sub/mul
// linear form. Returns false on a nonlinear node.
func (s *templateSolver) collectLinear(w int, coeff *big.Int, terms map[int]*big.Int, konst *big.Int) bool {
	g := &s.tpl.Gates[w]
	switch g.Op {
	case "add", "sub":
		a, e1 := templateArgInt(g.Args[0])
		b, e2 := templateArgInt(g.Args[1])
		if e1 != nil || e2 != nil {
			return false
		}
		c2 := coeff
		if g.Op == "sub" {
			c2 = new(big.Int).Neg(coeff)
		}
		return s.collectLinear(a, coeff, terms, konst) && s.collectLinear(b, c2, terms, konst)
	case "const":
		k, ok := new(big.Int).SetString(g.Args[0].String(), 10)
		if !ok {
			return false
		}
		konst.Add(konst, new(big.Int).Mul(coeff, k))
		return true
	case "var":
		v, err := templateArgInt(g.Args[0])
		if err != nil {
			return false
		}
		if terms[v] == nil {
			terms[v] = new(big.Int)
		}
		terms[v].Add(terms[v], coeff)
		return true
	case "mul":
		a, e1 := templateArgInt(g.Args[0])
		b, e2 := templateArgInt(g.Args[1])
		if e1 != nil || e2 != nil {
			return false
		}
		if s.tpl.Gates[a].Op == "const" {
			k, _ := new(big.Int).SetString(s.tpl.Gates[a].Args[0].String(), 10)
			return s.collectLinear(b, new(big.Int).Mul(coeff, k), terms, konst)
		}
		if s.tpl.Gates[b].Op == "const" {
			k, _ := new(big.Int).SetString(s.tpl.Gates[b].Args[0].String(), 10)
			return s.collectLinear(a, new(big.Int).Mul(coeff, k), terms, konst)
		}
		return false
	default:
		return false
	}
}

// tryRecomp: side is a boolean recomposition Σ 2^i·b_i (+ determined part) == target
// → each fresh b_i is bit i of the residual.
func (s *templateSolver) tryRecomp(side int, target *big.Int) bool {
	terms := map[int]*big.Int{}
	konst := new(big.Int)
	if !s.collectLinear(side, big.NewInt(1), terms, konst) {
		return false
	}
	rem := new(big.Int).Sub(target, konst)
	undet := map[int]uint{}
	for v, c := range terms {
		cc := new(big.Int).Mod(c, s.modulus)
		if s.varSet[v] {
			rem.Sub(rem, new(big.Int).Mul(cc, s.vars[v]))
			continue
		}
		bit := -1
		for i := 0; i < 64; i++ {
			if new(big.Int).Lsh(big.NewInt(1), uint(i)).Cmp(cc) == 0 {
				bit = i
				break
			}
		}
		if bit < 0 {
			return false
		}
		undet[v] = uint(bit)
	}
	if len(undet) == 0 {
		return false
	}
	rem.Mod(rem, s.modulus)
	for v, bit := range undet {
		s.bind(v, new(big.Int).And(new(big.Int).Rsh(rem, bit), big.NewInt(1)))
	}
	return true
}

func (s *templateSolver) solveSide(side int, target *big.Int) {
	if s.trySingleDefine(side, target) {
		return
	}
	if s.tryReduce(side, target) {
		return
	}
	s.tryRecomp(side, target)
}

// solve walks the emitted asserts to a fixpoint (asserts are in solved order, so a
// small pass cap suffices; the cap only guards against a malformed template).
func (s *templateSolver) solve() {
	countSet := func() int {
		n := 0
		for _, ok := range s.varSet {
			if ok {
				n++
			}
		}
		return n
	}
	for pass := 0; pass < 16; pass++ {
		before := countSet()
		for i := range s.wireOK {
			s.wireOK[i] = false
		}
		for _, a := range s.tpl.Asserts {
			lv, lok := s.evalWire(a.L)
			rv, rok := s.evalWire(a.R)
			switch {
			case lok && !rok:
				s.solveSide(a.R, lv)
			case rok && !lok:
				s.solveSide(a.L, rv)
			}
		}
		if countSet() == before {
			return
		}
	}
}

// ---------------------------------------------------------------------------
// §2  The fold-template witness hint.
// ---------------------------------------------------------------------------

// friFoldParentBitVars is, in select-gate (== parent-bit j) order, the variable
// index of each of the fold template's 18 parent-index bits — the condition var of
// each `select(bit, ginv, 1)` in the invS chain. Loaded once alongside the class.
type friFoldHintPlan struct {
	tpl          *Template
	inputVars    []int // the 12 sibling0/sibling1/beta limb vars (public inputs 0..11)
	parentVars   []int // the 18 parent-bit vars, j-order
	witnessIdx   []int // ClassifyVars(12).Witness — the free witnesses to emit, ascending
	numParent    int
	numInputLimb int
}

const friFoldHintInputLimbs = 12 // sibling0(4) ++ sibling1(4) ++ beta(4)

var (
	friFoldHintOnce sync.Once
	friFoldHintVal  *friFoldHintPlan
	friFoldHintErr  error
)

func loadFriFoldHintPlan() (*friFoldHintPlan, error) {
	friFoldHintOnce.Do(func() {
		tpl, err := LoadTemplate(friFoldTemplatePath())
		if err != nil {
			friFoldHintErr = fmt.Errorf("fold hint: load template: %w", err)
			return
		}
		if err := checkFriFoldTemplateShape(tpl); err != nil {
			friFoldHintErr = fmt.Errorf("fold hint: %w", err)
			return
		}
		// Bind a PREFIX of 12 public inputs (sibling0/sibling1/beta); folded_claim is
		// SOLVED, so its 4 limbs are derived, not supplied.
		cls, err := tpl.ClassifyVars(friFoldHintInputLimbs)
		if err != nil {
			friFoldHintErr = fmt.Errorf("fold hint: classify(12): %w", err)
			return
		}
		plan := &friFoldHintPlan{
			tpl:          tpl,
			witnessIdx:   cls.Witness,
			numParent:    friFoldParentBits,
			numInputLimb: friFoldHintInputLimbs,
		}
		for i := 0; i < friFoldHintInputLimbs; i++ {
			plan.inputVars = append(plan.inputVars, tpl.PublicInputs[i].Var)
		}
		for i := range tpl.Gates {
			if tpl.Gates[i].Op == "select" {
				cw, err := templateArgInt(tpl.Gates[i].Args[0])
				if err != nil {
					friFoldHintErr = fmt.Errorf("fold hint: select %d cond: %w", i, err)
					return
				}
				g := &tpl.Gates[cw]
				if g.Op != "var" {
					friFoldHintErr = fmt.Errorf("fold hint: select %d condition wire %d is not a bare var", i, cw)
					return
				}
				v, _ := templateArgInt(g.Args[0])
				plan.parentVars = append(plan.parentVars, v)
			}
		}
		if len(plan.parentVars) != friFoldParentBits {
			friFoldHintErr = fmt.Errorf("fold hint: %d select gates != %d parent bits",
				len(plan.parentVars), friFoldParentBits)
			return
		}
		friFoldHintVal = plan
	})
	return friFoldHintVal, friFoldHintErr
}

// friFoldWitnessHint materializes the fold template's free internal witnesses for
// one commit-phase round. Inputs: the 12 sibling0/sibling1/beta limbs followed by
// the 18 parent-index bits (real bits, zero-padded above logMaxHeight−r−1). It binds
// those, natively solves the emitted friFoldData template to a fixpoint (deriving
// folded_claim and every reduce/canonicity intermediate), and writes the
// ClassifyVars(12).Witness free witnesses in ascending index order — exactly what
// ReplayTemplateWithWitness consumes. UNTRUSTED: the template's replayed constraints
// pin every one of these against the bound inputs.
func friFoldWitnessHint(mod *big.Int, inputs, outputs []*big.Int) error {
	plan, err := loadFriFoldHintPlan()
	if err != nil {
		return err
	}
	want := plan.numInputLimb + plan.numParent
	if len(inputs) != want {
		return fmt.Errorf("friFoldWitnessHint: %d inputs, want %d (%d limbs + %d parent bits)",
			len(inputs), want, plan.numInputLimb, plan.numParent)
	}
	if len(outputs) != len(plan.witnessIdx) {
		return fmt.Errorf("friFoldWitnessHint: %d outputs, want %d free witnesses",
			len(outputs), len(plan.witnessIdx))
	}
	s := newTemplateSolver(plan.tpl, mod)
	for i, v := range plan.inputVars {
		s.bind(v, inputs[i])
	}
	for j, v := range plan.parentVars {
		s.bind(v, inputs[plan.numInputLimb+j])
	}
	s.solve()
	for k, idx := range plan.witnessIdx {
		if !s.varSet[idx] {
			return fmt.Errorf("friFoldWitnessHint: free witness var %d unsolved "+
				"(malformed inputs or template drift)", idx)
		}
		outputs[k].Set(s.vars[idx])
	}
	return nil
}

// ---------------------------------------------------------------------------
// §3  The FRI-stage replay context + per-round replay entries.
// ---------------------------------------------------------------------------

// friStageReplay holds the committed Lean-emitted templates the FRI-stage emit path
// replays in place of the hand-Go per-round loop, plus the fold witness plan. A nil
// *friStageReplay (the deployed SettlementCircuit lane) selects the hand-Go oracle;
// a non-nil one (the emit / transcript-stage lane) selects the replay.
type friStageReplay struct {
	leafTpl    *Template         // leafhash_template.json (8 row limbs → leaf)
	merkleTpls map[int]*Template // depth → merkle_path_bn254_d{d}.json
	foldTpl    *Template         // fri_fold_template.json (18 parent bits)
	foldWit    []int             // ClassifyVars(12).Witness indices, ascending
	parentVars []int             // fold template parent-bit var indices, j-order
	parentBits int               // 18
}

// newFriStageReplay assembles the replay context from the templates the block-path
// loaders already produced (merkleTpls, foldTpl) plus the committed leaf-hash
// template and the fold's ClassifyVars(12) plan. Returns (nil, nil) if the fold
// template is absent (nothing to replay).
func newFriStageReplay(merkleTpls map[int]*Template, foldTpl *Template) (*friStageReplay, error) {
	if foldTpl == nil {
		return nil, nil
	}
	leafTpl, err := LoadTemplate(leafHashTemplatePath())
	if err != nil {
		return nil, fmt.Errorf("fri-stage replay: load leaf-hash template: %w", err)
	}
	if err := checkLeafHashTemplateShape(leafTpl); err != nil {
		return nil, err
	}
	plan, err := loadFriFoldHintPlan()
	if err != nil {
		return nil, err
	}
	return &friStageReplay{
		leafTpl:    leafTpl,
		merkleTpls: merkleTpls,
		foldTpl:    foldTpl,
		foldWit:    plan.witnessIdx,
		parentVars: plan.parentVars,
		parentBits: plan.numParent,
	}, nil
}

func leafHashTemplatePath() string { return "emitted/leafhash_template.json" }

// checkLeafHashTemplateShape fail-closes if the leaf-hash template is not the
// MultiField32LeafHash[8] boundaried shape (8 row limbs → 1 leaf, no free
// witnesses), so an emitter drift is caught at load, not silently replayed.
func checkLeafHashTemplateShape(tpl *Template) error {
	if len(tpl.Gadgets) != 1 || tpl.Gadgets[0].Gadget != "MultiField32LeafHash" {
		return fmt.Errorf("leaf-hash template %q: unexpected gadget provenance %v "+
			"(want a single MultiField32LeafHash)", tpl.Name, tpl.Gadgets)
	}
	if len(tpl.PublicInputs) != 9 {
		return fmt.Errorf("leaf-hash template %q: %d public inputs != 9 (8 row limbs + leaf)",
			tpl.Name, len(tpl.PublicInputs))
	}
	cls, err := tpl.ClassifyVars(8)
	if err != nil {
		return fmt.Errorf("leaf-hash template %q: classify(8): %w", tpl.Name, err)
	}
	if len(cls.Witness) != 0 {
		return fmt.Errorf("leaf-hash template %q: %d free witnesses != 0 "+
			"(the 8-row leaf hash is a pure define-chain)", tpl.Name, len(cls.Witness))
	}
	return nil
}

// merkleOpen replays one commit-phase authentication path for the reconstructed
// sibling group (e0, e1): it hashes the two extension evals to the BN254 leaf via
// the Lean leaf-hash template (ReplayTemplate — the 8 canonical row limbs, e0's
// coefficients first, solve the leaf), then verifies the depth-d path against `root`
// via the Lean merklePathData template (ReplayClosed — leaf/root/siblings/path-bits
// bound by index). Replaces friMerkleLeafHashNative + VerifyMerklePathBn254 on the
// emit path.
func (fr *friStageReplay) merkleOpen(api frontend.API, e0, e1 BBExt,
	siblings, bits []frontend.Variable, root frontend.Variable) error {
	rows := []frontend.Variable{e0[0], e0[1], e0[2], e0[3], e1[0], e1[1], e1[2], e1[3]}
	leafOut, err := ReplayTemplate(api, *fr.leafTpl, rows)
	if err != nil {
		return fmt.Errorf("commit-phase leaf hash (Lean template %q): %w", fr.leafTpl.Name, err)
	}
	if len(leafOut) != 1 {
		return fmt.Errorf("commit-phase leaf hash: %d outputs, want 1 leaf", len(leafOut))
	}
	leaf := leafOut[0]
	d := len(siblings)
	if len(bits) != d {
		return fmt.Errorf("commit-phase Merkle open: %d siblings but %d path bits", d, len(bits))
	}
	tpl := fr.merkleTpls[d]
	if tpl == nil {
		return fmt.Errorf("no Lean-emitted Merkle-path template for depth %d", d)
	}
	b := make(map[int]frontend.Variable, 2+2*d)
	b[0] = leaf
	b[1] = root
	for i := 0; i < d; i++ {
		b[2+2*i] = siblings[i]
		b[2+2*i+1] = bits[i]
	}
	if err := ReplayClosed(api, *tpl, b); err != nil {
		return fmt.Errorf("commit-phase depth-%d Merkle open (Lean template %q): %w", d, tpl.Name, err)
	}
	return nil
}

// fold replays one arity-2 commit-phase fold for the reconstructed sibling group
// (e0, e1) at beta, over the parent-index bits. It hint-materializes the fold
// template's free witnesses (friFoldWitnessHint), binds the 12 sibling0/sibling1/
// beta limbs, OVERRIDES the parent-bit witnesses with the REAL zero-padded query
// index bits (so invS is bound to the sampled index, not a prover choice), and
// replays through ReplayTemplateWithWitness — returning the SOLVED folded_claim (the
// deployed fold `(e0+e1)/2 + β(e0−e1)inv(2s)`, authored in Lean). Replaces
// friFoldRowArity2 on the emit path.
func (fr *friStageReplay) fold(bb *BBApi, e0, e1, beta BBExt, parentBits []frontend.Variable) (BBExt, error) {
	api := bb.API()
	lfh := len(parentBits)
	if lfh > fr.parentBits {
		return BBExt{}, fmt.Errorf("fold replay: %d parent bits exceed the template's %d", lfh, fr.parentBits)
	}
	// Zero-pad the parent bits to the template's fixed width (a zero bit selects the
	// invS no-op factor 1, so padding leaves invS unchanged).
	padded := make([]frontend.Variable, fr.parentBits)
	for j := 0; j < fr.parentBits; j++ {
		if j < lfh {
			padded[j] = parentBits[j]
		} else {
			padded[j] = frontend.Variable(0)
		}
	}
	hintIn := make([]frontend.Variable, 0, friFoldHintInputLimbs+fr.parentBits)
	hintIn = append(hintIn, e0[0], e0[1], e0[2], e0[3], e1[0], e1[1], e1[2], e1[3],
		beta[0], beta[1], beta[2], beta[3])
	hintIn = append(hintIn, padded...)
	outs, err := api.Compiler().NewHint(friFoldWitnessHint, len(fr.foldWit), hintIn...)
	if err != nil {
		return BBExt{}, fmt.Errorf("fold witness hint: %w", err)
	}
	wmap := make(map[int]frontend.Variable, len(fr.foldWit))
	for k, idx := range fr.foldWit {
		wmap[idx] = outs[k]
	}
	// The parent bits are the only free witnesses NOT pinned to a bound input; bind
	// them to the REAL query-index Variables so the fold's invS is the deployed one.
	for j, v := range fr.parentVars {
		wmap[v] = padded[j]
	}
	in := []frontend.Variable{e0[0], e0[1], e0[2], e0[3], e1[0], e1[1], e1[2], e1[3],
		beta[0], beta[1], beta[2], beta[3]}
	out, err := ReplayTemplateWithWitness(api, *fr.foldTpl, in, wmap)
	if err != nil {
		return BBExt{}, fmt.Errorf("fri fold template %q replay: %w", fr.foldTpl.Name, err)
	}
	if len(out) != 4 {
		return BBExt{}, fmt.Errorf("fri fold replay: %d outputs, want 4 folded_claim limbs", len(out))
	}
	return BBExt{out[0], out[1], out[2], out[3]}, nil
}
