/-
# Dregg2.Crypto.PrivateGraphRewriteAirBridge

The missing leg of the deployed private-graph-rewrite AIR: `Satisfied2 → Accepts`.

`PrivateGraphRewriteDescriptor` stops at `privateGraphRewrite_decoded_air_sound`
(`DecodedAirFacts`: bits are honest `0/1`, range cells are in `[0,16)`, the nine
eight-felt digest blocks are full wide chip outputs, public pins are exact).  Its
own residual note names the three remaining legs:

  1. turn the controlled-swap equations into `List.Perm`;
  2. package the padded trace columns as the bounded witness;
  3. identify the nine wide outputs with `Accepts`.

This module discharges all three and assembles
`privateGraphRewrite_sat_imp_accepts`.  Two deliberate strengthenings over the
checkpoint layer:

* the trace is an ARBITRARY nonempty `VmTrace`, not the canonical `constTrace`
  four-row fixture — matching the neighbouring lowerings
  (`TypedLinearPredicateDescriptorIR2.sound`).  Row 0's content is available
  because the descriptor emits every semantic body BOTH as a `.gate` (binding on
  every non-last row) and as a `.boundary .last` (binding on the last row), so a
  one-row trace and a many-row trace both force it;
* nothing in `Accepts` or `BoundedOneStep` is weakened.  The spec is the deployed
  circuit's intended meaning and is used verbatim.

The residual assumptions are exactly the checkpoint layer's, none new: field
canonicity of the row and of the public inputs, a faithful four-bit range table,
and a sound WIDE Poseidon2 chip table (`ChipTableSoundN permOut`).  The abstract
wide permutation `permOut` is the hash `Accepts` is instantiated at, so no
collision-resistance is assumed here either.
-/
import Dregg2.Crypto.PrivateGraphRewriteDescriptor

namespace Dregg2.Crypto.PrivateGraphRewriteAirBridge

open Dregg2.Crypto.PrivateGraphRewrite
open Dregg2.Crypto.PrivateGraphRewriteDescriptor
open Dregg2.Crypto.GraphRewrite
open Dregg2.Crypto.Hypergraph
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
   ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt rangeRows
   range_row_mem_iff Lookup)

set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## §0 — modular-to-exact arithmetic on emitted bodies. -/

theorem modEq_of_sub {x y : Int} (h : x - y ≡ 0 [ZMOD 2013265921]) :
    x ≡ y [ZMOD 2013265921] := by
  have h2 := Int.ModEq.add_right y h
  simpa using h2

theorem eqBody_eval (a : Assignment) (l r : EmittedExpr) :
    (eqBody l r).eval a = l.eval a - r.eval a := by
  simp only [eqBody, sub, neg, mul, add, c, EmittedExpr.eval]
  ring

theorem choose_eval (a : Assignment) (b l r : EmittedExpr) :
    (choose b l r).eval a = l.eval a + b.eval a * (r.eval a - l.eval a) := by
  simp only [choose, add, mul, sub, neg, c, EmittedExpr.eval]
  ring

theorem choose_eval_zero {a : Assignment} {b l r : EmittedExpr} (hb : b.eval a = 0) :
    (choose b l r).eval a = l.eval a := by rw [choose_eval, hb]; ring

theorem choose_eval_one {a : Assignment} {b l r : EmittedExpr} (hb : b.eval a = 1) :
    (choose b l r).eval a = r.eval a := by rw [choose_eval, hb]; ring

theorem exact_eq_of_gate {a : Assignment} {l r : EmittedExpr}
    (hmod : (eqBody l r).eval a ≡ 0 [ZMOD 2013265921])
    (hl : 0 ≤ l.eval a ∧ l.eval a < 2013265921)
    (hr : 0 ≤ r.eval a ∧ r.eval a < 2013265921) :
    l.eval a = r.eval a := by
  refine eq_of_modEq_of_canonical (modEq_of_sub ?_) hl hr
  rw [← eqBody_eval]
  exact hmod

theorem var_eval (a : Assignment) (col : Nat) : (v col).eval a = a col := rfl

/-- Exact integer equality of a column with an already-bounded emitted body. -/
theorem col_eq_of_gate {a : Assignment} (hcanon : CanonicalAssignment a)
    {col : Nat} {r : EmittedExpr}
    (hmod : (eqBody (v col) r).eval a ≡ 0 [ZMOD 2013265921])
    (hr : 0 ≤ r.eval a ∧ r.eval a < 2013265921) : a col = r.eval a := by
  have h := exact_eq_of_gate hmod (l := v col) (by rw [var_eval]; exact hcanon col) hr
  rw [var_eval] at h
  exact h

theorem col_eq_col_of_gate {a : Assignment} (hcanon : CanonicalAssignment a)
    {col col' : Nat}
    (hmod : (eqBody (v col) (v col')).eval a ≡ 0 [ZMOD 2013265921]) : a col = a col' := by
  have h := col_eq_of_gate hcanon hmod (by rw [var_eval]; exact hcanon col')
  rw [var_eval] at h
  exact h

theorem zero_of_modEq_canonical {x : Int} (hcanon : 0 ≤ x ∧ x < 2013265921)
    (h : x ≡ 0 [ZMOD 2013265921]) : x = 0 :=
  eq_of_modEq_of_canonical h hcanon (by norm_num)

/-! ## §1 — the deployed constraint families, as membership lemmas. -/

theorem mem_sem_meta {b : EmittedExpr} (h : b ∈ metadataBodies) : b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

theorem mem_sem_ruleVar {b : EmittedExpr} (h : b ∈ ruleVarBodies) : b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

theorem mem_sem_padding {b : EmittedExpr} (h : b ∈ paddingBodies) : b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

theorem mem_sem_sigmaInj {b : EmittedExpr} (h : b ∈ sigmaInjectiveBodies) :
    b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

theorem mem_sem_lhsNonempty : lhsNonemptyBody ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append, List.mem_singleton]; tauto

theorem mem_sem_srcOld {b : EmittedExpr} (h : b ∈ sourceBodies OLD_STAGE_BASE false) :
    b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

theorem mem_sem_srcNew {b : EmittedExpr} (h : b ∈ sourceBodies NEW_STAGE_BASE true) :
    b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

theorem mem_sem_swap {b : EmittedExpr} (h : b ∈ swapBodies OLD_STAGE_BASE OLD_SWAP_BASE) :
    b ∈ semanticBodies := by
  simp only [semanticBodies, List.mem_append]; tauto

/-! ### bit columns -/

theorem mem_bitCols_ruleSlot : RULE_SLOT ∈ bitCols := by
  simp only [bitCols, List.mem_append, List.mem_singleton]; tauto

theorem mem_bitCols_ruleActive {rule slot : Nat} (hr : rule < 2) (hs : slot < 4) :
    ruleCol rule slot R_ACTIVE ∈ bitCols := by
  have h : ruleCol rule slot R_ACTIVE ∈
      ((List.range 2).flatMap fun rule => (List.range 4).map fun slot =>
        ruleCol rule slot R_ACTIVE) :=
    List.mem_flatMap.mpr ⟨rule, List.mem_range.mpr hr,
      List.mem_map.mpr ⟨slot, List.mem_range.mpr hs, rfl⟩⟩
  simp only [bitCols, List.mem_append]; tauto

theorem mem_bitCols_ruleBit {rule slot f : Nat} (hr : rule < 2) (hs : slot < 4)
    (hf : f = R_SRC_B0 ∨ f = R_SRC_B1 ∨ f = R_DST_B0 ∨ f = R_DST_B1) :
    ruleCol rule slot f ∈ bitCols := by
  have h : ruleCol rule slot f ∈
      ((List.range 2).flatMap fun rule => (List.range 4).flatMap fun slot =>
        [ruleCol rule slot R_SRC_B0, ruleCol rule slot R_SRC_B1,
         ruleCol rule slot R_DST_B0, ruleCol rule slot R_DST_B1]) :=
    List.mem_flatMap.mpr ⟨rule, List.mem_range.mpr hr,
      List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs, by
        rcases hf with rfl | rfl | rfl | rfl <;> simp⟩⟩
  simp only [bitCols, List.mem_append]; tauto

theorem mem_bitCols_ctxActive {slot : Nat} (hs : slot < 2) :
    contextCol slot E_ACTIVE ∈ bitCols := by
  have h : contextCol slot E_ACTIVE ∈
      ((List.range 2).map fun slot => contextCol slot E_ACTIVE) :=
    List.mem_map.mpr ⟨slot, List.mem_range.mpr hs, rfl⟩
  simp only [bitCols, List.mem_append]; tauto

theorem mem_bitCols_oldActive {stage slot : Nat} (hst : stage < 7) (hs : slot < 4) :
    oldStage stage slot E_ACTIVE ∈ bitCols := by
  have h : oldStage stage slot E_ACTIVE ∈
      ((List.range 7).flatMap fun stage => (List.range 4).map fun slot =>
        oldStage stage slot E_ACTIVE) :=
    List.mem_flatMap.mpr ⟨stage, List.mem_range.mpr hst,
      List.mem_map.mpr ⟨slot, List.mem_range.mpr hs, rfl⟩⟩
  simp only [bitCols, List.mem_append]; tauto

theorem mem_bitCols_newActive {slot : Nat} (hs : slot < 4) :
    newStage 0 slot E_ACTIVE ∈ bitCols := by
  have h : newStage 0 slot E_ACTIVE ∈
      ((List.range 4).map fun slot => newStage 0 slot E_ACTIVE) :=
    List.mem_map.mpr ⟨slot, List.mem_range.mpr hs, rfl⟩
  simp only [bitCols, List.mem_append]; tauto

theorem mem_bitCols_swap {stage : Nat} (h6 : stage < 6) :
    OLD_SWAP_BASE + stage ∈ bitCols := by
  have h : OLD_SWAP_BASE + stage ∈ (List.range 6 |>.map (OLD_SWAP_BASE + ·)) :=
    List.mem_map.mpr ⟨stage, List.mem_range.mpr h6, rfl⟩
  simp only [bitCols, List.mem_append]; tauto

/-! ### range columns -/

theorem mem_rangeCols_ruleLabel {rule slot : Nat} (hr : rule < 2) (hs : slot < 4) :
    ruleCol rule slot R_LABEL ∈ rangeCols := by
  have h : ruleCol rule slot R_LABEL ∈
      ((List.range 2).flatMap (fun rule =>
        (List.range 4).flatMap (fun slot => [ruleCol rule slot R_LABEL]))) :=
    List.mem_flatMap.mpr ⟨rule, List.mem_range.mpr hr,
      List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs, by simp⟩⟩
  simp only [rangeCols, List.mem_append]; tauto

theorem mem_rangeCols_ctx {slot f : Nat} (hs : slot < 2)
    (hf : f = E_LABEL ∨ f = E_SRC ∨ f = E_DST) : contextCol slot f ∈ rangeCols := by
  have h : contextCol slot f ∈
      ((List.range 2).flatMap (fun slot =>
        [contextCol slot E_LABEL, contextCol slot E_SRC, contextCol slot E_DST])) :=
    List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs, by
      rcases hf with rfl | rfl | rfl <;> simp⟩
  simp only [rangeCols, List.mem_append]; tauto

theorem mem_rangeCols_sigma {k : Nat} (hk : k < 4) : sigmaCol k ∈ rangeCols := by
  have h : sigmaCol k ∈ ((List.range 4).map sigmaCol) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  simp only [rangeCols, List.mem_append]; tauto

/-! ## §2 — row-0 facts for an ARBITRARY nonempty trace.

The descriptor emits every semantic body twice: as a `.gate` (bound on every row
but the last) and as a `.boundary .last` (bound on the last row).  So row 0
carries the whole semantic block whatever the trace length is. -/

/-- The first main row of a trace. -/
def row0 (t : VmTrace) : Assignment := (envAt t 0).loc

theorem mem_constraints_boundary {body : EmittedExpr} (h : body ∈ semanticBodies) :
    VmConstraint2.base (.boundary VmRow.last body) ∈
      privateGraphRewriteDescriptor.constraints := by
  have hm : VmConstraint2.base (.boundary VmRow.last body) ∈
      semanticBodies.map (fun b => VmConstraint2.base (VmConstraint.boundary VmRow.last b)) :=
    List.mem_map_of_mem h
  simp only [privateGraphRewriteDescriptor, List.mem_append]
  tauto

theorem mem_constraints_range {col : Nat} (h : col ∈ rangeCols) :
    VmConstraint2.lookup ⟨TableId.range, [v col]⟩ ∈
      privateGraphRewriteDescriptor.constraints := by
  have hm := range_lookup_mem_of_col h
  simp only [privateGraphRewriteDescriptor, List.mem_append]
  tauto

theorem gates_row0 {hash : List Int → Int} {t : VmTrace} (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t)
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval (row0 t) ≡ 0 [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  by_cases hlast : t.rows.length = 1
  · have h := hsat.rowConstraints 0 hpos _ (mem_constraints_boundary hbody)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, row0, hlast] using h
  · have hb : ((0 : Nat) + 1 == t.rows.length) = false := by
      simp only [Nat.zero_add, beq_eq_false_iff_ne, ne_eq]
      omega
    have h := hsat.rowConstraints 0 hpos _ (semantic_gate_mem hbody)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, row0, hb] using h

theorem pins_row0 {hash : List Int → Int} {t : VmTrace} (hne : t.rows ≠ [])
    (hcanon : CanonicalAssignment (row0 t)) (hcanonPis : CanonicalAssignment t.pub)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t)
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding VmRow.first col pi) ∈ publicPins) :
    row0 t col = t.pub pi := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos _ (public_pin_mem hpin)
  have hmod : row0 t col ≡ t.pub pi [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, row0, envAt] using h
  exact eq_of_modEq_of_canonical hmod (hcanon col) (hcanonPis pi)

theorem ranges_row0 {hash : List Int → Int} {t : VmTrace} (hne : t.rows ≠ [])
    (hrange : t.tf TableId.range = rangeRows 4)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t)
    {col : Nat} (hcol : col ∈ rangeCols) :
    0 ≤ row0 t col ∧ row0 t col < 16 := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hrow := hsat.rowConstraints 0 hpos _ (mem_constraints_range hcol)
  have hmem : [row0 t col] ∈ t.tf TableId.range := by
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, row0, v, EmittedExpr.eval] using hrow
  rw [hrange] at hmem
  have hb := (range_row_mem_iff (row0 t col) 4).mp hmem
  norm_num at hb ⊢
  exact hb

theorem bits_row0 {hash : List Int → Int} {t : VmTrace} (hne : t.rows ≠ [])
    (hcanon : CanonicalAssignment (row0 t))
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t)
    {col : Nat} (hcol : col ∈ bitCols) : row0 t col = 0 ∨ row0 t col = 1 :=
  binary_of_modular_gate hcanon (gates_row0 hne hsat (binary_body_mem_of_bit_col hcol))

theorem wide_hash_row0 {hash : List Int → Int} {t : VmTrace} (hne : t.rows ≠ [])
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t)
    {inputs : List EmittedExpr} {outCols : List Nat}
    (hlen : inputs.length ≤ 16)
    (hlookup : VmConstraint2.lookup
      ⟨TableId.poseidon2, chipLookupTupleN inputs outCols⟩ ∈ hashLookups) :
    outCols.map (row0 t) = permOut (inputs.map (·.eval (row0 t))) := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hrow := hsat.rowConstraints 0 hpos _ (hash_lookup_mem hlookup)
  have hmem : (chipLookupTupleN inputs outCols).map (·.eval (row0 t)) ∈
      t.tf TableId.poseidon2 := by
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, row0] using hrow
  exact chip_lookup_sound_N permOut (t.tf TableId.poseidon2) hChip (row0 t)
    inputs outCols hlen hmem

/-- Everything the semantic block gives at row 0, bundled. -/
structure AirFacts (a : Assignment) : Prop where
  canon : CanonicalAssignment a
  gates : ∀ body ∈ semanticBodies, body.eval a ≡ 0 [ZMOD 2013265921]
  bits : ∀ col ∈ bitCols, a col = 0 ∨ a col = 1
  ranges : ∀ col ∈ rangeCols, 0 ≤ a col ∧ a col < 16

theorem airFacts_row0 {hash : List Int → Int} {t : VmTrace} (hne : t.rows ≠ [])
    (hcanon : CanonicalAssignment (row0 t))
    (hrange : t.tf TableId.range = rangeRows 4)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t) :
    AirFacts (row0 t) :=
  ⟨hcanon, fun _ hb => gates_row0 hne hsat hb, fun _ hc => bits_row0 hne hcanon hsat hc,
   fun _ hc => ranges_row0 hne hrange hsat hc⟩

/-! ## §3 — finite decode of columns into the bounded witness carriers. -/

abbrev Raw := Fin 4 → Int

def i16 (x : Int) : Fin 16 := ⟨x.toNat % 16, Nat.mod_lt _ (by norm_num)⟩
def i4 (x : Int) : Fin 4 := ⟨x.toNat % 4, Nat.mod_lt _ (by norm_num)⟩

theorem i16_val {x : Int} (h0 : 0 ≤ x) (h16 : x < 16) : ((i16 x).val : Int) = x := by
  have h : x.toNat % 16 = x.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [i16, h]
  omega

theorem i4_val {x : Int} (h0 : 0 ≤ x) (h4 : x < 4) : ((i4 x).val : Int) = x := by
  have h : x.toNat % 4 = x.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [i4, h]
  omega

theorem i16_zero : i16 0 = 0 := rfl

/-- Raw four-field host slot read off a stage block. -/
def rawAt (a : Assignment) (base stage : Nat) : Fin 4 → Raw :=
  fun slot field => a (stageCol base stage slot.val field.val)

/-- Raw four-field host slot read off the two preserved-context slots. -/
def rawCtx (a : Assignment) : Fin 2 → Raw :=
  fun slot field => a (contextCol slot.val field.val)

def slotOf (r : Raw) : HostEdgeSlot :=
  { active := decide (r 0 = 1), label := i16 (r 1), src := i16 (r 2), dst := i16 (r 3) }

def ruleSlotOf (a : Assignment) (rule slot : Nat) : RuleEdgeSlot :=
  { active := decide (a (ruleCol rule slot R_ACTIVE) = 1)
  , label := i16 (a (ruleCol rule slot R_LABEL))
  , src := i4 (a (ruleCol rule slot R_SRC))
  , dst := i4 (a (ruleCol rule slot R_DST)) }

/-- Bounds + canonical padding of one raw slot. -/
structure RawOk (r : Raw) : Prop where
  bit : r 0 = 0 ∨ r 0 = 1
  lab : 0 ≤ r 1 ∧ r 1 < 16
  src : 0 ≤ r 2 ∧ r 2 < 16
  dst : 0 ≤ r 3 ∧ r 3 < 16
  pad : r 0 = 0 → r 1 = 0 ∧ r 2 = 0 ∧ r 3 = 0

theorem slotOf_active {r : Raw} : (slotOf r).active = true ↔ r 0 = 1 := by
  simp [slotOf]

theorem slotOf_padding {r : Raw} (h : RawOk r) : (slotOf r).canonicalPadding := by
  intro hact
  have h0 : r 0 = 0 := by
    rcases h.bit with h1 | h1
    · exact h1
    · exact absurd (slotOf_active.mpr h1) (by simp [hact])
  obtain ⟨e1, e2, e3⟩ := h.pad h0
  refine ⟨?_, ?_, ?_⟩ <;> simp only [slotOf, e1, e2, e3] <;> exact i16_zero

theorem hostSlotFields_slotOf {r : Raw} (h : RawOk r) :
    hostSlotFields (slotOf r) = [r 0, r 1, r 2, r 3] := by
  have hb : boolInt (slotOf r).active = r 0 := by
    rcases h.bit with h1 | h1 <;> simp [slotOf, boolInt, h1]
  have e1 : (((slotOf r).label).val : Int) = r 1 := i16_val h.lab.1 h.lab.2
  have e2 : (((slotOf r).src).val : Int) = r 2 := i16_val h.src.1 h.src.2
  have e3 : (((slotOf r).dst).val : Int) = r 3 := i16_val h.dst.1 h.dst.2
  simp only [hostSlotFields, hb, e1, e2, e3]

/-! ## §4 — LEG 1: the six-comparator swap network decodes to `List.Perm`. -/

/-- The index the comparator reads from, as a `Fin 4` selector. -/
def swapIdxF (stage : Fin 6) (bit : Bool) (slot : Fin 4) : Fin 4 :=
  match bit with
  | false => slot
  | true =>
      if slot = (swapPair stage).1 then (swapPair stage).2
      else if slot = (swapPair stage).2 then (swapPair stage).1 else slot

theorem controlledSwap4_apply {α : Type} (stage : Fin 6) (bit : Bool)
    (xs : Fin 4 → α) (slot : Fin 4) :
    controlledSwap4 stage bit xs slot = xs (swapIdxF stage bit slot) := by
  cases bit
  · rfl
  · show (if slot = (swapPair stage).1 then xs (swapPair stage).2
          else if slot = (swapPair stage).2 then xs (swapPair stage).1 else xs slot)
        = xs (if slot = (swapPair stage).1 then (swapPair stage).2
              else if slot = (swapPair stage).2 then (swapPair stage).1 else slot)
    split_ifs <;> rfl

/-- The control bit of comparator `stage`, decoded. -/
def swapBit (a : Assignment) (stage : Fin 6) : Bool :=
  decide (a (OLD_SWAP_BASE + stage.val) = 1)

/-- The emitted swap gate for one `(stage, slot, field)` cell. -/
theorem swap_body_mem (stage : Fin 6) {slot field : Nat} (hs : slot < 4) (hf : field < 4) :
    eqBody (v (stageCol OLD_STAGE_BASE (stage.val + 1) slot field))
      (choose (v (OLD_SWAP_BASE + stage.val))
        (v (stageCol OLD_STAGE_BASE stage.val slot field))
        (if slot = ((swapPair stage).1).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).2).val field)
          else if slot = ((swapPair stage).2).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).1).val field)
          else v (stageCol OLD_STAGE_BASE stage.val slot field)))
      ∈ semanticBodies := by
  refine mem_sem_swap ?_
  refine List.mem_flatten.mpr ⟨swapStageBodies OLD_STAGE_BASE OLD_SWAP_BASE stage, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨stage, rfl⟩
  · exact List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs,
      List.mem_map.mpr ⟨field, List.mem_range.mpr hf, rfl⟩⟩

theorem swap_col_eq {a : Assignment} (F : AirFacts a) (stage : Fin 6) (slot field : Fin 4) :
    a (stageCol OLD_STAGE_BASE (stage.val + 1) slot.val field.val)
      = a (stageCol OLD_STAGE_BASE stage.val
            (swapIdxF stage (swapBit a stage) slot).val field.val) := by
  have hg := F.gates _ (swap_body_mem stage slot.isLt field.isLt)
  have hbit := F.bits _ (mem_bitCols_swap stage.isLt)
  rcases hbit with hb | hb
  · have hchoose : (choose (v (OLD_SWAP_BASE + stage.val))
        (v (stageCol OLD_STAGE_BASE stage.val slot.val field.val))
        (if slot.val = ((swapPair stage).1).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).2).val field.val)
          else if slot.val = ((swapPair stage).2).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).1).val field.val)
          else v (stageCol OLD_STAGE_BASE stage.val slot.val field.val))).eval a
        = a (stageCol OLD_STAGE_BASE stage.val slot.val field.val) :=
      choose_eval_zero (by rw [var_eval]; exact hb)
    have h := col_eq_of_gate F.canon hg (by rw [hchoose]; exact F.canon _)
    rw [hchoose] at h
    have hidx : swapIdxF stage (swapBit a stage) slot = slot := by
      have : swapBit a stage = false := by simp [swapBit, hb]
      simp [swapIdxF, this]
    rw [hidx]
    exact h
  · have hbt : swapBit a stage = true := by simp [swapBit, hb]
    have hpartner :
        (if slot.val = ((swapPair stage).1).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).2).val field.val)
          else if slot.val = ((swapPair stage).2).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).1).val field.val)
          else v (stageCol OLD_STAGE_BASE stage.val slot.val field.val))
        = v (stageCol OLD_STAGE_BASE stage.val
              (swapIdxF stage (swapBit a stage) slot).val field.val) := by
      rw [hbt]
      show _ = v (stageCol OLD_STAGE_BASE stage.val
        (if slot = (swapPair stage).1 then (swapPair stage).2
         else if slot = (swapPair stage).2 then (swapPair stage).1 else slot).val field.val)
      by_cases h1 : slot = (swapPair stage).1
      · have hv1 : slot.val = ((swapPair stage).1).val := by rw [h1]
        rw [if_pos hv1, if_pos h1]
      · have hne1 : ¬ (slot.val = ((swapPair stage).1).val) := fun hc => h1 (Fin.ext hc)
        rw [if_neg hne1, if_neg h1]
        by_cases h2 : slot = (swapPair stage).2
        · have hv2 : slot.val = ((swapPair stage).2).val := by rw [h2]
          rw [if_pos hv2, if_pos h2]
        · have hne2 : ¬ (slot.val = ((swapPair stage).2).val) := fun hc => h2 (Fin.ext hc)
          rw [if_neg hne2, if_neg h2]
    have hchoose : (choose (v (OLD_SWAP_BASE + stage.val))
        (v (stageCol OLD_STAGE_BASE stage.val slot.val field.val))
        (if slot.val = ((swapPair stage).1).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).2).val field.val)
          else if slot.val = ((swapPair stage).2).val then
            v (stageCol OLD_STAGE_BASE stage.val ((swapPair stage).1).val field.val)
          else v (stageCol OLD_STAGE_BASE stage.val slot.val field.val))).eval a
        = a (stageCol OLD_STAGE_BASE stage.val
              (swapIdxF stage (swapBit a stage) slot).val field.val) := by
      rw [choose_eval_one (by rw [var_eval]; exact hb), hpartner, var_eval]
    have h := col_eq_of_gate F.canon hg (by rw [hchoose]; exact F.canon _)
    rw [hchoose] at h
    exact h

theorem old_stage_step {a : Assignment} (F : AirFacts a) (stage : Fin 6) :
    rawAt a OLD_STAGE_BASE (stage.val + 1)
      = controlledSwap4 stage (swapBit a stage) (rawAt a OLD_STAGE_BASE stage.val) := by
  funext slot field
  rw [controlledSwap4_apply]
  exact swap_col_eq F stage slot field

/-- **LEG 1.** The satisfied six-comparator network forces the exact four-slot
multiset: the hashed stage-6 block is a permutation of the canonical stage-0
`context ++ σ·lhs` arrangement. -/
theorem old_stage6_perm {a : Assignment} (F : AirFacts a) :
    (List.ofFn (rawAt a OLD_STAGE_BASE 0)).Perm (List.ofFn (rawAt a OLD_STAGE_BASE 6)) := by
  have h1 := old_stage_step F 0
  have h2 := old_stage_step F 1
  have h3 := old_stage_step F 2
  have h4 := old_stage_step F 3
  have h5 := old_stage_step F 4
  have h6 := old_stage_step F 5
  simp only [Fin.val_zero, Fin.val_one, Fin.isValue] at h1 h2 h3 h4 h5 h6
  exact six_controlled_swaps_perm (rawAt a OLD_STAGE_BASE 0) (rawAt a OLD_STAGE_BASE 1)
    (rawAt a OLD_STAGE_BASE 2) (rawAt a OLD_STAGE_BASE 3) (rawAt a OLD_STAGE_BASE 4)
    (rawAt a OLD_STAGE_BASE 5) (rawAt a OLD_STAGE_BASE 6)
    (swapBit a 0) (swapBit a 1) (swapBit a 2) (swapBit a 3) (swapBit a 4) (swapBit a 5)
    h1 h2 h3 h4 h5 h6

/-- Every stage-6 slot is literally some stage-0 slot; bounds and padding travel. -/
theorem old_stage6_reindex {a : Assignment} (F : AirFacts a) (slot : Fin 4) :
    ∃ j : Fin 4, rawAt a OLD_STAGE_BASE 6 slot = rawAt a OLD_STAGE_BASE 0 j := by
  have h1 := old_stage_step F 0
  have h2 := old_stage_step F 1
  have h3 := old_stage_step F 2
  have h4 := old_stage_step F 3
  have h5 := old_stage_step F 4
  have h6 := old_stage_step F 5
  have g1 : rawAt a OLD_STAGE_BASE 1
      = controlledSwap4 0 (swapBit a 0) (rawAt a OLD_STAGE_BASE 0) := h1
  have g2 : rawAt a OLD_STAGE_BASE 2
      = controlledSwap4 1 (swapBit a 1) (rawAt a OLD_STAGE_BASE 1) := h2
  have g3 : rawAt a OLD_STAGE_BASE 3
      = controlledSwap4 2 (swapBit a 2) (rawAt a OLD_STAGE_BASE 2) := h3
  have g4 : rawAt a OLD_STAGE_BASE 4
      = controlledSwap4 3 (swapBit a 3) (rawAt a OLD_STAGE_BASE 3) := h4
  have g5 : rawAt a OLD_STAGE_BASE 5
      = controlledSwap4 4 (swapBit a 4) (rawAt a OLD_STAGE_BASE 4) := h5
  have g6 : rawAt a OLD_STAGE_BASE 6
      = controlledSwap4 5 (swapBit a 5) (rawAt a OLD_STAGE_BASE 5) := h6
  refine ⟨swapIdxF 0 (swapBit a 0) (swapIdxF 1 (swapBit a 1) (swapIdxF 2 (swapBit a 2)
    (swapIdxF 3 (swapBit a 3) (swapIdxF 4 (swapBit a 4) (swapIdxF 5 (swapBit a 5) slot))))), ?_⟩
  rw [g6, controlledSwap4_apply, g5, controlledSwap4_apply, g4, controlledSwap4_apply,
    g3, controlledSwap4_apply, g2, controlledSwap4_apply, g1, controlledSwap4_apply]

/-! ## §5 — the source stage: stage 0 IS `context ++ σ·pattern`. -/

def selR (a : Assignment) : Nat := if a RULE_SLOT = 1 then 1 else 0

theorem selR_lt (a : Assignment) : selR a < 2 := by
  unfold selR; split <;> omega

theorem choose_ruleSlot {a : Assignment} (F : AirFacts a) (l r : EmittedExpr) :
    (choose (v RULE_SLOT) l r).eval a = if a RULE_SLOT = 1 then r.eval a else l.eval a := by
  rcases F.bits RULE_SLOT mem_bitCols_ruleSlot with h | h
  · rw [choose_eval_zero (by rw [var_eval]; exact h)]
    simp [h]
  · rw [choose_eval_one (by rw [var_eval]; exact h)]
    simp [h]

theorem choose_ruleCol {a : Assignment} (F : AirFacts a) (slot field : Nat) :
    (choose (v RULE_SLOT) (v (ruleCol 0 slot field)) (v (ruleCol 1 slot field))).eval a
      = a (ruleCol (selR a) slot field) := by
  rw [choose_ruleSlot F, var_eval, var_eval]
  unfold selR
  split <;> rfl

/-- Membership of the four context-copy gates of one source block. -/
theorem source_ctx_mem (base : Nat) (rhs : Bool) {slot field : Nat}
    (hs : slot < 2) (hf : field < 4) :
    eqBody (v (stageCol base 0 slot field)) (v (contextCol slot field))
      ∈ sourceBodies base rhs := by
  refine List.mem_append_left _ ?_
  exact List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs,
    List.mem_map.mpr ⟨field, List.mem_range.mpr hf, rfl⟩⟩

theorem source_rule_mem (base : Nat) (rhs : Bool) {slot : Nat} (hs : slot < 2)
    {b : EmittedExpr}
    (hb : b ∈ [ eqBody (v (stageCol base 0 (2 + slot) E_ACTIVE))
          (choose (v RULE_SLOT)
            (v (ruleCol 0 ((if rhs then 2 else 0) + slot) R_ACTIVE))
            (v (ruleCol 1 ((if rhs then 2 else 0) + slot) R_ACTIVE)))
      , eqBody (v (stageCol base 0 (2 + slot) E_LABEL))
          (choose (v RULE_SLOT)
            (v (ruleCol 0 ((if rhs then 2 else 0) + slot) R_LABEL))
            (v (ruleCol 1 ((if rhs then 2 else 0) + slot) R_LABEL)))
      , eqBody (v (stageCol base 0 (2 + slot) E_SRC))
          (mul (selectedRuleActive ((if rhs then 2 else 0) + slot))
            (choose (v RULE_SLOT)
              (muxSigma 0 ((if rhs then 2 else 0) + slot) true)
              (muxSigma 1 ((if rhs then 2 else 0) + slot) true)))
      , eqBody (v (stageCol base 0 (2 + slot) E_DST))
          (mul (selectedRuleActive ((if rhs then 2 else 0) + slot))
            (choose (v RULE_SLOT)
              (muxSigma 0 ((if rhs then 2 else 0) + slot) false)
              (muxSigma 1 ((if rhs then 2 else 0) + slot) false))) ]) :
    b ∈ sourceBodies base rhs := by
  refine List.mem_append_right _ ?_
  exact List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs, hb⟩

theorem i4_lit0 : (i4 (0 + 2 * 0)).val = 0 := rfl
theorem i4_lit1 : (i4 (1 + 2 * 0)).val = 1 := rfl
theorem i4_lit2 : (i4 (0 + 2 * 1)).val = 2 := rfl
theorem i4_lit3 : (i4 (1 + 2 * 1)).val = 3 := rfl

/-- The `muxSigma` two-bit selector really reads `σ` at the rule slot's variable. -/
theorem mux_eval_gen {a : Assignment} {vcol b0col b1col : Nat}
    (h0 : a b0col = 0 ∨ a b0col = 1) (h1 : a b1col = 0 ∨ a b1col = 1)
    (hvar : a vcol = a b0col + 2 * a b1col) :
    (choose (v b1col) (choose (v b0col) (v (sigmaCol 0)) (v (sigmaCol 1)))
      (choose (v b0col) (v (sigmaCol 2)) (v (sigmaCol 3)))).eval a
      = a (sigmaCol (i4 (a vcol)).val) := by
  rcases h1 with e1 | e1
  · rw [choose_eval_zero (b := v b1col) (by rw [var_eval]; exact e1)]
    rcases h0 with e0 | e0
    · rw [choose_eval_zero (b := v b0col) (by rw [var_eval]; exact e0), var_eval, hvar, e0, e1,
        i4_lit0]
    · rw [choose_eval_one (b := v b0col) (by rw [var_eval]; exact e0), var_eval, hvar, e0, e1,
        i4_lit1]
  · rw [choose_eval_one (b := v b1col) (by rw [var_eval]; exact e1)]
    rcases h0 with e0 | e0
    · rw [choose_eval_zero (b := v b0col) (by rw [var_eval]; exact e0), var_eval, hvar, e0, e1,
        i4_lit2]
    · rw [choose_eval_one (b := v b0col) (by rw [var_eval]; exact e0), var_eval, hvar, e0, e1,
        i4_lit3]

/-- The two-bit decomposition gate of one rule-slot endpoint. -/
theorem ruleVar_eq_gen {a : Assignment} (F : AirFacts a) {rule slot fv f0 f1 : Nat}
    (hmem : eqBody (v (ruleCol rule slot fv))
      (add (v (ruleCol rule slot f0)) (mul (c 2) (v (ruleCol rule slot f1))))
      ∈ ruleVarBodies)
    (h0 : a (ruleCol rule slot f0) = 0 ∨ a (ruleCol rule slot f0) = 1)
    (h1 : a (ruleCol rule slot f1) = 0 ∨ a (ruleCol rule slot f1) = 1) :
    a (ruleCol rule slot fv)
      = a (ruleCol rule slot f0) + 2 * a (ruleCol rule slot f1) := by
  have hg := F.gates _ (mem_sem_ruleVar hmem)
  have hev : (add (v (ruleCol rule slot f0)) (mul (c 2) (v (ruleCol rule slot f1)))).eval a
      = a (ruleCol rule slot f0) + 2 * a (ruleCol rule slot f1) := by
    simp only [add, mul, c, v, EmittedExpr.eval]
  have hbound : 0 ≤ (add (v (ruleCol rule slot f0))
        (mul (c 2) (v (ruleCol rule slot f1)))).eval a ∧
      (add (v (ruleCol rule slot f0)) (mul (c 2) (v (ruleCol rule slot f1)))).eval a
        < 2013265921 := by
    rw [hev]
    rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rw [e0, e1] <;> norm_num
  have h := col_eq_of_gate F.canon hg hbound
  rw [hev] at h
  exact h

theorem ruleVarSrc_mem {rule slot : Nat} (hr : rule < 2) (hs : slot < 4) :
    eqBody (v (ruleCol rule slot R_SRC))
      (add (v (ruleCol rule slot R_SRC_B0)) (mul (c 2) (v (ruleCol rule slot R_SRC_B1))))
      ∈ ruleVarBodies :=
  List.mem_flatMap.mpr ⟨rule, List.mem_range.mpr hr,
    List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs, by simp⟩⟩

theorem ruleVarDst_mem {rule slot : Nat} (hr : rule < 2) (hs : slot < 4) :
    eqBody (v (ruleCol rule slot R_DST))
      (add (v (ruleCol rule slot R_DST_B0)) (mul (c 2) (v (ruleCol rule slot R_DST_B1))))
      ∈ ruleVarBodies :=
  List.mem_flatMap.mpr ⟨rule, List.mem_range.mpr hr,
    List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs, by simp⟩⟩

theorem ruleVarSrc_eq {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    a (ruleCol rule slot R_SRC)
      = a (ruleCol rule slot R_SRC_B0) + 2 * a (ruleCol rule slot R_SRC_B1) :=
  ruleVar_eq_gen F (ruleVarSrc_mem hr hs)
    (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inl rfl)))
    (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inl rfl))))

theorem ruleVarDst_eq {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    a (ruleCol rule slot R_DST)
      = a (ruleCol rule slot R_DST_B0) + 2 * a (ruleCol rule slot R_DST_B1) :=
  ruleVar_eq_gen F (ruleVarDst_mem hr hs)
    (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inr (Or.inl rfl)))))
    (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inr (Or.inr rfl)))))

/-! ## §6 — LEG 2: the padded source stage IS `context ++ σ·pattern`. -/

theorem liveHost_four (s : Fin 4 → HostEdgeSlot) :
    liveHostEdges s
      = [s 0, s 1, s 2, s 3].filterMap (fun e => if e.active then some e.edge else none) := rfl

theorem liveHost_two (s : Fin 2 → HostEdgeSlot) :
    liveHostEdges s
      = [s 0, s 1].filterMap (fun e => if e.active then some e.edge else none) := rfl

theorem liveRule_two (s : Fin 2 → RuleEdgeSlot) :
    liveRuleEdges s
      = [s 0, s 1].filterMap (fun e => if e.active then some e.edge else none) := rfl

theorem i4_zero : i4 0 = 0 := rfl

/-- Raw slot vector addressed by a plain `Nat` slot index. -/
def rawN (a : Assignment) (base stage slot : Nat) : Raw :=
  fun f => a (stageCol base stage slot f.val)

def rawCtxN (a : Assignment) (slot : Nat) : Raw :=
  fun f => a (contextCol slot f.val)

theorem rawAt_eq_rawN (a : Assignment) (base stage : Nat) (slot : Fin 4) :
    rawAt a base stage slot = rawN a base stage slot.val := rfl

/-! ### padding gates -/

theorem rule_pad_mem {rule slot k : Nat} (hr : rule < 2) (hs : slot < 4) (hk : k < 3) :
    mul (sub (c 1) (v (ruleCol rule slot R_ACTIVE))) (v (ruleCol rule slot (1 + k)))
      ∈ paddingBodies :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, List.mem_range.mpr hr,
    List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs,
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩⟩)

theorem ctx_pad_mem {slot k : Nat} (hs : slot < 2) (hk : k < 3) :
    mul (sub (c 1) (v (contextCol slot E_ACTIVE))) (v (contextCol slot (1 + k)))
      ∈ paddingBodies :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs,
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩)

theorem pad_zero_gen {a : Assignment} (F : AirFacts a) {actCol fCol : Nat}
    (hmem : mul (sub (c 1) (v actCol)) (v fCol) ∈ paddingBodies)
    (hact : a actCol = 0) : a fCol = 0 := by
  have hg := F.gates _ (mem_sem_padding hmem)
  have hev : (mul (sub (c 1) (v actCol)) (v fCol)).eval a = a fCol := by
    simp only [mul, sub, neg, add, c, v, EmittedExpr.eval, hact]; ring
  rw [hev] at hg
  exact zero_of_modEq_canonical (F.canon _) hg

theorem rawCtxN_ok {a : Assignment} (F : AirFacts a) {slot : Nat} (hs : slot < 2) :
    RawOk (rawCtxN a slot) := by
  refine ⟨F.bits _ (mem_bitCols_ctxActive hs),
    F.ranges _ (mem_rangeCols_ctx hs (Or.inl rfl)),
    F.ranges _ (mem_rangeCols_ctx hs (Or.inr (Or.inl rfl))),
    F.ranges _ (mem_rangeCols_ctx hs (Or.inr (Or.inr rfl))), ?_⟩
  intro h0
  have h0' : a (contextCol slot E_ACTIVE) = 0 := h0
  exact ⟨(pad_zero_gen F (ctx_pad_mem hs (k := 0) (by norm_num)) h0' :
            a (contextCol slot E_LABEL) = 0),
         (pad_zero_gen F (ctx_pad_mem hs (k := 1) (by norm_num)) h0' :
            a (contextCol slot E_SRC) = 0),
         (pad_zero_gen F (ctx_pad_mem hs (k := 2) (by norm_num)) h0' :
            a (contextCol slot E_DST) = 0)⟩

/-! ### the source block -/

theorem stage0_ctx_col {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {slot field : Nat} (hs : slot < 2) (hf : field < 4) :
    a (stageCol base 0 slot field) = a (contextCol slot field) :=
  col_eq_col_of_gate F.canon (F.gates _ (hsub _ (source_ctx_mem base rhs hs hf)))

theorem stage0_ctxN {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {slot : Nat} (hs : slot < 2) : rawN a base 0 slot = rawCtxN a slot := by
  funext f
  exact stage0_ctx_col F hsub hs f.isLt

theorem selectedRuleActive_eval {a : Assignment} (F : AirFacts a) (s : Nat) :
    (selectedRuleActive s).eval a = a (ruleCol (selR a) s R_ACTIVE) :=
  choose_ruleCol F s R_ACTIVE

theorem muxSigma_src_eval {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    (muxSigma rule slot true).eval a
      = a (sigmaCol (i4 (a (ruleCol rule slot R_SRC))).val) :=
  mux_eval_gen (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inl rfl)))
    (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inl rfl))))
    (ruleVarSrc_eq F hr hs)

theorem muxSigma_dst_eval {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    (muxSigma rule slot false).eval a
      = a (sigmaCol (i4 (a (ruleCol rule slot R_DST))).val) :=
  mux_eval_gen (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inr (Or.inl rfl)))))
    (F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inr (Or.inr rfl)))))
    (ruleVarDst_eq F hr hs)

theorem ruleOff_add_lt {rhs : Bool} {k : Nat} (hk : k < 2) :
    (if rhs then 2 else 0) + k < 4 := by cases rhs <;> simp <;> omega

theorem stage0_rule_active {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {k : Nat} (hk : k < 2) :
    a (stageCol base 0 (2 + k) E_ACTIVE)
      = a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE) := by
  have hmem : eqBody (v (stageCol base 0 (2 + k) E_ACTIVE))
      (choose (v RULE_SLOT)
        (v (ruleCol 0 ((if rhs then 2 else 0) + k) R_ACTIVE))
        (v (ruleCol 1 ((if rhs then 2 else 0) + k) R_ACTIVE))) ∈ sourceBodies base rhs :=
    source_rule_mem base rhs hk (by simp)
  have hg := F.gates _ (hsub _ hmem)
  have hev := choose_ruleCol F ((if rhs then 2 else 0) + k) R_ACTIVE
  have h := col_eq_of_gate F.canon hg (by rw [hev]; exact F.canon _)
  rw [hev] at h
  exact h

theorem stage0_rule_label {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {k : Nat} (hk : k < 2) :
    a (stageCol base 0 (2 + k) E_LABEL)
      = a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_LABEL) := by
  have hmem : eqBody (v (stageCol base 0 (2 + k) E_LABEL))
      (choose (v RULE_SLOT)
        (v (ruleCol 0 ((if rhs then 2 else 0) + k) R_LABEL))
        (v (ruleCol 1 ((if rhs then 2 else 0) + k) R_LABEL))) ∈ sourceBodies base rhs :=
    source_rule_mem base rhs hk (by simp)
  have hg := F.gates _ (hsub _ hmem)
  have hev := choose_ruleCol F ((if rhs then 2 else 0) + k) R_LABEL
  have h := col_eq_of_gate F.canon hg (by rw [hev]; exact F.canon _)
  rw [hev] at h
  exact h

theorem stage0_rule_src {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {k : Nat} (hk : k < 2) :
    a (stageCol base 0 (2 + k) E_SRC)
      = a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE)
        * a (sigmaCol
              (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).val) := by
  have hslt : (if rhs then 2 else 0) + k < 4 := ruleOff_add_lt hk
  have hmem : eqBody (v (stageCol base 0 (2 + k) E_SRC))
      (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
        (choose (v RULE_SLOT)
          (muxSigma 0 ((if rhs then 2 else 0) + k) true)
          (muxSigma 1 ((if rhs then 2 else 0) + k) true))) ∈ sourceBodies base rhs :=
    source_rule_mem base rhs hk (by simp)
  have hg := F.gates _ (hsub _ hmem)
  have hchoose : (choose (v RULE_SLOT)
      (muxSigma 0 ((if rhs then 2 else 0) + k) true)
      (muxSigma 1 ((if rhs then 2 else 0) + k) true)).eval a
      = a (sigmaCol (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).val) := by
    rw [choose_ruleSlot F, muxSigma_src_eval F (by norm_num) hslt,
      muxSigma_src_eval F (by norm_num) hslt]
    unfold selR
    split <;> rfl
  have hev : (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
      (choose (v RULE_SLOT)
        (muxSigma 0 ((if rhs then 2 else 0) + k) true)
        (muxSigma 1 ((if rhs then 2 else 0) + k) true))).eval a
      = a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE)
        * a (sigmaCol
              (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).val) := by
    simp only [mul, EmittedExpr.eval]
    rw [selectedRuleActive_eval F, hchoose]
  have hbound : 0 ≤ (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
      (choose (v RULE_SLOT)
        (muxSigma 0 ((if rhs then 2 else 0) + k) true)
        (muxSigma 1 ((if rhs then 2 else 0) + k) true))).eval a ∧
      (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
      (choose (v RULE_SLOT)
        (muxSigma 0 ((if rhs then 2 else 0) + k) true)
        (muxSigma 1 ((if rhs then 2 else 0) + k) true))).eval a < 2013265921 := by
    rw [hev]
    obtain ⟨hs1, hs2⟩ := F.ranges _ (mem_rangeCols_sigma
      (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).isLt)
    rcases F.bits _ (mem_bitCols_ruleActive (selR_lt a) hslt) with e | e
    · rw [e, zero_mul]; norm_num
    · rw [e, one_mul]; omega
  have h := col_eq_of_gate F.canon hg hbound
  rw [hev] at h
  exact h

theorem stage0_rule_dst {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {k : Nat} (hk : k < 2) :
    a (stageCol base 0 (2 + k) E_DST)
      = a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE)
        * a (sigmaCol
              (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).val) := by
  have hslt : (if rhs then 2 else 0) + k < 4 := ruleOff_add_lt hk
  have hmem : eqBody (v (stageCol base 0 (2 + k) E_DST))
      (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
        (choose (v RULE_SLOT)
          (muxSigma 0 ((if rhs then 2 else 0) + k) false)
          (muxSigma 1 ((if rhs then 2 else 0) + k) false))) ∈ sourceBodies base rhs :=
    source_rule_mem base rhs hk (by simp)
  have hg := F.gates _ (hsub _ hmem)
  have hchoose : (choose (v RULE_SLOT)
      (muxSigma 0 ((if rhs then 2 else 0) + k) false)
      (muxSigma 1 ((if rhs then 2 else 0) + k) false)).eval a
      = a (sigmaCol (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).val) := by
    rw [choose_ruleSlot F, muxSigma_dst_eval F (by norm_num) hslt,
      muxSigma_dst_eval F (by norm_num) hslt]
    unfold selR
    split <;> rfl
  have hev : (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
      (choose (v RULE_SLOT)
        (muxSigma 0 ((if rhs then 2 else 0) + k) false)
        (muxSigma 1 ((if rhs then 2 else 0) + k) false))).eval a
      = a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE)
        * a (sigmaCol
              (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).val) := by
    simp only [mul, EmittedExpr.eval]
    rw [selectedRuleActive_eval F, hchoose]
  have hbound : 0 ≤ (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
      (choose (v RULE_SLOT)
        (muxSigma 0 ((if rhs then 2 else 0) + k) false)
        (muxSigma 1 ((if rhs then 2 else 0) + k) false))).eval a ∧
      (mul (selectedRuleActive ((if rhs then 2 else 0) + k))
      (choose (v RULE_SLOT)
        (muxSigma 0 ((if rhs then 2 else 0) + k) false)
        (muxSigma 1 ((if rhs then 2 else 0) + k) false))).eval a < 2013265921 := by
    rw [hev]
    obtain ⟨hs1, hs2⟩ := F.ranges _ (mem_rangeCols_sigma
      (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).isLt)
    rcases F.bits _ (mem_bitCols_ruleActive (selR_lt a) hslt) with e | e
    · rw [e, zero_mul]; norm_num
    · rw [e, one_mul]; omega
  have h := col_eq_of_gate F.canon hg hbound
  rw [hev] at h
  exact h

theorem stage0_ruleN_ok {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {k : Nat} (hk : k < 2) : RawOk (rawN a base 0 (2 + k)) := by
  have hslt : (if rhs then 2 else 0) + k < 4 := ruleOff_add_lt hk
  have hact := stage0_rule_active F hsub hk
  have hlab := stage0_rule_label F hsub hk
  have hsrc := stage0_rule_src F hsub hk
  have hdst := stage0_rule_dst F hsub hk
  have hbit := F.bits _ (mem_bitCols_ruleActive (selR_lt a) hslt)
  obtain ⟨hl1, hl2⟩ := F.ranges _ (mem_rangeCols_ruleLabel (selR_lt a) hslt)
  obtain ⟨hp1, hp2⟩ := F.ranges _ (mem_rangeCols_sigma
    (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).isLt)
  obtain ⟨hq1, hq2⟩ := F.ranges _ (mem_rangeCols_sigma
    (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).isLt)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show a (stageCol base 0 (2 + k) E_ACTIVE) = 0 ∨ a (stageCol base 0 (2 + k) E_ACTIVE) = 1
    rw [hact]; exact hbit
  · show 0 ≤ a (stageCol base 0 (2 + k) E_LABEL) ∧ a (stageCol base 0 (2 + k) E_LABEL) < 16
    rw [hlab]; exact ⟨hl1, hl2⟩
  · show 0 ≤ a (stageCol base 0 (2 + k) E_SRC) ∧ a (stageCol base 0 (2 + k) E_SRC) < 16
    rw [hsrc]
    rcases hbit with e | e
    · rw [e, zero_mul]; norm_num
    · rw [e, one_mul]; omega
  · show 0 ≤ a (stageCol base 0 (2 + k) E_DST) ∧ a (stageCol base 0 (2 + k) E_DST) < 16
    rw [hdst]
    rcases hbit with e | e
    · rw [e, zero_mul]; norm_num
    · rw [e, one_mul]; omega
  · intro h0
    have h0' : a (stageCol base 0 (2 + k) E_ACTIVE) = 0 := h0
    rw [hact] at h0'
    refine ⟨?_, ?_, ?_⟩
    · show a (stageCol base 0 (2 + k) E_LABEL) = 0
      rw [hlab]
      exact (pad_zero_gen F (rule_pad_mem (selR_lt a) hslt (k := 0) (by norm_num)) h0' :
        a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_LABEL) = 0)
    · show a (stageCol base 0 (2 + k) E_SRC) = 0
      rw [hsrc, h0', zero_mul]
    · show a (stageCol base 0 (2 + k) E_DST) = 0
      rw [hdst, h0', zero_mul]

theorem stage0_okN {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    {slot : Nat} (hs : slot < 4) : RawOk (rawN a base 0 slot) := by
  have h4 : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rw [stage0_ctxN F hsub (by norm_num)]; exact rawCtxN_ok F (by norm_num)
  · rw [stage0_ctxN F hsub (by norm_num)]; exact rawCtxN_ok F (by norm_num)
  · exact stage0_ruleN_ok F hsub (k := 0) (by norm_num)
  · exact stage0_ruleN_ok F hsub (k := 1) (by norm_num)

theorem stage0_ok {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies)
    (slot : Fin 4) : RawOk (rawAt a base 0 slot) :=
  stage0_okN F hsub slot.isLt

/-! ### the decoded substitution -/

def sigmaOf (a : Assignment) : Var → Node := fun k => i16 (a (sigmaCol k.val))

theorem sigmaPairs_zipIdx :
    sigmaPairs.zipIdx
      = [((0, 1), 0), ((0, 2), 1), ((0, 3), 2), ((1, 2), 3), ((1, 3), 4), ((2, 3), 5)] := rfl

theorem sigma_distinct {a : Assignment} (F : AirFacts a) {i j idx : Nat}
    (hmem : ((i, j), idx) ∈ sigmaPairs.zipIdx) :
    a (sigmaCol i) ≠ a (sigmaCol j) := by
  have hbody : sub (mul (sub (v (sigmaCol i)) (v (sigmaCol j))) (v (sigmaInvCol idx))) (c 1)
      ∈ sigmaInjectiveBodies := List.mem_map_of_mem hmem
  have hg := F.gates _ (mem_sem_sigmaInj hbody)
  intro heq
  have hev : (sub (mul (sub (v (sigmaCol i)) (v (sigmaCol j))) (v (sigmaInvCol idx)))
      (c 1)).eval a = -1 := by
    simp only [sub, mul, neg, add, c, v, EmittedExpr.eval, heq]
    ring
  rw [hev] at hg
  have hd : (2013265921 : Int) ∣ (-1) := Int.modEq_zero_iff_dvd.mp hg
  have hd1 : (2013265921 : Int) ∣ 1 := (dvd_neg).mp hd
  have hle := Int.le_of_dvd (by norm_num) hd1
  norm_num at hle

theorem sigmaOf_injective {a : Assignment} (F : AirFacts a) :
    Function.Injective (sigmaOf a) := by
  have d01 := sigma_distinct F (i := 0) (j := 1) (idx := 0) (by rw [sigmaPairs_zipIdx]; simp)
  have d02 := sigma_distinct F (i := 0) (j := 2) (idx := 1) (by rw [sigmaPairs_zipIdx]; simp)
  have d03 := sigma_distinct F (i := 0) (j := 3) (idx := 2) (by rw [sigmaPairs_zipIdx]; simp)
  have d12 := sigma_distinct F (i := 1) (j := 2) (idx := 3) (by rw [sigmaPairs_zipIdx]; simp)
  have d13 := sigma_distinct F (i := 1) (j := 3) (idx := 4) (by rw [sigmaPairs_zipIdx]; simp)
  have d23 := sigma_distinct F (i := 2) (j := 3) (idx := 5) (by rw [sigmaPairs_zipIdx]; simp)
  have key : ∀ i j : Nat, i < 4 → j < 4 → i ≠ j → a (sigmaCol i) ≠ a (sigmaCol j) := by
    intro i j hi hj hij
    have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hi4 with rfl | rfl | rfl | rfl <;> rcases hj4 with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hij
        | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d03 | exact d03.symm
        | exact d12 | exact d12.symm | exact d13 | exact d13.symm | exact d23 | exact d23.symm
  intro x y hxy
  by_contra hne
  have hxy' : i16 (a (sigmaCol x.val)) = i16 (a (sigmaCol y.val)) := hxy
  obtain ⟨hx1, hx2⟩ := F.ranges _ (mem_rangeCols_sigma x.isLt)
  obtain ⟨hy1, hy2⟩ := F.ranges _ (mem_rangeCols_sigma y.isLt)
  have hv : ((i16 (a (sigmaCol x.val))).val : Int) = ((i16 (a (sigmaCol y.val))).val : Int) := by
    rw [hxy']
  rw [i16_val hx1 hx2, i16_val hy1 hy2] at hv
  exact key x.val y.val x.isLt y.isLt (fun hc => hne (Fin.ext hc)) hv

/-! ### the selected rule is nonempty on the left -/

theorem lhs_active {a : Assignment} (F : AirFacts a) :
    a (ruleCol (selR a) 0 R_ACTIVE) = 1 ∨ a (ruleCol (selR a) 1 R_ACTIVE) = 1 := by
  have hg := F.gates _ mem_sem_lhsNonempty
  have hev : lhsNonemptyBody.eval a
      = (1 - a (ruleCol (selR a) 0 R_ACTIVE)) * (1 - a (ruleCol (selR a) 1 R_ACTIVE)) := by
    simp only [lhsNonemptyBody]
    rw [choose_ruleSlot F]
    unfold selR
    split_ifs <;> simp only [mul, sub, neg, add, c, v, EmittedExpr.eval] <;> ring
  have h0 := F.bits _ (mem_bitCols_ruleActive (selR_lt a) (by norm_num : (0 : Nat) < 4))
  have h1 := F.bits _ (mem_bitCols_ruleActive (selR_lt a) (by norm_num : (1 : Nat) < 4))
  rcases h0 with e0 | e0
  · rcases h1 with e1 | e1
    · exfalso
      rw [hev, e0, e1] at hg
      have hone : (1 : Int) ≡ 0 [ZMOD 2013265921] := by simpa using hg
      have hd : (2013265921 : Int) ∣ 1 := Int.modEq_zero_iff_dvd.mp hone
      have hle := Int.le_of_dvd (by norm_num) hd
      norm_num at hle
    · exact Or.inr e1
  · exact Or.inl e0

theorem ruleSlotOf_pad {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) : (ruleSlotOf a rule slot).canonicalPadding := by
  intro hact
  have h0 : a (ruleCol rule slot R_ACTIVE) = 0 := by
    rcases F.bits _ (mem_bitCols_ruleActive hr hs) with h | h
    · exact h
    · exfalso
      have : (ruleSlotOf a rule slot).active = true := by simp [ruleSlotOf, h]
      rw [hact] at this
      exact Bool.noConfusion this
  have hl : a (ruleCol rule slot R_LABEL) = 0 :=
    pad_zero_gen F (rule_pad_mem hr hs (k := 0) (by norm_num)) h0
  have hs2 : a (ruleCol rule slot R_SRC) = 0 :=
    pad_zero_gen F (rule_pad_mem hr hs (k := 1) (by norm_num)) h0
  have hd : a (ruleCol rule slot R_DST) = 0 :=
    pad_zero_gen F (rule_pad_mem hr hs (k := 2) (by norm_num)) h0
  refine ⟨?_, ?_, ?_⟩
  · show i16 (a (ruleCol rule slot R_LABEL)) = 0
    rw [hl]; exact i16_zero
  · show i4 (a (ruleCol rule slot R_SRC)) = 0
    rw [hs2]; exact i4_zero
  · show i4 (a (ruleCol rule slot R_DST)) = 0
    rw [hd]; exact i4_zero

/-! ### the decoded edge lists -/

theorem filterMap_two_map {α β γ δ : Type} (f : α → Option γ) (h : β → Option δ)
    (m : δ → γ) (x0 x1 : α) (y0 y1 : β)
    (e0 : f x0 = (h y0).map m) (e1 : f x1 = (h y1).map m) :
    [x0, x1].filterMap f = ([y0, y1].filterMap h).map m := by
  cases hy0 : h y0 <;> cases hy1 : h y1 <;> simp [e0, e1, hy0, hy1]

theorem slot_edge_eq {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies) {k : Nat} (hk : k < 2) :
    (if (slotOf (rawN a base 0 (2 + k))).active
        then some (slotOf (rawN a base 0 (2 + k))).edge else none)
      = (if (ruleSlotOf a (selR a) ((if rhs then 2 else 0) + k)).active
          then some (ruleSlotOf a (selR a) ((if rhs then 2 else 0) + k)).edge
          else none).map (mapEdge (sigmaOf a)) := by
  have hact := stage0_rule_active F hsub hk
  have hlabv := stage0_rule_label F hsub hk
  have hslt : (if rhs then 2 else 0) + k < 4 := ruleOff_add_lt hk
  rcases F.bits _ (mem_bitCols_ruleActive (selR_lt a) hslt) with e | e
  · have hA : (slotOf (rawN a base 0 (2 + k))).active = false := by
      show decide (a (stageCol base 0 (2 + k) E_ACTIVE) = 1) = false
      rw [hact, e]; simp
    have hB : (ruleSlotOf a (selR a) ((if rhs then 2 else 0) + k)).active = false := by
      show decide (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE) = 1) = false
      rw [e]; simp
    rw [if_neg (by simp [hA]), if_neg (by simp [hB])]
    rfl
  · have hactv : a (stageCol base 0 (2 + k) E_ACTIVE) = 1 := by rw [hact, e]
    have hA : (slotOf (rawN a base 0 (2 + k))).active = true := by
      show decide (a (stageCol base 0 (2 + k) E_ACTIVE) = 1) = true
      rw [hactv]; simp
    have hB : (ruleSlotOf a (selR a) ((if rhs then 2 else 0) + k)).active = true := by
      show decide (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_ACTIVE) = 1) = true
      rw [e]; simp
    have hsrcv : a (stageCol base 0 (2 + k) E_SRC)
        = a (sigmaCol (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).val) := by
      rw [stage0_rule_src F hsub hk, e, one_mul]
    have hdstv : a (stageCol base 0 (2 + k) E_DST)
        = a (sigmaCol (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).val) := by
      rw [stage0_rule_dst F hsub hk, e, one_mul]
    rw [if_pos (by simp [hA]), if_pos (by simp [hB]), Option.map_some]
    refine congrArg some ?_
    have hlab : i16 (a (stageCol base 0 (2 + k) E_LABEL))
        = i16 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_LABEL)) := by rw [hlabv]
    have hsrc : i16 (a (stageCol base 0 (2 + k) E_SRC))
        = i16 (a (sigmaCol
            (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))).val)) := by rw [hsrcv]
    have hdst : i16 (a (stageCol base 0 (2 + k) E_DST))
        = i16 (a (sigmaCol
            (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST))).val)) := by rw [hdstv]
    show ((i16 (a (stageCol base 0 (2 + k) E_LABEL))),
        [i16 (a (stageCol base 0 (2 + k) E_SRC)), i16 (a (stageCol base 0 (2 + k) E_DST))])
      = ((i16 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_LABEL))),
        [sigmaOf a (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_SRC))),
         sigmaOf a (i4 (a (ruleCol (selR a) ((if rhs then 2 else 0) + k) R_DST)))])
    rw [hlab, hsrc, hdst]
    rfl

/-- **LEG 2.** The satisfied source block IS the canonical decomposition
`preserved context ++ instantiated pattern`. -/
theorem source_edges {a : Assignment} (F : AirFacts a) {base : Nat} {rhs : Bool}
    (hsub : ∀ b ∈ sourceBodies base rhs, b ∈ semanticBodies) :
    liveHostEdges (fun i : Fin 4 => slotOf (rawAt a base 0 i))
      = liveHostEdges (fun i : Fin 2 => slotOf (rawCtxN a i.val))
        ++ (liveRuleEdges (fun k : Fin 2 =>
              ruleSlotOf a (selR a) ((if rhs then 2 else 0) + k.val))).map
            (mapEdge (sigmaOf a)) := by
  have c0 : rawAt a base 0 0 = rawCtxN a 0 := stage0_ctxN F hsub (by norm_num)
  have c1 : rawAt a base 0 1 = rawCtxN a 1 := stage0_ctxN F hsub (by norm_num)
  rw [liveHost_four, liveHost_two, liveRule_two, c0, c1]
  rw [show ([slotOf (rawCtxN a 0), slotOf (rawCtxN a 1), slotOf (rawAt a base 0 2),
        slotOf (rawAt a base 0 3)] : List HostEdgeSlot)
      = [slotOf (rawCtxN a 0), slotOf (rawCtxN a 1)]
        ++ [slotOf (rawAt a base 0 2), slotOf (rawAt a base 0 3)] from rfl,
    List.filterMap_append]
  refine congrArg (fun l => _ ++ l) ?_
  exact filterMap_two_map _ _ _ _ _ _ _
    (slot_edge_eq F hsub (k := 0) (by norm_num))
    (slot_edge_eq F hsub (k := 1) (by norm_num))

/-- **LEG 1, decoded.** The hashed stage-6 host graph is a permutation of the
canonical stage-0 arrangement. -/
theorem old_edges_perm {a : Assignment} (F : AirFacts a) :
    (liveHostEdges (fun i : Fin 4 => slotOf (rawAt a OLD_STAGE_BASE 6 i))).Perm
      (liveHostEdges (fun i : Fin 4 => slotOf (rawAt a OLD_STAGE_BASE 0 i))) := by
  have hp := (old_stage6_perm F).symm
  have h2 := (hp.map slotOf).filterMap (fun e => if e.active then some e.edge else none)
  simpa [liveHostEdges, List.map_ofFn, Function.comp_def] using h2

/-! ## §7 — LEG 3: the nine wide chip outputs ARE the `Accepts` digests. -/

theorem len_stageFieldExprs (base stage : Nat) : (stageFieldExprs base stage).length = 16 := rfl
theorem len_graphRootInputExprs (cb bb : Nat) (s : Int) :
    (graphRootInputExprs cb bb s).length = 16 := rfl
theorem len_ruleFieldExprs (r : Nat) : (ruleFieldExprs r).length = 16 := rfl
theorem len_ruleLeafInputExprs (cb r : Nat) : (ruleLeafInputExprs cb r).length = 16 := rfl
theorem len_rulesetInputExprs : rulesetInputExprs.length = 16 := rfl

theorem outCols_map (a : Assignment) (base : Nat) :
    ((List.range 8).map (base + ·)).map a
      = [a (base + 0), a (base + 1), a (base + 2), a (base + 3),
         a (base + 4), a (base + 5), a (base + 6), a (base + 7)] := rfl

theorem digest8_cols {permOut : List Int → List Int} {a : Assignment} {base : Nat}
    {xs : List Int}
    (h : permOut xs = [a (base + 0), a (base + 1), a (base + 2), a (base + 3),
      a (base + 4), a (base + 5), a (base + 6), a (base + 7)]) :
    digest8 permOut xs = fun i => a (base + i.val) := by
  funext i
  simp only [digest8, h]
  fin_cases i <;> rfl

theorem graphCoreInputs_eq (g : BoundedGraph) :
    graphCoreInputs g = hostSlotFields (g.slots 0) ++ hostSlotFields (g.slots 1)
      ++ hostSlotFields (g.slots 2) ++ hostSlotFields (g.slots 3) := rfl

theorem stageFieldExprs_eval (a : Assignment) (base stage : Nat) :
    (stageFieldExprs base stage).map (fun e => e.eval a)
      = [a (stageCol base stage 0 0), a (stageCol base stage 0 1),
         a (stageCol base stage 0 2), a (stageCol base stage 0 3),
         a (stageCol base stage 1 0), a (stageCol base stage 1 1),
         a (stageCol base stage 1 2), a (stageCol base stage 1 3),
         a (stageCol base stage 2 0), a (stageCol base stage 2 1),
         a (stageCol base stage 2 2), a (stageCol base stage 2 3),
         a (stageCol base stage 3 0), a (stageCol base stage 3 1),
         a (stageCol base stage 3 2), a (stageCol base stage 3 3)] := rfl

theorem core_eq_stageFields {a : Assignment} {base stage : Nat}
    (hp : ∀ i, (slotOf (rawAt a base stage i)).canonicalPadding)
    (hok : ∀ i, RawOk (rawAt a base stage i)) :
    graphCoreInputs ⟨fun i => slotOf (rawAt a base stage i), hp⟩
      = (stageFieldExprs base stage).map (fun e => e.eval a) := by
  rw [graphCoreInputs_eq, stageFieldExprs_eval,
    hostSlotFields_slotOf (hok 0), hostSlotFields_slotOf (hok 1),
    hostSlotFields_slotOf (hok 2), hostSlotFields_slotOf (hok 3)]
  rfl

theorem graphRootInputExprs_eval (a : Assignment) (cb bb : Nat) (side : Int) :
    (graphRootInputExprs cb bb side).map (fun e => e.eval a)
      = graphRootInputs (fun i => a (cb + i.val)) (fun i => a (bb + i.val))
          (a DOMAIN) (a SESSION) (a VERSION) side := rfl

theorem ruleFieldExprs_eval (a : Assignment) (r : Nat) :
    (ruleFieldExprs r).map (fun e => e.eval a)
      = [a (ruleCol r 0 0), a (ruleCol r 0 1), a (ruleCol r 0 2), a (ruleCol r 0 3),
         a (ruleCol r 1 0), a (ruleCol r 1 1), a (ruleCol r 1 2), a (ruleCol r 1 3),
         a (ruleCol r 2 0), a (ruleCol r 2 1), a (ruleCol r 2 2), a (ruleCol r 2 3),
         a (ruleCol r 3 0), a (ruleCol r 3 1), a (ruleCol r 3 2), a (ruleCol r 3 3)] := rfl

theorem ruleCoreInputs_eq (r : BoundedRule) :
    ruleCoreInputs r = ruleSlotFields (r.lhs.slots 0) ++ ruleSlotFields (r.lhs.slots 1)
      ++ (ruleSlotFields (r.rhs.slots 0) ++ ruleSlotFields (r.rhs.slots 1)) := rfl

theorem ruleLeafInputExprs_eval (a : Assignment) (cb r : Nat) :
    (ruleLeafInputExprs cb r).map (fun e => e.eval a)
      = ruleLeafInputs (fun i => a (cb + i.val)) (fun i => a (ruleBlindCol r i.val))
          (a DOMAIN) (a VERSION) (a SHAPE) (r : Int) := rfl

theorem rulesetInputExprs_eval (a : Assignment) :
    rulesetInputExprs.map (fun e => e.eval a)
      = rulesetNodeInputs (fun i => a (RULE0_LEAF_BASE + i.val))
          (fun i => a (RULE1_LEAF_BASE + i.val)) := rfl

theorem ruleVarSrc_lt {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    0 ≤ a (ruleCol rule slot R_SRC) ∧ a (ruleCol rule slot R_SRC) < 4 := by
  rw [ruleVarSrc_eq F hr hs]
  rcases F.bits _ (mem_bitCols_ruleBit hr hs (Or.inl rfl)) with e0 | e0 <;>
    rcases F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inl rfl))) with e1 | e1 <;>
      rw [e0, e1] <;> norm_num

theorem ruleVarDst_lt {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    0 ≤ a (ruleCol rule slot R_DST) ∧ a (ruleCol rule slot R_DST) < 4 := by
  rw [ruleVarDst_eq F hr hs]
  rcases F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inr (Or.inl rfl)))) with e0 | e0 <;>
    rcases F.bits _ (mem_bitCols_ruleBit hr hs (Or.inr (Or.inr (Or.inr rfl)))) with e1 | e1 <;>
      rw [e0, e1] <;> norm_num

theorem ruleSlotFields_eq {a : Assignment} (F : AirFacts a) {rule slot : Nat}
    (hr : rule < 2) (hs : slot < 4) :
    ruleSlotFields (ruleSlotOf a rule slot)
      = [a (ruleCol rule slot R_ACTIVE), a (ruleCol rule slot R_LABEL),
         a (ruleCol rule slot R_SRC), a (ruleCol rule slot R_DST)] := by
  have hb : boolInt (ruleSlotOf a rule slot).active = a (ruleCol rule slot R_ACTIVE) := by
    rcases F.bits _ (mem_bitCols_ruleActive hr hs) with h | h <;>
      simp [ruleSlotOf, boolInt, h]
  obtain ⟨hl1, hl2⟩ := F.ranges _ (mem_rangeCols_ruleLabel hr hs)
  obtain ⟨hs1, hs2⟩ := ruleVarSrc_lt F hr hs
  obtain ⟨hd1, hd2⟩ := ruleVarDst_lt F hr hs
  have e1 : (((ruleSlotOf a rule slot).label).val : Int) = a (ruleCol rule slot R_LABEL) :=
    i16_val hl1 hl2
  have e2 : (((ruleSlotOf a rule slot).src).val : Int) = a (ruleCol rule slot R_SRC) :=
    i4_val hs1 hs2
  have e3 : (((ruleSlotOf a rule slot).dst).val : Int) = a (ruleCol rule slot R_DST) :=
    i4_val hd1 hd2
  simp only [ruleSlotFields, hb, e1, e2, e3]

/-! ### public-input pins -/

theorem pin_domain : VmConstraint2.base (.piBinding VmRow.first DOMAIN 0) ∈ publicPins := by
  simp [publicPins]
theorem pin_session : VmConstraint2.base (.piBinding VmRow.first SESSION 1) ∈ publicPins := by
  simp [publicPins]
theorem pin_version : VmConstraint2.base (.piBinding VmRow.first VERSION 2) ∈ publicPins := by
  simp [publicPins]
theorem pin_shape : VmConstraint2.base (.piBinding VmRow.first SHAPE 3) ∈ publicPins := by
  simp [publicPins]

theorem pin_ruleset {lane : Nat} (h : lane < 8) :
    VmConstraint2.base (.piBinding VmRow.first (RULESET_ROOT_BASE + lane) (5 + lane))
      ∈ publicPins := by
  have hm : VmConstraint2.base
      (VmConstraint.piBinding VmRow.first (RULESET_ROOT_BASE + lane) (5 + lane)) ∈
      ((List.range 8).map fun lane => VmConstraint2.base
        (VmConstraint.piBinding VmRow.first (RULESET_ROOT_BASE + lane) (5 + lane))) :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr h, rfl⟩
  simp only [publicPins, List.mem_append]; tauto

theorem pin_old {lane : Nat} (h : lane < 8) :
    VmConstraint2.base (.piBinding VmRow.first (OLD_ROOT_BASE + lane) (13 + lane))
      ∈ publicPins := by
  have hm : VmConstraint2.base
      (VmConstraint.piBinding VmRow.first (OLD_ROOT_BASE + lane) (13 + lane)) ∈
      ((List.range 8).map fun lane => VmConstraint2.base
        (VmConstraint.piBinding VmRow.first (OLD_ROOT_BASE + lane) (13 + lane))) :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr h, rfl⟩
  simp only [publicPins, List.mem_append]; tauto

theorem pin_new {lane : Nat} (h : lane < 8) :
    VmConstraint2.base (.piBinding VmRow.first (NEW_ROOT_BASE + lane) (21 + lane))
      ∈ publicPins := by
  have hm : VmConstraint2.base
      (VmConstraint.piBinding VmRow.first (NEW_ROOT_BASE + lane) (21 + lane)) ∈
      ((List.range 8).map fun lane => VmConstraint2.base
        (VmConstraint.piBinding VmRow.first (NEW_ROOT_BASE + lane) (21 + lane))) :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr h, rfl⟩
  simp only [publicPins, List.mem_append]; tauto

/-- The public statement read off the descriptor's 29-felt PI vector. -/
def pubOf (pis : Assignment) : PublicStatement :=
  { domain := pis 0, session := pis 1, version := pis 2, shape := pis 3, index := pis 4
  , rulesetRoot := fun i => pis (5 + i.val)
  , oldRoot := fun i => pis (13 + i.val)
  , newRoot := fun i => pis (21 + i.val) }

theorem metadata_version {a : Assignment} (F : AirFacts a) : a VERSION = PROTOCOL_VERSION := by
  have hmem : eqBody (v VERSION) (c PROTOCOL_VERSION) ∈ semanticBodies :=
    mem_sem_meta (by simp [metadataBodies])
  have h := col_eq_of_gate F.canon (F.gates _ hmem)
    (by simp only [c, EmittedExpr.eval, PROTOCOL_VERSION]; norm_num)
  simpa only [c, EmittedExpr.eval] using h

theorem metadata_shape {a : Assignment} (F : AirFacts a) : a SHAPE = SHAPE_ID := by
  have hmem : eqBody (v SHAPE) (c SHAPE_ID) ∈ semanticBodies :=
    mem_sem_meta (by simp [metadataBodies])
  have h := col_eq_of_gate F.canon (F.gates _ hmem)
    (by simp only [c, EmittedExpr.eval, SHAPE_ID]; norm_num)
  simpa only [c, EmittedExpr.eval] using h

/-! ## §8 — assembly: `Satisfied2 → Accepts`. -/

theorem live_nonempty {s : Fin 2 → RuleEdgeSlot}
    (h : (s 0).active = true ∨ (s 1).active = true) : liveRuleEdges s ≠ [] := by
  rw [liveRule_two]
  rcases h with h | h
  · simp [h]
  · cases h0 : (s 0).active <;> simp [h, h0]

theorem selectedRule_mem (w : PrivateWitness) : w.selectedRule ∈ List.ofFn w.rules := by
  simp only [PrivateWitness.selectedRule]
  split
  · exact List.mem_ofFn.mpr ⟨1, rfl⟩
  · exact List.mem_ofFn.mpr ⟨0, rfl⟩

theorem source_edges_old {a : Assignment} (F : AirFacts a) :
    liveHostEdges (fun i : Fin 4 => slotOf (rawAt a OLD_STAGE_BASE 0 i))
      = liveHostEdges (fun i : Fin 2 => slotOf (rawCtxN a i.val))
        ++ (liveRuleEdges (fun k : Fin 2 => ruleSlotOf a (selR a) k.val)).map
            (mapEdge (sigmaOf a)) := by
  have h := source_edges F (base := OLD_STAGE_BASE) (rhs := false) (fun _ hb => mem_sem_srcOld hb)
  simpa using h

theorem source_edges_new {a : Assignment} (F : AirFacts a) :
    liveHostEdges (fun i : Fin 4 => slotOf (rawAt a NEW_STAGE_BASE 0 i))
      = liveHostEdges (fun i : Fin 2 => slotOf (rawCtxN a i.val))
        ++ (liveRuleEdges (fun k : Fin 2 => ruleSlotOf a (selR a) (2 + k.val))).map
            (mapEdge (sigmaOf a)) := by
  have h := source_edges F (base := NEW_STAGE_BASE) (rhs := true) (fun _ hb => mem_sem_srcNew hb)
  simpa using h

/-- The witness read straight off the padded trace columns. -/
def mkWitness (a : Assignment)
    (hpadOld : ∀ i, (slotOf (rawAt a OLD_STAGE_BASE 6 i)).canonicalPadding)
    (hpadNew : ∀ i, (slotOf (rawAt a NEW_STAGE_BASE 0 i)).canonicalPadding)
    (hpadCtx : ∀ i : Fin 2, (slotOf (rawCtxN a i.val)).canonicalPadding)
    (hpadLhs : ∀ r k : Fin 2, (ruleSlotOf a r.val k.val).canonicalPadding)
    (hpadRhs : ∀ r k : Fin 2, (ruleSlotOf a r.val (2 + k.val)).canonicalPadding) :
    PrivateWitness :=
  { oldGraph := ⟨fun i => slotOf (rawAt a OLD_STAGE_BASE 6 i), hpadOld⟩
  , newGraph := ⟨fun i => slotOf (rawAt a NEW_STAGE_BASE 0 i), hpadNew⟩
  , rules := fun r => ⟨⟨fun k => ruleSlotOf a r.val k.val, hpadLhs r⟩,
                       ⟨fun k => ruleSlotOf a r.val (2 + k.val), hpadRhs r⟩⟩
  , sigma := sigmaOf a
  , context := ⟨fun i => slotOf (rawCtxN a i.val), hpadCtx⟩
  , oldBlind := fun l => a (OLD_BLIND_BASE + l.val)
  , newBlind := fun l => a (NEW_BLIND_BASE + l.val)
  , ruleBlinds := fun r l => a (ruleBlindCol r.val l.val)
  , ruleSlot := decide (a RULE_SLOT = 1) }

theorem mkWitness_sel_lhs {a : Assignment} (h1 h2 h3 h4 h5) :
    (mkWitness a h1 h2 h3 h4 h5).selectedRule.lhs.slots
      = fun k : Fin 2 => ruleSlotOf a (selR a) k.val := by
  by_cases h : a RULE_SLOT = 1 <;>
    simp [mkWitness, PrivateWitness.selectedRule, selR, h]

theorem mkWitness_sel_rhs {a : Assignment} (h1 h2 h3 h4 h5) :
    (mkWitness a h1 h2 h3 h4 h5).selectedRule.rhs.slots
      = fun k : Fin 2 => ruleSlotOf a (selR a) (2 + k.val) := by
  by_cases h : a RULE_SLOT = 1 <;>
    simp [mkWitness, PrivateWitness.selectedRule, selR, h]

/-- **`privateGraphRewrite_sat_imp_accepts`** — the deployed private-graph-rewrite
descriptor is SOUND for its bounded semantic relation: any nonempty canonical
satisfying trace, read against a faithful four-bit range table and a sound wide
Poseidon2 chip, yields a private witness that `Accepts` the public statement
carried by the 29-felt PI vector.  Composed with `accepts_rewriteStep` this says
the committed `oldRoot`/`newRoot` endpoints really do name one injective
match-driven bounded hyperedge replacement. -/
theorem privateGraphRewrite_sat_imp_accepts
    {hash : List Int → Int} (permOut : List Int → List Int) (t : VmTrace)
    (hne : t.rows ≠ [])
    (hcanon : CanonicalAssignment (row0 t)) (hcanonPis : CanonicalAssignment t.pub)
    (hChip : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hrange : t.tf TableId.range = rangeRows 4)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t) :
    ∃ w : PrivateWitness, Accepts permOut (pubOf t.pub) w := by
  have F : AirFacts (row0 t) := airFacts_row0 hne hcanon hrange hsat
  set a := row0 t with ha
  have hsubOld : ∀ b ∈ sourceBodies OLD_STAGE_BASE false, b ∈ semanticBodies :=
    fun _ h => mem_sem_srcOld h
  have hsubNew : ∀ b ∈ sourceBodies NEW_STAGE_BASE true, b ∈ semanticBodies :=
    fun _ h => mem_sem_srcNew h
  have hok0Old : ∀ i, RawOk (rawAt a OLD_STAGE_BASE 0 i) := fun i => stage0_ok F hsubOld i
  have hok6Old : ∀ i, RawOk (rawAt a OLD_STAGE_BASE 6 i) := by
    intro i
    obtain ⟨j, hj⟩ := old_stage6_reindex F i
    rw [hj]; exact hok0Old j
  have hok0New : ∀ i, RawOk (rawAt a NEW_STAGE_BASE 0 i) := fun i => stage0_ok F hsubNew i
  have hokCtx : ∀ i : Fin 2, RawOk (rawCtxN a i.val) := fun i => rawCtxN_ok F i.isLt
  have hpadOld : ∀ i, (slotOf (rawAt a OLD_STAGE_BASE 6 i)).canonicalPadding :=
    fun i => slotOf_padding (hok6Old i)
  have hpadNew : ∀ i, (slotOf (rawAt a NEW_STAGE_BASE 0 i)).canonicalPadding :=
    fun i => slotOf_padding (hok0New i)
  have hpadCtx : ∀ i : Fin 2, (slotOf (rawCtxN a i.val)).canonicalPadding :=
    fun i => slotOf_padding (hokCtx i)
  have hpadLhs : ∀ r k : Fin 2, (ruleSlotOf a r.val k.val).canonicalPadding := by
    intro r k
    exact ruleSlotOf_pad F r.isLt (by have := k.isLt; omega)
  have hpadRhs : ∀ r k : Fin 2, (ruleSlotOf a r.val (2 + k.val)).canonicalPadding := by
    intro r k
    exact ruleSlotOf_pad F r.isLt (by have := k.isLt; omega)
  -- public-input pins
  have pinDom : a DOMAIN = t.pub 0 := pins_row0 hne hcanon hcanonPis hsat pin_domain
  have pinSes : a SESSION = t.pub 1 := pins_row0 hne hcanon hcanonPis hsat pin_session
  have pinVer : a VERSION = t.pub 2 := pins_row0 hne hcanon hcanonPis hsat pin_version
  have pinShp : a SHAPE = t.pub 3 := pins_row0 hne hcanon hcanonPis hsat pin_shape
  have pinRs : ∀ l : Fin 8, a (RULESET_ROOT_BASE + l.val) = t.pub (5 + l.val) :=
    fun l => pins_row0 hne hcanon hcanonPis hsat (pin_ruleset l.isLt)
  have pinOldR : ∀ l : Fin 8, a (OLD_ROOT_BASE + l.val) = t.pub (13 + l.val) :=
    fun l => pins_row0 hne hcanon hcanonPis hsat (pin_old l.isLt)
  have pinNewR : ∀ l : Fin 8, a (NEW_ROOT_BASE + l.val) = t.pub (21 + l.val) :=
    fun l => pins_row0 hne hcanon hcanonPis hsat (pin_new l.isLt)
  -- the nine wide chip outputs
  have hOldCore : permOut ((stageFieldExprs OLD_STAGE_BASE 6).map (fun e => e.eval a))
      = [a (OLD_CORE_BASE + 0), a (OLD_CORE_BASE + 1), a (OLD_CORE_BASE + 2),
         a (OLD_CORE_BASE + 3), a (OLD_CORE_BASE + 4), a (OLD_CORE_BASE + 5),
         a (OLD_CORE_BASE + 6), a (OLD_CORE_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_stageFieldExprs _ _))
      (by simp [hashLookups, graphCoreLookup])).symm.trans (outCols_map a OLD_CORE_BASE)
  have hNewCore : permOut ((stageFieldExprs NEW_STAGE_BASE 0).map (fun e => e.eval a))
      = [a (NEW_CORE_BASE + 0), a (NEW_CORE_BASE + 1), a (NEW_CORE_BASE + 2),
         a (NEW_CORE_BASE + 3), a (NEW_CORE_BASE + 4), a (NEW_CORE_BASE + 5),
         a (NEW_CORE_BASE + 6), a (NEW_CORE_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_stageFieldExprs _ _))
      (by simp [hashLookups, graphCoreLookup])).symm.trans (outCols_map a NEW_CORE_BASE)
  have hOldRoot : permOut ((graphRootInputExprs OLD_CORE_BASE OLD_BLIND_BASE
        GRAPH_STATE_TAG).map (fun e => e.eval a))
      = [a (OLD_ROOT_BASE + 0), a (OLD_ROOT_BASE + 1), a (OLD_ROOT_BASE + 2),
         a (OLD_ROOT_BASE + 3), a (OLD_ROOT_BASE + 4), a (OLD_ROOT_BASE + 5),
         a (OLD_ROOT_BASE + 6), a (OLD_ROOT_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_graphRootInputExprs _ _ _))
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a OLD_ROOT_BASE)
  have hNewRoot : permOut ((graphRootInputExprs NEW_CORE_BASE NEW_BLIND_BASE
        GRAPH_STATE_TAG).map (fun e => e.eval a))
      = [a (NEW_ROOT_BASE + 0), a (NEW_ROOT_BASE + 1), a (NEW_ROOT_BASE + 2),
         a (NEW_ROOT_BASE + 3), a (NEW_ROOT_BASE + 4), a (NEW_ROOT_BASE + 5),
         a (NEW_ROOT_BASE + 6), a (NEW_ROOT_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_graphRootInputExprs _ _ _))
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a NEW_ROOT_BASE)
  have hR0Core : permOut ((ruleFieldExprs 0).map (fun e => e.eval a))
      = [a (RULE0_CORE_BASE + 0), a (RULE0_CORE_BASE + 1), a (RULE0_CORE_BASE + 2),
         a (RULE0_CORE_BASE + 3), a (RULE0_CORE_BASE + 4), a (RULE0_CORE_BASE + 5),
         a (RULE0_CORE_BASE + 6), a (RULE0_CORE_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_ruleFieldExprs _))
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a RULE0_CORE_BASE)
  have hR1Core : permOut ((ruleFieldExprs 1).map (fun e => e.eval a))
      = [a (RULE1_CORE_BASE + 0), a (RULE1_CORE_BASE + 1), a (RULE1_CORE_BASE + 2),
         a (RULE1_CORE_BASE + 3), a (RULE1_CORE_BASE + 4), a (RULE1_CORE_BASE + 5),
         a (RULE1_CORE_BASE + 6), a (RULE1_CORE_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_ruleFieldExprs _))
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a RULE1_CORE_BASE)
  have hR0Leaf : permOut ((ruleLeafInputExprs RULE0_CORE_BASE 0).map (fun e => e.eval a))
      = [a (RULE0_LEAF_BASE + 0), a (RULE0_LEAF_BASE + 1), a (RULE0_LEAF_BASE + 2),
         a (RULE0_LEAF_BASE + 3), a (RULE0_LEAF_BASE + 4), a (RULE0_LEAF_BASE + 5),
         a (RULE0_LEAF_BASE + 6), a (RULE0_LEAF_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_ruleLeafInputExprs _ _))
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a RULE0_LEAF_BASE)
  have hR1Leaf : permOut ((ruleLeafInputExprs RULE1_CORE_BASE 1).map (fun e => e.eval a))
      = [a (RULE1_LEAF_BASE + 0), a (RULE1_LEAF_BASE + 1), a (RULE1_LEAF_BASE + 2),
         a (RULE1_LEAF_BASE + 3), a (RULE1_LEAF_BASE + 4), a (RULE1_LEAF_BASE + 5),
         a (RULE1_LEAF_BASE + 6), a (RULE1_LEAF_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq (len_ruleLeafInputExprs _ _))
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a RULE1_LEAF_BASE)
  have hRsRoot : permOut (rulesetInputExprs.map (fun e => e.eval a))
      = [a (RULESET_ROOT_BASE + 0), a (RULESET_ROOT_BASE + 1), a (RULESET_ROOT_BASE + 2),
         a (RULESET_ROOT_BASE + 3), a (RULESET_ROOT_BASE + 4), a (RULESET_ROOT_BASE + 5),
         a (RULESET_ROOT_BASE + 6), a (RULESET_ROOT_BASE + 7)] :=
    (wide_hash_row0 hne permOut hChip hsat (le_of_eq len_rulesetInputExprs)
      (by simp [hashLookups, hashLookup])).symm.trans (outCols_map a RULESET_ROOT_BASE)
  set W : PrivateWitness := mkWitness a hpadOld hpadNew hpadCtx hpadLhs hpadRhs with hW
  refine ⟨W, ?_⟩
  -- graph cores
  have hOldCoreIn : graphCoreInputs W.oldGraph
      = (stageFieldExprs OLD_STAGE_BASE 6).map (fun e => e.eval a) := by
    rw [hW]; exact core_eq_stageFields hpadOld hok6Old
  have hNewCoreIn : graphCoreInputs W.newGraph
      = (stageFieldExprs NEW_STAGE_BASE 0).map (fun e => e.eval a) := by
    rw [hW]; exact core_eq_stageFields hpadNew hok0New
  have hOldCoreDig : digest8 permOut (graphCoreInputs W.oldGraph)
      = fun i => a (OLD_CORE_BASE + i.val) := by
    rw [hOldCoreIn]; exact digest8_cols hOldCore
  have hNewCoreDig : digest8 permOut (graphCoreInputs W.newGraph)
      = fun i => a (NEW_CORE_BASE + i.val) := by
    rw [hNewCoreIn]; exact digest8_cols hNewCore
  -- rule cores
  have hRC0 : ruleCoreInputs (W.rules 0) = (ruleFieldExprs 0).map (fun e => e.eval a) := by
    have hexp : ruleCoreInputs (W.rules 0)
        = ruleSlotFields (ruleSlotOf a 0 0) ++ ruleSlotFields (ruleSlotOf a 0 1)
          ++ (ruleSlotFields (ruleSlotOf a 0 2) ++ ruleSlotFields (ruleSlotOf a 0 3)) := by
      rw [hW]; rfl
    rw [hexp, ruleFieldExprs_eval,
      ruleSlotFields_eq F (rule := 0) (slot := 0) (by norm_num) (by norm_num),
      ruleSlotFields_eq F (rule := 0) (slot := 1) (by norm_num) (by norm_num),
      ruleSlotFields_eq F (rule := 0) (slot := 2) (by norm_num) (by norm_num),
      ruleSlotFields_eq F (rule := 0) (slot := 3) (by norm_num) (by norm_num)]
    rfl
  have hRC1 : ruleCoreInputs (W.rules 1) = (ruleFieldExprs 1).map (fun e => e.eval a) := by
    have hexp : ruleCoreInputs (W.rules 1)
        = ruleSlotFields (ruleSlotOf a 1 0) ++ ruleSlotFields (ruleSlotOf a 1 1)
          ++ (ruleSlotFields (ruleSlotOf a 1 2) ++ ruleSlotFields (ruleSlotOf a 1 3)) := by
      rw [hW]; rfl
    rw [hexp, ruleFieldExprs_eval,
      ruleSlotFields_eq F (rule := 1) (slot := 0) (by norm_num) (by norm_num),
      ruleSlotFields_eq F (rule := 1) (slot := 1) (by norm_num) (by norm_num),
      ruleSlotFields_eq F (rule := 1) (slot := 2) (by norm_num) (by norm_num),
      ruleSlotFields_eq F (rule := 1) (slot := 3) (by norm_num) (by norm_num)]
    rfl
  have hLeaf0 : ruleLeafDigest permOut (pubOf t.pub) W 0
      = fun i => a (RULE0_LEAF_BASE + i.val) := by
    show digest8 permOut (ruleLeafInputs (digest8 permOut (ruleCoreInputs (W.rules 0)))
      (W.ruleBlinds 0) (t.pub 0) (t.pub 2) (t.pub 3) ((0 : Fin 2).val)) = _
    rw [hRC0, digest8_cols hR0Core]
    have hpre : ruleLeafInputs (fun i => a (RULE0_CORE_BASE + i.val)) (W.ruleBlinds 0)
        (t.pub 0) (t.pub 2) (t.pub 3) ((0 : Fin 2).val)
        = (ruleLeafInputExprs RULE0_CORE_BASE 0).map (fun e => e.eval a) := by
      rw [ruleLeafInputExprs_eval, pinDom, pinVer, pinShp, hW]
      rfl
    rw [hpre]
    exact digest8_cols hR0Leaf
  have hLeaf1 : ruleLeafDigest permOut (pubOf t.pub) W 1
      = fun i => a (RULE1_LEAF_BASE + i.val) := by
    show digest8 permOut (ruleLeafInputs (digest8 permOut (ruleCoreInputs (W.rules 1)))
      (W.ruleBlinds 1) (t.pub 0) (t.pub 2) (t.pub 3) ((1 : Fin 2).val)) = _
    rw [hRC1, digest8_cols hR1Core]
    have hpre : ruleLeafInputs (fun i => a (RULE1_CORE_BASE + i.val)) (W.ruleBlinds 1)
        (t.pub 0) (t.pub 2) (t.pub 3) ((1 : Fin 2).val)
        = (ruleLeafInputExprs RULE1_CORE_BASE 1).map (fun e => e.eval a) := by
      rw [ruleLeafInputExprs_eval, pinDom, pinVer, pinShp, hW]
      rfl
    rw [hpre]
    exact digest8_cols hR1Leaf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show t.pub 2 = PROTOCOL_VERSION
    rw [← pinVer]; exact metadata_version F
  · show t.pub 3 = SHAPE_ID
    rw [← pinShp]; exact metadata_shape F
  · intro i; rw [hW]; exact F.canon _
  · intro i; rw [hW]; exact F.canon _
  · intro slot i; rw [hW]; exact F.canon _
  · -- the bounded step
    refine ⟨selectedRule_mem W, ?_, ?_, ?_, ?_⟩
    · rw [hW]; exact sigmaOf_injective F
    · rw [hW, mkWitness_sel_lhs]
      refine live_nonempty ?_
      rcases lhs_active F with h | h
      · left
        show decide (a (ruleCol (selR a) 0 R_ACTIVE) = 1) = true
        rw [h]; simp
      · right
        show decide (a (ruleCol (selR a) 1 R_ACTIVE) = 1) = true
        rw [h]; simp
    · show (liveHostEdges (fun i : Fin 4 => slotOf (rawAt a OLD_STAGE_BASE 6 i))).Perm
        (liveHostEdges (fun i : Fin 2 => slotOf (rawCtxN a i.val))
          ++ (liveRuleEdges W.selectedRule.lhs.slots).map (mapEdge (sigmaOf a)))
      rw [hW, mkWitness_sel_lhs, ← source_edges_old F]
      exact old_edges_perm F
    · show liveHostEdges (fun i : Fin 4 => slotOf (rawAt a NEW_STAGE_BASE 0 i))
        = liveHostEdges (fun i : Fin 2 => slotOf (rawCtxN a i.val))
          ++ (liveRuleEdges W.selectedRule.rhs.slots).map (mapEdge (sigmaOf a))
      rw [hW, mkWitness_sel_rhs]
      exact source_edges_new F
  · -- old root
    have hpre : graphRootInputs (digest8 permOut (graphCoreInputs W.oldGraph)) W.oldBlind
        (t.pub 0) (t.pub 1) (t.pub 2) GRAPH_STATE_TAG
        = (graphRootInputExprs OLD_CORE_BASE OLD_BLIND_BASE GRAPH_STATE_TAG).map
            (fun e => e.eval a) := by
      rw [hOldCoreDig, graphRootInputExprs_eval, pinDom, pinSes, pinVer, hW]
      rfl
    show (fun i : Fin 8 => t.pub (13 + i.val)) = digest8 permOut
      (graphRootInputs (digest8 permOut (graphCoreInputs W.oldGraph)) W.oldBlind
        (t.pub 0) (t.pub 1) (t.pub 2) GRAPH_STATE_TAG)
    rw [hpre, digest8_cols hOldRoot]
    funext i
    rw [pinOldR i]
  · -- new root
    have hpre : graphRootInputs (digest8 permOut (graphCoreInputs W.newGraph)) W.newBlind
        (t.pub 0) (t.pub 1) (t.pub 2) GRAPH_STATE_TAG
        = (graphRootInputExprs NEW_CORE_BASE NEW_BLIND_BASE GRAPH_STATE_TAG).map
            (fun e => e.eval a) := by
      rw [hNewCoreDig, graphRootInputExprs_eval, pinDom, pinSes, pinVer, hW]
      rfl
    show (fun i : Fin 8 => t.pub (21 + i.val)) = digest8 permOut
      (graphRootInputs (digest8 permOut (graphCoreInputs W.newGraph)) W.newBlind
        (t.pub 0) (t.pub 1) (t.pub 2) GRAPH_STATE_TAG)
    rw [hpre, digest8_cols hNewRoot]
    funext i
    rw [pinNewR i]
  · -- ruleset root
    have hpre : rulesetNodeInputs (ruleLeafDigest permOut (pubOf t.pub) W 0)
        (ruleLeafDigest permOut (pubOf t.pub) W 1)
        = rulesetInputExprs.map (fun e => e.eval a) := by
      rw [hLeaf0, hLeaf1, rulesetInputExprs_eval]
    show (fun i : Fin 8 => t.pub (5 + i.val)) = _
    rw [hpre, digest8_cols hRsRoot]
    funext i
    rw [pinRs i]

/-- The consequence the history protocol's `sound` field consumes: a satisfying
trace of the DEPLOYED descriptor exhibits a witness whose committed old/new roots
open to graphs related by a genuine generic `RewriteStep`, matched by an INJECTIVE
subgraph embedding of the selected rule's left-hand side. -/
theorem privateGraphRewrite_sat_imp_rewriteStep
    {hash : List Int → Int} (permOut : List Int → List Int) (t : VmTrace)
    (hne : t.rows ≠ [])
    (hcanon : CanonicalAssignment (row0 t)) (hcanonPis : CanonicalAssignment t.pub)
    (hChip : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hrange : t.tf TableId.range = rangeRows 4)
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 [] t) :
    ∃ w : PrivateWitness,
      Accepts permOut (pubOf t.pub) w ∧
      RewriteStep ((List.ofFn w.rules).map BoundedRule.toRule)
        w.oldGraph.toHypergraph w.newGraph.toHypergraph ∧
      Embeds w.selectedRule.lhs.toHypergraph w.oldGraph.toHypergraph := by
  obtain ⟨w, hw⟩ := privateGraphRewrite_sat_imp_accepts permOut t hne hcanon hcanonPis
    hChip hrange hsat
  exact ⟨w, hw, accepts_rewriteStep hw, accepts_embeds hw⟩

#assert_all_clean [
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.gates_row0,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.pins_row0,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.ranges_row0,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.bits_row0,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.wide_hash_row0,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.airFacts_row0,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.swap_col_eq,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.old_stage_step,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.old_stage6_perm,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.old_stage6_reindex,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.old_edges_perm,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.source_edges,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.source_edges_old,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.source_edges_new,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.sigmaOf_injective,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.lhs_active,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.privateGraphRewrite_sat_imp_accepts,
  Dregg2.Crypto.PrivateGraphRewriteAirBridge.privateGraphRewrite_sat_imp_rewriteStep]

end Dregg2.Crypto.PrivateGraphRewriteAirBridge
