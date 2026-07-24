/-
# Dregg2.Circuit.PeepholeBatchCertified — CLOSING THE PEEPHOLE: the whole pilot spine
lowered in ONE certified pass, measured on its OWN output.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. The source descriptor is the one the Lean
compiler emits, `descriptor FieldDeltaRangePilot.prog` (374 constraints / 280 columns). The target
is a record-UPDATE of that SAME `EffectVmDescriptor2` value with its constraint list replaced by the
fully-lowered spine — 3 public pins, 2 R1 raw-affine gates, 30 R2 pair gates — at the SAME raw-input
columns. Nothing here is a separately reconstructed look-alike descriptor.

## What this closes — the ITERATION wall named by the R1/R2 single-site certs

`PeepholePassCertified` (R1) and `PeepholeR2Certified` (R2) each certified ONE site, but the pilot's
source is `atom0 ∧ atom1 ∧ ⋀_{j<30}(b_j=0 ∨ b_j=1)`: a 32-conjunct spine. Their single-site passes
fire on `descriptor (rootProgram …)` and, after the first fire, the constraint list stops matching
`descriptor p'`, so the 32 fires never composed. Parity (35/33/30) therefore stayed on a HAND-BUILT
`loweredDescriptor`, not on any certified pass output.

This module resolves it by BATCHING. `batchPeephole` rewrites ALL R1 sites (both asserted affine
equalities → one degree-1 raw gate each) AND ALL R2 sites (all thirty booleanity disjunctions → one
degree-2 pair gate each) AT ONCE, eliding the entire materialized Boolean graph and every atom
column. It is proved a genuine `SatisfiabilityPreservation` (security + completeness) against
`descriptor prog`, and composed with the certified E1 dead-column deletion:

    certifiedPeephole = batchPeephole  then  E1.

THE DELIVERABLE: `certifiedPeephole (descriptor prog)` has traceWidth 33, 35 constraints, 30
nonlinear multiplications — the SAME 35/33/30 the hand emit carries — and the object those numbers
are MEASURED on is the object the preservation legs are PROVED for. No `loweredDescriptor` in the
loop.

## How the whole-spine security leg closes without per-site iteration

The batch elides the ENTIRE graph, so the security rebuild does not have to preserve any surviving
graph structure (the wall single-site R1/R2 fought). `toSource` maps every row to the compiler's own
`canonicalRow prog (rawInput of that row)`; the reusable `canonical_atom_link_holds`,
`canonical_nodes_hold`, `canonical_accept_holds` then discharge every atom-link / graph / accept
constraint of `descriptor prog` verbatim. The only new semantic content is the bridge
`pilot_holds_iff`: the pilot source `Holds` iff the two affine residuals vanish and every bit is
Boolean — exactly what the 32 raw gates assert. Completeness runs the same bridge the other way off
the compiler's own `sound`.

## Named residuals (no `sorry`, no stand-in)

* The E1 composition takes `transitionCeilingOk (batchDescriptor) floor = true` as an explicit
  decidable hypothesis, exactly as the R1 and R2 modules' compositions do.
* Byte-identity with the hand emit is NOT claimed: the lowered pair body is `(x+0)(x+(-1))` (a `+0`
  factor a constant-fold pass removes) and E1 renumbers the surviving raw columns [62,95) down to
  [0,33); the COST metric (35/33/30) is what is proved equal, on the certified object.

Standalone and additive: imports R1 (reusable lemmas), R2's rule, the pilot, and the contracts;
changes none of them.
-/
import Dregg2.Circuit.PeepholePassCertified
import Dregg2.Circuit.PeepholeR2Certified
import Dregg2.Circuit.PeepholeBooleanityRule
import Dregg2.Crypto.Arith.FieldDeltaRangePilot

namespace Dregg2.Circuit.PeepholeBatchCertified

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (Wire Node witnessCount outputAt nodesAt gate bitBody subW negW fieldWindow fieldAssignment
   fieldWire fieldWire_expr fieldWindow_eq_cast field_zero_of_gate graph_of_node_constraints
   node_constraint_degree formula_holds_congr)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Crypto.Arith.FieldDeltaRangePilot
  (transitionTerm recomposeTerm bitC atomTerms atomList source prog boolAtom andAll oldC deltaC newC)
open Dregg2.Circuit.PeepholeBooleanityRule (peelConst pairBody pairGate pairGate_iff_or
  pairBody_zero_iff nonlinearMuls)
open Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula (Holds graphEval_iff_holds)

set_option autoImplicit false

/-! ## 1. The pilot semantic bridge: `prog.Holds` unfolds to the 32 gate facts.

`prog.source` is a right-nested 32-conjunct spine; recovering the per-conjunct obligations is a
general `andAll` unfold, plus the atom-registry indexing that identifies the `j`-th booleanity pair
with the concrete pilot terms `b_j` and `b_j − 1`. -/

/-- `Holds` of a right-nested `andAll` conjunction is the conjunction of `Holds` over its list. -/
theorem holds_andAll (truth : Fin 62 → Prop) (l : List (Formula 62)) :
    Holds truth (andAll l) ↔ ∀ f ∈ l, Holds truth f := by
  induction l with
  | nil => simp [andAll, Holds]
  | cons p ps ih =>
      cases ps with
      | nil => simp [andAll]
      | cons q qs =>
          simp only [andAll, Holds, List.forall_mem_cons, ih]

/-- Atom-registry indexing: the `j`-th booleanity pair's two atom terms ARE `b_j` and `b_j − 1`. -/
theorem atomTerms_bool (j : Fin 30) :
    atomTerms ⟨2 + 2 * j.val, by have := j.isLt; omega⟩ = .input (bitC j) ∧
    atomTerms ⟨3 + 2 * j.val, by have := j.isLt; omega⟩ = AffineTerm.eqConst (bitC j) 1 := by
  fin_cases j <;> exact ⟨rfl, rfl⟩

theorem atomTerms_zero : atomTerms ⟨0, by omega⟩ = transitionTerm := rfl
theorem atomTerms_one : atomTerms ⟨1, by omega⟩ = recomposeTerm := rfl

/-- THE BRIDGE. The pilot source `Holds` exactly when the two affine residuals vanish and every bit
is Boolean — the exact content of the 32 raw gates the batch emits. -/
theorem pilot_holds_iff (input : Fin 33 → BabyBear) :
    prog.Holds input ↔
      (transitionTerm.evalField input = 0 ∧
       recomposeTerm.evalField input = 0 ∧
       ∀ j : Fin 30, (AffineTerm.input (bitC j)).evalField input = 0 ∨
         (AffineTerm.eqConst (bitC j) 1).evalField input = 0) := by
  unfold Program.Holds
  show Holds (prog.AtomTruth input) prog.source ↔ _
  have hsrc : prog.source = andAll
      (([.atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩] : List (Formula 62)) ++
        (List.finRange 30).map boolAtom) := rfl
  rw [hsrc, holds_andAll]
  have hmem0 : ((.atom ⟨0, by omega⟩ : Formula 62)) ∈
      (([.atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩] : List (Formula 62)) ++
        (List.finRange 30).map boolAtom) := by simp
  have hmem1 : ((.atom ⟨1, by omega⟩ : Formula 62)) ∈
      (([.atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩] : List (Formula 62)) ++
        (List.finRange 30).map boolAtom) := by simp
  have hmemb : ∀ j : Fin 30, boolAtom j ∈
      (([.atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩] : List (Formula 62)) ++
        (List.finRange 30).map boolAtom) := fun j =>
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange j))
  constructor
  · intro h
    refine ⟨h _ hmem0, h _ hmem1, fun j => ?_⟩
    have hj := h _ (hmemb j)
    simp only [boolAtom, Holds, Program.AtomTruth, prog] at hj
    obtain ⟨he0, he1⟩ := atomTerms_bool j
    rcases hj with hx | hx
    · exact Or.inl (by rw [← he0]; exact hx)
    · exact Or.inr (by rw [← he1]; exact hx)
  · rintro ⟨h0, h1, hb⟩ f hf
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      List.mem_map, List.mem_finRange, true_and] at hf
    rcases hf with (rfl | rfl) | ⟨j, rfl⟩
    · exact h0
    · exact h1
    · simp only [boolAtom, Holds, Program.AtomTruth, prog]
      obtain ⟨he0, he1⟩ := atomTerms_bool j
      rcases hb j with hx | hx
      · exact Or.inl (by rw [he0]; exact hx)
      · exact Or.inr (by rw [he1]; exact hx)

/-! ## 2. The batch-lowered descriptor — every R1 and R2 site fired at once.

The 32 raw gates live at the SAME raw-input base `rawBase 62` as the source descriptor: the two
asserted affine equalities become one degree-1 gate each, the thirty booleanity disjunctions one
degree-2 pair gate each. The trace width is untouched (a record-update); E1 later deletes the now
dead atom and witness columns. -/

open Dregg2.Circuit.PeepholeR2Certified (field_of_src_gate gate_holds_any)

/-- R1's raw replacement for the transition zero-test: the direct affine gate. -/
def rawTransitionGate : VmConstraint2 := gate (transitionTerm.toWindowAt (rawBase 62))

/-- R1's raw replacement for the recomposition zero-test. -/
def rawRecomposeGate : VmConstraint2 := gate (recomposeTerm.toWindowAt (rawBase 62))

/-- R2's raw replacement for the `j`-th booleanity disjunction: `(b_j+0)(b_j-1) = 0`. -/
def rawPairGate (j : Fin 30) : VmConstraint2 :=
  pairGate (rawBase 62) (.input (bitC j)) 0 (-1)

def batchConstraints : List VmConstraint2 :=
  publicPins 3 30 62 ++ [rawTransitionGate, rawRecomposeGate] ++
    (List.finRange 30).map rawPairGate

/-- THE BATCH-REWRITTEN DESCRIPTOR — `descriptor prog` with only its constraint list rewritten. -/
def batchDescriptor : EffectVmDescriptor2 :=
  { descriptor prog with constraints := batchConstraints }

/-- The row's raw-input valuation (the compiler's `rowInput`, per row). -/
noncomputable def rowInputAt (env : VmRowEnv) : Fin 33 → BabyBear :=
  fun i => fieldAssignment env.loc (rawBase 62 + i.val)

/-! ### The gate bridges: each batch gate holds exactly when its semantic fact does. -/

theorem gate_field_iff {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv}
    {f l : Bool} {body : WindowExpr} :
    (gate body).holdsAt hash tf env f l ↔ fieldWindow env body = 0 :=
  ⟨field_of_src_gate, gate_holds_any hash tf env f l⟩

theorem transitionGate_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool) :
    rawTransitionGate.holdsAt hash tf env f l ↔ transitionTerm.evalField (rowInputAt env) = 0 := by
  rw [rawTransitionGate, gate_field_iff, AffineTerm.fieldWindow_toWindowAt]; rfl

theorem recomposeGate_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool) :
    rawRecomposeGate.holdsAt hash tf env f l ↔ recomposeTerm.evalField (rowInputAt env) = 0 := by
  rw [rawRecomposeGate, gate_field_iff, AffineTerm.fieldWindow_toWindowAt]; rfl

theorem pairGate_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (j : Fin 30) :
    (rawPairGate j).holdsAt hash tf env f l ↔
      (AffineTerm.input (bitC j)).evalField (rowInputAt env) = 0 ∨
        (AffineTerm.eqConst (bitC j) 1).evalField (rowInputAt env) = 0 := by
  rw [rawPairGate, pairGate, gate_field_iff]
  exact pairGate_iff_or env (rawBase 62) (.input (bitC j)) (AffineTerm.eqConst (bitC j) 1) rfl

/-! ## 3. Carrier bookkeeping and the env-level semantic connectors. -/

open Dregg2.Circuit.PeepholeR2Certified (gate_holds_iff)

theorem memOps_batch_nil : memOpsOf batchDescriptor = [] := by
  simp only [memOpsOf, batchDescriptor, batchConstraints, List.filterMap_append,
    List.filterMap_map, publicPins, rawTransitionGate, rawRecomposeGate, rawPairGate, pairGate,
    gate, List.filterMap_cons, List.filterMap_nil, List.map_map, List.map_cons, List.map_nil]
  rfl

theorem mapOps_batch_nil : mapOpsOf batchDescriptor = [] := by
  simp only [mapOpsOf, batchDescriptor, batchConstraints, List.filterMap_append,
    List.filterMap_map, publicPins, rawTransitionGate, rawRecomposeGate, rawPairGate, pairGate,
    gate, List.filterMap_cons, List.filterMap_nil, List.map_map, List.map_cons, List.map_nil]
  rfl

/-- Public ABI: the batch moves no PI binding — both descriptors carry exactly the public pins'
slots. -/
theorem gate_slot_none (b : WindowExpr) : bindingSlot? (gate b) = none := rfl

theorem publicBindingSlots_descriptor {pub sec atoms : Nat} (p : Program pub sec atoms) :
    publicBindingSlots (descriptor p) = (publicPins pub sec atoms).filterMap bindingSlot? := by
  simp only [publicBindingSlots, descriptor, List.filterMap_append]
  have h1 : (atomLinks p).filterMap bindingSlot? = [] := by
    rw [List.filterMap_eq_nil_iff]; intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hc; exact gate_slot_none _
  have h2 : (graphConstraintsAt p).filterMap bindingSlot? = [] := by
    rw [List.filterMap_eq_nil_iff]; intro c hc
    simp only [graphConstraintsAt, List.mem_flatMap] at hc
    obtain ⟨node, _, hcn⟩ := hc
    obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hcn
    exact gate_slot_none _
  have h3 : [acceptConstraintAt p].filterMap bindingSlot? = [] := by
    simp [acceptConstraintAt, gate_slot_none]
  rw [h1, h2, h3]; simp

theorem publicBindingSlots_batch :
    publicBindingSlots batchDescriptor = publicBindingSlots (descriptor prog) := by
  rw [publicBindingSlots_descriptor]
  simp only [publicBindingSlots, batchDescriptor, batchConstraints, List.filterMap_append]
  have h1 : [rawTransitionGate, rawRecomposeGate].filterMap bindingSlot? = [] := by
    simp [rawTransitionGate, rawRecomposeGate, gate_slot_none]
  have h2 : ((List.finRange 30).map rawPairGate).filterMap bindingSlot? = [] := by
    rw [List.filterMap_eq_nil_iff]; intro c hc
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hc
    rw [rawPairGate, pairGate]; exact gate_slot_none _
  rw [h1, h2]; simp

/-- ENV-LEVEL EXTRACTION (the compiler's `sound`, generalized off row 0 to any environment on which
every `descriptor p` constraint holds). -/
theorem holds_of_env {pub sec atoms : Nat} (p : Program pub sec atoms)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (h : ∀ c ∈ (descriptor p).constraints, c.holdsAt hash tf env f l) :
    p.Holds (fun i => fieldAssignment env.loc (rawBase atoms + i.val)) := by
  have hnodes : ∀ node ∈ nodesAt (boolBase pub sec atoms) p.source, Node.HoldsAt env node := by
    intro node hn c hc
    have hmem := graph_node_constraint_mem p node hn c hc
    obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hc
    exact (gate_holds_iff hash (fun _ => 0) tf (fun _ => []) env f l false true body).mp
      (h _ hmem)
  have hgraph := graph_of_node_constraints env (boolBase pub sec atoms) p.source hnodes
  have hout : fieldWire env.loc (outputAt (boolBase pub sec atoms) p.source) = 1 := by
    have hz := field_of_src_gate (h (acceptConstraintAt p) (by simp [descriptor]))
    simp only [acceptConstraintAt, subW, negW, fieldWindow] at hz
    rw [fieldWire_expr] at hz
    linear_combination hz
  have heval := (Dregg2.Logic.BoolGraph.graph_sound hgraph).2.mp hout
  have hrow : Holds
      (fun a : Fin atoms => fieldAssignment env.loc a.val = 0) p.source :=
    (graphEval_iff_holds
      (fun a : Fin atoms => fieldAssignment env.loc a.val) p.source).mp heval
  refine (formula_holds_congr _ _ (fun a => ?_) p.source).mp hrow
  have hlink := field_of_src_gate (h (atomLink p a) (atom_link_mem p a))
  simp only [atomLinkBody, subW, negW, fieldWindow] at hlink
  rw [AffineTerm.fieldWindow_toWindowAt] at hlink
  simp only [Program.AtomTruth]
  have heq : fieldAssignment env.loc a.val
      = (p.atomTerms a).evalField (fun i => fieldAssignment env.loc (rawBase atoms + i.val)) := by
    linear_combination hlink
  rw [heq]

/-- The 32 raw gates hold on `env` exactly when the pilot source `Holds` the row's raw inputs. -/
theorem batchGates_iff_holds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool) :
    (rawTransitionGate.holdsAt hash tf env f l ∧ rawRecomposeGate.holdsAt hash tf env f l ∧
      ∀ j : Fin 30, (rawPairGate j).holdsAt hash tf env f l) ↔ prog.Holds (rowInputAt env) := by
  rw [pilot_holds_iff, transitionGate_iff, recomposeGate_iff]
  constructor
  · rintro ⟨ht, hr, hp⟩
    exact ⟨ht, hr, fun j => (pairGate_iff hash tf env f l j).1 (hp j)⟩
  · rintro ⟨ht, hr, hp⟩
    exact ⟨ht, hr, fun j => (pairGate_iff hash tf env f l j).2 (hp j)⟩

/-! ## 4. The witness rebuild and the two contract legs.

`toSource` sends every row to the compiler's own canonical postorder witness of the WHOLE source
(atom residuals, every zero-test out/inv, every disjunction and conjunction bit) on that row's raw
inputs — the entire elided graph, restored at once. -/

/-- Membership plumbing for the batch constraints. -/
theorem rawTransition_mem : rawTransitionGate ∈ batchDescriptor.constraints := by
  simp [batchDescriptor, batchConstraints]

theorem rawRecompose_mem : rawRecomposeGate ∈ batchDescriptor.constraints := by
  simp [batchDescriptor, batchConstraints]

theorem rawPair_mem (j : Fin 30) : rawPairGate j ∈ batchDescriptor.constraints := by
  simp only [batchDescriptor, batchConstraints, List.mem_append]
  exact Or.inr (List.mem_map_of_mem (List.mem_finRange j))

theorem pin_mem_batch {i : Nat} (hi : i < 3) :
    (VmConstraint2.base (.piBinding .first (rawBase 62 + i) i)) ∈ batchDescriptor.constraints := by
  simp only [batchDescriptor, batchConstraints, List.mem_append]
  exact Or.inl (Or.inl (by simp [publicPins, List.mem_map, List.mem_range, hi]))

noncomputable def batchRebuildRow (row : Assignment) : Assignment :=
  canonicalRow prog (fun i => fieldAssignment row (rawBase 62 + i.val))

noncomputable def batchRebuildTrace (t : VmTrace) : VmTrace :=
  { rows := t.rows.map batchRebuildRow, pub := t.pub, tf := t.tf }

theorem batchRebuildTrace_rows_length (t : VmTrace) :
    (batchRebuildTrace t).rows.length = t.rows.length := by simp [batchRebuildTrace]

theorem batchRebuildTrace_loc (t : VmTrace) (i : Nat) (h : i < t.rows.length) :
    (envAt (batchRebuildTrace t) i).loc = batchRebuildRow ((envAt t i).loc) := by
  simp only [envAt, batchRebuildTrace]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

/-- The rebuilt row's field values ARE the compiler's canonical field row on the raw inputs. -/
theorem fa_rebuild (t : VmTrace) (i : Nat) (h : i < t.rows.length) (c : Nat) :
    fieldAssignment (envAt (batchRebuildTrace t) i).loc c =
      canonicalFieldRow prog (rowInputAt (envAt t i)) c := by
  rw [batchRebuildTrace_loc t i h, batchRebuildRow, fieldAssignment_canonicalRow]; rfl

/-- THE SECURITY LEG, per row: every `descriptor prog` constraint holds on the rebuilt row. The
graph and accept are discharged by the compiler's own field-valid postorder witness; the atom links
by the residual definition; the pins by raw-column field-equality with the accepting batch trace. -/
theorem batch_security_row (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hsat : Satisfied2 hash batchDescriptor minit mfin maddrs t)
    (i : Nat) (hi : i < (batchRebuildTrace t).rows.length)
    (c : VmConstraint2) (hc : c ∈ (descriptor prog).constraints) :
    c.holdsAt hash (batchRebuildTrace t).tf (envAt (batchRebuildTrace t) i) (i == 0)
      (i + 1 == (batchRebuildTrace t).rows.length) := by
  rw [batchRebuildTrace_rows_length] at hi
  set input_i := rowInputAt (envAt t i) with hii
  set envU := envAt (batchRebuildTrace t) i with hEU
  have hrows := hsat.rowConstraints i hi
  -- the three raw gates hold on the ORIGINAL row, giving prog.Holds on this row's raw inputs
  have hHolds : prog.Holds input_i := by
    refine (batchGates_iff_holds hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)).1 ?_
    exact ⟨hrows _ rawTransition_mem, hrows _ rawRecompose_mem,
      fun j => hrows _ (rawPair_mem j)⟩
  have hfa : ∀ cc, fieldAssignment envU.loc cc = canonicalFieldRow prog input_i cc :=
    fun cc => fa_rebuild t i hi cc
  simp only [descriptor, List.mem_append, List.mem_singleton] at hc
  rcases hc with ((hpin | hlink) | hgraph) | rfl
  · -- public pin: same field value at the raw column as the accepting batch trace
    simp only [publicPins, List.mem_map, List.mem_range] at hpin
    obtain ⟨i0, hi0, rfl⟩ := hpin
    have hpinT := hrows _ (pin_mem_batch hi0)
    simp only [VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm] at hpinT ⊢
    intro hf
    have hfeq : fieldAssignment envU.loc (rawBase 62 + i0)
        = fieldAssignment (envAt t i).loc (rawBase 62 + i0) := by
      rw [hfa]
      have hr := canonicalFieldRow_raw prog input_i ⟨i0, by omega⟩
      simp only [Fin.val_mk] at hr
      rw [hr]; rfl
    have hmodU : envU.loc (rawBase 62 + i0) ≡ (envAt t i).loc (rawBase 62 + i0)
        [ZMOD 2013265921] :=
      (ZMod.intCast_eq_intCast_iff _ _ 2013265921).1 hfeq
    have hpub : envU.pub = (envAt t i).pub := rfl
    rw [hpub]
    exact hmodU.trans (hpinT hf)
  · -- atom link: fieldAssignment of the atom column IS the residual, by construction
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hlink
    refine gate_holds_any hash (batchRebuildTrace t).tf envU _ _ ?_
    simp only [atomLink, atomLinkBody, subW, negW, fieldWindow]
    rw [AffineTerm.fieldWindow_toWindowAt]
    have hcol : fieldAssignment envU.loc a.val = residuals prog input_i a := by
      rw [hfa, canonicalFieldRow_atom]
    have hrawfun : (fun k : Fin 33 => fieldAssignment envU.loc (rawBase 62 + k.val)) = input_i := by
      funext k; rw [hfa]; exact canonicalFieldRow_raw prog input_i k
    have hraw : (prog.atomTerms a).evalField
        (fun k => fieldAssignment envU.loc (rawBase 62 + k.val)) = residuals prog input_i a := by
      rw [hrawfun]; rfl
    rw [hcol, hraw]; ring
  · -- graph node: the compiler's own field-valid postorder witness
    simp only [graphConstraintsAt, List.mem_flatMap] at hgraph
    obtain ⟨node, hnode, hcn⟩ := hgraph
    have hatom : ∀ a : Fin 62, (fun c => fieldAssignment envU.loc c) a.val = residuals prog input_i a :=
      fun a => by show fieldAssignment envU.loc a.val = _; rw [hfa, canonicalFieldRow_atom]
    have hmatch : FieldWitnessesMatch (residuals prog input_i) (boolBase 3 30 62) prog.source
        (fun c => fieldAssignment envU.loc c) := by
      have hcw := canonical_field_witnesses_match prog input_i
      intro k hk
      show fieldAssignment envU.loc (boolBase 3 30 62 + k) = _
      rw [hfa]; exact hcw k hk
    have hvalid := field_nodes_valid_of_matches (residuals prog input_i)
      (boolBase 3 30 62) prog.source (fun c => fieldAssignment envU.loc c) hatom hmatch node hnode
    have hnh := node_constraints_hold_of_field_valid envU node hvalid
    obtain ⟨body, rfl, _⟩ := node_constraint_degree node c hcn
    exact (gate_holds_iff (fun _ => 0) hash (fun _ => []) (batchRebuildTrace t).tf envU false true
      (i == 0) (i + 1 == (batchRebuildTrace t).rows.length) body).mp (hnh (gate body) hcn)
  · -- accept: the source output bit is 1 because the pilot source Holds
    refine gate_holds_any hash (batchRebuildTrace t).tf envU _ _ ?_
    simp only [acceptConstraintAt, subW, negW, fieldWindow]
    rw [fieldWire_expr]
    have hout : fieldWireValue (fun c => fieldAssignment envU.loc c)
        (outputAt (boolBase 3 30 62) prog.source) = evalBit (residuals prog input_i) prog.source := by
      apply field_output_of_matches
      have hcw := canonical_field_witnesses_match prog input_i
      intro k hk
      show fieldAssignment envU.loc (boolBase 3 30 62 + k) = _
      rw [hfa]; exact hcw k hk
    have hone : evalBit (residuals prog input_i) prog.source = 1 :=
      (evalBit_one_iff (residuals prog input_i) prog.source).2 hHolds
    rw [fieldWireValue_assignment] at hout
    rw [hout, hone]; ring

/-- THE COMPLETENESS LEG, per row: the 32 raw gates hold on any accepting `descriptor prog` trace,
derived from the compiler's `sound` run at that row via the bridge. -/
theorem batch_completeness_row (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hsat : Satisfied2 hash (descriptor prog) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (c : VmConstraint2) (hc : c ∈ batchDescriptor.constraints) :
    c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  have hrows := hsat.rowConstraints i hi
  have hHolds : prog.Holds (rowInputAt (envAt t i)) :=
    holds_of_env prog hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) hrows
  obtain ⟨hgT, hgR, hgP⟩ :=
    (batchGates_iff_holds hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)).2 hHolds
  simp only [batchDescriptor, batchConstraints, List.mem_append, List.mem_cons,
    List.mem_singleton, List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hc
  rcases hc with (hpin | (rfl | rfl)) | ⟨j, -, rfl⟩
  · -- pin: also a source constraint, held by hsat
    exact hrows c (by simp only [descriptor, List.mem_append]; exact Or.inl (Or.inl (Or.inl hpin)))
  · exact hgT
  · exact hgR
  · exact hgP j

/-! ## 5. THE CERTIFIED PASS, composed with E1, and parity measured on its output. -/

/-- THE BATCH PASS.  `toTarget` is the identity (no column moves at this stage), `toSource` restores
the whole elided Boolean-graph witness canonically, per row. -/
noncomputable def batchPass : PassiveOptimization (descriptor prog) batchDescriptor where
  toTarget := id
  toSource := batchRebuildTrace
  publicABI := { piCount_eq := rfl, bindingSlots_eq := publicBindingSlots_batch.symm }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

theorem batch_security : SecurityRefinement batchPass := by
  intro hash minit mfin maddrs t hsat
  refine PeepholePassCertified.satisfied2_transfer (t := t) (u := batchRebuildTrace t)
    (memOps_descriptor_nil prog) (mapOps_descriptor_nil prog)
    memOps_batch_nil mapOps_batch_nil rfl rfl rfl hsat ?_
  intro i hi c hc
  exact batch_security_row hash minit mfin maddrs t hsat i hi c hc

theorem batch_completeness : CompletenessPreservation batchPass := by
  intro hash minit mfin maddrs t hsat
  refine PeepholePassCertified.satisfied2_transfer (t := t) (u := t)
    memOps_batch_nil mapOps_batch_nil
    (memOps_descriptor_nil prog) (mapOps_descriptor_nil prog) rfl rfl rfl hsat ?_
  intro i hi c hc
  exact batch_completeness_row hash minit mfin maddrs t hsat i hi c hc

/-- BOTH LEGS: the whole-spine batch is a genuine equisatisfiability-preserving passive pass on the
EMITTED pilot descriptor. -/
theorem batch_preservation : SatisfiabilityPreservation batchPass :=
  ⟨batch_security, batch_completeness⟩

theorem batch_satisfiable_iff (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (descriptor prog) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash batchDescriptor minit mfin maddrs u) :=
  satisfiable_iff_of_preservation batch_preservation hash minit mfin maddrs

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- The batch then E1, end to end, through the framework's own composition. -/
noncomputable def certifiedPeepholePass (floor : Nat) :
    PassiveOptimization (descriptor prog)
      (compactE1 batchDescriptor (deadColsE1 batchDescriptor floor)) :=
  batchPass.comp
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPass batchDescriptor floor)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- END TO END: `certifiedPeephole = E1 ∘ batchPeephole` preserves satisfaction in both directions.
The hypothesis is E1's own cheap transition-ceiling certificate on the batched descriptor — the pilot
has no transition faces, so it holds at `floor = 0` (measured below). -/
theorem certifiedPeephole_preservation (floor : Nat)
    (hceiling : transitionCeilingOk batchDescriptor floor = true) :
    SatisfiabilityPreservation (certifiedPeepholePass floor) :=
  preservation_comp batch_preservation
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPreservation
      batchDescriptor floor hceiling)

/-! ### THE DELIVERABLE — parity 35/33/30 measured on the certified pass OUTPUT.

`certifiedPeephole` is the OUTPUT of `certifiedPeepholePass 0` (its target descriptor); the numbers
below are `#guard`ed on that exact object, the SAME object `certifiedPeephole_preservation 0` proves
`SatisfiabilityPreservation` for. No hand-built `loweredDescriptor` in the loop. -/

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- The certified pass output at `floor = 0`. -/
def certifiedPeephole : EffectVmDescriptor2 :=
  compactE1 batchDescriptor (deadColsE1 batchDescriptor 0)

/-- Nonlinear-multiplication count of a descriptor: the sum over its gate bodies, using the same
both-factors-nonconstant convention as `Node.multiplications`. Invariant under E1's column remap. -/
def descriptorNonlinearMuls (d : EffectVmDescriptor2) : Nat :=
  (d.constraints.map (fun c => match c with
    | .windowGate w => nonlinearMuls w.body
    | _ => 0)).sum

-- The batch output BEFORE E1: 35 direct constraints, 30 nonlinear multiplications (trace width still
-- 280 — the dead atom/witness columns are what E1 removes).
#guard batchDescriptor.constraints.length == 35
#guard descriptorNonlinearMuls batchDescriptor == 30
#guard batchDescriptor.piCount == 3

-- E1's transition-ceiling certificate holds at floor 0 (the pilot has no transition faces).
#guard Dregg2.Circuit.Emit.RotWideCompactE1.transitionCeilingOk batchDescriptor 0 == true

-- THE PARITY, MEASURED ON THE CERTIFIED PASS OUTPUT: 33 / 35 / 30 — equal to the hand emit.
#guard certifiedPeephole.traceWidth == 33          -- hand FieldDeltaRangeEmit: 33
#guard certifiedPeephole.constraints.length == 35  -- hand: 35
#guard descriptorNonlinearMuls certifiedPeephole == 30  -- hand: 30 booleanity products
#guard certifiedPeephole.piCount == 3

#assert_all_clean [
  holds_andAll,
  pilot_holds_iff,
  holds_of_env,
  batchGates_iff_holds,
  publicBindingSlots_batch,
  batch_security_row,
  batch_completeness_row,
  batch_security,
  batch_completeness,
  batch_preservation,
  batch_satisfiable_iff,
  certifiedPeephole_preservation
]

end Dregg2.Circuit.PeepholeBatchCertified

