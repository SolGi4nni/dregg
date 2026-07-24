/-
# Dregg2.Circuit.PeepholeGeneralBatch — ONE certified batch peephole pass over ARBITRARY descriptors.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint; the
pass READS the constraint list any `EffectVmDescriptor2` carries and rewrites it, and the security
argument is a machine-checked polynomial identity over the emitted gate bodies.

## What this closes — the general recognizer's remaining ALL-SITES leg

`PeepholeGeneralPass` supplied the general RECOGNIZER (`recognizePeephole`, reading constraint
SHAPES) and a per-SITE certified rule. `PeepholeBatchCertified` fired ALL sites at once, but through
the program-specific `pilot_holds_iff` — keyed to ONE program. This module is the program-INDEPENDENT
all-sites batch: `generalBatchPeephole : EffectVmDescriptor2 → EffectVmDescriptor2` folds a single
shape-determined rewrite over EVERY recognized zero-test site of an ARBITRARY descriptor, and it is
proved a genuine `SatisfiabilityPreservation` — over every `d`, not one pilot — then composed with
the certified E1 via `preservation_comp`.

## The shape-determined, program-INDEPENDENT rewrite

A materialized `zeroTest x out inv` node emits three gates
  (B) `out·(out−1) = 0`                         — `out` is a bit
  (P) `x·out = 0`
  (I) `x·inv + out − 1 = 0`
The BIT gate (B) is REDUNDANT: it is implied by (P) and (I) over the field, by the exact polynomial
identity
    out·(out−1)  =  out·(x·inv + out − 1)  −  inv·(x·out).
So a target witness that satisfies (P) and (I) already satisfies (B): removing (B) is sound in BOTH
directions with the IDENTITY trace map — no witness rebuild, no source-program `Holds` lemma. The
"rebuild" the batch's per-site witness once needed is here DISCHARGED BY THE SHAPE: the elided gate's
content is a consequence of the two surviving companion gates of the SAME node, read off the list.

`generalBatchPeephole d` removes exactly the bit gate `gate (bitBody (.col out))` of every `out` for
which the list also carries a matching inverse gate `(I)` and product gate `(P)` — a purely syntactic,
decidable, program-independent condition. Over-recognition is impossible-to-unsound: the polynomial
identity holds whenever (P) and (I) are present, whatever the surrounding descriptor.

## Named residual (no `sorry`, no stand-in)

This batch elides one REDUNDANT gate per recognized zero-test (−1 constraint, −1 nonlinear
multiplication each): a genuine, general, both-directions optimization. It does NOT reach the pilot's
35/33/30 collapse — that collapse asserts the residual `x = 0` at the accept frontier, which is
program-DEPENDENT (sound only where the accept path forces `out = 1`) and remains
`PeepholeBatchCertified`'s pilot-specific achievement. The remaining leg for a GENERAL cost-parity
pass is the syntactic accept-reachability qualification (design §2's frontier scan): only then may the
whole zero-test be replaced by the raw affine gate program-independently. What is closed here is the
part that IS program-independent: the redundant-booleanity elision, all sites, arbitrary descriptor.

Standalone and additive: imports the recognizer/pilot for the demonstrations and the framework;
changes none of them.
-/
import Dregg2.Circuit.PeepholeGeneralPass
import Dregg2.Circuit.PeepholeBatchCertified

namespace Dregg2.Circuit.PeepholeGeneralBatch

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (gate bitBody Wire)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (descriptor)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false

/-! ## 1. The syntactic recognition of a redundant zero-test bit gate. -/

/-- `some out` iff `c` is the (non-transition) booleanity gate `gate (bitBody (.col out))`, i.e.
`out·(out−1) = 0`. -/
def isBitGateCol : VmConstraint2 → Option Nat
  | .windowGate w =>
      if w.onTransition then none else
      match w.body with
      | .mul (.loc a) (.add (.loc b) (.const k)) =>
          if a == b && k == (-1 : Int) then some a else none
      | _ => none
  | _ => none

/-- `c` is the (non-transition) product gate `gate (x·out)`. -/
def isProdGate (x out : Nat) (c : VmConstraint2) : Bool :=
  match c with
  | .windowGate w =>
      !w.onTransition &&
      (match w.body with
       | .mul (.loc a) (.loc b) => a == x && b == out
       | _ => false)
  | _ => false

/-- The list carries a matching product gate `x·out = 0`. -/
def hasProdGate (cs : List VmConstraint2) (x out : Nat) : Bool :=
  cs.any (isProdGate x out)

/-- The `out` columns whose zero-test bit gate is REDUNDANT: the list carries an inverse gate
`x·inv + out − 1 = 0` for some `x, inv`, together with the matching product gate `x·out = 0`. -/
def confirmedOuts (cs : List VmConstraint2) : List Nat :=
  cs.filterMap fun c =>
    match c with
    | .windowGate w =>
        if w.onTransition then none else
        match w.body with
        | .add (.add (.mul (.loc x) (.loc _inv)) (.loc out)) (.const k) =>
            if k == (-1 : Int) && hasProdGate cs x out then some out else none
        | _ => none
    | _ => none

/-- Keep a constraint unless it is a bit gate whose column is confirmed-redundant. -/
def keepPred (outs : List Nat) (c : VmConstraint2) : Bool :=
  match isBitGateCol c with
  | some o => decide (o ∉ outs)
  | none => true

/-- THE GENERAL BATCH PASS on descriptors: elide every confirmed-redundant zero-test bit gate. A
record-update of the constraint list; trace geometry, public ABI, hash sites, ranges, memory/map ops
untouched. -/
def generalBatchPeephole (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints.filter (keepPred (confirmedOuts d.constraints)) }

/-! ## 2. Shape lemmas — every match direction inverted, no `decide` on the descriptor. -/

/-- A recognized bit gate IS `gate (bitBody (.col out))`. -/
theorem isBitGateCol_eq {c : VmConstraint2} {out : Nat} (h : isBitGateCol c = some out) :
    c = gate (bitBody (.col out)) := by
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only [isBitGateCol] at h
    split at h
    · simp at h
    · rename_i honT
      split at h
      · rename_i a b k
        split at h
        · rename_i hcond
          rw [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨hab, hk⟩ := hcond
          subst hab; subst hk
          have honT' : onT = false := by cases onT <;> simp_all
          subst honT'
          rfl
        · simp at h
      · simp at h
  | base _ => simp [isBitGateCol] at h
  | lookup _ => simp [isBitGateCol] at h
  | memOp _ => simp [isBitGateCol] at h
  | mapOp _ => simp [isBitGateCol] at h
  | umemOp _ => simp [isBitGateCol] at h
  | proofBind _ => simp [isBitGateCol] at h

/-- Product / inverse gates are never bit gates, so they always survive the filter. -/
theorem isBitGateCol_prod (x out : Nat) : isBitGateCol (gate (.mul (.loc x) (.loc out))) = none :=
  rfl

theorem isBitGateCol_inv (x inv out : Nat) :
    isBitGateCol
        (gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)))) = none := rfl

/-- A matched product gate IS `gate (x·out)`. -/
theorem isProdGate_eq {x out : Nat} {c : VmConstraint2} (h : isProdGate x out c = true) :
    c = gate (.mul (.loc x) (.loc out)) := by
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only [isProdGate, Bool.and_eq_true] at h
    obtain ⟨hoT, hbody⟩ := h
    have honT : onT = false := by cases onT <;> simp_all
    subst honT
    split at hbody
    · rename_i a b
      simp only [Bool.and_eq_true, beq_iff_eq] at hbody
      obtain ⟨ha, hb⟩ := hbody
      subst ha; subst hb
      rfl
    · simp at hbody
  | base _ => simp [isProdGate] at h
  | lookup _ => simp [isProdGate] at h
  | memOp _ => simp [isProdGate] at h
  | mapOp _ => simp [isProdGate] at h
  | umemOp _ => simp [isProdGate] at h
  | proofBind _ => simp [isProdGate] at h

/-- A confirmed `out` witnesses its two companion gates in the ORIGINAL list. -/
theorem confirmed_companions {cs : List VmConstraint2} {out : Nat} (h : out ∈ confirmedOuts cs) :
    ∃ x inv, gate (.mul (.loc x) (.loc out)) ∈ cs ∧
      gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))) ∈ cs := by
  obtain ⟨c, hc, hmatch⟩ := List.mem_filterMap.1 h
  cases c with
  | windowGate w =>
    obtain ⟨body, onT⟩ := w
    simp only at hmatch
    split at hmatch
    · simp at hmatch
    · rename_i honT
      split at hmatch
      · rename_i x inv out' k
        split at hmatch
        · rename_i hcond
          rw [Option.some.injEq] at hmatch
          subst hmatch
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨hk, hprod⟩ := hcond
          subst hk
          have honT' : onT = false := by cases onT <;> simp_all
          subst honT'
          refine ⟨x, inv, ?_, ?_⟩
          · obtain ⟨c2, hc2, hp2⟩ := List.any_eq_true.1 hprod
            rw [isProdGate_eq hp2] at hc2
            exact hc2
          · exact hc
        · simp at hmatch
      · simp at hmatch
  | base _ => simp at hmatch
  | lookup _ => simp at hmatch
  | memOp _ => simp at hmatch
  | mapOp _ => simp at hmatch
  | umemOp _ => simp at hmatch
  | proofBind _ => simp at hmatch

/-! ## 3. The polynomial redundancy identity — program-independent soundness core. -/

open Dregg2.Circuit.PeepholePassCertified (gate_dvd_iff)

/-- THE SOUNDNESS CORE: a witness that satisfies the product gate `x·out = 0` and the inverse gate
`x·inv + out − 1 = 0` already satisfies the bit gate `out·(out−1) = 0`. Pure field identity, no
source program. -/
theorem bit_gate_of_companions (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (x out inv : Nat)
    (h2 : (gate (.mul (.loc x) (.loc out))).holdsAt hash tf env f l)
    (h3 : (gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1)))).holdsAt
      hash tf env f l) :
    (gate (bitBody (.col out))).holdsAt hash tf env f l := by
  rw [gate_dvd_iff] at h2 h3 ⊢
  have hid : (bitBody (.col out)).eval env =
      env.loc out * (WindowExpr.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))).eval env
        - env.loc inv * (WindowExpr.mul (.loc x) (.loc out)).eval env := by
    show (WindowExpr.mul (Wire.col out).expr (.add (Wire.col out).expr (.const (-1)))).eval env = _
    simp only [Wire.expr, WindowExpr.eval]; ring
  rw [hid]
  exact dvd_sub (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_left h2 _)

/-! ## 4. Filter bookkeeping — the pass changes only bit gates, so every carrier is preserved. -/

/-- Removed constraints are exactly the recognized bit gates; every non-bit constraint is kept, and a
kept bit gate has a non-confirmed column. -/
theorem keep_of_not_bit {outs : List Nat} {c : VmConstraint2} (h : isBitGateCol c = none) :
    keepPred outs c = true := by simp [keepPred, h]

/-- A dropped constraint is a windowGate (only bit gates are dropped). -/
theorem dropped_isBitGate {outs : List Nat} {c : VmConstraint2} (h : keepPred outs c = false) :
    ∃ out, isBitGateCol c = some out ∧ out ∈ outs := by
  unfold keepPred at h
  cases hb : isBitGateCol c with
  | none => rw [hb] at h; simp at h
  | some out =>
    rw [hb] at h
    simp only [decide_eq_false_iff_not, Decidable.not_not] at h
    exact ⟨out, rfl, h⟩

/-- A generic list fact: filtering by `P` then `filterMap`ping by `f` equals `filterMap`ping the
whole list, when every dropped element already maps to `none`. -/
theorem filterMap_filter_of_removed_none {α β : Type} (P : α → Bool) (f : α → Option β)
    (h : ∀ a, P a = false → f a = none) :
    ∀ l : List α, (l.filter P).filterMap f = l.filterMap f
  | [] => rfl
  | a :: l => by
      cases hpa : P a with
      | true =>
        rw [List.filter_cons_of_pos hpa, List.filterMap_cons, List.filterMap_cons,
          filterMap_filter_of_removed_none P f h l]
      | false =>
        rw [List.filter_cons_of_neg (by simp [hpa]), List.filterMap_cons, h a hpa,
          filterMap_filter_of_removed_none P f h l]

/-- Every dropped constraint (a bit gate) is a `windowGate`, so it maps to `none` under `memOpsOf` /
`mapOpsOf` / `bindingSlot?`. -/
theorem dropped_windowGate {outs : List Nat} {c : VmConstraint2}
    (h : keepPred outs c = false) : ∃ w, c = .windowGate w := by
  obtain ⟨out, hbit, -⟩ := dropped_isBitGate h
  exact ⟨_, isBitGateCol_eq hbit⟩

theorem memOps_general (d : EffectVmDescriptor2) :
    memOpsOf (generalBatchPeephole d) = memOpsOf d := by
  show (d.constraints.filter _).filterMap _ = _
  apply filterMap_filter_of_removed_none
  intro a ha
  obtain ⟨w, rfl⟩ := dropped_windowGate ha
  rfl

theorem mapOps_general (d : EffectVmDescriptor2) :
    mapOpsOf (generalBatchPeephole d) = mapOpsOf d := by
  show (d.constraints.filter _).filterMap _ = _
  apply filterMap_filter_of_removed_none
  intro a ha
  obtain ⟨w, rfl⟩ := dropped_windowGate ha
  rfl

theorem bindingSlots_general (d : EffectVmDescriptor2) :
    publicBindingSlots (generalBatchPeephole d) = publicBindingSlots d := by
  show (d.constraints.filter _).filterMap _ = _
  apply filterMap_filter_of_removed_none
  intro a ha
  obtain ⟨w, rfl⟩ := dropped_windowGate ha
  rfl

theorem hashSites_general (d : EffectVmDescriptor2) :
    (generalBatchPeephole d).hashSites = d.hashSites := rfl

theorem ranges_general (d : EffectVmDescriptor2) :
    (generalBatchPeephole d).ranges = d.ranges := rfl

theorem piCount_general (d : EffectVmDescriptor2) :
    (generalBatchPeephole d).piCount = d.piCount := rfl

/-! ## 5. The `Satisfied2` transfer for a constraint-only change. -/

/-- When two descriptors agree on hash sites, ranges, and the constraint-derived memory/map ops, a
witness of one becomes a witness of the other as soon as the target's constraints hold on it. -/
theorem satisfied2_congr_constraints {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (d1 d2 : EffectVmDescriptor2) {t : VmTrace}
    (hh : d2.hashSites = d1.hashSites) (hr : d2.ranges = d1.ranges)
    (hmem : memOpsOf d2 = memOpsOf d1) (hmap : mapOpsOf d2 = mapOpsOf d1)
    (hrow : ∀ i, i < t.rows.length → ∀ c ∈ d2.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length))
    (hsat : Satisfied2 hash d1 minit mfin maddrs t) :
    Satisfied2 hash d2 minit mfin maddrs t := by
  have hml : memLog d2 t = memLog d1 t := by unfold memLog; rw [hmem]
  have hmpl : mapLog d2 t = mapLog d1 t := by unfold mapLog; rw [hmap]
  refine ⟨hrow, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hh]; exact hsat.rowHashes i hi
  · intro i hi r hrng; rw [hr] at hrng; exact hsat.rowRanges i hi r hrng
  · intro op hop; rw [hml] at hop; exact hsat.memClosed op hop
  · rw [hml]; exact hsat.memDisciplined
  · rw [hml]; exact hsat.memBalanced
  · rw [hml]; exact hsat.memTableFaithful
  · rw [hmpl]; exact hsat.mapTableFaithful

/-! ## 6. The two contract legs, over an ARBITRARY descriptor. -/

/-- The elided bit gate holds on a target witness. -/
theorem elided_bit_holds (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (tf : TraceFamily)
    (env : VmRowEnv) (f l : Bool) {out : Nat}
    (hconf : out ∈ confirmedOuts d.constraints)
    (htgt : ∀ c ∈ (generalBatchPeephole d).constraints, c.holdsAt hash tf env f l) :
    (gate (bitBody (.col out))).holdsAt hash tf env f l := by
  obtain ⟨x, inv, hp, hi⟩ := confirmed_companions hconf
  have hpKeep : gate (.mul (.loc x) (.loc out)) ∈ (generalBatchPeephole d).constraints := by
    show _ ∈ d.constraints.filter _
    exact List.mem_filter.2 ⟨hp, keep_of_not_bit (isBitGateCol_prod x out)⟩
  have hiKeep : gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))) ∈
      (generalBatchPeephole d).constraints := by
    show _ ∈ d.constraints.filter _
    exact List.mem_filter.2 ⟨hi, keep_of_not_bit (isBitGateCol_inv x inv out)⟩
  exact bit_gate_of_companions hash tf env f l x out inv (htgt _ hpKeep) (htgt _ hiKeep)

theorem general_batch_pass_security_row (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (d : EffectVmDescriptor2) (t : VmTrace)
    (hsat : Satisfied2 hash (generalBatchPeephole d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (c : VmConstraint2) (hc : c ∈ d.constraints) :
    c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  by_cases hin : c ∈ (generalBatchPeephole d).constraints
  · exact hsat.rowConstraints i hi c hin
  · -- c dropped ⇒ a confirmed bit gate
    have hkeep : keepPred (confirmedOuts d.constraints) c = false := by
      by_contra hne
      simp only [Bool.not_eq_false] at hne
      exact hin (List.mem_filter.2 ⟨hc, hne⟩)
    obtain ⟨out, hbit, hconf⟩ := dropped_isBitGate hkeep
    rw [isBitGateCol_eq hbit]
    exact elided_bit_holds hash d t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) hconf
      (hsat.rowConstraints i hi)

/-! ## 7. The general pass and its certified preservation. -/

/-- THE PASS.  Both trace maps are the identity: the rewrite drops redundant constraints only. -/
def generalBatchPass (d : EffectVmDescriptor2) :
    PassiveOptimization d (generalBatchPeephole d) where
  toTarget := id
  toSource := id
  publicABI := { piCount_eq := (piCount_general d).symm
                 bindingSlots_eq := (bindingSlots_general d).symm }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

/-- SECURITY over ARBITRARY `d`: a target witness expands (identity) to a source witness. -/
theorem general_batch_security (d : EffectVmDescriptor2) :
    SecurityRefinement (generalBatchPass d) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints (generalBatchPeephole d) d rfl rfl
    (memOps_general d).symm (mapOps_general d).symm ?_ hsat
  intro i hi c hc
  exact general_batch_pass_security_row hash minit mfin maddrs d t hsat i hi c hc

/-- COMPLETENESS over ARBITRARY `d`: a source witness projects (identity) to a target witness; the
target constraints are a sublist of the source, held verbatim. -/
theorem general_batch_completeness (d : EffectVmDescriptor2) :
    CompletenessPreservation (generalBatchPass d) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints d (generalBatchPeephole d) rfl rfl
    (memOps_general d) (mapOps_general d) ?_ hsat
  intro i hi c hc
  exact hsat.rowConstraints i hi c (List.mem_of_mem_filter hc)

/-- BOTH LEGS: the program-INDEPENDENT batch is a genuine equisatisfiability-preserving passive pass
on EVERY descriptor. -/
theorem general_batch_preservation (d : EffectVmDescriptor2) :
    SatisfiabilityPreservation (generalBatchPass d) :=
  ⟨general_batch_security d, general_batch_completeness d⟩

theorem general_batch_satisfiable_iff (d : EffectVmDescriptor2)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash d minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (generalBatchPeephole d) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (general_batch_preservation d) hash minit mfin maddrs

/-! ## 8. Composition with the certified E1 — end to end, over ARBITRARY `d`. -/

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- The general batch then E1, through the framework's own composition. -/
noncomputable def certifiedGeneralBatchPass (d : EffectVmDescriptor2) (floor : Nat) :
    PassiveOptimization d
      (compactE1 (generalBatchPeephole d) (deadColsE1 (generalBatchPeephole d) floor)) :=
  (generalBatchPass d).comp
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPass
      (generalBatchPeephole d) floor)

open Dregg2.Circuit.Emit.RotWideCompactE1 in
/-- END TO END over ARBITRARY `d`: `E1 ∘ generalBatch` preserves satisfaction in both directions. The
hypothesis is E1's own cheap transition-ceiling certificate on the batched descriptor. -/
theorem certifiedGeneralBatch_preservation (d : EffectVmDescriptor2) (floor : Nat)
    (hceiling : transitionCeilingOk (generalBatchPeephole d) floor = true) :
    SatisfiabilityPreservation (certifiedGeneralBatchPass d floor) :=
  preservation_comp (general_batch_preservation d)
    (Dregg2.Metatheory.EffectVmDescriptor2PassiveOptimization.E1.derivedPreservation
      (generalBatchPeephole d) floor hceiling)

/-! ## 9. GENERALITY — ONE theorem certifies BOTH the pilot and the second descriptor.

`general_batch_preservation` is a `∀ d` theorem; the two corollaries below are pure instantiations at
the field-delta pilot descriptor and at the independent `secondDescriptor` from `PeepholeGeneralPass`.
No pilot-specific bridge, no second theorem. -/

open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Circuit.PeepholeGeneralPass (secondDescriptor)

/-- Certified on the PILOT descriptor — an instance of the general theorem. -/
theorem pilot_batch_preservation :
    SatisfiabilityPreservation (generalBatchPass (descriptor prog)) :=
  general_batch_preservation (descriptor prog)

/-- Certified on the SECOND, independent descriptor — the SAME general theorem. -/
theorem second_batch_preservation :
    SatisfiabilityPreservation (generalBatchPass secondDescriptor) :=
  general_batch_preservation secondDescriptor

/-! ## 10. The pass FIRES on both — measured, compiled `==`, no kernel `decide`. -/

-- Pilot: 62 zero-tests ⇒ 62 redundant bit gates elided (374 → 312 constraints).
#guard (confirmedOuts (descriptor prog).constraints).length == 62
#guard (generalBatchPeephole (descriptor prog)).constraints.length + 62 ==
  (descriptor prog).constraints.length
#guard (generalBatchPeephole (descriptor prog)).piCount == 3

-- Second descriptor: 3 zero-tests ⇒ 3 redundant bit gates elided.
#guard (confirmedOuts secondDescriptor.constraints).length == 3
#guard (generalBatchPeephole secondDescriptor).constraints.length + 3 ==
  secondDescriptor.constraints.length

#assert_all_clean [
  isBitGateCol_eq,
  confirmed_companions,
  bit_gate_of_companions,
  memOps_general,
  mapOps_general,
  bindingSlots_general,
  satisfied2_congr_constraints,
  elided_bit_holds,
  general_batch_pass_security_row,
  general_batch_security,
  general_batch_completeness,
  general_batch_preservation,
  general_batch_satisfiable_iff,
  certifiedGeneralBatch_preservation,
  pilot_batch_preservation,
  second_batch_preservation
]

end Dregg2.Circuit.PeepholeGeneralBatch
