/-
# Dregg2.Circuit.Emit.MultiStepChainRefine — the WHOLE-DESCRIPTOR functional-correctness bridge for
the MULTI-STEP derivation-chaining composition (`MultiStepChainEmit.multiStepChainDesc`).

## What Rung-0 already proved (in `MultiStepChainEmit.lean`)
`multiStepChainDesc` is byte-pinned to the deployed wire, and its continuity window has a LOCAL
soundness lemma (`continuity_zero_iff` : the window body vanishes iff `nxt[PREV] = loc[ACC]`). What was
MISSING: the whole-descriptor bridge — that a trace SATISFYING the descriptor (`Satisfied2`)
corresponds to the genuine semantic relation the chain circuit computes.

## What THIS file proves (Rung-1)
The census dossier for `multi_step` is `spec_status = NO_LEAN`: no proven semantic model existed for
the CHAINING semantics. So this file FIRST authors the missing functional spec — the genuine relation
the multi-step composition is meant to compute — then proves the emitted descriptor refines it
(SAT ⟹ SEM, the load-bearing soundness direction).

### The semantic relation (authored here): the Merkle–Damgård accumulated-hash chain
`chainFold hash initial [d₀,…,d_{K-1}]` = `foldl (fun acc d => hash [acc, d]) initial [d₀,…,d_{K-1}]`
— the running left-fold that starts at `initial_state_root` and absorbs each step's `derived_hash`
by `hash_2_to_1(acc, derived)`. This IS the chaining producer
(`circuit/src/multi_step_air.rs::compute_accumulated_hashes`): `prev₀ = initial`,
`accᵢ = hash_2_to_1(prevᵢ, derivedᵢ)`, `prevᵢ₊₁ = accᵢ`, `final = acc_last`.

### The bridge (whole descriptor, not one gate)
`multiStepChain_refines_chainFold` (SAT ⟹ SEM): a trace that SATISFIES the whole `multiStepChainDesc`
against the NAMED Poseidon2 chip-lookup soundness carrier `ChipTableSound hash (t.tf .poseidon2)`
forces its published tail PI to be the genuine chain fold of the published head PI over the trace's
`derived_hash` column:

    t.pub FINAL_PI = chainFold hash (t.pub INITIAL_PI) (traceDeriveds t).

It COMPOSES all four constraint families over ALL rows: the per-row `hash_2_to_1` absorb (MS1, the chip
lookup + the lever `chip_lookup_sound`), the transition continuity (MS2, the window), and the two
boundary PI pins (MS3, `initPin`/`finalPin`) — assembled by induction over the row count. This is the
whole descriptor's chaining semantics, not a single-gate restatement.

### Non-vacuity (the anti-scar proof)
`wTrace_satisfied2` builds a CONCRETE one-row trace + a concrete chip table + `hash = 0` for which
`Satisfied2` genuinely holds AND `ChipTableSound` holds — the hypothesis chain is inhabited;
`witness_spec` fires the bridge end-to-end on it. `badCont_rejects` and `badAbsorb_rejects` exhibit
CONCRETE traces that FAIL `Satisfied2` because a constraint BITES: an unlinked chain
(`nxt[PREV] ≠ loc[ACC]`) trips the MS2 continuity window, and an empty chip table makes the MS1 absorb
lookup unsatisfiable — so neither the continuity gate nor the hash-binding lookup is decorative.

### Honest residuals (NAMED, not laundered)
The per-derivation single-step constraints (Datalog body membership, head binding, range proofs) are
the SIBLING `derivation` family — `DERIVED` here is that circuit's published `derived_hash` column,
taken as a free per-row input at the chain layer (exactly the split the emit file's `## Residuals`
records). MS4 conclusion-decode and POLICY_ROOT are likewise not emitted at this layer.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The SOLE cryptographic carrier is the
NAMED Poseidon2 chip-lookup soundness `ChipTableSound hash (t.tf .poseidon2)` (the deployed chip AIR's
own faithfulness — the same carrier `chip_lookup_sound` rides); `hash` is a parameter, and the carrier
enters only as an explicit hypothesis, never an axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.MultiStepChainEmit

namespace Dregg2.Circuit.Emit.MultiStepChainRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace TraceFamily VmConstraint2 Lookup TableId WindowConstraint WindowExpr envAt zeroAsg
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES memOpsOf mapOpsOf
   memLog mapLog opRow memCheck_nil)
open Dregg2.Circuit.Emit.MultiStepChainEmit
  (multiStepChainDesc ms1Absorb ms2Continuity initPin finalPin contBody contBody_eq
   continuity_zero_iff PREV DERIVED ACC LANES INITIAL_PI FINAL_PI)

set_option autoImplicit false

/-! ## §1 — the authored functional spec (NO_LEAN): the Merkle–Damgård accumulated-hash chain. -/

/-- **`chainFold hash initial deriveds`** — THE FUNCTIONAL SPEC of the multi-step composition: fold
each step's `derived_hash` into the running accumulator by `hash_2_to_1(acc, derived) = hash [acc, d]`,
from the `initial_state_root`. The Lean twin of the deployed producer
`MultiStepWitness::compute_accumulated_hashes`. -/
def chainFold (hash : List ℤ → ℤ) (initial : ℤ) (deriveds : List ℤ) : ℤ :=
  deriveds.foldl (fun acc d => hash [acc, d]) initial

/-- Absorbing one more `derived` at the tail is one more `hash_2_to_1` step — the fold's recursion. -/
theorem chainFold_concat (hash : List ℤ → ℤ) (initial : ℤ) (ds : List ℤ) (d : ℤ) :
    chainFold hash initial (ds ++ [d]) = hash [chainFold hash initial ds, d] := by
  simp only [chainFold, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## §2 — trace-derived sequences (the chain's per-row columns). -/

/-- The accumulated hash LEAVING step `i` (`accᵢ`, the chip out0 column). -/
def accAt (t : VmTrace) (i : Nat) : ℤ := (envAt t i).loc ACC
/-- The accumulated hash ENTERING step `i` (`prevᵢ`). -/
def prevAt (t : VmTrace) (i : Nat) : ℤ := (envAt t i).loc PREV
/-- This step's per-derivation `derived_hash` (a free input at the chain layer). -/
def derivedAt (t : VmTrace) (i : Nat) : ℤ := (envAt t i).loc DERIVED

/-- The `derived_hash` sequence read off the trace, in row order — the chain's input list. -/
def traceDeriveds (t : VmTrace) : List ℤ :=
  (List.range t.rows.length).map (derivedAt t)

/-! ## §2b — the field-faithful mod-`p` envelope.

Under the deployed denotation the continuity window and the two PI pins bind only CONGRUENCES
(`≡ [ZMOD p]`, `p` the BabyBear prime). A chain accumulator is re-hashed at the next step, so a mod-`p`
congruence on `PREV`/`ACC` cannot thread through the abstract `hash` — we recover the genuine ℤ
equalities from the DEPLOYED range-check canonicality (`0 ≤ cell < p`) of the stored spine columns
(`PREV`/`ACC` on every row, and the head/tail PIs). The absorb lemma (MS1) rides `chip_lookup_sound`
directly, so it is a genuine equality already; only MS2/MS3 need this lift. Inhabited by `wMscCanon`. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  rw [Int.modEq_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega

/-- The deployed range-check envelope: every stored spine cell (`PREV`/`ACC` on every row) and both
public inputs are canonical field cells. -/
def MscCanon (t : VmTrace) : Prop :=
  (∀ i, i < t.rows.length → Canon (prevAt t i) ∧ Canon (accAt t i))
  ∧ Canon (t.pub INITIAL_PI) ∧ Canon (t.pub FINAL_PI)

/-- A specific constraint is a member of `multiStepChainDesc`'s (flat) constraint list. -/
local macro "in_ms" : tactic =>
  `(tactic| (simp only [multiStepChainDesc, List.mem_cons, List.mem_singleton]; tauto))

/-! ## §3 — extraction plumbing: the four constraint families, forced from `Satisfied2`. -/

/-- **MS1 (the per-step absorb).** On EVERY row, the chip-lookup + the Poseidon2 chip-lookup soundness
lever force `accᵢ = hash_2_to_1(prevᵢ, derivedᵢ) = hash [prevᵢ, derivedᵢ]`. -/
theorem accAt_absorb (hash : List ℤ → ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hsat : Satisfied2 hash multiStepChainDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    accAt t i = hash [prevAt t i, derivedAt t i] := by
  have hrow := hsat.rowConstraints i hi ms1Absorb (by in_ms)
  simp only [ms1Absorb, VmConstraint2.holdsAt, Lookup.holdsAt] at hrow
  have hsound := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t i).loc
    [.var PREV, .var DERIVED] ACC LANES (by decide) hrow
  simpa only [accAt, prevAt, derivedAt, List.map_cons, List.map_nil, EmittedExpr.eval] using hsound

/-- **MS2 (chain continuity).** On every TRANSITION row (`i+1 < len`), the continuity window forces
`prevᵢ₊₁ = accᵢ` — the next step's entering hash is this step's leaving hash. -/
theorem prev_succ_eq_acc (hash : List ℤ → ℤ) (t : VmTrace)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hsat : Satisfied2 hash multiStepChainDesc minit mfin maddrs t) (hcanon : MscCanon t)
    (i : Nat) (hnext : i + 1 < t.rows.length) :
    prevAt t (i + 1) = accAt t i := by
  have hi : i < t.rows.length := by omega
  have hrow := hsat.rowConstraints i hi ms2Continuity (by in_ms)
  simp only [ms2Continuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_true] at hrow
  have hlastf : (i + 1 == t.rows.length) = false := by rw [beq_eq_false_iff_ne]; omega
  -- the window binds `contBody.eval ≡ 0 [ZMOD p]`, i.e. `prevAt (i+1) ≡ accAt i [ZMOD p]`.
  have hbody : contBody.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := hrow hlastf
  have hshift : (envAt t i).nxt PREV = prevAt t (i + 1) := by simp only [prevAt, envAt]
  have hacc : (envAt t i).loc ACC = accAt t i := by simp only [accAt]
  have hkey : contBody.eval (envAt t i) = prevAt t (i + 1) - accAt t i := by
    simp only [contBody_eq, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval, hshift, hacc]; ring
  rw [hkey] at hbody
  have hmod : prevAt t (i + 1) ≡ accAt t i [ZMOD 2013265921] := by
    have := hbody.add_right (accAt t i); simpa using this
  exact eq_of_modEq_canon (hcanon.1 (i + 1) hnext).1 (hcanon.1 i hi).2 hmod

/-- **MS3a (the head pin).** On row 0, `initPin` forces `prev₀ = pi[INITIAL_STATE_ROOT]`. -/
theorem prev_zero_eq_pi (hash : List ℤ → ℤ) (t : VmTrace)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hsat : Satisfied2 hash multiStepChainDesc minit mfin maddrs t) (hcanon : MscCanon t)
    (h0 : 0 < t.rows.length) :
    prevAt t 0 = t.pub INITIAL_PI := by
  have hrow := hsat.rowConstraints 0 h0 initPin (by in_ms)
  simp only [initPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrow
  have hpin : prevAt t 0 ≡ t.pub INITIAL_PI [ZMOD 2013265921] := by
    simpa only [prevAt, envAt] using hrow rfl
  exact eq_of_modEq_canon (hcanon.1 0 h0).1 hcanon.2.1 hpin

/-- **MS3b (the tail pin).** On the last row, `finalPin` forces `acc_last = pi[FINAL_ACCUMULATED_HASH]`. -/
theorem acc_last_eq_pi (hash : List ℤ → ℤ) (t : VmTrace)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hsat : Satisfied2 hash multiStepChainDesc minit mfin maddrs t) (hcanon : MscCanon t)
    (h0 : 0 < t.rows.length) :
    accAt t (t.rows.length - 1) = t.pub FINAL_PI := by
  have hlast : t.rows.length - 1 < t.rows.length := by omega
  have hrow := hsat.rowConstraints (t.rows.length - 1) hlast finalPin (by in_ms)
  simp only [finalPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrow
  have hL : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [show t.rows.length - 1 + 1 = t.rows.length from by omega]; exact beq_self_eq_true _
  have hpin : accAt t (t.rows.length - 1) ≡ t.pub FINAL_PI [ZMOD 2013265921] := by
    simpa only [accAt, envAt] using hrow hL
  exact eq_of_modEq_canon (hcanon.1 (t.rows.length - 1) hlast).2 hcanon.2.2 hpin

/-! ## §4 — the running-accumulator invariant (the chain assembled over the rows). -/

/-- **The chain invariant.** For every step `m` in range, the leaving accumulator `accₘ` equals the
chain fold of the head PI over the first `m+1` `derived_hash` values. Proved by induction: base = the
head pin + MS1 at row 0; step = MS1 at `m+1` composed with MS2 (`prevₘ₊₁ = accₘ`) and the IH. -/
theorem acc_chain (hash : List ℤ → ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hsat : Satisfied2 hash multiStepChainDesc minit mfin maddrs t) (hcanon : MscCanon t)
    (h0 : 0 < t.rows.length) :
    ∀ m, m < t.rows.length →
      accAt t m = chainFold hash (t.pub INITIAL_PI) ((List.range (m + 1)).map (derivedAt t)) := by
  intro m
  induction m with
  | zero =>
    intro _
    have hA := accAt_absorb hash t hChip hsat 0 h0
    have hC := prev_zero_eq_pi hash t hsat hcanon h0
    rw [hA, hC]
    simp only [Nat.zero_add, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, chainFold, List.foldl_cons, List.foldl_nil]
  | succ k ih =>
    intro hk1
    have hk : k < t.rows.length := by omega
    have hmap : (List.range (k + 1 + 1)).map (derivedAt t)
        = ((List.range (k + 1)).map (derivedAt t)) ++ [derivedAt t (k + 1)] := by
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [accAt_absorb hash t hChip hsat (k + 1) hk1, prev_succ_eq_acc hash t hsat hcanon k hk1, ih hk,
      hmap, chainFold_concat]

/-! ## §5 — THE BRIDGE (SAT ⟹ SEM): a satisfying trace computes the genuine chain fold. -/

/-- **`multiStepChain_refines_chainFold` — THE whole-descriptor soundness bridge.** A trace that
satisfies the whole `multiStepChainDesc` (`Satisfied2`), against the NAMED Poseidon2 chip-lookup
soundness carrier, has its published tail PI equal to the genuine Merkle–Damgård chain fold of its
published head PI over the trace's `derived_hash` column. Composes MS1 (every-row absorb), MS2
(every-transition continuity), and MS3 (both boundary pins) via the chain invariant — the whole
descriptor's chaining semantics, not a single-gate restatement. -/
theorem multiStepChain_refines_chainFold (hash : List ℤ → ℤ) (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (h0 : 0 < t.rows.length)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hsat : Satisfied2 hash multiStepChainDesc minit mfin maddrs t) (hcanon : MscCanon t) :
    t.pub FINAL_PI = chainFold hash (t.pub INITIAL_PI) (traceDeriveds t) := by
  have hD := acc_last_eq_pi hash t hsat hcanon h0
  have hchain := acc_chain hash t hChip hsat hcanon h0 (t.rows.length - 1) (by omega)
  rw [← hD, hchain, traceDeriveds, Nat.sub_add_cancel h0]

/-! ## §6 — non-vacuity: a CONCRETE satisfying witness (bridge fires) + two failing ones (gate bites).

The witness is the "zero chain": a single step over the constant-zero hash, every column `0`. The chip
table carries exactly the one absorb row the MS1 lookup produces, and `hash = 0` makes it a genuine
`chipRow`, so `ChipTableSound` holds. This is a REAL satisfying trace, not a scar: `witness_spec` fires
the whole bridge end-to-end on it, and the failing traces show teeth that BITE. -/

/-- The single chip row the MS1 lookup produces at the all-zero row: `chipRow 0 [0,0] (0×7)`. -/
def wChipRow : List ℤ := chipRow (fun _ => 0) [0, 0] (List.replicate 7 0)

/-- The witness trace family: the one MS1 chip row on `poseidon2`, empty elsewhere. -/
def wTf : TraceFamily := fun tid => match tid with | .poseidon2 => [wChipRow] | _ => []

/-- The concrete one-row satisfying trace (all columns `0`, all PIs `0`). -/
def wTrace : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := wTf }

/-- **The chip table is genuinely sound** for `hash = 0`: its one row IS a `chipRow` of the arity-2
absorb `[0,0]` (padding `≤ CHIP_RATE`, `7 = CHIP_OUT_LANES - 1` lanes). -/
theorem wChipSound : ChipTableSound (fun _ => 0) (wTf .poseidon2) := by
  intro r hr
  change r ∈ [wChipRow] at hr
  fin_cases hr
  exact ⟨[0, 0], List.replicate 7 0, by decide, by decide, rfl⟩

/-- The chain descriptor declares no memory / map ops, so the gathered logs are empty. -/
theorem w_memLog : memLog multiStepChainDesc wTrace = [] := rfl
theorem w_mapLog : mapLog multiStepChainDesc wTrace = [] := rfl

/-- **Non-vacuity (accept) — the hypothesis is GENUINELY inhabited.** The concrete trace SATISFIES the
whole `multiStepChainDesc`: MS1 lands in the chip table, MS2 is vacuous on the lone (last) row, and both
PI pins close on the zero head/tail; the memory legs are trivial (no mem/map ops). -/
theorem wTrace_satisfied2 :
    Satisfied2 (fun _ => 0) multiStepChainDesc (fun _ => 0) (fun _ => (0, 0)) [] wTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints: the lone row is row 0; each of the four constraints holds.
    intro i hi c hc
    have hi0 : i = 0 := by have : wTrace.rows.length = 1 := rfl; omega
    subst hi0
    have hc' : c ∈ [ms1Absorb, ms2Continuity, initPin, finalPin] := hc
    fin_cases hc'
    · simp only [ms1Absorb, VmConstraint2.holdsAt, Lookup.holdsAt]; decide
    · simp only [ms2Continuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_true]; decide
    · simp only [initPin, VmConstraint2.holdsAt, VmConstraint.holdsVm]; decide
    · simp only [finalPin, VmConstraint2.holdsAt, VmConstraint.holdsVm]; decide
  · intro i _; exact True.intro
  · intro i _ r hr; simp [multiStepChainDesc] at hr
  · intro op hop; rw [w_memLog] at hop; cases hop
  · rw [w_memLog]; decide
  · rw [w_memLog]; exact memCheck_nil _ _
  · rw [w_memLog]; rfl
  · rw [w_mapLog]; rfl

/-- The canonicality envelope is genuinely INHABITED on the all-zero witness. -/
theorem wMscCanon : MscCanon wTrace := by
  refine ⟨?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  intro i hi
  have hi0 : i = 0 := by have : wTrace.rows.length = 1 := rfl; omega
  subst hi0
  exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The bridge fires end-to-end on the concrete witness** (SAT ⟹ SEM, non-vacuously): the tail PI is
DERIVED to be the chain fold of the head PI, not assumed. -/
theorem witness_spec :
    wTrace.pub FINAL_PI = chainFold (fun _ => 0) (wTrace.pub INITIAL_PI) (traceDeriveds wTrace) :=
  multiStepChain_refines_chainFold (fun _ => 0) wTrace wChipSound (by decide) wTrace_satisfied2
    wMscCanon

/-- A two-row trace whose row-1 `PREV` (9) ≠ row-0 `ACC` (5) — the MS2 continuity link is BROKEN. -/
def badContRow0 : Assignment := fun c => if c = ACC then 5 else 0
def badContRow1 : Assignment := fun c => if c = PREV then 9 else 0
def badContTrace : VmTrace :=
  { rows := [badContRow0, badContRow1], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — MS2 continuity BITES).** The unlinked chain FAILS `Satisfied2`: the
continuity window on the transition row forces `nxt[PREV] = loc[ACC]`, i.e. `9 = 5` — exactly the
"chain the next step from a hash the previous step never produced" break the window forbids. -/
theorem badCont_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash multiStepChainDesc minit mfin maddrs badContTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) ms2Continuity (by in_ms)
  simp only [ms2Continuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_true] at hc
  have hbody : contBody.eval (envAt badContTrace 0) ≡ 0 [ZMOD 2013265921] := hc (by decide)
  revert hbody
  decide

/-- A one-row trace with an EMPTY chip table — the MS1 absorb lookup has nowhere to land. -/
def badAbsorbTrace : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — MS1 absorb BITES).** With an empty Poseidon2 chip table the MS1 lookup
`… ∈ tf .poseidon2 = []` is unsatisfiable, so `Satisfied2` FAILS: the hash-binding lookup is
load-bearing, not decorative — a trace whose accumulated hash is unbacked by any chip row is rejected. -/
theorem badAbsorb_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash multiStepChainDesc minit mfin maddrs badAbsorbTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) ms1Absorb (by in_ms)
  simp only [ms1Absorb, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  revert hc
  decide

/-! ### Shape pins. -/
#guard decide (wTrace.rows.length = 1)
#guard decide (badContTrace.rows.length = 2)
#guard decide (wChipRow.length = 1 + CHIP_RATE + CHIP_OUT_LANES)

#assert_axioms multiStepChain_refines_chainFold
#assert_axioms acc_chain
#assert_axioms wTrace_satisfied2
#assert_axioms wChipSound
#assert_axioms witness_spec
#assert_axioms badCont_rejects
#assert_axioms badAbsorb_rejects

end Dregg2.Circuit.Emit.MultiStepChainRefine
