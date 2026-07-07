/-
# `EffectVmEmitIvcStateTransitionRefine` — the RUNG-1 functional-correctness refinement for the
emitted IVC state-transition descriptor (`ivcStateTransitionDescriptor`).

## What this file IS

`EffectVmEmitIvcStateTransition.lean` proves only PER-GATE facts — the two rejection teeth
(`ivc_rejects_tampered_published_hash`, `ivc_rejects_tampered_seed`) and the single-gate hash
lift (`ivc_step_is_hashed`), each stated over the per-window predicate `ivcWindowHolds`. This file
proves the missing WHOLE-DESCRIPTOR bridge: a trace SATISFYING the emitted descriptor via the
deployed acceptance predicate `Satisfied2` (the multi-table, whole-trace denotation) genuinely
COMPUTES an IVC hash-chain accumulation.

## The authored semantic relation (spec_status = NO_LEAN)

No proven Lean model of the IVC accumulator existed (the sibling `EffectVmEmitBundleFold.lean`
likewise carries only per-gate teeth). So §1 AUTHORS the functional spec:

* `extendAccumulatedHash hash old root step := hash [IVC_DOMAIN_TAG, old, root, step]` — the genuine
  single fold-step (`ivc.rs::extend_accumulated_hash`, `ivc.rs:231-242`);
* `ivcChain hash seed s roots` — the genuine multi-step IVC accumulator: fold a list of new state
  roots from `seed`, one per step, incrementing the step index. This is what the deployed AIR is
  meant to compute.

## The bridge (SAT_IMPLIES_SEM — the load-bearing direction)

Against a SOUND Poseidon2 chip table, `Satisfied2` of the descriptor forces the genuine relation:

* `ivc_sat_seeds_genuine_extension` — the FIRST row seeds the chain: `old_hash = pi[seed]`,
  `step = 1`, and its `new_hash` IS the genuine one-step extension of the published seed at step 1.
* `ivc_sat_publishes_genuine_extension` — the LAST row publishes: the published `accumulated_hash`
  (`pi[3]`) IS the genuine extension of the last row's `(old_hash, new_root)` at the published
  `step_count` (`pi[2]`). This is a functional statement about the PUBLIC interface — the published
  output equals a genuine Poseidon2 hash of the last fold step, lifted from the lookup + boundary.
* `ivc_single_step_refines_chain` — for a one-row trace the descriptor is a COMPLETE refinement of
  the authored fold spec: `pi[accumulated_hash] = ivcChain hash pi[seed] 1 [new_root]` and
  `pi[step_count] = 1`. The endpoint IS the fold's base case.

The genuineness lift (chip-lookup membership ⟹ real Poseidon2 hash) rides the named carrier
`ChipTableSound hash (t.tf .poseidon2)`, the same chip-soundness floor the ~15 hash-carrying
families ride. Sequential inter-row continuity is deliberately NOT enforced in-circuit (the hand
AIR omits the continuity gate for padding-safety, see the emit file); the bridge proves exactly the
descriptor's genuine endpoint content, not more.

## Non-vacuity (the anti-scar proof)

`§5` exhibits a CONCRETE inhabitant `demoTrace` (a one-step run seed `100` → root `7`) that
PROVABLY `Satisfied2` (`ivc_demo_accepts`), and the tampered variant `demoTraceBad` (published hash
forged) that PROVABLY FAILS `Satisfied2` (`ivc_demo_tampered_rejects` — the published-hash tooth
bites). Feeding the honest witness to the bridge recovers the genuine fold value
(`ivc_witness_refines`: `0 = ivcChain hash0 100 1 [7]`), so the hypothesis is inhabited AND the
conclusion is not a constant restatement.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 collision-resistance enters
ONLY through the named hypothesis `ChipTableSound hash (t.tf .poseidon2)`, never as an axiom. NEW
file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition

namespace Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint siteHoldsAll)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition

set_option autoImplicit false

/-! ## §1 — the authored functional spec: the genuine IVC hash-chain accumulator. -/

/-- **The genuine IVC fold-step.** Extend an accumulated hash by a new state root at a given step,
`extend_accumulated_hash = hash_many([IVC_DOMAIN_TAG, old_hash, new_root, step])`
(`ivc.rs:231-242`, `ivc.rs:617-620`). This is the per-row relation the deployed AIR enforces. -/
def extendAccumulatedHash (hash : List ℤ → ℤ) (oldHash newRoot step : ℤ) : ℤ :=
  hash [IVC_DOMAIN_TAG, oldHash, newRoot, step]

/-- **The genuine IVC accumulator (the multi-step reference computation).** Starting from `seed` at
step `s`, absorb the list of new state roots one per step, incrementing the step index each time.
`ivcChain hash seed s roots` is the accumulated hash after folding `roots`. This is THE functional
spec of `dregg-ivc-state-transition-v1`: the published `accumulated_hash` is meant to be a genuine
`ivcChain` of the sequence of fold-step roots from the seed. -/
def ivcChain (hash : List ℤ → ℤ) (seed : ℤ) : ℤ → List ℤ → ℤ
  | _, []           => seed
  | s, root :: rest => ivcChain hash (extendAccumulatedHash hash seed root s) (s + 1) rest

/-- The base case: a one-root fold is exactly one genuine extension. -/
theorem ivcChain_single (hash : List ℤ → ℤ) (seed s root : ℤ) :
    ivcChain hash seed s [root] = extendAccumulatedHash hash seed root s := by
  simp [ivcChain]

/-! ## §2 — the descriptor-constraint membership facts (the 5 enforced constraints). -/

theorem perRowHash_mem : perRowHash ∈ ivcStateTransitionDescriptor.constraints := by
  show perRowHash ∈ ivcConstraints; simp [ivcConstraints]

theorem firstStepIsOne_mem : firstStepIsOne ∈ ivcStateTransitionDescriptor.constraints := by
  show firstStepIsOne ∈ ivcConstraints; simp [ivcConstraints]

theorem firstSeedBind_mem : firstSeedBind ∈ ivcStateTransitionDescriptor.constraints := by
  show firstSeedBind ∈ ivcConstraints; simp [ivcConstraints]

theorem lastStepBind_mem : lastStepBind ∈ ivcStateTransitionDescriptor.constraints := by
  show lastStepBind ∈ ivcConstraints; simp [ivcConstraints]

theorem lastNewHashBind_mem : lastNewHashBind ∈ ivcStateTransitionDescriptor.constraints := by
  show lastNewHashBind ∈ ivcConstraints; simp [ivcConstraints]

/-! ## §3 — the per-constraint extraction lemmas from `Satisfied2` (whole-trace denotation). -/

/-- **Every row is a genuine hash step.** Against a sound chip table, `Satisfied2` forces each row's
`new_hash` column to be the genuine `hash([IVC_DOMAIN_TAG, old_hash, new_root, step])` — the
whole-trace analogue of `ivc_step_is_hashed`, extracted from `Satisfied2.rowConstraints`. -/
theorem ivc_row_hashed (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc Ivc.NEW_HASH_COL
      = hash [IVC_DOMAIN_TAG, (envAt t i).loc Ivc.OLD_HASH_COL,
              (envAt t i).loc Ivc.NEW_ROOT_COL, (envAt t i).loc Ivc.STEP_COL] := by
  have hc := hsat.rowConstraints i hi perRowHash perRowHash_mem
  simp only [perRowHash, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  have hkey := chip_lookup_sound hash (t.tf .poseidon2) hSound (envAt t i).loc
    [.const IVC_DOMAIN_TAG, .var Ivc.OLD_HASH_COL, .var Ivc.NEW_ROOT_COL, .var Ivc.STEP_COL]
    Ivc.NEW_HASH_COL (siteLaneCols Ivc.LANE1_COL)
    (by unfold CHIP_RATE; decide) hc
  simpa [EmittedExpr.eval] using hkey

/-- **First-row `step = 1`** — from `Satisfied2` (the row-0 boundary `step - 1 = 0`). -/
theorem ivc_first_step_one (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t)
    (hn : 0 < t.rows.length) :
    (envAt t 0).loc Ivc.STEP_COL = 1 := by
  have hc := hsat.rowConstraints 0 hn firstStepIsOne firstStepIsOne_mem
  simp only [firstStepIsOne, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have hb := hc (by decide)
  simp only [EmittedExpr.eval] at hb
  omega

/-- **First-row `old_hash = pi[seed]`** — from `Satisfied2` (the row-0 seed pin). -/
theorem ivc_first_seed_bind (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t)
    (hn : 0 < t.rows.length) :
    (envAt t 0).loc Ivc.OLD_HASH_COL = t.pub Ivc.PI_INITIAL_HASH := by
  have hc := hsat.rowConstraints 0 hn firstSeedBind firstSeedBind_mem
  simp only [firstSeedBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hc (by decide)

/-- **Last-row `step = pi[step_count]`** — from `Satisfied2` (the last-row step pin). -/
theorem ivc_last_step_bind (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t)
    (hn : 0 < t.rows.length) :
    (envAt t (t.rows.length - 1)).loc Ivc.STEP_COL = t.pub Ivc.PI_STEP_COUNT := by
  have hi : t.rows.length - 1 < t.rows.length := Nat.sub_lt hn Nat.one_pos
  have hc := hsat.rowConstraints (t.rows.length - 1) hi lastStepBind lastStepBind_mem
  simp only [lastStepBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    simp [Nat.sub_add_cancel hn]
  exact hc hlast

/-- **Last-row `new_hash = pi[accumulated_hash]`** — from `Satisfied2` (the published-hash pin, the
soundness anchor). -/
theorem ivc_last_newhash_bind (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t)
    (hn : 0 < t.rows.length) :
    (envAt t (t.rows.length - 1)).loc Ivc.NEW_HASH_COL = t.pub Ivc.PI_ACC_HASH := by
  have hi : t.rows.length - 1 < t.rows.length := Nat.sub_lt hn Nat.one_pos
  have hc := hsat.rowConstraints (t.rows.length - 1) hi lastNewHashBind lastNewHashBind_mem
  simp only [lastNewHashBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    simp [Nat.sub_add_cancel hn]
  exact hc hlast

/-! ## §4 — the WHOLE-DESCRIPTOR bridge (SAT_IMPLIES_SEM). -/

/-- **`ivc_sat_publishes_genuine_extension` — the publish endpoint.** For any nonempty trace, against
a sound chip table, `Satisfied2` forces the published `accumulated_hash` (`pi[3]`) to be the GENUINE
Poseidon2 extension of the last fold step's `(old_hash, new_root)` at the published `step_count`
(`pi[2]`). The published output is a genuine hash of the last step, not a prover-chosen value. -/
theorem ivc_sat_publishes_genuine_extension (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hn : 0 < t.rows.length)
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t) :
    t.pub Ivc.PI_ACC_HASH
      = extendAccumulatedHash hash
          ((envAt t (t.rows.length - 1)).loc Ivc.OLD_HASH_COL)
          ((envAt t (t.rows.length - 1)).loc Ivc.NEW_ROOT_COL)
          (t.pub Ivc.PI_STEP_COUNT) := by
  have hi : t.rows.length - 1 < t.rows.length := Nat.sub_lt hn Nat.one_pos
  have hhash := ivc_row_hashed hash t minit mfin maddrs hSound hsat (t.rows.length - 1) hi
  have hstep := ivc_last_step_bind hash t minit mfin maddrs hsat hn
  have hpub := ivc_last_newhash_bind hash t minit mfin maddrs hsat hn
  rw [← hpub, hhash, hstep]
  rfl

/-- **`ivc_sat_seeds_genuine_extension` — the seed endpoint.** For any nonempty trace, against a
sound chip table, `Satisfied2` forces the FIRST row to seed the chain: its `old_hash` is the
published seed `pi[0]`, its `step` is 1, and its `new_hash` IS the genuine one-step extension of the
published seed at step 1. -/
theorem ivc_sat_seeds_genuine_extension (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hn : 0 < t.rows.length)
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t) :
    (envAt t 0).loc Ivc.NEW_HASH_COL
        = extendAccumulatedHash hash (t.pub Ivc.PI_INITIAL_HASH)
            ((envAt t 0).loc Ivc.NEW_ROOT_COL) 1
      ∧ (envAt t 0).loc Ivc.OLD_HASH_COL = t.pub Ivc.PI_INITIAL_HASH
      ∧ (envAt t 0).loc Ivc.STEP_COL = 1 := by
  have hhash := ivc_row_hashed hash t minit mfin maddrs hSound hsat 0 hn
  have hseed := ivc_first_seed_bind hash t minit mfin maddrs hsat hn
  have hstep := ivc_first_step_one hash t minit mfin maddrs hsat hn
  refine ⟨?_, hseed, hstep⟩
  rw [hhash, hseed, hstep]
  rfl

/-- **`ivc_single_step_refines_chain` — the COMPLETE functional refinement (base case).** For a
ONE-row trace, against a sound chip table, the published `accumulated_hash` EQUALS the genuine IVC
fold `ivcChain hash pi[seed] 1 [new_root]`, and the published `step_count` is 1. The whole
descriptor refines the authored `ivcChain` spec at its base case. -/
theorem ivc_single_step_refines_chain (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (h1 : t.rows.length = 1)
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t) :
    t.pub Ivc.PI_ACC_HASH
        = ivcChain hash (t.pub Ivc.PI_INITIAL_HASH) 1 [(envAt t 0).loc Ivc.NEW_ROOT_COL]
      ∧ t.pub Ivc.PI_STEP_COUNT = 1 := by
  have hn : 0 < t.rows.length := by rw [h1]; exact Nat.one_pos
  have hlast0 : t.rows.length - 1 = 0 := by rw [h1]
  have hpublish := ivc_sat_publishes_genuine_extension hash t minit mfin maddrs hn hSound hsat
  rw [hlast0] at hpublish
  have hseed := ivc_first_seed_bind hash t minit mfin maddrs hsat hn
  have hstepbind := ivc_last_step_bind hash t minit mfin maddrs hsat hn
  rw [hlast0] at hstepbind
  have hstep1 := ivc_first_step_one hash t minit mfin maddrs hsat hn
  have hsc : t.pub Ivc.PI_STEP_COUNT = 1 := by rw [← hstepbind, hstep1]
  refine ⟨?_, hsc⟩
  rw [hpublish, hseed, hsc, ivcChain_single]

/-! ## §5 — non-vacuity: a concrete satisfying witness AND a concrete failing one. -/

/-- A constant abstract hash: any value serves the witness (the model quantifies over `hash`; the
concrete inhabitant only needs SOME hash making `Satisfied2` inhabited). -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The concrete one-step run row: `step = 1`, `old_hash = 100` (the seed), `new_root = 7`,
`new_hash = 0 = hash0([IVC_DOMAIN_TAG, 100, 7, 1])`, chip lanes `0`. -/
def demoRow0 : Assignment :=
  fun v => if v = 0 then 1 else if v = 1 then 100 else if v = 2 then 7 else 0

/-- The row's evaluated per-row chip-lookup tuple (carried by the Poseidon2 chip table). -/
def ivcTupleAt (a : Assignment) : List ℤ :=
  (chipLookupTuple [.const IVC_DOMAIN_TAG, .var Ivc.OLD_HASH_COL, .var Ivc.NEW_ROOT_COL,
      .var Ivc.STEP_COL] Ivc.NEW_HASH_COL (siteLaneCols Ivc.LANE1_COL)).map (·.eval a)

/-- The witness trace family: the Poseidon2 chip table carries EXACTLY the row's evaluated tuple
(so the per-row lookup holds); every other table is empty (no mem/map content). -/
def demoTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [ivcTupleAt demoRow0]
  | _          => []

/-- The public inputs: seed `pi[0] = 100`, step-count `pi[2] = 1`, published hash `pi[3] = 0`. -/
def demoPub : Assignment :=
  fun k => if k = 0 then 100 else if k = 2 then 1 else 0

/-- The concrete one-row IVC trace (an honest single fold step). -/
def demoTrace : VmTrace := { rows := [demoRow0], pub := demoPub, tf := demoTf }

theorem memOpsOf_ivc : memOpsOf ivcStateTransitionDescriptor = [] := rfl
theorem mapOpsOf_ivc : mapOpsOf ivcStateTransitionDescriptor = [] := rfl
theorem memLog_ivc (t : VmTrace) : memLog ivcStateTransitionDescriptor t = [] := by
  simp [memLog, memOpsOf_ivc]
theorem mapLog_ivc (t : VmTrace) : mapLog ivcStateTransitionDescriptor t = [] := by
  simp [mapLog, mapOpsOf_ivc]

/-- **The witness chip table is SOUND.** Its single row IS a genuine `chipRow` of the arity-4
absorb `[IVC_DOMAIN_TAG, 100, 7, 1]` (with the seven permutation lanes `0`). -/
theorem demo_chip_sound : ChipTableSound hash0 (demoTf .poseidon2) := by
  intro r hr
  rw [show demoTf .poseidon2 = [ivcTupleAt demoRow0] from rfl, List.mem_singleton] at hr
  subst hr
  exact ⟨[IVC_DOMAIN_TAG, 100, 7, 1], List.replicate 7 0, by decide, by decide, by decide⟩

set_option maxRecDepth 4096 in
/-- **`ivc_demo_accepts` — a CONCRETE `Satisfied2` inhabitant.** The honest one-step run PROVABLY
satisfies the emitted descriptor: the per-row lookup holds by membership, the four boundaries hold
(`step = 1`, `old_hash = 100`, `step = step_count = 1`, `new_hash = accumulated_hash = 0`), and the
memory legs collapse to the empty log (the descriptor declares no mem/map ops). -/
theorem ivc_demo_accepts :
    Satisfied2 hash0 ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] demoTrace where
  rowConstraints := by
    intro i hi c hc
    have hi1 : i < 1 := hi
    clear hi
    simp only [ivcStateTransitionDescriptor, ivcConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        perRowHash, firstStepIsOne, firstSeedBind, lastStepBind, lastNewHashBind, demoTrace] <;>
      decide
  rowHashes := by
    intro i _
    rw [show ivcStateTransitionDescriptor.hashSites = ([] : List _) from rfl]
    exact True.intro
  rowRanges := by
    intro i _ r hr
    rw [show ivcStateTransitionDescriptor.ranges = ([] : List _) from rfl] at hr
    simp at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_ivc] at hop; simp at hop
  memDisciplined := by rw [memLog_ivc]; trivial
  memBalanced := by rw [memLog_ivc]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_ivc]; rfl
  mapTableFaithful := by rw [mapLog_ivc]; rfl

/-- The public inputs of the TAMPERED run: the published hash `pi[3]` is forged to `1 ≠ 0`. -/
def demoPubBad : Assignment :=
  fun k => if k = 0 then 100 else if k = 2 then 1 else if k = 3 then 1 else 0

/-- The tampered trace: honest row, but the published `accumulated_hash` disagrees with `new_hash`. -/
def demoTraceBad : VmTrace := { rows := [demoRow0], pub := demoPubBad, tf := demoTf }

/-- **`ivc_demo_tampered_rejects` — the published-hash tooth BITES at the `Satisfied2` level.** The
tampered run cannot satisfy the descriptor: the last-row boundary `new_hash = accumulated_hash`
forces `0 = 1`, a contradiction. (Companion of the honest `ivc_demo_accepts`: the acceptance
predicate genuinely SEPARATES honest from forged.) -/
theorem ivc_demo_tampered_rejects :
    ¬ Satisfied2 hash0 ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] demoTraceBad := by
  intro h
  have hc := h.rowConstraints 0 (by decide) lastNewHashBind lastNewHashBind_mem
  simp only [lastNewHashBind, VmConstraint2.holdsAt, VmConstraint.holdsVm, demoTraceBad] at hc
  exact absurd (hc (by decide)) (by decide)

/-- **`ivc_witness_refines` — the bridge FIRES on the concrete honest witness.** Feeding `demoTrace`
to `ivc_single_step_refines_chain` recovers the genuine fold value: the published accumulated hash
equals `ivcChain hash0 100 1 [7]`. The hypothesis is inhabited and the conclusion is a genuine
computation, not a tautology. -/
theorem ivc_witness_refines :
    demoTrace.pub Ivc.PI_ACC_HASH
      = ivcChain hash0 (demoTrace.pub Ivc.PI_INITIAL_HASH) 1
          [(envAt demoTrace 0).loc Ivc.NEW_ROOT_COL] :=
  (ivc_single_step_refines_chain hash0 demoTrace (fun _ => 0) (fun _ => (0, 0)) [] rfl
    demo_chip_sound ivc_demo_accepts).1

/-- The recovered value is the concrete endpoint `0` over the read seed `100` and root `7`. -/
theorem ivc_witness_value :
    demoTrace.pub Ivc.PI_ACC_HASH = 0
      ∧ demoTrace.pub Ivc.PI_INITIAL_HASH = 100
      ∧ (envAt demoTrace 0).loc Ivc.NEW_ROOT_COL = 7 := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## §6 — axiom hygiene. -/

#assert_axioms ivc_row_hashed
#assert_axioms ivc_sat_publishes_genuine_extension
#assert_axioms ivc_sat_seeds_genuine_extension
#assert_axioms ivc_single_step_refines_chain
#assert_axioms ivc_demo_accepts
#assert_axioms ivc_demo_tampered_rejects
#assert_axioms ivc_witness_refines

end Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRefine
