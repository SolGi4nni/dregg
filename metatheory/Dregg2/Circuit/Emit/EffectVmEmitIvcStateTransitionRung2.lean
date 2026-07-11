/-
# `EffectVmEmitIvcStateTransitionRung2` — the RUNG-2 MULTI-STEP no-forgery for the emitted IVC
state-transition descriptor (`ivcStateTransitionDescriptor`), and the precise EMIT-GAP it exposes.

## What RUNG 1 concluded, and the residual it left

`EffectVmEmitIvcStateTransitionRefine.lean` (RUNG 1) proved the genuine endpoint content of the
descriptor against the named Poseidon2 chip-soundness carrier `ChipTableSound`:

* `ivc_row_hashed` — EVERY row's `new_hash` IS the genuine `hash [IVC_DOMAIN_TAG, old, root, step]`;
* `ivc_sat_seeds_genuine_extension` / `ivc_sat_publishes_genuine_extension` — the FIRST row seeds and
  the LAST row publishes a genuine one-step extension;
* `ivc_single_step_refines_chain` — for a ONE-row trace the published `accumulated_hash` IS the
  genuine IVC fold `ivcChain hash pi[seed] 1 [new_root]` (the base case, complete).

The GENUINE multi-step no-forgery — `accept ⟹ pi[accumulated_hash] = ivcChain hash pi[seed] 1
(rootsOf t)` for a trace of ANY length — is NOT concluded by Rung 1, and provably cannot be: the
emitted descriptor DELIBERATELY omits the two inter-row transition gates (`EffectVmEmit…Ivc…`,
"Faithful omission"): the copy-forward continuity `old_hashᵢ₊₁ = new_hashᵢ` and the step-increment
`stepᵢ₊₁ = stepᵢ + 1`. The deployed `StateTransitionAir` drops them because the STARK pads by
DUPLICATING the last row (an ungated transition gate would fire on the padded clone and reject honest
traces). The published `accumulated_hash` is a SINGLE hash of the last `(old_hash, new_root, step)`
triple — NOT a fold-commitment over the whole chain (contrast DFA-routing, whose `route_commitment`
IS a running fold, letting its Rung-2 discharge the terminal gap by collision-resistance). So there
is NO whole-chain commitment for a CR anchor to bind against, and the intermediate accumulator is
free: a multi-row prover can publish a genuine hash of a chain that DID NOT continue from the seed.

## What THIS file proves (RUNG-2 PARTIAL)

`ivc_multi_refines_chain` — against the SAME named carrier `ChipTableSound` (per-row Poseidon2 hash
genuineness) PLUS the two omitted gates supplied as explicit hypotheses `IvcContinuity` /
`IvcStepIncrement`, under the boundary canonicality envelope `IvcTraceCanon` (the deployed
range-check invariant Rung 1 threads — boundary pins now hold only `≡ 0 [ZMOD p]`, and reading an ℤ
equality back off a mod-`p` pin needs both sides canonical in `[0, p)`), a satisfying trace of ANY
length genuinely computes the IVC accumulator:
`pi[accumulated_hash] = ivcChain hash pi[seed] 1 (rootsOf t)` and `pi[step_count] = length`. This is
the genuine multi-step no-forgery, strictly generalising Rung 1's single-row base case.

The remaining gap is therefore NOT a crypto residual — it is an EMIT-FIX: the descriptor must gain a
`windowGate` enforcing `next.old_hash − new_hash = 0` and `next.step − step − 1 = 0`, GUARDED (as
DFA-routing's `copyForwardWindow`/`continuityWindow` are) so it never fires on the genuine→padding
transition. Named precisely, its padding-safety obligation intact.

## Non-vacuity + load-bearing anchor (the anti-scar proofs)

* `ivc_multi_fires` — a CONCRETE honest 2-row run over an abstract range-canonical `hash` (outputs
  in `[0, p)`, the chip's range-check invariant) meets EVERY hypothesis (Satisfied2, ChipTableSound,
  `IvcTraceCanon`, both gates non-vacuously at `i = 0`) and the discharged conclusion FIRES with the
  genuine nested value `hash [TAG, hash [TAG, 100, 7, 1], 9, 2]`.
* `ivc_continuity_is_load_bearing` — a CONCRETE 2-row CHEAT (row 1's `old_hash` set to `hash [TAG,
  200, 7, 1] ≠ new_hash₀`) PROVABLY `Satisfied2`s AND rides a SOUND chip table, yet
  `pi[accumulated_hash] ≠ ivcChain hash pi[seed] 1 (rootsOf t)`. So Rung 1's hypotheses
  (`Satisfied2 ∧ ChipTableSound`) ALONE cannot force the chain — the continuity gate is a real
  filter, not free. The hypothesis set of `ivc_multi_refines_chain` is thus non-vacuous AND its
  added gates are load-bearing (not a `P → P` laundering).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 hash genuineness rides ONLY the
named `ChipTableSound` hypothesis; the cheat's value-separation rides ONLY the named
`Function.Injective hash` (the reference CR realisation). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRefine

namespace Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition
open Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRefine

set_option autoImplicit false

/-! ## §0 — trace-index plumbing (local mirrors of the `DfaRoutingRefine` helpers). -/

variable {t : VmTrace}

/-- `getD` on an in-bounds index is `getElem`. -/
theorem getD_row {i : Nat} (hi : i < t.rows.length) : t.rows.getD i zeroAsg = t.rows[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The current-row environment's `loc` is the trace row (in-bounds). -/
theorem envAt_loc {i : Nat} (hi : i < t.rows.length) : (envAt t i).loc = t.rows[i]'hi :=
  getD_row hi

/-- The current-row environment's `nxt` is the next trace row (in-bounds). -/
theorem envAt_nxt {i : Nat} (hi : i + 1 < t.rows.length) : (envAt t i).nxt = t.rows[i + 1]'hi :=
  getD_row hi

/-- `getLast (a :: l) = getLast l` (up to the proof-irrelevant non-emptiness witnesses). -/
theorem getLast_cons' (a : Assignment) (l : List Assignment) (h : l ≠ []) (h2 : a :: l ≠ []) :
    (a :: l).getLast h2 = l.getLast h := List.getLast_cons h

/-! ## §1 — the two OMITTED transition gates, as explicit predicates.

These are exactly the inter-row transitions the deployed `StateTransitionAir` (and hence the emitted
descriptor) drops for padding-safety. A window gate reads the CURRENT row (`loc`) and the NEXT row
(`nxt`); these predicates phrase the gates in that window form. -/

/-- **The copy-forward continuity gate** (omitted from the descriptor): each row's `old_hash` is the
previous row's `new_hash`, so the accumulator genuinely threads across the trace. -/
def IvcContinuity (t : VmTrace) : Prop :=
  ∀ i, i + 1 < t.rows.length →
    (envAt t i).nxt Ivc.OLD_HASH_COL = (envAt t i).loc Ivc.NEW_HASH_COL

/-- **The step-increment gate** (omitted from the descriptor): the fold-step index advances by one
each row, so the published chain uses the canonical steps `1, 2, …, n`. -/
def IvcStepIncrement (t : VmTrace) : Prop :=
  ∀ i, i + 1 < t.rows.length →
    (envAt t i).nxt Ivc.STEP_COL = (envAt t i).loc Ivc.STEP_COL + 1

/-- The new state root a row reads (the IVC fold's per-step input). -/
def nextRoot (a : Assignment) : ℤ := a Ivc.NEW_ROOT_COL

/-- The sequence of new state roots the trace reads, one per row (the IVC fold's input list). -/
def rootsOf (t : VmTrace) : List ℤ := t.rows.map nextRoot

/-- The `ivcChain` cons step, as an `xs`-abstract rewrite (fold one root, advance the step index). -/
theorem ivcChain_cons (hash : List ℤ → ℤ) (seed base x : ℤ) (xs : List ℤ) :
    ivcChain hash seed base (x :: xs)
      = ivcChain hash (extendAccumulatedHash hash seed x base) (base + 1) xs := by
  simp only [ivcChain]

/-! ## §2 — `ivcChain` snoc-free left fold: the last row folds the whole prefix.

`newhash_is_chain` is the pure list-recursion heart: a list of row assignments whose per-row
`new_hash` is genuine (chip soundness), whose accumulators copy-forward (continuity), whose steps
count `base, base+1, …` (step-increment), and whose first `old_hash` is `seed`, has its LAST row's
`new_hash` equal to the genuine `ivcChain hash seed base (rootsOf)`. Mirrors `DfaRoutingRefine`'s
`continuous_map` / the template's `accumulates_map`. -/

theorem newhash_is_chain (hash : List ℤ → ℤ) :
    ∀ (l : List Assignment) (seed base : ℤ)
      (_ : ∀ i (hi : i < l.length),
        (l[i]'hi) Ivc.NEW_HASH_COL
          = hash [IVC_DOMAIN_TAG, (l[i]'hi) Ivc.OLD_HASH_COL, (l[i]'hi) Ivc.NEW_ROOT_COL,
                  (l[i]'hi) Ivc.STEP_COL])
      (_ : ∀ i (hi : i + 1 < l.length),
        (l[i + 1]'hi) Ivc.OLD_HASH_COL = (l[i]'(Nat.lt_of_succ_lt hi)) Ivc.NEW_HASH_COL)
      (_ : ∀ i (hi : i < l.length), (l[i]'hi) Ivc.STEP_COL = base + (i : ℤ))
      (_ : ∀ (hn : 0 < l.length), (l[0]'hn) Ivc.OLD_HASH_COL = seed)
      (hne : l ≠ []),
      (l.getLast hne) Ivc.NEW_HASH_COL = ivcChain hash seed base (l.map nextRoot)
  | [], _, _, _, _, _, _, hne => absurd rfl hne
  | [a], seed, base, hrow, _, hstep, hseed, _ => by
      simp only [List.getLast_singleton, List.map_cons, List.map_nil]
      rw [ivcChain_single]
      have hr0 := hrow 0 (by simp)
      have hs0 := hseed (by simp)
      have hst0 := hstep 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.cast_zero, add_zero] at hr0 hs0 hst0
      rw [hr0, hs0, hst0]
      rfl
  | a :: b :: rest, seed, base, hrow, hcont, hstep, hseed, hne => by
      -- the sublist hypotheses (index-shifted by one)
      have hrow' : ∀ i (hi : i < (b :: rest).length),
          ((b :: rest)[i]'hi) Ivc.NEW_HASH_COL
            = hash [IVC_DOMAIN_TAG, ((b :: rest)[i]'hi) Ivc.OLD_HASH_COL,
                    ((b :: rest)[i]'hi) Ivc.NEW_ROOT_COL, ((b :: rest)[i]'hi) Ivc.STEP_COL] :=
        fun i hi => by
          have h := hrow (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
          simpa only [List.getElem_cons_succ] using h
      have hcont' : ∀ i (hi : i + 1 < (b :: rest).length),
          ((b :: rest)[i + 1]'hi) Ivc.OLD_HASH_COL
            = ((b :: rest)[i]'(Nat.lt_of_succ_lt hi)) Ivc.NEW_HASH_COL :=
        fun i hi => by
          have h := hcont (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
          simpa only [List.getElem_cons_succ] using h
      have hstep' : ∀ i (hi : i < (b :: rest).length),
          ((b :: rest)[i]'hi) Ivc.STEP_COL = (base + 1) + (i : ℤ) :=
        fun i hi => by
          have h := hstep (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
          simp only [List.getElem_cons_succ] at h
          rw [h]; push_cast; ring
      have hr0 := hrow 0 (by simp)
      have hs0 := hseed (by simp)
      have hst0 := hstep 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.cast_zero, add_zero] at hr0 hs0 hst0
      have hkey : (a Ivc.NEW_HASH_COL) = extendAccumulatedHash hash seed (nextRoot a) base := by
        rw [hr0, hs0, hst0]; rfl
      have hseed' : ∀ (hn : 0 < (b :: rest).length),
          ((b :: rest)[0]'hn) Ivc.OLD_HASH_COL = a Ivc.NEW_HASH_COL :=
        fun _ => by
          have h := hcont 0 (by simp only [List.length_cons]; omega)
          simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using h
      rw [getLast_cons' a (b :: rest) (by simp) hne, List.map_cons, ivcChain_cons, ← hkey]
      exact newhash_is_chain hash (b :: rest) (a Ivc.NEW_HASH_COL) (base + 1)
        hrow' hcont' hstep' hseed' (by simp)

/-! ## §3 — THE RUNG-2 MULTI-STEP DISCHARGE. -/

/-- **`ivc_multi_refines_chain` — the genuine multi-step IVC no-forgery.** A trace `t` of ANY length
that `Satisfied2`s the emitted descriptor, rides a SOUND Poseidon2 chip table (`hSound` — the named
`ChipTableSound` carrier), and additionally meets the two omitted transition gates `IvcContinuity` /
`IvcStepIncrement`, and rides the boundary canonicality envelope `IvcTraceCanon` (the deployed
range-check invariant — the mod-`p` boundary pins collapse to ℤ equalities only on canonical
representatives), has its published `accumulated_hash` (`pi[3]`) EQUAL to the genuine IVC fold
`ivcChain hash pi[seed] 1 (rootsOf t)`, and its published `step_count` (`pi[2]`) equal to the row
count. The published output cannot be a forged accumulation of a chain that did not thread the seed. -/
theorem ivc_multi_refines_chain (hash : List ℤ → ℤ) (t : VmTrace)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hne : t.rows ≠ [])
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash ivcStateTransitionDescriptor minit mfin maddrs t)
    (hcanon : IvcTraceCanon t)
    (hcont : IvcContinuity t)
    (hstepinc : IvcStepIncrement t) :
    t.pub Ivc.PI_ACC_HASH
        = ivcChain hash (t.pub Ivc.PI_INITIAL_HASH) 1 (rootsOf t)
      ∧ t.pub Ivc.PI_STEP_COUNT = (t.rows.length : ℤ) := by
  have hpos : 0 < t.rows.length := List.length_pos_iff.mpr hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  -- (a) per-row hash genuineness, continuity, step-count, seed — pushed to `getElem` form
  have hrow : ∀ i (hi : i < t.rows.length),
      (t.rows[i]'hi) Ivc.NEW_HASH_COL
        = hash [IVC_DOMAIN_TAG, (t.rows[i]'hi) Ivc.OLD_HASH_COL, (t.rows[i]'hi) Ivc.NEW_ROOT_COL,
                (t.rows[i]'hi) Ivc.STEP_COL] := fun i hi => by
    have h := ivc_row_hashed hash t minit mfin maddrs hSound hsat i hi
    rwa [envAt_loc hi] at h
  have hcont' : ∀ i (hi : i + 1 < t.rows.length),
      (t.rows[i + 1]'hi) Ivc.OLD_HASH_COL = (t.rows[i]'(Nat.lt_of_succ_lt hi)) Ivc.NEW_HASH_COL :=
    fun i hi => by
      have h := hcont i hi
      rwa [envAt_nxt hi, envAt_loc (Nat.lt_of_succ_lt hi)] at h
  have hstep : ∀ i (hi : i < t.rows.length), (t.rows[i]'hi) Ivc.STEP_COL = 1 + (i : ℤ) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have h := ivc_first_step_one hash t minit mfin maddrs hsat hi (hcanon.1 0 hi).1
      rw [envAt_loc hi] at h
      simpa using h
    | succ k ih =>
      intro hi
      have hkl : k < t.rows.length := Nat.lt_of_succ_lt hi
      have hinc := hstepinc k hi
      rw [envAt_nxt hi, envAt_loc hkl] at hinc
      rw [hinc, ih hkl]; push_cast; ring
  have hseed : ∀ (hn : 0 < t.rows.length),
      (t.rows[0]'hn) Ivc.OLD_HASH_COL = t.pub Ivc.PI_INITIAL_HASH := fun hn => by
    have h := ivc_first_seed_bind hash t minit mfin maddrs hsat hn (hcanon.1 0 hn).2.1 hcanon.2.1
    rwa [envAt_loc hn] at h
  -- (b) the list-recursion heart: last new_hash IS the genuine ivcChain
  have hchain := newhash_is_chain hash t.rows (t.pub Ivc.PI_INITIAL_HASH) 1 hrow hcont' hstep hseed hne
  -- (c) the last new_hash is pinned to the published accumulated_hash (B/last boundary)
  have hpub := ivc_last_newhash_bind hash t minit mfin maddrs hsat hpos
    (hcanon.1 (t.rows.length - 1) hlt).2.2 hcanon.2.2.2
  rw [envAt_loc hlt] at hpub
  have hgl : (t.rows.getLast hne) Ivc.NEW_HASH_COL = (t.rows[t.rows.length - 1]'hlt) Ivc.NEW_HASH_COL := by
    rw [List.getLast_eq_getElem hne]
  refine ⟨?_, ?_⟩
  · rw [← hpub, ← hgl, hchain]; rfl
  · -- step_count = length: last step = 1 + (length-1) = length
    have hsc := ivc_last_step_bind hash t minit mfin maddrs hsat hpos
      (hcanon.1 (t.rows.length - 1) hlt).1 hcanon.2.2.1
    rw [envAt_loc hlt] at hsc
    have hslast := hstep (t.rows.length - 1) hlt
    rw [← hsc, hslast]
    have : 1 ≤ t.rows.length := hpos
    omega

/-! ## §4 — non-vacuity, FIRING half (1-row, from the Rung-1 witness).

The Rung-1 honest witness `demoTrace` (one seed-`100` → root-`7` step over `hash0`) meets EVERY
hypothesis of `ivc_multi_refines_chain` — the two omitted gates hold VACUOUSLY on a one-row trace —
so the discharge FIRES, recovering the genuine one-step fold value. -/

theorem ivc_multi_fires_demo :
    demoTrace.pub Ivc.PI_ACC_HASH
        = ivcChain hash0 (demoTrace.pub Ivc.PI_INITIAL_HASH) 1 (rootsOf demoTrace)
      ∧ demoTrace.pub Ivc.PI_STEP_COUNT = (demoTrace.rows.length : ℤ) :=
  ivc_multi_refines_chain hash0 demoTrace (fun _ => 0) (fun _ => (0, 0)) []
    (by simp [demoTrace]) demo_chip_sound ivc_demo_accepts demoTrace_canon
    (by intro i hi; simp only [demoTrace, List.length_cons, List.length_nil] at hi; omega)
    (by intro i hi; simp only [demoTrace, List.length_cons, List.length_nil] at hi; omega)

/-- The recovered one-step value is the concrete endpoint `0` over seed `100`, root `7`, and the read
root list `[7]`. -/
theorem ivc_multi_fires_demo_value :
    demoTrace.pub Ivc.PI_ACC_HASH = 0
      ∧ rootsOf demoTrace = [7]
      ∧ ivcChain hash0 (demoTrace.pub Ivc.PI_INITIAL_HASH) 1 (rootsOf demoTrace) = 0 := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## §5 — the 2-row abstract-hash constructions (honest witness + cheat).

Both traces genuinely hash EVERY row (so a SOUND chip table + `Satisfied2` hold); they differ ONLY in
row 1's `old_hash`. The honest trace threads it (continuity holds); the cheat forges it to a hash of a
DIFFERENT seed, breaking continuity — and thereby the published chain. -/

/-- Column list → assignment (mirrors the sibling refine files). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

section TwoRow
variable (hash : List ℤ → ℤ)

/-- Row 0 (shared by honest + cheat): `step=1, old=100 (seed), root=7, new=hash[TAG,100,7,1]`. -/
def wRow0 : Assignment :=
  rowOf [1, 100, 7, hash [IVC_DOMAIN_TAG, 100, 7, 1], 0, 0, 0, 0, 0, 0, 0]

/-- Honest row 1: `old = new_hash₀` (continuity holds), `root=9`, genuine `new_hash`. -/
def honRow1 : Assignment :=
  rowOf [2, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9,
         hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2], 0, 0, 0, 0, 0, 0, 0]

/-- Cheat row 1: `old = hash[TAG,200,7,1] ≠ new_hash₀` (continuity BROKEN), `root=9`, genuine
`new_hash` of the FORGED `old`. -/
def cheatRow1 : Assignment :=
  rowOf [2, hash [IVC_DOMAIN_TAG, 200, 7, 1], 9,
         hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 200, 7, 1], 9, 2], 0, 0, 0, 0, 0, 0, 0]

/-- Honest public inputs: seed `100`, step-count `2`, published hash = the genuine 2-step fold. -/
def honPub : Assignment :=
  rowOf [100, 0, 2, hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2]]

/-- Cheat public inputs: seed `100`, step-count `2`, published hash = the FORGED last-row hash. -/
def cheatPub : Assignment :=
  rowOf [100, 0, 2, hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 200, 7, 1], 9, 2]]

/-- Honest chip table: the two rows' genuine per-row lookup tuples. -/
def honTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [ivcTupleAt (wRow0 hash), ivcTupleAt (honRow1 hash)]
  | _          => []

/-- Cheat chip table: the two rows' genuine per-row lookup tuples (each row IS genuinely hashed). -/
def cheatTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [ivcTupleAt (wRow0 hash), ivcTupleAt (cheatRow1 hash)]
  | _          => []

/-- The honest 2-row IVC trace. -/
def honTrace : VmTrace := { rows := [wRow0 hash, honRow1 hash], pub := honPub hash, tf := honTf hash }

/-- The cheating 2-row IVC trace. -/
def cheatTrace : VmTrace :=
  { rows := [wRow0 hash, cheatRow1 hash], pub := cheatPub hash, tf := cheatTf hash }

/-- **The honest chip table is SOUND** — each row IS a genuine arity-4 `chipRow` of the permutation. -/
theorem honTf_sound : ChipTableSound hash ((honTrace hash).tf .poseidon2) := by
  intro r hr
  simp only [honTrace, honTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[IVC_DOMAIN_TAG, 100, 7, 1], List.replicate 7 0, by simp [CHIP_RATE], by decide, rfl⟩
  · exact ⟨[IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2], List.replicate 7 0,
      by simp [CHIP_RATE], by decide, rfl⟩

/-- **The cheat chip table is SOUND** — the forgery is in continuity, NOT in the hashing: every row is
still a genuine arity-4 `chipRow`. -/
theorem cheatTf_sound : ChipTableSound hash ((cheatTrace hash).tf .poseidon2) := by
  intro r hr
  simp only [cheatTrace, cheatTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[IVC_DOMAIN_TAG, 100, 7, 1], List.replicate 7 0, by simp [CHIP_RATE], by decide, rfl⟩
  · exact ⟨[IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 200, 7, 1], 9, 2], List.replicate 7 0,
      by simp [CHIP_RATE], by decide, rfl⟩

/-- **The honest trace `Satisfied2`s the descriptor** — the two per-row lookups by membership in the
sound chip table, the row-0/last-row boundary pins met by construction. -/
theorem honTrace_satisfied2 :
    Satisfied2 hash ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] (honTrace hash) where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    clear hi
    simp only [ivcStateTransitionDescriptor, ivcConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        perRowHash, firstStepIsOne, firstSeedBind, lastStepBind, lastNewHashBind,
        honTrace, honTf, envAt, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq,
        reduceCtorEq] <;>
      first
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | trivial
        | simp [wRow0, honRow1, honPub, rowOf, EmittedExpr.eval, Ivc.STEP_COL, Ivc.OLD_HASH_COL,
            Ivc.NEW_HASH_COL, Ivc.PI_INITIAL_HASH, Ivc.PI_STEP_COUNT, Ivc.PI_ACC_HASH]
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

/-- **The cheat trace `Satisfied2`s the descriptor** — identical shape to the honest one; the broken
continuity is INVISIBLE to `Satisfied2` (no continuity gate exists), which is precisely the point. -/
theorem cheatTrace_satisfied2 :
    Satisfied2 hash ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] (cheatTrace hash) where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    clear hi
    simp only [ivcStateTransitionDescriptor, ivcConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        perRowHash, firstStepIsOne, firstSeedBind, lastStepBind, lastNewHashBind,
        cheatTrace, cheatTf, envAt, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq,
        reduceCtorEq] <;>
      first
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | trivial
        | simp [wRow0, cheatRow1, cheatPub, rowOf, EmittedExpr.eval, Ivc.STEP_COL, Ivc.OLD_HASH_COL,
            Ivc.NEW_HASH_COL, Ivc.PI_INITIAL_HASH, Ivc.PI_STEP_COUNT, Ivc.PI_ACC_HASH]
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

/-- **The honest trace meets continuity** (non-vacuously at `i = 0`: row 1's `old_hash` IS row 0's
`new_hash`). -/
theorem honTrace_continuity : IvcContinuity (honTrace hash) := by
  intro i hi
  simp only [honTrace, List.length_cons, List.length_nil] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp [honTrace, envAt, honRow1, wRow0, rowOf, Ivc.OLD_HASH_COL, Ivc.NEW_HASH_COL]

/-- **The honest trace meets step-increment** (non-vacuously at `i = 0`: `step₁ = 2 = step₀ + 1`). -/
theorem honTrace_stepinc : IvcStepIncrement (honTrace hash) := by
  intro i hi
  simp only [honTrace, List.length_cons, List.length_nil] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp [honTrace, envAt, honRow1, wRow0, rowOf, Ivc.STEP_COL]

/-- **The honest 2-row trace is CANONICAL**, given the hash outputs land in `[0, p)` (the deployed
Poseidon2 chip writes canonical BabyBear representatives — `hcanonHash` names exactly that
range-check invariant; it is NOT free for an arbitrary `hash`): every boundary-pinned cell (`step ∈
{1, 2}`, `old_hash ∈ {100, hash …}`, both `new_hash`es) and every bound PI (`100`, `2`, the
published fold) is a representative in `[0, p)`. -/
theorem honTrace_canon (hcanonHash : ∀ l, 0 ≤ hash l ∧ hash l < 2013265921) :
    IvcTraceCanon (honTrace hash) := by
  refine ⟨?_, by norm_num [honTrace, honPub, rowOf, Ivc.PI_INITIAL_HASH],
    by norm_num [honTrace, honPub, rowOf, Ivc.PI_STEP_COUNT],
    hcanonHash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2]⟩
  intro i hi
  simp only [honTrace, List.length_cons, List.length_nil, Nat.reduceAdd] at hi
  interval_cases i <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [honTrace, envAt, wRow0, honRow1, rowOf, List.getD_cons_zero, List.getD_cons_succ,
      Ivc.STEP_COL, Ivc.OLD_HASH_COL, Ivc.NEW_HASH_COL] <;>
    first
      | exact hcanonHash _
      | norm_num

/-- **THE RUNG-2 DISCHARGE FIRES on the genuine 2-row witness (the non-vacuity TRUE half).** Every
hypothesis of `ivc_multi_refines_chain` is met — Satisfied2, a SOUND chip table, the canonicality
envelope (from the hash's `[0, p)` range), and BOTH omitted gates non-vacuously — so the published
`accumulated_hash` IS the genuine 2-step fold. -/
theorem ivc_multi_fires (hcanonHash : ∀ l, 0 ≤ hash l ∧ hash l < 2013265921) :
    (honTrace hash).pub Ivc.PI_ACC_HASH
        = ivcChain hash ((honTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (honTrace hash))
      ∧ (honTrace hash).pub Ivc.PI_STEP_COUNT = ((honTrace hash).rows.length : ℤ) :=
  ivc_multi_refines_chain hash (honTrace hash) (fun _ => 0) (fun _ => (0, 0)) []
    (by simp [honTrace]) (honTf_sound hash) (honTrace_satisfied2 hash)
    (honTrace_canon hash hcanonHash) (honTrace_continuity hash) (honTrace_stepinc hash)

/-- The fired value is the genuine NESTED 2-step fold `hash [TAG, hash [TAG, 100, 7, 1], 9, 2]` over
the read roots `[7, 9]` — a real computation, not a collapsed constant. -/
theorem ivc_multi_fires_value :
    rootsOf (honTrace hash) = [7, 9]
      ∧ (honTrace hash).pub Ivc.PI_ACC_HASH
          = hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2]
      ∧ ivcChain hash ((honTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (honTrace hash))
          = hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2] := by
  refine ⟨rfl, rfl, ?_⟩
  simp [rootsOf, nextRoot, honTrace, wRow0, honRow1, rowOf, honPub, ivcChain, extendAccumulatedHash,
    Ivc.NEW_ROOT_COL, Ivc.PI_INITIAL_HASH]

/-! ## §6 — non-vacuity, LOAD-BEARING half: the continuity gate is a real filter.

The cheat forges row 1's `old_hash` to a hash of a DIFFERENT seed. It still `Satisfied2`s and rides a
SOUND chip table — everything Rung 1 assumes — yet its published `accumulated_hash` is NOT the genuine
`ivcChain`. So `Satisfied2 ∧ ChipTableSound` ALONE cannot force the no-forgery conclusion; the
`IvcContinuity` hypothesis of `ivc_multi_refines_chain` is LOAD-BEARING, not a `P → P` laundering. -/

/-- The cheat's read roots are `[7, 9]` (same as the honest run — the forgery is invisible to the read
input). -/
theorem cheat_rootsOf : rootsOf (cheatTrace hash) = [7, 9] := rfl

/-- **The cheat VIOLATES continuity** (row 1's `old_hash = hash[TAG,200,7,1] ≠ hash[TAG,100,7,1] =
new_hash₀`), given `hash` is injective. -/
theorem cheat_violates_continuity (hinj : Function.Injective hash) :
    ¬ IvcContinuity (cheatTrace hash) := by
  intro hC
  have h := hC 0 (by simp [cheatTrace])
  simp only [cheatTrace, envAt, cheatRow1, wRow0, rowOf, List.getD_cons_zero, List.getD_cons_succ,
    Ivc.OLD_HASH_COL, Ivc.NEW_HASH_COL] at h
  -- h : hash [TAG, 200, 7, 1] = hash [TAG, 100, 7, 1]
  have := hinj h
  simp only [List.cons.injEq] at this
  omega

/-- **`ivc_continuity_is_load_bearing`** — the cheat meets Rung 1's WHOLE hypothesis set
(`Satisfied2 ∧ ChipTableSound`) yet its published hash is NOT the genuine `ivcChain`. The added
continuity/step gates are therefore genuinely needed: no `Satisfied2`-only theorem could conclude the
multi-step no-forgery. -/
theorem ivc_continuity_is_load_bearing (hinj : Function.Injective hash) :
    Satisfied2 hash ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] (cheatTrace hash)
      ∧ ChipTableSound hash ((cheatTrace hash).tf .poseidon2)
      ∧ (cheatTrace hash).pub Ivc.PI_ACC_HASH
          ≠ ivcChain hash ((cheatTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (cheatTrace hash)) := by
  refine ⟨cheatTrace_satisfied2 hash, cheatTf_sound hash, ?_⟩
  -- published = hash[TAG, hash[TAG,200,7,1], 9, 2] ; genuine chain = hash[TAG, hash[TAG,100,7,1], 9, 2]
  have hpub : (cheatTrace hash).pub Ivc.PI_ACC_HASH
      = hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 200, 7, 1], 9, 2] := rfl
  have hchain : ivcChain hash ((cheatTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (cheatTrace hash))
      = hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2] := by
    simp [rootsOf, nextRoot, cheatTrace, wRow0, cheatRow1, rowOf, cheatPub, ivcChain,
      extendAccumulatedHash, Ivc.NEW_ROOT_COL, Ivc.PI_INITIAL_HASH]
  rw [hpub, hchain]
  intro heq
  have h1 := hinj heq
  simp only [List.cons.injEq, true_and] at h1
  have h2 := hinj h1.1
  simp only [List.cons.injEq] at h2
  omega

end TwoRow

/-! ## §7 — axiom tripwires. -/

#assert_axioms newhash_is_chain
#assert_axioms ivc_multi_refines_chain
#assert_axioms ivc_multi_fires_demo
#assert_axioms honTf_sound
#assert_axioms cheatTf_sound
#assert_axioms honTrace_satisfied2
#assert_axioms cheatTrace_satisfied2
#assert_axioms ivc_multi_fires
#assert_axioms ivc_continuity_is_load_bearing
#assert_axioms cheat_violates_continuity

end Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2
