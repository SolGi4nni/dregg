/-
# Dregg2.Circuit.Emit.TemporalPredicateRung2 — the RUNG-2 no-forgery discharge for the emitted
TEMPORAL-predicate (GTE continuous-predicate) descriptor (`temporalPredicateDesc`).

## What this file IS

`TemporalPredicateRefine.lean` (RUNG 1) proves the whole-descriptor bridge `Satisfied2 ⟹
GtePredicateHeld` on every active step — but its `GtePredicateHeld e := e.loc THRESHOLD ≤ e.loc VALUE`
is stated against the row's OWN witnessed `THRESHOLD` COLUMN, and the connection to the PUBLISHED
threshold `pi[PI_THRESHOLD]` is proven only at ROW 0 (`temporalPredicate_threshold_is_published`).
That is exactly the residual: an "only-relative-to-the-disclosed-column" order + a single-row PI pin
where the genuine no-forgery property needs the MULTI-ROW binding to the one published threshold.

## Why an anchor is genuinely needed (this is NOT laundering)

Rung 1's per-step order alone does NOT give no-forgery: a prover could carry the row-0 threshold pin
`threshold₀ = pi` and still DRIFT the interior `THRESHOLD` column below `pi`, satisfying the LOCAL
range gadget at a step whose VALUE is below the PUBLISHED threshold. `local_order_and_pin_permit_forgery`
(§4) exhibits exactly such a fragment — local order holds at every row, row-0 threshold is the
published one, yet an interior value is below the published threshold — possible only because the T3
threshold-constancy window gate is VIOLATED there. So the soundness of "every step's value ≥ the
PUBLISHED threshold" pivots on the T3 constancy chain, which `cheatTrace_not_satisfied` shows the
full descriptor genuinely enforces (the drift makes the trace NOT `Satisfied2`).

## The discharge (the T3 threshold-constancy window gate — carrier-FREE)

The TEMPORAL descriptor is main-only (no Poseidon2 chip / hash sites), so there is NO cryptographic
carrier: the residual is discharged from the descriptor ITSELF. The T3 window gate `t3Body`
(`next[threshold] − local[threshold] = 0`, `on_transition = true`) is enforced by `Satisfied2` on
every transition (`window_t3_forces`), and chains from row 0 to give `THRESHOLD` constant across the
whole run (`threshold_constant`). Composed with the row-0 PI pin, every row's threshold column IS the
published threshold (`temporalPredicate_threshold_col_published`); composed with Rung 1's per-step
order, every active step's VALUE genuinely clears the PUBLISHED threshold
(`temporalPredicate_no_forgery`).

## Axiom hygiene / non-vacuity

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; there is NO named crypto carrier (the
family is carrier-free — the T3 constancy is a descriptor-internal window gate). §5 exhibits a concrete
2-row `Satisfied2` witness whose no-forgery conclusion FIRES (`value = 8 ≥ 3 = published threshold`)
and on which the T3 constancy machinery genuinely propagates across the transition
(`wtTrace_threshold_propagates`); §4 is the load-bearing cheat. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.TemporalPredicateRefine

namespace Dregg2.Circuit.Emit.TemporalPredicateRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff eqToModEq)
open Dregg2.Circuit.Emit.TemporalPredicateEmit
open Dregg2.Circuit.Emit.TemporalPredicateRefine

set_option autoImplicit false

/-- The abstract hash never enters the temporal-predicate denotation (main-only: no hash sites / map
ops), so any value serves as the descriptor's `hash` in the concrete witnesses below. -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-! ## §1 — The T3 threshold-constancy window gate is genuinely present, and reads off `Satisfied2`. -/

/-- The T3 constancy window gate `⟨t3Body, true⟩` is a declared constraint of `temporalPredicateDesc`
(the middle `windowGates` block). -/
theorem mem_t3 : VmConstraint2.windowGate ⟨t3Body, true⟩ ∈ temporalPredicateDesc.constraints := by
  simp only [temporalPredicateDesc, windowGates]
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_self

/-- **Any `onTransition` window constraint forces its body to vanish on a NON-LAST row.** (The exact
`DfaRoutingRefine.window_forces` shape, re-stated for `temporalPredicateDesc`.) -/
theorem tp_window_forces {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {w : WindowConstraint} (hw : VmConstraint2.windowGate w ∈ temporalPredicateDesc.constraints)
    (honT : w.onTransition = true) :
    w.body.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i hi _ hw
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, honT, if_true] at hrc
  exact hrc hlf

/-- **T3 constancy off `Satisfied2` (per non-last transition), MOD `p`.** The threshold column copies
forward across every active window: `threshold` at row `i+1` congruent to `threshold` at row `i` (the
DEPLOYED field constraint; the ℤ constancy is recovered off canonicality at the no-forgery step). -/
theorem window_t3_forces {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length) :
    (envAt t i).nxt THRESHOLD ≡ (envAt t i).loc THRESHOLD [ZMOD 2013265921] :=
  (gate_modEq_iff (by simp only [t3Body, WindowExpr.eval]; ring)).mp
    (tp_window_forces hsat hi hnl mem_t3 rfl)

/-! ## §2 — The constancy chain: `THRESHOLD` is constant across the whole run. -/

/-- **The threshold column is CONSTANT across the run** — chaining the per-transition T3 constancy
from row 0. For every in-range row `i`, `THRESHOLD` at `i` equals `THRESHOLD` at row 0. This is the
multi-row binding Rung 1 leaves open (it only pinned row 0). -/
theorem threshold_constant {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      (envAt t i).loc THRESHOLD ≡ (envAt t 0).loc THRESHOLD [ZMOD 2013265921]
  | 0, _ => Int.ModEq.refl _
  | (i + 1), hi => by
      have hstep : (envAt t i).nxt THRESHOLD ≡ (envAt t i).loc THRESHOLD [ZMOD 2013265921] :=
        window_t3_forces hsat (Nat.lt_of_succ_lt hi) (Nat.ne_of_lt hi)
      have hih : (envAt t i).loc THRESHOLD ≡ (envAt t 0).loc THRESHOLD [ZMOD 2013265921] :=
        threshold_constant hsat i (Nat.lt_of_succ_lt hi)
      calc (envAt t (i + 1)).loc THRESHOLD
          = (envAt t i).nxt THRESHOLD := rfl
        _ ≡ (envAt t i).loc THRESHOLD [ZMOD 2013265921] := hstep
        _ ≡ (envAt t 0).loc THRESHOLD [ZMOD 2013265921] := hih

/-- **Every row's threshold column IS the published threshold.** Constancy (§2) composed with the
row-0 PI pin (`temporalPredicate_threshold_is_published`): the residual "single-row spec vs. multi-row
binding" is closed — no interior row can carry a threshold other than `pi[PI_THRESHOLD]`. -/
theorem temporalPredicate_threshold_col_published {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc THRESHOLD ≡ t.pub PI_THRESHOLD [ZMOD 2013265921] :=
  (threshold_constant hsat i hi).trans
    (temporalPredicate_threshold_is_published hash minit mfin maddrs t hsat hlen)

/-! ## §3 — THE RUNG-2 NO-FORGERY THEOREM. -/

/-- **`temporalPredicate_no_forgery` — accept ⟹ every active step's value clears the PUBLISHED
threshold.** The genuine security property: a `Satisfied2` trace forces, on every active (non-last)
row, `VALUE ≥ pi[PI_THRESHOLD]` — the value against the ONE published threshold, not a per-row
witnessed column. Rung 1's per-step order (`temporalPredicate_satisfied2_sound`, against the local
column) is composed with the whole-run threshold-constancy binding
(`temporalPredicate_threshold_col_published`) to discharge the residual. No crypto carrier. -/
theorem temporalPredicate_no_forgery {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length)
    (i : Nat) (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    (hcanon : TpCanon (envAt t i))
    (hpubc : 0 ≤ t.pub PI_THRESHOLD ∧ t.pub PI_THRESHOLD < 2013265921) :
    t.pub PI_THRESHOLD ≤ (envAt t i).loc VALUE := by
  have horder : (envAt t i).loc THRESHOLD ≤ (envAt t i).loc VALUE :=
    temporalPredicate_satisfied2_sound hash minit mfin maddrs t hsat i hi hnl hcanon
  -- the published-threshold binding is a mod-`p` congruence; both cells are canonical (threshold in
  -- the low half by `TpCanon`, the PI by `hpubc`), so it lifts to the genuine ℤ equality.
  have hpubm : (envAt t i).loc THRESHOLD ≡ t.pub PI_THRESHOLD [ZMOD 2013265921] :=
    temporalPredicate_threshold_col_published hsat hlen i hi
  have hpub : (envAt t i).loc THRESHOLD = t.pub PI_THRESHOLD := by
    obtain ⟨_, _, _, hcTh⟩ := hcanon
    obtain ⟨hpc0, hpc1⟩ := hpubc
    rw [Int.modEq_iff_dvd] at hpubm; obtain ⟨k, hk⟩ := hpubm
    omega
  calc t.pub PI_THRESHOLD = (envAt t i).loc THRESHOLD := hpub.symm
    _ ≤ (envAt t i).loc VALUE := horder

/-- **The no-forgery property on EVERY active step** — the whole-run reading of the discharge. -/
theorem temporalPredicate_no_forgery_every_step {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hcanon : ∀ i, i < t.rows.length → i + 1 ≠ t.rows.length → TpCanon (envAt t i))
    (hpubc : 0 ≤ t.pub PI_THRESHOLD ∧ t.pub PI_THRESHOLD < 2013265921) :
    ∀ i, i < t.rows.length → i + 1 ≠ t.rows.length →
      t.pub PI_THRESHOLD ≤ (envAt t i).loc VALUE :=
  fun i hi hnl => temporalPredicate_no_forgery hsat hlen i hi hnl (hcanon i hi hnl) hpubc

#assert_axioms mem_t3
#assert_axioms window_t3_forces
#assert_axioms threshold_constant
#assert_axioms temporalPredicate_threshold_col_published
#assert_axioms temporalPredicate_no_forgery

/-! ## §4 — LOAD-BEARING ANCHOR: Rung 1's local-column order is strictly weaker than no-forgery.

The T3 threshold-constancy chain is the anchor that upgrades Rung 1's "order relative to the disclosed
column" into genuine no-forgery against the published threshold. This section shows it is load-bearing:
a fragment satisfying LOCAL order at every row AND the row-0 threshold pin can still carry an interior
value BELOW the published threshold — possible only because T3 is violated there — and the full
descriptor rejects exactly such a fragment (T3 bites, so it is not `Satisfied2`). -/

/-- Row 0 of the cheat: `value = threshold = 100` (local order holds; threshold IS the published
`pi = 100`). -/
def cheatRow0 : Assignment := fun c => if c = VALUE then 100 else if c = THRESHOLD then 100 else 0

/-- Row 1 of the cheat: threshold DRIFTED down to `1`, `value = 2` (local order `1 ≤ 2` still holds),
yet `value = 2` is BELOW the published threshold `100`. -/
def cheatRow1 : Assignment := fun c => if c = VALUE then 2 else if c = THRESHOLD then 1 else 0

/-- The published threshold `pi[PI_THRESHOLD] = 100`. -/
def cheatPub : Assignment := fun k => if k = PI_THRESHOLD then 100 else 0

/-- The 2-row cheat fragment. -/
def cheatTrace : VmTrace := { rows := [cheatRow0, cheatRow1], pub := cheatPub, tf := fun _ => [] }

/-- **The Rung-1 reading (local order + row-0 pin) PERMITS a forgery.** Both rows satisfy local order,
row-0 threshold IS the published threshold, YET row-1's value is BELOW the published threshold — a
genuine forgery of "value ≥ published threshold", possible only because the T3 threshold-constancy is
violated (`threshold₁ ≠ threshold₀`). So the T3 constancy anchor is load-bearing: Rung 1's conclusion
alone cannot conclude no-forgery. -/
theorem local_order_and_pin_permit_forgery :
    (cheatRow0 THRESHOLD ≤ cheatRow0 VALUE)
    ∧ (cheatRow1 THRESHOLD ≤ cheatRow1 VALUE)
    ∧ (cheatRow0 THRESHOLD = cheatPub PI_THRESHOLD)
    ∧ (cheatRow1 VALUE < cheatPub PI_THRESHOLD)
    ∧ (cheatRow1 THRESHOLD ≠ cheatRow0 THRESHOLD) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The full descriptor REJECTS the forgery — the T3 window gate bites.** The drifted-threshold
fragment cannot `Satisfied2` the temporal-predicate descriptor: `window_t3_forces` would force
`threshold₁ = threshold₀`, i.e. `1 = 100` — impossible. This is what makes the descriptor genuinely
enforce the constancy the Rung-2 discharge consumes. -/
theorem cheatTrace_not_satisfied :
    ¬ Satisfied2 hash0 temporalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] cheatTrace := by
  intro hsat
  have h : (envAt cheatTrace 0).nxt THRESHOLD ≡ (envAt cheatTrace 0).loc THRESHOLD [ZMOD 2013265921] :=
    window_t3_forces (i := 0) hsat (by decide) (by decide)
  exact absurd h (by decide)

#assert_axioms local_order_and_pin_permit_forgery
#assert_axioms cheatTrace_not_satisfied

/-! ## §5 — NON-VACUITY, TRUE half: a concrete `Satisfied2` witness whose no-forgery conclusion FIRES.

A genuine 2-row GTE run: row 0 is a valid range-gadget row (`value = 8 ≥ threshold = 3`, reusing
`TemporalPredicateRefine.acceptLoc`), row 1 the padded last row threading the counters and the T3
threshold constancy. Every hypothesis of `temporalPredicate_no_forgery` is met and the discharged
conclusion fires: `value = 8 ≥ 3 = pi[PI_THRESHOLD]`. The T3 constancy machinery genuinely propagates
across the transition (`wtTrace_threshold_propagates`). -/

/-- Every diff-bit column of the `acceptLoc` accept row is boolean, so its C2 bit gate vanishes. -/
theorem acceptLoc_bit_zero (j : Nat) (hj : j < NUM_DIFF_BITS) :
    (bitBinaryBody j).eval acceptLoc = 0 := by
  have hj30 : j < 30 := hj
  clear hj
  rw [bit_binary_zero_iff acceptLoc j]
  interval_cases j <;> decide

/-- The padded last row: threshold held at `3` (T3), `accumulator = 2` (T1), `step_index = 1` (T2),
everything else `0`. -/
def wtRow1 : Assignment := fun c =>
  if c = THRESHOLD then 3
  else if c = ACCUMULATOR then 2
  else if c = STEP_INDEX then 1
  else 0

/-- Public inputs: `padded_len = 2` (last `accumulator`), `threshold = 3`, both state roots `0`. -/
def wtPub : Assignment := fun k =>
  if k = PI_PADDED_LEN then 2
  else if k = PI_THRESHOLD then 3
  else 0

/-- The concrete 2-row genuine trace (row 0 = the accept row, row 1 = padded last row). -/
def wtTrace : VmTrace := { rows := [acceptLoc, wtRow1], pub := wtPub, tf := fun _ => [] }

theorem memOpsOf_tp : memOpsOf temporalPredicateDesc = [] := rfl
theorem mapOpsOf_tp : mapOpsOf temporalPredicateDesc = [] := rfl
theorem memLog_tp (t : VmTrace) : memLog temporalPredicateDesc t = [] := by
  simp [memLog, memOpsOf_tp]
theorem mapLog_tp (t : VmTrace) : mapLog temporalPredicateDesc t = [] := by
  simp [mapLog, mapOpsOf_tp]

/-- A base gate whose body vanishes on `acceptLoc` holds at any row of the 2-row trace (forced on
the active row 0, vacuous on the last row 1). -/
theorem wt_gate_holds {g : EmittedExpr} (h0 : g.eval acceptLoc = 0) (i : Nat) (hi : i < 2) :
    VmConstraint2.holdsAt hash0 wtTrace.tf (envAt wtTrace i) (i == 0) (i + 1 == 2)
      (.base (.gate g)) := by
  interval_cases i
  · exact eqToModEq h0
  · exact trivial

/-- An `onTransition` window gate whose body vanishes on the row-0 window holds at any row (forced on
row 0, vacuous on the last row 1). -/
theorem wt_window_holds {body : WindowExpr} (h0 : body.eval (envAt wtTrace 0) = 0) (i : Nat)
    (hi : i < 2) :
    VmConstraint2.holdsAt hash0 wtTrace.tf (envAt wtTrace i) (i == 0) (i + 1 == 2)
      (.windowGate ⟨body, true⟩) := by
  interval_cases i
  · exact fun _ => eqToModEq h0
  · exact fun hc => absurd hc (by decide)

/-- A first-row boundary whose body vanishes on `acceptLoc` holds at any row (forced on the first
row 0, vacuous off it). -/
theorem wt_bfirst_holds {b : EmittedExpr} (h0 : b.eval acceptLoc = 0) (i : Nat) (hi : i < 2) :
    VmConstraint2.holdsAt hash0 wtTrace.tf (envAt wtTrace i) (i == 0) (i + 1 == 2)
      (.base (.boundary .first b)) := by
  interval_cases i
  · exact fun _ => eqToModEq h0
  · exact fun hc => absurd hc (by decide)

/-- A first-row PI pin met on `acceptLoc` holds at any row (forced on the first row, vacuous off it). -/
theorem wt_pifirst_holds {col k : Nat} (h0 : acceptLoc col = wtPub k) (i : Nat) (hi : i < 2) :
    VmConstraint2.holdsAt hash0 wtTrace.tf (envAt wtTrace i) (i == 0) (i + 1 == 2)
      (.base (.piBinding .first col k)) := by
  interval_cases i
  · exact fun _ => eqToModEq h0
  · exact fun hc => absurd hc (by decide)

/-- A last-row PI pin met on `wtRow1` holds at any row (forced on the last row 1, vacuous off it). -/
theorem wt_pilast_holds {col k : Nat} (h0 : wtRow1 col = wtPub k) (i : Nat) (hi : i < 2) :
    VmConstraint2.holdsAt hash0 wtTrace.tf (envAt wtTrace i) (i == 0) (i + 1 == 2)
      (.base (.piBinding .last col k)) := by
  interval_cases i
  · exact fun hc => absurd hc (by decide)
  · exact fun _ => eqToModEq h0

/-- **The witness PROVABLY satisfies the emitted descriptor.** Row 0's range gadget + counters vanish,
the three windows thread across the transition (including T3 constancy `3 = 3`), the boundary + PI
pins are met, and the memory legs are the empty-log balance. -/
theorem wtTrace_satisfies :
    Satisfied2 hash0 temporalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] wtTrace where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    clear hi
    simp only [temporalPredicateDesc] at hc
    rcases List.mem_append.mp hc with hpw | hbd
    · rcases List.mem_append.mp hpw with hpr | hwd
      · -- c ∈ perRowGates
        simp only [perRowGates] at hpr
        rcases List.mem_append.mp hpr with hhb | htail
        · rcases List.mem_cons.mp hhb with rfl | hbit
          · exact wt_gate_holds (by decide) i hi2
          · obtain ⟨j, hjr, rfl⟩ := List.mem_map.mp hbit
            exact wt_gate_holds (acceptLoc_bit_zero j (List.mem_range.mp hjr)) i hi2
        · fin_cases htail <;> exact wt_gate_holds (by decide) i hi2
      · -- c ∈ windowGates
        simp only [windowGates] at hwd
        fin_cases hwd <;> exact wt_window_holds (by decide) i hi2
    · -- c ∈ boundaries
      simp only [boundaries] at hbd
      fin_cases hbd
      · exact wt_bfirst_holds (by decide) i hi2
      · exact wt_bfirst_holds (by decide) i hi2
      · exact wt_pilast_holds (by decide) i hi2
      · exact wt_pifirst_holds (by decide) i hi2
      · exact wt_pifirst_holds (by decide) i hi2
      · exact wt_pilast_holds (by decide) i hi2
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [temporalPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_tp] at hop; simp at hop
  memDisciplined := by rw [memLog_tp]; trivial
  memBalanced := by rw [memLog_tp]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_tp]; rfl
  mapTableFaithful := by rw [mapLog_tp]; rfl

/-- **The RUNG-2 no-forgery discharge FIRES on the genuine witness.** Feeding the concrete satisfying
trace recovers `pi[PI_THRESHOLD] ≤ VALUE` on the active row 0 — WITHOUT any residual hypothesis. -/
theorem wtTrace_no_forgery_fires :
    wtTrace.pub PI_THRESHOLD ≤ (envAt wtTrace 0).loc VALUE :=
  temporalPredicate_no_forgery wtTrace_satisfies (by decide) 0 (by decide) (by decide)
    acceptEnv_canon ⟨by decide, by decide⟩

/-- The recovered numbers are real and distinct (`3 ≤ 8`), the threshold the published one — the
conclusion is a genuine bound, not a `True`/`P → P` shell. -/
theorem wtTrace_no_forgery_value :
    wtTrace.pub PI_THRESHOLD = 3 ∧ (envAt wtTrace 0).loc VALUE = 8 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The T3 constancy machinery genuinely fires on the witness** — `threshold_constant` at row 1
(an inductive step through `window_t3_forces` at the transition) forces `threshold₁ = threshold₀`. -/
theorem wtTrace_threshold_propagates :
    (envAt wtTrace 1).loc THRESHOLD ≡ (envAt wtTrace 0).loc THRESHOLD [ZMOD 2013265921] :=
  threshold_constant wtTrace_satisfies 1 (by decide)

#assert_axioms acceptLoc_bit_zero
#assert_axioms wtTrace_satisfies
#assert_axioms wtTrace_no_forgery_fires
#assert_axioms wtTrace_no_forgery_value
#assert_axioms wtTrace_threshold_propagates

end Dregg2.Circuit.Emit.TemporalPredicateRung2
