/-
# Dregg2.Circuit.Emit.NonRevocationRung2 — the RUNG-2 no-forgery discharge for the emitted
non-revocation descriptor (`nonRevocationDesc`, the `revocation` family), UNCONDITIONAL after the
lower-bound soundness fix, plus the historical witness of the CLOSED bug.

## What Rung 1 gave us and what the lower-bound fix closed

`NonRevocationRefine.lean` (RUNG 1) proves the whole-descriptor bridge
`nonRevocation_nonmembership` : `Satisfied2 ∧ ChipTableSound ∧ RangeTableSound ∧ (sorted, adjacent
spine) ⟹ NonMember spine x` — the queried item is a GENUINE non-member of the committed set (NOT
revoked). Before the fix, that bridge consumed an EXPLICIT residual `FieldCanonicalDiffs t :=
0 ≤ DIFF_L ∧ 0 ≤ DIFF_R` (the STRICT-LOWER half of the half-field ordering). The old half-field range
argument certified only `RL = HALF_P_MINUS_1 − diff ∈ [0, 2^30)`, which over ℤ bounds `diff ∈
(HALF_P_MINUS_1 − 2^30, HALF_P_MINUS_1]` — the lower bound `diff ≥ 0` was NOT forced.

The FIX (now deployed in `nonRevocationDesc`) adds two DIRECT range lookups binding `DIFF_L`, `DIFF_R`
themselves to `[0, 2^30)`. So `Satisfied2` now FORCES `DiffLowerRangeSound` (`sat_forces_lowerRange`)
and hence `FieldCanonicalDiffs` (Rung 1's `sat_forces_canon`) — the residual is discharged BY THE
EMITTED CIRCUIT, and `nonRevocation_rung2` is UNCONDITIONAL.

## The measured gap the fix closed (MODEL-FOUND — a REAL circuit seam, not a modelling artifact)

`HALF_P_MINUS_1 = 1006632959` and `2^30 = 1073741824 > (p−1)/2`, so the single `RL ∈ [0, 2^30)` lookup
overshoots the honest positive window by exactly `2^30 − 1 − HALF_P_MINUS_1 = 2^26`
(`window_width`). The OLD 12-constraint descriptor (`nonRevocationDescPreFix`) therefore admitted a
NEGATIVE window `diff ∈ [−2^26, −1]`: a canonical felt `diff = p−1` (signed `−1`) gives
`RL = HALF_P_MINUS_1 + 1 = 1006632960 < 2^30`. `satisfied_admits_negative_window` records that the
`RL`-lookup-alone bound is only `−2^26 ≤ DIFF_L`, and `prefix_carriers_admitted_forgery` exhibits the
concrete forgery: the queried item set EQUAL to a present leaf (`x = L = 100`, `diff_left = −1`)
PROVABLY `Satisfied2`s the PRE-FIX descriptor against realizable carriers, yet `x` is a genuine MEMBER
— a revoked item forging freshness. The DEPLOYED descriptor REJECTS this same trace
(`fixed_forbids_the_forgery`): its direct `[DIFF_L]` lookup refuses `[−1]`. That contrast IS the
closed soundness bug, kept true on both sides.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The range-argument faithfulness enters
ONLY as the NAMED `DiffLowerRangeSound` / `RangeTableSound` hypotheses; the Poseidon2 CR enters ONLY
as `ChipTableSound`; the exclusion core `sorted_gap_excludes` is unconditional combinatorics. NEW
file; all imports read-only.
-/
import Dregg2.Circuit.Emit.NonRevocationRefine

namespace Dregg2.Circuit.Emit.NonRevocationRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   Table memLog mapLog)
open Dregg2.Circuit.Emit.NonRevocationEmit
open Dregg2.Circuit.Emit.NonRevocationRefine
open Dregg2.Crypto.NonMembership (Sorted Adjacent NonMember sorted_gap_excludes)

set_option autoImplicit false

/-- Constraint-membership tactic (twin of Rung 1's local `nr_mem`): every constraint we name is
literally in `nonRevocationDesc` (including the two direct diff range lookups added by the fix). -/
local macro "nr_mem" : tactic =>
  `(tactic| (simp [nonRevocationDesc, nonRevLastRowFix, level0Lookup, level1Lookup, rangeLLookup,
      rangeRLookup, rangeLDiffLookup, rangeRDiffLookup]))

/-! ## §1 — MEASURING the gap (the half-field overshoot is exactly `2^26`). -/

/-- The single range lookup `RL ∈ [0, 2^30)` overshoots the honest positive window `[0,
HALF_P_MINUS_1]` by exactly `2^26` — the width of the negative window both models admit. -/
theorem window_width : (2 : ℤ) ^ ORDERING_BITS - 1 - HALF_P_MINUS_1 = 2 ^ 26 := by decide

/-- **The `RL` range-wire lookup ALONE bounds `DIFF_L` only down to `−2^26`.** From the range lookup
`RL < 2^30` and the binding `RL = HALF_P_MINUS_1 − DIFF_L`, that single lookup forces only
`DIFF_L ≥ HALF_P_MINUS_1 − (2^30 − 1) = −2^26` — it does NOT exclude the negative window `[−2^26, −1]`.
This is the exact overshoot the OLD (pre-fix) 12-constraint descriptor left open, admitting the
`x ≤ L` freshness forgery (`nonRevocationDescPreFix` below). It is still TRUE of the fixed descriptor
(the `RL` lookup is unchanged), but is no longer load-bearing: the fix's DIRECT `[DIFF_L]` range lookup
now additionally forces `0 ≤ DIFF_L` (`sat_forces_lowerRange`), so the OVERALL `Satisfied2` closes the
window this single-lookup bound leaves. -/
theorem satisfied_admits_negative_window {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range)) :
    (-(2 ^ 26) : ℤ) ≤ (envAt t 0).loc DIFF_L := by
  have hrl := (rangeLBind_body_zero_iff _).mp (gateZero0 hsat hlen rangeLBindBody (by nr_mem))
  have hub := (range0 hsat hRange (by omega) RL (by nr_mem)).2
  rw [hrl] at hub
  have hpow : (2 : ℤ) ^ ORDERING_BITS = 1073741824 := by decide
  rw [hpow] at hub
  simp only [HALF_P_MINUS_1] at hub
  have : ((2 : ℤ) ^ 26) = 67108864 := by decide
  omega

/-! ## §2 — THE NAMED CARRIER (the lower-gap range tooth) + the discharge. -/

/-- **`DiffLowerRangeSound t` — THE NAMED CARRIER (= the emit-fix).** The range argument certifies the
diff wires THEMSELVES lie in `[0, 2^30)` — the twin of `RangeTableSound` applied to `DIFF_L`/`DIFF_R`
directly, i.e. the lower-gap range lookup `nonRevocationDesc` is MISSING. NAMED, never a Lean axiom. -/
def DiffLowerRangeSound (t : VmTrace) : Prop :=
  (0 ≤ (envAt t 0).loc DIFF_L ∧ (envAt t 0).loc DIFF_L < 2 ^ ORDERING_BITS) ∧
  (0 ≤ (envAt t 0).loc DIFF_R ∧ (envAt t 0).loc DIFF_R < 2 ^ ORDERING_BITS)

/-- **`lowerRange_discharges_canon`** — the carrier discharges Rung 1's `FieldCanonicalDiffs` residual
(its `0 ≤` halves). Genuine, not laundering: `DiffLowerRangeSound` STRICTLY refines
`FieldCanonicalDiffs` (it additionally caps the diffs at `2^30`). -/
theorem lowerRange_discharges_canon {t : VmTrace} (h : DiffLowerRangeSound t) :
    FieldCanonicalDiffs t :=
  ⟨h.1.1, h.2.1⟩

/-- **`sat_forces_lowerRange` — THE DEPLOYED DESCRIPTOR NOW FORCES THE CARRIER.** With the lower-bound
fix in `nonRevocationDesc`, the two direct diff range lookups put `[DIFF_L]`, `[DIFF_R]` into the range
table; against `RangeTableSound` (via Rung 1's `range0`) that forces `DiffLowerRangeSound`
UNCONDITIONALLY — the carrier that Rung 2 had to RE-ASSUME is now a consequence of `Satisfied2`. -/
theorem sat_forces_lowerRange {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range)) :
    DiffLowerRangeSound t :=
  ⟨range0 hsat hRange hlen DIFF_L (by nr_mem), range0 hsat hRange hlen DIFF_R (by nr_mem)⟩

/-- **`nonRevocation_rung2` — THE RUNG-2 NO-FORGERY DISCHARGE (now UNCONDITIONAL).**
A `Satisfied2` active-row-0 window, against the Poseidon2 chip carrier and the range carrier, with the
committed sorted spine in which the bracketing leaves are adjacent, forces the queried item to be a
GENUINE non-member of the committed set (NOT revoked) — `NonMember spine x`, welded to
`sorted_gap_excludes`. WITHOUT `FieldCanonicalDiffs` / `DiffLowerRangeSound` as a hypothesis: with the
lower-bound fix present, the descriptor's own diff range lookups force them (`sat_forces_lowerRange`),
so Rung 1's `nonRevocation_nonmembership` already discharges the whole thing. -/
theorem nonRevocation_rung2 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range))
    (spine : List ℤ)
    (hsorted : Sorted spine)
    (hadj : Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)) :
    NonMember spine ((envAt t 0).loc X) :=
  nonRevocation_nonmembership hlen hsat hChip hRange spine hsorted hadj

#assert_axioms window_width
#assert_axioms satisfied_admits_negative_window
#assert_axioms lowerRange_discharges_canon
#assert_axioms sat_forces_lowerRange
#assert_axioms nonRevocation_rung2

/-! ## §3 — the shared committed tree + honest / cheating traces.

A depth-2 tree over the adjacent bottom siblings `L = 100`, `R = 300` under sibling `sib = 7`, folding
to the committed root `hash [hash [100,300], 7]`, at consecutive positions `5, 6`. -/

/-- A concrete little-endian digit hash (base `10^6`): `[100,300] ↦ 100000300` (twin of Rung 1's). -/
private def demoHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) 0

/-- The shared Poseidon2 chip table: the two genuine node hashes of the committed tree. -/
private def demoTbl : List (List ℤ) :=
  [ chipRow demoHash [100, 300] (List.replicate 7 0)
  , chipRow demoHash [100000300, 7] (List.replicate 7 0) ]

/-- The shared chip table is genuinely SOUND (so `ChipTableSound` is realizable, not just assumed). -/
private theorem demoTbl_chipSound (tf : TableId → Table) (h : tf .poseidon2 = demoTbl) :
    ChipTableSound demoHash (tf .poseidon2) := by
  rw [h]
  intro r hr
  simp only [demoTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[100, 300], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[100000300, 7], List.replicate 7 0, by decide, by decide, rfl⟩

/-! ### §3a — the HONEST witness (`x = 200`, strictly bracketed, `diff = 99`). -/

private def hnRow : Assignment := fun c =>
  if c = X then 200
  else if c = LEAF_L then 100
  else if c = LEAF_R then 300
  else if c = LPOS then 5
  else if c = RPOS then 6
  else if c = DIFF_L then 99
  else if c = DIFF_R then 99
  else if c = RL then 1006632860
  else if c = RR then 1006632860
  else if c = PAR0 then 100000300
  else if c = CUR1 then 100000300
  else if c = SIB1 then 7
  else if c = PAR1 then 100000300000007
  else 0

private def hnPub : Assignment := fun k =>
  if k = ROOT_PI then 100000300000007 else if k = QUERIED_PI then 200 else 0

private def hnRangeTbl : List (List ℤ) := [[1006632860], [99]]

private def hnTrace : VmTrace :=
  { rows := [hnRow, hnRow], pub := hnPub
    tf := fun tid => match tid with
      | .poseidon2 => demoTbl
      | .range => hnRangeTbl
      | _ => [] }

private theorem hn_sat :
    Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] hnTrace := by
  have hmemlog : memLog nonRevocationDesc hnTrace = [] := rfl
  have hmaplog : mapLog nonRevocationDesc hnTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hnTrace.rows.length = 2 from rfl] at hi
    simp only [nonRevocationDesc, nonRevLastRowFix, List.cons_append, List.nil_append,
      level0Lookup, level1Lookup, rangeLLookup, rangeRLookup,
      rangeLDiffLookup, rangeRDiffLookup] at hc
    interval_cases i
    · have hF : ((0 : Nat) == 0) = true := rfl
      have hLf : ((0 : Nat) + 1 == hnTrace.rows.length) = false := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hF, hLf] <;>
        decide
    · have hFf : ((1 : Nat) == 0) = false := rfl
      have hL : ((1 : Nat) + 1 == hnTrace.rows.length) = true := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hFf, hL] <;>
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

private theorem hn_chipSound : ChipTableSound demoHash (hnTrace.tf .poseidon2) :=
  demoTbl_chipSound _ rfl

private theorem hn_rangeSound : RangeTableSound ORDERING_BITS (hnTrace.tf .range) := by
  intro r hr
  simp only [hnTrace, hnRangeTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨1006632860, rfl, by decide, by decide⟩
  · exact ⟨99, rfl, by decide, by decide⟩

/-- **The deployed descriptor FORCES the lower-gap carrier on the honest witness** — `DiffLowerRangeSound`
is not merely satisfiable, it is DERIVED from the honest trace's `Satisfied2` + `RangeTableSound` through
the fix's direct diff range lookups (`sat_forces_lowerRange`). Non-vacuity of the forcing lemma. -/
theorem honest_forces_lowerRange : DiffLowerRangeSound hnTrace :=
  sat_forces_lowerRange (by decide) hn_sat hn_rangeSound

/-- **NON-VACUITY (TRUE half) — the RUNG-2 discharge FIRES end-to-end.** Every hypothesis of
`nonRevocation_rung2` jointly holds on the concrete honest instance (inhabited `Satisfied2`,
realizable chip / range carriers, a concrete sorted spine with `100`/`300` adjacent), and the
conclusion is the GENUINE non-membership `200 ∉ [100,300]` — WITHOUT any `FieldCanonicalDiffs` /
`DiffLowerRangeSound` hypothesis (the descriptor forces them). Not a hollow green. -/
theorem honest_rung2_fires : NonMember ([100, 300] : List ℤ) 200 := by
  have hsorted : Sorted ([100, 300] : List ℤ) := by simp [Sorted, List.pairwise_cons]
  have hadj : Adjacent ([100, 300] : List ℤ)
      ((envAt hnTrace 0).loc LEAF_L) ((envAt hnTrace 0).loc LEAF_R) := ⟨[], [], rfl⟩
  exact nonRevocation_rung2 (by decide) hn_sat hn_chipSound hn_rangeSound
    [100, 300] hsorted hadj

/-! ### §3b — THE CLOSED BUG: the PRE-FIX descriptor admitted a member-forgery; the fixed one rejects it.

The `revocation` soundness bug (now closed): the OLD 12-constraint descriptor range-checked only the
half-field wires `RL`/`RR`, never `DIFF_L`/`DIFF_R`, so the `2^26` negative window admitted a revoked
(present) item forging freshness. `nonRevocationDescPreFix` is that exact pre-fix descriptor, kept as a
TRUE historical witness. The model-found forgery: the queried item set EQUAL to the present left
neighbor (`x = LEAF_L = 100`), so `diff_left = x − L − 1 = −1`, a canonical felt `p−1` whose range-wire
`RL = HALF_P_MINUS_1 + 1 = 1006632960 < 2^30` decomposes into 30 bits. It PROVABLY `Satisfied2`s the
PRE-FIX descriptor (`prefix_cheat_sat`) yet is a genuine member — but does NOT `Satisfied2` the deployed
fixed descriptor, whose direct `[DIFF_L]` lookup rejects `[−1]` (`fixed_forbids_the_forgery`). Same
committed tree/root as the honest witness — only the queried item and the diff/range wires change. -/

/-- **`nonRevocationDescPreFix` — THE HISTORICAL PRE-FIX DESCRIPTOR (the CLOSED soundness bug).** The
12-constraint non-revocation descriptor as emitted BEFORE the lower-bound fix: identical to
`nonRevocationDesc` but WITHOUT the two direct diff range lookups (`rangeLDiffLookup`,
`rangeRDiffLookup`). It range-checks only the half-field wires `RL`/`RR`, so the `2^26` negative window
leaks — a revoked item can forge freshness (`prefix_carriers_admitted_forgery`). Retained as a TRUE
witness that the bug was real; the deployed descriptor closes it (`fixed_forbids_the_forgery`). -/
def nonRevocationDescPreFix : EffectVmDescriptor2 :=
  { name        := "dregg-non-revocation-sorted-tree::poseidon2-v1-PREFIX-BUGGY"
  , traceWidth  := NONREV_WIDTH
  , piCount     := 2
  , tables      := [Dregg2.Circuit.DescriptorIR2.rangeTableDef ORDERING_BITS]
  , constraints :=
      [ level0Lookup
      , level1Lookup
      , .base (.gate contBody)
      , .base (.gate diffLBody)
      , .base (.gate diffRBody)
      , .base (.gate rangeLBindBody)
      , .base (.gate rangeRBindBody)
      , rangeLLookup
      , rangeRLookup
      , .base (.gate adjBody)
      , .base (.piBinding VmRow.first PAR1 ROOT_PI)
      , .base (.piBinding VmRow.first X QUERIED_PI) ]
  , hashSites   := []
  , ranges      := [] }

private def chRow : Assignment := fun c =>
  if c = X then 100
  else if c = LEAF_L then 100
  else if c = LEAF_R then 300
  else if c = LPOS then 5
  else if c = RPOS then 6
  else if c = DIFF_L then -1
  else if c = DIFF_R then 199
  else if c = RL then 1006632960
  else if c = RR then 1006632760
  else if c = PAR0 then 100000300
  else if c = CUR1 then 100000300
  else if c = SIB1 then 7
  else if c = PAR1 then 100000300000007
  else 0

private def chPub : Assignment := fun k =>
  if k = ROOT_PI then 100000300000007 else if k = QUERIED_PI then 100 else 0

private def chRangeTbl : List (List ℤ) := [[1006632960], [1006632760]]

private def chTrace : VmTrace :=
  { rows := [chRow, chRow], pub := chPub
    tf := fun tid => match tid with
      | .poseidon2 => demoTbl
      | .range => chRangeTbl
      | _ => [] }

/-- **The forgery PROVABLY `Satisfied2`s the PRE-FIX descriptor (the bug was real).** With `x = L = 100`,
`diff_left = −1`, and the range-wire `RL = 1006632960 ∈ [0, 2^30)`, every constraint of the OLD
12-constraint `nonRevocationDescPreFix` holds on the active row 0 (and the vacuous/lookup legs on the
padding row 1) — the pre-fix `Satisfied2` is met by an item that is a genuine member. The deployed FIXED
descriptor rejects this same trace (`fixed_forbids_the_forgery`). -/
theorem prefix_cheat_sat :
    Satisfied2 demoHash nonRevocationDescPreFix (fun _ => 0) (fun _ => (0, 0)) [] chTrace := by
  have hmemlog : memLog nonRevocationDescPreFix chTrace = [] := rfl
  have hmaplog : mapLog nonRevocationDescPreFix chTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show chTrace.rows.length = 2 from rfl] at hi
    simp only [nonRevocationDescPreFix, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup] at hc
    interval_cases i
    · have hF : ((0 : Nat) == 0) = true := rfl
      have hLf : ((0 : Nat) + 1 == chTrace.rows.length) = false := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hF, hLf] <;>
        decide
    · have hFf : ((1 : Nat) == 0) = false := rfl
      have hL : ((1 : Nat) + 1 == chTrace.rows.length) = true := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hFf, hL] <;>
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDescPreFix] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

theorem cheat_chipSound : ChipTableSound demoHash (chTrace.tf .poseidon2) :=
  demoTbl_chipSound _ rfl

theorem cheat_rangeSound : RangeTableSound ORDERING_BITS (chTrace.tf .range) := by
  intro r hr
  simp only [chTrace, chRangeTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨1006632960, rfl, by decide, by decide⟩
  · exact ⟨1006632760, rfl, by decide, by decide⟩

/-- The cheat VIOLATES the named lower-gap carrier (`diff_left = −1 < 0`) — the exact tooth the
deployed descriptor lacks. -/
theorem cheat_violates_lower : ¬ DiffLowerRangeSound chTrace := by
  intro h; exact absurd h.1.1 (by decide)

/-- The cheat VIOLATES Rung 1's `FieldCanonicalDiffs` residual too (`0 ≤ DIFF_L` is `0 ≤ −1`). -/
theorem cheat_violates_canon : ¬ FieldCanonicalDiffs chTrace := by
  intro h; exact absurd h.1 (by decide)

/-- **`prefix_carriers_admitted_forgery` — THE CLOSED BUG, WITNESSED.** On the forgery, the PRE-FIX
descriptor `Satisfied2`s, both named carriers (`ChipTableSound`, `RangeTableSound`) are realizable, the
committed spine `[100,300]` is sorted with `100`/`300` adjacent — yet the queried item `x = 100` is a
genuine MEMBER (`¬ NonMember [100,300] 100`), and the `FieldCanonicalDiffs` residual is violated. So NO
theorem concluding `NonMember` from the PRE-FIX `Satisfied2` + those carriers alone could exist: the
`2^26` negative window admitted a revoked-item freshness forgery. This is the exact soundness hole the
lower-bound fix closes — the fixed descriptor rejects this same trace (`fixed_forbids_the_forgery`). -/
theorem prefix_carriers_admitted_forgery :
    Satisfied2 demoHash nonRevocationDescPreFix (fun _ => 0) (fun _ => (0, 0)) [] chTrace
    ∧ ChipTableSound demoHash (chTrace.tf .poseidon2)
    ∧ RangeTableSound ORDERING_BITS (chTrace.tf .range)
    ∧ Sorted ([100, 300] : List ℤ)
    ∧ Adjacent ([100, 300] : List ℤ) ((envAt chTrace 0).loc LEAF_L) ((envAt chTrace 0).loc LEAF_R)
    ∧ (envAt chTrace 0).loc X ∈ ([100, 300] : List ℤ)
    ∧ ¬ NonMember ([100, 300] : List ℤ) ((envAt chTrace 0).loc X)
    ∧ ¬ FieldCanonicalDiffs chTrace := by
  refine ⟨prefix_cheat_sat, cheat_chipSound, cheat_rangeSound, ?_, ⟨[], [], rfl⟩, ?_, ?_,
    cheat_violates_canon⟩
  · simp [Sorted, List.pairwise_cons]
  · show (100 : ℤ) ∈ ([100, 300] : List ℤ); simp
  · rintro ⟨_, hni⟩
    exact hni (by show (100 : ℤ) ∈ ([100, 300] : List ℤ); simp)

/-- **`fixed_forbids_the_forgery` — THE FIX BITES (the positive closure).** The SAME forgery trace does
NOT `Satisfied2` the deployed FIXED `nonRevocationDesc`: its direct `[DIFF_L]` range lookup requires
`[−1] ∈ tf.range = chRangeTbl = [[1006632960],[1006632760]]`, which fails. So the revoked-item freshness
forgery that `Satisfied2`d the pre-fix descriptor is now rejected — the soundness bug is closed. -/
theorem fixed_forbids_the_forgery :
    ¬ Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] chTrace := by
  intro h
  have hmem : VmConstraint2.lookup ⟨TableId.range, [.var DIFF_L]⟩ ∈ nonRevocationDesc.constraints := by
    nr_mem
  have h0 := h.rowConstraints 0 (by decide) _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt, List.map_cons, List.map_nil,
    EmittedExpr.eval] at h0
  revert h0; decide

#assert_axioms honest_rung2_fires
#assert_axioms honest_forces_lowerRange
#assert_axioms prefix_cheat_sat
#assert_axioms cheat_violates_lower
#assert_axioms cheat_violates_canon
#assert_axioms prefix_carriers_admitted_forgery
#assert_axioms fixed_forbids_the_forgery

/-! ### §3c — THE LAST-ROW / HEIGHT-1 FORGERY: the transition-only `.gate` mapping re-opened the
member-forgery on a single-row trace; the `nonRevLastRowFix` boundary re-lowerings close it.

The deployed IR-v2 AIR lowers a `.base (.gate _)` with `builder.when_transition()` — VACUOUS on the
last row. On a HEIGHT-1 trace (`rows.length = 1`) row 0 IS the last row, so EVERY one of the six
semantic binding gates is exempt: the ordering witness `DIFF_L` is DECOUPLED from `x − L − 1`, so the
`x = L` member-forgery the direct `[DIFF_L]` lookup was meant to reject slips back in — the adversary
sets `DIFF_L = 0` (which the range lookup happily serves) while `x = L = 100` is a genuine committed
member (revoked). `nonRevocationDescPreLast` is the descriptor BEFORE the last-row fix (the 14
transition-only constraints); the forged single-row trace `Satisfied2`s it (`flr_satCore`) yet `x = 100`
is a MEMBER of the committed set `[100, 300]`. The landed `nonRevLastRowFix` is EXACTLY what catches
it: the fixed real `nonRevocationDesc` REJECTS the forged trace — its last-row `diffLBody` boundary is
`0 − 100 + 100 + 1 = 1 ≠ 0` (`fixed_forbids_lastrow_forgery`, THE GATE). -/

/-- **`nonRevocationDescPreLast` — the descriptor WITHOUT the last-row fix** (the 14 transition-only
constraints; identical to `nonRevocationDesc` minus `nonRevLastRowFix`). This is what the emit produced
before the fix; it is the descriptor the height-1 forgery exploits. -/
def nonRevocationDescPreLast : EffectVmDescriptor2 :=
  { name        := "dregg-non-revocation-sorted-tree::poseidon2-v1-PRELAST"
  , traceWidth  := NONREV_WIDTH
  , piCount     := 2
  , tables      := [Dregg2.Circuit.DescriptorIR2.rangeTableDef ORDERING_BITS]
  , constraints :=
      [ level0Lookup
      , level1Lookup
      , .base (.gate contBody)
      , .base (.gate diffLBody)
      , .base (.gate diffRBody)
      , .base (.gate rangeLBindBody)
      , .base (.gate rangeRBindBody)
      , rangeLLookup
      , rangeRLookup
      , rangeLDiffLookup
      , rangeRDiffLookup
      , .base (.gate adjBody)
      , .base (.piBinding VmRow.first PAR1 ROOT_PI)
      , .base (.piBinding VmRow.first X QUERIED_PI) ]
  , hashSites   := []
  , ranges      := [] }

/-- The forged HEIGHT-1 row: `x = L = 100` (a genuine member of the committed set `[100,300]`), but the
lower ordering witness `DIFF_L = 0` (not the honest `x − L − 1 = −1`). On a single-row trace the
`.gate diffLBody` binding is vacuous, so this decoupling is admitted. The committed tree/root is the
SAME as the honest witness (`root = hash [hash [100,300], 7]`); only the queried item and `DIFF_L`
change. `DIFF_R = 199` honest, `RL = RR = 0` (free — their binding gates are vacuous too, only the
range lookup on them bites, and `0 ∈ [0,2^30)`). -/
private def flrRow : Assignment := fun c =>
  if c = X then 100
  else if c = LEAF_L then 100
  else if c = LEAF_R then 300
  else if c = LPOS then 5
  else if c = RPOS then 6
  else if c = DIFF_L then 0
  else if c = DIFF_R then 199
  else if c = RL then 0
  else if c = RR then 0
  else if c = PAR0 then 100000300
  else if c = CUR1 then 100000300
  else if c = SIB1 then 7
  else if c = PAR1 then 100000300000007
  else 0

private def flrPub : Assignment := fun k =>
  if k = ROOT_PI then 100000300000007 else if k = QUERIED_PI then 100 else 0

private def flrRangeTbl : List (List ℤ) := [[0], [199]]

private def flrTrace : VmTrace :=
  { rows := [flrRow], pub := flrPub
    tf := fun tid => match tid with
      | .poseidon2 => demoTbl
      | .range => flrRangeTbl
      | _ => [] }

/-- **The height-1 forgery PROVABLY `Satisfied2`s the pre-last (transition-only) descriptor.** All six
binding gates are vacuous on the single row (which is the last row), so `x = L = 100` with a decoupled
`DIFF_L = 0` sails through: the chip lookups hold (same committed root), the four range lookups hold
(`0, 199 ∈ [0,2^30)`), the pins hold (`root`, `x = 100`). The fixed descriptor rejects the same trace
(`fixed_forbids_lastrow_forgery`). -/
theorem flr_satCore :
    Satisfied2 demoHash nonRevocationDescPreLast (fun _ => 0) (fun _ => (0, 0)) [] flrTrace := by
  have hmemlog : memLog nonRevocationDescPreLast flrTrace = [] := rfl
  have hmaplog : mapLog nonRevocationDescPreLast flrTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == flrTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show flrTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    simp only [nonRevocationDescPreLast, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup,
      rangeLDiffLookup, rangeRDiffLookup] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        EmittedExpr.eval, List.map_cons, List.map_nil, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDescPreLast] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

theorem flr_chipSound : ChipTableSound demoHash (flrTrace.tf .poseidon2) :=
  demoTbl_chipSound _ rfl

theorem flr_rangeSound : RangeTableSound ORDERING_BITS (flrTrace.tf .range) := by
  intro r hr
  simp only [flrTrace, flrRangeTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨199, rfl, by decide, by decide⟩

/-- The forged queried item is a GENUINE MEMBER of the committed set — so no theorem concluding
`NonMember` from the pre-last `Satisfied2` could exist: it admits a revoked item forging freshness. -/
theorem flr_not_nonmember : ¬ NonMember ([100, 300] : List ℤ) ((envAt flrTrace 0).loc X) := by
  rintro ⟨_, hni⟩
  exact hni (by show (100 : ℤ) ∈ ([100, 300] : List ℤ); simp)

/-- **`fixed_forbids_lastrow_forgery` — THE GATE (the last-row fix bites).** The SAME height-1 forgery
does NOT `Satisfied2` the deployed FIXED `nonRevocationDesc`: `nonRevLastRowFix` supplies a
`.boundary VmRow.last diffLBody` constraint that FIRES on the single (last) row, and there
`diffLBody = DIFF_L − x + L + 1 = 0 − 100 + 100 + 1 = 1 ≠ 0`. The member-forgery that `Satisfied2`d the
transition-only descriptor is rejected — the last-row soundness hole is closed. -/
theorem fixed_forbids_lastrow_forgery :
    ¬ Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] flrTrace := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last diffLBody) ∈ nonRevocationDesc.constraints := by
    nr_mem
  have h0 := h.rowConstraints 0 (by decide) _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    show (0 + 1 == flrTrace.rows.length) = true from rfl] at h0
  revert h0; decide

/-- **`lastrow_carriers_admitted_forgery` — THE CLOSED BUG, WITNESSED (last-row class).** On the
height-1 forgery, the transition-only pre-last descriptor `Satisfied2`s, both named carriers are
realizable, the committed spine `[100,300]` is sorted with `100`/`300` adjacent — yet the queried item
`x = 100` is a genuine MEMBER, and the FIXED descriptor rejects the same trace. The `nonRevLastRowFix`
re-lowerings are LOAD-BEARING: they turn the accepted member-forgery into a rejection. -/
theorem lastrow_carriers_admitted_forgery :
    Satisfied2 demoHash nonRevocationDescPreLast (fun _ => 0) (fun _ => (0, 0)) [] flrTrace
    ∧ ChipTableSound demoHash (flrTrace.tf .poseidon2)
    ∧ RangeTableSound ORDERING_BITS (flrTrace.tf .range)
    ∧ Sorted ([100, 300] : List ℤ)
    ∧ Adjacent ([100, 300] : List ℤ) ((envAt flrTrace 0).loc LEAF_L) ((envAt flrTrace 0).loc LEAF_R)
    ∧ (envAt flrTrace 0).loc X ∈ ([100, 300] : List ℤ)
    ∧ ¬ NonMember ([100, 300] : List ℤ) ((envAt flrTrace 0).loc X)
    ∧ ¬ Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] flrTrace := by
  refine ⟨flr_satCore, flr_chipSound, flr_rangeSound, ?_, ⟨[], [], rfl⟩, ?_, flr_not_nonmember,
    fixed_forbids_lastrow_forgery⟩
  · simp [Sorted, List.pairwise_cons]
  · show (100 : ℤ) ∈ ([100, 300] : List ℤ); simp

#assert_axioms flr_satCore
#assert_axioms flr_chipSound
#assert_axioms flr_rangeSound
#assert_axioms flr_not_nonmember
#assert_axioms fixed_forbids_lastrow_forgery
#assert_axioms lastrow_carriers_admitted_forgery

end Dregg2.Circuit.Emit.NonRevocationRung2
