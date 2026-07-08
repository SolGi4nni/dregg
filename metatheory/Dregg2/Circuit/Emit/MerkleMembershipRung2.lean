/-
# Dregg2.Circuit.Emit.MerkleMembershipRung2 — the RUNG-2 no-forgery discharge for the
depth-2, 4-ary Poseidon2 Merkle-membership descriptor (`MerkleMembershipEmit.merkleMembershipDesc`).

## The bug this file both CLOSES and PINS (the adversarial-audit finding, P0)

The intended relation is `root = hash[hash[leaf, s0a, s0b, s0c], s1a, s1b, s1c]`
(`MerkleMembershipRefine.MerkleMembers2`). The only constraint tying level-1's path input `CUR1` to
level-0's parent digest `PARENT0` — the leaf-into-root chain — was `continuityGate := .base (.gate
contBody)`, a `when_transition` constraint that is VACUOUS on the last row (`holdsVm … isLast=true
(.gate _) = True`, `EffectVmEmit.lean:465`). On a **height-1 trace** row 0 is BOTH first and last, so
`CUR1` was entirely FREE, decoupling the level-0 (leaf) side from the level-1 (root) side. A prover
could commit a forged non-member `leaf` (with `PARENT0 = hash[leaf, s0*]`) while setting `CUR1` to the
REAL honest intermediate digest, land both chip lookups on genuine permutation rows, and pin `PARENT1`
to the REAL root — an accepted proof of membership for a leaf that is NOT under the committed root.

**The fix** (`MerkleMembershipEmit.continuityLastFix`, the `adjLastOrderFix` shape from commit
`0f8d478b2`): a `.base (.boundary VmRow.last contBody)` counterpart that fires on the last row, so the
level-tie `CUR1 = PARENT0` is enforced on EVERY row (transition `.gate` for rows `0..n-2`, last-row
boundary for row `n-1`) — matching the deployed every-row `assert_zero` lowering.

## What this file proves

* `contAtRow0` / `merkleMembership_no_forgery` — with the fix, the level-tie holds on row 0 for ANY
  non-empty trace (via the transition gate when row 0 is not last, via the last-row boundary when it
  is), so the whole-descriptor membership bridge now holds at `0 < height` — the height-1 case the
  Rung-1 bridge (`merkleMembership_sat_refines`, `1 < height`) could not reach. This is the direction
  the forgery attacked, now closed.

* THE REGRESSION GATE (§3): a CONCRETE height-1 forge trace — forged non-member `leaf = 99`, genuine
  chip rows for both levels, `CUR1` = the real intermediate `hash[1,2,3,4]` ≠ `PARENT0 = hash[99,1,1,1]`,
  `PARENT1` = the real root — that
    - `forge_satisfied_legacy`: **WAS** `Satisfied2` under the pre-fix 4-constraint `legacyMerkleDesc`
      (the exact forgery hole the audit found), and
    - `forge_rejected`: is now **NOT** `Satisfied2` under the fixed `merkleMembershipDesc` — the new
      last-row boundary forces `CUR1 = PARENT0`, i.e. `1020304 = 99010101`, which fails, and
    - `forge_nonmember`: is a GENUINE non-member (`99` authenticates to `99010101050607`, not the
      committed `1020304050607`).
  `forge_was_accepted_now_rejected` packages the three: same trace, accepted before, rejected after,
  never a member — the permanent non-vacuity pole of the fix.

* Non-vacuity TRUE half (§4): `honest_height1_fires` fires the strengthened bridge on a genuine
  height-1 honest witness, deriving real membership — the fix ACCEPTS the honest height-1 case.

## Sibling sweep (proof-strategy upgrade)

`merkleMembershipDesc` has exactly five constraints: `level0Lookup`, `level1Lookup` (every-row chip
lookups — never gated, fire on the last row too), `continuityGate` (the transition `.gate` fixed here),
`rootPin` (a FIRST-row PI pin — anchored at row 0, fires unconditionally there), and `continuityLastFix`
(the fix). The ONLY transition-only `.gate` binding a semantic column was `continuityGate`; every other
constraint already covers the row it needs. So the descriptor has no remaining vacuous-last-row hole.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The sole cryptographic carrier is the NAMED
chip-table faithfulness `ChipTableSound hash (t.tf .poseidon2)` (entering through `chip_lookup_sound`,
as in Rung 1), never a Lean axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.MerkleMembershipRefine

namespace Dregg2.Circuit.Emit.MerkleMembershipRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv holdsVm_boundaryLast_true)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace TraceFamily TableId envAt Lookup
   ChipTableSound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.MerkleMembershipEmit
  (merkleMembershipDesc level0Lookup level1Lookup continuityGate continuityLastFix rootPin contBody
   continuity_body_zero_iff MEMBERSHIP_WIDTH
   LEAF SIB0A SIB0B SIB0C PARENT0 CUR1 SIB1A SIB1B SIB1C PARENT1
   LEVEL0_LANES LEVEL1_LANES ROOT_PI)
open Dregg2.Circuit.Emit.MerkleMembershipRefine
  (merkleFold2 MerkleMembers2 lookupChip4 firstPi activeGateZero)

set_option autoImplicit false

/-! ## §0 — the membership tactic (every constraint we name is literally in the descriptor). -/

local macro "mm_mem" : tactic =>
  `(tactic| (show _ ∈ merkleMembershipDesc.constraints;
             simp [merkleMembershipDesc, level0Lookup, level1Lookup, continuityGate,
               continuityLastFix, rootPin]))

/-! ## §1 — the last-row extractor + the every-row level-tie (the fix's teeth). -/

/-- A declared `.boundary VmRow.last` body vanishes on the LAST row — the counterpart to
`activeGateZero` (which reads the transition rows). This is the leg the fix adds. -/
theorem lastBoundaryZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hlast : (j + 1 == t.rows.length) = true)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.boundary VmRow.last body) ∈ merkleMembershipDesc.constraints) :
    body.eval (envAt t j).loc = 0 := by
  have h := hsat.rowConstraints j hj _ hmem
  rw [hlast] at h
  simp only [VmConstraint2.holdsAt, holdsVm_boundaryLast_true] at h
  exact h

/-- **`contAtRow0` — the level-tie `CUR1 = PARENT0` on row 0 of ANY non-empty trace.** This is what the
fix buys over Rung 1: if row 0 is a transition row (`1 < height`) the transition `continuityGate` fires;
if row 0 IS the last row (`height = 1`, the forgery's case) the new `continuityLastFix` fires. Either
way the levels chain — so `CUR1` is no longer free on a height-1 trace. -/
theorem contAtRow0 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hpos : 0 < t.rows.length)
    (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t) :
    (envAt t 0).loc CUR1 = (envAt t 0).loc PARENT0 := by
  by_cases hlast : (0 + 1 == t.rows.length) = true
  · -- row 0 is the last row (height 1): the last-row boundary continuity fix fires.
    exact (continuity_body_zero_iff (envAt t 0).loc).mp
      (lastBoundaryZero hsat 0 hpos hlast contBody (by mm_mem))
  · -- row 0 is a transition row (height > 1): the transition continuity gate fires.
    have hf : (0 + 1 == t.rows.length) = false := by
      simp only [Bool.not_eq_true] at hlast; exact hlast
    exact (continuity_body_zero_iff (envAt t 0).loc).mp
      (activeGateZero hsat 0 hpos hf contBody (by mm_mem))

/-! ## §2 — the strengthened whole-descriptor bridge (no-forgery, any non-empty height). -/

/-- **`merkleMembership_no_forgery` — SAT_IMPLIES_SEM at `0 < height`.** With the fix, a `Satisfied2`
trace against the NAMED Poseidon2 chip carrier binds the genuine depth-2 Merkle-membership relation
between the row-0 witness columns and the committed root PI — for ANY non-empty trace, including the
height-1 case the Rung-1 bridge (`merkleMembership_sat_refines`, `1 < height`) could not reach and the
forgery exploited. The level-tie now comes from `contAtRow0` (every-row), not the transition gate. -/
theorem merkleMembership_no_forgery {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hpos : 0 < t.rows.length)
    (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    MerkleMembers2 hash
      ((envAt t 0).loc LEAF) ((envAt t 0).loc SIB0A) ((envAt t 0).loc SIB0B) ((envAt t 0).loc SIB0C)
      ((envAt t 0).loc SIB1A) ((envAt t 0).loc SIB1B) ((envAt t 0).loc SIB1C)
      (t.pub ROOT_PI) := by
  have hp0 : (envAt t 0).loc PARENT0
      = hash [(envAt t 0).loc LEAF, (envAt t 0).loc SIB0A, (envAt t 0).loc SIB0B,
              (envAt t 0).loc SIB0C] :=
    lookupChip4 hsat hChip 0 hpos LEAF SIB0A SIB0B SIB0C PARENT0 LEVEL0_LANES (by mm_mem)
  have hp1 : (envAt t 0).loc PARENT1
      = hash [(envAt t 0).loc CUR1, (envAt t 0).loc SIB1A, (envAt t 0).loc SIB1B,
              (envAt t 0).loc SIB1C] :=
    lookupChip4 hsat hChip 0 hpos CUR1 SIB1A SIB1B SIB1C PARENT1 LEVEL1_LANES (by mm_mem)
  have hcont : (envAt t 0).loc CUR1 = (envAt t 0).loc PARENT0 := contAtRow0 hpos hsat
  have hroot : (envAt t 0).loc PARENT1 = t.pub ROOT_PI :=
    firstPi hsat hpos PARENT1 ROOT_PI (by mm_mem)
  unfold MerkleMembers2 merkleFold2
  rw [← hroot, hp1, hcont, hp0]

/-! ## §3 — THE REGRESSION GATE: the audit's height-1 forge, accepted before / rejected now. -/

/-- The order-sensitive little-endian digit hash — injective enough to distinguish levels; the same
shape `MerkleMembershipRefine`'s witnesses ride. `fHash [a,b,c,d] = a·100³ + b·100² + c·100 + d`. -/
private def fHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **The forging row (height-1).** A forged NON-member leaf `99` with siblings `1,1,1`, so
`PARENT0 = fHash[99,1,1,1] = 99010101`. The chained input `CUR1` is set to the REAL honest
intermediate `fHash[1,2,3,4] = 1020304` (≠ `PARENT0`, the decoupling the vacuous continuity allowed),
level-1 siblings `5,6,7`, and top parent `PARENT1 = fHash[1020304,5,6,7] = 1020304050607` = the REAL
root. Every lane / unused column is `0`. -/
private def fRow : Assignment := fun c =>
  if c = LEAF then 99 else if c = SIB0A then 1 else if c = SIB0B then 1 else if c = SIB0C then 1
  else if c = PARENT0 then 99010101
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607 else 0

/-- The committed public root is the REAL root `1020304050607` — the leaf `99` does NOT hash to it. -/
private def fPub : Assignment := fun k => if k = ROOT_PI then 1020304050607 else 0

/-- The chip table: the two GENUINE `child → parent` `chipRow`s the two lookups absorb (both land on
real permutation rows — the forgery does not lie about the hashes, it lies about the LEVEL-TIE). -/
private def fTbl : List (List ℤ) :=
  [chipRow fHash [99, 1, 1, 1] (List.replicate 7 0),
   chipRow fHash [1020304, 5, 6, 7] (List.replicate 7 0)]

/-- The concrete HEIGHT-1 forging trace (`rows = [fRow]`, so row 0 is BOTH first and last — exactly the
degenerate height the vacuous continuity gate failed to constrain). -/
private def fTrace : VmTrace :=
  { rows := [fRow], pub := fPub
    tf := fun tid => match tid with | .poseidon2 => fTbl | _ => [] }

/-- **The forge's chip table is genuinely SOUND** — each row is a real `chipRow fHash` of its absorbed
inputs, so the NAMED carrier `ChipTableSound` HOLDS for the forgery. The rejection therefore is NOT a
malformed table; it is precisely the level-tie the fix restored. -/
theorem fTf_chipSound : ChipTableSound fHash (fTrace.tf .poseidon2) := by
  intro r hr
  simp only [fTrace, fTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[99, 1, 1, 1], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩

/-- **The forged leaf is a GENUINE non-member.** `99` authenticates to
`fHash[fHash[99,1,1,1],5,6,7] = 99010101050607`, NOT the committed root `1020304050607`. So the trace
below is a real forgery: an accepted proof (pre-fix) of membership for a leaf not under the root. -/
theorem forge_nonmember : ¬ MerkleMembers2 fHash 99 1 1 1 5 6 7 1020304050607 := by
  unfold MerkleMembers2 merkleFold2 fHash; decide

/-! ### §3a — the PRE-FIX descriptor and the forgery it accepted. -/

/-- **`legacyMerkleDesc`** — the descriptor EXACTLY as it stood before the fix: the two chip lookups,
the transition-only continuity `.gate`, and the root pin — WITHOUT `continuityLastFix`. This is the
under-constrained shape the audit found. -/
def legacyMerkleDesc : EffectVmDescriptor2 :=
  { merkleMembershipDesc with
    constraints := [level0Lookup, level1Lookup, continuityGate, rootPin] }

/-- **THE FORGERY HOLE (pre-fix acceptance).** The height-1 forge trace `Satisfied2`s the pre-fix
`legacyMerkleDesc`: both chip lookups land in the sound table, the continuity `.gate` is VACUOUS on the
only/last row (so `CUR1 = 1020304 ≠ 99010101 = PARENT0` is never checked), and the first-row root pin
`PARENT1 = 1020304050607` holds. An accepted proof of a FALSE membership — the bug. -/
theorem forge_satisfied_legacy :
    Satisfied2 fHash legacyMerkleDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  have hmemlog : memLog legacyMerkleDesc fTrace = [] := rfl
  have hmaplog : mapLog legacyMerkleDesc fTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show fTrace.rows.length = 1 from rfl] at hi
    rw [show legacyMerkleDesc.constraints
          = [level0Lookup, level1Lookup, continuityGate, rootPin] from rfl] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        level0Lookup, level1Lookup, continuityGate, rootPin] <;>
      trivial
  · intro i _; trivial
  · intro i _ r hr; simp [legacyMerkleDesc, merkleMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **THE FIX (post-fix rejection — the regression).** The SAME forge trace is NOT `Satisfied2` under
the fixed `merkleMembershipDesc`: on the height-1 trace row 0 is the last row, so `continuityLastFix`
fires and forces `CUR1 = PARENT0`, i.e. `1020304 = 99010101` — false. The specific accepted-but-non-
satisfying witness the audit found is now UNSAT. -/
theorem forge_rejected :
    ¬ Satisfied2 fHash merkleMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last contBody)
      ∈ merkleMembershipDesc.constraints := by mm_mem
  have hlast : (0 + 1 == fTrace.rows.length) = true := by decide
  have h0 := lastBoundaryZero h 0 (by decide) hlast contBody hmem
  revert h0; decide

/-- **THE REGRESSION, packaged.** The exact audit witness is accepted by the pre-fix descriptor, is a
genuine non-member, and is REJECTED by the fixed descriptor. This is the forgery closed and pinned. -/
theorem forge_was_accepted_now_rejected :
    Satisfied2 fHash legacyMerkleDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace
      ∧ ¬ MerkleMembers2 fHash 99 1 1 1 5 6 7 1020304050607
      ∧ ¬ Satisfied2 fHash merkleMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace :=
  ⟨forge_satisfied_legacy, forge_nonmember, forge_rejected⟩

/-! ## §4 — non-vacuity TRUE half: the fix ACCEPTS a genuine height-1 honest witness, and the
strengthened bridge FIRES on it (deriving real membership the Rung-1 `1 < height` bridge could not). -/

/-- The honest height-1 row: leaf `1`, level-0 siblings `2,3,4`, `PARENT0 = fHash[1,2,3,4] = 1020304`,
the chained input `CUR1 = 1020304` (= PARENT0, honest), level-1 siblings `5,6,7`, top parent
`PARENT1 = fHash[1020304,5,6,7] = 1020304050607`. -/
private def hRow : Assignment := fun c =>
  if c = LEAF then 1 else if c = SIB0A then 2 else if c = SIB0B then 3 else if c = SIB0C then 4
  else if c = PARENT0 then 1020304
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607 else 0

private def hPub : Assignment := fun k => if k = ROOT_PI then 1020304050607 else 0

private def hTbl : List (List ℤ) :=
  [chipRow fHash [1, 2, 3, 4] (List.replicate 7 0),
   chipRow fHash [1020304, 5, 6, 7] (List.replicate 7 0)]

/-- The genuine HEIGHT-1 honest trace (`rows = [hRow]`) — the case the fix makes provable. -/
private def hTrace : VmTrace :=
  { rows := [hRow], pub := hPub
    tf := fun tid => match tid with | .poseidon2 => hTbl | _ => [] }

/-- The honest chip table is SOUND. -/
theorem hTf_chipSound : ChipTableSound fHash (hTrace.tf .poseidon2) := by
  intro r hr
  simp only [hTrace, hTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[1, 2, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩

/-- **The honest height-1 trace `Satisfied2`s the FIXED descriptor** — all five constraints hold on the
single row: both chip lookups land, the transition gate is vacuous (last row), the root pin closes, and
the new `continuityLastFix` closes because `CUR1 = PARENT0 = 1020304` (honest chaining). So the fix does
NOT over-constrain: honest height-1 membership is still accepted. -/
theorem hTrace_satisfied2 :
    Satisfied2 fHash merkleMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace := by
  have hmemlog : memLog merkleMembershipDesc hTrace = [] := rfl
  have hmaplog : mapLog merkleMembershipDesc hTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hTrace.rows.length = 1 from rfl] at hi
    rw [show merkleMembershipDesc.constraints
          = [level0Lookup, level1Lookup, continuityGate, rootPin, continuityLastFix] from rfl] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        level0Lookup, level1Lookup, continuityGate, continuityLastFix, rootPin] <;>
      trivial
  · intro i _; trivial
  · intro i _ r hr; simp [merkleMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **THE STRENGTHENED BRIDGE FIRES on a genuine height-1 witness (the TRUE half).** All three
hypotheses (`0 < height`, `Satisfied2`, `ChipTableSound`) hold, and membership is DERIVED — the Rung-1
bridge could not even state this (it needs `1 < height`). Non-vacuous: the antecedent is inhabited. -/
theorem honest_height1_fires :
    MerkleMembers2 fHash
      ((envAt hTrace 0).loc LEAF) ((envAt hTrace 0).loc SIB0A) ((envAt hTrace 0).loc SIB0B)
      ((envAt hTrace 0).loc SIB0C) ((envAt hTrace 0).loc SIB1A) ((envAt hTrace 0).loc SIB1B)
      ((envAt hTrace 0).loc SIB1C) (hTrace.pub ROOT_PI) :=
  merkleMembership_no_forgery (by decide) hTrace_satisfied2 hTf_chipSound

/-- The fired witness IS the closed-form true instance `1020304050607 = fHash[fHash[1,2,3,4],5,6,7]`. -/
theorem honest_height1_is_member :
    (MerkleMembers2 fHash
        ((envAt hTrace 0).loc LEAF) ((envAt hTrace 0).loc SIB0A) ((envAt hTrace 0).loc SIB0B)
        ((envAt hTrace 0).loc SIB0C) ((envAt hTrace 0).loc SIB1A) ((envAt hTrace 0).loc SIB1B)
        ((envAt hTrace 0).loc SIB1C) (hTrace.pub ROOT_PI))
      ↔ MerkleMembers2 fHash 1 2 3 4 5 6 7 1020304050607 := Iff.rfl

/-! ## §5 — shape pins + axiom hygiene. -/

#guard decide (fTrace.rows.length = 1)
#guard decide (hTrace.rows.length = 1)
#guard legacyMerkleDesc.constraints.length == 4
#guard merkleMembershipDesc.constraints.length == 5
-- the forged leaf's TRUE root differs from the committed root (the forgery is real):
#guard merkleFold2 fHash 99 1 1 1 5 6 7 != 1020304050607
-- the honest leaf's TRUE root IS the committed root (the accepted witness is real):
#guard merkleFold2 fHash 1 2 3 4 5 6 7 == 1020304050607

#assert_axioms lastBoundaryZero
#assert_axioms contAtRow0
#assert_axioms merkleMembership_no_forgery
#assert_axioms fTf_chipSound
#assert_axioms forge_nonmember
#assert_axioms forge_satisfied_legacy
#assert_axioms forge_rejected
#assert_axioms forge_was_accepted_now_rejected
#assert_axioms hTf_chipSound
#assert_axioms hTrace_satisfied2
#assert_axioms honest_height1_fires

end Dregg2.Circuit.Emit.MerkleMembershipRung2
