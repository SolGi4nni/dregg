/-
# Dregg2.Circuit.Emit.BlindedMembershipRung2 — the RUNG-2 no-forgery + unlinkability discharge for the
blinded ring-membership descriptor (`BlindedMembershipEmit.blindedMembershipDesc`).

## What this file proves (the three teeth + the unlinkability pole)

The descriptor makes TWO claims a forger might attack: (1) the published `blinded_leaf` really is
`hash_2_to_1(leaf_hash, blinding)`, and (2) `leaf_hash` sits under the public `root`. Rung 2 pins that
BOTH bite, and that the intended unlinkability holds.

* `lastBoundaryZero` / `contAtRow0` / `blindedMembership_no_forgery` — the same height-1 level-tie hole
  `MerkleMembershipRung2` closed (the `when_transition` continuity gate is vacuous on the last row, so
  on a height-1 trace `CUR1` was free, decoupling the forged leaf from the real intermediate). The
  `continuityLastFix` boundary makes `CUR1 = PARENT0` hold on EVERY row, so the whole-descriptor bridge
  now holds at `0 < height` — the height the forgery exploited.

* THE MEMBERSHIP FORGE (§3): a CONCRETE height-1 forge — forged non-member `leaf = 99`, genuine chip
  rows, `CUR1` = the real intermediate ≠ `PARENT0`, `PARENT1` = the real root — that
    - `forge_satisfied_legacy`: WAS `Satisfied2` under the pre-fix `legacyBlindedDesc`, and
    - `forge_nonmember_rejected`: is now NOT `Satisfied2` under the fixed descriptor (the last-row
      boundary forces `CUR1 = PARENT0`, i.e. `1020304 = 99010101`, false), and
    - `forge_nonmember`: is a GENUINE non-member.

* THE BLINDING FORGE (§3b): `forge_blinded_leaf_rejected` — a trace publishing a `blinded_leaf` that is
  NOT `hash_2_to_1(leaf_hash, blinding)`, against a SOUND chip table, is UNSAT: the arity-2 blinding
  chip tooth (`lookupChip2`) forces the digest to the genuine Poseidon2 image, contradicting the forged
  value. The unlinkable commitment cannot be spoofed.

* NON-VACUITY TRUE half (§4): `honest_satisfied2` — the fix ACCEPTS a genuine height-1 honest show, and
  `honest_height1_fires` fires the strengthened bridge on it (deriving real blinded membership).

* THE UNLINKABILITY POLE (§5): `honest_two_shows_unlinkable` — the in-circuit twin of
  `credentials/tests/anonymity_soundness.rs`. ONE credential (same `leaf_hash`, same `root`) shown with
  two DIFFERENT blinding factors yields two DIFFERENT published `blinded_leaf`, BOTH `Satisfied2`. The
  hidden fresh factor is exactly what makes two shows unlinkable while both prove the same membership.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The sole cryptographic carrier is the NAMED
chip-table faithfulness `ChipTableSound hash (t.tf .poseidon2)` (through `chip_lookup_sound`), never a
Lean axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.BlindedMembershipRefine

namespace Dregg2.Circuit.Emit.BlindedMembershipRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv holdsVm_boundaryLast_true)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace TraceFamily TableId envAt Lookup
   ChipTableSound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.BlindedMembershipEmit
  (blindedMembershipDesc level0Lookup level1Lookup blindLookup continuityGate continuityLastFix
   rootPin blindedLeafPin contBody continuity_body_zero_iff
   LEAF SIB0A SIB0B SIB0C PARENT0 CUR1 SIB1A SIB1B SIB1C PARENT1 BLINDING BLINDED_LEAF
   LEVEL0_LANES LEVEL1_LANES BLIND_LANES ROOT_PI BLINDED_LEAF_PI)
open Dregg2.Circuit.Emit.MerkleMembershipRefine (merkleFold2 MerkleMembers2)
open Dregg2.Circuit.Emit.BlindedMembershipRefine
  (BlindedMembers lookupChip4 lookupChip2 firstPi activeGateZero)

set_option autoImplicit false

/-! ## §0 — the membership tactic. -/

local macro "bm_mem" : tactic =>
  `(tactic| (show _ ∈ blindedMembershipDesc.constraints;
             simp [blindedMembershipDesc, level0Lookup, level1Lookup, blindLookup, continuityGate,
               continuityLastFix, rootPin, blindedLeafPin]))

/-! ## §1 — the last-row extractor + the every-row level-tie (the fix's teeth). -/

/-- A declared `.boundary VmRow.last` body vanishes on the LAST row — the leg the fix adds. -/
theorem lastBoundaryZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hlast : (j + 1 == t.rows.length) = true)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.boundary VmRow.last body) ∈ blindedMembershipDesc.constraints) :
    body.eval (envAt t j).loc = 0 := by
  have h := hsat.rowConstraints j hj _ hmem
  rw [hlast] at h
  simp only [VmConstraint2.holdsAt, holdsVm_boundaryLast_true] at h
  exact h

/-- **`contAtRow0` — the level-tie `CUR1 = PARENT0` on row 0 of ANY non-empty trace.** Transition gate
when `1 < height`; the new last-row boundary fix when `height = 1` (the forgery's case). -/
theorem contAtRow0 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hpos : 0 < t.rows.length)
    (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t) :
    (envAt t 0).loc CUR1 = (envAt t 0).loc PARENT0 := by
  by_cases hlast : (0 + 1 == t.rows.length) = true
  · exact (continuity_body_zero_iff (envAt t 0).loc).mp
      (lastBoundaryZero hsat 0 hpos hlast contBody (by bm_mem))
  · have hf : (0 + 1 == t.rows.length) = false := by
      simp only [Bool.not_eq_true] at hlast; exact hlast
    exact (continuity_body_zero_iff (envAt t 0).loc).mp
      (activeGateZero hsat 0 hpos hf contBody (by bm_mem))

/-! ## §2 — the strengthened whole-descriptor bridge (no-forgery, any non-empty height). -/

/-- **`blindedMembership_no_forgery` — SAT_IMPLIES_SEM at `0 < height`.** With the fix, a `Satisfied2`
trace against the NAMED chip carrier binds the genuine blinded ring-membership relation for ANY
non-empty trace — including the height-1 case the Rung-1 bridge could not reach and the forgery
exploited. The level-tie now comes from `contAtRow0` (every-row), not the transition gate. -/
theorem blindedMembership_no_forgery {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hpos : 0 < t.rows.length)
    (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    BlindedMembers hash
      (t.pub BLINDED_LEAF_PI)
      ((envAt t 0).loc LEAF) ((envAt t 0).loc BLINDING)
      ((envAt t 0).loc SIB0A) ((envAt t 0).loc SIB0B) ((envAt t 0).loc SIB0C)
      ((envAt t 0).loc SIB1A) ((envAt t 0).loc SIB1B) ((envAt t 0).loc SIB1C)
      (t.pub ROOT_PI) := by
  refine ⟨?_, ?_⟩
  · have hbleaf : (envAt t 0).loc BLINDED_LEAF = t.pub BLINDED_LEAF_PI :=
      firstPi hsat hpos BLINDED_LEAF BLINDED_LEAF_PI (by bm_mem)
    have hblind : (envAt t 0).loc BLINDED_LEAF
        = hash [(envAt t 0).loc LEAF, (envAt t 0).loc BLINDING] :=
      lookupChip2 hsat hChip 0 hpos LEAF BLINDING BLINDED_LEAF BLIND_LANES (by bm_mem)
    rw [← hbleaf]; exact hblind
  · have hp0 : (envAt t 0).loc PARENT0
        = hash [(envAt t 0).loc LEAF, (envAt t 0).loc SIB0A, (envAt t 0).loc SIB0B,
                (envAt t 0).loc SIB0C] :=
      lookupChip4 hsat hChip 0 hpos LEAF SIB0A SIB0B SIB0C PARENT0 LEVEL0_LANES (by bm_mem)
    have hp1 : (envAt t 0).loc PARENT1
        = hash [(envAt t 0).loc CUR1, (envAt t 0).loc SIB1A, (envAt t 0).loc SIB1B,
                (envAt t 0).loc SIB1C] :=
      lookupChip4 hsat hChip 0 hpos CUR1 SIB1A SIB1B SIB1C PARENT1 LEVEL1_LANES (by bm_mem)
    have hcont : (envAt t 0).loc CUR1 = (envAt t 0).loc PARENT0 := contAtRow0 hpos hsat
    have hroot : (envAt t 0).loc PARENT1 = t.pub ROOT_PI :=
      firstPi hsat hpos PARENT1 ROOT_PI (by bm_mem)
    unfold MerkleMembers2 merkleFold2
    rw [← hroot, hp1, hcont, hp0]

/-! ## §3 — THE MEMBERSHIP FORGE: the height-1 non-member, accepted before / rejected now. -/

/-- The order-sensitive little-endian digit hash. -/
private def fHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **The forging row (height-1).** A forged NON-member leaf `99` (siblings `1,1,1`), so
`PARENT0 = fHash[99,1,1,1] = 99010101`. `CUR1` is set to the REAL honest intermediate
`fHash[1,2,3,4] = 1020304` (≠ `PARENT0` — the decoupling the vacuous continuity allowed), siblings
`5,6,7`, top parent `PARENT1 = 1020304050607` = the REAL root; blinding `8`, blinded `fHash[99,8]=9908`. -/
private def fRow : Assignment := fun c =>
  if c = LEAF then 99 else if c = SIB0A then 1 else if c = SIB0B then 1 else if c = SIB0C then 1
  else if c = PARENT0 then 99010101
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607
  else if c = BLINDING then 8 else if c = BLINDED_LEAF then 9908 else 0

private def fPub : Assignment := fun k =>
  if k = BLINDED_LEAF_PI then 9908 else if k = ROOT_PI then 1020304050607 else 0

private def fTbl : List (List ℤ) :=
  [chipRow fHash [99, 1, 1, 1] (List.replicate 7 0),
   chipRow fHash [1020304, 5, 6, 7] (List.replicate 7 0),
   chipRow fHash [99, 8] (List.replicate 7 0)]

/-- The concrete HEIGHT-1 forging trace (`rows = [fRow]`, row 0 is BOTH first and last). -/
private def fTrace : VmTrace :=
  { rows := [fRow], pub := fPub
    tf := fun tid => match tid with | .poseidon2 => fTbl | _ => [] }

/-- **The forge's chip table is genuinely SOUND** — each row is a real `chipRow fHash`. The rejection
is NOT a malformed table; it is precisely the level-tie the fix restored. -/
theorem fTf_chipSound : ChipTableSound fHash (fTrace.tf .poseidon2) := by
  intro r hr
  simp only [fTrace, fTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h
  · exact ⟨[99, 1, 1, 1], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[99, 8], List.replicate 7 0, by decide, by decide, h⟩

/-- **The forged leaf is a GENUINE non-member.** `99` authenticates to `99010101050607`, NOT the
committed root `1020304050607`. -/
theorem forge_nonmember : ¬ MerkleMembers2 fHash 99 1 1 1 5 6 7 1020304050607 := by
  unfold MerkleMembers2 merkleFold2 fHash; decide

/-- **`legacyBlindedDesc`** — the descriptor as it stood before the last-row fix (no
`continuityLastFix`). The under-constrained shape. -/
def legacyBlindedDesc : EffectVmDescriptor2 :=
  { blindedMembershipDesc with
    constraints := [level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin,
                    blindedLeafPin] }

/-- **THE FORGERY HOLE (pre-fix acceptance).** The height-1 forge `Satisfied2`s `legacyBlindedDesc`:
the three chip lookups land, the continuity `.gate` is VACUOUS on the only/last row (so
`CUR1 = 1020304 ≠ 99010101 = PARENT0` is never checked), and the two first-row PI pins hold. An
accepted proof of a FALSE membership. -/
theorem forge_satisfied_legacy :
    Satisfied2 fHash legacyBlindedDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  have hmemlog : memLog legacyBlindedDesc fTrace = [] := rfl
  have hmaplog : mapLog legacyBlindedDesc fTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show fTrace.rows.length = 1 from rfl] at hi
    rw [show legacyBlindedDesc.constraints
          = [level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin, blindedLeafPin]
          from rfl] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin, blindedLeafPin] <;>
      trivial
  · intro i _; trivial
  · intro i _ r hr; simp [legacyBlindedDesc, blindedMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **`forge_nonmember_rejected` — THE FIX (post-fix rejection).** The SAME forge is NOT `Satisfied2`
under the fixed `blindedMembershipDesc`: on the height-1 trace row 0 is the last row, so
`continuityLastFix` fires and forces `CUR1 = PARENT0`, i.e. `1020304 = 99010101` — false. -/
theorem forge_nonmember_rejected :
    ¬ Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last contBody)
      ∈ blindedMembershipDesc.constraints := by bm_mem
  have hlast : (0 + 1 == fTrace.rows.length) = true := by decide
  have h0 := lastBoundaryZero h 0 (by decide) hlast contBody hmem
  revert h0; decide

/-- **THE MEMBERSHIP REGRESSION, packaged.** Accepted pre-fix, genuine non-member, rejected post-fix. -/
theorem forge_was_accepted_now_rejected :
    Satisfied2 fHash legacyBlindedDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace
      ∧ ¬ MerkleMembers2 fHash 99 1 1 1 5 6 7 1020304050607
      ∧ ¬ Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace :=
  ⟨forge_satisfied_legacy, forge_nonmember, forge_nonmember_rejected⟩

/-! ## §3b — THE BLINDING FORGE: a spoofed `blinded_leaf` is UNSAT (the arity-2 tooth bites). -/

/-- The blinding-forge row: honest member `1` under the real root, but the published `BLINDED_LEAF` is
the SPOOFED value `777` — NOT `fHash[1,8] = 108`. The chained input is honest (`CUR1 = PARENT0`), so
only the blinding tooth can reject it. -/
private def gRow : Assignment := fun c =>
  if c = LEAF then 1 else if c = SIB0A then 2 else if c = SIB0B then 3 else if c = SIB0C then 4
  else if c = PARENT0 then 1020304
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607
  else if c = BLINDING then 8 else if c = BLINDED_LEAF then 777 else 0

private def gPub : Assignment := fun k =>
  if k = BLINDED_LEAF_PI then 777 else if k = ROOT_PI then 1020304050607 else 0

/-- The chip table is the GENUINE one (containing the real `fHash[1,8]=108` blinding row) — so it is
SOUND. The spoof lies in the trace's `BLINDED_LEAF` column, not the table. -/
private def gTbl : List (List ℤ) :=
  [chipRow fHash [1, 2, 3, 4] (List.replicate 7 0),
   chipRow fHash [1020304, 5, 6, 7] (List.replicate 7 0),
   chipRow fHash [1, 8] (List.replicate 7 0)]

private def gTrace : VmTrace :=
  { rows := [gRow], pub := gPub
    tf := fun tid => match tid with | .poseidon2 => gTbl | _ => [] }

/-- The blinding-forge chip table is genuinely SOUND for `fHash`. -/
theorem gTf_chipSound : ChipTableSound fHash (gTrace.tf .poseidon2) := by
  intro r hr
  simp only [gTrace, gTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h
  · exact ⟨[1, 2, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1, 8], List.replicate 7 0, by decide, by decide, h⟩

/-- **`forge_blinded_leaf_rejected` — the arity-2 blinding tooth BITES.** Against the SOUND chip table,
a trace whose published `blinded_leaf` (`777`) is not `hash_2_to_1(leaf_hash, blinding) = fHash[1,8] =
108` cannot be `Satisfied2`: the blinding chip lookup (`lookupChip2`) forces `BLINDED_LEAF` to the
genuine Poseidon2 image, i.e. `777 = 108` — false. The unlinkable commitment cannot be spoofed. -/
theorem forge_blinded_leaf_rejected :
    ¬ Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] gTrace := by
  intro h
  have hblind := lookupChip2 h gTf_chipSound 0 (by decide) LEAF BLINDING BLINDED_LEAF BLIND_LANES
    (by bm_mem)
  revert hblind
  simp only [gTrace, envAt]
  unfold fHash
  decide

/-! ## §4 — non-vacuity TRUE half: the fix ACCEPTS a genuine height-1 honest show. -/

/-- The honest height-1 show (blinding `8`): member `1` under root `1020304050607`, honest chaining
`CUR1 = PARENT0 = 1020304`, blinded leaf `fHash[1,8] = 108`. -/
private def hRow : Assignment := fun c =>
  if c = LEAF then 1 else if c = SIB0A then 2 else if c = SIB0B then 3 else if c = SIB0C then 4
  else if c = PARENT0 then 1020304
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607
  else if c = BLINDING then 8 else if c = BLINDED_LEAF then 108 else 0

private def hPub : Assignment := fun k =>
  if k = BLINDED_LEAF_PI then 108 else if k = ROOT_PI then 1020304050607 else 0

private def hTbl : List (List ℤ) :=
  [chipRow fHash [1, 2, 3, 4] (List.replicate 7 0),
   chipRow fHash [1020304, 5, 6, 7] (List.replicate 7 0),
   chipRow fHash [1, 8] (List.replicate 7 0)]

private def hTrace : VmTrace :=
  { rows := [hRow], pub := hPub
    tf := fun tid => match tid with | .poseidon2 => hTbl | _ => [] }

theorem hTf_chipSound : ChipTableSound fHash (hTrace.tf .poseidon2) := by
  intro r hr
  simp only [hTrace, hTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h
  · exact ⟨[1, 2, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1, 8], List.replicate 7 0, by decide, by decide, h⟩

/-- **`honest_satisfied2` — the fix does NOT over-constrain.** The honest height-1 show `Satisfied2`s
the FIXED descriptor: all seven constraints hold (the three chip lookups land, the transition gate is
vacuous on the last row, the two PI pins close, and `continuityLastFix` closes because
`CUR1 = PARENT0 = 1020304`). -/
theorem honest_satisfied2 :
    Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace := by
  have hmemlog : memLog blindedMembershipDesc hTrace = [] := rfl
  have hmaplog : mapLog blindedMembershipDesc hTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hTrace.rows.length = 1 from rfl] at hi
    rw [show blindedMembershipDesc.constraints
          = [level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin, blindedLeafPin,
             continuityLastFix] from rfl] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        level0Lookup, level1Lookup, blindLookup, continuityGate, continuityLastFix, rootPin,
        blindedLeafPin] <;>
      trivial
  · intro i _; trivial
  · intro i _ r hr; simp [blindedMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The strengthened bridge FIRES on a genuine height-1 witness (the TRUE half).** All three
hypotheses hold; blinded membership is DERIVED — the Rung-1 bridge could not even state this. -/
theorem honest_height1_fires :
    BlindedMembers fHash
      (hTrace.pub BLINDED_LEAF_PI)
      ((envAt hTrace 0).loc LEAF) ((envAt hTrace 0).loc BLINDING)
      ((envAt hTrace 0).loc SIB0A) ((envAt hTrace 0).loc SIB0B) ((envAt hTrace 0).loc SIB0C)
      ((envAt hTrace 0).loc SIB1A) ((envAt hTrace 0).loc SIB1B) ((envAt hTrace 0).loc SIB1C)
      (hTrace.pub ROOT_PI) :=
  blindedMembership_no_forgery (by decide) honest_satisfied2 hTf_chipSound

/-! ## §5 — THE UNLINKABILITY POLE: two shows of ONE credential publish DIFFERENT blinded leaves,
both accepted (the in-circuit twin of `credentials/tests/anonymity_soundness.rs`). -/

/-- Show #2 of the SAME credential — identical member `1`, identical root, but a fresh blinding factor
`9` (≠ show #1's `8`), so the published blinded leaf is `fHash[1,9] = 109` (≠ `108`). -/
private def hRow2 : Assignment := fun c =>
  if c = LEAF then 1 else if c = SIB0A then 2 else if c = SIB0B then 3 else if c = SIB0C then 4
  else if c = PARENT0 then 1020304
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607
  else if c = BLINDING then 9 else if c = BLINDED_LEAF then 109 else 0

private def hPub2 : Assignment := fun k =>
  if k = BLINDED_LEAF_PI then 109 else if k = ROOT_PI then 1020304050607 else 0

private def hTbl2 : List (List ℤ) :=
  [chipRow fHash [1, 2, 3, 4] (List.replicate 7 0),
   chipRow fHash [1020304, 5, 6, 7] (List.replicate 7 0),
   chipRow fHash [1, 9] (List.replicate 7 0)]

private def hTrace2 : VmTrace :=
  { rows := [hRow2], pub := hPub2
    tf := fun tid => match tid with | .poseidon2 => hTbl2 | _ => [] }

/-- Show #2's chip table is SOUND. -/
theorem honest_satisfied2_show2 :
    Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace2 := by
  have hmemlog : memLog blindedMembershipDesc hTrace2 = [] := rfl
  have hmaplog : mapLog blindedMembershipDesc hTrace2 = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hTrace2.rows.length = 1 from rfl] at hi
    rw [show blindedMembershipDesc.constraints
          = [level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin, blindedLeafPin,
             continuityLastFix] from rfl] at hc
    interval_cases i
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        level0Lookup, level1Lookup, blindLookup, continuityGate, continuityLastFix, rootPin,
        blindedLeafPin] <;>
      trivial
  · intro i _; trivial
  · intro i _ r hr; simp [blindedMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **`honest_two_shows_unlinkable` — THE UNLINKABILITY WITNESS (in-circuit).** ONE credential — the
SAME hidden `leaf_hash` (`= 1` in both), the SAME public `root` — shown twice with two DIFFERENT
hidden blinding factors publishes two DIFFERENT `blinded_leaf` (`108 ≠ 109`), and BOTH shows are
`Satisfied2`. This mirrors `credentials/tests/anonymity_soundness.rs`: the fresh hidden factor makes
the two presentations unlinkable while both remain valid proofs of the same membership. -/
theorem honest_two_shows_unlinkable :
    Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace
      ∧ Satisfied2 fHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace2
      ∧ (envAt hTrace 0).loc LEAF = (envAt hTrace2 0).loc LEAF
      ∧ hTrace.pub ROOT_PI = hTrace2.pub ROOT_PI
      ∧ hTrace.pub BLINDED_LEAF_PI ≠ hTrace2.pub BLINDED_LEAF_PI := by
  refine ⟨honest_satisfied2, honest_satisfied2_show2, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide

/-! ## §6 — shape pins + axiom hygiene. -/

#guard decide (fTrace.rows.length = 1)
#guard decide (hTrace.rows.length = 1)
#guard decide (hTrace2.rows.length = 1)
#guard legacyBlindedDesc.constraints.length == 6
#guard blindedMembershipDesc.constraints.length == 7
-- the forged leaf's TRUE root differs from the committed root (the membership forge is real):
#guard merkleFold2 fHash 99 1 1 1 5 6 7 != 1020304050607
-- the honest leaf's TRUE root IS the committed root:
#guard merkleFold2 fHash 1 2 3 4 5 6 7 == 1020304050607
-- two shows genuinely differ (108 ≠ 109) though they blind the SAME leaf `1`:
#guard fHash [1, 8] != fHash [1, 9]

#assert_axioms lastBoundaryZero
#assert_axioms contAtRow0
#assert_axioms blindedMembership_no_forgery
#assert_axioms fTf_chipSound
#assert_axioms forge_nonmember
#assert_axioms forge_satisfied_legacy
#assert_axioms forge_nonmember_rejected
#assert_axioms forge_was_accepted_now_rejected
#assert_axioms gTf_chipSound
#assert_axioms forge_blinded_leaf_rejected
#assert_axioms honest_satisfied2
#assert_axioms honest_height1_fires
#assert_axioms honest_satisfied2_show2
#assert_axioms honest_two_shows_unlinkable

end Dregg2.Circuit.Emit.BlindedMembershipRung2
