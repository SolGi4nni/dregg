/-
# Dregg2.Circuit.Emit.BlindedMembershipRefine — the WHOLE-DESCRIPTOR functional-correctness bridge
for the blinded ring-membership descriptor (`BlindedMembershipEmit.blindedMembershipDesc`).

## What Rung 0 gave us and what this file adds

`BlindedMembershipEmit` byte-pins `blindedMembershipDesc` and proves one per-gate lemma
(`continuity_body_zero_iff`). MISSING: the WHOLE-DESCRIPTOR bridge — that a trace SATISFYING the
descriptor (`Satisfied2`) corresponds to the GENUINE blinded ring-membership relation: the published
`blinded_leaf` PI is `hash_2_to_1` of a HIDDEN `(leaf_hash, blinding)` whose `leaf_hash` sits under the
public `root`. This file proves it (SAT ⟹ SEM, the load-bearing soundness direction).

## The functional spec (authored here — `spec_status = NO_LEAN`)

`BlindedMembers` is the trace-independent relation: `blinded_leaf = hash [leaf_hash, blinding]`
(the arity-2 blinding of `poseidon2_air.rs:720`) AND `leaf_hash` authenticates to `root` along the
depth-2 4-ary Merkle path (`MerkleMembershipRefine.MerkleMembers2`, reused). The membership half is
literally the proven Merkle-membership fold; `blindedMembership_exists_hidden` repackages the bridge
as the mission's `∃ hidden leaf_hash, blinding : blinded_leaf = hash₂(leaf,blinding) ∧ leaf ∈ tree(root)`
(via `MembersUnderRoot4`), so unlinkability is exactly the freedom in the existentially-hidden factor.

## The bridge (whole descriptor, not one gate)

`blindedMembership_sat_refines` (SAT_IMPLIES_SEM): a trace SATISFYING the whole descriptor — against
the NAMED Poseidon2 chip carrier — binds `BlindedMembers` between the row-0 hidden witness columns
(`leaf_hash`, `blinding`, the two sibling triples) and the two public PIs. It COMPOSES all seven
constraints: the arity-2 blinding lookup (`chip_lookup_sound`), its first-row PI pin, the two 4-ary
`child → parent` chip lookups, the chain-continuity gate (`CUR1 = PARENT0`, read on a non-last row 0),
and the root pin. Crucially the blinding lookup and the level-0 lookup share the `LEAF` column, so the
published `blinded_leaf` commits to exactly the proven member — not a single-gate restatement.

## Non-vacuity (the anti-scar proof)

`concrete_sat` builds a CONCRETE two-row trace + a concrete sound chip table for which `Satisfied2`
AND `ChipTableSound` hold — the hypothesis chain is genuinely INHABITED; `witness_spec` fires the
bridge end-to-end. `concrete_fail_chain` / `concrete_fail_root` / `concrete_fail_blind` exhibit
CONCRETE traces that FAIL `Satisfied2` because a constraint BITES. `witness_spec_closed` /
`witness_spec_false` show the SPEC itself separates (TRUE and FALSE) — never a `True`/`P → P` stub.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The sole cryptographic carrier is the
NAMED chip soundness `ChipTableSound hash (t.tf .poseidon2)`, never an axiom. NEW file; imports
read-only.
-/
import Dregg2.Circuit.Emit.BlindedMembershipEmit
import Dregg2.Circuit.Emit.MerkleMembershipRefine

namespace Dregg2.Circuit.Emit.BlindedMembershipRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.BlindedMembershipEmit
  (blindedMembershipDesc level0Lookup level1Lookup blindLookup continuityGate continuityLastFix
   rootPin blindedLeafPin contBody continuity_body_zero_iff
   LEAF SIB0A SIB0B SIB0C PARENT0 CUR1 SIB1A SIB1B SIB1C PARENT1 BLINDING BLINDED_LEAF
   LEVEL0_LANES LEVEL1_LANES BLIND_LANES ROOT_PI BLINDED_LEAF_PI)
open Dregg2.Circuit.Emit.MerkleMembershipRefine
  (merkleFold2 MerkleMembers2 MembersUnderRoot4 foldNode4 merkleMembers2_as_fold)

set_option autoImplicit false

/-! ## §1 — the functional spec (trace-independent; blinding tooth + membership fold). -/

/-- **`BlindedMembers`** — THE FUNCTIONAL SPEC of the blinded ring-membership descriptor: the
published `blinded_leaf` is the arity-2 Poseidon2 blinding of the hidden `(leaf_hash, blinding)`
(`hash_2_to_1`), AND that `leaf_hash` authenticates to the public `root` along the depth-2 4-ary
Merkle path. -/
def BlindedMembers (hash : List ℤ → ℤ)
    (blinded_leaf leaf_hash blinding s0a s0b s0c s1a s1b s1c root : ℤ) : Prop :=
  blinded_leaf = hash [leaf_hash, blinding]
    ∧ MerkleMembers2 hash leaf_hash s0a s0b s0c s1a s1b s1c root

/-! ## §2 — extracting the row facts from `Satisfied2` (the descriptor's own constraints). -/

/-- The membership tactic: every constraint we name is literally in `blindedMembershipDesc`. -/
local macro "bm_mem" : tactic =>
  `(tactic| (show _ ∈ blindedMembershipDesc.constraints;
             simp [blindedMembershipDesc, level0Lookup, level1Lookup, blindLookup, continuityGate,
               continuityLastFix, rootPin, blindedLeafPin]))

/-- A declared arity-4 chip lookup, against the NAMED sound chip table, forces the digest column to be
the genuine Poseidon2 hash of the four evaluated inputs — on ANY row (lookups are never gated). -/
theorem lookupChip4 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (j : Nat) (hj : j < t.rows.length)
    (i0 i1 i2 i3 digestCol : Nat) (lanes : List Nat)
    (hmem : VmConstraint2.lookup ⟨TableId.poseidon2,
              chipLookupTuple [.var i0, .var i1, .var i2, .var i3] digestCol lanes⟩
              ∈ blindedMembershipDesc.constraints) :
    (envAt t j).loc digestCol
      = hash [(envAt t j).loc i0, (envAt t j).loc i1, (envAt t j).loc i2, (envAt t j).loc i3] := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t j).loc
    [.var i0, .var i1, .var i2, .var i3] digestCol lanes (by show (4 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- A declared arity-2 chip lookup forces the digest column to be the genuine Poseidon2 `hash_2_to_1`
of the two evaluated inputs — the blinding tooth (`blinded_leaf = hash [leaf_hash, blinding]`). -/
theorem lookupChip2 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (j : Nat) (hj : j < t.rows.length)
    (i0 i1 digestCol : Nat) (lanes : List Nat)
    (hmem : VmConstraint2.lookup ⟨TableId.poseidon2,
              chipLookupTuple [.var i0, .var i1] digestCol lanes⟩
              ∈ blindedMembershipDesc.constraints) :
    (envAt t j).loc digestCol = hash [(envAt t j).loc i0, (envAt t j).loc i1] := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t j).loc
    [.var i0, .var i1] digestCol lanes (by show (2 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- A declared `.gate` body vanishes on any ACTIVE (non-last) row — the `when_transition` arm. -/
theorem activeGateZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hlast : (j + 1 == t.rows.length) = false)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.gate body) ∈ blindedMembershipDesc.constraints) :
    body.eval (envAt t j).loc = 0 := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h

/-- A declared first-row PI binding pins `loc[col] = pub[k]` on row 0. -/
theorem firstPi {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k) ∈ blindedMembershipDesc.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-! ## §3 — the whole-descriptor refinement (SAT_IMPLIES_SEM). -/

/-- **`blindedMembership_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM).**
A `Satisfied2` of `blindedMembershipDesc`, against the NAMED Poseidon2 chip carrier, binds the genuine
blinded ring-membership relation between the row-0 hidden witness columns and the two public PIs.
Composes all seven constraints: the arity-2 blinding lookup + its PI pin (giving `blinded_leaf =
hash [leaf_hash, blinding]`), and the Merkle half (two 4-ary lookups + continuity + root pin). The
shared `LEAF` column ties the blinding to the proven member. `1 < t.rows.length` is the deployed
padded-height condition making row 0 a genuine transition row for the `when_transition` continuity
gate. -/
theorem blindedMembership_sat_refines {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    BlindedMembers hash
      (t.pub BLINDED_LEAF_PI)
      ((envAt t 0).loc LEAF) ((envAt t 0).loc BLINDING)
      ((envAt t 0).loc SIB0A) ((envAt t 0).loc SIB0B) ((envAt t 0).loc SIB0C)
      ((envAt t 0).loc SIB1A) ((envAt t 0).loc SIB1B) ((envAt t 0).loc SIB1C)
      (t.pub ROOT_PI) := by
  have hlen0 : 0 < t.rows.length := by omega
  have hlast : (0 + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  refine ⟨?_, ?_⟩
  · -- the blinding tooth: blinded_leaf PI = hash [leaf_hash, blinding].
    have hbleaf : (envAt t 0).loc BLINDED_LEAF = t.pub BLINDED_LEAF_PI :=
      firstPi hsat hlen0 BLINDED_LEAF BLINDED_LEAF_PI (by bm_mem)
    have hblind : (envAt t 0).loc BLINDED_LEAF
        = hash [(envAt t 0).loc LEAF, (envAt t 0).loc BLINDING] :=
      lookupChip2 hsat hChip 0 hlen0 LEAF BLINDING BLINDED_LEAF BLIND_LANES (by bm_mem)
    rw [← hbleaf]; exact hblind
  · -- the membership half: root = hash [hash [leaf, s0*], s1*].
    have hp0 : (envAt t 0).loc PARENT0
        = hash [(envAt t 0).loc LEAF, (envAt t 0).loc SIB0A, (envAt t 0).loc SIB0B,
                (envAt t 0).loc SIB0C] :=
      lookupChip4 hsat hChip 0 hlen0 LEAF SIB0A SIB0B SIB0C PARENT0 LEVEL0_LANES (by bm_mem)
    have hp1 : (envAt t 0).loc PARENT1
        = hash [(envAt t 0).loc CUR1, (envAt t 0).loc SIB1A, (envAt t 0).loc SIB1B,
                (envAt t 0).loc SIB1C] :=
      lookupChip4 hsat hChip 0 hlen0 CUR1 SIB1A SIB1B SIB1C PARENT1 LEVEL1_LANES (by bm_mem)
    have hcont : (envAt t 0).loc CUR1 = (envAt t 0).loc PARENT0 :=
      (continuity_body_zero_iff (envAt t 0).loc).mp
        (activeGateZero hsat 0 hlen0 hlast contBody (by bm_mem))
    have hroot : (envAt t 0).loc PARENT1 = t.pub ROOT_PI :=
      firstPi hsat hlen0 PARENT1 ROOT_PI (by bm_mem)
    unfold MerkleMembers2 merkleFold2
    rw [← hroot, hp1, hcont, hp0]

/-- **`blindedMembership_exists_hidden` — the mission's `∃ hidden` packaging.** From the bridge: there
EXIST a hidden `leaf_hash`, `blinding` and an authentication path (the hidden siblings) such that the
published `blinded_leaf` is `hash [leaf_hash, blinding]` and `leaf_hash` folds up the path to the
public `root`. The freedom in the existentially-hidden `blinding` is precisely the unlinkability. -/
theorem blindedMembership_exists_hidden {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash blindedMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    ∃ (leaf_hash blinding : ℤ) (steps : List (ℤ × ℤ × ℤ)),
      t.pub BLINDED_LEAF_PI = hash [leaf_hash, blinding]
        ∧ MembersUnderRoot4 hash leaf_hash (t.pub ROOT_PI) steps := by
  obtain ⟨hblind, hmem⟩ := blindedMembership_sat_refines hlen hsat hChip
  refine ⟨(envAt t 0).loc LEAF, (envAt t 0).loc BLINDING,
    [((envAt t 0).loc SIB0A, (envAt t 0).loc SIB0B, (envAt t 0).loc SIB0C),
     ((envAt t 0).loc SIB1A, (envAt t 0).loc SIB1B, (envAt t 0).loc SIB1C)], hblind, ?_⟩
  exact (merkleMembers2_as_fold hash _ _ _ _ _ _ _ _).mp hmem

/-! ## §4 — non-vacuity of the SPEC (the target is TRUE and FALSE, never a stub). -/

/-- A concrete little-endian digit hash — order-sensitive, injective enough to distinguish levels
and arities. -/
private def cHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **Witness TRUE — the spec is INHABITED.** Leaf `1` (siblings `2,3,4`) folds to parent `1020304`,
which with siblings `5,6,7` folds to root `1020304050607`; blinded with factor `8` gives
`cHash [1,8] = 108`. A concrete, nontrivial identity — not a stub. -/
theorem witness_spec_closed : BlindedMembers cHash 108 1 8 2 3 4 5 6 7 1020304050607 := by
  unfold BlindedMembers MerkleMembers2 merkleFold2 cHash; decide

/-- **Witness FALSE — the spec CONSTRAINS.** The very same member/blinding with the WRONG published
`blinded_leaf` is NOT accepted: the blinding tooth must equal `hash [leaf, blinding]`. -/
theorem witness_spec_false_blind : ¬ BlindedMembers cHash 999 1 8 2 3 4 5 6 7 1020304050607 := by
  unfold BlindedMembers MerkleMembers2 merkleFold2 cHash; decide

/-- **Witness FALSE — the membership half CONSTRAINS.** The right blinded leaf but the WRONG root is
rejected: `leaf_hash` must fold to the committed root. -/
theorem witness_spec_false_root : ¬ BlindedMembers cHash 108 1 8 2 3 4 5 6 7 999 := by
  unfold BlindedMembers MerkleMembers2 merkleFold2 cHash; decide

/-! ## §5 — THE ANTI-SCAR: a CONCRETE trace that genuinely SATISFIES the descriptor, plus three that
FAIL it (each constraint BITES). -/

/-- The single logical row: member leaf `1`, level-0 siblings `2,3,4`, parent `1020304`; chained
`CUR1 = 1020304`, level-1 siblings `5,6,7`, root `1020304050607`; blinding `8`, blinded leaf
`cHash [1,8] = 108`. -/
private def cRow : Assignment := fun c =>
  if c = LEAF then 1 else if c = SIB0A then 2 else if c = SIB0B then 3 else if c = SIB0C then 4
  else if c = PARENT0 then 1020304
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607
  else if c = BLINDING then 8 else if c = BLINDED_LEAF then 108 else 0

private def cPub : Assignment := fun k =>
  if k = BLINDED_LEAF_PI then 108 else if k = ROOT_PI then 1020304050607 else 0

/-- The chip table: the two genuine 4-ary `child → parent` rows and the arity-2 blinding row. -/
private def cTbl : List (List ℤ) :=
  [chipRow cHash [1, 2, 3, 4] (List.replicate 7 0),
   chipRow cHash [1020304, 5, 6, 7] (List.replicate 7 0),
   chipRow cHash [1, 8] (List.replicate 7 0)]

/-- The concrete two-row satisfying trace (padded height ≥ 2 makes row 0 a genuine transition row). -/
private def cTrace : VmTrace :=
  { rows := [cRow, cRow], pub := cPub
    tf := fun tid => match tid with | .poseidon2 => cTbl | _ => [] }

/-- **The concrete chip table is genuinely SOUND** for `cHash` — each row is a real `chipRow`, so the
NAMED carrier `ChipTableSound` is realizable, not just assumed. -/
theorem concrete_chipSound : ChipTableSound cHash (cTrace.tf .poseidon2) := by
  intro r hr
  simp only [cTrace, cTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h
  · exact ⟨[1, 2, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1, 8], List.replicate 7 0, by decide, by decide, h⟩

/-- **The `Satisfied2` HYPOTHESIS IS INHABITED.** The concrete trace genuinely satisfies the whole
deployed denotation — every constraint holds on both rows (the three chip lookups land in the table,
the continuity gate closes `1020304 = 1020304`, the root pin and blinded-leaf pin close), and the
empty memory / table legs close. Refutes the vacuity scar. -/
theorem concrete_sat :
    Satisfied2 cHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTrace := by
  have hmemlog : memLog blindedMembershipDesc cTrace = [] := rfl
  have hmaplog : mapLog blindedMembershipDesc cTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show cTrace.rows.length = 2 from rfl] at hi
    rw [show blindedMembershipDesc.constraints
          = [level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin, blindedLeafPin,
             continuityLastFix] from rfl] at hc
    interval_cases i <;>
      (fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          level0Lookup, level1Lookup, blindLookup, continuityGate, continuityLastFix, rootPin,
          blindedLeafPin] <;>
        trivial)
  · intro i _; trivial
  · intro i _ r hr; simp [blindedMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The bridge fires end-to-end on the concrete inhabited witness** (SAT ⟹ SEM, non-vacuously). -/
theorem witness_spec : BlindedMembers cHash
    (cTrace.pub BLINDED_LEAF_PI)
    ((envAt cTrace 0).loc LEAF) ((envAt cTrace 0).loc BLINDING)
    ((envAt cTrace 0).loc SIB0A) ((envAt cTrace 0).loc SIB0B) ((envAt cTrace 0).loc SIB0C)
    ((envAt cTrace 0).loc SIB1A) ((envAt cTrace 0).loc SIB1B) ((envAt cTrace 0).loc SIB1C)
    (cTrace.pub ROOT_PI) :=
  blindedMembership_sat_refines (by decide) concrete_sat concrete_chipSound

/-- The fired witness IS the closed-form true instance. -/
theorem witness_spec_is_closed :
    (BlindedMembers cHash
      (cTrace.pub BLINDED_LEAF_PI)
      ((envAt cTrace 0).loc LEAF) ((envAt cTrace 0).loc BLINDING)
      ((envAt cTrace 0).loc SIB0A) ((envAt cTrace 0).loc SIB0B) ((envAt cTrace 0).loc SIB0C)
      ((envAt cTrace 0).loc SIB1A) ((envAt cTrace 0).loc SIB1B) ((envAt cTrace 0).loc SIB1C)
      (cTrace.pub ROOT_PI))
    ↔ BlindedMembers cHash 108 1 8 2 3 4 5 6 7 1020304050607 := Iff.rfl

/-- A trace with a BROKEN path: `CUR1 = 0 ≠ 1020304 = PARENT0`. -/
private def cRowBadChain : Assignment := fun c => if c = CUR1 then 0 else cRow c
private def cTraceBadChain : VmTrace := { cTrace with rows := [cRowBadChain, cRowBadChain] }

/-- **REJECTS a broken path (continuity tooth BITES).** -/
theorem concrete_fail_chain :
    ¬ Satisfied2 cHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBadChain := by
  intro h
  have hmem : VmConstraint2.base (.gate contBody) ∈ blindedMembershipDesc.constraints := by bm_mem
  have hlast : (0 + 1 == cTraceBadChain.rows.length) = false := by decide
  have h0 := activeGateZero h 0 (by decide) hlast contBody hmem
  revert h0; decide

/-- A trace with a WRONG top digest: `PARENT1 = 0 ≠ 1020304050607 = root PI`. -/
private def cRowBadRoot : Assignment := fun c => if c = PARENT1 then 0 else cRow c
private def cTraceBadRoot : VmTrace := { cTrace with rows := [cRowBadRoot, cRowBadRoot] }

/-- **REJECTS a wrong root (root-pin tooth BITES).** -/
theorem concrete_fail_root :
    ¬ Satisfied2 cHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBadRoot := by
  intro h
  have hmem : VmConstraint2.base (.piBinding VmRow.first PARENT1 ROOT_PI)
      ∈ blindedMembershipDesc.constraints := by bm_mem
  have h0 := firstPi h (by decide) PARENT1 ROOT_PI hmem
  revert h0; decide

/-- A trace with a WRONG published blinded leaf: `BLINDED_LEAF = 0 ≠ 108 = blinded-leaf PI`. -/
private def cRowBadBlind : Assignment := fun c => if c = BLINDED_LEAF then 0 else cRow c
private def cTraceBadBlind : VmTrace := { cTrace with rows := [cRowBadBlind, cRowBadBlind] }

/-- **REJECTS a wrong published blinded leaf (blinded-leaf-pin tooth BITES).** -/
theorem concrete_fail_blind :
    ¬ Satisfied2 cHash blindedMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBadBlind := by
  intro h
  have hmem : VmConstraint2.base (.piBinding VmRow.first BLINDED_LEAF BLINDED_LEAF_PI)
      ∈ blindedMembershipDesc.constraints := by bm_mem
  have h0 := firstPi h (by decide) BLINDED_LEAF BLINDED_LEAF_PI hmem
  revert h0; decide

/-! ## §6 — shape pins + axiom hygiene. -/

#guard decide (cTrace.rows.length = 2)
-- the fold + blind genuinely recompose (order-sensitive digit hash):
#guard foldNode4 cHash 1 [(2, 3, 4), (5, 6, 7)] == 1020304050607
#guard cHash [1, 8] == 108

#assert_axioms lookupChip4
#assert_axioms lookupChip2
#assert_axioms blindedMembership_sat_refines
#assert_axioms blindedMembership_exists_hidden
#assert_axioms concrete_chipSound
#assert_axioms concrete_sat
#assert_axioms witness_spec
#assert_axioms concrete_fail_chain
#assert_axioms concrete_fail_root
#assert_axioms concrete_fail_blind

end Dregg2.Circuit.Emit.BlindedMembershipRefine
