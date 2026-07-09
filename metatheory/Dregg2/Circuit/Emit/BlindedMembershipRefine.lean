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
import Dregg2.Circuit.DecideSatisfied2

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

/-! ============================================================================================
## §7 — the DEPTH-GENERAL, 4-ARY, GENERAL-POSITION bridge (Golden Lift, stage 3d-DIM).

The whole-descriptor SAT ⟹ SEM bridge for `blindedMembership4aryDesc depth` — the depth-8,
general-position descriptor that carries production presentations. Unlike the depth-2 single-row
descriptor above, this one is ONE 4-ary level per row tied by a continuity WINDOW gate, so the
membership half is a genuine MULTI-ROW fold. The bridge is UNIVERSAL over depth (any non-empty
trace); depth-8 is an instance. -/

section General

open Dregg2.Circuit.DescriptorIR2
  (WindowConstraint envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.BlindedMembershipEmit
  (blindedMembership4aryDesc gConstraints gPerRowGates gLastRowBoundaries gPerRowBodies
   gParentLookup gBlindLookup gContinuity gBlindedLeafPin gRootPin gContWindow gCont_zero_iff
   gArrangeList gChildren_arranged bitBinaryBody child0Body child1Body child2Body child3Body
   gCUR gSIB0 gSIB1 gSIB2 gB0 gB1 gC0 gC1 gC2 gC3 gPAR gBLINDING gBLINDED_LEAF
   gPATH_LANES gBLIND_LANES gPI_BLINDED_LEAF gPI_ROOT)

/-! ### The positional 4-ary fold spec (trace-independent). -/

/-- One 4-ary level step: hash the positional arrangement of the running hash + siblings. -/
def gStep (hash : List ℤ → ℤ) (cur : ℤ) (s : ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ :=
  match s with
  | (s0, s1, s2, b0, b1) => hash (gArrangeList cur s0 s1 s2 b0 b1)

/-- The positional 4-ary Merkle fold over a list of `(s0,s1,s2,b0,b1)` authentication steps. -/
def gFoldPos (hash : List ℤ → ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ × ℤ × ℤ × ℤ)) : ℤ :=
  steps.foldl (gStep hash) leaf

/-- The fold peels at the TOP (last) level. -/
theorem gFoldPos_concat (hash : List ℤ → ℤ) (leaf : ℤ)
    (steps : List (ℤ × ℤ × ℤ × ℤ × ℤ)) (s : ℤ × ℤ × ℤ × ℤ × ℤ) :
    gFoldPos hash leaf (steps ++ [s]) = gStep hash (gFoldPos hash leaf steps) s := by
  simp only [gFoldPos, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **`Blinded4aryMembers`** — THE FUNCTIONAL SPEC of the depth-general blinded ring-membership: the
published `blinded_leaf` is the arity-2 Poseidon2 blinding of the hidden `(leaf, blinding)`, AND that
`leaf` positionally folds up the `steps` to the public `root`. -/
def Blinded4aryMembers (hash : List ℤ → ℤ)
    (blinded_leaf leaf blinding root : ℤ) (steps : List (ℤ × ℤ × ℤ × ℤ × ℤ)) : Prop :=
  blinded_leaf = hash [leaf, blinding] ∧ gFoldPos hash leaf steps = root

/-- The authentication steps a length-`n` prefix of the trace exposes (one per row). -/
def gStepsOf (t : VmTrace) (n : Nat) : List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  (List.range n).map (fun j =>
    ((envAt t j).loc gSIB0, (envAt t j).loc gSIB1, (envAt t j).loc gSIB2,
     (envAt t j).loc gB0, (envAt t j).loc gB1))

/-! ### Membership tactic + universal row extractions. -/

local macro "g_mem" : tactic =>
  `(tactic| (show _ ∈ gConstraints;
             simp [gConstraints, gPerRowGates, gLastRowBoundaries, gPerRowBodies, gParentLookup,
               gBlindLookup, gContinuity, gBlindedLeafPin, gRootPin]))

variable {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {depth : Nat}

/-- Every per-row body (bit-binary ×2, child-selection ×4) vanishes on EVERY row: on non-last rows
via the transition `.gate`, on the last row via the re-lowered `.boundary .last`. -/
theorem gPerRowBodyZero
    (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (b : EmittedExpr) (hb : b ∈ gPerRowBodies) (j : Nat) (hj : j < t.rows.length) :
    b.eval (envAt t j).loc = 0 := by
  by_cases hlast : (j + 1 == t.rows.length) = true
  · have hmem : VmConstraint2.base (.boundary VmRow.last b)
        ∈ (blindedMembership4aryDesc depth).constraints := by
      show _ ∈ gConstraints
      simp only [gConstraints, gLastRowBoundaries, List.mem_append, List.mem_map]
      exact Or.inr ⟨b, hb, rfl⟩
    have h := hsat.rowConstraints j hj _ hmem
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
    exact h hlast
  · have hf : (j + 1 == t.rows.length) = false := by
      simp only [Bool.not_eq_true] at hlast; exact hlast
    have hmem : VmConstraint2.base (.gate b) ∈ (blindedMembership4aryDesc depth).constraints := by
      show _ ∈ gConstraints
      simp only [gConstraints, gPerRowGates, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨b, hb, rfl⟩)
    have h := hsat.rowConstraints j hj _ hmem
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hf] at h
    exact h

/-- On any row, the four child columns are the positional arrangement of the running hash + siblings
(the six per-row gates + the arrangement reduction). -/
theorem gArrangeAt (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) :
    [(envAt t j).loc gC0, (envAt t j).loc gC1, (envAt t j).loc gC2, (envAt t j).loc gC3]
      = gArrangeList ((envAt t j).loc gCUR) ((envAt t j).loc gSIB0) ((envAt t j).loc gSIB1)
          ((envAt t j).loc gSIB2) ((envAt t j).loc gB0) ((envAt t j).loc gB1) := by
  have hz := fun b hb => gPerRowBodyZero hsat b hb j hj
  exact gChildren_arranged _
    (hz _ (by simp [gPerRowBodies])) (hz _ (by simp [gPerRowBodies]))
    (hz _ (by simp [gPerRowBodies])) (hz _ (by simp [gPerRowBodies]))
    (hz _ (by simp [gPerRowBodies])) (hz _ (by simp [gPerRowBodies]))

/-- The arity-4 parent chip binds `gPAR` to `hash` of the four child columns, on any row. -/
theorem gParentAt (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (j : Nat) (hj : j < t.rows.length) :
    (envAt t j).loc gPAR
      = hash [(envAt t j).loc gC0, (envAt t j).loc gC1, (envAt t j).loc gC2,
              (envAt t j).loc gC3] := by
  have hmem : gParentLookup ∈ (blindedMembership4aryDesc depth).constraints := by g_mem
  have h := hsat.rowConstraints j hj _ hmem
  simp only [gParentLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t j).loc
    [.var gC0, .var gC1, .var gC2, .var gC3] gPAR gPATH_LANES
    (by show (4 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- The arity-2 blinding tooth binds `gBLINDED_LEAF` to `hash [cur, blinding]`, on any row. -/
theorem gBlindAt (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (j : Nat) (hj : j < t.rows.length) :
    (envAt t j).loc gBLINDED_LEAF
      = hash [(envAt t j).loc gCUR, (envAt t j).loc gBLINDING] := by
  have hmem : gBlindLookup ∈ (blindedMembership4aryDesc depth).constraints := by g_mem
  have h := hsat.rowConstraints j hj _ hmem
  simp only [gBlindLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t j).loc
    [.var gCUR, .var gBLINDING] gBLINDED_LEAF gBLIND_LANES
    (by show (2 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- The continuity window gate ties `next.cur = this.par` on every non-last row. -/
theorem gContAt (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hnl : (j + 1 == t.rows.length) = false) :
    (envAt t (j + 1)).loc gCUR = (envAt t j).loc gPAR := by
  have hmem : gContinuity ∈ (blindedMembership4aryDesc depth).constraints := by g_mem
  have h := hsat.rowConstraints j hj _ hmem
  simp only [gContinuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_true] at h
  have hz : gContWindow.eval (envAt t j) = 0 := h hnl
  have hkey := (gCont_zero_iff (envAt t j)).mp hz
  have heq : (envAt t (j + 1)).loc gCUR = (envAt t j).nxt gCUR := rfl
  rw [heq]; exact hkey

/-- The row-0 blinded-leaf pin: `loc gBLINDED_LEAF = pub gPI_BLINDED_LEAF`. -/
theorem gBlindedLeafPi (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    (envAt t 0).loc gBLINDED_LEAF = t.pub gPI_BLINDED_LEAF := by
  have hmem : gBlindedLeafPin ∈ (blindedMembership4aryDesc depth).constraints := by g_mem
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [gBlindedLeafPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-- The last-row root pin: `loc gPAR = pub gPI_ROOT`. -/
theorem gRootPi (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    (envAt t (t.rows.length - 1)).loc gPAR = t.pub gPI_ROOT := by
  have hmem : gRootPin ∈ (blindedMembership4aryDesc depth).constraints := by g_mem
  have hj : t.rows.length - 1 < t.rows.length := by omega
  have h := hsat.rowConstraints (t.rows.length - 1) hj _ hmem
  simp only [gRootPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  refine h ?_
  have : t.rows.length - 1 + 1 = t.rows.length := by omega
  simp [this]

/-! ### The multi-row fold assembly (the genuine cross-row induction). -/

/-- **`gFoldsTo`** — reading the per-row steps, the row-0 running hash positionally folds up to each
row's parent digest. The load-bearing cross-row induction: base = the level-0 parent; step chains via
the continuity gate (`cur_{j+1} = par_j`) and the arrangement + parent chip at level `j+1`. -/
theorem gFoldsTo (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    ∀ j, j < t.rows.length →
      gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t (j + 1)) = (envAt t j).loc gPAR := by
  intro j
  induction j with
  | zero =>
    intro hj0
    have key : gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t 1)
        = hash (gArrangeList ((envAt t 0).loc gCUR) ((envAt t 0).loc gSIB0)
            ((envAt t 0).loc gSIB1) ((envAt t 0).loc gSIB2) ((envAt t 0).loc gB0)
            ((envAt t 0).loc gB1)) := by
      simp only [gStepsOf, List.range_one, List.map_cons, List.map_nil, gFoldPos,
        List.foldl_cons, List.foldl_nil, gStep]
    rw [key, ← gArrangeAt hsat 0 hj0, ← gParentAt hsat hChip 0 hj0]
  | succ j ih =>
    intro hj
    have hjS : j < t.rows.length := by omega
    have hnl : (j + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hjplus : j + 1 < t.rows.length := hj
    have hcont : (envAt t (j + 1)).loc gCUR = (envAt t j).loc gPAR := gContAt hsat j hjS hnl
    -- gStepsOf t (j+2) = gStepsOf t (j+1) ++ [step_{j+1}]
    have hsteps : gStepsOf t (j + 2)
        = gStepsOf t (j + 1)
          ++ [((envAt t (j + 1)).loc gSIB0, (envAt t (j + 1)).loc gSIB1,
               (envAt t (j + 1)).loc gSIB2, (envAt t (j + 1)).loc gB0,
               (envAt t (j + 1)).loc gB1)] := by
      simp only [gStepsOf, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    show gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t (j + 1 + 1)) = (envAt t (j + 1)).loc gPAR
    have key : gFoldPos hash ((envAt t 0).loc gCUR) (gStepsOf t (j + 1 + 1))
        = hash (gArrangeList ((envAt t j).loc gPAR) ((envAt t (j + 1)).loc gSIB0)
            ((envAt t (j + 1)).loc gSIB1) ((envAt t (j + 1)).loc gSIB2)
            ((envAt t (j + 1)).loc gB0) ((envAt t (j + 1)).loc gB1)) := by
      rw [show j + 1 + 1 = j + 2 from rfl, hsteps, gFoldPos_concat, ih hjS]
      simp only [gStep]
    rw [key, ← hcont, ← gArrangeAt hsat (j + 1) hjplus, ← gParentAt hsat hChip (j + 1) hjplus]

/-- **`blinded4ary_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT ⟹ SEM), depth-general.**
A trace SATISFYING `blindedMembership4aryDesc depth`, against the NAMED Poseidon2 chip carrier, binds
the genuine blinded ring-membership relation: the published `blinded_leaf` PI is `hash [leaf,
blinding]` of the hidden row-0 `(cur, blinding)`, AND that `cur` positionally folds up the per-row
steps to the public `root` PI. Holds for ANY non-empty trace — the production depth-8 is the instance
`depth := 8`, `t.rows.length = 8`. The blind tooth and the level-0 arrangement share the `gCUR`
column, so the published `blinded_leaf` commits to exactly the member proven under `root`. -/
theorem blinded4ary_sat_refines
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash (blindedMembership4aryDesc depth) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    Blinded4aryMembers hash
      (t.pub gPI_BLINDED_LEAF) ((envAt t 0).loc gCUR) ((envAt t 0).loc gBLINDING)
      (t.pub gPI_ROOT) (gStepsOf t t.rows.length) := by
  refine ⟨?_, ?_⟩
  · -- the blind tooth: blinded_leaf PI = hash [cur_0, blinding_0].
    rw [← gBlindedLeafPi hsat hlen]
    exact gBlindAt hsat hChip 0 hlen
  · -- the membership fold: cur_0 folds to the last parent = root PI.
    have hj : t.rows.length - 1 < t.rows.length := by omega
    have hfold := gFoldsTo hsat hChip (t.rows.length - 1) hj
    rw [Nat.sub_add_cancel hlen] at hfold
    rw [hfold]
    exact gRootPi hsat hlen

/-! ### Non-vacuity: a CONCRETE depth-2 (2-row) general-position accepting trace fires the bridge. -/

/-- An order-sensitive digit hash (order- and arity-sensitive, so it separates levels/positions). -/
private def gHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **Row 0** — a MIXED-position level (position 1: `b0=1,b1=0`, so children `[s0, cur, s1, s2] =
[2,1,3,4]`, parent `gHash [2,1,3,4] = 2010304`). Member `leaf = 1`, siblings `2,3,4`; blinding `8`,
blinded leaf `gHash [1,8] = 108`. -/
private def gRow0 : Assignment := fun c =>
  if c = gCUR then 1 else if c = gSIB0 then 2 else if c = gSIB1 then 3 else if c = gSIB2 then 4
  else if c = gB0 then 1 else if c = gB1 then 0
  else if c = gC0 then 2 else if c = gC1 then 1 else if c = gC2 then 3 else if c = gC3 then 4
  else if c = gPAR then 2010304
  else if c = gBLINDING then 8 else if c = gBLINDED_LEAF then 108 else 0

/-- **Row 1 (the last row)** — position 0 (leftmost): running hash `cur = 2010304` (= row-0 parent, the
continuity chain), siblings `5,6,7`, children `[2010304,5,6,7]`, parent (root)
`gHash [2010304,5,6,7] = 2010304050607`. Blinding `8`, blinded leaf `gHash [2010304,8] = 201030408`. -/
private def gRow1 : Assignment := fun c =>
  if c = gCUR then 2010304 else if c = gSIB0 then 5 else if c = gSIB1 then 6 else if c = gSIB2 then 7
  else if c = gB0 then 0 else if c = gB1 then 0
  else if c = gC0 then 2010304 else if c = gC1 then 5 else if c = gC2 then 6 else if c = gC3 then 7
  else if c = gPAR then 2010304050607
  else if c = gBLINDING then 8 else if c = gBLINDED_LEAF then 201030408 else 0

private def gPub : Assignment := fun k =>
  if k = gPI_BLINDED_LEAF then 108 else if k = gPI_ROOT then 2010304050607 else 0

/-- The chip table: the two genuine `child → parent` arity-4 rows and the two arity-2 blinding rows. -/
private def gTbl : List (List ℤ) :=
  [chipRow gHash [2, 1, 3, 4] (List.replicate 7 0),
   chipRow gHash [2010304, 5, 6, 7] (List.replicate 7 0),
   chipRow gHash [1, 8] (List.replicate 7 0),
   chipRow gHash [2010304, 8] (List.replicate 7 0)]

private def gTrace : VmTrace :=
  { rows := [gRow0, gRow1], pub := gPub
    tf := fun tid => match tid with | .poseidon2 => gTbl | _ => [] }

/-- The concrete chip table is genuinely SOUND for `gHash`. -/
theorem gConcrete_chipSound : ChipTableSound gHash (gTrace.tf .poseidon2) := by
  intro r hr
  simp only [gTrace, gTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h
  · exact ⟨[2, 1, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[2010304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1, 8], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[2010304, 8], List.replicate 7 0, by decide, by decide, h⟩

/-- **The `Satisfied2` hypothesis is INHABITED at depth 2 (2 rows, GENERAL position).** Every
constraint holds on both rows: the two arity-4 parent lookups and two arity-2 blinding lookups land in
the table, the per-row bit-binary + child-selection gates close (row 0 uses position 1, row 1 position
0), the continuity window ties row 1's `cur` to row 0's parent, and the blinded-leaf/root PI pins
close. Refutes the vacuity scar for the general family. -/
theorem gConcrete_sat :
    Satisfied2 gHash (blindedMembership4aryDesc 2) (fun _ => 0) (fun _ => (0, 0)) [] gTrace := by
  have hmemlog : memLog (blindedMembership4aryDesc 2) gTrace = [] := rfl
  have hmaplog : mapLog (blindedMembership4aryDesc 2) gTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show gTrace.rows.length = 2 from rfl] at hi
    rw [show (blindedMembership4aryDesc 2).constraints = gConstraints from rfl] at hc
    interval_cases i <;>
      (fin_cases hc <;>
        simp only [VmConstraint2.holdsAt] <;>
        first
          | exact (Dregg2.Circuit.Argus.InterpCore.decideConstraint_iff _ _ _ _).mp (by decide)
          | exact (Dregg2.Circuit.DecideSatisfied2.decideLookup_iff _ _ _).mp (by decide)
          | exact (Dregg2.Circuit.DecideSatisfied2.decideWindow_iff _ _ _).mp (by decide))
  · intro i _; trivial
  · intro i _ r hr; simp [blindedMembership4aryDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The bridge FIRES end-to-end on the concrete inhabited depth-2 general-position witness** (SAT ⟹
SEM, non-vacuously): all hypotheses hold, and the whole blinded-membership relation is DERIVED. -/
theorem gWitness_spec :
    Blinded4aryMembers gHash (gTrace.pub gPI_BLINDED_LEAF) ((envAt gTrace 0).loc gCUR)
      ((envAt gTrace 0).loc gBLINDING) (gTrace.pub gPI_ROOT) (gStepsOf gTrace gTrace.rows.length) :=
  blinded4ary_sat_refines (by decide) gConcrete_sat gConcrete_chipSound

/-- The fired witness IS the closed-form true instance (blind tooth `108 = gHash [1,8]`, and `1`
folds through position 1 then position 0 to `2010304050607`). -/
theorem gWitness_spec_closed :
    Blinded4aryMembers gHash 108 1 8 2010304050607 [(2, 3, 4, 1, 0), (5, 6, 7, 0, 0)] := by
  unfold Blinded4aryMembers gFoldPos gStep gArrangeList gHash; decide

/-- **Witness FALSE — the spec CONSTRAINS.** The same member/blinding with the WRONG blinded leaf is
rejected. -/
theorem gWitness_spec_false_blind :
    ¬ Blinded4aryMembers gHash 999 1 8 2010304050607 [(2, 3, 4, 1, 0), (5, 6, 7, 0, 0)] := by
  unfold Blinded4aryMembers gFoldPos gStep gArrangeList gHash; decide

/-- **Witness FALSE — the membership half CONSTRAINS.** The right blinded leaf but the WRONG root is
rejected: the positional fold must reach the committed root. -/
theorem gWitness_spec_false_root :
    ¬ Blinded4aryMembers gHash 108 1 8 999 [(2, 3, 4, 1, 0), (5, 6, 7, 0, 0)] := by
  unfold Blinded4aryMembers gFoldPos gStep gArrangeList gHash; decide

#assert_axioms gFoldsTo
#assert_axioms blinded4ary_sat_refines
#assert_axioms gConcrete_sat
#assert_axioms gWitness_spec
#assert_axioms gBlindAt
#assert_axioms gArrangeAt

end General

end Dregg2.Circuit.Emit.BlindedMembershipRefine
