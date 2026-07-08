/-
# Dregg2.Circuit.Emit.MerkleMembershipRefine — the WHOLE-DESCRIPTOR functional-correctness bridge
for the depth-2, 4-ary Poseidon2 Merkle-membership family
(`MerkleMembershipEmit.merkleMembershipDesc`).

## What Rung 0 gave us (`MerkleMembershipEmit.lean`) and what this file adds

`MerkleMembershipEmit` byte-pins `merkleMembershipDesc` and proves ONE per-GATE lemma
(`continuity_body_zero_iff` : the chain-continuity gate body is zero iff `CUR1 = PARENT0`). What was
MISSING: the WHOLE-DESCRIPTOR bridge — that a trace SATISFYING the descriptor (`Satisfied2`)
corresponds to the GENUINE Merkle-membership relation the circuit is meant to compute. This file
proves it (SAT ⟹ SEM, the load-bearing soundness direction).

## The functional spec (authored here — `spec_status = NO_LEAN`)

`merkleFold2` / `MerkleMembers2` are the trace-independent functional relation: a leaf sits under a
public root in a depth-2, 4-ary Poseidon2 Merkle tree when the root is the hash of the leaf's
level-0 parent (`hash [leaf, s0a, s0b, s0c]`, the leaf at lane 0) with the level-1 siblings
(`hash [parent0, s1a, s1b, s1c]`). `MembersUnderRoot4` gives the same as a general Merkle fold over
the two authentication steps, and `merkleMembers2_as_fold` proves the two coincide — so the spec is
undeniably the Merkle-membership fold, not an ad-hoc equation. This mirrors the deployed
`MerklePoseidon2StarkAir` (`circuit/src/poseidon2_air.rs`) `child → parent` `hash_4_to_1` step.

## The bridge (whole descriptor, not one gate)

`merkleMembership_sat_refines` (SAT_IMPLIES_SEM): a trace that SATISFIES the whole
`merkleMembershipDesc` — against the NAMED Poseidon2 chip carrier `ChipTableSound hash
(t.tf .poseidon2)` — binds the genuine Merkle-membership relation between the row-0 witness columns
(leaf + the two sibling triples) and the public root PI. It COMPOSES all four constraints: the two
`child → parent` chip lookups (through `chip_lookup_sound`), the chain-continuity gate
(`CUR1 = PARENT0`, tying the levels — a `when_transition` gate, so read on a non-last row 0), and
the root-pin (`PARENT1 = root PI`, first row). Not a single-gate restatement.

## Non-vacuity (the anti-scar proof)

`concrete_sat` builds a CONCRETE two-row trace + a concrete sound chip table (`concrete_chipSound`)
for which `Satisfied2` holds AND `ChipTableSound cHash` holds — the hypothesis chain is genuinely
INHABITED (not an empty/unsatisfiable antecedent); `witness_spec` fires the bridge end-to-end on it,
deriving `1020304050607 = cHash [cHash [1,2,3,4], 5,6,7]` (a true, nontrivial identity —
`witness_spec_closed`). `concrete_fail_chain` and `concrete_fail_root` exhibit CONCRETE traces that
FAIL `Satisfied2` because a constraint BITES: a broken path (`CUR1 ≠ PARENT0`) trips the continuity
gate, and a wrong top digest trips the root-pin. `witness_spec_false` shows the SPEC itself
separates (a wrong root is rejected) — so the target is TRUE and FALSE, never a `True`/`P → P` stub.

## Honest residual (direction)

Only SAT_IMPLIES_SEM (soundness — accept ⟹ genuine membership) is proven; this is the load-bearing
direction. Completeness (SEM ⟹ a satisfying trace) is not attempted in one additive file, but the
concrete satisfying witness is a completeness EXEMPLAR for a true instance.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The sole cryptographic carrier is the
NAMED chip soundness `ChipTableSound hash (t.tf .poseidon2)` (the deployed chip AIR's own
faithfulness — the same carrier `AdjacencyMembershipRefine`/`HeapOpenEmit` ride), never an axiom.
NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.MerkleMembershipEmit

namespace Dregg2.Circuit.Emit.MerkleMembershipRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.MerkleMembershipEmit
  (merkleMembershipDesc level0Lookup level1Lookup continuityGate continuityLastFix rootPin contBody
   continuity_body_zero_iff
   LEAF SIB0A SIB0B SIB0C PARENT0 CUR1 SIB1A SIB1B SIB1C PARENT1
   LEVEL0_LANES LEVEL1_LANES ROOT_PI)

set_option autoImplicit false

/-! ## §1 — the functional spec (trace-independent; the twin of the hand AIR's `child → parent`
step). `spec_status = NO_LEAN` — no proven model existed, so the missing functional spec is
authored here. -/

/-- **`merkleFold2`** — the depth-2, 4-ary Poseidon2 Merkle authentication fold: the `leaf` sits at
lane 0 of its level-0 node (siblings `s0a s0b s0c`), whose digest sits at lane 0 of the level-1 node
(siblings `s1a s1b s1c`). The reconstructed root. -/
def merkleFold2 (hash : List ℤ → ℤ) (leaf s0a s0b s0c s1a s1b s1c : ℤ) : ℤ :=
  hash [hash [leaf, s0a, s0b, s0c], s1a, s1b, s1c]

/-- **`MerkleMembers2 hash leaf s0a s0b s0c s1a s1b s1c root`** — THE FUNCTIONAL SPEC: `leaf`
authenticates to the committed `root` along the depth-2, 4-ary path given by the sibling triples.
The membership relation the circuit is meant to certify. -/
def MerkleMembers2 (hash : List ℤ → ℤ) (leaf s0a s0b s0c s1a s1b s1c root : ℤ) : Prop :=
  root = merkleFold2 hash leaf s0a s0b s0c s1a s1b s1c

/-- A general 4-ary (leaf-at-lane-0) Merkle fold over a list of `(sib, sib, sib)` authentication
steps — the trace-independent "leaf folds up its path" relation. -/
def foldNode4 (hash : List ℤ → ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ × ℤ)) : ℤ :=
  steps.foldl (fun acc s => match s with | (a, b, c) => hash [acc, a, b, c]) leaf

/-- **`MembersUnderRoot4`** — `leaf` authenticates to `root` along the 4-ary path `steps`. -/
def MembersUnderRoot4 (hash : List ℤ → ℤ) (leaf root : ℤ) (steps : List (ℤ × ℤ × ℤ)) : Prop :=
  foldNode4 hash leaf steps = root

/-- **The spec IS the general Merkle-membership fold** over its two authentication steps: the
depth-2 relation coincides with `leaf` folding up the path `[(s0a,s0b,s0c), (s1a,s1b,s1c)]` to the
root. So `MerkleMembers2` is genuinely membership, not an ad-hoc equation. -/
theorem merkleMembers2_as_fold (hash : List ℤ → ℤ) (leaf s0a s0b s0c s1a s1b s1c root : ℤ) :
    MerkleMembers2 hash leaf s0a s0b s0c s1a s1b s1c root
      ↔ MembersUnderRoot4 hash leaf root [(s0a, s0b, s0c), (s1a, s1b, s1c)] := by
  unfold MerkleMembers2 merkleFold2 MembersUnderRoot4 foldNode4
  simp only [List.foldl_cons, List.foldl_nil]
  exact eq_comm

/-! ## §2 — extracting the row facts from `Satisfied2` (the descriptor's own constraints). -/

/-- The membership tactic: every constraint we name is literally in `merkleMembershipDesc`. -/
local macro "mm_mem" : tactic =>
  `(tactic| (show _ ∈ merkleMembershipDesc.constraints;
             simp [merkleMembershipDesc, level0Lookup, level1Lookup, continuityGate,
               continuityLastFix, rootPin]))

/-- A declared arity-4 chip lookup, against the NAMED sound chip table, forces the digest column to
be the genuine Poseidon2 hash of the four evaluated input columns — on ANY row (the lookup is not
gated). This is where the Poseidon2 CR carrier enters, through `chip_lookup_sound`. -/
theorem lookupChip4 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (j : Nat) (hj : j < t.rows.length)
    (i0 i1 i2 i3 digestCol : Nat) (lanes : List Nat)
    (hmem : VmConstraint2.lookup ⟨TableId.poseidon2,
              chipLookupTuple [.var i0, .var i1, .var i2, .var i3] digestCol lanes⟩
              ∈ merkleMembershipDesc.constraints) :
    (envAt t j).loc digestCol
      = hash [(envAt t j).loc i0, (envAt t j).loc i1, (envAt t j).loc i2, (envAt t j).loc i3] := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t j).loc
    [.var i0, .var i1, .var i2, .var i3] digestCol lanes (by show (4 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- A declared `.gate` body vanishes on any ACTIVE (non-last) row — the `when_transition` arm. -/
theorem activeGateZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hlast : (j + 1 == t.rows.length) = false)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.gate body) ∈ merkleMembershipDesc.constraints) :
    body.eval (envAt t j).loc = 0 := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h

/-- A declared first-row PI binding pins `loc[col] = pub[k]` on row 0. -/
theorem firstPi {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k) ∈ merkleMembershipDesc.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-! ## §3 — the whole-descriptor refinement (SAT_IMPLIES_SEM). -/

/-- **`merkleMembership_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM).**
A `Satisfied2` of `merkleMembershipDesc`, against the NAMED Poseidon2 chip carrier, binds the
genuine depth-2, 4-ary Merkle-membership relation between the row-0 witness columns (the leaf and
the two sibling triples) and the committed public root PI. Composes all four constraints: the two
`child → parent` chip lookups, the chain-continuity gate (tying the levels — read on the non-last
row 0), and the root pin. `1 < t.rows.length` is the deployed padded-height condition that makes
row 0 a genuine transition row so the `when_transition` continuity gate fires. -/
theorem merkleMembership_sat_refines {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash merkleMembershipDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    MerkleMembers2 hash
      ((envAt t 0).loc LEAF) ((envAt t 0).loc SIB0A) ((envAt t 0).loc SIB0B) ((envAt t 0).loc SIB0C)
      ((envAt t 0).loc SIB1A) ((envAt t 0).loc SIB1B) ((envAt t 0).loc SIB1C)
      (t.pub ROOT_PI) := by
  have hlen0 : 0 < t.rows.length := by omega
  have hlast : (0 + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  -- level-0 `child → parent`: PARENT0 = hash [leaf, s0a, s0b, s0c].
  have hp0 : (envAt t 0).loc PARENT0
      = hash [(envAt t 0).loc LEAF, (envAt t 0).loc SIB0A, (envAt t 0).loc SIB0B,
              (envAt t 0).loc SIB0C] :=
    lookupChip4 hsat hChip 0 hlen0 LEAF SIB0A SIB0B SIB0C PARENT0 LEVEL0_LANES (by mm_mem)
  -- level-1 `child → parent`: PARENT1 = hash [cur1, s1a, s1b, s1c].
  have hp1 : (envAt t 0).loc PARENT1
      = hash [(envAt t 0).loc CUR1, (envAt t 0).loc SIB1A, (envAt t 0).loc SIB1B,
              (envAt t 0).loc SIB1C] :=
    lookupChip4 hsat hChip 0 hlen0 CUR1 SIB1A SIB1B SIB1C PARENT1 LEVEL1_LANES (by mm_mem)
  -- chain continuity: CUR1 = PARENT0 (the levels chain).
  have hcont : (envAt t 0).loc CUR1 = (envAt t 0).loc PARENT0 :=
    (continuity_body_zero_iff (envAt t 0).loc).mp
      (activeGateZero hsat 0 hlen0 hlast contBody (by mm_mem))
  -- root pin: PARENT1 = the public root PI (first row).
  have hroot : (envAt t 0).loc PARENT1 = t.pub ROOT_PI :=
    firstPi hsat hlen0 PARENT1 ROOT_PI (by mm_mem)
  -- assemble the whole fold: root = hash [hash [leaf, s0*], s1*].
  unfold MerkleMembers2 merkleFold2
  rw [← hroot, hp1, hcont, hp0]

/-! ## §4 — non-vacuity of the SPEC (the target is TRUE and FALSE, never a stub). -/

/-- A concrete little-endian digit hash — `[a,b,c,d] ↦ 100·(100·(100·a+b)+c)+d`, injective enough to
distinguish levels. -/
private def cHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **Witness TRUE — the spec is INHABITED (closed form).** Leaf `1` with level-0 siblings `2,3,4`
folds to parent `cHash [1,2,3,4] = 1020304`, which with level-1 siblings `5,6,7` folds to root
`cHash [1020304,5,6,7] = 1020304050607`. A concrete, nontrivial arithmetic identity — not a stub. -/
theorem witness_spec_closed : MerkleMembers2 cHash 1 2 3 4 5 6 7 1020304050607 := by
  unfold MerkleMembers2 merkleFold2 cHash; decide

/-- **Witness FALSE — the spec CONSTRAINS.** The very same leaf/siblings with the WRONG root are NOT
accepted: the top digest must equal the published root. A `True`/`P → P` bridge could not separate
this. -/
theorem witness_spec_false : ¬ MerkleMembers2 cHash 1 2 3 4 5 6 7 999 := by
  unfold MerkleMembers2 merkleFold2 cHash; decide

/-! ## §5 — THE ANTI-SCAR: a CONCRETE trace that genuinely SATISFIES the descriptor (the
`Satisfied2` hypothesis is INHABITED), plus two that FAIL it (constraints BITE). -/

/-- The single logical row: leaf `1`, level-0 siblings `2,3,4`, level-0 parent `1020304`; the
chained level-1 input `CUR1 = 1020304`, level-1 siblings `5,6,7`, top parent (root)
`1020304050607`. All lane / unused columns are `0`. -/
private def cRow : Assignment := fun c =>
  if c = LEAF then 1 else if c = SIB0A then 2 else if c = SIB0B then 3 else if c = SIB0C then 4
  else if c = PARENT0 then 1020304
  else if c = CUR1 then 1020304 else if c = SIB1A then 5 else if c = SIB1B then 6
  else if c = SIB1C then 7 else if c = PARENT1 then 1020304050607 else 0

private def cPub : Assignment := fun k => if k = ROOT_PI then 1020304050607 else 0

/-- The chip table: the two genuine `child → parent` `chipRow`s the two lookups absorb. -/
private def cTbl : List (List ℤ) :=
  [chipRow cHash [1, 2, 3, 4] (List.replicate 7 0),
   chipRow cHash [1020304, 5, 6, 7] (List.replicate 7 0)]

/-- The concrete two-row satisfying trace (both rows carry `cRow`; the padded height ≥ 2 makes
row 0 a genuine transition row, so the continuity gate fires). -/
private def cTrace : VmTrace :=
  { rows := [cRow, cRow], pub := cPub
    tf := fun tid => match tid with | .poseidon2 => cTbl | _ => [] }

/-- **The concrete chip table is genuinely SOUND** for `cHash` (each row is a real `chipRow`) — so
the NAMED carrier `ChipTableSound` is realizable, not just assumed. -/
theorem concrete_chipSound : ChipTableSound cHash (cTrace.tf .poseidon2) := by
  intro r hr
  simp only [cTrace, cTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[1, 2, 3, 4], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[1020304, 5, 6, 7], List.replicate 7 0, by decide, by decide, h⟩

/-- **The `Satisfied2` HYPOTHESIS IS INHABITED.** The concrete trace genuinely satisfies the whole
deployed denotation — every constraint holds on both rows (the two chip lookups land in the table,
the continuity gate closes `1020304 = 1020304`, the root pin closes `1020304050607`), and the empty
memory / table legs close. Refutes the vacuity scar: `merkleMembership_sat_refines` is NOT a theorem
over an empty antecedent. -/
theorem concrete_sat :
    Satisfied2 cHash merkleMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTrace := by
  have hmemlog : memLog merkleMembershipDesc cTrace = [] := rfl
  have hmaplog : mapLog merkleMembershipDesc cTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show cTrace.rows.length = 2 from rfl] at hi
    rw [show merkleMembershipDesc.constraints
          = [level0Lookup, level1Lookup, continuityGate, rootPin, continuityLastFix] from rfl] at hc
    interval_cases i <;>
      (fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          level0Lookup, level1Lookup, continuityGate, continuityLastFix, rootPin] <;>
        trivial)
  · intro i _; trivial
  · intro i _ r hr; simp [merkleMembershipDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The bridge fires end-to-end on the concrete inhabited witness** (SAT ⟹ SEM, non-vacuously):
all three hypotheses (`Satisfied2`, `ChipTableSound`, `1 < length`) hold, and the whole membership
relation is DERIVED, not assumed. -/
theorem witness_spec : MerkleMembers2 cHash
    ((envAt cTrace 0).loc LEAF) ((envAt cTrace 0).loc SIB0A) ((envAt cTrace 0).loc SIB0B)
    ((envAt cTrace 0).loc SIB0C) ((envAt cTrace 0).loc SIB1A) ((envAt cTrace 0).loc SIB1B)
    ((envAt cTrace 0).loc SIB1C) (cTrace.pub ROOT_PI) :=
  merkleMembership_sat_refines (by decide) concrete_sat concrete_chipSound

/-- The fired witness spec IS the closed-form true instance (`1020304050607 = cHash […]`). -/
theorem witness_spec_is_closed :
    MerkleMembers2 cHash
      ((envAt cTrace 0).loc LEAF) ((envAt cTrace 0).loc SIB0A) ((envAt cTrace 0).loc SIB0B)
      ((envAt cTrace 0).loc SIB0C) ((envAt cTrace 0).loc SIB1A) ((envAt cTrace 0).loc SIB1B)
      ((envAt cTrace 0).loc SIB1C) (cTrace.pub ROOT_PI)
    ↔ MerkleMembers2 cHash 1 2 3 4 5 6 7 1020304050607 := by
  rfl

/-- A trace with a BROKEN path: `CUR1 = 0 ≠ 1020304 = PARENT0`. -/
private def cRowBadChain : Assignment := fun c => if c = CUR1 then 0 else cRow c
private def cTraceBadChain : VmTrace := { cTrace with rows := [cRowBadChain, cRowBadChain] }

/-- **The descriptor genuinely REJECTS a broken path (continuity tooth BITES).** No `Satisfied2`
exists for the non-chaining trace: the chain-continuity gate on the transition row 0 forces
`CUR1 = PARENT0`, i.e. `0 = 1020304`. -/
theorem concrete_fail_chain :
    ¬ Satisfied2 cHash merkleMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBadChain := by
  intro h
  have hmem : VmConstraint2.base (.gate contBody) ∈ merkleMembershipDesc.constraints := by mm_mem
  have hlast : (0 + 1 == cTraceBadChain.rows.length) = false := by decide
  have h0 := activeGateZero h 0 (by decide) hlast contBody hmem
  revert h0; decide

/-- A trace with a WRONG top digest: `PARENT1 = 0 ≠ 1020304050607 = root PI`. -/
private def cRowBadRoot : Assignment := fun c => if c = PARENT1 then 0 else cRow c
private def cTraceBadRoot : VmTrace := { cTrace with rows := [cRowBadRoot, cRowBadRoot] }

/-- **The descriptor genuinely REJECTS a wrong root (root-pin tooth BITES).** No `Satisfied2` exists:
the first-row root pin forces the top parent `PARENT1` to equal the committed root PI, i.e.
`0 = 1020304050607`. -/
theorem concrete_fail_root :
    ¬ Satisfied2 cHash merkleMembershipDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBadRoot := by
  intro h
  have hmem : VmConstraint2.base (.piBinding VmRow.first PARENT1 ROOT_PI)
      ∈ merkleMembershipDesc.constraints := by mm_mem
  have h0 := firstPi h (by decide) PARENT1 ROOT_PI hmem
  revert h0; decide

/-! ## §6 — shape pins + axiom hygiene. -/

#guard decide (cTrace.rows.length = 2)
#guard decide (cTraceBadChain.rows.length = 2)
#guard decide (cTraceBadRoot.rows.length = 2)
-- the fold genuinely recomposes the two-level path (order-sensitive digit hash):
#guard foldNode4 cHash 1 [(2, 3, 4), (5, 6, 7)] == 1020304050607

#assert_axioms merkleMembers2_as_fold
#assert_axioms lookupChip4
#assert_axioms merkleMembership_sat_refines
#assert_axioms concrete_chipSound
#assert_axioms concrete_sat
#assert_axioms witness_spec
#assert_axioms concrete_fail_chain
#assert_axioms concrete_fail_root

end Dregg2.Circuit.Emit.MerkleMembershipRefine
