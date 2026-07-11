/-
# Dregg2.Circuit.Emit.CapInsertEmit — the INSERT-shaped CAP-tree keystone, the assurance core for the
three cap-key-SET-GROWING cap-writes (`delegate` / `introduce` / `delegateAtten`).

## Why this file exists (the cap-write liveness break — writesTo8 is UPDATE-at-key only)

`CapOpenEmit.lean`'s after-spine (`effCapOpenWriteV3` + `afterSpineCols`) is the UPDATE-AT-KEY shape:
it membership-opens an EXISTING cap leaf against BEFORE, narrows it in place, and re-opens the narrowed
leaf against AFTER at the SAME sibling path — the exact shape `attenuate` needs (the key set is
PRESERVED, only the leaf VALUE moves). But the OTHER cap-writes that CHANGE the cap key-set do NOT fit
that shape: `delegate` / `introduce` / `delegateAtten` each SPLICE a FRESH cap key into the sorted
cap-tree (`cap_root.rs::CanonicalCapTree::insert_witness`) — the key is ABSENT in BEFORE, lands at the
sorted position, and the tree REBUILDS. There is NO shared before/after path. The update-shaped
after-spine therefore does NOT fit them (the exact accumulator obstruction, at the arity-7 cap tree).

This file builds the CORRECT insert-shaped keystone — the cap twin of `AccumulatorInsertEmit`
(`accumInsert_writesTo8` for the arity-2 heap tree), here over the arity-7 CAP tree keyed by
`CapLeaf.slot_hash`. The honest model of the sorted cap insert:
  (a) NON-MEMBERSHIP of the fresh cap key in BEFORE — the pred/succ bracket (`GapOpen.inner`:
      `pred < key < succ`, both present + adjacent in the sorted cap-tree) ⟹ `key ∉ keysOf beforeRoot`
      (`SortedTreeNonMembership.nonMembership_sound`, over `Cap8Scheme.MembersAt8`);
  (b) MEMBERSHIP of the spliced cap leaf in AFTER — `MembersAt8 afterRoot leaf` (the `insert_witness`
      recompose path in the REBUILT cap-tree reaching the AFTER cap-root8), TRACE-FORCED off the reused
      `effCapOpenV3` membership read welded to the committed AFTER cap-root group;
  (c) the ROOT RECOMPUTE tying BEFORE→AFTER — the cap key set grows by EXACTLY the fresh key, in sorted
      order (`SortedTreeNonMembership.update_sound` / `CapTreeUpdate.capInsert_sound`).

## The deliverables
  * `capInserts8` (§A) — the faithful arity-7 cap INSERT relation (the cap twin of `accumInserts8`):
    fresh in BEFORE, present in AFTER, set-grows-by-exactly-key; its faithful consequences.
  * `capInsert_writesTo8` (§B) — THE KEYSTONE: the non-membership bracket + the AFTER cap-membership +
    the two spine bindings FORCE `capInserts8` over the FULL committed 8-felt BEFORE/AFTER cap-root
    groups — NEVER lane-0. The cap analog of `accumInsert_writesTo8`.
  * `effCapInsertV3` (§C) — the DEPLOYED insert-shaped cap descriptor: the reused `effCapOpenV3`
    membership read welded to the committed AFTER cap-root group. `effCapInsertV3_forces_write8`
    TRACE-FORCES the honest insert (b) is forced, (a)+(c) ride the realizable carriers).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon2-CR floor enters only through
the `Cap8Scheme` arity-16 `node8` carrier already in play, and the realizable spine↔root binding
`SpineCommits` is a HYPOTHESIS, never an axiom; never a fabricated shared path; never lane-0.
-/
import Dregg2.Circuit.SortedTreeNonMembership
import Dregg2.Circuit.CapTreeUpdate
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.Emit.CapInsertEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (TraceFamily VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (MembersAt8)
open Dregg2.Circuit.DeployedCapOpen
  (CapOpenCols leafOf groupVal capPermOut SatisfiedEff capOpenEff_membership
   MembershipCore membershipCore_opens)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols eqGate eqGate_eval effCapOpenV3 effCapOpenV3_satisfiedEff
   effCapOpenV3_membershipCore diffGate_exact
   afterCapRootWelds effCapInsertV3)
open Dregg2.Circuit.SortedTreeNonMembership
  (SpineCommits keysOf GapOpen keyOf nonMembership_sound update_sound sortedInsert)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (capRootGroupCol)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §A — the faithful arity-7 cap INSERT relation `capInserts8` (the cap twin of `accumInserts8`).

The cap insert has NO shared before/after path; the faithful insert claim is: the fresh cap `leaf`'s
key (`keyOf leaf = leaf.slot_hash`) was ABSENT in BEFORE, the whole 7-field `leaf` is PRESENT in AFTER
(`MembersAt8 afterRoot leaf`), and the committed cap key set grows by EXACTLY that key. Packaged
existentially over the (realizable) sorted key spine the BEFORE cap-root commits. -/

/-- **`capInserts8 S8 beforeRoot leaf afterRoot`** — the faithful 8-felt CAP insert: the BEFORE cap-root
commits some sorted spine, `keyOf leaf` is ABSENT from the BEFORE cap-tree, the spliced 7-field `leaf`
is a MEMBER of the AFTER cap-tree, and the AFTER cap-root commits the INSERTED spine (`sortedInsert
(keyOf leaf) spine`). Over the FULL committed BEFORE/AFTER 8-felt cap-root groups (~124-bit), NEVER
lane-0. The cap `leaf` carries the whole authority edge (target/tier/facet), so no separate key/value
columns are needed — `keyOf leaf` is the sort key. -/
def capInserts8 (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf) (afterRoot : Digest8) :
    Prop :=
  ∃ spine : List ℤ,
    SpineCommits S8 beforeRoot spine ∧
    keyOf leaf ∉ keysOf S8 beforeRoot ∧
    MembersAt8 S8 afterRoot leaf ∧
    SpineCommits S8 afterRoot (sortedInsert (keyOf leaf) spine)

/-- **`capInserts8_setGrows` — the faithful set-grow consequence.** The AFTER committed cap key set is
EXACTLY the BEFORE set plus the fresh `keyOf leaf` (`update_sound`): the delegate/introduce adds
precisely the new cap key, nothing else. -/
theorem capInserts8_setGrows (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) (h : capInserts8 S8 beforeRoot leaf afterRoot) :
    ∀ y, y ∈ keysOf S8 afterRoot ↔ (y = keyOf leaf ∨ y ∈ keysOf S8 beforeRoot) := by
  obtain ⟨spine, hbefore, hfresh, _hmem, hafter⟩ := h
  exact update_sound S8 beforeRoot afterRoot (keyOf leaf) spine hbefore hfresh hafter

/-- **`capInserts8_leaf_present`** — the whole 7-field cap `leaf` (target/tier/facet) is a genuine MEMBER
of the AFTER cap-tree at the FULL 8-felt cap-root: the new authority edge is stored, not merely
lane-0-projected. -/
theorem capInserts8_leaf_present (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) (h : capInserts8 S8 beforeRoot leaf afterRoot) :
    MembersAt8 S8 afterRoot leaf := by
  obtain ⟨_spine, _hbefore, _hfresh, hmem, _hafter⟩ := h
  exact hmem

/-- **`capInserts8_fresh`** — the inserted `keyOf leaf` was genuinely ABSENT from BEFORE (no overwrite):
the cap insert is a FRESH-key insert, not a silent in-place rebind. Anti-ghost: distinguishes a genuine
delegate/introduce from an attenuate-shaped update-at-key masquerade. -/
theorem capInserts8_fresh (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) (h : capInserts8 S8 beforeRoot leaf afterRoot) :
    keyOf leaf ∉ keysOf S8 beforeRoot := by
  obtain ⟨_spine, _hbefore, hfresh, _hmem, _hafter⟩ := h
  exact hfresh

/-! ## §B — THE KEYSTONE: `capInsert_writesTo8` (the non-membership + after-membership + recompute FORCE
the faithful cap insert). Covers `delegate` / `introduce` / `delegateAtten` (all splice a fresh cap key).

Given: the BEFORE cap-root commits a sorted spine; a `GapOpen` covering `keyOf leaf` valid against that
spine (the pred/succ bracket, whose neighbor openings ride the proven `Cap8Scheme` recompose
soundness); the spliced 7-field `leaf` opens against the AFTER cap-root (`MembersAt8`); and the AFTER
cap-root commits the inserted spine — then the faithful insert `capInserts8` holds. The cap twin of
`AccumulatorInsertEmit.accumInsert_writesTo8`. -/
theorem capInsert_writesTo8 (S8 : Cap8Scheme)
    (beforeRoot afterRoot : Digest8) (leaf : CapLeaf) (spine : List ℤ)
    (hbefore : SpineCommits S8 beforeRoot spine)
    (g : GapOpen S8 beforeRoot (keyOf leaf)) (hcov : g.coversSpine spine)
    (hafterMem : MembersAt8 S8 afterRoot leaf)
    (hafter : SpineCommits S8 afterRoot (sortedInsert (keyOf leaf) spine)) :
    capInserts8 S8 beforeRoot leaf afterRoot := by
  -- (a) the fresh-key non-membership in BEFORE, from the covering gap over the committed spine.
  have hfresh : keyOf leaf ∉ keysOf S8 beforeRoot :=
    nonMembership_sound S8 beforeRoot (keyOf leaf) spine hbefore g hcov
  -- (b)+(c) assemble the faithful insert relation.
  exact ⟨spine, hbefore, hfresh, hafterMem, hafter⟩

/-- **`capInsert_writesTo8_setGrows` — the KEYSTONE's headline consequence, in one shot.** From the
non-membership bracket + the AFTER cap-membership + the two spine bindings, the AFTER committed cap key
set is EXACTLY the BEFORE set plus the fresh `keyOf leaf`. The genuine faithful 8-felt cap insert, over
the ACTUAL sorted cap insert (NOT the attenuate update-at-key shared-spine). -/
theorem capInsert_writesTo8_setGrows (S8 : Cap8Scheme)
    (beforeRoot afterRoot : Digest8) (leaf : CapLeaf) (spine : List ℤ)
    (hbefore : SpineCommits S8 beforeRoot spine)
    (g : GapOpen S8 beforeRoot (keyOf leaf)) (hcov : g.coversSpine spine)
    (hafterMem : MembersAt8 S8 afterRoot leaf)
    (hafter : SpineCommits S8 afterRoot (sortedInsert (keyOf leaf) spine)) :
    ∀ y, y ∈ keysOf S8 afterRoot ↔ (y = keyOf leaf ∨ y ∈ keysOf S8 beforeRoot) :=
  capInserts8_setGrows S8 beforeRoot leaf afterRoot
    (capInsert_writesTo8 S8 beforeRoot afterRoot leaf spine hbefore g hcov hafterMem hafter)

#assert_axioms capInserts8_setGrows
#assert_axioms capInserts8_leaf_present
#assert_axioms capInserts8_fresh
#assert_axioms capInsert_writesTo8
#assert_axioms capInsert_writesTo8_setGrows

/-! ## §C — the DEPLOYED insert descriptor `effCapInsertV3` + the trace-FORCED after-membership.

The insert-shaped cap descriptor a light client checks: the reused cap-membership read (`effCapOpenV3`)
whose `capRoot` group is welded to the committed AFTER cap-root block — so the read opens the spliced
cap leaf against AFTER. Its `Satisfied2` TRACE-FORCES part (b) of the honest insert —
`MembersAt8 afterRoot (leafOf …)`, the spliced-leaf membership in the REBUILT after cap-tree (exactly
the `cap_root.rs::CanonicalCapTree::insert_witness` recompose path). SATISFIABLE by the honest insert
producer (the after-membership path is what `insert_witness` fills).

Parts (a) [the fresh-key non-membership bracket in BEFORE] and (c) [the set-recompute] ride the
deployed `.absent`/`.insert` node8-AIR map-op (deployed-faithful) and the realizable `GapOpen` /
`SpineCommits` carriers — the SAME named-realizable status `SpineCommits` carries throughout (a
HYPOTHESIS, never an axiom; never a fabricated shared path; never lane-0 — the spliced membership +
the BEFORE/AFTER cap-roots are the FULL committed 8-felt groups). The cap twin of
`AccumulatorInsertEmit.effAccumInsertV3`. -/

/-! The descriptor defs `afterCapRootWelds` / `effCapInsertV3` LIVE in `CapOpenEmit` (the deployed
wrapper definitions there reference them, and this file imports `CapOpenEmit` — the defs cannot live
here without a cycle). This section proves the keystone theorems ABOUT them. -/

/-- Every AFTER-weld constraint is a constraint of the insert descriptor. -/
theorem effCapInsertV3_appMem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ afterCapRootWelds base.traceWidth) :
    c ∈ (effCapInsertV3 base name n).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the insert descriptor strips (constraint-subset) to a `Satisfied2` of the reused
cap-membership read `effCapOpenV3` — the AFTER welds are all `.base (.gate …)`, read no base column and
contribute no map/mem op. -/
theorem effCapInsertV3_strips_to_capOpen (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (h : Satisfied2 hash (effCapInsertV3 base name n) minit mfin maddrs t) :
    Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapInsertV3 base name n)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapOpenV3 base name n) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effCapInsertV3, afterCapRootWelds,
      List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapInsertV3 base name n)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapOpenV3 base name n) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effCapInsertV3, afterCapRootWelds,
      List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (effCapInsertV3 base name n) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effCapOpenV3 base name n) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (effCapInsertV3 base name n) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effCapOpenV3 base name n) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effCapOpenV3 base name n).constraints ++ afterCapRootWelds base.traceWidth
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- Any AFTER-weld `.base (.gate g)` constraint forces `g.eval ≡ 0 [ZMOD p]` on an active (non-last)
row — the field-faithful gate consequence (the ℤ equality follows under cell canonicality, at the
consumer). -/
theorem effCapInsertV3_gate_forces (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effCapInsertV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr) (hin : VmConstraint2.base (.gate g) ∈ afterCapRootWelds base.traceWidth) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hrow _ (effCapInsertV3_appMem base name n _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- **`effCapInsertV3_forces_afterMembership`** — THE STEP-B DELIVERABLE: a `Satisfied2` of the insert
descriptor TRACE-FORCES `MembersAt8 afterRoot (leafOf …)` over the FULL committed AFTER cap-root group
(`capRootGroupCol (EFFECT_VM_WIDTH + 239)`, the whole ~124-bit cap-root) at the read leaf — the
spliced-leaf membership in the rebuilt after cap-tree. -/
theorem effCapInsertV3_forces_afterMembership (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    -- the deployed cell canonicality (`0 ≤ · < p`): lifts the mod-`p` membership gates + welds to
    -- their ℤ form (the Merkle fold and `MembersAt8` are ℤ-level).
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    MembersAt8 S8 (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + 239) k))
      (leafOf (capOpenCols base.traceWidth) (envAt t i)) := by
  set e := envAt t i with he
  set w := base.traceWidth with hw
  -- strip to the reused cap-open read, rebuild the membership CORE, read off the 8-felt membership.
  have hopenSat := effCapInsertV3_strips_to_capOpen base name n hash minit mfin maddrs t hsat
  have hCore : MembershipCore hash t.tf (capOpenCols w) e :=
    effCapOpenV3_membershipCore base name n hash minit mfin maddrs t hopenSat i hi hnotlast hcells
  have hmem0 : MembersAt8 S8 (groupVal e (capOpenCols w).capRoot) (leafOf (capOpenCols w) e) :=
    membershipCore_opens S8 hash t.tf (capOpenCols w) e hChip hCore
  -- weld: the read capRoot group IS the committed AFTER cap-root group.
  have hroot : groupVal e (capOpenCols w).capRoot
      = (fun k => e.loc (capRootGroupCol (EFFECT_VM_WIDTH + 239) k)) := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot k)
        (capRootGroupCol (EFFECT_VM_WIDTH + 239) k))) ∈ afterCapRootWelds w :=
      List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have hmod := effCapInsertV3_gate_forces base name n hash minit mfin maddrs t hsat i hi hnotlast _ hin
    -- the eqGate residual collapses in `(−p, p)` under canonicality.
    unfold Dregg2.Circuit.Emit.CapOpenEmit.eqGate at hmod
    simp only [EmittedExpr.eval] at hmod
    have := diffGate_exact (hcells _) (hcells _) hmod
    simp only [groupVal]
    linarith
  rw [hroot] at hmem0
  exact hmem0

/-- **`effCapInsertV3_forces_write8` — THE STEP-A+B DELIVERABLE (assurance layer, per cap-write family).**
A `Satisfied2` of the insert descriptor, together with the realizable non-membership bracket (`GapOpen`
over the committed BEFORE cap spine) + the two spine bindings, FORCES the faithful 8-felt CAP insert
`capInserts8` over the FULL committed BEFORE/AFTER cap-root groups: the spliced 7-field leaf membership
in AFTER is TRACE-FORCED; the fresh-key non-membership in BEFORE and the set-recompute ride the
realizable carriers (`SpineCommits`, a HYPOTHESIS — the deployed `compute_canonical_capability_root_felt`
fold — never an axiom, never lane-0). Covers `delegate` / `introduce` / `delegateAtten`. The cap twin of
`AccumulatorInsertEmit.effAccumInsertV3_forces_write8`. -/
theorem effCapInsertV3_forces_write8 (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (spine : List ℤ)
    (hbefore : SpineCommits S8 (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k)) spine)
    (g : GapOpen S8 (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k))
          (keyOf (leafOf (capOpenCols base.traceWidth) (envAt t i))))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits S8 (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + 239) k))
                (sortedInsert (keyOf (leafOf (capOpenCols base.traceWidth) (envAt t i))) spine)) :
    capInserts8 S8
        (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k))
        (leafOf (capOpenCols base.traceWidth) (envAt t i))
        (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + 239) k)) := by
  have hafterMem := effCapInsertV3_forces_afterMembership S8 base name n hash minit mfin maddrs t
    hChip hsat i hi hnotlast hcells
  exact capInsert_writesTo8 S8 _ _ (leafOf (capOpenCols base.traceWidth) (envAt t i)) spine
    hbefore g hcov hafterMem hafter

#assert_axioms effCapInsertV3_forces_afterMembership
#assert_axioms effCapInsertV3_forces_write8

end Dregg2.Circuit.Emit.CapInsertEmit
