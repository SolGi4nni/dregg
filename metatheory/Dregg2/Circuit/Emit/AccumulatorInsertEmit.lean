/-
# Dregg2.Circuit.Emit.AccumulatorInsertEmit — the INSERT-shaped accumulator keystone, the CORRECT-shaped
genuine close for the FOURTH/FIFTH/SIXTH faithful-root (nullifier · commitments · cells — the three
DEDICATED accumulator roots), over the ACTUAL deployed sorted INSERT.

## Why this file exists (the update-shape obstruction, and the honest fix)

`AccumulatorOpenEmit.lean` built `effAccumWriteV3` / `accumOpen_writesTo8` — the UPDATE-AT-KEY shaped
after-spine (two `HeapMembershipCore` witnesses SHARING a sibling path, before = old leaf, after =
in-place-updated leaf at the SAME key). That shape is the exact twin of heap/fields, whose deployed
writes ARE update-at-key. But the three accumulators are NOT update-at-key: each accumulator write
(`noteSpend` nullifier-insert / `noteCreate` commitments-insert / `createCell` cells-insert) is a
SORTED-TREE FRESH-KEY INSERT (`heap_root.rs::CanonicalHeapTree8::insert_witness`) — the key is ABSENT
in BEFORE, splices at the sorted position, and the tree REBUILDS. There is NO shared before/after
path (a prior agent proved this a genuine obstruction). The update-shaped after-spine therefore does
NOT fit the accumulators.

This file builds the CORRECT insert-shaped keystone. The honest model of the sorted insert:
  (a) NON-MEMBERSHIP of the fresh key in BEFORE — the predecessor/successor bracket (`GapOpen8.inner`:
      `pred < key < succ`, both present + adjacent in the sorted tree) ⟹ `key ∉ keysOf8 beforeRoot`
      (`SortedTreeNonMembershipHeap8.nonMembership_sound8`);
  (b) MEMBERSHIP of the spliced `(key, value)` leaf in AFTER — `MembersAt8 afterRoot (key, value)`
      (the `insert_witness` membership path in the REBUILT tree reaching the AFTER root);
  (c) the ROOT RECOMPUTE tying BEFORE→AFTER — the set grows by EXACTLY the fresh key, in sorted order
      (`SortedTreeNonMembershipHeap8.update_sound8`: `keysOf8 afterRoot = insert key (keysOf8 beforeRoot)`).

## The deliverables
  * `accumInserts8` (§A) — the faithful insert relation (the insert twin of `heapWritesTo8`): fresh in
    BEFORE, present in AFTER, set-grows-by-exactly-key; its faithful consequences.
  * `accumInsert_writesTo8` (§B) — THE KEYSTONE: the non-membership witness + the AFTER membership +
    the two spine bindings FORCE `accumInserts8` over the FULL committed 8-felt BEFORE/AFTER root
    groups — NEVER the lane-0 squeeze. Parametric over the 3 families (like `accumOpen_writesTo8`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR floor enters only through
the `Heap8Scheme` node8 carrier already in play, and the realizable spine↔root binding `SpineCommits8`
is a HYPOTHESIS, never an axiom.
-/
import Dregg2.Circuit.SortedTreeNonMembershipHeap8
import Dregg2.Circuit.Emit.HeapOpenEmit

namespace Dregg2.Circuit.Emit.AccumulatorInsertEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (TraceFamily VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols DEPTH groupVal)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (MembersAt8)
open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols eqGate eqGate_eval)
open Dregg2.Circuit.Emit.HeapOpenEmit
  (heapLeafPairOf heapPermOut HeapMembershipCore heapOpen_recompose8
   effHeapOpenV3 effHeapOpenV3_core)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8
  (SpineCommits8 keysOf8 GapOpen8 keyOfH nonMembership_sound8 update_sound8)
open Dregg2.Circuit.SortedTreeNonMembership (sortedInsert)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §A — the faithful INSERT relation `accumInserts8` (the insert twin of `heapWritesTo8`).

`heapWritesTo8 S8 oldRoot k v newRoot` says a SHARED path recomposes `oldRoot` from `(k, oldVal)` and
`newRoot` from `(k, v)` — the update-at-key shape. The accumulator insert has NO shared path; the
faithful insert claim is instead: `key` was ABSENT in BEFORE, `(key, value)` is PRESENT in AFTER, and
the committed key set grows by EXACTLY `key`. We package it existentially over the (realizable) sorted
key spine the BEFORE root commits to. -/

/-- **`accumInserts8 S8 beforeRoot key value afterRoot`** — the faithful 8-felt accumulator INSERT: the
BEFORE root commits some sorted spine, `key` is ABSENT from the BEFORE tree, the spliced `(key, value)`
leaf is a MEMBER of the AFTER tree, and the AFTER root commits the INSERTED spine (`sortedInsert key
spine`). Over the FULL committed BEFORE/AFTER 8-felt root groups (~124-bit), NEVER lane-0. -/
def accumInserts8 (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ) (afterRoot : Digest8) :
    Prop :=
  ∃ spine : List ℤ,
    SpineCommits8 S8 beforeRoot spine ∧
    key ∉ keysOf8 S8 beforeRoot ∧
    MembersAt8 S8 afterRoot (key, value) ∧
    SpineCommits8 S8 afterRoot (sortedInsert key spine)

/-- **`accumInserts8_setGrows` — the faithful set-grow consequence.** The AFTER committed key set is
EXACTLY the BEFORE set plus the fresh `key` (`update_sound8`): the insert adds precisely `key`, nothing
else. The insert twin of `heapWritesTo8_forces_postleaf` at the set level. -/
theorem accumInserts8_setGrows (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ)
    (afterRoot : Digest8) (h : accumInserts8 S8 beforeRoot key value afterRoot) :
    ∀ y, y ∈ keysOf8 S8 afterRoot ↔ (y = key ∨ y ∈ keysOf8 S8 beforeRoot) := by
  obtain ⟨spine, hbefore, hfresh, _hmem, hafter⟩ := h
  exact update_sound8 S8 beforeRoot afterRoot key spine hbefore hfresh hafter

/-- **`accumInserts8_value_present`** — the written `(key, value)` leaf is a genuine MEMBER of the AFTER
tree at the FULL 8-felt root: the value is stored at `key` in AFTER, not merely lane-0-projected. -/
theorem accumInserts8_value_present (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ)
    (afterRoot : Digest8) (h : accumInserts8 S8 beforeRoot key value afterRoot) :
    MembersAt8 S8 afterRoot (key, value) := by
  obtain ⟨_spine, _hbefore, _hfresh, hmem, _hafter⟩ := h
  exact hmem

/-- **`accumInserts8_fresh`** — the inserted `key` was genuinely ABSENT from BEFORE (no overwrite): the
insert is a FRESH-key insert, not a silent update. Anti-ghost: distinguishes a genuine insert from an
update-at-key masquerade. -/
theorem accumInserts8_fresh (S8 : Heap8Scheme) (beforeRoot : Digest8) (key value : ℤ)
    (afterRoot : Digest8) (h : accumInserts8 S8 beforeRoot key value afterRoot) :
    key ∉ keysOf8 S8 beforeRoot := by
  obtain ⟨_spine, _hbefore, hfresh, _hmem, _hafter⟩ := h
  exact hfresh

/-! ## §B — THE KEYSTONE: `accumInsert_writesTo8` (the non-membership + after-membership + recompute
FORCE the faithful insert). Parametric over the 3 accumulator families (via the abstract roots/leaves).

Given: the BEFORE root commits a sorted spine; a `GapOpen8` covering `key` valid against that spine
(the pred/succ bracket, whose neighbor openings ride the proven `Heap8Scheme` recompose soundness); the
spliced `(key, value)` leaf opens against the AFTER root (`MembersAt8`); and the AFTER root commits the
inserted spine — then the faithful insert `accumInserts8` holds. This is the insert twin of
`accumOpen_writesTo8` — the STEP-A keystone the assurance case's per-family §J trio consumes. -/
theorem accumInsert_writesTo8 (S8 : Heap8Scheme)
    (beforeRoot afterRoot : Digest8) (key value : ℤ) (spine : List ℤ)
    (hbefore : SpineCommits8 S8 beforeRoot spine)
    (g : GapOpen8 S8 beforeRoot key) (hcov : g.coversSpine spine)
    (hafterMem : MembersAt8 S8 afterRoot (key, value))
    (hafter : SpineCommits8 S8 afterRoot (sortedInsert key spine)) :
    accumInserts8 S8 beforeRoot key value afterRoot := by
  -- (a) the fresh-key non-membership in BEFORE, from the covering gap over the committed spine.
  have hfresh : key ∉ keysOf8 S8 beforeRoot :=
    nonMembership_sound8 S8 beforeRoot key spine hbefore g hcov
  -- (b)+(c) assemble the faithful insert relation.
  exact ⟨spine, hbefore, hfresh, hafterMem, hafter⟩

/-- **`accumInsert_writesTo8_setGrows` — the KEYSTONE's headline consequence, in one shot.** From the
non-membership bracket + the AFTER membership + the two spine bindings, the AFTER committed key set is
EXACTLY the BEFORE set plus the fresh `key`. The genuine faithful 8-felt insert the apex proves per
accumulator family, over the ACTUAL sorted insert (NOT the update-at-key shared-spine). -/
theorem accumInsert_writesTo8_setGrows (S8 : Heap8Scheme)
    (beforeRoot afterRoot : Digest8) (key value : ℤ) (spine : List ℤ)
    (hbefore : SpineCommits8 S8 beforeRoot spine)
    (g : GapOpen8 S8 beforeRoot key) (hcov : g.coversSpine spine)
    (hafterMem : MembersAt8 S8 afterRoot (key, value))
    (hafter : SpineCommits8 S8 afterRoot (sortedInsert key spine)) :
    ∀ y, y ∈ keysOf8 S8 afterRoot ↔ (y = key ∨ y ∈ keysOf8 S8 beforeRoot) :=
  accumInserts8_setGrows S8 beforeRoot key value afterRoot
    (accumInsert_writesTo8 S8 beforeRoot afterRoot key value spine
      hbefore g hcov hafterMem hafter)

#assert_axioms accumInserts8_setGrows
#assert_axioms accumInserts8_value_present
#assert_axioms accumInserts8_fresh
#assert_axioms accumInsert_writesTo8
#assert_axioms accumInsert_writesTo8_setGrows

/-! ## §C — the DEPLOYED insert descriptor `effAccumInsertV3` + the trace-FORCED after-membership.

The insert-shaped descriptor a light client checks: the reused heap-open read (`effHeapOpenV3`) whose
`capRoot` group is welded to the committed AFTER accumulator block, with the read leaf's `(addr, value)`
pinned to the accumulator's published KEY / VALUE columns. Its `Satisfied2` TRACE-FORCES part (b) of
the honest insert — `MembersAt8 afterRoot (key, value)`, the spliced-leaf membership in the REBUILT
after-tree (exactly the `heap_root.rs::CanonicalHeapTree8::insert_witness` membership path). This is
SATISFIABLE by the honest insert producer (the after-membership path is what `insert_witness` fills).

Parts (a) [the fresh-key non-membership bracket in BEFORE] and (c) [the set-recompute] ride the
deployed `.absent`/`.insert` node8-AIR map-op (deployed-faithful) and the realizable `GapOpen8` /
`SpineCommits8` carriers — the SAME named-realizable status `SpineCommits8` carries throughout (a
HYPOTHESIS, never an axiom; never a fabricated shared path; never lane-0 — the spliced membership +
the BEFORE/AFTER roots are the FULL committed 8-felt groups). This is the assurance-layer twin of the
deployed node8-AIR insert faithfulness, EXACTLY as `AccumulatorOpenEmit.effAccumWriteV3` was for the
(non-fitting) update shape — here the shape is CORRECT for the accumulators' genuine sorted insert. -/

/-- The 8 AFTER accumulator-root weld gates: the read appendix `capRoot` group equals the committed
AFTER accumulator block (`groupCol (EFFECT_VM_WIDTH + 227)`) — the spliced leaf opens against AFTER. -/
def afterGroupWeldsI (groupCol : Nat → Fin 8 → Nat) (w : Nat) : List VmConstraint2 :=
  (List.finRange 8).map (fun i =>
    VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot i) (groupCol (EFFECT_VM_WIDTH + 227) i))))

/-- **The SELECTOR-GATED bind gate.** With `sel = none` the bind is UNCONDITIONAL (`var a - var col =
0`, byte-identical to a bare `eqGate` — the noteCreate/createCell families whose base economics do not
force the VALUE column to `0` off-row). With `sel = some s` the bind is GATED by the effect's runtime
selector column `s` (`var s · (var a - var col) = 0`): ACTIVE on the firing row (`s = 1`, forcing `a =
col` — the REAL bind, never removed) and VACUOUS on padding/off-row (`s = 0`) — the nullifier family,
whose base noteSpend economics force `NOTE_VALUE_LO = 0` on non-spend rows (conflicting with an
unconditional per-row value bind). The MEMBERSHIP + rootPin welds (`afterGroupWeldsI`) stay
UNCONDITIONAL regardless: the producer lays the appendix leaf constant, so the fold reaches the
after-root on every row. -/
def bindGateI (sel : Option Nat) (a col : Nat) : EmittedExpr :=
  match sel with
  | none   => eqGate a col
  | some s => .mul (.var s) (eqGate a col)

/-- The selector-gated bind forces `a = col` on any row where the gate holds AND (when gated) the
selector is `1`. Ungated (`none`): unconditional. Gated (`some s`): needs `env s = 1` (the active
firing row). -/
theorem bindGateI_forces (sel : Option Nat) (a col : Nat) (env : VmRowEnv)
    (h : (bindGateI sel a col).eval env.loc = 0)
    (hsel : ∀ s, sel = some s → env.loc s = 1) :
    env.loc a = env.loc col := by
  cases sel with
  | none => exact (eqGate_eval a col env).mp (by simpa [bindGateI] using h)
  | some s =>
    have hs : env.loc s = 1 := hsel s rfl
    have hg : (eqGate a col).eval env.loc = 0 := by
      have : env.loc s * (eqGate a col).eval env.loc = 0 := by
        simpa [bindGateI, EmittedExpr.eval] using h
      rw [hs, one_mul] at this; exact this
    exact (eqGate_eval a col env).mp hg

/-- The key-bind gate: the read leaf's `addr` (leaf 0) equals the accumulator's published KEY column,
selector-gated by `sel`. -/
def keyBindGateI (sel : Option Nat) (keyCol : Nat) (w : Nat) : EmittedExpr :=
  bindGateI sel ((capOpenCols w).leaf 0) keyCol

/-- The value-bind gate: the read leaf's `value` (leaf 1) equals the accumulator's published VALUE
column, selector-gated by `sel`. -/
def valueBindGateI (sel : Option Nat) (valueCol : Nat) (w : Nat) : EmittedExpr :=
  bindGateI sel ((capOpenCols w).leaf 1) valueCol

/-- The insert-appendix constraint list: the 8 AFTER-root welds (UNCONDITIONAL) + the selector-gated key
bind + the selector-gated value bind. All `.base (.gate …)` — reads no base column, contributes no
map/mem op (so the strip is additive) regardless of `sel`. -/
def accumInsertConstraints (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (w : Nat) : List VmConstraint2 :=
  afterGroupWeldsI groupCol w
  ++ [VmConstraint2.base (.gate (keyBindGateI sel keyCol w)),
      VmConstraint2.base (.gate (valueBindGateI sel valueCol w))]

/-- **`effAccumInsertV3 groupCol keyCol valueCol sel base name`** — the insert-shaped accumulator-write
descriptor: the reused heap-open read (`effHeapOpenV3`) with its `capRoot` welded to the AFTER
accumulator block + the SELECTOR-GATED KEY/VALUE binds. NO after-spine (the insert has no shared
before/after path; the fresh-key non-membership is the deployed `.absent` map-op, not a second in-row
membership). Its `Satisfied2` FORCES `MembersAt8 afterRoot (key, value)`
(`effAccumInsertV3_forces_afterMembership`) on the active row. `sel = none` is byte-identical to the
un-gated descriptor (the always-bound families); `sel = some s` gates the binds on the runtime selector
`s` (the nullifier family). -/
def effAccumInsertV3 (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { (effHeapOpenV3 base name) with
    name        := name
    constraints := (effHeapOpenV3 base name).constraints
                     ++ accumInsertConstraints groupCol keyCol valueCol sel base.traceWidth }

/-- Every insert-appendix constraint is a constraint of the write descriptor. -/
theorem effAccumInsertV3_appMem (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ accumInsertConstraints groupCol keyCol valueCol sel base.traceWidth) :
    c ∈ (effAccumInsertV3 groupCol keyCol valueCol sel base name).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the insert descriptor strips (constraint-subset) to a `Satisfied2` of the reused
heap-open read `effHeapOpenV3` — the insert appendix is all `.base (.gate …)`, reads no base column and
contributes no map/mem op. -/
theorem effAccumInsertV3_strips_to_open (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat)
    (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (h : Satisfied2 hash (effAccumInsertV3 groupCol keyCol valueCol sel base name) minit mfin maddrs t) :
    Satisfied2 hash (effHeapOpenV3 base name) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (effAccumInsertV3 groupCol keyCol valueCol sel base name)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effHeapOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effAccumInsertV3, accumInsertConstraints,
      afterGroupWeldsI, List.filterMap_append, List.filterMap_map, List.filterMap_cons]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (effAccumInsertV3 groupCol keyCol valueCol sel base name)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effHeapOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effAccumInsertV3, accumInsertConstraints,
      afterGroupWeldsI, List.filterMap_append, List.filterMap_map, List.filterMap_cons]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (effAccumInsertV3 groupCol keyCol valueCol sel base name) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effHeapOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (effAccumInsertV3 groupCol keyCol valueCol sel base name) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effHeapOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effHeapOpenV3 base name).constraints
                     ++ accumInsertConstraints groupCol keyCol valueCol sel base.traceWidth
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- Any insert-appendix `.base (.gate g)` constraint forces `g.eval = 0` on an active (non-last) row. -/
theorem accumInsertI_gate_forces (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat)
    (sel : Option Nat) (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effAccumInsertV3 groupCol keyCol valueCol sel base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr)
    (hin : VmConstraint2.base (.gate g)
             ∈ accumInsertConstraints groupCol keyCol valueCol sel base.traceWidth) :
    g.eval (envAt t i).loc = 0 := by
  have hrow := hsat.rowConstraints i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hrow _ (effAccumInsertV3_appMem groupCol keyCol valueCol sel base name _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- **`effAccumInsertV3_forces_afterMembership`** — THE STEP-B DELIVERABLE: a `Satisfied2` of the insert
descriptor TRACE-FORCES `MembersAt8 afterRoot (key, value)` over the FULL committed AFTER accumulator
group (`groupCol (EFFECT_VM_WIDTH + 227)`, the whole ~124-bit root) at the accumulator's published
`keyCol`/`valueCol` — the spliced-leaf membership in the rebuilt after-tree. -/
theorem effAccumInsertV3_forces_afterMembership (S8 : Heap8Scheme)
    (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat) (sel : Option Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (heapPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumInsertV3 groupCol keyCol valueCol sel base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hsel : ∀ s, sel = some s → (envAt t i).loc s = 1) :
    MembersAt8 S8 (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + 227) k))
      ((envAt t i).loc keyCol, (envAt t i).loc valueCol) := by
  set e := envAt t i with he
  set w := base.traceWidth with hw
  -- the membership core from the reused heap-open read.
  have hopenSat := effAccumInsertV3_strips_to_open groupCol keyCol valueCol sel
    hash base name minit mfin maddrs t hsat
  have hcore : HeapMembershipCore t.tf (capOpenCols w) e :=
    effHeapOpenV3_core base name hash minit mfin maddrs t hopenSat i hi hnotlast
  have hrec := heapOpen_recompose8 S8 t.tf (capOpenCols w) e hChip hcore
  have hmem0 : MembersAt8 S8 (groupVal e (capOpenCols w).capRoot) (heapLeafPairOf (capOpenCols w) e) :=
    ⟨_, hrec⟩
  -- weld: the read capRoot group IS the committed AFTER accumulator group.
  have hroot : groupVal e (capOpenCols w).capRoot
      = (fun k => e.loc (groupCol (EFFECT_VM_WIDTH + 227) k)) := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot k)
        (groupCol (EFFECT_VM_WIDTH + 227) k)))
        ∈ accumInsertConstraints groupCol keyCol valueCol sel w := by
      refine List.mem_append_left _ ?_
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have := (eqGate_eval _ _ e).mp
      (accumInsertI_gate_forces groupCol keyCol valueCol sel base name hash minit mfin maddrs t hsat
        i hi hnotlast _ hin)
    simpa [groupVal] using this
  -- key/value binds: the read leaf's (addr, value) is (keyCol, valueCol), selector-gated (`hsel`).
  have hkeyb : e.loc ((capOpenCols w).leaf 0) = e.loc keyCol := by
    have hin : VmConstraint2.base (.gate (keyBindGateI sel keyCol w))
        ∈ accumInsertConstraints groupCol keyCol valueCol sel w := by
      refine List.mem_append_right _ ?_; simp
    exact bindGateI_forces sel ((capOpenCols w).leaf 0) keyCol e
      (accumInsertI_gate_forces groupCol keyCol valueCol sel base name hash minit mfin maddrs t hsat
        i hi hnotlast _ hin) hsel
  have hvalb : e.loc ((capOpenCols w).leaf 1) = e.loc valueCol := by
    have hin : VmConstraint2.base (.gate (valueBindGateI sel valueCol w))
        ∈ accumInsertConstraints groupCol keyCol valueCol sel w := by
      refine List.mem_append_right _ ?_; simp
    exact bindGateI_forces sel ((capOpenCols w).leaf 1) valueCol e
      (accumInsertI_gate_forces groupCol keyCol valueCol sel base name hash minit mfin maddrs t hsat
        i hi hnotlast _ hin) hsel
  have hpair : heapLeafPairOf (capOpenCols w) e = (e.loc keyCol, e.loc valueCol) := by
    simp only [heapLeafPairOf, hkeyb, hvalb]
  rw [hroot, hpair] at hmem0
  exact hmem0

/-- **`effAccumInsertV3_forces_write8` — THE STEP-A+B DELIVERABLE (assurance layer, per accumulator
family).** A `Satisfied2` of the insert descriptor, together with the realizable non-membership bracket
(`GapOpen8` over the committed BEFORE spine) + the two spine bindings, FORCES the faithful 8-felt
INSERT `accumInserts8` over the FULL committed BEFORE/AFTER accumulator-root groups: the spliced
`(key, value)` leaf membership in AFTER is TRACE-FORCED; the fresh-key non-membership in BEFORE and the
set-recompute ride the realizable carriers (`SpineCommits8`, a HYPOTHESIS — the deployed
`compute_canonical_heap_root_8` fold — never an axiom, never lane-0). The insert twin of
`AccumulatorOpenEmit.effAccumWriteV3_forces_write8`, CORRECT-shaped for the genuine sorted insert. -/
theorem effAccumInsertV3_forces_write8 (S8 : Heap8Scheme)
    (groupCol : Nat → Fin 8 → Nat) (keyCol valueCol : Nat) (sel : Option Nat)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (heapPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumInsertV3 groupCol keyCol valueCol sel base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hsel : ∀ s, sel = some s → (envAt t i).loc s = 1)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k)) spine)
    (g : GapOpen8 S8 (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k)) ((envAt t i).loc keyCol))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits8 S8 (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + 227) k))
                (sortedInsert ((envAt t i).loc keyCol) spine)) :
    accumInserts8 S8
        (fun k => (envAt t i).loc (groupCol EFFECT_VM_WIDTH k))
        ((envAt t i).loc keyCol)
        ((envAt t i).loc valueCol)
        (fun k => (envAt t i).loc (groupCol (EFFECT_VM_WIDTH + 227) k)) := by
  have hafterMem := effAccumInsertV3_forces_afterMembership S8 groupCol keyCol valueCol sel
    base name hash minit mfin maddrs t hChip hsat i hi hnotlast hsel
  exact accumInsert_writesTo8 S8 _ _ _ _ spine hbefore g hcov hafterMem hafter

#assert_axioms effAccumInsertV3_forces_afterMembership
#assert_axioms effAccumInsertV3_forces_write8

end Dregg2.Circuit.Emit.AccumulatorInsertEmit
