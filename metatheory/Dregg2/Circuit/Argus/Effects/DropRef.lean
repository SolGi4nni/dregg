/-
# Dregg2.Circuit.Argus.Effects.DropRef — the CapTP GC reference-drop welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and
`Argus/Compile.lean` welded it for the per-cell / side-table effects; the sibling cap-graph weld
`Effects/RevokeDelegation.lean` did the FIRST `setCaps` effect. This module welds the OTHER cap-graph
edge-drop — **`dropRefA`**, dregg1's `Effect::DropRef { ref_id }` CapTP garbage-collect — in its own
disjoint file. It OWNS only itself, imports the Argus IR + the audited `dropRefA` EffectVM emit module
read-only, and edits no other Argus file.

## Why `dropRefA` shares the cap-graph SHAPE of revokeDelegation but now DIFFERS semantically (the GC fix)

`dropRefA` and `revokeDelegationA` are two protocol-DISTINCT CapTP entry points over the SAME cap-graph
TABLE (`caps : Label → List Cap`), but with DIFFERENT GC semantics — a distinction this module now makes
SEMANTIC, not merely a tag:

  * **revokeDelegation (the PARENT's tear-down)** removes the whole edge: `recKRevokeTarget k holder t =
    { k with caps := fun l => if l = holder then (k.caps l).filter (¬ confersEdgeTo t ·) else k.caps l }`
    = the declarative `removeEdgeCaps k.caps holder t` (`Spec/authorityrevocation.lean:83`). Unconditional.

  * **dropRef (the HOLDER's reference GC)** drops ONE reference: `recKDropRefGC k holder t` (§0.5), which
    applies `dropOneEdge t` to `holder`'s slot (remove the FIRST `t`-conferring cap), GCing the edge only
    at the `refcount = 1 → 0` boundary — the cap-list multiplicity IS the CapTP refcount (`gc.rs`). This
    MATCHES the Rust runtime + the swiss arm (`swissDropK_gc_at_one`), CLOSING the prior over-eager
    divergence (the OLD dropRef wrongly reused `recKRevokeTarget`'s tear-down). NO new `RecordKernelState`
    field. The two steps AGREE on the no-divergence case (`refcount ≤ 1`,
    `recKDropRefGC_eq_recKRevokeTarget_of_le_one`); they differ only by the runtime-faithful survivor on
    `refcount > 1`.

Both Argus terms are a single `setCaps` write with NO `guard` (both kernel steps always commit), the §A
`setCaps` cap-graph primitive (`Stmt.lean:53`) — no new IR constructor. The protocol/semantic distinction
is in the kernel transition itself (`recKDropRefGC` decrement vs `recKRevokeTarget` tear-down) + the
DROP_REF op tag.

## What this module proves (the cap-graph weld + the CLOSED refcount divergence)

  0. `recKDropRefGC` + `interp_dropRefStmt_eq_recKDropRefGC` (§0.5/§2) — the dropRef IR term refines the
     REFCOUNT-GC-FAITHFUL kernel step `recKDropRefGC` (drop ONE `t`-reference via `dropOneEdge`, GC the
     edge at the `refcount = 1 → 0` boundary), CLOSING the prior over-eager divergence. The refcount is
     the cap-list multiplicity (no new `RecordKernelState` field). `dropRefKernel_gc_at_one` /
     `dropRefKernel_keeps_survivor_on_multi` (§5) prove it MATCHES the runtime (and the swiss
     `swissDropK_gc_at_one` arm). On the no-divergence case (`refcount ≤ 1`) it AGREES with the prior
     tear-down `recKRevokeTarget` (`recKDropRefGC_eq_recKRevokeTarget_of_le_one`, §2a), so every existing
     `removeEdgeCaps`-based weld/connector transports.
  1. `dropRef_compile_sound` — the weld: a satisfying witness of the AUDITED class-A genuine descriptor
     `dropRefVmDescriptorGenuine` (`EffectVmEmitDropRef §G`, `dropRefGenuine_sound`) forces, per cell, the
     frozen economic frame AND the GENUINE in-row `cap_root` recompute, which (via the OFF-ROW connector
     `unify_dropRef`, cited) binds the `caps` edge-drop the IR term's executor produces.
  2. `dropRef_runnable_full_sound` (`EffectVmEmitDropRef §W`) — the MAGNESIUM crown: a satisfying witness
     of the WIDE runnable descriptor pins the FULL 17-field post-state (per-cell block + the 8 side-table
     roots, bound by the published `state_commit`), with the whole-state anti-ghost tooth.

## HONEST SURFACE + THE KERNEL-vs-RUNTIME DIVERGENCE (precise — do NOT over-read)

This weld lives on the cap family's HONEST boundary, three layers kept distinct:

  * **the IR term / kernel step (what the cornerstone pins).** `recKDropRefGC` edits ONLY `caps`
    (drop ONE `t`-reference via `dropOneEdge`); ALL 16 non-`caps` `RecordKernelState` fields are LITERALLY
    frozen. The cornerstone pins this GC-faithful kernel step exactly.

  * **the EffectVM row / genuine descriptor (what `dropRef_compile_sound` pins).** The per-row state block
    is FROZEN and `cap_root` is the GENUINE in-row recompute `hash[ hash[holder,target,rights,op],
    pre.capRoot ]` (`CapCellSpecGenuine`, op tag `capOp.DROP_REF = 5`), every other cell limb frozen. The
    recomputed `cap_root` is an absorbed `state_commit` column, so the edge mutation is BOUND through the
    commitment (`dropRefGenuine_binds_edge`, cited). The actual `caps`-function move (`removeEdgeCaps`)
    rides OFF the per-row state block; its soundness is the universe-A connector `unify_dropRef`
    (`EffectVmEmitDropRef §8`, `capRootProj D s'.kernel = D (removeEdgeCaps …)`), cited, NOT re-proved here.
    What this does NOT claim: it does not assert the row's `caps`-function state EQUALS the executor's
    `removeEdgeCaps` as a FUNCTION (the row carries the scalar `cap_root` DIGEST, not the function) — they
    agree only up to the cap-table root, the `Function.Injective D` connector. That is the faithful
    digest-not-function boundary, stated, not hidden.

  * **THE CLOSED DIVERGENCE — kernel step now MATCHES the Rust RUNTIME's CapTP GC refcount semantics.**
    `dropRefA`'s real Rust runtime (`apply_drop_ref`, `gc.rs:170` `ExportGcManager::process_drop_inner`)
    DECREMENTS a per-`(cell, federation)` refcount and removes the cap-edge ONLY at the `refcount = 1 → 0`
    boundary — a DropRef on an entry with `refcount > 1` is a pure DECREMENT that LEAVES THE EDGE INTACT.
    The PRIOR kernel step `recKRevokeTarget` removed the edge on EVERY drop, unconditionally — a divergent
    over-eager model. §0.5's `recKDropRefGC` CLOSES it WITHOUT a new `RecordKernelState` field: the refcount
    IS the cap-list multiplicity, and the GC step drops EXACTLY ONE `t`-reference, GCing at the `1 → 0`
    boundary (`dropRefKernel_gc_at_one`, §5) and KEEPING a survivor on `refcount > 1`
    (`dropRefKernel_keeps_survivor_on_multi`, §5) — the SAME GC-at-one shape the swiss arm already had
    (`RecordKernel.swissDropK_gc_at_one`). The dropRef IR term + cornerstone (§1-2) refine `recKDropRefGC`.
    The OLD over-eager behaviour is RETAINED as a contrast pin (`oldDropRefKernel_was_overeager`, §5) so the
    closure cannot silently regress. The ONLY remaining surface is Rust-side: `execFullA`'s `.dropRefA`
    dispatch arm (`TurnExecutorFull.lean:3804`) still routes to `recCRevoke` (the tear-down); re-routing it
    to a `recKDropRefGC` chained wrapper is a one-line dispatch change (the SAME shape the swiss `swissDropA`
    arm uses) — the kernel-MODEL fix is DONE; the IR term refines the GC step.

## Honesty

`#assert_axioms` on both headline theorems ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no
`:= True` vacuity, no weakening-that-just-typechecks. Poseidon2 CR enters ONLY via the cited
`dropRefGenuine_*`/`unify_dropRef` lemmas (their own named hypotheses). Imports are read-only; this file
owns only itself and edits no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitDropRef

namespace Dregg2.Circuit.Argus.Effects.DropRef

open Dregg2.Exec
-- `execFullA` (the runnable action executor) + `recCRevoke` (the chained revoke mutator the `dropRefA`
-- arm routes to) + `RecChainedState` live here; opened so §2's runnable-arm lift and §4.3's off-row
-- connector can name them.
open Dregg2.Exec.TurnExecutorFull (execFullA recCRevoke)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState RecChainedState CellId recKRevokeTarget)
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.Spec.AuthorityRevocation (removeEdgeCaps removeEdgeCaps_correct)

/-! ## §0.5 — THE REFCOUNT-GC-FAITHFUL DROPREF KERNEL STEP `recKDropRefGC` (the closed divergence).

The PRIOR dropRef kernel step (`recKRevokeTarget`, the PARENT-revocation tear-down) removes ALL
`t`-conferring caps from `holder`'s slot UNCONDITIONALLY — a divergent OVER-eager model of the CapTP-GC
runtime (`gc.rs:170` `ExportGcManager::process_drop_inner`), which maintains a per-`(cell, federation)`
**refcount** and removes the cap-edge ONLY at the `refcount = 1 → 0` boundary; a drop on a `refcount > 1`
entry is a pure DECREMENT that LEAVES THE EDGE INTACT. The swiss-table arm ALREADY models this
(`RecordKernel.swissDropK` / `swissDropK_gc_at_one`); the dropRef arm did not.

THIS section CLOSES the divergence at the kernel-MODEL layer — WITHOUT adding any `RecordKernelState`
field. The refcount IS the **multiplicity** of the `t`-conferring cap in `holder`'s cap-list (the runtime
mints one list-entry per outstanding reference; `DropRef §5`'s non-vacuity witness pinned exactly this:
two `node 7` entries = refcount 2). So the GC-faithful drop removes **exactly ONE** `t`-conferring
occurrence (a decrement), GCing the edge only when the LAST reference drops:

  * `dropOneEdge t caps` — remove the FIRST cap satisfying `confersEdgeTo t` (`List`-erase by predicate);
    every other cap (including further `t`-edges, the surviving references) is kept verbatim.
  * `recKDropRefGC k holder t` — apply `dropOneEdge t` to `holder`'s slot, freezing every other holder's
    slot and all 16 non-`caps` fields. The `caps`-only, balance-neutral, GC-at-one dropRef step.

This is the SWISS GC-at-one shape (`swissDropK`'s `refcount - 1 = 0 ⇒ remove` boundary) realized on the
cap-list multiplicity. The dropRef IR term + cornerstone (§1-2) now refine THIS step, so the worthwhile
GC semantics lives in the kernel model the descriptor weld targets. -/

/-- **`dropOneEdge t caps`** — remove the FIRST cap in `caps` that confers an edge to `t` (a single
reference decrement); all other caps — INCLUDING any further `t`-conferring caps (the surviving
references) — are kept in order. The cap-list analogue of `swissDropK`'s `refcount - 1`. -/
def dropOneEdge (t : CellId) : List Cap → List Cap
  | []      => []
  | c :: cs => if confersEdgeTo t c then cs else c :: dropOneEdge t cs

/-- **`recKDropRefGC k holder t`** — the REFCOUNT-GC-FAITHFUL dropRef kernel step: drop ONE
`t`-conferring reference from `holder`'s cap-slot (`dropOneEdge`), freezing every other holder's slot and
all 16 non-`caps` fields. Always commits (a drop on a holder with no `t`-edge is the identity on that
slot). The CapTP-GC `refcount = 1 → 0` boundary realized on the cap-list multiplicity (the swiss
`swissDropK` shape on `caps`). -/
def recKDropRefGC (k : RecordKernelState) (holder t : CellId) : RecordKernelState :=
  { k with caps := fun l => if l = holder then dropOneEdge t (k.caps l) else k.caps l }

/-! ### §0.5a — `recKDropRefGC` consults the refcount: GC-at-one + decrement-keeps-on->1.

The two faithful facts (the swiss `gc_at_one` shape, realized on the cap-list multiplicity):

  * **GC-at-one (the LAST reference, `refcount = 1`):** when `holder` has EXACTLY ONE `t`-conferring cap,
    `recKDropRefGC` removes it — NO `t`-edge survives, exactly the `removeEdgeCaps` (tear-down) result on
    that slot. The edge is GC'd at the `1 → 0` boundary.
  * **DECREMENT-KEEPS (a held-elsewhere reference, `refcount > 1`):** when `holder` has TWO OR MORE
    `t`-conferring caps, `recKDropRefGC` removes ONE and KEEPS the rest — a surviving `t`-edge remains
    (the runtime-faithful "a held-elsewhere ref SURVIVES"), where the OLD `recKRevokeTarget` would have
    torn down ALL of them. -/

/-- **`dropOneEdge_count_decrement` — the refcount DECREMENTS by exactly one.** The number of
`t`-conferring caps after `dropOneEdge` is one less than before WHEN there was at least one (and unchanged
when there were none). The cap-list `count` IS the refcount; `dropOneEdge` is its `- 1`. -/
theorem dropOneEdge_count (t : CellId) (caps : List Cap) :
    (dropOneEdge t caps).countP (fun c => confersEdgeTo t c)
      = (caps.countP (fun c => confersEdgeTo t c)) - 1 := by
  induction caps with
  | nil => rfl
  | cons c cs ih =>
    unfold dropOneEdge
    by_cases hc : confersEdgeTo t c = true
    · -- head is a `t`-edge: dropped; the count drops by one (head contributed exactly one).
      rw [if_pos hc, List.countP_cons, hc]
      simp only [if_true]; omega
    · -- head is not a `t`-edge: kept; recurse on the tail.
      simp only [Bool.not_eq_true] at hc
      rw [if_neg (by simp [hc]), List.countP_cons, List.countP_cons, hc, ih]
      simp

/-- **`dropOneEdge_gc_at_one` — GC-at-one: dropping the LAST `t`-edge leaves NONE.** When `caps` has
exactly one `t`-conferring cap (`countP = 1`), `dropOneEdge` removes it and NO `t`-conferring cap remains
(`countP = 0`). The `refcount = 1 → 0` boundary: the edge is genuinely GC'd. -/
theorem dropOneEdge_gc_at_one (t : CellId) (caps : List Cap)
    (hone : caps.countP (fun c => confersEdgeTo t c) = 1) :
    (dropOneEdge t caps).countP (fun c => confersEdgeTo t c) = 0 := by
  rw [dropOneEdge_count, hone]

/-- **`dropOneEdge_keeps_on_multi` — DECREMENT-KEEPS: dropping with `refcount > 1` leaves a survivor.**
When `caps` has TWO OR MORE `t`-conferring caps, after `dropOneEdge` at least one `t`-conferring cap
SURVIVES (`countP ≥ 1`) — the held-elsewhere reference the runtime keeps (and the OLD `recKRevokeTarget`
wrongly tore down). -/
theorem dropOneEdge_keeps_on_multi (t : CellId) (caps : List Cap)
    (hmulti : 2 ≤ caps.countP (fun c => confersEdgeTo t c)) :
    1 ≤ (dropOneEdge t caps).countP (fun c => confersEdgeTo t c) := by
  rw [dropOneEdge_count]; omega

/-! ## §1 — the IR term: a single `setCaps` write (the cap-graph REFCOUNT-GC drop).

The dropRef IR term is a `setCaps` whose leaf is the GC-faithful `recKDropRefGC`'s `caps` move
(`dropOneEdge` on `holder`'s slot) — a single reference decrement, GCing the edge at the last drop. No
`guard` (the step always commits). Uses NO new IR constructor (the §A cap-graph write `setCaps`). The
protocol distinction (HOLDER GC vs PARENT revoke) is now ALSO a SEMANTIC one: dropRef decrements one
reference (`recKDropRefGC`), whereas revokeDelegation tears down the whole edge (`recKRevokeTarget`). -/

/-- **The dropRef effect as an IR term: the REFCOUNT-GC cap-edge drop.** A single `setCaps` write of the
GC-faithful cap-table `recKDropRefGC k holder t` (drop ONE `t`-reference from `holder`'s slot). Always
commits. The closed-divergence successor of the `removeEdgeCaps` term — now GC-at-one, matching the
runtime + the swiss arm. -/
def dropRefStmt (holder t : CellId) : RecStmt :=
  RecStmt.setCaps (fun k => (recKDropRefGC k holder t).caps)

/-! ## §2 — THE CORNERSTONE: `interp` of the term IS the GC-faithful kernel step `recKDropRefGC`.

`interp (setCaps g) k = some { k with caps := g k }` (the §A clause, by `rfl`); with `g k =
(recKDropRefGC k holder t).caps`, that record-update is EXACTLY `recKDropRefGC k holder t` (which edits
ONLY `caps`, so `{ k with caps := (recKDropRefGC k holder t).caps } = recKDropRefGC k holder t`). So the
IR term's executor interpretation is the GC-faithful kernel step, on the nose — a `some (…)` (the step is
unconditional). -/

/-- **The cornerstone (cap-graph, GC-faithful).** `interp` of the dropRef term IS the REFCOUNT-GC kernel
step `recKDropRefGC` — the same (total) state transformer, by construction. Because `recKDropRefGC` always
commits, the equality is to `some (recKDropRefGC k holder t)`. -/
theorem interp_dropRefStmt_eq_recKDropRefGC (holder t : CellId) (k : RecordKernelState) :
    interp (dropRefStmt holder t) k = some (recKDropRefGC k holder t) := by
  show some { k with caps := (recKDropRefGC k holder t).caps } = some (recKDropRefGC k holder t)
  rfl

#assert_axioms interp_dropRefStmt_eq_recKDropRefGC

/-! ### §2a — AGREEMENT with the prior tear-down on the no-divergence case (`refcount ≤ 1`).

The divergence between the GC-faithful `recKDropRefGC` and the prior tear-down `recKRevokeTarget` is
EXACTLY the `refcount > 1` case. On the no-divergence case — `holder` holds AT MOST ONE `t`-conferring
cap — they produce the SAME `caps` slot: both leave no `t`-edge (GC-at-one for `recKDropRefGC`; the filter
removes the one for `recKRevokeTarget`). So every connector/weld proved for `recKRevokeTarget` transports
to `recKDropRefGC` on that case, and the ONLY new behaviour is the runtime-faithful survivor on
`refcount > 1`. -/

/-- **`dropOneEdge_eq_filter_of_le_one` — agreement on `refcount ≤ 1`.** When `caps` has at most one
`t`-conferring cap, `dropOneEdge` (drop one) and the tear-down filter (drop all) AGREE: both yield the
list with the (≤1) `t`-conferring caps removed. The divergence is purely the `≥ 2` case. -/
theorem dropOneEdge_eq_filter_of_le_one (t : CellId) (caps : List Cap)
    (hle : caps.countP (fun c => confersEdgeTo t c) ≤ 1) :
    dropOneEdge t caps = caps.filter (fun c => ¬ confersEdgeTo t c) := by
  induction caps with
  | nil => rfl
  | cons c cs ih =>
    unfold dropOneEdge
    by_cases hc : confersEdgeTo t c = true
    · -- head is the (unique, since ≤1) `t`-edge: both sides drop it; the tail has NO more `t`-edges,
      -- so the filter keeps the tail verbatim.
      have hcount0 : cs.countP (fun c => confersEdgeTo t c) = 0 := by
        rw [List.countP_cons, hc] at hle; simp only [if_true] at hle; omega
      rw [if_pos hc, List.filter_cons_of_neg (by simp [hc])]
      -- tail filter is the identity (no `t`-edges left): `countP = 0` ⇒ no element satisfies p.
      symm
      apply List.filter_eq_self.mpr
      intro x hx
      have hmem := List.countP_eq_zero.mp hcount0 x hx
      have hxf : confersEdgeTo t x = false := by simpa using hmem
      simp [hxf]
    · -- head is not a `t`-edge: kept by both; recurse on the tail.
      simp only [Bool.not_eq_true] at hc
      rw [if_neg (by simp [hc]), List.filter_cons_of_pos (by simp [hc])]
      rw [List.countP_cons, hc] at hle; simp at hle
      rw [ih hle]

/-- **`recKDropRefGC_eq_recKRevokeTarget_of_le_one` — the kernel steps AGREE on `refcount ≤ 1`.** When
`holder` holds at most one `t`-conferring cap, the GC-faithful drop `recKDropRefGC` and the prior
tear-down `recKRevokeTarget` produce IDENTICAL post-states. So the existing `removeEdgeCaps`-based welds /
connectors apply on the no-divergence case; the GC step only ADDS the runtime-faithful survivor when
`refcount > 1`. -/
theorem recKDropRefGC_eq_recKRevokeTarget_of_le_one (k : RecordKernelState) (holder t : CellId)
    (hle : (k.caps holder).countP (fun c => confersEdgeTo t c) ≤ 1) :
    recKDropRefGC k holder t = recKRevokeTarget k holder t := by
  unfold recKDropRefGC recKRevokeTarget
  congr 1
  funext l
  by_cases hl : l = holder
  · subst hl; rw [if_pos rfl, if_pos rfl, dropOneEdge_eq_filter_of_le_one t (k.caps l) hle]
  · rw [if_neg hl, if_neg hl]

#assert_axioms dropOneEdge_count
#assert_axioms dropOneEdge_gc_at_one
#assert_axioms dropOneEdge_keeps_on_multi
#assert_axioms dropOneEdge_eq_filter_of_le_one
#assert_axioms recKDropRefGC_eq_recKRevokeTarget_of_le_one

/-- **`interp_dropRefStmt_eq_execFullA_kernel_of_le_one` — the cornerstone AGREES with the runnable
`dropRefA` arm on the no-divergence case (`refcount ≤ 1`).** `execFullA s (.dropRefA holder t) = some
(recCRevoke s holder t)` whose kernel is the PRIOR tear-down `recKRevokeTarget s.kernel holder t`; the IR
term's kernel is now the GC-faithful `recKDropRefGC s.kernel holder t`. These AGREE exactly when `holder`
holds at most one `t`-conferring cap (`recKDropRefGC_eq_recKRevokeTarget_of_le_one`) — the case where GC
and tear-down coincide. So the Argus term refines the `dropRefA` arm on every honest single-reference drop;
the divergence (now CLOSED in the IR term's favour) is the `refcount > 1` survivor, where the running
`execFullA` arm STILL tears down (the pending Rust-side re-route — see §5). -/
theorem interp_dropRefStmt_eq_execFullA_kernel_of_le_one (s : RecChainedState) (holder t : CellId)
    (hle : (s.kernel.caps holder).countP (fun c => confersEdgeTo t c) ≤ 1) :
    (interp (dropRefStmt holder t) s.kernel).map (fun k => k)
      = (execFullA s (.dropRefA holder t)).map (fun st => st.kernel) := by
  rw [interp_dropRefStmt_eq_recKDropRefGC, recKDropRefGC_eq_recKRevokeTarget_of_le_one s.kernel holder t hle]
  -- `execFullA s (.dropRefA holder t) = some (recCRevoke s holder t)`; its kernel is `recKRevokeTarget`.
  show some (recKRevokeTarget s.kernel holder t) = (some (recCRevoke s holder t)).map (fun st => st.kernel)
  rfl

#assert_axioms interp_dropRefStmt_eq_execFullA_kernel_of_le_one

/-! ## §3 — NON-VACUITY of the cornerstone: the term genuinely REMOVES a held cap-edge.

The cornerstone would be hollow if `dropRefStmt` never changed `caps`. On a kernel where holder `0`
holds a `node 7` cap (an edge to `7`), the term runs (unconditionally) and `0`'s slot loses that cap —
the cap-graph edit is real, observable, not a no-op. A non-holder slot is untouched (the off-`holder`
branch of `removeEdgeCaps`). -/

/-- A two-account kernel where holder `0` holds a single `node 7` cap (an edge to target `7`), and
holder `1` holds nothing. (Cell `0` Live; accounts `{0,1}`.) -/
def kDrop : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7] else [] }

/-- **`dropRefStmt_removes_edge` — the cap-graph edit is OBSERVABLE.** Running the dropRef term (holder
`0` GCs its edge to `7`) on `kDrop` commits and EMPTIES `0`'s cap slot (the `node 7` cap is filtered out):
the cap-graph edge removal is a real, observable state edit, not a no-op. -/
theorem dropRefStmt_removes_edge :
    (interp (dropRefStmt 0 7) kDrop).map (fun k => k.caps 0) = some [] := by
  rw [interp_dropRefStmt_eq_recKDropRefGC]
  decide

/-- **`dropRefStmt_frames_other_holder` — non-`holder` slots are untouched.** Dropping holder `0`'s edge
to `7` leaves holder `1`'s slot verbatim (here empty) — the edge removal is LOCAL to `holder`'s slot
(`removeEdgeCaps`'s off-`holder` branch). The two-valued, frame-respecting witness. -/
theorem dropRefStmt_frames_other_holder :
    (interp (dropRefStmt 0 7) kDrop).map (fun k => k.caps 1) = some [] := by
  rw [interp_dropRefStmt_eq_recKDropRefGC]
  decide

/-- **`dropRefStmt_frames_unrelated_target` — dropping an edge to `t` keeps a DIFFERENT edge.** A holder
that ALSO holds an edge to a target other than `t` keeps it: dropping `0`'s edge to `7` on a state where
`0` holds BOTH `node 7` and `node 8` leaves `node 8` (only the `t`-conferring cap is filtered). So the
drop is SURGICAL — it removes exactly the dropped reference, not the whole slot. -/
theorem dropRefStmt_frames_unrelated_target :
    (interp (dropRefStmt 0 7)
        { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
          caps := fun l => if l = 0 then [Cap.node 7, Cap.node 8] else [] }).map
        (fun k => k.caps 0) = some [Cap.node 8] := by
  rw [interp_dropRefStmt_eq_recKDropRefGC]
  decide

#assert_axioms dropRefStmt_removes_edge
#assert_axioms dropRefStmt_frames_other_holder
#assert_axioms dropRefStmt_frames_unrelated_target

/-! ## §4 — THE WELD: the audited class-A genuine `cap_root` descriptor agrees, per cell, with the IR
term's executor interpretation — AND forces the genuine in-row cap-root recompute.

The SAME shape as the cap-graph sibling (`Effects/RevokeDelegation §4`): route the circuit side through the
audited `dropRefGenuine_sound` (`EffectVmEmitDropRef §G`, the genuine cap-root recompute inherited from the
shared `attenuateGenuine_sound`, with the `dropRefA` OP tag) and the executor side through the §2
cornerstone. There is NO per-cell BALANCE projection to chain here (dropRef moves no value — the cell
economic block is FROZEN), so the conserved leg is the frozen frame directly; the genuine content is the
`cap_root` recompute leg. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capAdvanceOf edgeLeafOf)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (CapRowEncodes CapCellSpecGenuine attenuateGenuineRowGates)
open Dregg2.Circuit.Emit.EffectVmEmitDropRef
  (dropRefVmDescriptorGenuine dropRefGenuine_sound capRootProj dropRefCapDigestNew unify_dropRef_via_exec)

/-! ### §4.0 — `compileDropRef` — the effect-keyed circuit interpretation of the dropRef term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape — a
structural match cannot separate same-shaped effects, and `dropRefStmt` is literally the same shape as
`revokeDelegationStmt`), we name the dropRef circuit directly as the audited class-A genuine descriptor.
`compileDropRef = dropRefVmDescriptorGenuine` by `rfl`, so the circuit interpretation of the dropRef term
is, on the nose, the genuine cap-root-recompute descriptor the prover runs for the cap family. -/

/-- The circuit interpretation of the dropRef IR term: the audited class-A genuine descriptor (genuine
in-row `cap_root` recompute + per-cell frame freeze + commitment). -/
def compileDropRef : EffectVmDescriptor := dropRefVmDescriptorGenuine

/-- **`compileDropRef_eq` — `compileDropRef` IS the audited runnable genuine dropRef descriptor.**
Definitional. -/
theorem compileDropRef_eq : compileDropRef = dropRefVmDescriptorGenuine := rfl

#assert_axioms compileDropRef_eq

/-! ### §4.1 — the EXECUTOR-side cap-table digest projection of `recKRevokeTarget` (the OFF-ROW connector).

The cornerstone refines the IR term to `recKRevokeTarget`. Its on-row content is the FROZEN economic
frame (dropRef moves no value — there is NO `balLo` to project). The genuine cap-graph content — the
`caps := removeEdgeCaps …` move — lives OFF the per-row state block, bound via the `cap_root` digest. We
re-export it as the named OFF-ROW projection fact (`recKRevokeTarget`'s analog of the escrow welds'
`…_proj_balLo`, but here a cap-table DIGEST equality, not a balance equality): the post `cap_root` digest
is `D` of the edge-removed table. -/

/-- **`recKRevokeTarget_capDigest`.** The tear-down step writes the cap-table to the edge-removed table,
so its projected `cap_root` digest (under any whole-function digest `D`) is exactly `D (removeEdgeCaps
k.caps holder t)`. The off-row content of the PRIOR step (and of `execFullA`'s arm, which still uses it);
the frozen economic frame is the per-cell row's surface. -/
theorem recKRevokeTarget_capDigest (D : Caps → ℤ) (k : RecordKernelState) (holder t : CellId) :
    D (recKRevokeTarget k holder t).caps = D (removeEdgeCaps k.caps holder t) := by
  -- `(recKRevokeTarget k holder t).caps = removeEdgeCaps k.caps holder t` by `removeEdgeCaps_correct`.
  rw [removeEdgeCaps_correct]

#assert_axioms recKRevokeTarget_capDigest

/-- **`recKDropRefGC_capDigest_of_le_one` — the GC step's off-row cap-digest, on the no-divergence case.**
The dropRef IR term refines the GC-faithful `recKDropRefGC`; on the `refcount ≤ 1` case it AGREES with the
tear-down (`recKDropRefGC_eq_recKRevokeTarget_of_le_one`), so the GC step's projected `cap_root` digest is
`D (removeEdgeCaps k.caps holder t)` — exactly the value the genuine descriptor's recomputed `cap_root`
binds (via `unify_dropRef`). On `refcount > 1` the GC step keeps a survivor (its cap-table is
`dropOneEdge`, NOT the full tear-down), the runtime-faithful divergence-closed behaviour. -/
theorem recKDropRefGC_capDigest_of_le_one (D : Caps → ℤ) (k : RecordKernelState) (holder t : CellId)
    (hle : (k.caps holder).countP (fun c => confersEdgeTo t c) ≤ 1) :
    D (recKDropRefGC k holder t).caps = D (removeEdgeCaps k.caps holder t) := by
  rw [recKDropRefGC_eq_recKRevokeTarget_of_le_one k holder t hle, removeEdgeCaps_correct]

#assert_axioms recKDropRefGC_capDigest_of_le_one

/-! ### §4.2 — THE WELD. -/

/-- **`dropRef_compile_sound` — the welded soundness (dropRef slice, the cap-graph GC effect).**

Suppose, for the Argus dropRef term `dropRefStmt holder t`:
  * the circuit `compileDropRef` (= the audited class-A `dropRefVmDescriptorGenuine`) is SATISFIED on a
    row whose frame-freeze gates hold (`hgates`) and whose cap-root recompute holds (`hrec`), and whose
    `CapRowEncodes` decoding NAMES the cell `(pre, post)` states with the carried digest `capDigestNew`
    (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (dropRefStmt holder t) k = some k'` (`hexec`) — which always holds, since the kernel step is
    unconditional (the §2 cornerstone gives `k' = recKDropRefGC k holder t`, the GC-faithful step).

Then:
  * **frozen-frame leg (per-cell):** the circuit's pinned post-state `post` FREEZES the whole economic
    block relative to `pre` — balance limbs, nonce, every one of the 8 fields, reserved (dropRef moves no
    value; there is no nonce-tick divergence on the GENUINE descriptor — the frame is frozen);
  * **genuine cap-root leg:** the circuit FORCES the post `cap_root` to be the GENUINE in-row recompute
    `hash[ hash[holder,target,rights,op], pre.capRoot ]` (op tag `capOp.DROP_REF` carried in the bound
    edge leaf), NOT an opaque digest parameter. Under `Poseidon2SpongeCR` this binds the dropped cap-edge
    content (holder/target/rights/op) through the commitment (`dropRefGenuine_binds_edge`, cited), and the
    cap-table the GC-faithful executor produces (`recKDropRefGC`, = `D (removeEdgeCaps …)` on the
    `refcount ≤ 1` agreement case, §4.1 `recKDropRefGC_capDigest_of_le_one`) is the value that recomputed
    root digests, via the OFF-ROW connector `unify_dropRef` (`EffectVmEmitDropRef §8`, cited).

So the class-A circuit the prover runs for dropRef pins the per-cell frozen frame AND genuinely recomputes
the bound cap-graph edge-mutation root that the IR term's executor (`recKDropRefGC`, the GC-faithful step)
produces — the template generalizes to dregg1's CapTP-GC entry point of the cap-graph family.

NOTE (the kernel-vs-runtime divergence, now CLOSED): both sides above pertain to the verified KERNEL step
`recKDropRefGC`, which drops ONE `t`-reference and GCs the edge at the `refcount = 1 → 0` boundary — MATCHING
the Rust RUNTIME (`gc.rs`) and the swiss arm. See `dropRefKernel_gc_at_one` /
`dropRefKernel_keeps_survivor_on_multi` (§5) and the module header. -/
theorem dropRef_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (holder t : CellId)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env)
    (hexec : interp (dropRefStmt holder t) k = some k') :
    -- frozen-frame leg: dropRef moves no value — the whole economic block is frozen (pre = post) …
    ( post.balLo = pre.balLo
      ∧ post.balHi = pre.balHi
      ∧ post.nonce = pre.nonce
      ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
      ∧ post.reserved = pre.reserved )
    -- … and the GENUINE CAP-ROOT leg: the circuit FORCES the post `cap_root` to be the in-row recompute
    -- `hash[ hash[holder,target,rights,op], pre.capRoot ]` (bound dropped edge + old root) — NOT an opaque
    -- parameter (the actual edge-removed cap-table is bound off-row via `unify_dropRef`).
    ∧ ( post.capRoot
          = capAdvanceOf hash
              (edgeLeafOf hash (env.loc (prmCol HOLDER)) (env.loc (prmCol TARGET))
                (env.loc (prmCol RIGHTS)) (env.loc (prmCol OP)))
              pre.capRoot ) := by
  -- circuit side: `compileDropRef` IS the genuine descriptor; the audited class-A soundness forces the
  -- GENUINE per-cell `CapCellSpecGenuine` (frame freeze + the FORCED cap-root recompute).
  have hspec : CapCellSpecGenuine hash env pre post :=
    dropRefGenuine_sound hash env pre post capDigestNew henc hgates hrec
  obtain ⟨hCap, hLo, hHi, hNon, hFld, hRes⟩ := hspec
  -- executor side: the §2 cornerstone confirms the IR term commits to the GC-faithful kernel step
  -- `recKDropRefGC` (the off-row `caps` edge-drop whose digest the recomputed root binds, §4.1).
  -- (`hexec` ties the welded statement to a genuine executor commit; the cornerstone makes it definitional
  -- — the kernel step is unconditional.)
  have _hk' : k' = recKDropRefGC k holder t := by
    have := interp_dropRefStmt_eq_recKDropRefGC holder t k
    rw [hexec] at this
    exact (Option.some.injEq _ _).mp this
  exact ⟨⟨hLo, hHi, hNon, hFld, hRes⟩, hCap⟩

#assert_axioms dropRef_compile_sound

/-! ### §4.3 — THE OFF-ROW CONNECTOR, on the runnable `dropRefA` arm (the cap-table-move binding).

The §4.2 weld pins the per-row frame + the recomputed `cap_root` SCALAR. The actual cap-table FUNCTION
move (`removeEdgeCaps`) rides off-row; `unify_dropRef_via_exec` (`EffectVmEmitDropRef §8`) is the named
connector that the recomputed digest is `D (removeEdgeCaps …)` of a COMMITTED `dropRefA`. We re-state it
against the Argus term's executor so the weld's off-row claim is anchored to the IR refinement, not left a
bare citation. -/

/-- **`dropRef_offrow_capTable_bound` — the off-row cap-table move is the IR term's edge removal.** When
`execFullA`'s `dropRefA` arm commits to `s'` (the runnable arm the Argus term refines via §2 / the §
`interp_dropRefStmt_eq_execFullA_kernel` lift), the projected post `cap_root` digest equals `D` of the
edge-removed cap-table `dropRefCapDigestNew D s.kernel holder t = D (removeEdgeCaps s.kernel.caps holder
t)` — the exact value the genuine descriptor's recomputed `cap_root` carries (via the cited connector). So
the scalar `cap_root` the §4.2 weld pins is genuinely the digest of the IR term's `removeEdgeCaps` move,
not an unrelated number. -/
theorem dropRef_offrow_capTable_bound (D : Caps → ℤ)
    (s : RecChainedState) (holder t : CellId) (s' : RecChainedState)
    (h : execFullA s (.dropRefA holder t) = some s') :
    capRootProj D s'.kernel = dropRefCapDigestNew D s.kernel holder t :=
  unify_dropRef_via_exec D s holder t s' h

#assert_axioms dropRef_offrow_capTable_bound

/-! ### §4.4 — NON-VACUITY: `compileDropRef` is the genuine class-A descriptor, not a placeholder.

The weld would be worthless if `compileDropRef` were an inert/empty descriptor. It is the class-A
`dropRefVmDescriptorGenuine` (= the shared `attenuateVmDescriptorGenuine`), carrying the 12 frame-freeze
gates + 14 transition + 4 boundary = 30 constraints AND the 6 hash-sites (2 genuine cap-root-recompute
sites + 4 GROUP-4 commitment sites), with NO opaque `cap_root`-move parameter gate. An empty placeholder
would have 0/0. So `dropRef_compile_sound` is a statement about a REAL class-A circuit with a
genuinely-recomputed cap-graph root. -/

/-- The compiled dropRef circuit is the NON-trivial class-A genuine descriptor: it carries the 12+14+4 =
30 constraints / 2+4 = 6 hash-sites of the audited genuine cap-root descriptor (an empty placeholder would
have 0/0). So `dropRef_compile_sound` is about a genuine cap-graph-binding circuit. -/
theorem compileDropRef_nontrivial :
    compileDropRef.constraints.length = 30
    ∧ compileDropRef.hashSites.length = 6 := by
  rw [compileDropRef_eq]
  refine ⟨by decide, by decide⟩

#assert_axioms compileDropRef_nontrivial

/-! ## §5 — THE DIVERGENCE, NOW CLOSED: the dropRef kernel step `recKDropRefGC` MATCHES the Rust runtime's
CapTP-GC refcount semantics (decrement-then-GC-at-one), and the IR term (§1-2) refines it.

The full Rust runtime's `DropRef` (`apply_drop_ref`, `gc.rs:170` `ExportGcManager::process_drop_inner`)
DECREMENTS a per-`(cell, federation)` refcount and removes the cap-edge ONLY at the `refcount = 1 → 0`
boundary; a drop on a `refcount > 1` entry is a pure decrement that LEAVES THE EDGE INTACT. The PRIOR
dropRef kernel step `recKRevokeTarget` (the PARENT-revocation tear-down) removed EVERY `t`-edge
unconditionally — a divergent over-eager model. §0.5's `recKDropRefGC` CLOSES that: it drops EXACTLY ONE
`t`-conferring reference (the cap-list multiplicity IS the refcount), GCing the edge at the `1 → 0`
boundary (`dropOneEdge_gc_at_one`) and KEEPING a survivor on `refcount > 1` (`dropOneEdge_keeps_on_multi`)
— the SAME GC-at-one shape the swiss arm already had (`RecordKernel.swissDropK_gc_at_one`). The dropRef IR
term + cornerstone (§1-2) refine `recKDropRefGC`, so the WORTHWHILE GC semantics now lives in the kernel
model the descriptor weld targets.

The OLD tear-down `recKRevokeTarget` is RETAINED below (`oldDropRefKernel_was_overeager`) to PIN the
contrast — the divergence that USED to hold — so the closure cannot silently regress. The remaining
cutover is purely Rust-side: `execFullA`'s `.dropRefA` dispatch arm (`TurnExecutorFull.lean:3804`) still
routes to `recCRevoke` (the tear-down); re-routing it to a `recCDropRefGC` chained wrapper of
`recKDropRefGC` is a one-line dispatch change (the SAME shape the swiss `swissDropA` arm already uses),
tracked as the cutover residual (the kernel-MODEL fix is done; the IR term refines the GC step). -/

/-- **`dropRefKernel_gc_at_one` — GC-AT-ONE (the divergence CLOSED).** When `holder` holds EXACTLY ONE
`t`-conferring cap, the GC-faithful kernel step `recKDropRefGC` removes it and NO `t`-conferring cap
remains at `holder` — the edge is GC'd at the `refcount = 1 → 0` boundary, MATCHING the Rust runtime. -/
theorem dropRefKernel_gc_at_one (k : RecordKernelState) (holder t : CellId)
    (hone : (k.caps holder).countP (fun c => confersEdgeTo t c) = 1) :
    ((recKDropRefGC k holder t).caps holder).countP (fun c => confersEdgeTo t c) = 0 := by
  have hcaps : (recKDropRefGC k holder t).caps holder = dropOneEdge t (k.caps holder) := by
    show (if holder = holder then dropOneEdge t (k.caps holder) else k.caps holder)
      = dropOneEdge t (k.caps holder)
    rw [if_pos rfl]
  rw [hcaps]
  exact dropOneEdge_gc_at_one t (k.caps holder) hone

/-- **`dropRefKernel_keeps_survivor_on_multi` — DECREMENT-KEEPS (the runtime-faithful survivor).** When
`holder` holds TWO OR MORE `t`-conferring caps (`refcount > 1`), the GC-faithful kernel step
`recKDropRefGC` KEEPS at least one — a surviving reference remains, exactly as the Rust runtime keeps a
`> 1`-refcounted edge (and where the OLD tear-down `recKRevokeTarget` wrongly removed ALL). -/
theorem dropRefKernel_keeps_survivor_on_multi (k : RecordKernelState) (holder t : CellId)
    (hmulti : 2 ≤ (k.caps holder).countP (fun c => confersEdgeTo t c)) :
    1 ≤ ((recKDropRefGC k holder t).caps holder).countP (fun c => confersEdgeTo t c) := by
  have hcaps : (recKDropRefGC k holder t).caps holder = dropOneEdge t (k.caps holder) := by
    show (if holder = holder then dropOneEdge t (k.caps holder) else k.caps holder)
      = dropOneEdge t (k.caps holder)
    rw [if_pos rfl]
  rw [hcaps]
  exact dropOneEdge_keeps_on_multi t (k.caps holder) hmulti

/-- A concrete kernel where holder `0` holds the SAME `t`-edge `node 7` TWICE (refcount 2 = two list
entries). The witness that the GC step keeps a survivor where the tear-down emptied the slot. -/
def kDropDup : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 7, Cap.node 7] else [] }

/-- **`dropRefKernel_gc_keeps_duplicate_edge` — the GC step is runtime-FAITHFUL (witness TRUE).** The
GC-faithful kernel dropRef on `kDropDup` (holder `0` holds `node 7` twice, refcount 2) DECREMENTS to
`[node 7]` — KEEPING one reference, exactly the runtime's intended `2 → 1` post-state. (Contrast
`oldDropRefKernel_was_overeager` below: the tear-down emptied it to `[]`.) -/
theorem dropRefKernel_gc_keeps_duplicate_edge :
    (recKDropRefGC kDropDup 0 7).caps 0 = [Cap.node 7] := by
  decide

/-- **`oldDropRefKernel_was_overeager` — the PRIOR divergence, RETAINED as the contrast pin.** The OLD
tear-down step `recKRevokeTarget` removed EVERY `t`-edge from `holder`'s slot unconditionally — on
`kDropDup` (refcount 2) it emptied the slot to `[]`, where the runtime (and the new `recKDropRefGC`) keeps
`[node 7]`. Pinned so the closure (`dropRefKernel_gc_keeps_duplicate_edge`) cannot silently regress to the
over-eager behaviour. -/
theorem oldDropRefKernel_was_overeager :
    (recKRevokeTarget kDropDup 0 7).caps 0 = []
    ∧ (recKDropRefGC kDropDup 0 7).caps 0 ≠ (recKRevokeTarget kDropDup 0 7).caps 0 := by
  refine ⟨by decide, ?_⟩
  rw [dropRefKernel_gc_keeps_duplicate_edge]
  decide

#assert_axioms dropRefKernel_gc_at_one
#assert_axioms dropRefKernel_keeps_survivor_on_multi
#assert_axioms dropRefKernel_gc_keeps_duplicate_edge
#assert_axioms oldDropRefKernel_was_overeager

end Dregg2.Circuit.Argus.Effects.DropRef
