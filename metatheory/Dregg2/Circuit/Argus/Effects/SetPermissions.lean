/-
# Dregg2.Circuit.Argus.Effects.SetPermissions — the protocol-managed CELL-STATE-PERMISSIONS field-write
effect `setPermissionsA` welded into the Argus IR, as a FULL-STATE (`SetPermissionsSpec`, all 17 kernel
fields + log) weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it on
transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` welded a per-component effect to its genuine
standalone v2 `Surface2` descriptor (`balanceA_full_sound`); `Effects/CellSeal.lean` followed that stronger
full-state surface for the LIFECYCLE family, carrying the kernel-vs-runtime receipt-log divergence explicitly.
This module welds the genuinely DIFFERENT primitive `setPermissionsA` — a write of a CELL-RECORD FIELD (the
per-cell `permissions` slot), the protocol-managed-metadata regime — in a disjoint file (it imports the Argus
IR + the audited `setPermissionsA` instance + the independent permissions spec, all read-only, and owns only
its own declarations).

`setPermissionsA` is the permission-gate write (dregg1 `apply_set_permissions` ~`apply.rs:775`, applied LAST
off the ORIGINAL snapshot). The verified chained transition is `stateStep s permsField actor cell (.int p)`,
and `execFullA s (.setPermissionsA actor cell p) = stateStep s permsField actor cell (.int p)`
(`TurnExecutorFull.lean:3798`):

    stateStep s permsField actor cell (.int p)
      = if stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
           ∧ cellLive s.kernel cell = true then
          some { kernel := writeField s.kernel permsField cell (.int p),
                 log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
        else none

so a committed write (i) sets ONLY `cell`'s `permissions` record slot to `p` via `writeField` (= the
per-cell map `setPermsCellMap k cell p`; every OTHER cell whole, every OTHER RecordKernelState field FROZEN —
it is balance-NEUTRAL and cap-NEUTRAL: `SetPermissions` is `Neutral`), AND (ii) PREPENDS one self-targeted
receipt row onto the chain log. The admissibility gate is the THREE-LEG `stateStep` gate: `stateAuthB`
(self-authority over `cell`, the `SetPermissions` permission), `cell ∈ accounts` (MEMBERSHIP), and `cellLive`
(LIVENESS — the R6 gate; no write into a sealed/destroyed cell). Because the body writes a slot of the `cell`
RECORD, the IR move is the §A `setCell {cell}` component-write primitive over the leaf
`fun k c => setField permsField (k.cell c) (.int p)` — exactly the per-cell `setPermsCellMap`. That is the
structural contrast with cellSeal (`setLifecycle`) / balanceA (`setBal`): a `permissions`-slot record write.

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; `stateStep` is a
`RecChainedState → Option RecChainedState` step — it ALSO prepends a receipt row to the `log`, and the `log`
lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's `interp` cannot — and does not — emit
the log row; it captures EXACTLY the KERNEL side of the chained step (the `writeField` permissions write). This
is the SAME chained-vs-raw boundary `CellSeal`/`BalanceA` carry, here named precisely:

  * `interp (setPermissionsStmt actor cell p) k` produces the KERNEL post-state `writeField k permsField cell
    (.int p)`, gated on EXACTLY `stateStep`'s three-conjunct guard read on `k` (`interp_setPermissionsStmt_eq_kernel`).
  * lifting to the chained `execFullA` (`interp_setPermissionsStmt_chained`) re-attaches the runtime receipt
    row `permsReceipt actor cell :: s.log` — the runtime layer the kernel `interp` does not model. The welded
    conclusion (§4) then names the chained post-state `{ kernel := k', log := receipt :: s.log }` EXPLICITLY,
    so the receipt-log obligation is part of the welded statement (not papered).

## THE COLLAPSED-vs-FULL PERMISSIONS-STRUCT DIVERGENCE (carried explicitly — the effect-hint finding).

dregg1's `SetPermissions { cell, new_permissions }` binds a FULL 8-field permission struct (and the running
prover anchors `permissions_hash[0]` into `params[0]` and binds the full 8-limb digest via
`compute_effects_hash` — `circuit/src/effect_vm/trace.rs:577`, `air.rs:939-960`). The Lean kernel COLLAPSES
that struct to a SINGLE scalar `permissions : Int` slot `p` on the cell record. So this weld is over the
collapsed scalar surface: `interp`/the descriptor/the spec all speak about ONE `permissions` field set to `p`,
NOT the 8 component bits/the digest. This is an HONEST surface narrowing, not a soundness gap on the modelled
scalar — every theorem here is true of the collapsed model — but a re-widening to the 8-field struct + the
off-row `params[0]`/effects_hash digest binding is FUTURE work (the class-C gap noted in
`Emit/EffectVmEmitSetPermissions.lean`). The §4 weld carries this as the explicit `collapsedScalarSurface`
documentation conjunct's subject (named in the theorem docs + the §5 non-vacuity witness), so the divergence is
part of the welded statement's honesty, not buried.

## THE DESCRIPTOR — a GENUINE full-state v1 `EffectCommit`/`CommitSurface`, NOT EffectVM-inherited.

`setPermissionsA` carries its OWN standalone v1 `EffectCommit`/`CommitSurface` descriptor + full soundness
(`Dregg2/Circuit/Inst/setPermissionsA.lean`): `setPermissionsE` (the `EffectSpec` whose touched set is the
SINGLE cell `{cell}`, expected leaf `setPermsCellMap`, a growing log) and
`setPermissionsA_full_sound : satisfiedE … setPermissionsE … ⟹ SetPermissionsSpec` — a FULL 17-field
declarative post-state soundness (`Spec/cellstatepermissions.lean`'s `SetPermissionsSpec`: the `permissions`
slot set, the log grows by one receipt, every OTHER kernel field frozen), keyed on the CHAINED executor
`stateStep`/`execFullA` via the INDEPENDENT `execFullA_setPermissions_iff_spec` (executor ⟺ spec, BOTH
directions). This is the full-state surface (all 17 fields enumerated, no ghost field can be silently
mutated). NB it is the v1 `satisfiedE`/`CommitSurface` framework (single touched cell, `touchedCellMap` apex),
NOT the v2 `Surface2`/`satisfiedE2` whole-function-digest balanceA/cellSeal use — but it concludes the SAME
strength of full-state spec; the surface is honestly named `full-state-SetPermissionsSpec (v1 CommitSurface)`.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the cell-leaf /
rest-frame Poseidon-CR injectivity assumptions enter ONLY inside the reused `setPermissionsA_full_sound` (its
`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portals + the two `AccountsWF`
side-conditions), not in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState

namespace Dregg2.Circuit.Argus.Effects.SetPermissions

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
-- `stateAuthB`/`cellLive`/`writeField`/`setField`/`permsField` field-write engine names live in
-- `Dregg2.Exec.EffectsState` (`permsField` itself is in `TurnExecutorFull`, opened above). `Cap` (for the
-- `Cap.node` cap literals in the §5 fixtures) lives in `Dregg2.Authority`. (`open` is not transitive, so
-- these are named even though the Inst/Spec deps use them.)
open Dregg2.Exec.EffectsState (stateAuthB cellLive writeField setField fieldOf stateStep)
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Argus (RecStmt interp)
-- The independent full-state spec corner (executor ⟺ spec, both directions) + the spec + the cell-map helper.
open Dregg2.Circuit.Spec.CellStatePermissions
  (setPermsGuard SetPermissionsSpec setPermsCellMap execFullA_setPermissions_iff_spec
   setPermissions_cellWrite_correct)
-- The standalone v1 descriptor + its full soundness (the circuit ⟹ spec corner).
open Dregg2.Circuit.Inst.SetPermissionsA
  (SetPermissionsArgs setPermissionsE setPermissionsA_full_sound)
-- The v1 `EffectCommit`/`CommitSurface` circuit-side names (mirrors `Inst/setPermissionsA.lean`'s opens). The
-- digest-portal injectivity predicates + `AccountsWF` live in `StateCommit`; the circuit framework names
-- (`CommitSurface`/`satisfiedE`/`encodeE`) in `EffectCommit`.
open Dregg2.Circuit.StateCommit
  (logHashInjective AccountsWF compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE encodeE)

/-! ## §1 — The setPermissions effect as an Argus IR term (gate, then the `permissions`-slot record write).

`stateStep s permsField actor cell (.int p)`'s KERNEL side is `if <3-conjunct guard> then some (writeField k
permsField cell (.int p)) else none` (plus the runtime log prepend §3 carries). We capture the kernel side
term-for-term: a `Bool` `setPermsGuardB` of the EXACT 3 conjuncts, then a `setCell {cell}` whose leaf is
`fun k c => setField permsField (k.cell c) (.int p)` — which, on the singleton touched set, IS the per-cell
map `setPermsCellMap k cell p` (the post-`cell` map `stateStep`/`writeField` installs; the §2 cornerstone
proves the equality). The contrast with cellSeal/balanceA is the move primitive: `setCell` (rewrites the
per-cell record, here the `permissions` slot) over `setField permsField`, NOT `setLifecycle`/`setBal`. -/

/-- The setPermissions admissibility gate as a `Bool` — exactly `stateStep`'s `if` (the 3 conjuncts:
self-authority over `cell` via `stateAuthB` [the `SetPermissions` permission], `cell` is a live account via
membership, and `cell`'s lifecycle admits effects via `cellLive` [R6]). The self-targeted metadata gate. -/
def setPermsGuardB (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell && decide (cell ∈ k.accounts) && cellLive k cell

/-- **The setPermissions effect as an IR term: gate, then write the cell's `permissions` slot to `p`.**
Mirrors `transferStmt`/`cellSealStmt` (gate, then move) but the move is `setCell {cell}` over the
`permissions`-slot record write — `fun k c => setField permsField (k.cell c) (.int p)` — NOT `setLifecycle`
(cellSeal's) or `setBal` (balanceA's). On the singleton touched set this leaf IS `setPermsCellMap k cell p`,
EXACTLY the post-`cell` map `stateStep`/`writeField` installs on the kernel (the runtime receipt-log row is
re-attached in §3). The scalar `p : Int` is the COLLAPSED permissions surface — dregg1's 8-field struct
collapses to this one slot (the file-header divergence). -/
def setPermissionsStmt (actor cell : CellId) (p : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (setPermsGuardB actor cell))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k c => setField permsField (k.cell c) (.int p)))

/-! ## §2 — The cornerstone: `interp` of the setPermissions term IS the KERNEL side of `stateStep`. -/

/-- The setPermissions `Bool` gate decodes to `stateStep`'s admissibility proposition — exactly the three-leg
`setPermsGuard` (the SAME order the chained step's `if` checks them). The analog of
`transferGuard_iff`/`cellSealGuard_iff`. -/
theorem setPermsGuardB_iff (actor cell : CellId) (k : RecordKernelState) :
    setPermsGuardB actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true) := by
  simp only [setPermsGuardB, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {cell}` permissions-slot map IS `setPermsCellMap` (= `writeField`'s post-`cell` map). On the
singleton touched set `{cell}`, `c ∈ {cell} ↔ c = cell`, so the `setCell` map `fun c => if c ∈ {cell} then
setField permsField (k.cell c) (.int p) else k.cell c` is exactly `setPermsCellMap k cell p`. The per-cell
analog of `transferCellMap_eq`/`creditCellMap_eq` for the `permissions`-slot write. -/
theorem setPermsCellMap_eq (cell : CellId) (p : Int) (k : RecordKernelState) :
    (fun c => if c ∈ ({cell} : Finset CellId) then setField permsField (k.cell c) (.int p) else k.cell c)
      = setPermsCellMap k cell p := by
  funext c
  unfold setPermsCellMap
  by_cases h : c = cell
  · simp [h]
  · simp [Finset.mem_singleton, h]

/-- **The cornerstone (kernel-side permissions write).** `interp` of the setPermissions term IS the KERNEL
side of the verified chained transition `stateStep s permsField actor cell (.int p)` — on the same 3-conjunct
guard, the term commits to exactly the kernel state `writeField k permsField cell (.int p)` the chained step
installs (via `setPermsCellMap = writeField.cell`), and rejects on exactly the same gate. This is the
per-effect executor-refinement for the protocol-managed-METADATA family, over the genuine `permissions` record
slot via `setCell`/`setField permsField` (NOT the record-cell-balance `setCell`/`recTransfer`, nor
`setLifecycle`/`setBal`). The runtime receipt-log prepend is re-attached in §3 (the kernel-vs-runtime
divergence this file carries). -/
theorem interp_setPermissionsStmt_eq_kernel (actor cell : CellId) (p : Int) (k : RecordKernelState) :
    interp (setPermissionsStmt actor cell p) k
      = if setPermsGuardB actor cell k = true
        then some (writeField k permsField cell (.int p)) else none := by
  simp only [setPermissionsStmt, interp]
  by_cases hg : setPermsGuardB actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setCell {cell}` move installs the per-cell map, which
    -- IS `setPermsCellMap k cell p`, i.e. the `cell` field of `writeField k permsField cell (.int p)`.
    rw [if_pos hg, if_pos hg]
    simp only [Option.bind]
    rw [setPermsCellMap_eq]
    -- the kernel post-state `{ k with cell := setPermsCellMap k cell p }` is `writeField k permsField cell
    -- (.int p)` (same record update; `writeField`'s `cell` field equals `setPermsCellMap` by definition).
    rfl
  · -- REJECT: the guard fails ⇒ `none.bind _ = none` on the LHS, `else none` on the RHS.
    rw [if_neg hg, if_neg hg]
    simp only [Option.bind]

#assert_axioms interp_setPermissionsStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `stateStep` / `execFullA`.

The standalone setPermissions descriptor (§4) is keyed on the CHAINED executor `stateStep` / `execFullA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.setPermissionsA actor cell p) = stateStep s
permsField actor cell (.int p)`. The §2 cornerstone is over the KERNEL side only. The chained layer is exactly
the §2 kernel write PLUS the runtime receipt-log prepend `permsReceipt actor cell :: s.log` — the runtime
piece the `RecordKernelState`-level `interp` structurally cannot emit. We bridge faithfully, naming the
receipt-row prepend EXPLICITLY in the chained post-state (the honest kernel-vs-runtime divergence — NOT
papered). -/

/-- The runtime receipt row a committed `setPermissionsA` prepends: one self-targeted (`src = dst = cell`),
zero-amount metadata-advance row, EXACTLY the row `stateStep`/`SetPermissionsSpec` install. -/
def permsReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`interp_setPermissionsStmt_chained` — the IR term's KERNEL executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (setPermissionsStmt actor cell p) s.kernel = some k'`),
the unified action executor `execFullA s (.setPermissionsA actor cell p)` commits to the chained state
`⟨k', permsReceipt actor cell :: s.log⟩`. So the Argus term's KERNEL meaning lifts to the chained executor the
standalone descriptor speaks about, with the runtime receipt-log row (which the kernel `interp` does not model)
re-attached HERE — the explicit kernel-vs-runtime bridge. -/
theorem interp_setPermissionsStmt_chained
    (s : RecChainedState) (actor cell : CellId) (p : Int) (k' : RecordKernelState)
    (hexec : interp (setPermissionsStmt actor cell p) s.kernel = some k') :
    execFullA s (.setPermissionsA actor cell p)
      = some { kernel := k', log := permsReceipt actor cell :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel-side write, gated on `setPermsGuardB`.
  rw [interp_setPermissionsStmt_eq_kernel] at hexec
  -- `execFullA s (.setPermissionsA actor cell p)` reduces to `stateStep s permsField actor cell (.int p)`.
  -- Open BOTH on the same guard (its decoded 3-conjunct IS `stateStep`'s `if` condition).
  show stateStep s permsField actor cell (.int p)
      = some { kernel := k', log := permsReceipt actor cell :: s.log }
  unfold stateStep
  by_cases hg : setPermsGuardB actor cell s.kernel = true
  · -- ADMIT: `hexec` names `k' = writeField s.kernel permsField cell (.int p)`; the chained step commits to
    -- that kernel + the receipt-row prepend, which is `permsReceipt actor cell :: s.log` by definition.
    rw [if_pos hg] at hexec
    rw [if_pos ((setPermsGuardB_iff actor cell s.kernel).mp hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- REJECT: contradictory — `hexec` would equate `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_setPermissionsStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of setPermissions' OWN standalone full-state circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against setPermissions' GENUINE standalone descriptor `setPermissionsCircuit S setPermissionsE`
(the v1 `EffectCommit`/`CommitSurface` circuit whose soundness is `setPermissionsA_full_sound`), NOT an
EffectVM `cellProj` row — see the descriptor note in this file's header. The executor side is routed through §3
(`interp` ⟹ `execFullA`) and the independent `execFullA_setPermissions_iff_spec` (executor ⟺
`SetPermissionsSpec`); the circuit side is the audited `setPermissionsA_full_sound` (circuit ⟹
`SetPermissionsSpec`). Both name the SAME `SetPermissionsSpec`, so they PROVABLY agree on the WHOLE 17-field
state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `setPermissions` term: setPermissions' OWN audited standalone v1
`CommitSurface` circuit step — the full-state arithmetization `satisfiedE S setPermissionsE (encodeE …)`
satisfied on the encoded `(s, ⟨actor,cell,p⟩, s')` triple. Its soundness `setPermissionsA_full_sound` pins the
complete `SetPermissionsSpec`. The `setPermissions`-keyed analog of `cellSealCircuit`/`balanceACircuit`, in the
descriptor universe where setPermissions carries its OWN genuine full-state circuit (NOT EffectVM-inherited). -/
def setPermissionsCircuit (S : CommitSurface) (s : RecChainedState) (args : SetPermissionsArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE S setPermissionsE (encodeE S setPermissionsE s args s')

/-- **`setPermissionsSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`SetPermissionsSpec s actor cell p ·` are equal. Rather than re-derive this field-by-field, we route through
the PROVEN executor⟺spec corner `execFullA_setPermissions_iff_spec`: each `SetPermissionsSpec` reconstructs the
SAME committed value `execFullA s (.setPermissionsA actor cell p) = some ·`, and `some` is injective. This is
exactly the sense in which `SetPermissionsSpec` is functional — it determines the post-state — so the
circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem setPermissionsSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId} {p : Int}
    (h₁ : SetPermissionsSpec s actor cell p s₁) (h₂ : SetPermissionsSpec s actor cell p s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.setPermissionsA actor cell p) = some s₁ :=
    (execFullA_setPermissions_iff_spec s actor cell p s₁).mpr h₁
  have e₂ : execFullA s (.setPermissionsA actor cell p) = some s₂ :=
    (execFullA_setPermissions_iff_spec s actor cell p s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`setPermissions_compile_sound` — the welded soundness (setPermissions slice), against setPermissions'
OWN descriptor.**

Suppose, for the Argus setPermissions term `setPermissionsStmt actor cell p`:
  * the standalone setPermissions circuit `setPermissionsCircuit S s ⟨actor,cell,p⟩ s'` (= `setPermissionsE`'s
    full-state v1 arithmetization satisfied on the encoded triple) holds, under the realizable digest portals
    (`hN : compressNInjective S.compressN`, `hL : cellLeafInjective S.CH`, `hRest : RestHashIffFrame S.RH`,
    `hLog : logHashInjective S.LH`) and the two account well-formedness side-conditions
    (`hwf : AccountsWF s.kernel`, `hwf' : AccountsWF s'.kernel`);
  * the IR term's KERNEL executor interpretation COMMITS: `interp (setPermissionsStmt actor cell p) s.kernel =
    some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor produces
once the runtime receipt-row is re-attached: `s' = { kernel := k', log := permsReceipt actor cell :: s.log }`.
I.e. setPermissions' OWN circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (the
`permissions` slot of `cell` set to `p` by `writeField`/`setPermsCellMap`, every other field frozen — the
balance-NEUTRAL, cap-NEUTRAL metadata regime) AND the receipt log — the full `SetPermissionsSpec`, not a
per-cell projection. The receipt-log row is named EXPLICITLY in the conclusion, so the kernel-vs-runtime
divergence is part of the welded statement. (The COLLAPSED-vs-FULL permissions-struct divergence — the file
header's `collapsedScalarSurface` — is honestly carried: `p` is the scalar collapse of dregg1's 8-field
struct; this weld is sound on that collapsed surface.) So the circuit the prover runs for setPermissions pins
the complete chained state the IR term's executor produces. -/
theorem setPermissions_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (p : Int) (k' : RecordKernelState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hcirc : setPermissionsCircuit S s ⟨actor, cell, p⟩ s')
    (hexec : interp (setPermissionsStmt actor cell p) s.kernel = some k') :
    s' = { kernel := k', log := permsReceipt actor cell :: s.log } := by
  -- circuit side: setPermissions' OWN audited soundness forces the FULL `SetPermissionsSpec` on
  -- `(s, ⟨actor,cell,p⟩, s')`.
  have hspec : SetPermissionsSpec s actor cell p s' :=
    setPermissionsA_full_sound S hN hL hRest hLog s ⟨actor, cell, p⟩ s' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.setPermissionsA actor cell p) = some
  -- ⟨k', receipt::log⟩`, and the independent executor⟺spec corner turns THAT into
  -- `SetPermissionsSpec s actor cell p ⟨k', receipt::log⟩`.
  have hspec' : SetPermissionsSpec s actor cell p { kernel := k', log := permsReceipt actor cell :: s.log } :=
    (execFullA_setPermissions_iff_spec s actor cell p _).mp
      (interp_setPermissionsStmt_chained s actor cell p k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact setPermissionsSpec_unique hspec hspec'

#assert_axioms setPermissions_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely WRITES the permissions slot (write observable), preserves every
other field (balance/cap/lifecycle frame), and the gate REJECTS forged / non-account / non-Live inputs
(fail-closed).

The cornerstone/weld would be hollow if setPermissions never committed, if the write were a no-op, or if the
gate admitted everything. A concrete two-cell kernel `kP0` (cell 0 Live, actor 0 owns it by `Cap.node 0`)
exercises a real write; the rejection lemmas show each guard leg fails closed. -/

/-- A two-cell kernel for the §5 witnesses: cells 0 and 1 live accounts (lifecycle defaults to Live `0`), cell
0 owned by actor 0 via `Cap.node 0` (so `stateAuthB ... 0 0` holds), holding `permissions := 1` initially. -/
def kP0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0), ("permissions", .int 1)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
    bal := fun _ _ => 0 }

/-- **NON-VACUITY (the WRITE is OBSERVABLE — the collapsed scalar surface).** The committed write sets cell
`0`'s `permissions` slot from `1` to `7` — the metadata genuinely changes (the `setCell`/`setField permsField`
write is real, not a no-op). This exercises the COLLAPSED scalar permissions surface (one `Int` slot, dregg1's
8-field struct collapsed): a fresh value `7` lands and reads back. -/
theorem setPermissionsStmt_writes :
    (interp (setPermissionsStmt 0 0 7) kP0).map (fun k => fieldOf permsField (k.cell 0)) = some 7 := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the cell ACTUALLY commits).** The write to a Live, self-owned cell COMMITS (`isSome`) — the
3-conjunct gate genuinely admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem setPermissionsStmt_commits :
    (interp (setPermissionsStmt 0 0 7) kP0).isSome = true := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: `balance` is untouched — the balance-NEUTRAL regime).** Setting cell `0`'s
permissions leaves cell `0`'s `balance` slot at `0` — `setField permsField` writes ONLY the `permissions`
slot, never `balance` (the DISTINCT-slot non-interference `setPermissions_cellWrite_correct` proves). No value
is conjured by a metadata write. -/
theorem setPermissionsStmt_balance_frozen :
    (interp (setPermissionsStmt 0 0 7) kP0).map (fun k => fieldOf "balance" (k.cell 0)) = some 0 := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Setting cell `0`'s permissions leaves cell `1`'s
`permissions` at its initial `1` — `setCell {0}` rewrites ONLY cell `0`'s record, confirming the write is
local (not a global permissions collapse). The per-cell frame the full-state `SetPermissionsSpec` pins,
observed. -/
theorem setPermissionsStmt_other_cell_untouched :
    (interp (setPermissionsStmt 0 0 7) kP0).map (fun k => fieldOf permsField (k.cell 1)) = some 1 := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: the cap-graph is untouched — no authority amplification).** Setting cell `0`'s
permissions leaves cell `0`'s cap list at `[Cap.node 0, Cap.node 1]` — a `permissions`-SLOT record write is
distinct from the kernel cap table, so it edits NO capability (the cap-NEUTRAL leg of `SetPermissionsSpec`). A
metadata write cannot grant authority. -/
theorem setPermissionsStmt_caps_frozen :
    (interp (setPermissionsStmt 0 0 7) kP0).map (fun k => k.caps 0) = some [Cap.node 0, Cap.node 1] := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A write attempted by actor `5`, who holds NO authority over
cell `0` (empty cap list), does NOT commit — the term returns `none` (the `stateAuthB` self-authority leg of
the gate fails). A stranger cannot rewrite a cell's permissions. -/
theorem setPermissionsStmt_rejects_unauthorized :
    interp (setPermissionsStmt 5 0 7) kP0 = none := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: non-account target).** A write into cell `5`, which is NOT a live account
(`5 ∉ {0,1}`), does NOT commit — the term returns `none` (the MEMBERSHIP leg fails). -/
theorem setPermissionsStmt_rejects_nonaccount :
    interp (setPermissionsStmt 5 5 7) kP0 = none := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: non-Live cell — R6).** A write into a cell that is NOT Live (lifecycle `1` =
Sealed) does NOT commit — the term returns `none` (the `cellLive` LIVENESS leg fails; the R6 gate). A sealed
cell's permissions cannot be rewritten. -/
theorem setPermissionsStmt_rejects_nonlive :
    interp (setPermissionsStmt 0 0 7) { kP0 with lifecycle := fun _ => 1 } = none := by
  rw [interp_setPermissionsStmt_eq_kernel]
  decide

#assert_axioms setPermissionsStmt_writes
#assert_axioms setPermissionsStmt_commits
#assert_axioms setPermissionsStmt_balance_frozen
#assert_axioms setPermissionsStmt_other_cell_untouched
#assert_axioms setPermissionsStmt_caps_frozen
#assert_axioms setPermissionsStmt_rejects_unauthorized
#assert_axioms setPermissionsStmt_rejects_nonaccount
#assert_axioms setPermissionsStmt_rejects_nonlive

end Dregg2.Circuit.Argus.Effects.SetPermissions
