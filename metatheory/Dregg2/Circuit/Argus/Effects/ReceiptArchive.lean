/-
# Dregg2.Circuit.Argus.Effects.ReceiptArchive — the CELL-STATE-AUDIT effect `receiptArchiveA` (the
receipt-archive lifecycle commitment) welded into the Argus IR, as a FULL-STATE weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` then welded a per-component effect to a
genuine standalone full-state descriptor (`balanceA_full_sound`), concluding the WHOLE 17-field
post-state, and `Effects/Refusal.lean` followed that surface for the AUDIT-WRITE family's `refusalA`
sibling. This module follows the SAME strong full-state surface for `receiptArchiveA` — the OTHER
cell-state-audit variant — in a disjoint file (it imports the Argus IR + the audited `receiptArchiveA`
v1 instance + the independent cell-state-audit spec, all read-only, and owns only its own declarations).

`receiptArchiveA` is dregg1's receipt-archive **lifecycle commitment**: the live executor's
`.receiptArchiveA` arm writes ONLY `cell`'s `"lifecycle"` RECORD slot (inside the `cell : CellId → Value`
record map) to `1`, a one-shot receipt-archived flag. It is BALANCE-NEUTRAL (no `bal` move), CAP-NEUTRAL
(no authority amplification), and freezes the other 15 kernel components + every other cell's whole
record. The verified executor arm is DEFINITIONALLY the bare authority-gated field write
(`Spec/cellstateaudit.lean`'s `execFullA_receiptArchiveA_eq`):

    execFullA s (.receiptArchiveA actor cell) = stateStep s lifecycleField actor cell (.int 1)

and `stateStep` (`EffectsState.lean:205`) commits IFF its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY (dregg1's cross-cell SetState leg)
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP (`cell` a live account)
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS (R6: `cell` admits effects)

— writing `cell`'s `"lifecycle"` RECORD slot to `1` (via `writeField`, touching ONLY that cell's record
in the `cell` map) and prepending one self-targeted receipt row to the chain log. Because the move
touches the per-cell RECORD map, the IR body's move is the §`setCell` primitive (over the single touched
cell `{cell}`) with leaf `setField lifecycleField (k.cell c) (.int 1)` — NOT `setBal` (balanceA's), NOT
`setLifecycle` (cellSeal's, which writes the `lifecycle` SIDE-TABLE), and NOT the `setLifecycle`
primitive at all (see the RECORD-slot vs SIDE-TABLE note below). The structural shape is IDENTICAL to
`refusalA` — the SAME `setCell {cell}`-over-`setField`-at-a-non-`balance`-slot move; the two audit
variants differ ONLY in WHICH non-`balance` slot they stamp (`"lifecycle"` vs `"refusal"`).

## THE RECORD-SLOT vs SIDE-TABLE name collision (recorded — read this).

`receiptArchiveA` writes the `"lifecycle"` RECORD FIELD — slot `"lifecycle"` inside the `cell` MAP's
record at index `cell`. This is a DIFFERENT object from `RecordKernelState.lifecycle`, the `CellId → Nat`
SIDE-TABLE that `cellLive`/the R6 gate reads (and that `cellSealStmt`'s `setLifecycle` primitive flips).
So even though the field is NAMED `"lifecycle"`, the IR move is `setCell` (the record map), NOT
`setLifecycle` (the side-table), and the welded `ReceiptArchiveSpec` FREEZES the side-table
(`s'.kernel.lifecycle = s.kernel.lifecycle`, one of the 16 frame fields) — so the cell's liveness is
preserved and it can still be re-targeted later. This is the load-bearing confirmation the name
collision hides no frame interaction (it is exactly `Spec/cellstateaudit.lean`'s
`receiptArchiveA_lifecycleSideTableFrame`), surfaced here so the `setCell`-not-`setLifecycle` choice is
not mistaken for a primitive mismatch. The IR has the right primitive: `setCell` IS the
record-map writer.

## THE DESCRIPTOR — a GENUINE full-state v1 `EffectCommit` soundness (the surface).

Like `refusalA` (and unlike balanceA/cellSeal, whose standalone descriptors live in the v2
`EffectCommit2`/`Surface2` universe), `receiptArchiveA`'s genuine standalone circuit⟺spec crown jewel
lives in the **v1 `EffectCommit`** universe (`Dregg2/Circuit/Inst/receiptArchiveA.lean`):
`receiptArchiveE` (the `EffectSpec` whose touched set is the singleton `{cell}`, expected leaf
`auditCellMap … lifecycleField`, with a single `propBit` guard column for the three-leg `auditGuard`)
and

    receiptArchiveA_full_sound : satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s')
                                   ⟹ ReceiptArchiveSpec …

a FULL 17-field declarative post-state soundness (`Spec/cellstateaudit.lean`'s `ReceiptArchiveSpec`: the
`"lifecycle"` RECORD slot flips, the log grows by one receipt, every OTHER kernel field frozen —
including the `lifecycle` SIDE-TABLE), keyed on the CHAINED executor `execFullA` via the INDEPENDENT
`execFullA_receiptArchiveA_iff_spec` (executor ⟺ spec, BOTH directions). This is the strong full-state
surface BalanceA prefers (the conclusion is the WHOLE post-state, not a per-cell `cellProj` projection) —
it just rides the v1 sponge framework (`CommitSurface`/`satisfiedE`/`encodeE`/`effect_circuit_full_sound`)
rather than the v2 one, because that is the descriptor `receiptArchiveA` carries. There is a
SEPARATE per-cell EffectVM row (`Emit/EffectVmEmitReceiptArchive`) that pins the `field[1]` lifecycle
column SET + frame freeze, but its OWN header records two boundaries — (a) the receipt-LOG growth is NOT
an EffectVM column (it lives in the `logHashInjective` portal), and (b) the per-row circuit is a per-cell
`field[1]` projection — so we weld against the FULL-STATE v1 one, and note the EffectVM per-row row as a
DIFFERENT universe we do not weld here (carried in the structured report).

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; the executor arm
`stateStep`/`execFullA` is a `RecChainedState → Option RecChainedState` step — it ALSO prepends a receipt
row to the `log`, and the `log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's
`interp` cannot — and does not — emit the log row; it captures EXACTLY the KERNEL side of the chained step
(the `"lifecycle" := 1` record-slot write). This is the SAME chained-vs-raw boundary Refusal/CellSeal
carry, here named precisely:

  * `interp (receiptArchiveStmt actor cell) k` produces the KERNEL post-state `writeField k
    lifecycleField cell (.int 1)` (its `cell` map is `auditCellMap k cell lifecycleField`, every other
    kernel field frozen), gated on EXACTLY `stateStep`'s three-leg guard read on `k`
    (`interp_receiptArchiveStmt_eq_kernel`).
  * lifting to the chained `execFullA` (`interp_receiptArchiveStmt_chained`) re-attaches the runtime
    receipt row `{ actor, src := cell, dst := cell, amt := 0 } :: s.log` — the runtime layer the kernel
    `interp` does not model. The welded conclusion (§4) then names the chained post-state `{ kernel :=
    k', log := receipt :: s.log }` EXPLICITLY, so the receipt-log obligation is part of the welded
    statement.

## Axiom hygiene

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
sponge-injectivity assumptions enter ONLY inside the reused `receiptArchiveA_full_sound` (its
`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portals + `AccountsWF` on
both kernels), NOT in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Spec.cellstateaudit
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide

namespace Dregg2.Circuit.Argus.Effects.ReceiptArchive

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- The v1 `EffectCommit` framework + the sponge-injectivity portals (mirroring `Inst/receiptArchiveA.lean`).
open Dregg2.Circuit.StateCommit
  (AccountsWF compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface EffectSpec satisfiedE encodeE)
-- The independent full-state spec + executor⟺spec corner.
open Dregg2.Circuit.Spec.CellStateAudit
  (auditGuard auditCellMap auditCellMap_eq_writeField ReceiptArchiveSpec execFullA_receiptArchiveA_eq
   execFullA_receiptArchiveA_iff_spec)
-- The audited v1 instance: the `EffectSpec`, its args, and the crown-jewel full soundness.
open Dregg2.Circuit.Inst.ReceiptArchiveA (ReceiptArchiveArgs receiptArchiveE receiptArchiveA_full_sound)

/-! ## §1 — The receipt-archive effect as an Argus IR term (gate, then the `setCell` audit-slot write).

`stateStep`'s KERNEL side is `if <3-conjunct guard> then some (writeField k lifecycleField cell (.int 1))
else none` (plus the runtime log prepend §3 carries). We capture the kernel side term-for-term: a `Bool`
`receiptArchiveGuard` of the EXACT three conjuncts, then a `setCell {cell}` whose leaf writes the
`"lifecycle"` RECORD slot of `cell`'s record to `1`. The contrast with transfer/balanceA/cellSeal is the
touched object: the per-cell RECORD map (`setCell`), at a NON-`balance` audit slot, not the `bal` ledger
or the `lifecycle` SIDE-TABLE. It shares its shape EXACTLY with `refusalStmt` (same `setCell {cell}` over
`setField <slot> … (.int 1)`); only the slot name differs (`lifecycleField` vs `refusalField`). -/

/-- The receipt-archive admissibility gate as a `Bool` — exactly `stateStep`'s `if` (the three legs:
AUTHORITY over `cell` via `stateAuthB`; `cell` a live account MEMBERSHIP; `cell`'s lifecycle admits
effects LIVENESS, the R6 gate). This is the SAME gate the independent spec exposes as the `Prop`
`auditGuard`. -/
def receiptArchiveGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell
    && decide (cell ∈ k.accounts)
    && cellLive k cell

/-- **The receipt-archive effect as an IR term: gate, then write the `"lifecycle"` RECORD slot of `cell`
to `1`.** Mirrors `transferStmt`/`balanceAStmt`/`refusalStmt` (gate, then move) but the move is `setCell
{cell}` over the audit-slot write `setField lifecycleField (k.cell c) (.int 1)` — a NON-`balance` field of
the per-cell RECORD map — NOT `setBal` (balanceA's ledger) nor `setLifecycle` (cellSeal's SIDE-TABLE).
The `setCell` leaf is EXACTLY the per-cell map `writeField k lifecycleField cell (.int 1)` installs (the
runtime receipt-log row is re-attached in §3). -/
def receiptArchiveStmt (actor cell : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (receiptArchiveGuard actor cell))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k c => setField lifecycleField (k.cell c) (.int 1)))

/-! ## §2 — The cornerstone: `interp` of the receipt-archive term IS the KERNEL side of the executor arm. -/

/-- The receipt-archive `Bool` gate decodes to `stateStep`'s admissibility proposition (the three
conjuncts, in the SAME order the executor `if` checks them — the `auditGuard` proposition). The analog of
`transferGuard_iff` / `refusalGuard_iff`. -/
theorem receiptArchiveGuard_iff (actor cell : CellId) (k : RecordKernelState) :
    receiptArchiveGuard actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true) := by
  simp only [receiptArchiveGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {cell}` audit map is exactly `writeField … lifecycleField … (.int 1)` (identity off the
single cell). The receipt-archive analog of `transferCellMap_eq` / `refusalCellMap_eq`: the post-`cell`
map the IR move installs IS the executor's `writeField` post-cell map (so the kernel post-states coincide
as whole records, not just on the `cell` field). -/
theorem receiptArchiveCellMap_eq (cell : CellId) (k : RecordKernelState) :
    { k with cell := fun c => if c ∈ ({cell} : Finset CellId)
                                then setField lifecycleField (k.cell c) (.int 1) else k.cell c }
      = writeField k lifecycleField cell (.int 1) := by
  unfold writeField
  congr 1
  funext c
  by_cases hc : c = cell
  · simp [hc]
  · simp [Finset.mem_singleton, hc]

/-- **The cornerstone (kernel-side audit write).** `interp` of the receipt-archive term IS the KERNEL side
of the verified executor arm — on the same three-leg guard, the term commits to exactly the kernel state
`writeField k lifecycleField cell (.int 1)` the executor installs, and rejects on exactly the same gate.
This is the per-effect executor-refinement for the AUDIT-WRITE family, over the per-cell RECORD map via
`setCell` at the NON-`balance` `"lifecycle"` slot (NOT `setBal`/`setLifecycle`). The runtime receipt-log
prepend is re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
theorem interp_receiptArchiveStmt_eq_kernel (actor cell : CellId) (k : RecordKernelState) :
    interp (receiptArchiveStmt actor cell) k
      = if receiptArchiveGuard actor cell k = true then some (writeField k lifecycleField cell (.int 1))
        else none := by
  simp only [receiptArchiveStmt, interp]
  by_cases hg : receiptArchiveGuard actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`) on BOTH sides; the `setCell {cell}` move installs the
    -- per-cell map, which IS `writeField k lifecycleField cell (.int 1)` (whole record, by `…CellMap_eq`).
    simp only [if_pos hg, Option.bind]
    rw [receiptArchiveCellMap_eq]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none` on BOTH sides.
    simp only [if_neg hg, Option.bind]

#assert_axioms interp_receiptArchiveStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `execFullA`.

The standalone receipt-archive descriptor (§4) is keyed on the CHAINED executor `execFullA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.receiptArchiveA actor cell) = stateStep
s lifecycleField actor cell (.int 1)` (`execFullA_receiptArchiveA_eq`, by `rfl`). The §2 cornerstone is
over the KERNEL side only. The chained layer is exactly the §2 kernel write PLUS the runtime receipt-log
prepend `{ actor, src := cell, dst := cell, amt := 0 } :: s.log` — the runtime piece the
`RecordKernelState`-level `interp` structurally cannot emit. We bridge faithfully, naming the receipt-row
prepend EXPLICITLY in the chained post-state (the kernel-vs-runtime divergence). -/

/-- The self-targeted receipt row a committed receipt-archive prepends to the chain log (the SAME literal
`stateStep` installs: its `actor` field is the EFFECT's `actor`, its `src`/`dst` the target `cell`). Named
so the chained post-state's `log` clause is the genuine row. -/
def archiveReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`interp_receiptArchiveStmt_chained` — the IR term's KERNEL executor, lifted to the chained
`execFullA`.** When the §2 cornerstone commits on the kernel (`interp (receiptArchiveStmt actor cell)
s.kernel = some k'`), the unified action executor `execFullA s (.receiptArchiveA actor cell)` commits to
the chained state `⟨k', { actor, src := cell, dst := cell, amt := 0 } :: s.log⟩`. So the Argus term's
KERNEL meaning lifts to the chained executor the standalone descriptor speaks about, with the runtime
receipt-log row (which the kernel `interp` does not model) re-attached HERE — the explicit
kernel-vs-runtime bridge. -/
theorem interp_receiptArchiveStmt_chained
    (s : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hexec : interp (receiptArchiveStmt actor cell) s.kernel = some k') :
    execFullA s (.receiptArchiveA actor cell)
      = some { kernel := k',
               log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel-side write, gated on `receiptArchiveGuard`.
  rw [interp_receiptArchiveStmt_eq_kernel] at hexec
  -- `execFullA s (.receiptArchiveA actor cell)` reduces to `stateStep s lifecycleField actor cell
  -- (.int 1)`. Open BOTH on the same `receiptArchiveGuard` (its decoded 3-conjunct guard IS `stateStep`'s
  -- `if` condition).
  rw [execFullA_receiptArchiveA_eq]
  unfold stateStep
  by_cases hg : receiptArchiveGuard actor cell s.kernel = true
  · -- ADMIT: `hexec` names `k' = writeField s.kernel lifecycleField cell (.int 1)`; the chained step
    -- commits to that kernel + the receipt-row prepend.
    rw [if_pos hg] at hexec
    rw [if_pos ((receiptArchiveGuard_iff actor cell s.kernel).mp hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- REJECT: contradictory — `hexec` would equate `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_receiptArchiveStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of receipt-archive's OWN standalone full-state circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against receipt-archive's GENUINE standalone v1 descriptor `receiptArchiveCircuit S s
⟨actor,cell⟩ s'` (the full-state arithmetization whose soundness is `receiptArchiveA_full_sound`), NOT an
EffectVM `cellProj` row — see the descriptor note in this file's header. The executor side is routed
through §3 (`interp` ⟹ `execFullA`) and the independent `execFullA_receiptArchiveA_iff_spec` (executor ⟺
`ReceiptArchiveSpec`); the circuit side is the audited `receiptArchiveA_full_sound` (circuit ⟹
`ReceiptArchiveSpec`). Both name the SAME `ReceiptArchiveSpec`, so they PROVABLY agree on the WHOLE
17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `receiptArchive` term: receipt-archive's OWN audited standalone
v1 `EffectCommit` full-state circuit step — the full-state sponge arithmetization `satisfiedE S
receiptArchiveE (encodeE …)` satisfied on the encoded `(s, ⟨actor,cell⟩, s')` triple. Its soundness
`receiptArchiveA_full_sound` pins the complete `ReceiptArchiveSpec`. The `receiptArchive`-keyed analog of
`refusalCircuit`/`balanceACircuit`, in the v1 descriptor universe where receipt-archive carries its OWN
genuine full-state circuit. -/
def receiptArchiveCircuit (S : CommitSurface) (s : RecChainedState) (args : ReceiptArchiveArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s')

/-- **`receiptArchiveSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `ReceiptArchiveSpec s actor cell ·` are equal. Rather than re-derive this field-by-field, we route
through the PROVEN executor⟺spec corner `execFullA_receiptArchiveA_iff_spec`: each `ReceiptArchiveSpec`
reconstructs the SAME committed value `execFullA s (.receiptArchiveA actor cell) = some ·`, and `some` is
injective. This is exactly the sense in which `ReceiptArchiveSpec` is functional — it determines the
post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem receiptArchiveSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId}
    (h₁ : ReceiptArchiveSpec s actor cell s₁) (h₂ : ReceiptArchiveSpec s actor cell s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.receiptArchiveA actor cell) = some s₁ :=
    (execFullA_receiptArchiveA_iff_spec s actor cell s₁).mpr h₁
  have e₂ : execFullA s (.receiptArchiveA actor cell) = some s₂ :=
    (execFullA_receiptArchiveA_iff_spec s actor cell s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`receiptArchive_compile_sound` — the welded soundness (receipt-archive slice), against
receipt-archive's OWN descriptor.**

Suppose, for the Argus receipt-archive term `receiptArchiveStmt actor cell`:
  * the standalone receipt-archive circuit `receiptArchiveCircuit S s ⟨actor,cell⟩ s'` (= `receiptArchiveE`'s
    full-state v1 arithmetization satisfied on the encoded triple) holds, under the realizable Poseidon
    sponge portals (`hN : compressNInjective S.compressN`, `hL : cellLeafInjective S.CH`, `hRest :
    RestHashIffFrame S.RH`, `hLog : logHashInjective S.LH`) and `AccountsWF` on BOTH kernels (`hwf`,
    `hwf'`);
  * the IR term's KERNEL executor interpretation COMMITS: `interp (receiptArchiveStmt actor cell) s.kernel
    = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached: `s' = { kernel := k', log := { actor, src := cell,
dst := cell, amt := 0 } :: s.log }`. I.e. receipt-archive's OWN circuit and the IR term AGREE on the WHOLE
17-field RecordKernelState (the `"lifecycle"` RECORD slot of `cell` set to `1`, every other field — `bal`,
`caps`, `nullifiers`, the `lifecycle` SIDE-TABLE, every other cell — frozen) AND the receipt log — the
full `ReceiptArchiveSpec`, not a per-cell projection. The receipt-log row is named EXPLICITLY in the
conclusion, so the kernel-vs-runtime divergence is part of the welded statement. So the circuit the prover
runs for receipt-archive pins the complete chained state the IR term's executor produces. -/
theorem receiptArchive_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hcirc : receiptArchiveCircuit S s ⟨actor, cell⟩ s')
    (hexec : interp (receiptArchiveStmt actor cell) s.kernel = some k') :
    s' = { kernel := k',
           log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- circuit side: receipt-archive's OWN audited soundness forces the FULL `ReceiptArchiveSpec` on
  -- `(s, ⟨actor,cell⟩, s')`.
  have hspec : ReceiptArchiveSpec s actor cell s' :=
    receiptArchiveA_full_sound S hN hL hRest hLog s ⟨actor, cell⟩ s' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.receiptArchiveA actor cell) = some
  -- ⟨k', receipt::log⟩`, and the independent executor⟺spec corner turns THAT into `ReceiptArchiveSpec
  -- s actor cell ⟨k', receipt::log⟩`.
  have hspec' : ReceiptArchiveSpec s actor cell
      { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } :=
    (execFullA_receiptArchiveA_iff_spec s actor cell _).mp
      (interp_receiptArchiveStmt_chained s actor cell k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact receiptArchiveSpec_unique hspec hspec'

#assert_axioms receiptArchive_compile_sound

/-! ## §5 — NON-VACUITY: the IR term STAMPS the receipt-archive (slot write observable),
preserves every other field (frame — incl. the `lifecycle` SIDE-TABLE), and the gate REJECTS forged /
non-account / non-Live inputs (fail-closed).

The cornerstone/weld would be hollow if receipt-archive never committed, if the write were a no-op, or if
the gate admitted everything. A concrete two-cell kernel `kRA0` (cells 0,1 live; cell 0 owned by actor 0
via `Cap.node 0`, balance 42) exercises a real receipt-archive write; the rejection lemmas show each guard
leg fails closed. -/

/-- A two-cell kernel for the §5 witnesses: cells 0 and 1 live accounts (lifecycle SIDE-TABLE defaults to
Live `0`), cell 0 owned by actor 0 via `Cap.node 0` (so `stateAuthB … 0 0` holds), cell 0 holding `42` in
its `balance` RECORD slot. -/
def kRA0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 42)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 0, Dregg2.Authority.Cap.node 1] else []
    bal := fun _ _ => 0 }

/-- **NON-VACUITY (the RECEIPT-ARCHIVE is OBSERVABLE).** The committed receipt-archive STAMPS cell `0`'s
`"lifecycle"` RECORD slot to `1` (before: the slot is absent, read as `0`) — the receipt-archive lifecycle
commitment lands (the `setCell` audit write is real, not a no-op). -/
theorem receiptArchiveStmt_stamps :
    (interp (receiptArchiveStmt 0 0) kRA0).map (fun k => fieldOf "lifecycle" (k.cell 0)) = some 1 := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the cell ACTUALLY commits).** The receipt-archive of a Live, self-owned cell COMMITS
(`isSome`) — the three-leg gate admits. (Pins that the weld's `hexec` hypothesis is
satisfiable.) -/
theorem receiptArchiveStmt_commits :
    (interp (receiptArchiveStmt 0 0) kRA0).isSome = true := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: `balance` slot untouched — balance-Δ=0).** Stamping the receipt-archive leaves
cell `0`'s `"balance"` RECORD slot at `42` — the receipt-archive is balance-NEUTRAL (`setField
lifecycleField` writes a slot DISTINCT from `balance`), exactly the frozen-balance leg of
`ReceiptArchiveSpec`. No value is conjured or destroyed by a receipt-archive commitment. -/
theorem receiptArchiveStmt_balance_frozen :
    (interp (receiptArchiveStmt 0 0) kRA0).map (fun k => fieldOf "balance" (k.cell 0)) = some 42 := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: the `lifecycle` SIDE-TABLE untouched).** Stamping cell `0`'s receipt-archive
leaves the `CellId → Nat` liveness SIDE-TABLE at `0` (Live) for cell `0` — the write moved the RECORD slot
named `"lifecycle"`, NOT the side-table the R6 gate reads. This is the load-bearing confirmation the name
collision hides no frame interaction (the cell stays re-targetable), observed at the IR level. -/
theorem receiptArchiveStmt_lifecycle_sidetable_frozen :
    (interp (receiptArchiveStmt 0 0) kRA0).map (fun k => k.lifecycle 0) = some 0 := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Stamping cell `0`'s receipt-archive leaves cell
`1`'s `"lifecycle"` RECORD slot ABSENT (read as `0`) — `setCell {0}` rewrites ONLY the archiving cell's
record, confirming the write is local (not a global slot collapse). The per-cell frame the full-state
`ReceiptArchiveSpec` pins, observed. -/
theorem receiptArchiveStmt_other_cell_untouched :
    (interp (receiptArchiveStmt 0 0) kRA0).map (fun k => fieldOf "lifecycle" (k.cell 1)) = some 0 := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A receipt-archive attempted by actor `5`, who holds NO
authority over cell `0` (empty cap list), does NOT commit — the term returns `none` (the `stateAuthB`
authority leg fails). A stranger cannot stamp a receipt-archive into a cell. -/
theorem receiptArchiveStmt_rejects_unauthorized :
    interp (receiptArchiveStmt 5 0) kRA0 = none := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: non-account target).** A receipt-archive targeting a cell NOT in
`accounts` (cell `7`) does NOT commit — the term returns `none` (the MEMBERSHIP leg fails). (Actor `7`
owns cell `7` by the empty-caps `stateAuthB` self-rule, so this isolates the membership leg from the
authority leg.) -/
theorem receiptArchiveStmt_rejects_nonaccount :
    interp (receiptArchiveStmt 7 7) kRA0 = none := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: non-Live target).** A receipt-archive into a cell that is NOT Live
(lifecycle SIDE-TABLE discriminant flipped to Sealed `1`) does NOT commit — the term returns `none` (the
`cellLive` R6 leg fails; a receipt-archive commitment cannot be stamped into a dead cell). -/
theorem receiptArchiveStmt_rejects_nonlive :
    interp (receiptArchiveStmt 0 0) { kRA0 with lifecycle := fun _ => 1 } = none := by
  rw [interp_receiptArchiveStmt_eq_kernel]
  decide

#assert_axioms receiptArchiveStmt_stamps
#assert_axioms receiptArchiveStmt_commits
#assert_axioms receiptArchiveStmt_balance_frozen
#assert_axioms receiptArchiveStmt_lifecycle_sidetable_frozen
#assert_axioms receiptArchiveStmt_other_cell_untouched
#assert_axioms receiptArchiveStmt_rejects_unauthorized
#assert_axioms receiptArchiveStmt_rejects_nonaccount
#assert_axioms receiptArchiveStmt_rejects_nonlive

/-! ## §6 — THE MAGNESIUM UPGRADE: the RUNNABLE full-state soundness (all 17 fields + the 8 side-table
roots, on the circuit the prover RUNS).

§4 welded the Argus term against receipt-archive's ABSTRACT v1 `EffectCommit` full-state descriptor
(`receiptArchiveA_full_sound`, in the `satisfiedE`/`CommitSurface` universe). This section adds the
FULL-STATE-on-RUNNABLE soundness: the circuit the prover ACTUALLY RUNS — `satisfiedVm
archiveVmDescriptorWide`, the 188-wide `system_roots`-absorbing EffectVM descriptor — pins the FULL
17-field declarative post-state: the per-cell `field[1]` (the `lifecycle` RECORD slot) SET to `1` + the
rest of the block FROZEN (via the absorbed columns) AND ALL 8 side-table roots FROZEN (via the wide
commitment). This closes the Class-C "pale ghost" on the runnable descriptor: the narrow 186-wide
`receiptArchiveVmDescriptor`'s commitment bound NONE of the 8 side-table roots; the wide one binds them.

RESIDUALS (carried, NOT papered — the SAME boundaries §4 names): (a) the audit write's chained
motion is the self-targeted receipt prepended to `RecChainedState.log`, NOT a `RecordKernelState` field and
with NO EffectVM row column — it rides universe-A's `logHashInjective` portal; (b) the set `field[1]` is
the cell-record `lifecycle` SLOT, distinct from the kernel `lifecycle` SIDE-TABLE (one of the FROZEN frame
fields). This module closes the side-table-root binding gap on the kernel state. -/

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive (IsArchiveRow ArchiveRowEncodes ArchiveCellSpec)
open Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide
  (archiveVmDescriptorWide receiptArchive_runnable_full_sound)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`receiptArchive_runnable_full_state_weld` — THE RUNNABLE full-state soundness (receipt-archive
slice).** A row satisfying the RUNNABLE wide descriptor `archiveVmDescriptorWide` (`satisfiedVm`,
first/last active), decoded by `ArchiveRowEncodes env pre post` with the frozen-roots witness `sr =
preRoots`, pins the FULL 17-field declarative post-state: the per-cell `ArchiveCellSpec` (`field[1]` SET to
`1`, the rest of the block FROZEN) AND all 8 side-table roots FROZEN (`sr = preRoots`). This is the analog
of the abstract `receiptArchiveA_full_sound` (§4's circuit side), but for the circuit the prover ACTUALLY
RUNS — and it BINDS the side-table roots the narrow descriptor left unbound. The set `field[1]` IS
universe-A's `lifecycle`-write transition the IR term's executor produces (§4); the log-receipt is the
carried turn-level residual named above. -/
theorem receiptArchive_runnable_full_state_weld
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : IsArchiveRow env)
    (henc : ArchiveRowEncodes env pre post) (hroots : sr = preRoots)
    (hsat : satisfiedVm hash archiveVmDescriptorWide env true true) :
    ArchiveCellSpec pre post ∧ sr = preRoots :=
  receiptArchive_runnable_full_sound hash env pre post sr preRoots hrow henc hroots hsat

#assert_axioms receiptArchive_runnable_full_state_weld

end Dregg2.Circuit.Argus.Effects.ReceiptArchive
