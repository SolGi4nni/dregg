/-
# Dregg2.Circuit.Argus.Effects.BalanceA — the per-asset value-movement effect `balanceA` welded
into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn — each a SINGLE-CELL move on the per-cell record `balance` field (`setCell`,
`recKExec`/`recKMint`/`recKBurn`). This module welds the DIFFERENT ledger primitive `balanceA`,
in a disjoint file (it imports the Argus IR + the audited `balanceA` instance read-only and owns only its
own declarations).

`balanceA` moves the GENUINE per-asset ledger `bal : CellId → AssetId → ℤ` — NOT the record-cell `balance`
field that `transfer` moves. The verified kernel transition is `recKExecAsset` (`RecordKernel.lean:756`):

    recKExecAsset k turn a
      = if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
           ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
          some { k with bal := recTransferBal k.bal turn.src turn.dst a turn.amt }
        else none

so a committed movement DEBITS `(src, a)` and CREDITS `(dst, a)` by `turn.amt` (via `recTransferBal`,
the per-asset debit/credit movement) on the `bal` LEDGER, freezing every other RecordKernelState field.
Because it touches `bal`, the IR body's move is the §A `setBal` primitive — NOT `setCell` (transfer's).
That is the whole structural contrast: transfer ↦ `setCell` over `recTransfer` of the record `balance`;
balanceA ↦ `setBal` over `recTransferBal` of the asset-indexed `bal`. The gate is `recKExecAsset`'s
6-conjunct admissibility `if`, captured verbatim as a `Bool`.

## THE DESCRIPTOR INVESTIGATION (the most load-bearing finding — read this).

balanceA is NOT "covered by transfer's keystone by inheritance". It carries its OWN standalone descriptor
AND full circuit⟺spec soundness — but in a DIFFERENT circuit universe than the one `Argus/Compile.lean`
welds against, so the situation is worth stating precisely:

  * `Argus/Compile.lean` (transfer/mint/burn/createEscrow) welds against the EFFECTVM descriptor universe
    (`transferVmDescriptor`/`mintVmDescriptor`/…, `satisfiedVm`, the per-cell `cellProj` projection). In
    THAT universe there is NO dedicated `balanceAVmDescriptor`: the per-asset move is what the transfer/
    bridge EffectVM row pins (`recTransferBal_src`/`_dst`, `EffectVmEmitBridge`). So at the EffectVM layer,
    balanceA's circuit assurance WOULD be transfer-inherited — there is no separate EffectVM module.

  * But balanceA's GENUINE standalone circuit⟺spec crown jewel lives in the v2 EffectCommit2 / `Surface2`
    universe (`Dregg2/Circuit/Inst/balanceA.lean`): `balanceAE` (the `EffectSpec2` whose touched component
    is the WHOLE `bal` function, a `funcComponent` full-function digest) and
    `balanceA_full_sound : satisfiedE2 … (balanceAE …) … ⟹ BalanceMovementSpec` — a FULL 17-field
    declarative post-state soundness, keyed on the CHAINED executor `recCexecAsset`/`execFullA` via the
    independent `execFullA_balanceA_iff_spec` (`Spec/balancemovement.lean`). This is a SEPARATE, complete
    descriptor — balanceA is its OWN effect there, not transfer's.

This module covers both directions:

  (1) **Cornerstone (the standalone executor-refinement the task names):** `interp_balanceAStmt_eq_recKExecAsset`
      — the per-asset RAW-kernel executor `recKExecAsset` IS the Argus term, using `setBal`. New, standalone,
      the per-asset analog of `interp_transferStmt_eq_recKExec`.

  (2) **Compile weld against balanceA's OWN standalone descriptor (the v2 `Surface2` one, NOT transfer-
      inherited):** lift the raw-kernel cornerstone to the chained executor, then weld to the standalone
      `balanceACircuitStep`/`balanceA_full_sound`. The conclusion is the FULL `BalanceMovementSpec` agreement
      (all 17 kernel fields + the receipt log) — a satisfying witness of balanceA's own circuit agrees with
      the WHOLE post-state the IR term's executor produces. Strictly stronger than transfer's per-cell
      EffectVM weld, because balanceA's standalone descriptor carries the whole-state full-function digest.

The honest CHAINED-LAYER contrast carried explicitly (not papered): the raw kernel step `recKExecAsset` gates
on 6 conjuncts; the chained `recCexecAsset`/`execFullA` adds a 7th — `acceptsEffects` at `t.dst` (R1: no
credit into a Sealed/Destroyed cell). The lift theorem `interp_balanceAStmt_chained` carries that dst-liveness
conjunct as an explicit hypothesis, exactly as the kernel layering demands.

## Axiom hygiene

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
whole-function-digest assumption enters ONLY inside the reused `balanceA_full_sound` (its `Function.Injective D`
hypothesis), not in the welded conclusion's statement. Imports
are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
-- The sibling economic-family full-state-on-RUNNABLE welds (mint/burn), chained in here so the whole
-- economic family rides the existing `Argus.lean` import of `Effects.BalanceA` into the coherence anchor.
import Dregg2.Circuit.Argus.Effects.Mint
import Dregg2.Circuit.Argus.Effects.Burn

namespace Dregg2.Circuit.Argus.Effects.BalanceA

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/balanceA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective` lives in `StateCommit`; `Surface2`/`RestIffNoBal`/`satisfiedE2`/`encodeE2` in
-- `EffectCommit2`. (`effect2CircuitStep` is the `EffectRefinement` hub abbrev for exactly
-- `satisfiedE2 S E (encodeE2 S E …)`; we inline it here to keep this module's import surface to `Inst.balanceA`.)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec admitGuardA execFullA_balanceA_iff_spec)
open Dregg2.Circuit.Inst.BalanceA (BalanceArgs balanceAE balanceA_full_sound)

/-! ## §1 — The balanceA effect as an Argus IR term (gate, then the `setBal` ledger move).

`recKExecAsset` is `if <6-conjunct guard> then some { k with bal := recTransferBal … } else none`. We capture
it term-for-term: a `Bool` `guard` of the EXACT 6 conjuncts, then a `setBal` whose leaf is `recTransferBal`
on the `(src,a)`/`(dst,a)` ledger columns. The contrast with transfer is the move primitive: `setBal`
(rewrites `bal`) over `recTransferBal` (the asset-indexed debit/credit), NOT `setCell`/`recTransfer`. -/

/-- The balanceA admissibility gate as a `Bool` — exactly `recKExecAsset`'s `if` (the 7 conjuncts: authority
over `src`, non-negative amount, availability *in asset `a`* on the genuine `bal` ledger, distinctness,
both cells live accounts, and the SOURCE issuer-liveness gate `cellLifecycleLive`). This is the RAW-kernel
gate; the chained `recCexecAsset` adds `acceptsEffects` at `t.dst` on top (carried separately in §3). -/
def balanceAGuard (turn : Turn) (a : AssetId) (k : RecordKernelState) : Bool :=
  authorizedB k.caps turn
    && decide (0 ≤ turn.amt)
    && decide (turn.amt ≤ k.bal turn.src a)
    && decide (turn.src ≠ turn.dst)
    && decide (turn.src ∈ k.accounts)
    && decide (turn.dst ∈ k.accounts)
    && cellLifecycleLive k turn.src

/-- **The balanceA effect as an IR term: gate, then move the per-asset ledger.** Mirrors `transferStmt`
(gate, then move) but the move is `setBal` over `recTransferBal` — the asset-indexed debit/credit on the
genuine `bal` ledger — NOT `setCell` over `recTransfer` (transfer's record-`balance` move). The `setBal`
leaf is `recTransferBal k.bal src dst a amt`, EXACTLY the post-ledger `recKExecAsset` installs. -/
def balanceAStmt (turn : Turn) (a : AssetId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (balanceAGuard turn a))
    (RecStmt.setBal (fun k => recTransferBal k.bal turn.src turn.dst a turn.amt))

/-! ## §2 — The cornerstone: `interp` of the balanceA term IS the kernel step `recKExecAsset`. -/

/-- The balanceA `Bool` gate decodes to `recKExecAsset`'s admissibility proposition (the 7 conjuncts, in the
SAME order the kernel `if` checks them — the last being the SOURCE issuer-liveness gate). The per-asset analog
of `transferGuard_iff`. -/
theorem balanceAGuard_iff (turn : Turn) (a : AssetId) (k : RecordKernelState) :
    balanceAGuard turn a k = true ↔
      (authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
        ∧ cellLifecycleLive k turn.src = true) := by
  simp only [balanceAGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **The cornerstone (per-asset ledger).** `interp` of the balanceA term IS the verified per-asset kernel
transition `recKExecAsset` — the same partial function, by construction, exactly as the transfer cornerstone,
now over the genuine `bal` ledger via `setBal`/`recTransferBal` (NOT the record-cell `setCell`/`recTransfer`).
This is the per-asset executor-refinement: the executor IS the meaning of the term. -/
theorem interp_balanceAStmt_eq_recKExecAsset (turn : Turn) (a : AssetId) (k : RecordKernelState) :
    interp (balanceAStmt turn a) k = recKExecAsset k turn a := by
  simp only [balanceAStmt, interp]
  unfold recKExecAsset
  by_cases hg : balanceAGuard turn a k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setBal` move installs `recTransferBal …`, exactly
    -- the post-`bal` ledger `recKExecAsset` commits. The RHS `if` opens on the decoded 6-conjunct Prop.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((balanceAGuard_iff turn a k).mp hg)]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded Prop.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((balanceAGuard_iff turn a k).mpr hp))]

#assert_axioms interp_balanceAStmt_eq_recKExecAsset

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `recCexecAsset` / `execFullA`.

The standalone balanceA descriptor (§4) is keyed on the CHAINED executor `recCexecAsset` / `execFullA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.balanceA t a) = recCexecAsset s t a`. The
§2 cornerstone is over the RAW kernel step `recKExecAsset`. The chained layer is exactly `recKExecAsset` PLUS
two things: an `acceptsEffects` dst-liveness pre-gate (R1: no credit into a non-Live cell) and the receipt-log
prepend `t :: s.log`. We bridge faithfully, carrying the `acceptsEffects` conjunct as an explicit hypothesis
(the honest chained-vs-raw contrast). -/

/-- **`interp_balanceAStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When the
destination accepts effects (`acceptsEffects st.kernel t.dst = true`, the chained layer's extra R1 gate) and
the §2 cornerstone commits on the kernel (`interp (balanceAStmt t a) st.kernel = some k'`), the unified action
executor `execFullA st (.balanceA t a)` commits to the chained state `⟨k', t :: st.log⟩`. So the Argus term's
kernel meaning lifts to the chained executor the standalone descriptor speaks about, modulo the carried
dst-liveness side-condition. -/
theorem interp_balanceAStmt_chained
    (st : RecChainedState) (t : Turn) (a : AssetId) (k' : RecordKernelState)
    (haccept : acceptsEffects st.kernel t.dst = true)
    (hexec : interp (balanceAStmt t a) st.kernel = some k') :
    execFullA st (.balanceA t a) = some { kernel := k', log := t :: st.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `recKExecAsset`.
  rw [interp_balanceAStmt_eq_recKExecAsset] at hexec
  -- `execFullA st (.balanceA t a)` reduces to `recCexecAsset st t a`, which on `acceptsEffects` opens to a
  -- `match recKExecAsset …` — and `hexec` names that as `some k'`.
  show recCexecAsset st t a = some { kernel := k', log := t :: st.log }
  unfold recCexecAsset
  rw [if_pos haccept, hexec]

#assert_axioms interp_balanceAStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of balanceA's OWN standalone circuit agrees with the FULL
post-state the IR term's executor interpretation produces.

This welds against balanceA's GENUINE standalone descriptor `balanceACircuitStep S (balanceAE D hD)` (the v2
`Surface2` circuit whose soundness is `balanceA_full_sound`), NOT transfer's circuit — see the descriptor
investigation in this file's header. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the
independent `execFullA_balanceA_iff_spec` (executor ⟺ `BalanceMovementSpec`); the circuit side is the audited
`balanceA_full_sound` (circuit ⟹ `BalanceMovementSpec`). Both name the SAME `BalanceMovementSpec`, so they
PROVABLY agree on the WHOLE 17-field state — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `balanceA` term: balanceA's OWN audited standalone v2 `Surface2`
circuit step — the full-state arithmetization `satisfiedE2 S (balanceAE D hD) (encodeE2 …)` satisfied on the
encoded `(st, ⟨t,a⟩, st')` triple (DEFINITIONALLY the `EffectRefinement` hub's `effect2CircuitStep S (balanceAE
D hD) st ⟨t,a⟩ st'`, inlined here so this module imports only `Inst.balanceA`). Its soundness `balanceA_full_sound`
pins the complete `BalanceMovementSpec`. The `balanceA`-keyed analog of `compileE .transfer = transferVmDescriptor`,
in the descriptor universe where balanceA carries its OWN genuine circuit (NOT transfer-inherited). -/
def balanceACircuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (balanceAE D hD) (encodeE2 S (balanceAE D hD) st ⟨t, a⟩ st')

/-- **`balanceMovementSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`BalanceMovementSpec st t a ·` are equal. Rather than re-derive this field-by-field, we route through the
PROVEN executor⟺spec corner `execFullA_balanceA_iff_spec`: each `BalanceMovementSpec` reconstructs the SAME
committed value `execFullA st (.balanceA t a) = some ·`, and `some` is injective. This is exactly the sense in
which `BalanceMovementSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem balanceMovementSpec_unique {st st₁ st₂ : RecChainedState} {t : Turn} {a : AssetId}
    (h₁ : BalanceMovementSpec st t a st₁) (h₂ : BalanceMovementSpec st t a st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.balanceA t a) = some st₁ := (execFullA_balanceA_iff_spec st t a st₁).mpr h₁
  have e₂ : execFullA st (.balanceA t a) = some st₂ := (execFullA_balanceA_iff_spec st t a st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`balanceA_compile_sound` — the welded soundness (balanceA slice), against balanceA's OWN descriptor.**

Suppose, for the Argus balanceA term `balanceAStmt t a`:
  * the standalone balanceA circuit `balanceACircuit S D hD st t a st'` (= `balanceAE`'s full-state v2
    arithmetization satisfied on the encoded triple) holds, under the realizable whole-function digest portals
    (`hRest : RestIffNoBal S.RH`, `hLog : logHashInjective S.LH`, `hD : Function.Injective D`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (balanceAStmt t a) st.kernel = some k'`
    (`hexec`), with the destination accepting effects (`haccept`, the chained R1 side-condition).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor produces:
`st' = { kernel := k', log := t :: st.log }`. I.e. balanceA's OWN circuit and the IR term AGREE on the WHOLE
17-field RecordKernelState (`bal` debited/credited by `recTransferBal`, every other field frozen) AND the
receipt log — the full `BalanceMovementSpec`, not a per-cell projection. So the circuit the prover runs for
balanceA pins the complete state the IR term's executor produces. -/
theorem balanceA_compile_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (t : Turn) (a : AssetId) (k' : RecordKernelState)
    (hcirc : balanceACircuit S D hD st t a st')
    (haccept : acceptsEffects st.kernel t.dst = true)
    (hexec : interp (balanceAStmt t a) st.kernel = some k') :
    st' = { kernel := k', log := t :: st.log } := by
  -- circuit side: balanceA's OWN audited soundness forces the FULL `BalanceMovementSpec` on `(st, ⟨t,a⟩, st')`.
  have hspec : BalanceMovementSpec st t a st' :=
    balanceA_full_sound S D hD hRest hLog st ⟨t, a⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.balanceA t a) = some ⟨k', t :: st.log⟩`, and the
  -- independent executor⟺spec corner turns THAT into `BalanceMovementSpec st t a ⟨k', t :: st.log⟩`.
  have hspec' : BalanceMovementSpec st t a { kernel := k', log := t :: st.log } :=
    (execFullA_balanceA_iff_spec st t a _).mp (interp_balanceAStmt_chained st t a k' haccept hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact balanceMovementSpec_unique hspec hspec'

#assert_axioms balanceA_compile_sound

/-! ## §5 — NON-VACUITY: the IR term MOVES the ledger (debit/credit observable), the welded circuit
is the genuine standalone descriptor (not a placeholder), and the gate REJECTS forged inputs (fail-closed).

The cornerstone/weld would be hollow if balanceA never committed, if the move were a no-op, or if the gate
admitted everything. A concrete two-account kernel `kB0` (cells 0,1 live; cell 0 holds 30 of asset 0 on the
ledger) exercises a real movement; the rejection lemmas show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts (lifecycle defaults Live), cell 0
holds 30 of asset 0 on the genuine per-asset ledger `bal`, cell 1 holds nothing. -/
def kB0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 30 else 0 }

/-- The movement turn for the witnesses: actor 0 moves 30 from cell 0 to cell 1. -/
def tB0 : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

/-- **NON-VACUITY (the DEBIT is OBSERVABLE).** The committed movement DROPS source cell `0`'s asset-`0` ledger
entry from `30` to `0` — the value LEAVES the source (the `setBal`/`recTransferBal` debit is real). -/
theorem balanceAStmt_debits :
    (interp (balanceAStmt tB0 0) kB0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_balanceAStmt_eq_recKExecAsset]
  decide

/-- **NON-VACUITY (the CREDIT is OBSERVABLE).** The committed movement RAISES destination cell `1`'s asset-`0`
ledger entry from `0` to `30` — the value ARRIVES at the destination (the credit is real). -/
theorem balanceAStmt_credits :
    (interp (balanceAStmt tB0 0) kB0).map (fun k => k.bal 1 0) = some 30 := by
  rw [interp_balanceAStmt_eq_recKExecAsset]
  decide

/-- **NON-VACUITY (per-asset isolation).** The movement of asset `0` leaves a DIFFERENT asset column (`asset 1`)
of the source untouched — the `recTransferBal` write rewrites ONLY the moved asset's column, confirming `setBal`
moves the genuine asset-indexed ledger (not a scalar collapse). -/
theorem balanceAStmt_other_asset_untouched :
    (interp (balanceAStmt tB0 0) kB0).map (fun k => k.bal 0 1) = some 0 := by
  rw [interp_balanceAStmt_eq_recKExecAsset]
  decide

/-- **NON-VACUITY (fail-closed: overdraft).** A movement of MORE than the source holds in asset `0` (here 31 of
the 30 available) does NOT commit — the term returns `none` (the AVAILABILITY leg of the gate fails). No value
is conjured. -/
theorem balanceAStmt_rejects_overdraft :
    interp (balanceAStmt { actor := 0, src := 0, dst := 1, amt := 31 } 0) kB0 = none := by
  rw [interp_balanceAStmt_eq_recKExecAsset]
  decide

/-- **NON-VACUITY (fail-closed: self-move).** A self-movement (`src = dst`) does NOT commit — the DISTINCTNESS
leg fails; no value can be conjured by moving to oneself. -/
theorem balanceAStmt_rejects_self :
    interp (balanceAStmt { actor := 0, src := 0, dst := 0, amt := 30 } 0) kB0 = none := by
  rw [interp_balanceAStmt_eq_recKExecAsset]
  decide

#assert_axioms balanceAStmt_debits
#assert_axioms balanceAStmt_credits
#assert_axioms balanceAStmt_other_asset_untouched
#assert_axioms balanceAStmt_rejects_overdraft
#assert_axioms balanceAStmt_rejects_self

/-! ## §6 — FULL-STATE on the RUNNABLE EffectVM descriptor (the magnesium breadth, per-asset entry).

§4 welded balanceA against its OWN standalone v2 `Surface2` circuit (`balanceACircuit` /
`balanceA_full_sound`), whose `satisfiedE2` soundness already pins the COMPLETE `BalanceMovementSpec` (all
17 RecordKernelState fields, the whole-`bal`-function digest). That is full-state, but in the `satisfiedE2`
universe — NOT the `satisfiedVm` / `EffectVmDescriptor` universe (the circuit the EffectVM prover actually
runs row-by-row). As this file's DESCRIPTOR INVESTIGATION states, balanceA carries NO separate
`balanceAVmDescriptor`: at the EffectVM layer its per-asset move is what the TRANSFER row pins on the
`bal_lo` column — the genuine per-asset ledger entry `recTransferBal …` projected onto one cell's balance
limb. So balanceA's RUNNABLE EffectVM descriptor IS `transferVmDescriptorWide` (the magnesium STAGE-4 wide
descriptor, `EffectVmFullStateRunnable.transferVmDescriptorWide`), instantiated per ledger entry.

This section delivers balanceA's full-state-on-RUNNABLE THROUGH that wide descriptor, reusing the GENERIC
`runnable_full_sound` (the crypto is discharged ONCE there, against the NAMED `Poseidon2SpongeCR` portal —
nothing re-assumed here), and WELDS the descriptor-pinned per-entry post-state to `recKExecAsset`'s genuine
per-asset ledger move (`recTransferBal_correct`). The honest CONTRAST with the per-cell `bal_lo` block: the
EffectVM row carries ONE cell's balance limb, so balanceA's two-sided move (debit `(src,a)`, credit
`(dst,a)`) is TWO wide rows — a debit leg (`direction = 1`) and a credit leg (`direction = 0`) — paired at
the turn layer (cited, `TurnEmit`), exactly as the transfer keystone's BOUNDARY assigns the
two-sided conservation. Each leg's FULL 17-field per-cell post is pinned here. -/

section RunnableFullState

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (IsTransferRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState RowEncodes CellTransferSpec TransferParams signedMove)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (transferVmDescriptorWide transferRunnableSpec TransferFullClause runnable_full_sound)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots emptySystemRoots)
open Dregg2.Circuit.Spec.BalanceMovement (recTransferBal_correct)

/-- Project ledger entry `(c, a)` of `k` into the EffectVM `CellState` block: `balLo` = the genuine
per-asset ledger measure `bal c a` (the SAME measure `recTransferBal` moves), every other block component
`0` (balanceA touches no high-limb / nonce / field-array / cap-root / reserved on a ledger entry — all
FROZEN). `commit` (the digest output) is `0`. The per-asset analog of `EffectVmEmitMint.cellProjA`. -/
def cellProjA (k : RecordKernelState) (c : CellId) (a : AssetId) : CellState where
  balLo    := k.bal c a
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- balanceA's per-asset DEBIT-leg transfer params: amount `t.amt`, `direction = 1` (debit). `signedMove`
is `t.amt·(1 − 2) = −t.amt` — exactly `recTransferBal`'s `src` debit. -/
def debitParamsA (t : Turn) : TransferParams := { amount := t.amt, direction := 1 }

/-- balanceA's per-asset CREDIT-leg transfer params: amount `t.amt`, `direction = 0` (credit). `signedMove`
is `t.amt·(1 − 0) = +t.amt` — exactly `recTransferBal`'s `dst` credit. -/
def creditParamsA (t : Turn) : TransferParams := { amount := t.amt, direction := 0 }

/-- **`balanceA_runnable_full_sound` — THE DELIVERABLE (full-state on the RUNNABLE descriptor, per leg).**
A row satisfying `transferVmDescriptorWide` — the WIDE descriptor the EffectVM prover RUNS for balanceA's
per-asset `bal_lo` move (`satisfiedVm`, first/last active) — under the structured `RowEncodes` decode (for
either leg's params `p`), pins the FULL 17-field declarative post-state: the per-cell `CellTransferSpec`
(this entry's balance moved by the signed amount, the whole frame frozen) AND the 8 side-table roots FROZEN
(`postRoots = preRoots`). Routed THROUGH the generic `runnable_full_sound` at the validated
`transferRunnableSpec` — the crypto/anti-ghost on all 17 fields is the generic
`wide_rejects_state_tamper`/`wide_rejects_root_tamper`, the sole portal `Poseidon2SpongeCR`. Strictly
stronger than a per-row-intent projection: the wide `state_commit` absorbs the `system_roots` digest, so a
tamper of ANY of the 17 fields' content is UNSAT. -/
theorem balanceA_runnable_full_sound (p : TransferParams) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsTransferRow env)
    (henc : RowEncodes env pre p post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash transferVmDescriptorWide env true false) :
    CellTransferSpec pre p post ∧ postRoots = preRoots :=
  runnable_full_sound (transferRunnableSpec p preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

#assert_axioms balanceA_runnable_full_sound

/-! ### §6a — WELD: the descriptor-pinned per-entry post-state IS `recKExecAsset`'s genuine ledger move.

The full-state `balanceA_runnable_full_sound` pins a `CellTransferSpec` per leg; here we confirm that
per-cell move IS the per-asset ledger entry `recKExecAsset` commits, via `recTransferBal_correct` — so the
RUNNABLE descriptor and the §2 cornerstone executor agree on the moved entry (not a fourth spec). The
balanceA-specific content (over the reused transfer descriptor) is exactly this per-asset ledger weld. -/

/-- **`debitLeg_matches_executor` — the SOURCE entry agrees.** When `recKExecAsset` commits
(`interp (balanceAStmt t a) k = some k'`, the §2 cornerstone) with `src ≠ dst`, the DEBIT leg's
descriptor-pinned per-cell post (`CellTransferSpec` at `debitParamsA t`, decoding the projected `(src,a)`
entry) agrees with the executor's debited `(src,a)` ledger entry: `post.balLo ≡ k'.bal t.src a
[ZMOD 2013265921]`, where the executor entry is exactly `k.bal t.src a − t.amt`.

DEBT-A note: `CellTransferSpec.balLo` denotes a `≡ [ZMOD p]` move over the un-range-checked balance limb.
The agreement here is a WRITE (an equality of the moved value), NOT an ORDER, so by the classifying rule it
is REPAIRABLE (not a wrap forgery — the availability `amt ≤ bal` order lives only in `recKExecAsset`'s gate
over the genuine unbounded-ℤ kernel ledger `bal`, never over a circuit limb). We thread the mod-p congruence
and state the leg agreement faithfully as `≡ [ZMOD p]` — the executor's source debit, exactly, mod `p`. -/
theorem debitLeg_matches_executor (t : Turn) (a : AssetId) (k k' : RecordKernelState)
    (pre post : CellState) (postRoots preRoots : SysRoots)
    (hne : t.src ≠ t.dst)
    (hpre : pre = cellProjA k t.src a)
    (hspec : CellTransferSpec pre (debitParamsA t) post ∧ postRoots = preRoots)
    (hexec : interp (balanceAStmt t a) k = some k') :
    post.balLo ≡ k'.bal t.src a [ZMOD 2013265921] := by
  obtain ⟨_, hlo, _, _, _, _, _⟩ := hspec.1
  -- executor side (exact ℤ, no mod-p): the §2 cornerstone names `k'` as `recKExecAsset`'s post
  -- (`bal := recTransferBal …`), so `k'.bal t.src a = k.bal t.src a − t.amt`.
  rw [interp_balanceAStmt_eq_recKExecAsset] at hexec
  unfold recKExecAsset at hexec
  by_cases hg : (authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts ∧ cellLifecycleLive k t.src = true)
  · rw [if_pos hg] at hexec
    have hk' : k'.bal = recTransferBal k.bal t.src t.dst a t.amt :=
      (congrArg RecordKernelState.bal (Option.some.inj hexec)).symm
    have hbal : k'.bal t.src a = k.bal t.src a - t.amt := by
      rw [hk', (recTransferBal_correct k.bal t.src t.dst a t.amt hne).1]
    -- congruence side: `pre.balLo + signedMove (debitParamsA t) = k.bal src a + amt·(1−2·1) = bal src a − amt`.
    rw [hbal]
    have hrw : pre.balLo + signedMove (debitParamsA t) = k.bal t.src a - t.amt := by
      rw [hpre]; show k.bal t.src a + t.amt * (1 - 2 * 1) = k.bal t.src a - t.amt; ring
    rwa [hrw] at hlo
  · rw [if_neg hg] at hexec; simp only [reduceCtorEq] at hexec

/-- **`creditLeg_matches_executor` — the DESTINATION entry agrees.** Symmetric to the debit leg: the CREDIT
leg's descriptor-pinned per-cell post (`CellTransferSpec` at `creditParamsA t`, decoding the projected
`(dst,a)` entry) agrees with the executor's credited `(dst,a)` ledger entry: `post.balLo ≡ k'.bal t.dst a
[ZMOD 2013265921]`, where the executor entry is exactly `k.bal t.dst a + t.amt`. Same REPAIRABLE mod-p
credit-write (equality, not order) as the debit leg — stated faithfully as the `≡ [ZMOD p]` congruence. -/
theorem creditLeg_matches_executor (t : Turn) (a : AssetId) (k k' : RecordKernelState)
    (pre post : CellState) (postRoots preRoots : SysRoots)
    (hne : t.src ≠ t.dst)
    (hpre : pre = cellProjA k t.dst a)
    (hspec : CellTransferSpec pre (creditParamsA t) post ∧ postRoots = preRoots)
    (hexec : interp (balanceAStmt t a) k = some k') :
    post.balLo ≡ k'.bal t.dst a [ZMOD 2013265921] := by
  obtain ⟨_, hlo, _, _, _, _, _⟩ := hspec.1
  rw [interp_balanceAStmt_eq_recKExecAsset] at hexec
  unfold recKExecAsset at hexec
  by_cases hg : (authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts ∧ cellLifecycleLive k t.src = true)
  · rw [if_pos hg] at hexec
    have hk' : k'.bal = recTransferBal k.bal t.src t.dst a t.amt :=
      (congrArg RecordKernelState.bal (Option.some.inj hexec)).symm
    have hbal : k'.bal t.dst a = k.bal t.dst a + t.amt := by
      rw [hk', (recTransferBal_correct k.bal t.src t.dst a t.amt hne).2.1]
    rw [hbal]
    have hrw : pre.balLo + signedMove (creditParamsA t) = k.bal t.dst a + t.amt := by
      rw [hpre]; show k.bal t.dst a + t.amt * (1 - 2 * 0) = k.bal t.dst a + t.amt; ring
    rwa [hrw] at hlo
  · rw [if_neg hg] at hexec; simp only [reduceCtorEq] at hexec

#assert_axioms debitLeg_matches_executor
#assert_axioms creditLeg_matches_executor

/-! ### §6b — NON-VACUITY: a concrete leg satisfies the full clause, and it is refutable.

The full-state lift is hollow if `CellTransferSpec` is never inhabited per-asset. We exhibit a concrete
DEBIT leg (`kB0`/`tB0` from §5: cell 0 holds 30 of asset 0, moves 30 to cell 1) whose projected `(src,a)`
entry `100 → ...` realizes the `debitParamsA` move, and refute a forged post. -/

/-- The DEBIT leg's projected pre-state for `kB0`/`tB0`: cell 0's asset-0 entry is `30`, rest `0`. -/
def debitPreB0 : CellState := cellProjA kB0 tB0.src 0

/-- The DEBIT leg's full post: `bal_lo 30 → 0` (debit by 30), frame frozen, nonce ticked, roots frozen.
A concrete inhabitant of `transferRunnableSpec`'s `fullClause` for balanceA's debit leg. -/
def debitPostB0 : CellState :=
  { debitPreB0 with balLo := 0, nonce := debitPreB0.nonce + 1 }

/-- **`debitLeg_realizes` — NON-VACUITY (witness TRUE).** The DEBIT leg's `fullClause` is INHABITED:
`debitPostB0` is the genuine `debitParamsA tB0` image of `debitPreB0` (`30 → 0`, signed move `−30`, frame
frozen) with frozen roots. So the per-asset full clause is NOT `True`. -/
theorem debitLeg_realizes :
    (transferRunnableSpec (debitParamsA tB0) emptySystemRoots).fullClause
      debitPreB0 debitPostB0 emptySystemRoots := by
  refine ⟨⟨Or.inr rfl, ?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩
  show debitPostB0.balLo = debitPreB0.balLo + signedMove (debitParamsA tB0)
  show (0 : ℤ) = debitPreB0.balLo + tB0.amt * (1 - 2 * 1)
  simp only [debitPreB0, cellProjA, kB0, tB0]
  norm_num

/-- **`debitLeg_clause_not_trivial` — REFUTABLE (witness FALSE).** A post whose `bal_lo` is NOT the debit
(`debitPreB0.balLo = 30`, demanding `0`, but a forged `999`) FAILS the full clause. -/
theorem debitLeg_clause_not_trivial :
    ¬ (transferRunnableSpec (debitParamsA tB0) emptySystemRoots).fullClause
        debitPreB0 { debitPostB0 with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨_, hbal, _⟩, _⟩
  -- hbal : 999 = debitPreB0.balLo + signedMove (debitParamsA tB0) = 30 + (−30) = 0
  simp only [debitPreB0, cellProjA, kB0, tB0, signedMove, debitParamsA] at hbal
  norm_num at hbal

#assert_axioms debitLeg_realizes
#assert_axioms debitLeg_clause_not_trivial

end RunnableFullState

end Dregg2.Circuit.Argus.Effects.BalanceA
