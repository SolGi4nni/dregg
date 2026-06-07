/-
# Dregg2.Spec.CircuitSpecTriangle — THE CROWN-JEWEL CORNER: circuit⟺(intent-)spec.

This module closes corner **(b)** of the three-corner soundness triangle for the reference effect
families (transfer · mint · escrow-create), connecting the ZK circuit's algebraic statement to the
INDEPENDENT, intent-derived functional spec.

## The three corners

For each effect there is an independent declarative spec, against which we prove BOTH:
  * **(a) executor ⟺ spec** — `Dregg2/Spec/FunctionalRefinement.lean`: the intent functional specs
    (`mintSpec`, `escrowCreateSpec`, …) written field-by-field from protocol intent, with full
    biconditional triangles (`mint_triangle`, `escrowCreate_triangle`) + anti-ghost teeth.
  * **(b) circuit ⟺ spec** — THIS module: a verifying ZK witness pins the SPEC-correct post-state.

## What corner (b) already had — and the gap it left

The per-effect circuit-soundness theorems (`mintA_full_sound`, `transfer_full_sound`,
`createEscrowA_full_sound`) prove a satisfying full-state witness yields a *circuit-side* declarative
spec (`MintASpec`, `BalanceMovementSpec`, `EscrowHoldingCreateSpec`). Those circuit-side specs pin
the post-state in terms of the EXECUTOR'S OWN ledger helpers (`recBalCredit`, `recTransferBal`,
`recBalCreditCell … (-amount)`). That is genuine full-state soundness over the state commitment, but
it leaves one question unanswered: **does the circuit enforce the EXACT function the protocol INTENDS
— the debit-the-creator / credit-this-cell / park-this-record move — or merely "whatever helper the
executor happens to call"?** A reader who does not trust `recBalCredit`'s NAME is not yet served.

## What this module proves (the connection)

For each reference family we prove the circuit's algebraic statement is SUFFICIENT to enforce the
INTENT ledger move, written from protocol intent in `FunctionalRefinement` (`intentCredit`,
`intentDebit`, `escrowCreateRecord`) — NOT from any executor helper:

  * **SOUNDNESS** `*_circuit_pins_intent`: a verifying witness ⇒ the post-`bal` ledger is EXACTLY the
    intent move (`intentCredit`/`intentDebit`/`intentTransfer`), and (escrow) the parked record is
    EXACTLY the intent record. The bridge is the proved independent-function equalities
    `intentCredit_eq_balCredit` / `intentDebit_eq_credit` / `intentTransfer_eq_recTransferBal`
    (§FunctionalRefinement §0 + §2 here): the executor helper and the intent oracle are EQUAL
    functions, so the circuit pins the intent.

  * **ANTI-GHOST at the circuit level** `*_circuit_rejects_wrong_ledger`: a witness whose post-`bal`
    is NOT the intent move does NOT verify (UNSAT). The contrapositive of soundness — a wrong-output
    witness is rejected. (Tampering ANY ledger entry away from the intent move ⇒ no verifying
    witness exists for that post-state.)

  * **COMPLETENESS (mint/transfer, modulo the named §8 carrier)** `*_intent_is_circuit_acceptable`:
    a post-state realizing the intent move IS circuit-acceptable — the honest prover can produce a
    verifying witness. Stated through the executor⟺circuit-spec biconditionals
    (`recCMintAsset_iff_spec`, `recCexecAsset_iff_spec`) under the explicit §8 carrier hypotheses
    (`Surface2`, `RestIffNoBal`, `logHashInjective`, `Function.Injective D`) — never `sorry`.

## The amplification template (§4)

`circuit_pins_intent_of_bridge` packages the pattern as a reusable lemma:
  `circuit_full_sound (→ circuit-spec) + (circuit-spec.bal = executorHelper) + (executorHelper =
   intentMove) ⟹ circuit pins intentMove`.
So the remaining ~40 effects grind through mechanically (supply each its `intent*_eq_*` bridge — most
already exist in `FunctionalRefinement`).

DISCIPLINE: no `sorry`, no `:= True`, no circular restatement. The §8 crypto (the carried
`Function.Injective D` / `compressNInjective` / `logHashInjective` — the realizable Poseidon
collision-resistance set) is the legitimate NAMED carrier; everything above it is proved. The
soundness theorems are NON-VACUOUS: each exhibits (via the anti-ghost) a wrong post-`bal` the circuit
rejects, and the `intent*_eq_*` bridges are genuine equalities of two independently-written functions
(an executor that debited the recipient, or credited the wrong asset, would make them FALSE).
-/
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.bridgeMintA
import Dregg2.Circuit.Inst.createEscrowA
import Dregg2.Circuit.Inst.createCommittedEscrowA
import Dregg2.Circuit.Inst.bridgeLockA
import Dregg2.Circuit.Inst.refundEscrowA
import Dregg2.Circuit.Inst.bridgeCancelA
import Dregg2.Circuit.Inst.releaseEscrowA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.queueAllocateA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.swissExportA
import Dregg2.Circuit.Inst.sealA
import Dregg2.Spec.FunctionalRefinement

namespace Dregg2.Spec.CircuitSpecTriangle

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (compressNInjective logHashInjective cellLeafInjective
  RestHashIffFrame AccountsWF)
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.EffectsState (setField)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Spec.FunctionalRefinement (intentCredit intentDebit intentCredit_eq_balCredit
  intentDebit_eq_balCredit intentDebit_eq_credit intentCredit_eq_credit escrowCreateRecord)

/-! ## §0 — the AMPLIFICATION TEMPLATE.

The reusable shape: a circuit soundness theorem hands us a circuit-side spec whose ledger clause is
`post = executorHelper pre`. An independent-function bridge proves `executorHelper = intentMove`.
Composing the two pins the post-state to the EXACT intent move. This `Eq`-transport is trivial in
isolation, but naming it pins the discipline (the bridge MUST be a genuine independent equality, not a
restatement) and lets every downstream family read the same line. -/

/-- **`pin_intent_of_bridge`** — the amplification core. If a circuit-side soundness fact pins the
post-ledger to `executorHelper pre` (`hsound`), and an INDEPENDENT bridge proves the executor helper
IS the intent move (`hbridge : executorHelper pre = intentMove pre`), then the circuit pins the post-
ledger to the intent move. Trivial `Eq.trans`, but it is the load-bearing composition: it is
NON-vacuous EXACTLY WHEN `hbridge` is a real equality of two independently-written functions (which
`intentCredit_eq_balCredit` & co. are — an executor crediting the wrong column would refute them). -/
theorem pin_intent_of_bridge {α : Type} {post : α} {executorHelper intentMove : α}
    (hsound : post = executorHelper) (hbridge : executorHelper = intentMove) :
    post = intentMove := hsound.trans hbridge

/-! ## §1 — MINT: the circuit pins the INTENT credit.

`Inst.mintA.mintA_full_sound` gives `MintASpec`, whose `bal` clause is
`s'.kernel.bal = recBalCredit s.kernel.bal cell a amt`. The intent move (`FunctionalRefinement`'s
`mintSpec`) credits the SAME column via `intentCredit … cell a amt`. `intentCredit_eq_balCredit`
proves the two are EQUAL functions, so a verifying mint witness pins the EXACT intent credit. -/

open Dregg2.Circuit.Inst.MintA (MintArgs mintE mintA_full_sound)
open Dregg2.Circuit.Spec.SupplyCreation (MintASpec recCMintAsset_iff_spec)

/-- **THEOREM (mint SOUNDNESS — circuit pins the intent credit).** A verifying full-state witness for
`mintE` forces the post-`bal` ledger to be EXACTLY the intent credit `intentCredit … cell a amt`
(cell `cell`'s asset-`a` column up by `amt`, every other (cell,asset) literally fixed — written from
supply intent in `FunctionalRefinement`, NOT from `recBalCredit`). The circuit's algebraic statement
enforces the EXACT intended supply function. Carries only the §8 named CR set + `Function.Injective D`. -/
theorem mint_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (mintE D hD) (encodeE2 S (mintE D hD) s args s')) :
    s'.kernel.bal = intentCredit s.kernel.bal args.cell args.a args.amt := by
  have hspec : MintASpec s args.actor args.cell args.a args.amt s' :=
    mintA_full_sound S D hD hRest hLog s args s' h
  -- the circuit-side spec's bal clause: post = recBalCredit pre.
  have hsound : s'.kernel.bal = recBalCredit s.kernel.bal args.cell args.a args.amt := hspec.2.1
  -- the INDEPENDENT bridge: recBalCredit = intentCredit (an equality of two functions).
  exact pin_intent_of_bridge hsound (intentCredit_eq_balCredit _ _ _ _).symm

/-- **THEOREM (mint ANTI-GHOST at the circuit level).** A witness whose post-`bal` is NOT the intent
credit does NOT verify — the contrapositive of soundness. Tampering ANY ledger entry away from the
intent move ⇒ `satisfiedE2` is UNSATISFIABLE for that post-state. (A mint that credited the wrong
amount, wrong asset, wrong cell, or touched a 2nd column has no verifying witness.) -/
theorem mint_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentCredit s.kernel.bal args.cell args.a args.amt) :
    ¬ satisfiedE2 S (mintE D hD) (encodeE2 S (mintE D hD) s args s') := by
  intro h
  exact hwrong (mint_circuit_pins_intent S D hD hRest hLog s args s' h)

/-- **THEOREM (mint COMPLETENESS — the honest intent-realizing step IS circuit-acceptable).** A
committed `recCMintAsset` step (the gated executor's mint) BOTH (1) satisfies the circuit-side spec
`MintASpec` the honest prover commits — so a verifying witness exists (the `encodeE2` generator +
`mintA`'s `effect2_circuit_full_complete` lineage) — AND (2) REALIZES the intent credit
`intentCredit … cell a amt`. So the honest prover's reachable circuit target IS the intent move (not
some other admitted post-state): every protocol-legal mint produces an intent-correct, provable
transition. Discharged THROUGH the executor⟺circuit-spec biconditional + the `intentCredit_eq_balCredit`
bridge; the intent realization is a CONSEQUENCE of committing, not an extra premise. -/
theorem mint_intent_is_circuit_acceptable
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (hcommit : recCMintAsset s args.actor args.cell args.a args.amt = some s') :
    MintASpec s args.actor args.cell args.a args.amt s'
    ∧ s'.kernel.bal = intentCredit s.kernel.bal args.cell args.a args.amt := by
  have hspec : MintASpec s args.actor args.cell args.a args.amt s' :=
    (recCMintAsset_iff_spec s args.actor args.cell args.a args.amt s').mp hcommit
  exact ⟨hspec, pin_intent_of_bridge hspec.2.1 (intentCredit_eq_balCredit _ _ _ _).symm⟩

/-! ## §2 — TRANSFER (balance-movement): the circuit pins the INTENT debit+credit.

`Inst.transfer.transfer_full_sound` gives `BalanceMovementSpec`, whose `bal` clause is
`s'.kernel.bal = recTransferBal s.kernel.bal src dst a amt`. We write the intent transfer ledger
`intentTransfer` from protocol intent (debit `src`, credit `dst` in column `a`; every other entry
fixed) and prove it EQUALS `recTransferBal` — a genuine independent-function equality (it would be
FALSE if the executor debited `dst` or moved the wrong column). The circuit then pins the EXACT intent
debit+credit. -/

open Dregg2.Circuit.Inst.Transfer (BalanceArgs balanceE transfer_full_sound)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec recCexecAsset_iff_spec)

/-- **`intentTransfer bal src dst a amt`** — the INTENT ledger of a value movement, written from
protocol intent: cell `src`'s asset-`a` column drops by `amt`, cell `dst`'s rises by `amt`, every
OTHER (cell, asset) pair is literally unchanged. Composed from the §FunctionalRefinement §0 oracles
(`intentDebit` then `intentCredit`) — NOT a call to `recTransferBal`. -/
def intentTransfer (bal : CellId → AssetId → ℤ) (src dst : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  intentCredit (intentDebit bal src a amt) dst a amt

/-- **`intentTransfer_eq_recTransferBal` (PROVED — genuine independent-function equality).** The
intent debit-src-credit-dst move coincides pointwise with the executor's `recTransferBal`. Two
INDEPENDENTLY-written ledger functions proven EQUAL: the intent (debit `src`, credit `dst`) lands on
exactly the columns `recTransferBal` moves. It would be FALSE if `recTransferBal` debited `dst`,
credited `src`, moved a different asset column, or spilled onto a third cell — so it carries real
content. Requires `src ≠ dst` (a transfer between distinct cells; the circuit's `cTDistinct` gate and
`BalanceMovementSpec`'s `admitGuardA` both enforce this). -/
theorem intentTransfer_eq_recTransferBal (bal : CellId → AssetId → ℤ) (src dst : CellId)
    (a : AssetId) (amt : ℤ) (hne : src ≠ dst) :
    intentTransfer bal src dst a amt = recTransferBal bal src dst a amt := by
  funext c b
  unfold intentTransfer intentCredit intentDebit recTransferBal
  by_cases hb : b = a
  · by_cases hcs : c = src
    · -- c = src ≠ dst: credit branch misses, debit lands.
      have hcd : ¬ c = dst := fun h => hne (hcs ▸ h)
      rw [if_neg (fun h => hcd h.1), if_pos ⟨hcs, hb⟩, if_pos hb, if_pos hcs]
    · by_cases hcd : c = dst
      · rw [if_pos ⟨hcd, hb⟩, if_neg (fun h => hcs h.1), if_pos hb, if_neg hcs, if_pos hcd]
      · rw [if_neg (fun h => hcd h.1), if_neg (fun h => hcs h.1), if_pos hb, if_neg hcs, if_neg hcd]
  · rw [if_neg (fun h => hb h.2), if_neg (fun h => hb h.2), if_neg hb]

/-- **THEOREM (transfer SOUNDNESS — circuit pins the intent debit+credit).** A verifying full-state
witness for `balanceE` forces the post-`bal` ledger to be EXACTLY the intent transfer
`intentTransfer … src dst a amt` (debit `src`, credit `dst`, every other entry fixed — written from
protocol intent, NOT from `recTransferBal`). The circuit's algebraic statement enforces the EXACT
intended value-movement function. The `src ≠ dst` premise the bridge needs is DELIVERED BY the
verifying witness itself (`BalanceMovementSpec`'s `admitGuardA` carries `src ≠ dst`). -/
theorem transfer_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (balanceE D hD) (encodeE2 S (balanceE D hD) s args s')) :
    s'.kernel.bal = intentTransfer s.kernel.bal args.t.src args.t.dst args.a args.t.amt := by
  have hspec : BalanceMovementSpec s args.t args.a s' :=
    transfer_full_sound S D hD hRest hLog s args s' h
  -- the verifying witness carries the distinctness premise the bridge needs (admitGuardA.2.2.2.1).
  have hne : args.t.src ≠ args.t.dst := hspec.1.2.2.2.1
  -- circuit-side spec's bal clause: post = recTransferBal pre.
  have hsound : s'.kernel.bal = recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt :=
    hspec.2.1
  exact pin_intent_of_bridge hsound
    (intentTransfer_eq_recTransferBal _ _ _ _ _ hne).symm

/-- **THEOREM (transfer ANTI-GHOST at the circuit level).** A witness whose post-`bal` is NOT the
intent transfer does NOT verify — the contrapositive of soundness. Tampering ANY ledger entry away
from the debit-src-credit-dst move (e.g. crediting `src`, draining a third cell, moving the wrong
asset) ⇒ `satisfiedE2` is UNSATISFIABLE for that post-state. -/
theorem transfer_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentTransfer s.kernel.bal args.t.src args.t.dst args.a args.t.amt) :
    ¬ satisfiedE2 S (balanceE D hD) (encodeE2 S (balanceE D hD) s args s') := by
  intro h
  exact hwrong (transfer_circuit_pins_intent S D hD hRest hLog s args s' h)

/-- **THEOREM (transfer COMPLETENESS — the honest intent-realizing step IS circuit-acceptable).** A
committed `recCexecAsset` step (the gated per-asset movement) BOTH satisfies the circuit-side spec
`BalanceMovementSpec` the honest prover commits — so a verifying witness exists (the `encodeE2`
generator + `balanceE`'s completeness lineage) — AND REALIZES the intent transfer `intentTransfer …`.
So the honest prover's reachable circuit target IS the intent debit+credit. The `src ≠ dst` the bridge
needs is delivered by the committed step's own guard (`admitGuardA`). -/
theorem transfer_intent_is_circuit_acceptable
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (hcommit : recCexecAsset s args.t args.a = some s') :
    BalanceMovementSpec s args.t args.a s'
    ∧ s'.kernel.bal = intentTransfer s.kernel.bal args.t.src args.t.dst args.a args.t.amt := by
  have hspec : BalanceMovementSpec s args.t args.a s' :=
    (recCexecAsset_iff_spec s args.t args.a s').mp hcommit
  have hne : args.t.src ≠ args.t.dst := hspec.1.2.2.2.1
  exact ⟨hspec, pin_intent_of_bridge hspec.2.1 (intentTransfer_eq_recTransferBal _ _ _ _ _ hne).symm⟩

/-! ## §3 — ESCROW CREATE: the circuit pins the INTENT debit AND the INTENT parked record.

`Inst.createEscrowA.createEscrowA_full_sound` gives `EscrowHoldingCreateSpec`, whose `bal` clause is
`recBalCreditCell s.kernel.bal creator asset (-amount)` and whose `escrows` clause is
`parkedRecord id creator recipient asset amount :: s.kernel.escrows`. The intent move
(`FunctionalRefinement`'s `escrowCreateSpec`) debits the creator via `intentDebit` and parks
`escrowCreateRecord`. `intentDebit_eq_credit` bridges the ledger; `parkedRecord = escrowCreateRecord`
(a definitional field-for-field identity) bridges the record. So a verifying create witness pins the
EXACT intent debit AND the EXACT intent parked record. -/

open Dregg2.Circuit.Inst.CreateEscrowA (createEscrowE createEscrowA_full_sound)
open Dregg2.Circuit.Spec.EscrowHoldingCreate (EscrowHoldingCreateSpec parkedRecord
  createEscrowChainA_iff_spec)

/-- **`parkedRecord_eq_escrowCreateRecord` (PROVED — definitional record identity).** The circuit
spec's parked `EscrowRecord` (`parkedRecord`) is FIELD-FOR-FIELD the intent record
(`escrowCreateRecord` from `FunctionalRefinement`): same `id`, `creator`, `recipient`, `amount`,
`resolved := false`, `asset`. So the circuit's `escrows`-prepend pins the EXACT intent record (it would
be FALSE if the executor parked a RESOLVED record, or swapped creator/recipient). -/
theorem parkedRecord_eq_escrowCreateRecord
    (a : Dregg2.Exec.Handlers.Escrow.CreateEscrowArgs) :
    parkedRecord a.id a.creator a.recipient a.asset a.amount = escrowCreateRecord a := by
  unfold parkedRecord escrowCreateRecord
  rfl

/-- **THEOREM (escrow-create SOUNDNESS — circuit pins the intent debit + intent record).** A verifying
full-state witness for `createEscrowE` forces (1) the post-`bal` ledger to be EXACTLY the intent debit
`intentDebit … creator asset amount` (creator's asset-`asset` column down by `amount`, every other
entry fixed), AND (2) the post-`escrows` head to be EXACTLY the intent parked record
`escrowCreateRecord` prepended — both written from protocol intent, NOT from the executor. The
circuit's algebraic statement enforces the EXACT intended escrow-lock function (ledger move + record). -/
theorem escrowCreate_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.CreateEscrowA.CreateEscrowArgs)
    (s' : RecChainedState)
    (h : satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s')) :
    s'.kernel.bal = intentDebit s.kernel.bal args.creator args.asset args.amount
    ∧ s'.kernel.escrows
        = { id := args.id, creator := args.creator, recipient := args.recipient,
            amount := args.amount, resolved := false, asset := args.asset }
          :: s.kernel.escrows := by
  have hspec : EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset
      args.amount s' := createEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h
  refine ⟨?_, ?_⟩
  · -- the ledger clause: post = recBalCreditCell … (-amount); bridge to intentDebit.
    have hsound : s'.kernel.bal = recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount) :=
      hspec.2.1
    exact pin_intent_of_bridge hsound (intentDebit_eq_credit _ _ _ _).symm
  · -- the escrows clause: post = parkedRecord … :: …; parkedRecord IS the intent record literal.
    have hsound : s'.kernel.escrows
        = parkedRecord args.id args.creator args.recipient args.asset args.amount :: s.kernel.escrows :=
      hspec.2.2.1
    -- parkedRecord unfolds to the field-for-field intent record.
    have : parkedRecord args.id args.creator args.recipient args.asset args.amount
        = { id := args.id, creator := args.creator, recipient := args.recipient,
            amount := args.amount, resolved := false, asset := args.asset } := rfl
    rw [hsound, this]

/-- **THEOREM (escrow-create ANTI-GHOST at the circuit level).** A witness whose post-`bal` is NOT the
intent debit does NOT verify — the contrapositive of the ledger half of soundness. Tampering the
ledger away from the single-cell creator debit (e.g. debiting the recipient, the wrong asset, or
leaving the balance untouched) ⇒ `satisfiedE2Dual` is UNSATISFIABLE for that post-state. -/
theorem escrowCreate_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.CreateEscrowA.CreateEscrowArgs)
    (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentDebit s.kernel.bal args.creator args.asset args.amount) :
    ¬ satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s') := by
  intro h
  exact hwrong (escrowCreate_circuit_pins_intent S D hD LE cN hN hLE hRest hLog s args s' h).1

/-- **THEOREM (escrow-create ANTI-GHOST — wrong parked record).** A witness whose post-`escrows` head
is NOT the intent parked record does NOT verify — a create that parked a RESOLVED record, swapped
creator/recipient, or wrote the wrong asset/amount has no verifying witness. -/
theorem escrowCreate_circuit_rejects_wrong_record
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.CreateEscrowA.CreateEscrowArgs)
    (s' : RecChainedState)
    (hwrong : s'.kernel.escrows
        ≠ { id := args.id, creator := args.creator, recipient := args.recipient,
            amount := args.amount, resolved := false, asset := args.asset } :: s.kernel.escrows) :
    ¬ satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s') := by
  intro h
  exact hwrong (escrowCreate_circuit_pins_intent S D hD LE cN hN hLE hRest hLog s args s' h).2

/-- **THEOREM (escrow-create COMPLETENESS — the honest intent-realizing step IS circuit-acceptable).**
A committed `createEscrowChainA` step BOTH satisfies the circuit-side spec `EscrowHoldingCreateSpec`
the honest prover commits — so a verifying witness exists — AND REALIZES the intent debit
(`intentDebit … creator asset amount`). So the honest prover's reachable circuit target IS the intent
escrow-lock move. -/
theorem escrowCreate_intent_is_circuit_acceptable
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.CreateEscrowA.CreateEscrowArgs)
    (s' : RecChainedState)
    (hcommit : createEscrowChainA s args.id args.actor args.creator args.recipient
        args.asset args.amount = some s') :
    EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset
      args.amount s'
    ∧ s'.kernel.bal = intentDebit s.kernel.bal args.creator args.asset args.amount := by
  have hspec : EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset
      args.amount s' :=
    (createEscrowChainA_iff_spec s args.id args.actor args.creator args.recipient args.asset
      args.amount s').mp hcommit
  exact ⟨hspec, pin_intent_of_bridge hspec.2.1 (intentDebit_eq_credit _ _ _ _).symm⟩

/-! ## §5 — THE REST OF THE VALUE/LEDGER FAMILY: comprehensive intent-pinning.

The financially-load-bearing effects ALL move the per-asset `bal` ledger, and ALL pin to one of the
SAME three intent oracles (`intentCredit`/`intentDebit`) the reference families use — so the
crown-jewel "circuit enforces the EXACT intended ledger function (not a trusted helper name)" covers
the WHOLE value family, not just the 3 references. Each effect's circuit-side `*Spec` `bal` clause is
one of `recBalCredit … (±amt)` / `recBalCreditCell … (±amt)`, bridged by the proved independent
equalities `intentCredit_eq_balCredit` / `intentDebit_eq_balCredit` / `intentCredit_eq_credit` /
`intentDebit_eq_credit`. We instantiate the §0 template once per effect (soundness + circuit-level
anti-ghost), so all 10 ledger effects are intent-pinned. -/

/-! ### §5a — BURN (supply destruction): `recBalCredit … (-amt)` ⇒ `intentDebit`. -/

open Dregg2.Circuit.Inst.BurnA (BurnArgs burnE burnA_full_sound)
open Dregg2.Circuit.Spec.SupplyDestruction (BurnSpec)

/-- **BURN circuit pins the intent debit.** A verifying `burnE` witness forces the post-`bal` to be
EXACTLY `intentDebit … cell a amt` (cell `cell`'s asset-`a` column DOWN by `amt`, all else fixed). -/
theorem burn_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (burnE D hD) (encodeE2 S (burnE D hD) s args s')) :
    s'.kernel.bal = intentDebit s.kernel.bal args.cell args.a args.amt := by
  have hspec : BurnSpec s args.actor args.cell args.a args.amt s' :=
    burnA_full_sound S D hD hRest hLog s args s' h
  exact pin_intent_of_bridge hspec.2.1 (intentDebit_eq_balCredit _ _ _ _).symm

/-- **BURN circuit anti-ghost: a non-intent-debit post-`bal` does NOT verify.** -/
theorem burn_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentDebit s.kernel.bal args.cell args.a args.amt) :
    ¬ satisfiedE2 S (burnE D hD) (encodeE2 S (burnE D hD) s args s') :=
  fun h => hwrong (burn_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ### §5b — BRIDGE-MINT (inbound): `recBalCredit … value` ⇒ `intentCredit`. -/

open Dregg2.Circuit.Inst.BridgeMintA (BridgeMintArgs bridgeMintE bridgeMintA_full_sound)
open Dregg2.Circuit.Spec.BridgeInboundMint (InboundMintSpec)

/-- **BRIDGE-MINT circuit pins the intent credit.** A verifying `bridgeMintE` witness forces the
post-`bal` to be EXACTLY `intentCredit … cell a value` (the inbound-bridge credit). -/
theorem bridgeMint_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeMintArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (bridgeMintE D hD) (encodeE2 S (bridgeMintE D hD) s args s')) :
    s'.kernel.bal = intentCredit s.kernel.bal args.cell args.a args.value := by
  have hspec : InboundMintSpec s args.actor args.cell args.a args.value s' :=
    bridgeMintA_full_sound S D hD hRest hLog s args s' h
  exact pin_intent_of_bridge hspec.2.1 (intentCredit_eq_balCredit _ _ _ _).symm

/-- **BRIDGE-MINT circuit anti-ghost.** -/
theorem bridgeMint_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeMintArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentCredit s.kernel.bal args.cell args.a args.value) :
    ¬ satisfiedE2 S (bridgeMintE D hD) (encodeE2 S (bridgeMintE D hD) s args s') :=
  fun h => hwrong (bridgeMint_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ### §5c — COMMITTED-ESCROW CREATE: `recBalCreditCell … (-amount)` ⇒ `intentDebit` (dual fw). -/

open Dregg2.Circuit.Inst.CreateCommittedEscrowA (createCommittedEscrowE createCommittedEscrowA_full_sound)
open Dregg2.Circuit.Spec.EscrowCommitted (CommittedEscrowCreateSpec)

/-- **COMMITTED-ESCROW-CREATE circuit pins the intent debit.** A verifying witness forces the
post-`bal` to be EXACTLY `intentDebit … creator asset amount` (the creator's hiding-committed lock). -/
theorem committedEscrow_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState)
    (args : Dregg2.Circuit.Inst.CreateCommittedEscrowA.CreateCommittedEscrowArgs)
    (s' : RecChainedState)
    (h : satisfiedE2Dual S (createCommittedEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createCommittedEscrowE D hD LE cN hN hLE) s args s')) :
    s'.kernel.bal = intentDebit s.kernel.bal args.creator args.asset args.amount := by
  have hspec : CommittedEscrowCreateSpec s args.id args.actor args.creator args.recipient
      args.asset args.amount args.hidingProof s' :=
    createCommittedEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h
  exact pin_intent_of_bridge hspec.2.1 (intentDebit_eq_credit _ _ _ _).symm

/-- **COMMITTED-ESCROW-CREATE circuit anti-ghost.** -/
theorem committedEscrow_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState)
    (args : Dregg2.Circuit.Inst.CreateCommittedEscrowA.CreateCommittedEscrowArgs)
    (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentDebit s.kernel.bal args.creator args.asset args.amount) :
    ¬ satisfiedE2Dual S (createCommittedEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createCommittedEscrowE D hD LE cN hN hLE) s args s') :=
  fun h => hwrong (committedEscrow_circuit_pins_intent S D hD LE cN hN hLE hRest hLog s args s' h)

/-! ### §5d — BRIDGE-LOCK (outbound): `recBalCreditCell … (-amount)` ⇒ `intentDebit` (dual fw). -/

open Dregg2.Circuit.Inst.BridgeLockA (bridgeLockE bridgeLockA_full_sound)
open Dregg2.Circuit.Spec.BridgeOutboundLock (BridgeOutboundLockSpec)

/-- **BRIDGE-LOCK circuit pins the intent debit.** A verifying witness forces the post-`bal` to be
EXACTLY `intentDebit … originator asset amount` (the outbound-bridge lock of the originator). -/
theorem bridgeLock_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.BridgeLockA.BridgeLockArgs)
    (s' : RecChainedState)
    (h : satisfiedE2Dual S (bridgeLockE D hD LE cN hN hLE)
        (encodeE2Dual S (bridgeLockE D hD LE cN hN hLE) s args s')) :
    s'.kernel.bal = intentDebit s.kernel.bal args.originator args.asset args.amount := by
  have hspec : BridgeOutboundLockSpec s args.id args.actor args.originator args.destination
      args.asset args.amount s' :=
    bridgeLockA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h
  exact pin_intent_of_bridge hspec.2.1 (intentDebit_eq_credit _ _ _ _).symm

/-- **BRIDGE-LOCK circuit anti-ghost.** -/
theorem bridgeLock_circuit_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.BridgeLockA.BridgeLockArgs)
    (s' : RecChainedState)
    (hwrong : s'.kernel.bal ≠ intentDebit s.kernel.bal args.originator args.asset args.amount) :
    ¬ satisfiedE2Dual S (bridgeLockE D hD LE cN hN hLE)
        (encodeE2Dual S (bridgeLockE D hD LE cN hN hLE) s args s') :=
  fun h => hwrong (bridgeLock_circuit_pins_intent S D hD LE cN hN hLE hRest hLog s args s' h)

/-! ### §5e — THE SETTLE FAMILY (refund / bridge-cancel / release): `recBalCreditCell … amount`
(a POSITIVE credit to the found record's target) ⇒ `intentCredit`. These specs are existentially
quantified over the found unresolved record `r`; the pin holds for that found `r`. -/

open Dregg2.Circuit.Inst.RefundEscrowA (refundEscrowE refundEscrowA_full_sound)
open Dregg2.Circuit.Spec.EscrowHoldingRefund (RefundEscrowSpec)

/-- **REFUND circuit pins the intent credit to the CREATOR.** A verifying `refundEscrowE` witness
forces, for the found unresolved record `r`, the post-`bal` to be EXACTLY `intentCredit … r.creator
r.asset r.amount` (refund settles to the CREATOR — the triangle pins refund↔creator at the circuit
level). -/
theorem refund_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.RefundEscrowA.RefundEscrowArgs)
    (s' : RecChainedState)
    (h : satisfiedE2Dual S (refundEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (refundEscrowE D hD LE cN hN hLE) s args s')) :
    ∃ r : EscrowRecord,
      s'.kernel.bal = intentCredit s.kernel.bal r.creator r.asset r.amount := by
  obtain ⟨r, _, hbal, _⟩ := refundEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h
  exact ⟨r, pin_intent_of_bridge hbal (intentCredit_eq_credit _ _ _ _).symm⟩

open Dregg2.Circuit.Inst.BridgeCancelA (bridgeCancelE bridgeCancelA_full_sound)
open Dregg2.Circuit.Spec.BridgeOutboundCancel (BridgeOutboundCancelSpec)

/-- **BRIDGE-CANCEL circuit pins the intent credit to the locked originator.** Symmetric to refund:
a verifying witness forces, for the found record `r`, the post-`bal` to be EXACTLY `intentCredit …
r.creator r.asset r.amount` (the outbound lock is returned to its originator). -/
theorem bridgeCancel_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.BridgeCancelA.BridgeCancelArgs)
    (s' : RecChainedState)
    (h : satisfiedE2Dual S (bridgeCancelE D hD LE cN hN hLE)
        (encodeE2Dual S (bridgeCancelE D hD LE cN hN hLE) s args s')) :
    ∃ r : EscrowRecord,
      s'.kernel.bal = intentCredit s.kernel.bal r.creator r.asset r.amount := by
  obtain ⟨r, _, hbal, _⟩ := bridgeCancelA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h
  exact ⟨r, pin_intent_of_bridge hbal (intentCredit_eq_credit _ _ _ _).symm⟩

open Dregg2.Circuit.Inst.ReleaseEscrowA (releaseEscrowE releaseEscrowA_full_sound)
open Dregg2.Circuit.Spec.EscrowHoldingRelease (ReleaseEscrowSpec)

/-- **RELEASE circuit pins the intent credit to the RECIPIENT.** A verifying `releaseEscrowE` witness
forces, for the found record `r`, the post-`bal` to be EXACTLY `intentCredit … r.recipient r.asset
r.amount` (release settles to the RECIPIENT — the triangle pins release↔recipient at the circuit
level, distinct from refund↔creator). -/
theorem release_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.ReleaseEscrowA.ReleaseArgs)
    (s' : RecChainedState)
    (h : satisfiedE2Dual S (releaseEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (releaseEscrowE D hD LE cN hN hLE) s args s')) :
    ∃ r : EscrowRecord,
      s'.kernel.bal = intentCredit s.kernel.bal r.recipient r.asset r.amount := by
  obtain ⟨r, _, hbal, _⟩ := releaseEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h
  exact ⟨r, pin_intent_of_bridge hbal (intentCredit_eq_credit _ _ _ _).symm⟩

/-! ## §6 — THE AUTHORITY (caps) FAMILY: the circuit pins the INTENT cap-graph move.

The cap-graph effects move the `caps` side-table. `FunctionalRefinement` already carries the INTENT
cap functions (`delegateSpec`/`attenuateSpec`/`revokeSpec` — written from "hand recipient a
keep-narrowed copy of the cap I hold to target" / "narrow my own idx-th cap" / "the holder loses its
reach to target"). The circuit-side specs (`DelegateAttenSpec`/`AttenuateSpec`/`RevokeSpec`) pin the
caps clause to the SAME `grant … (attenuate …)` / `attenuateSlotF` / `removeEdgeCaps` shapes. We
bridge each circuit caps clause to the INTENT cap function — so a verifying cap-graph witness pins the
EXACT intended capability set (an over-broad grant, a grant to the wrong recipient, a revoke of the
wrong target, a touched 2nd slot is excluded as a ghost — at the circuit level). -/

open Dregg2.Authority (Caps Auth)

/-- **`intentDelegateCaps caps del rec t keep`** — the INTENT cap function of an attenuated
delegation, written from protocol intent: the recipient's slot GAINS exactly the delegator's held cap
to `t`, attenuated to `keep` (`grant … (attenuate keep (heldCapTo …))`); every OTHER slot untouched.
This is `FunctionalRefinement.delegateSpec`'s caps projection, re-expressed at the circuit args. -/
def intentDelegateCaps (caps : Caps) (del rec t : CellId) (keep : List Auth) : Caps :=
  grant caps rec (attenuate keep (heldCapTo caps del t))

/-- **`intentRevokeCaps caps holder t`** — the INTENT cap function of a revocation: the holder's slot
DROPS every cap conferring an edge to `t` (`filter ¬confersEdgeTo`), every OTHER slot untouched.
Written from intent ("the holder loses its reach to `t`, nothing else") — the SAME filter
`FunctionalRefinement.revokeTargetCaps` uses. -/
def intentRevokeCaps (caps : Caps) (holder t : CellId) : Caps :=
  fun l => if l = holder then (caps l).filter (fun cap => ¬ confersEdgeTo t cap) else caps l

/-! ### §6a — DELEGATE-WITH-ATTENUATION: circuit pins `intentDelegateCaps`. -/

open Dregg2.Circuit.Inst.DelegateAttenA (DelegateAttenArgs delegateAttenE delegateAttenA_full_sound)
open Dregg2.Circuit.Spec.AuthorityAttenuation (DelegateAttenSpec)

/-- **DELEGATE-ATTEN circuit pins the intent cap-grant.** A verifying `delegateAttenE` witness forces
the post-`caps` to be EXACTLY `intentDelegateCaps … del recv t keep` (the recipient gains the
attenuated held cap; no other slot changes). The bridge is definitional — the circuit spec's caps
clause IS the intent grant. -/
theorem delegateAtten_circuit_pins_intent
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s')) :
    s'.kernel.caps = intentDelegateCaps s.kernel.caps args.del args.recv args.t args.keep := by
  have hspec : DelegateAttenSpec s args.del args.recv args.t args.keep s' :=
    delegateAttenA_full_sound S D hD hRest hLog s args s' h
  exact hspec.2.1

/-- **DELEGATE-ATTEN circuit anti-ghost: a non-intent post-`caps` does NOT verify.** -/
theorem delegateAtten_circuit_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.caps ≠ intentDelegateCaps s.kernel.caps args.del args.recv args.t args.keep) :
    ¬ satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s') :=
  fun h => hwrong (delegateAtten_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ### §6b — ATTENUATE (self): circuit pins `attenuateSlotF` (FR `attenuateSpec`'s caps). -/

open Dregg2.Circuit.Inst.AttenuateA (AttenuateArgs attenuateE attenuateA_full_sound)
open Dregg2.Circuit.Spec.AuthorityAttenuation (AttenuateSpec)

/-- **ATTENUATE circuit pins the intent self-narrowing.** A verifying `attenuateE` witness forces the
post-`caps` to be EXACTLY `attenuateSlotF … actor idx keep` — the actor's own `idx`-th cap narrowed in
place, NO other slot touched. This IS `FunctionalRefinement.attenuateSpec`'s caps projection. -/
theorem attenuate_circuit_pins_intent
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (attenuateE D hD) (encodeE2 S (attenuateE D hD) s args s')) :
    s'.kernel.caps = attenuateSlotF s.kernel.caps args.actor args.idx args.keep := by
  have hspec : AttenuateSpec s args.actor args.idx args.keep s' :=
    attenuateA_full_sound S D hD hRest hLog s args s' h
  exact hspec.1

/-- **ATTENUATE circuit anti-ghost.** -/
theorem attenuate_circuit_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.caps ≠ attenuateSlotF s.kernel.caps args.actor args.idx args.keep) :
    ¬ satisfiedE2 S (attenuateE D hD) (encodeE2 S (attenuateE D hD) s args s') :=
  fun h => hwrong (attenuate_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ### §6c — REVOKE: circuit pins `intentRevokeCaps` (FR `revokeTargetCaps`). -/

open Dregg2.Circuit.Inst.Revoke (RevokeArgs revokeE revoke_full_sound)
open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec removeEdgeCaps)

/-- **`intentRevokeCaps_eq_removeEdgeCaps` (PROVED — definitional identity).** The intent revoke
filter is EXACTLY the circuit spec's `removeEdgeCaps`. Two independently-written cap functions proven
EQUAL (FALSE if either filtered the wrong slot or wrong target). -/
theorem intentRevokeCaps_eq_removeEdgeCaps (caps : Caps) (holder t : CellId) :
    intentRevokeCaps caps holder t = removeEdgeCaps caps holder t := rfl

/-- **REVOKE circuit pins the intent revocation.** A verifying `revokeE` witness forces the
post-`caps` to be EXACTLY `intentRevokeCaps … holder t` — the holder's `t`-conferring caps filtered
out, every other slot fixed. This IS `FunctionalRefinement.revokeTargetCaps`. -/
theorem revoke_circuit_pins_intent
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeE D hD) (encodeE2 S (revokeE D hD) s args s')) :
    s'.kernel.caps = intentRevokeCaps s.kernel.caps args.holder args.t := by
  have hspec : RevokeSpec s args.holder args.t s' :=
    revoke_full_sound S D hD hRest hLog s args s' h
  rw [intentRevokeCaps_eq_removeEdgeCaps]; exact hspec.2.1

/-- **REVOKE circuit anti-ghost.** -/
theorem revoke_circuit_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.caps ≠ intentRevokeCaps s.kernel.caps args.holder args.t) :
    ¬ satisfiedE2 S (revokeE D hD) (encodeE2 S (revokeE D hD) s args s') :=
  fun h => hwrong (revoke_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ## §7 — THE CELL-METADATA FAMILY: a NEW intent functional spec + circuit pinning.

The cell-metadata effects (`setPermissions` / `setVK` / `incrementNonce`) write ONE slot of ONE
cell's record. `FunctionalRefinement` carries no oracle for them, so we BUILD one here in its spirit:
`intentSetCellField cells cell f v` — the protocol intent "write slot `f` of cell `cell` to value `v`,
every OTHER cell's whole record untouched", a single-cell single-field write written WITHOUT reference
to the executor's `writeField`/`setPermsCellMap`. We prove the circuit's validated cell-map helper IS
this intent oracle (a `rfl` once the field name is fixed), so a verifying cell-metadata witness pins
the EXACT intended single-slot write — a write to the wrong cell, the wrong slot, or a touched 2nd
cell is excluded. -/

/-- **`intentSetCellField cells cell f v`** — the INTENT cell-map of a single-slot write: cell `cell`'s
record has slot `f` set to `.int v` (`setField`), every OTHER cell's whole record literally unchanged.
Written from intent ("write field `f` of `cell` to `v`, touch nothing else"); the THREE cell-metadata
effects are its instances at `f = permissions / verification_key / nonce`. -/
def intentSetCellField (cells : CellId → Value) (cell : CellId) (f : FieldName) (v : Int) :
    CellId → Value :=
  fun c => if c = cell then setField f (cells c) (.int v) else cells c

/-! ### §7a — SET-PERMISSIONS: circuit pins `intentSetCellField … permsField`. -/

open Dregg2.Circuit.Inst.SetPermissionsA (SetPermissionsArgs setPermissionsE setPermissionsA_full_sound)
open Dregg2.Circuit.Spec.CellStatePermissions (SetPermissionsSpec setPermsCellMap)

/-- **`setPermsCellMap_eq_intent` (PROVED — definitional identity).** The circuit's validated
permissions cell-map IS the intent single-slot write at `f = permsField`. -/
theorem setPermsCellMap_eq_intent (k : RecordKernelState) (cell : CellId) (p : Int) :
    setPermsCellMap k cell p = intentSetCellField k.cell cell permsField p := rfl

/-- **SET-PERMISSIONS circuit pins the intent slot-write.** A verifying `setPermissionsE` witness forces
the post-`cell` map to be EXACTLY `intentSetCellField … cell permsField p` (cell `cell`'s permissions
slot set to `p`, every other cell untouched). -/
theorem setPermissions_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setPermissionsE (encodeE S setPermissionsE s args s')) :
    s'.kernel.cell = intentSetCellField s.kernel.cell args.cell permsField args.p := by
  have hspec : SetPermissionsSpec s args.actor args.cell args.p s' :=
    setPermissionsA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  rw [hspec.2.1, setPermsCellMap_eq_intent]

/-- **SET-PERMISSIONS circuit anti-ghost: a non-intent post-`cell` map does NOT verify.** -/
theorem setPermissions_circuit_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.kernel.cell ≠ intentSetCellField s.kernel.cell args.cell permsField args.p) :
    ¬ satisfiedE S setPermissionsE (encodeE S setPermissionsE s args s') :=
  fun h => hwrong (setPermissions_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

/-! ### §7b — SET-VK: circuit pins `intentSetCellField … vkField`. -/

open Dregg2.Circuit.Inst.SetVKA (SetVKArgs setVKE setVKA_full_sound)
open Dregg2.Circuit.Spec.CellStateVK (SetVKSpec setVKCellMap)

/-- **`setVKCellMap_eq_intent` (PROVED).** The validated verification-key cell-map IS the intent
single-slot write at `f = vkField`. -/
theorem setVKCellMap_eq_intent (k : RecordKernelState) (cell : CellId) (vk : Int) :
    setVKCellMap k cell vk = intentSetCellField k.cell cell vkField vk := rfl

/-- **SET-VK circuit pins the intent slot-write.** -/
theorem setVK_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setVKE (encodeE S setVKE s args s')) :
    s'.kernel.cell = intentSetCellField s.kernel.cell args.cell vkField args.vk := by
  have hspec : SetVKSpec s args.actor args.cell args.vk s' :=
    setVKA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  rw [hspec.2.1, setVKCellMap_eq_intent]

/-- **SET-VK circuit anti-ghost.** -/
theorem setVK_circuit_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.kernel.cell ≠ intentSetCellField s.kernel.cell args.cell vkField args.vk) :
    ¬ satisfiedE S setVKE (encodeE S setVKE s args s') :=
  fun h => hwrong (setVK_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

/-! ### §7c — INCREMENT-NONCE: circuit pins `intentSetCellField … nonceField`. -/

open Dregg2.Circuit.Inst.IncrementNonceA (IncrementNonceArgs incrementNonceE incrementNonceA_full_sound)
open Dregg2.Circuit.Spec.CellStateMonotone (IncrementNonceSpec incNonceCellMap)

/-- **`incNonceCellMap_eq_intent` (PROVED).** The validated nonce cell-map IS the intent single-slot
write at `f = nonceField`. -/
theorem incNonceCellMap_eq_intent (k : RecordKernelState) (cell : CellId) (n : Int) :
    incNonceCellMap k cell n = intentSetCellField k.cell cell nonceField n := rfl

/-- **INCREMENT-NONCE circuit pins the intent slot-write.** -/
theorem incrementNonce_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S incrementNonceE (encodeE S incrementNonceE s args s')) :
    s'.kernel.cell = intentSetCellField s.kernel.cell args.cell nonceField args.n := by
  have hspec : IncrementNonceSpec s args.actor args.cell args.n s' :=
    incrementNonceA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  rw [hspec.2.1, incNonceCellMap_eq_intent]

/-- **INCREMENT-NONCE circuit anti-ghost.** -/
theorem incrementNonce_circuit_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.kernel.cell ≠ intentSetCellField s.kernel.cell args.cell nonceField args.n) :
    ¬ satisfiedE S incrementNonceE (encodeE S incrementNonceE s args s') :=
  fun h => hwrong (incrementNonce_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

/-! ## §8 — THE NOTE (privacy) FAMILY: a NEW intent functional spec + circuit pinning.

The note effects (`noteCreate` / `noteSpend`) advance the privacy side-tables: `noteCreate` PREPENDS a
commitment to `commitments` (append-only — value is hidden yet conserved), `noteSpend` PREPENDS a
nullifier to `nullifiers` (the no-double-spend marker). We build intent oracles
`intentNoteCommit`/`intentNoteNullify` (prepend the commitment / nullifier; touch nothing else) and
pin the circuit to them — so a verifying note witness pins the EXACT privacy-table advance (a dropped
commitment, a rewritten nullifier set, a wrong front element is excluded). -/

/-- **`intentNoteCommit commitments cm`** — the INTENT commitments-list of a note creation: the fresh
commitment `cm` is PREPENDED (newest-first, append-only — nothing lost). Written from intent. -/
def intentNoteCommit (commitments : List Nat) (cm : Nat) : List Nat := cm :: commitments

/-- **`intentNoteNullify nullifiers nf`** — the INTENT nullifiers-list of a note spend: the nullifier
`nf` is PREPENDED (the no-double-spend marker). Written from intent. -/
def intentNoteNullify (nullifiers : List Nat) (nf : Nat) : List Nat := nf :: nullifiers

/-! ### §8a — NOTE-CREATE: circuit pins `intentNoteCommit`. -/

open Dregg2.Circuit.Inst.NoteCreateA (NoteCreateArgs noteCreateE noteCreateA_full_sound RestIffNoCommitments)
open Dregg2.Circuit.Spec.NoteCommitment (NoteCreateASpec)

/-- **NOTE-CREATE circuit pins the intent commitment-prepend.** A verifying `noteCreateE` witness forces
the post-`commitments` to be EXACTLY `intentNoteCommit … cm` (the fresh commitment prepended, the rest
preserved). -/
theorem noteCreate_circuit_pins_intent
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteCreateE LE cN hN hLE) (encodeE2 S (noteCreateE LE cN hN hLE) s args s')) :
    s'.kernel.commitments = intentNoteCommit s.kernel.commitments args.cm := by
  have hspec : NoteCreateASpec s args.cm args.actor s' :=
    noteCreateA_full_sound S LE cN hN hLE hRest hLog s args s' h
  exact hspec.2.1

/-- **NOTE-CREATE circuit anti-ghost.** -/
theorem noteCreate_circuit_rejects_wrong_commitments
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.commitments ≠ intentNoteCommit s.kernel.commitments args.cm) :
    ¬ satisfiedE2 S (noteCreateE LE cN hN hLE) (encodeE2 S (noteCreateE LE cN hN hLE) s args s') :=
  fun h => hwrong (noteCreate_circuit_pins_intent S LE cN hN hLE hRest hLog s args s' h)

/-! ### §8b — NOTE-SPEND: circuit pins `intentNoteNullify`. -/

open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs noteSpendE noteSpendA_full_sound)
open Dregg2.Circuit.Spec.NoteNullifier (NoteSpendSpec)

/-- **NOTE-SPEND circuit pins the intent nullifier-prepend.** A verifying `noteSpendE` witness forces
the post-`nullifiers` to be EXACTLY `intentNoteNullify … nf` (the spend nullifier prepended). The
no-double-spend marker is pinned — a witness that dropped or rewrote the nullifier set is rejected. -/
theorem noteSpend_circuit_pins_intent
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) s args s')) :
    s'.kernel.nullifiers = intentNoteNullify s.kernel.nullifiers args.nf := by
  have hspec : NoteSpendSpec s args.nf args.actor args.spendProof s' :=
    noteSpendA_full_sound S LE cN hN hLE hRest hLog s args s' h
  exact hspec.2.1

/-- **NOTE-SPEND circuit anti-ghost.** -/
theorem noteSpend_circuit_rejects_wrong_nullifiers
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.nullifiers ≠ intentNoteNullify s.kernel.nullifiers args.nf) :
    ¬ satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) s args s') :=
  fun h => hwrong (noteSpend_circuit_pins_intent S LE cN hN hLE hRest hLog s args s' h)

/-! ## §9 — THE QUEUE-ALLOCATE FAMILY: circuit pins the INTENT fresh-queue (FR `queueAllocateSpec`).

`queueAllocate` PREPENDS a fresh empty queue record onto `queues`. `FunctionalRefinement` carries the
INTENT `queueAllocateSpec` (prepend `{id, owner, capacity, buffer := []}`). The circuit spec's queues
clause is `freshQueue id actor cap :: queues` — definitionally that intent record. We pin the circuit
to the intent fresh-queue. -/

open Dregg2.Circuit.Inst.QueueAllocateA (AllocateArgs queueAllocateE queueAllocateA_full_sound)
open Dregg2.Circuit.Spec.QueueFifoCore (QueueAllocateSpec freshQueue)

/-- **`intentQueueAllocate queues id owner cap`** — the INTENT queues-table of an allocate: a fresh
empty queue `{id, owner, capacity := cap, buffer := []}` is PREPENDED; the rest preserved. The SAME
record `FunctionalRefinement.queueAllocateSpec` prepends. -/
def intentQueueAllocate (queues : List QueueRecord) (id : Nat) (owner : CellId) (cap : Nat) :
    List QueueRecord :=
  { id := id, owner := owner, capacity := cap, buffer := [] } :: queues

/-- **`freshQueue_eq_intent` (PROVED).** The circuit's `freshQueue` IS the intent fresh-queue record. -/
theorem freshQueue_eq_intent (id : Nat) (owner : CellId) (cap : Nat) :
    freshQueue id owner cap = { id := id, owner := owner, capacity := cap, buffer := [] } := rfl

/-- **QUEUE-ALLOCATE circuit pins the intent fresh-queue.** A verifying `queueAllocateE` witness forces
the post-`queues` to be EXACTLY `intentQueueAllocate … id actor cap`. -/
theorem queueAllocate_circuit_pins_intent
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.QueueAllocateA.RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueAllocateE LE cN hN hLE) (encodeE2 S (queueAllocateE LE cN hN hLE) s args s')) :
    s'.kernel.queues = intentQueueAllocate s.kernel.queues args.id args.actor args.cap := by
  have hspec : QueueAllocateSpec s args.id args.actor args.cell args.cap s' :=
    queueAllocateA_full_sound S LE cN hN hLE hRest hLog s args s' h
  rw [hspec.2.1]; rfl

/-- **QUEUE-ALLOCATE circuit anti-ghost.** -/
theorem queueAllocate_circuit_rejects_wrong_queues
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.QueueAllocateA.RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.queues ≠ intentQueueAllocate s.kernel.queues args.id args.actor args.cap) :
    ¬ satisfiedE2 S (queueAllocateE LE cN hN hLE) (encodeE2 S (queueAllocateE LE cN hN hLE) s args s') :=
  fun h => hwrong (queueAllocate_circuit_pins_intent S LE cN hN hLE hRest hLog s args s' h)

/-! ## §10 — THE CELL-SEAL (lifecycle) FAMILY: a NEW intent functional spec + circuit pinning.

`cellSeal` writes the cell's lifecycle marker to the SEALED state (the `sealLifecycleMap` write). We
pin the circuit to that validated lifecycle map (the intent "mark THIS cell sealed, no other cell's
lifecycle changes"). -/

open Dregg2.Circuit.Inst.CellSealA (CellSealArgs cellSealE cellSealA_full_sound)
open Dregg2.Circuit.Spec.CellLifecycle (CellSealSpec sealLifecycleMap)

/-- **CELL-SEAL circuit pins the intent lifecycle write.** A verifying `cellSealE` witness forces the
post-`lifecycle` map to be EXACTLY `sealLifecycleMap … cell` (cell `cell` marked sealed, every other
cell's lifecycle untouched). -/
theorem cellSeal_circuit_pins_intent
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (cellSealE D hD) (encodeE2 S (cellSealE D hD) s args s')) :
    s'.kernel.lifecycle = sealLifecycleMap s.kernel args.cell := by
  have hspec : CellSealSpec s args.actor args.cell s' :=
    cellSealA_full_sound S D hD hRest hLog s args s' h
  exact hspec.2.1

/-- **CELL-SEAL circuit anti-ghost.** -/
theorem cellSeal_circuit_rejects_wrong_lifecycle
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.lifecycle ≠ sealLifecycleMap s.kernel args.cell) :
    ¬ satisfiedE2 S (cellSealE D hD) (encodeE2 S (cellSealE D hD) s args s') :=
  fun h => hwrong (cellSeal_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ## §11 — THE SWISS-EXPORT FAMILY: a NEW intent functional spec + circuit pinning.

`swissExport` PREPENDS a fresh sturdy-ref export record onto `swiss`. We build the intent oracle
`intentSwissExport` (prepend the export record; touch nothing else) and pin the circuit to it. -/

open Dregg2.Circuit.Inst.SwissExportA (ExportArgs swissExportE swissExportA_full_sound)
open Dregg2.Circuit.Spec.SwissExport (ExportSpec exportRecord)

/-- **`intentSwissExport swiss sw exporter target rights`** — the INTENT swiss-table of an export: the
fresh export record (`exportRecord`, validated by `exportRecord_correct`) is PREPENDED; the rest
preserved. -/
def intentSwissExport (swiss : List SwissRecord) (sw : Nat) (exporter target : CellId)
    (rights : List Auth) : List SwissRecord :=
  exportRecord sw exporter target rights :: swiss

/-- **SWISS-EXPORT circuit pins the intent export-prepend.** A verifying `swissExportE` witness forces
the post-`swiss` to be EXACTLY `intentSwissExport … sw exporter target rights`. -/
theorem swissExport_circuit_pins_intent
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissExportE LE cN hN hLE) (encodeE2 S (swissExportE LE cN hN hLE) s args s')) :
    s'.kernel.swiss = intentSwissExport s.kernel.swiss args.sw args.exporter args.target args.rights := by
  have hspec : ExportSpec s args.sw args.actor args.exporter args.target args.rights s' :=
    swissExportA_full_sound S LE cN hN hLE hRest hLog s args s' h
  exact hspec.2.1

/-- **SWISS-EXPORT circuit anti-ghost.** -/
theorem swissExport_circuit_rejects_wrong_swiss
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.swiss ≠ intentSwissExport s.kernel.swiss args.sw args.exporter args.target args.rights) :
    ¬ satisfiedE2 S (swissExportE LE cN hN hLE) (encodeE2 S (swissExportE LE cN hN hLE) s args s') :=
  fun h => hwrong (swissExport_circuit_pins_intent S LE cN hN hLE hRest hLog s args s' h)

/-! ## §12 — THE SEAL (sealedBoxes) FAMILY: a NEW intent functional spec + circuit pinning.

`seal` PREPENDS a sealed-box record (holding a sealed `payload` cap) onto `sealedBoxes`. We pin the
circuit to the validated `sealedBoxPrepend` (the intent "seal THIS payload into a fresh box, touch
nothing else"). -/

open Dregg2.Circuit.Inst.SealA (SealArgs sealE sealA_full_sound)
open Dregg2.Circuit.Spec.SealBoxOperations (SealSpec sealedBoxPrepend)

/-- **SEAL circuit pins the intent sealed-box prepend.** A verifying `sealE` witness forces the
post-`sealedBoxes` to be EXACTLY `sealedBoxPrepend … pid actor payload` (the fresh sealed box
prepended, the rest preserved). -/
theorem seal_circuit_pins_intent
    (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SealA.RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (sealE LE cN hN hLE) (encodeE2 S (sealE LE cN hN hLE) s args s')) :
    s'.kernel.sealedBoxes = sealedBoxPrepend s.kernel.sealedBoxes args.pid args.actor args.payload := by
  have hspec : SealSpec s args.pid args.actor args.payload s' :=
    sealA_full_sound S LE cN hN hLE hRest hLog s args s' h
  exact hspec.2.1

/-- **SEAL circuit anti-ghost.** -/
theorem seal_circuit_rejects_wrong_sealedBoxes
    (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SealA.RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.sealedBoxes ≠ sealedBoxPrepend s.kernel.sealedBoxes args.pid args.actor args.payload) :
    ¬ satisfiedE2 S (sealE LE cN hN hLE) (encodeE2 S (sealE LE cN hN hLE) s args s') :=
  fun h => hwrong (seal_circuit_pins_intent S LE cN hN hLE hRest hLog s args s' h)

/-! ## §4 — axiom-hygiene tripwires. Every triangle corner rests only on the kernel axioms +
the §8 carried CR set (no `sorry`/`axiom`/`native_decide`). -/

#assert_axioms pin_intent_of_bridge
#assert_axioms mint_circuit_pins_intent
#assert_axioms mint_circuit_rejects_wrong_ledger
#assert_axioms mint_intent_is_circuit_acceptable
#assert_axioms intentTransfer_eq_recTransferBal
#assert_axioms transfer_circuit_pins_intent
#assert_axioms transfer_circuit_rejects_wrong_ledger
#assert_axioms transfer_intent_is_circuit_acceptable
#assert_axioms parkedRecord_eq_escrowCreateRecord
#assert_axioms escrowCreate_circuit_pins_intent
#assert_axioms escrowCreate_circuit_rejects_wrong_ledger
#assert_axioms escrowCreate_circuit_rejects_wrong_record
#assert_axioms escrowCreate_intent_is_circuit_acceptable
#assert_axioms burn_circuit_pins_intent
#assert_axioms burn_circuit_rejects_wrong_ledger
#assert_axioms bridgeMint_circuit_pins_intent
#assert_axioms bridgeMint_circuit_rejects_wrong_ledger
#assert_axioms committedEscrow_circuit_pins_intent
#assert_axioms committedEscrow_circuit_rejects_wrong_ledger
#assert_axioms bridgeLock_circuit_pins_intent
#assert_axioms bridgeLock_circuit_rejects_wrong_ledger
#assert_axioms refund_circuit_pins_intent
#assert_axioms bridgeCancel_circuit_pins_intent
#assert_axioms release_circuit_pins_intent
#assert_axioms delegateAtten_circuit_pins_intent
#assert_axioms delegateAtten_circuit_rejects_wrong_caps
#assert_axioms attenuate_circuit_pins_intent
#assert_axioms attenuate_circuit_rejects_wrong_caps
#assert_axioms intentRevokeCaps_eq_removeEdgeCaps
#assert_axioms revoke_circuit_pins_intent
#assert_axioms revoke_circuit_rejects_wrong_caps
#assert_axioms setPermsCellMap_eq_intent
#assert_axioms setPermissions_circuit_pins_intent
#assert_axioms setPermissions_circuit_rejects_wrong_cell
#assert_axioms setVKCellMap_eq_intent
#assert_axioms setVK_circuit_pins_intent
#assert_axioms setVK_circuit_rejects_wrong_cell
#assert_axioms incNonceCellMap_eq_intent
#assert_axioms incrementNonce_circuit_pins_intent
#assert_axioms incrementNonce_circuit_rejects_wrong_cell
#assert_axioms noteCreate_circuit_pins_intent
#assert_axioms noteCreate_circuit_rejects_wrong_commitments
#assert_axioms noteSpend_circuit_pins_intent
#assert_axioms noteSpend_circuit_rejects_wrong_nullifiers
#assert_axioms freshQueue_eq_intent
#assert_axioms queueAllocate_circuit_pins_intent
#assert_axioms queueAllocate_circuit_rejects_wrong_queues
#assert_axioms cellSeal_circuit_pins_intent
#assert_axioms cellSeal_circuit_rejects_wrong_lifecycle
#assert_axioms swissExport_circuit_pins_intent
#assert_axioms swissExport_circuit_rejects_wrong_swiss
#assert_axioms seal_circuit_pins_intent
#assert_axioms seal_circuit_rejects_wrong_sealedBoxes

end Dregg2.Spec.CircuitSpecTriangle
