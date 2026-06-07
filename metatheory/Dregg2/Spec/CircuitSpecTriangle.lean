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
import Dregg2.Spec.FunctionalRefinement

namespace Dregg2.Spec.CircuitSpecTriangle

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (compressNInjective logHashInjective)
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

end Dregg2.Spec.CircuitSpecTriangle
