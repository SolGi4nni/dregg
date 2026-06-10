/-
# Dregg2.Spec.CircuitSpecTriangle — THE CROWN-JEWEL CORNER: circuit⟺(intent-)spec.

This module closes corner **(b)** of the three-corner soundness triangle for the reference effect
families (transfer · mint), connecting the ZK circuit's algebraic statement to the
INDEPENDENT, intent-derived functional spec.

## The three corners

For each effect there is an independent declarative spec, against which we prove BOTH:
  * **(a) executor ⟺ spec** — `Dregg2/Spec/FunctionalRefinement.lean`: the intent functional specs
    (`mintSpec`, …) written field-by-field from protocol intent, with full
    biconditional triangles (`mint_triangle`, …) + anti-ghost teeth.
  * **(b) circuit ⟺ spec** — THIS module: a verifying ZK witness pins the SPEC-correct post-state.

## What corner (b) already had — and the gap it left

The per-effect circuit-soundness theorems (`mintA_full_sound`, `transfer_full_sound`)
prove a satisfying full-state witness yields a *circuit-side* declarative
spec (`MintASpec`, `BalanceMovementSpec`). Those circuit-side specs pin
the post-state in terms of the EXECUTOR'S OWN ledger helpers (`recBalCredit`, `recTransferBal`,
`recBalCreditCell … (-amount)`). That is genuine full-state soundness over the state commitment, but
it leaves one question unanswered: **does the circuit enforce the EXACT function the protocol INTENDS
— the debit-the-creator / credit-this-cell / park-this-record move — or merely "whatever helper the
executor happens to call"?** A reader who does not trust `recBalCredit`'s NAME is not yet served.

## What this module proves (the connection)

For each reference family we prove the circuit's algebraic statement is SUFFICIENT to enforce the
INTENT ledger move, written from protocol intent in `FunctionalRefinement` (`intentCredit`,
`intentDebit`) — NOT from any executor helper:

  * **SOUNDNESS** `*_circuit_pins_intent`: a verifying witness ⇒ the post-`bal` ledger is EXACTLY the
    intent move (`intentCredit`/`intentDebit`/`intentTransfer`). The bridge is the proved
    independent-function equalities
    `intentCredit_eq_balCredit` / `intentDebit_eq_balCredit` / `intentTransfer_eq_recTransferBal`
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
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.exerciseA
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
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.EffectCommit5
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Spec.FunctionalRefinement (intentCredit intentDebit intentCredit_eq_balCredit
  intentDebit_eq_balCredit)

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

/-- **`intentTransfer_eq_recTransferBal` (genuine independent-function equality).** The
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

/-! ## §5 — THE REST OF THE VALUE/LEDGER FAMILY: comprehensive intent-pinning.

The financially-load-bearing effects ALL move the per-asset `bal` ledger, and ALL pin to one of the
SAME intent oracles (`intentCredit`/`intentDebit`) the reference families use — so the
crown-jewel "circuit enforces the EXACT intended ledger function (not a trusted helper name)" covers
the WHOLE value family, not just the references. (The escrow/obligation/bridge-lock families left the
kernel in the dregg3 reduction — re-provided as verified factories in `Dregg2/Apps/` — so the kernel
ledger family is burn + bridge-mint, alongside §1 mint and §2 transfer.) Each effect's circuit-side
`*Spec` `bal` clause is `recBalCredit … (±amt)`, bridged by the proved independent equalities
`intentCredit_eq_balCredit` / `intentDebit_eq_balCredit`. We instantiate the §0 template once per
effect (soundness + circuit-level anti-ghost). -/

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

/-- **`intentRevokeCaps_eq_removeEdgeCaps` (definitional identity).** The intent revoke
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

/-- **`setPermsCellMap_eq_intent` (definitional identity).** The circuit's validated
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

/-- **`setVKCellMap_eq_intent`.** The validated verification-key cell-map IS the intent
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

/-- **`incNonceCellMap_eq_intent`.** The validated nonce cell-map IS the intent single-slot
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

-- (F2a) §9 queue-allocate intent-pinning DELETED with the queue effect family
-- (VerbRegistry `.factory .queue`; behavior = the verified `Dregg2/Apps/QueueFactory`).

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

/-! ## §13 — MORE CAP-GRAPH EFFECTS: drop-ref / revoke-delegation (revocation) and
introduce / validate-handoff (unattenuated delegation) — circuit pins the INTENT cap move.

`revokeDelegation` commits a `RevokeSpec` (the holder loses its reach to `t`), so it
reuses `intentRevokeCaps` (§6c). `introduce` commits a `DelegateSpec` — an
UNATTENUATED Granovetter introduction (the recipient gains the delegator's WHOLE held cap to `t`); we
build `intentIntroduceCaps` for that. (F3: dropRef/validateHandoff died with the
seal/swiss/sturdyref family — caps-in-slots, `Apps/CapSlotFactory.lean`.) -/

open Dregg2.Circuit.Inst.RevokeDelegationA (revokeDelegationE revokeDelegationA_full_sound)
open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec)

/-- **REVOKE-DELEGATION circuit pins the intent revocation.** A verifying `revokeDelegationE` witness
forces the post-`caps` to be EXACTLY `intentRevokeCaps … holder t`. -/
theorem revokeDelegation_circuit_pins_intent
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RevokeDelegationA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s')) :
    s'.kernel.caps = intentRevokeCaps s.kernel.caps args.holder args.t := by
  have hspec : RevokeSpec s args.holder args.t s' :=
    revokeDelegationA_full_sound S D hD hRest hLog s args s' h
  rw [intentRevokeCaps_eq_removeEdgeCaps]; exact hspec.2.1

/-- **REVOKE-DELEGATION circuit anti-ghost.** -/
theorem revokeDelegation_circuit_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RevokeDelegationA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.caps ≠ intentRevokeCaps s.kernel.caps args.holder args.t) :
    ¬ satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s') :=
  fun h => hwrong (revokeDelegation_circuit_pins_intent S D hD hRest hLog s args s' h)

open Dregg2.Circuit.Inst.IntroduceA (IntroduceArgs introduceE introduceA_full_sound)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec recDelegateCaps)

/-- **`intentIntroduceCaps caps del rec t`** — the INTENT cap function of an UNATTENUATED Granovetter
introduction: the recipient's slot GAINS the delegator's WHOLE held cap to `t` (`grant … (heldCapTo
…)` — no attenuation), every other slot untouched. Written from intent ("introduce `rec` to `t` with
my full reach"); the SAME `grant`-of-held-cap the circuit's `recDelegateCaps` installs. -/
def intentIntroduceCaps (caps : Caps) (del rec t : CellId) : Caps :=
  grant caps rec (heldCapTo caps del t)

/-- **`intentIntroduceCaps_eq_recDelegateCaps` (definitional identity).** -/
theorem intentIntroduceCaps_eq_recDelegateCaps (caps : Caps) (del rec t : CellId) :
    intentIntroduceCaps caps del rec t = recDelegateCaps caps del rec t := rfl

/-- **INTRODUCE circuit pins the intent unattenuated introduction.** A verifying `introduceE` witness
forces the post-`caps` to be EXACTLY `intentIntroduceCaps … intro recip t`. -/
theorem introduce_circuit_pins_intent
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.IntroduceA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s')) :
    s'.kernel.caps = intentIntroduceCaps s.kernel.caps args.intro args.recip args.t := by
  have hspec : DelegateSpec s args.intro args.recip args.t s' :=
    introduceA_full_sound S D hD hRest hLog s args s' h
  rw [intentIntroduceCaps_eq_recDelegateCaps]; exact hspec.2.1

/-- **INTRODUCE circuit anti-ghost.** -/
theorem introduce_circuit_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.IntroduceA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.caps ≠ intentIntroduceCaps s.kernel.caps args.intro args.recip args.t) :
    ¬ satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s') :=
  fun h => hwrong (introduce_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ## §15 — CELL-UNSEAL (lifecycle) / REFRESH-DELEGATION (delegations). -/

open Dregg2.Circuit.Inst.CellUnsealA (CellUnsealArgs cellUnsealE cellUnsealA_full_sound)
open Dregg2.Circuit.Spec.CellLifecycle (CellUnsealSpec unsealLifecycleMap)

/-- **CELL-UNSEAL circuit pins the intent lifecycle write.** A verifying `cellUnsealE` witness forces
the post-`lifecycle` map to be EXACTLY `unsealLifecycleMap … cell` (cell `cell` marked unsealed, every
other cell's lifecycle untouched). -/
theorem cellUnseal_circuit_pins_intent
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (cellUnsealE D hD) (encodeE2 S (cellUnsealE D hD) s args s')) :
    s'.kernel.lifecycle = unsealLifecycleMap s.kernel args.cell := by
  have hspec : CellUnsealSpec s args.actor args.cell s' :=
    cellUnsealA_full_sound S D hD hRest hLog s args s' h
  exact hspec.2.1

/-- **CELL-UNSEAL circuit anti-ghost.** -/
theorem cellUnseal_circuit_rejects_wrong_lifecycle
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.lifecycle ≠ unsealLifecycleMap s.kernel args.cell) :
    ¬ satisfiedE2 S (cellUnsealE D hD) (encodeE2 S (cellUnsealE D hD) s args s') :=
  fun h => hwrong (cellUnseal_circuit_pins_intent S D hD hRest hLog s args s' h)

open Dregg2.Circuit.Inst.RefreshDelegationA
  (RefreshDelegationArgs refreshDelegationE refreshDelegationA_full_sound)
open Dregg2.Circuit.Spec.RefreshDelegation (RefreshDelegationSpec refreshDelegationsMap)

/-- **REFRESH-DELEGATION circuit pins the intent delegations write.** A verifying `refreshDelegationE`
witness forces the post-`delegations` map to be EXACTLY `refreshDelegationsMap … child` (the child's
delegation refreshed, every other entry untouched). -/
theorem refreshDelegation_circuit_pins_intent
    (S : Surface2) (D : (CellId → List Dregg2.Authority.Cap) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RefreshDelegationA.RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (refreshDelegationE D hD) (encodeE2 S (refreshDelegationE D hD) s args s')) :
    s'.kernel.delegations = refreshDelegationsMap s.kernel args.child := by
  have hspec : RefreshDelegationSpec s args.actor args.child s' :=
    refreshDelegationA_full_sound S D hD hRest hLog s args s' h
  exact hspec.2.1

/-- **REFRESH-DELEGATION circuit anti-ghost.** -/
theorem refreshDelegation_circuit_rejects_wrong_delegations
    (S : Surface2) (D : (CellId → List Dregg2.Authority.Cap) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RefreshDelegationA.RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.delegations ≠ refreshDelegationsMap s.kernel args.child) :
    ¬ satisfiedE2 S (refreshDelegationE D hD) (encodeE2 S (refreshDelegationE D hD) s args s') :=
  fun h => hwrong (refreshDelegation_circuit_pins_intent S D hD hRest hLog s args s' h)

/-! ## §16 — THE CELL-AUDIT / SOVEREIGN / EMIT-EVENT FAMILY (v1 commit framework).

`receiptArchive` / `refusal` write an AUDIT marker (`.int 1`) to one slot of one cell — an instance of
the §7 `intentSetCellField` oracle (at `f = lifecycle / refusal`, `v = 1`). `makeSovereign` rebinds a
cell to its sovereign-commitment value (`sovereignRebind`). `emitEvent` is LOG-ONLY (the kernel is
frozen; the intent is the receipt-chain advance). We pin each. -/

open Dregg2.Circuit.Inst.ReceiptArchiveA (ReceiptArchiveArgs receiptArchiveE receiptArchiveA_full_sound)
open Dregg2.Circuit.Spec.CellStateAudit (ReceiptArchiveSpec RefusalSpec auditCellMap)

/-- **`auditCellMap_eq_intent`.** The audit cell-map IS the intent slot-write of the marker
`.int 1` at field `f` (an instance of §7's `intentSetCellField`). -/
theorem auditCellMap_eq_intent (k : RecordKernelState) (cell : CellId) (f : FieldName) :
    auditCellMap k cell f = intentSetCellField k.cell cell f 1 := rfl

/-- **RECEIPT-ARCHIVE circuit pins the intent audit-marker write.** A verifying `receiptArchiveE`
witness forces the post-`cell` map to be EXACTLY `intentSetCellField … cell lifecycleField 1`. -/
theorem receiptArchive_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s')) :
    s'.kernel.cell = intentSetCellField s.kernel.cell args.cell lifecycleField 1 := by
  have hspec : ReceiptArchiveSpec s args.actor args.cell s' :=
    receiptArchiveA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  rw [hspec.2.1, auditCellMap_eq_intent]

/-- **RECEIPT-ARCHIVE circuit anti-ghost.** -/
theorem receiptArchive_circuit_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.kernel.cell ≠ intentSetCellField s.kernel.cell args.cell lifecycleField 1) :
    ¬ satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s') :=
  fun h => hwrong (receiptArchive_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

open Dregg2.Circuit.Inst.RefusalA (RefusalArgs refusalE refusalA_full_sound)

/-- **REFUSAL circuit pins the intent refusal-marker write.** -/
theorem refusal_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S refusalE (encodeE S refusalE s args s')) :
    s'.kernel.cell = intentSetCellField s.kernel.cell args.cell refusalField 1 := by
  have hspec : RefusalSpec s args.actor args.cell s' :=
    refusalA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  rw [hspec.2.1, auditCellMap_eq_intent]

/-- **REFUSAL circuit anti-ghost.** -/
theorem refusal_circuit_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.kernel.cell ≠ intentSetCellField s.kernel.cell args.cell refusalField 1) :
    ¬ satisfiedE S refusalE (encodeE S refusalE s args s') :=
  fun h => hwrong (refusal_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

open Dregg2.Circuit.Inst.MakeSovereignA (MakeSovereignArgs makeSovereignE makeSovereignA_full_sound)
open Dregg2.Circuit.Spec.SovereignCommitment (MakeSovereignSpec)

/-- **MAKE-SOVEREIGN circuit pins the intent sovereign-rebind.** A verifying `makeSovereignE` witness
forces the post-`cell` map to be EXACTLY `sovereignRebind … cell` (cell `cell` rebound to its
sovereign-commitment value, every other cell untouched). -/
theorem makeSovereign_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S makeSovereignE (encodeE S makeSovereignE s args s')) :
    s'.kernel.cell = sovereignRebind s.kernel.cell args.cell := by
  have hspec : MakeSovereignSpec s args.actor args.cell s' :=
    makeSovereignA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  exact hspec.2.1

/-- **MAKE-SOVEREIGN circuit anti-ghost.** -/
theorem makeSovereign_circuit_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.kernel.cell ≠ sovereignRebind s.kernel.cell args.cell) :
    ¬ satisfiedE S makeSovereignE (encodeE S makeSovereignE s args s') :=
  fun h => hwrong (makeSovereign_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

open Dregg2.Circuit.Inst.EmitEventA (EmitEventArgs emitEventE emitEventA_full_sound)
open Dregg2.Circuit.Spec.CellStateLog (EmitEventSpec emitReceipt)

/-- **EMIT-EVENT circuit pins the intent log advance.** `emitEvent` is LOG-ONLY (the kernel is frozen).
A verifying `emitEventE` witness forces the post-`log` to be EXACTLY `emitReceipt actor cell :: log`
(the disclosed event receipt prepended) — the intent receipt-chain advance, every kernel field frozen. -/
theorem emitEvent_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S emitEventE (encodeE S emitEventE s args s')) :
    s'.log = emitReceipt args.actor args.cell :: s.log := by
  have hspec : EmitEventSpec s args.actor args.cell args.topic args.data s' :=
    emitEventA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  exact hspec.2.1

/-- **EMIT-EVENT circuit anti-ghost (log).** -/
theorem emitEvent_circuit_rejects_wrong_log
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hwrong : s'.log ≠ emitReceipt args.actor args.cell :: s.log) :
    ¬ satisfiedE S emitEventE (encodeE S emitEventE s args s') :=
  fun h => hwrong (emitEvent_circuit_pins_intent S hN hL hRest hLog s args s' hwf hwf' h)

/-! ## §18 — THE CELL-CREATION FAMILY (createCell / spawn / createCellFromFactory) and CELL-DESTROY:
circuit pins the INTENT account-set growth / lifecycle-and-deathCert image.

`createCell` / `spawn` / `createCellFromFactory` all GROW the live account set by the new cell
(`insert newCell accounts` / `insert child accounts`). We build the intent oracle
`intentAccountInsert` and pin the accounts-growth (the capability-creation move — a cell brought to
life). `cellDestroy` writes the lifecycle + deathCert markers (`destroyKernelMap`); we pin both. Even
under the heavy multi-digest commit frameworks (Triple/Quint/Dual), the intent connection is a clean
projection of the full-state soundness. -/

open Dregg2.Circuit.BornEmptyCommit (BornEmptySideTables SpawnCreateLeg)

/-- **`intentAccountInsert accounts cell`** — the INTENT account set after a cell creation: the live
account set GROWS by `cell` (`insert`). Written from intent ("bring `cell` to life as a live
account"); the SAME `insert` the circuit specs pin. -/
def intentAccountInsert (accounts : Finset CellId) (cell : CellId) : Finset CellId :=
  insert cell accounts

/-! ### §18a — CREATE-CELL: circuit pins the intent account-insert (Triple framework). -/

open Dregg2.Circuit.Inst.CreateCellA (CreateCellArgs createCellE createCellA_full_sound)
open Dregg2.Circuit.Spec.AccountGrowth (CreateCellSpec SpawnSpec)

/-- **CREATE-CELL circuit pins the intent account-insert.** A verifying `createCellE` witness forces
the post-`accounts` to be EXACTLY `intentAccountInsert … newCell` (the new cell brought to life). -/
theorem createCell_circuit_pins_intent
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : Dregg2.Circuit.Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
        (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s')) :
    s'.kernel.accounts = intentAccountInsert s.kernel.accounts args.newCell := by
  have hspec : CreateCellSpec s args.actor args.newCell s' :=
    createCellA_full_sound S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h
  exact hspec.2.1

/-- **CREATE-CELL circuit anti-ghost.** -/
theorem createCell_circuit_rejects_wrong_accounts
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : Dregg2.Circuit.Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.accounts ≠ intentAccountInsert s.kernel.accounts args.newCell) :
    ¬ satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
        (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s') :=
  fun h => hwrong (createCell_circuit_pins_intent S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h)

/-! ### §18b — SPAWN: circuit pins the intent account-insert (Quint framework). -/

open Dregg2.Circuit.Inst.SpawnA (SpawnArgs spawnE spawnA_full_sound)

/-- **SPAWN circuit pins the intent account-insert.** A verifying `spawnE` witness forces the
post-`accounts` to be EXACTLY `intentAccountInsert … child` (the spawned child brought to life). -/
theorem spawn_circuit_pins_intent
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Dregg2.Authority.Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : Dregg2.Circuit.Inst.SpawnA.RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
        (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s')) :
    s'.kernel.accounts = intentAccountInsert s.kernel.accounts args.child := by
  have hspec : SpawnSpec s args.actor args.child args.target s' :=
    spawnA_full_sound S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog s args s' h
  exact hspec.2.1

/-- **SPAWN circuit anti-ghost.** -/
theorem spawn_circuit_rejects_wrong_accounts
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Dregg2.Authority.Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : Dregg2.Circuit.Inst.SpawnA.RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.accounts ≠ intentAccountInsert s.kernel.accounts args.child) :
    ¬ satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
        (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s') :=
  fun h => hwrong (spawn_circuit_pins_intent S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog s args s' h)

/-! ### §18c — CELL-DESTROY: circuit pins the intent lifecycle + deathCert image (Dual framework). -/

open Dregg2.Circuit.Inst.CellDestroyA (CellDestroyArgs cellDestroyE cellDestroyA_full_sound)
open Dregg2.Circuit.Spec.CellLifecycle (CellDestroySpec destroyKernelMap)

/-- **CELL-DESTROY circuit pins the intent lifecycle + deathCert image.** A verifying `cellDestroyE`
witness forces the post-`lifecycle` AND post-`deathCert` maps to be EXACTLY the `destroyKernelMap`
image (cell `cell` marked destroyed with cert `certHash`, no other cell's lifecycle/deathCert
changed). -/
theorem cellDestroy_circuit_pins_intent
    (S : Surface2) (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : Dregg2.Circuit.Inst.CellDestroyA.RestIffNoLifecycleDeathCert S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (cellDestroyE DLif hDLif DDC hDDC)
        (encodeE2Dual S (cellDestroyE DLif hDLif DDC hDDC) s args s')) :
    s'.kernel.lifecycle = (destroyKernelMap s.kernel args.cell args.certHash).lifecycle
    ∧ s'.kernel.deathCert = (destroyKernelMap s.kernel args.cell args.certHash).deathCert := by
  have hspec : CellDestroySpec s args.actor args.cell args.certHash s' :=
    cellDestroyA_full_sound S DLif hDLif DDC hDDC hRest hLog s args s' h
  exact ⟨hspec.2.1, hspec.2.2.1⟩

/-- **CELL-DESTROY circuit anti-ghost.** -/
theorem cellDestroy_circuit_rejects_wrong_lifecycle
    (S : Surface2) (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : Dregg2.Circuit.Inst.CellDestroyA.RestIffNoLifecycleDeathCert S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.lifecycle ≠ (destroyKernelMap s.kernel args.cell args.certHash).lifecycle) :
    ¬ satisfiedE2Dual S (cellDestroyE DLif hDLif DDC hDDC)
        (encodeE2Dual S (cellDestroyE DLif hDLif DDC hDDC) s args s') :=
  fun h => hwrong (cellDestroy_circuit_pins_intent S DLif hDLif DDC hDDC hRest hLog s args s' h).1

/-! ### §18d — CREATE-CELL-FROM-FACTORY: circuit pins the intent account-insert (Quint framework,
existential over the conforming factory entry `e`). -/

open Dregg2.Circuit.Inst.CreateCellFromFactoryA
  (CreateFromFactoryArgs createFromFactoryE createCellFromFactoryA_full_sound
   CreateFromFactoryCircuitSpec)
open Dregg2.Circuit.BornEmptyCommit (BornEmptyAuthorityTables)

/-- **CREATE-CELL-FROM-FACTORY circuit pins the intent account-insert.** A verifying
`createFromFactoryE` witness forces the post-`accounts` to be EXACTLY `intentAccountInsert … newCell`
(the factory-instantiated cell brought to life — for the conforming registered factory entry `e`). -/
theorem createFromFactory_circuit_pins_intent
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : Dregg2.Circuit.Inst.CreateCellFromFactoryA.RestIffNoFactoryTouched S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S
        (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
        (encodeE2Quint S
          (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) s args s')) :
    s'.kernel.accounts = intentAccountInsert s.kernel.accounts args.newCell := by
  have hspec : CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s' :=
    createCellFromFactoryA_full_sound S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      hRest hLog s args s' h
  obtain ⟨_e, _, hacc, _⟩ := hspec
  exact hacc

/-- **CREATE-CELL-FROM-FACTORY circuit anti-ghost.** -/
theorem createFromFactory_circuit_rejects_wrong_accounts
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : Dregg2.Circuit.Inst.CreateCellFromFactoryA.RestIffNoFactoryTouched S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (hwrong : s'.kernel.accounts ≠ intentAccountInsert s.kernel.accounts args.newCell) :
    ¬ satisfiedE2Quint S
        (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
        (encodeE2Quint S
          (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) s args s') :=
  fun h => hwrong (createFromFactory_circuit_pins_intent S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC
    DAuth hDAuth hRest hLog s args s' h)

/-! ## §19 — THE TAIL: balanceA (2nd value-movement instance) / pipelined-send / exercise
(queue-resize: F2a-deleted with the queue family). -/

/-! ### §19a — BALANCE-A: the SECOND v2 instance of the value movement, pinned to `intentTransfer`. -/

open Dregg2.Circuit.Inst.BalanceA (balanceAE balanceA_full_sound)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)

/-- **BALANCE-A circuit pins the intent debit+credit.** The alternate `balanceAE` instance of the
value movement also forces the post-`bal` to be EXACTLY `intentTransfer … src dst a amt` (same intent
as `transfer`, §2). -/
theorem balanceA_circuit_pins_intent
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.BalanceA.BalanceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (balanceAE D hD) (encodeE2 S (balanceAE D hD) s args s')) :
    s'.kernel.bal = intentTransfer s.kernel.bal args.t.src args.t.dst args.a args.t.amt := by
  have hspec : BalanceMovementSpec s args.t args.a s' :=
    balanceA_full_sound S D hD hRest hLog s args s' h
  have hne : args.t.src ≠ args.t.dst := hspec.1.2.2.2.1
  exact pin_intent_of_bridge hspec.2.1 (intentTransfer_eq_recTransferBal _ _ _ _ _ hne).symm

-- (F2a) §19b queue-resize intent-pinning DELETED with the queue effect family.

/-! ### §19c — PIPELINED-SEND: log-only; circuit pins the intent receipt advance. -/

open Dregg2.Circuit.Inst.PipelinedSendA (PipelinedSendArgs pipelinedSendE pipelinedSendA_full_sound)
open Dregg2.Circuit.Spec.QueuePipelinedSend (PipelinedSendSpec pipelinedSendReceipt)

/-- **PIPELINED-SEND circuit pins the intent log advance.** `pipelinedSend` is LOG-ONLY (the kernel is
frozen). A verifying witness forces the post-`log` to be EXACTLY `pipelinedSendReceipt actor :: log`. -/
theorem pipelinedSend_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S pipelinedSendE (encodeE S pipelinedSendE s args s')) :
    s'.log = pipelinedSendReceipt args.actor :: s.log := by
  have hspec : PipelinedSendSpec s args.actor s' :=
    pipelinedSendA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  exact hspec.1

/-! ### §19d — EXERCISE: circuit pins the whole intent hold-exercise post-state. -/

open Dregg2.Circuit.Inst.ExerciseA (ExerciseHoldArgs exerciseE exerciseA_full_sound)
open Dregg2.Circuit.Spec.Exercise (ExerciseHoldSpec)
open Dregg2.Circuit.ActionDispatch (exerciseHoldState)

/-- **EXERCISE circuit pins the intent hold-exercise post-state.** A verifying `exerciseE` witness
forces the WHOLE post-state to be EXACTLY `exerciseHoldState s actor` (the declarative hold-exercise
result). -/
theorem exercise_circuit_pins_intent
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExerciseHoldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S exerciseE (encodeE S exerciseE s args s')) :
    s' = exerciseHoldState s args.actor := by
  have hspec : ExerciseHoldSpec s args.actor args.target s' :=
    exerciseA_full_sound S hN hL hRest hLog s args s' hwf hwf' h
  exact hspec.2

-- (F2a) §20 transactional-queue intent-pinning (enqueue/dequeue/atomic-tx/pipeline-step)
-- DELETED with the queue effect family.

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
#assert_axioms burn_circuit_pins_intent
#assert_axioms burn_circuit_rejects_wrong_ledger
#assert_axioms bridgeMint_circuit_pins_intent
#assert_axioms bridgeMint_circuit_rejects_wrong_ledger
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
#assert_axioms cellSeal_circuit_pins_intent
#assert_axioms cellSeal_circuit_rejects_wrong_lifecycle
#assert_axioms revokeDelegation_circuit_pins_intent
#assert_axioms revokeDelegation_circuit_rejects_wrong_caps
#assert_axioms intentIntroduceCaps_eq_recDelegateCaps
#assert_axioms introduce_circuit_pins_intent
#assert_axioms introduce_circuit_rejects_wrong_caps
#assert_axioms cellUnseal_circuit_pins_intent
#assert_axioms cellUnseal_circuit_rejects_wrong_lifecycle
#assert_axioms refreshDelegation_circuit_pins_intent
#assert_axioms refreshDelegation_circuit_rejects_wrong_delegations

#assert_axioms auditCellMap_eq_intent
#assert_axioms receiptArchive_circuit_pins_intent
#assert_axioms receiptArchive_circuit_rejects_wrong_cell
#assert_axioms refusal_circuit_pins_intent
#assert_axioms refusal_circuit_rejects_wrong_cell
#assert_axioms makeSovereign_circuit_pins_intent
#assert_axioms makeSovereign_circuit_rejects_wrong_cell
#assert_axioms emitEvent_circuit_pins_intent
#assert_axioms emitEvent_circuit_rejects_wrong_log


#assert_axioms createCell_circuit_pins_intent
#assert_axioms createCell_circuit_rejects_wrong_accounts
#assert_axioms spawn_circuit_pins_intent
#assert_axioms spawn_circuit_rejects_wrong_accounts
#assert_axioms cellDestroy_circuit_pins_intent
#assert_axioms cellDestroy_circuit_rejects_wrong_lifecycle
#assert_axioms createFromFactory_circuit_pins_intent
#assert_axioms createFromFactory_circuit_rejects_wrong_accounts

#assert_axioms balanceA_circuit_pins_intent
#assert_axioms pipelinedSend_circuit_pins_intent
#assert_axioms exercise_circuit_pins_intent

end Dregg2.Spec.CircuitSpecTriangle
