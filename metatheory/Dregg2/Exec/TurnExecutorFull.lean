/-
# Dregg2.Exec.TurnExecutorFull — WIDENING the replacement executor to the FULL dregg1 op-set.

`Exec/TurnExecutor.lean`'s `execTurn` runs dregg1's call-forest of catalog-typed *balance/effect*
`Action`s as an all-or-nothing transaction, step-complete by construction (`execTurn_attests`: the
four `StepInv` conjuncts over the whole multi-`Action` turn). But dregg1's turn-executor does MORE
than balance/effect moves: it also runs **authority ops** (grant/revoke caps — the Granovetter
delegate / target-revoke) and **supply ops** (mint/burn — the only ops that legitimately move the
conserved total). For the replacement to SUBSUME every dregg1 turn kind, it must cover those too.

This module widens the executor. We introduce a single sum

  `FullAction = balance (a `TurnExecutor.Action`)
              | delegate / revoke  (an AUTHORITY turn, via `AuthTurn`'s `recKDelegate` /
                                    `recKRevokeTarget`)
              | mint / burn        (a SUPPLY turn, the record-cell refinement of
                                    `Generators.execMint` / `execBurn` over the `balance` FIELD)`

and one executor `execFull : RecChainedState → FullAction → Option RecChainedState`, all over the
SAME content-addressed record world (`RecChainedState` / `recTotal` / `balOf`) that `TurnExecutor`
and `AuthTurn` already share — so the widening is genuinely ONE executor, not three. Each kind is
all-or-nothing (fail-closed gates, `Option`-monad). A whole turn is a list of `FullAction`s run as
a transaction (`execFullTurn`), exactly `execTurn`'s discipline lifted to the wider op-set.

We then PROVE that EVERY kind attests its `StepInv` obligations, packaged as `fullActionInv`:

  * **balance/effect** — Conservation (the `balance` field) ∧ Authority ∧ ChainLink ∧ ObsAdvance,
    delegated VERBATIM to `recCexec_attests` (the `TurnExecutor` spine, one op);
  * **authority (delegate/revoke)** — the FRAME-FIX: `recTotal` is UNCHANGED (conservation trivially
    preserved — `recKDelegate_frame` / `recKRevokeTarget_frame`), and the cap graph is EDITED per
    `AuthTurn` (`recKDelegate_execGraph` / `recKRevokeTarget_execGraph` = `Spec.addEdge`/`removeEdge`
    = `Introduce`/`Revoke` `result`); a delegation is moreover AUTHORIZED (`recKDelegate_grounds`:
    the delegator holds the source edge — "only connectivity begets connectivity");
  * **mint/burn** — the supply MOVES by exactly `±amt` (`recMint_delta` / `recBurn_delta`, the
    record-cell refinement of `Generators.mint_delta`/`burn_delta`) with the
    Generative/Annihilative DISCLOSURE obligation discharged off `CatalogEffects`
    (`g_bridgeMint`/`a_burn` color ⇒ `is_disclosed_non_conservation`), and mint/burn are AUTHORIZED
    (the privileged `mintAuthorizedB` gate — a cell cannot coin its own supply).

The headline `execFull_attests` bundles these per-kind: every committed `FullAction` attests the
relevant `StepInv` content for its kind, so the replacement executor is **step-complete across EVERY
dregg1 turn kind** — not just balance/effect. (`fullActionInv` is never weakened: each kind carries
exactly its sound obligations, with conservation tracked EXACTLY — `0` for balance/authority, `±amt`
for mint/burn — via the `ledgerDelta` book-keeping, the executable shadow of dregg1's per-domain
`excess`.)

Discipline (REORIENT §6): no `axiom`/`admit`/`native_decide`/`sorry`. `#assert_axioms` on every
keystone. Pure, computable, `#eval`-able. Reuses `TurnExecutor`/`AuthTurn`/`Generators`/
`CatalogEffects`/`RecordKernel`; edits none. Verified standalone:
`lake env lean Dregg2/Exec/TurnExecutorFull.lean`.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Exec.AuthTurn
import Dregg2.Exec.Generators
import Dregg2.CatalogEffects
import Dregg2.Exec.EffectsState

namespace Dregg2.Exec.TurnExecutorFull

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.CatalogInstances (EffectKind effectLinearity)
open Dregg2.CatalogEffects (Regime effectObligation)
open Dregg2.Spec (Domain conservedInDomain LinearityClass)
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.Exec.EffectsState (setField fieldOf writeField stateAuthB stateStep stateStep_factors
  setField_balOf state_caps_unchanged state_authGraph_unchanged state_authorized state_obsadvance
  state_field_written stateStepGuarded stateStepGuarded_eq stateStepGuarded_admits
  stateStepGuarded_caveat_violation_fails caveatsAdmit)
open scoped BigOperators
open Dregg2.Tactics  -- the effect-arm combinators (`reject_none`/`commit_subst`/`gate_peel`/`bal_neutral`)

/-! ## §1 — Record-cell MINT/BURN: the supply generators over the `balance` FIELD.

`Exec/Generators.lean` proves `execMint`/`execBurn` over the *scalar* `KernelState` (`bal : CellId →
ℤ`, measure `total`). The full executor lives in the *record* world (`RecordKernelState`, measure
`recTotal` over the `balance` field). So we re-found the two supply generators here over the record
cell — the EXACT analog of `Generators` but writing the named `balance` field via `setBalance` —
reusing `Generators.mintAuthorizedB` (the privileged `node`/`control` gate; bare ownership is NOT
enough to coin supply) and `Kernel.sum_indicator` (the single-point-sum technique). -/

/-- Credit cell `cell`'s `balance` field by `amt` (record-cell mint write). Touches only `cell`'s
record (and only its `balance` field — every other field of the content-addressed record survives,
by `setBalance`); every other cell is untouched. -/
def recCreditCell (st : CellId → Value) (cell : CellId) (amt : ℤ) : CellId → Value :=
  fun c => if c = cell then setBalance (st c) (balOf (st c) + amt) else st c

/-- **Executable record-cell mint.** Fail-closed: credits `cell`'s `balance` field by `amt` only
when the actor is authorized to mint over `cell` (`mintAuthorizedB` — a `node`/`control` cap, NOT
mere ownership), the amount is non-negative, and `cell` is a live account. The record-cell
refinement of `Generators.execMint` over the `balance` field. -/
def recKMint (k : RecordKernelState) (actor cell : CellId) (amt : ℤ) : Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts then
    some { k with cell := recCreditCell k.cell cell amt }
  else
    none

/-- **Executable record-cell burn.** Fail-closed: debits `cell`'s `balance` field by `amt` only when
authorized, the amount is non-negative and available (`amt ≤ balOf (cell)`), and `cell` is live. The
record-cell refinement of `Generators.execBurn`. -/
def recKBurn (k : RecordKernelState) (actor cell : CellId) (amt : ℤ) : Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts then
    some { k with cell := recCreditCell k.cell cell (-amt) }
  else
    none

/-- The `balance`-field delta of a single-cell credit, as a debit/credit indicator (the named-field
analog of `Generators.sum_update_add`'s pointwise step). -/
theorem recCreditCell_balOf_delta (st : CellId → Value) (cell : CellId) (amt : ℤ) (c : CellId) :
    balOf (recCreditCell st cell amt c) - balOf (st c) = (if c = cell then amt else 0) := by
  unfold recCreditCell
  rcases eq_or_ne c cell with h | h
  · rw [if_pos h, setBalance_balOf, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- **Single-cell supply delta over `recTotal`.** Crediting exactly the live cell `cell ∈ acc` by
`v` (writing the `balance` field) changes the total `balance` measure by exactly `v`. Reuses
`Kernel.sum_indicator`, the same single-point-sum technique the scalar generators use. -/
theorem recCreditCell_recTotal_delta (acc : Finset CellId) (st : CellId → Value) (cell : CellId)
    (v : ℤ) (hc : cell ∈ acc) :
    (∑ c ∈ acc, balOf (recCreditCell st cell v c)) = (∑ c ∈ acc, balOf (st c)) + v := by
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, balOf (recCreditCell st cell v c) - balOf (st c)
      = (if c = cell then v else 0) := fun c _ => recCreditCell_balOf_delta st cell v c
  rw [Finset.sum_congr rfl hg, sum_indicator acc cell v hc]

/-- **Record-cell mint inflow — PROVED.** A committed record mint raises the total `balance` by
exactly `amt`: `recTotal k' = recTotal k + amt`. The record-cell refinement of
`Core.mint_delta`/`Generators.execMint_delta`. -/
theorem recKMint_delta (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKMint k actor cell amt = some k') : recTotal k' = recTotal k + amt := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hcell⟩ := hg
    simpa [recTotal] using recCreditCell_recTotal_delta k.accounts k.cell cell amt hcell
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Record-cell burn outflow — PROVED.** A committed record burn lowers the total `balance` by
exactly `amt`: `recTotal k' = recTotal k - amt`. The refinement of `Generators.execBurn_delta`. -/
theorem recKBurn_delta (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKBurn k actor cell amt = some k') : recTotal k' = recTotal k - amt := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hcell⟩ := hg
    have := recCreditCell_recTotal_delta k.accounts k.cell cell (-amt) hcell
    simpa [recTotal, sub_eq_add_neg] using this
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No mint without authority — PROVED** (the integrity shadow of the privileged supply
generator). A committed record mint implies the actor held mint authority over `cell`. -/
theorem recKMint_authorized (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKMint k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No burn without authority — PROVED.** A committed record burn implies mint authority. -/
theorem recKBurn_authorized (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKBurn k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed (record mint) — PROVED.** Without mint authority, no record mint commits. -/
theorem recKMint_unauthorized_fails (k : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : recKMint k actor cell amt = none := by
  unfold recKMint; rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **Fail-closed (record burn) — PROVED.** Without mint authority, no record burn commits. -/
theorem recKBurn_unauthorized_fails (k : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : recKBurn k actor cell amt = none := by
  unfold recKBurn; rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-! ## §2 — The DISCLOSURE obligation for mint/burn (the Generative/Annihilative gate).

A supply move legitimately breaks `Σδ = 0`, but its delta is FORCED into the receipt — the
`is_disclosed_non_conservation` obligation `CatalogEffects` proves of the Generative
(`bridgeMint`/mint) and Annihilative (`burn`) colors. We tie each record-cell supply op to its
catalog color so the disclosure obligation is discharged for the executable op, not just abstractly.
-/

/-- A `mint`'s catalog effect kind (dregg1's `Effect::BridgeMint` — Generative). -/
def mintEffect : EffectKind := .bridgeMint

/-- A `burn`'s catalog effect kind (dregg1's `Effect::Burn` — Annihilative). -/
def burnEffect : EffectKind := .burn

/-- **Mint discloses — PROVED.** The mint effect is Generative, hence carries the disclosed
non-conservation obligation: its supply delta must be revealed in the receipt. Discharged off
`CatalogEffects.generative_discloses` + `g_bridgeMint`. -/
theorem mint_discloses : (effectLinearity mintEffect).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses mintEffect Dregg2.CatalogEffects.g_bridgeMint

/-- **Burn discloses — PROVED.** The burn effect is Annihilative, hence disclosed: its destroyed
amount must be revealed. Discharged off `CatalogEffects.annihilative_discloses` + `a_burn`. -/
theorem burn_discloses : (effectLinearity burnEffect).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.annihilative_discloses burnEffect Dregg2.CatalogEffects.a_burn

/-- Mint/burn carry the `Disclosed` regime (NOT `Paired`): they break conservation BY DESIGN, with
the delta disclosed — the supply ops are exactly the non-`Paired` half of the catalog. PROVED. -/
theorem mint_regime_disclosed : effectObligation mintEffect = Regime.Disclosed := rfl
theorem burn_regime_disclosed : effectObligation burnEffect = Regime.Disclosed := rfl

/-! ## §3 — Authority turns lifted to `RecChainedState` (the chained delegate / revoke).

`AuthTurn`'s `recKDelegate`/`recKRevokeTarget` edit `RecordKernelState.caps`. To run them inside the
unified chained executor we lift each onto `RecChainedState`, threading the receipt chain exactly as
`recCexec` does (newest move first), but carrying an authority "move" marker rather than a balance
`Turn`. The conserved measure is FIXED across an authority turn (the dual frame). -/

/-- A synthetic receipt marker for an authority turn (a self-`Turn` on the actor, amount `0`), so the
authority edit lands a row on the SAME receipt chain (`List Turn`) as balance/supply ops. It carries
no balance delta (`amt := 0`) — the chain entry records THAT an authority edit happened, while the
graph change itself is proven separately (`AuthTurn`'s `execGraph` match). -/
def authReceipt (actor : CellId) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }

/-- **Chained delegate.** Run `recKDelegate`; on commit, append an authority receipt. -/
def recCDelegate (s : RecChainedState) (delegator recipient t : CellId) :
    Option RecChainedState :=
  match recKDelegate s.kernel delegator recipient t with
  | some k' => some { kernel := k', log := authReceipt delegator :: s.log }
  | none    => none

/-- **Chained RIGHTS-CARRYING delegate.** Run `recKDelegateAtten` (the faithful `apply_introduce`:
gate on the delegator holding a cap to `t`, then grant `recipient` the delegator's held cap to `t`
ATTENUATED to `keep` — REAL rights `⊆` held, `recKDelegateAtten_non_amplifying`, stricter than the
unattenuated held-cap copy of `recKDelegate`); on commit, append an authority receipt. Balance-NEUTRAL: edits
ONLY `caps` (`recKDelegateAtten_frame`), so `ledgerDeltaAsset = 0` for every asset. -/
def recCDelegateAtten (s : RecChainedState) (delegator recipient t : CellId) (keep : List Auth) :
    Option RecChainedState :=
  match recKDelegateAtten s.kernel delegator recipient t keep with
  | some k' => some { kernel := k', log := authReceipt delegator :: s.log }
  | none    => none

/-- **Chained revoke.** `recKRevokeTarget` always commits (revocation only subtracts authority);
append an authority receipt. -/
def recCRevoke (s : RecChainedState) (holder t : CellId) : RecChainedState :=
  { kernel := recKRevokeTarget s.kernel holder t, log := authReceipt holder :: s.log }

/-- **Chained mint.** Run `recKMint`; on commit, append a supply receipt (a self-`Turn` carrying the
minted `amt` as its `balance_change` — the disclosed delta on the chain). -/
def recCMint (s : RecChainedState) (actor cell : CellId) (amt : ℤ) : Option RecChainedState :=
  match recKMint s.kernel actor cell amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := amt } :: s.log }
  | none    => none

/-- **Chained burn.** Run `recKBurn`; on commit, append a supply receipt carrying `-amt`. -/
def recCBurn (s : RecChainedState) (actor cell : CellId) (amt : ℤ) : Option RecChainedState :=
  match recKBurn s.kernel actor cell amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := -amt } :: s.log }
  | none    => none

/-! ## §4 — `FullAction` and `execFull`: ONE executor over the FULL op-set. -/

/-- **The FULL dregg1 op-set, as one sum.** A single `FullAction` is one of:
  * `balance a` — a catalog-typed balance/effect `Action` (dregg1's `Action`; runs via `recCexec`);
  * `delegate delegator recipient t` — a Granovetter authority grant (runs via `recKDelegate`);
  * `revoke holder t` — a target revocation (runs via `recKRevokeTarget`);
  * `mint actor cell amt` / `burn actor cell amt` — the privileged supply generators.
This widens `TurnExecutor.Action` (balance/effect only) to subsume EVERY dregg1 turn kind. -/
inductive FullAction where
  /-- A catalog-typed balance/effect action (dregg1's `Action`). -/
  | balance  (a : Action)
  /-- A Granovetter delegation: `delegator` hands `recipient` connectivity to `t`. -/
  | delegate (delegator recipient t : CellId)
  /-- A target revocation: `holder` loses every cap conferring an edge to `t`. -/
  | revoke   (holder t : CellId)
  /-- A privileged supply mint: credit `cell`'s `balance` by `amt`. -/
  | mint     (actor cell : CellId) (amt : ℤ)
  /-- A privileged supply burn: debit `cell`'s `balance` by `amt`. -/
  | burn     (actor cell : CellId) (amt : ℤ)

/-- **The ledger delta of a `FullAction`** — its exact effect on the conserved `recTotal`. Balance,
authority (delegate/revoke), are conservation-trivial (`0`); mint adds `amt`, burn subtracts. The
executable shadow of dregg1's per-domain `excess` book-keeping. -/
def ledgerDelta : FullAction → ℤ
  | .balance _        => 0
  | .delegate _ _ _   => 0
  | .revoke _ _       => 0
  | .mint _ _ amt     => amt
  | .burn _ _ amt     => -amt

/-- **The full executor.** Dispatch each `FullAction` kind to its (reused, already-proven) chained
primitive. All-or-nothing per kind (each is `Option`); `revoke` always commits. ONE executor over
the full op-set — balance/effect ∪ authority ∪ supply. -/
def execFull (s : RecChainedState) : FullAction → Option RecChainedState
  | .balance a              => recCexec s a.move
  | .delegate del rec t     => recCDelegate s del rec t
  | .revoke holder t        => some (recCRevoke s holder t)
  | .mint actor cell amt    => recCMint s actor cell amt
  | .burn actor cell amt    => recCBurn s actor cell amt

/-- **The full turn executor.** A turn is a list of `FullAction`s run as an ALL-OR-NOTHING
transaction (the `Option`-monad fold; any `none` aborts the whole turn). The wider analog of
`TurnExecutor.execTurn`. -/
def execFullTurn (s : RecChainedState) : List FullAction → Option RecChainedState
  | []        => some s
  | a :: rest =>
    match execFull s a with
    | some s' => execFullTurn s' rest
    | none    => none

/-! ## §5 — Conservation, EXACTLY: every committed `FullAction` moves `recTotal` by `ledgerDelta`.

The unified conservation law (the record-world analog of `Unified.step_delta`): balance and
authority kinds are conservation-trivial (`0`); mint/burn move the supply by exactly `±amt`. Proved
by `cases` over the kinds, reusing each primitive's already-proven delta fact. -/

/-- **`execFull_ledger` — PROVED (unified conservation).** Every committed `FullAction` moves the
conserved `recTotal` by EXACTLY `ledgerDelta`: `0` for balance/authority, `+amt` for mint, `-amt`
for burn. The single law subsuming `recCexec`'s conservation (`0`), `recKDelegate_frame`/
`recKRevokeTarget_frame` (`0`), and `recKMint_delta`/`recKBurn_delta` (`±amt`). -/
theorem execFull_ledger (s s' : RecChainedState) (fa : FullAction) (h : execFull s fa = some s') :
    recTotal s'.kernel = recTotal s.kernel + ledgerDelta fa := by
  cases fa with
  | balance a =>
      -- balance: `recCexec` conserves (`recTotal` fixed); `ledgerDelta = 0`.
      simp only [execFull, ledgerDelta] at h ⊢
      rw [(recCexec_attests h).1]; ring
  | delegate del rec t =>
      -- delegate: the dual frame fixes `recTotal`; `ledgerDelta = 0`.
      simp only [execFull, recCDelegate, ledgerDelta] at h ⊢
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          rw [(recKDelegate_frame s.kernel k' del rec t hd).1]; ring
  | revoke holder t =>
      -- revoke: the dual frame fixes `recTotal`; `ledgerDelta = 0`.
      simp only [execFull, recCRevoke, ledgerDelta] at h ⊢
      simp only [Option.some.injEq] at h; subst h
      rw [(recKRevokeTarget_frame s.kernel holder t).1]; ring
  | mint actor cell amt =>
      -- mint: `recTotal` rises by `amt`; `ledgerDelta = +amt`.
      simp only [execFull, recCMint, ledgerDelta] at h ⊢
      cases hm : recKMint s.kernel actor cell amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          exact recKMint_delta s.kernel k' actor cell amt hm
  | burn actor cell amt =>
      -- burn: `recTotal` falls by `amt`; `ledgerDelta = -amt`.
      simp only [execFull, recCBurn, ledgerDelta] at h ⊢
      cases hb : recKBurn s.kernel actor cell amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          rw [recKBurn_delta s.kernel k' actor cell amt hb]; ring

/-- A `FullAction` is **balance-conserving** when its delta is `0` (everything but mint/burn — the
balance/effect and authority kinds). -/
def Conserving : FullAction → Prop
  | .balance _      => True
  | .delegate _ _ _ => True
  | .revoke _ _     => True
  | .mint _ _ _     => False
  | .burn _ _ _     => False

/-- A conserving `FullAction` has zero ledger delta — PROVED. -/
theorem ledgerDelta_eq_zero_of_conserving (fa : FullAction) (hc : Conserving fa) :
    ledgerDelta fa = 0 := by cases fa <;> simp_all [Conserving, ledgerDelta]

/-- **A conserving `FullAction` preserves `recTotal` — PROVED** (corollary of `execFull_ledger`):
balance/effect and authority turns leave the conserved supply FIXED. -/
theorem execFull_conserves (s s' : RecChainedState) (fa : FullAction)
    (hc : Conserving fa) (h : execFull s fa = some s') : recTotal s'.kernel = recTotal s.kernel := by
  rw [execFull_ledger s s' fa h, ledgerDelta_eq_zero_of_conserving fa hc, add_zero]

/-- **`execFull_balance_domain_conserves` — PROVED (per-domain Σ = 0 for conserving kinds).** A
committed conserving `FullAction` nets to `0` in the `balance` domain (the realized total-delta
singleton is `0`), the executable shadow of dregg1's `excess == 0` gate. -/
theorem execFull_balance_domain_conserves (s s' : RecChainedState) (fa : FullAction)
    (hc : Conserving fa) (h : execFull s fa = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain
  rw [execFull_conserves s s' fa hc h]; simp

/-! ## §6 — Authority: every committed kind that gates on authority WAS authorized.

Balance/effect actions go through `recCexec`'s `authorizedB` gate; delegations ground in the
Granovetter source edge (`recKDelegate_grounds`); mint/burn go through the privileged
`mintAuthorizedB` gate. (Revoke needs no authority — it only subtracts; this is the SAME asymmetry
as `AuthTurn`'s "revocation always commits".) -/

/-- **Balance action authorized — PROVED.** A committed balance `FullAction` was authorized
(`authorizedB` at the pre-state), via `recCexec_attests`. -/
theorem execFull_balance_authorized (s s' : RecChainedState) (a : Action)
    (h : execFull s (.balance a) = some s') : authorizedB s.kernel.caps a.move = true :=
  (recCexec_attests (by simpa [execFull] using h)).2.1

/-- **Delegation grounds — PROVED.** A committed delegation HOLDS the Granovetter source edge
`delegator ⟶ ⟨t,()⟩` on `execGraph` (only connectivity begets connectivity), via
`recKDelegate_grounds`. -/
theorem execFull_delegate_grounds (s s' : RecChainedState) (del rec t : CellId)
    (h : execFull s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' del rec t hd

/-- **Mint authorized — PROVED.** A committed mint implies the actor held the privileged mint
authority over `cell` (a `node`/`control` cap — not mere ownership). -/
theorem execFull_mint_authorized (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.mint actor cell amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFull, recCMint] at h
  cases hm : recKMint s.kernel actor cell amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMint_authorized s.kernel k' actor cell amt hm

/-- **Burn authorized — PROVED.** A committed burn implies privileged mint authority over `cell`. -/
theorem execFull_burn_authorized (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.burn actor cell amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFull, recCBurn] at h
  cases hb : recKBurn s.kernel actor cell amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' => exact recKBurn_authorized s.kernel k' actor cell amt hb

/-! ## §7 — The authority GRAPH change: a delegate/revoke IS `Spec.addEdge`/`removeEdge`.

The authority conjunct of step-completeness for the authority kinds: the cap edit's abstract image
is exactly a `Spec.AuthStep` edit of the connectivity graph — `recKDelegate_execGraph` /
`recKRevokeTarget_execGraph` from `AuthTurn`, here read off the committed `FullAction`. -/

/-- **Delegation IS `addEdge` — PROVED.** After a committed delegation, the reconstructed authority
graph is the pre-graph with the single Spec edge `recipient ⟶ ⟨t,()⟩` ADDED — `Spec.Introduce`'s
`result` verbatim. The authority conjunct for the delegate kind. -/
theorem execFull_delegate_addEdge (s s' : RecChainedState) (del rec t : CellId)
    (h : execFull s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      -- `recKDelegate` commits ⟹ it copied the held cap that witnesses connectivity to `t`.
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps del rec t hg
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **Delegation grants the copied held cap — PROVED.** The scalar executor's concrete cap edit is
the same non-amplifying held-cap copy as `recKDelegate`, not a fresh control cap. -/
theorem execFull_delegate_grants_held_cap (s s' : RecChainedState) (del rec t : CellId)
    (h : execFull s (.delegate del rec t) = some s') :
    heldCapTo s.kernel.caps del t ∈ s'.kernel.caps rec := by
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h
      simp only [Option.some.injEq] at h
      subst h
      exact recKDelegate_grants s.kernel k' del rec t hd

/-- **Revocation IS `removeEdge` — PROVED.** After a committed revocation, the reconstructed graph
is the pre-graph with the single Spec edge `holder ⟶ ⟨t,()⟩` REMOVED — `Spec.Revoke`'s `result`
verbatim. The authority conjunct for the revoke kind. -/
theorem execFull_revoke_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFull s (.revoke holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-! ## §8 — ChainLink / ObsAdvance: every committed kind appends EXACTLY one receipt.

The chain-link / replay-detection conjuncts. Each kind extends the receipt chain by exactly one row
(newest-first), so the chain grows by exactly one per `FullAction` — a replayed action would have to
re-append, and is detectable. -/

/-- The receipt a committed `FullAction` appends (newest-first): the balance kind appends its move;
authority appends its `authReceipt`; mint/burn append a self-`Turn` carrying the supply delta. -/
def fullReceipt : FullAction → Turn
  | .balance a            => a.move
  | .delegate del _ _     => authReceipt del
  | .revoke holder _      => authReceipt holder
  | .mint actor cell amt  => { actor := actor, src := cell, dst := cell, amt := amt }
  | .burn actor cell amt  => { actor := actor, src := cell, dst := cell, amt := -amt }

/-- **ChainLink — PROVED.** A committed `FullAction` extends the receipt chain by EXACTLY its
`fullReceipt`, newest-first, with no fork or rewrite: `s'.log = fullReceipt fa :: s.log`. The
per-action generalization of `recCexec`'s `s'.log = t :: s.log` across the whole op-set. -/
theorem execFull_chainlink (s s' : RecChainedState) (fa : FullAction)
    (h : execFull s fa = some s') : s'.log = fullReceipt fa :: s.log := by
  cases fa with
  | balance a =>
      simp only [execFull, fullReceipt] at h ⊢
      exact (recCexec_attests h).2.2.1
  | delegate del rec t =>
      simp only [execFull, recCDelegate, fullReceipt] at h ⊢
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | revoke holder t =>
      simp only [execFull, recCRevoke, fullReceipt] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | mint actor cell amt =>
      simp only [execFull, recCMint, fullReceipt] at h ⊢
      cases hm : recKMint s.kernel actor cell amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | burn actor cell amt =>
      simp only [execFull, recCBurn, fullReceipt] at h ⊢
      cases hb : recKBurn s.kernel actor cell amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' => rw [hb] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-- **ObsAdvance — PROVED.** A committed `FullAction` grows the chain by exactly one row, so a
replayed action (which would re-append the same receipt) is detectable. -/
theorem execFull_obsadvance (s s' : RecChainedState) (fa : FullAction)
    (h : execFull s fa = some s') : s'.log.length = s.log.length + 1 := by
  rw [execFull_chainlink s s' fa h]; simp

/-! ## §9 — `fullActionInv`: the per-kind step-completeness obligation, bundled.

The headline invariant: every committed `FullAction` attests EXACTLY its sound `StepInv` content for
its kind. Conservation is tracked EXACTLY (`ledgerDelta`); ChainLink + ObsAdvance hold for ALL kinds;
the authority/disclosure obligations are carried per kind. `fullActionInv` is never weakened — each
kind carries its full, sound obligations (the supply kinds correctly DISCLOSE rather than conserve,
the asymmetry dregg1's catalog forces). -/

/-- **The per-`FullAction` `StepInv`** — true of every committed action, across all kinds:
  * **Ledger** — `recTotal` moved by EXACTLY `ledgerDelta` (conservation tracked precisely:
    `0`/`±amt`);
  * **ChainLink** — the chain extends by exactly `fullReceipt fa` (newest-first), no fork/rewrite;
  * **ObsAdvance** — the chain grew by exactly one row (replay-detectable);
  * **KindObligation** — the kind-specific integrity content: balance ⇒ `authorizedB`; delegate ⇒
    grounds in the source edge AND edits the graph by `addEdge`; revoke ⇒ edits by `removeEdge`;
    mint/burn ⇒ `mintAuthorizedB` AND the Generative/Annihilative `is_disclosed_non_conservation`. -/
def fullActionInv (s : RecChainedState) (fa : FullAction) (s' : RecChainedState) : Prop :=
  -- Ledger: conservation tracked EXACTLY.
  (recTotal s'.kernel = recTotal s.kernel + ledgerDelta fa) ∧
  -- ChainLink: exactly the kind's receipt, newest-first.
  (s'.log = fullReceipt fa :: s.log) ∧
  -- ObsAdvance: exactly one row.
  (s'.log.length = s.log.length + 1) ∧
  -- KindObligation: the kind-specific authority/graph/disclosure content.
  (match fa with
   | .balance a          => authorizedB s.kernel.caps a.move = true
   | .delegate del rec t =>
       Dregg2.Spec.execGraph s.kernel.caps del
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩
   | .revoke holder t    =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .mint actor cell _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity mintEffect).is_disclosed_non_conservation = true
   | .burn actor cell _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity burnEffect).is_disclosed_non_conservation = true)

/-- **`execFull_attests` — THE FULL OP-SET IS STEP-COMPLETE BY CONSTRUCTION (PROVED).** Every
committed `FullAction` — balance/effect, authority (delegate/revoke), OR supply (mint/burn) — attests
its full `StepInv` content: exact ledger conservation (`ledgerDelta`) ∧ ChainLink ∧ ObsAdvance ∧ the
kind-specific obligation (authority / graph-edit / disclosure). So the replacement executor is
step-complete across EVERY dregg1 turn kind, not just balance/effect. -/
theorem execFull_attests {s s' : RecChainedState} {fa : FullAction} (h : execFull s fa = some s') :
    fullActionInv s fa s' := by
  refine ⟨execFull_ledger s s' fa h, execFull_chainlink s s' fa h, execFull_obsadvance s s' fa h, ?_⟩
  cases fa with
  | balance a => exact execFull_balance_authorized s s' a h
  | delegate del rec t =>
      exact ⟨execFull_delegate_grounds s s' del rec t h, execFull_delegate_addEdge s s' del rec t h⟩
  | revoke holder t => exact execFull_revoke_removeEdge s s' holder t h
  | mint actor cell amt => exact ⟨execFull_mint_authorized s s' actor cell amt h, mint_discloses⟩
  | burn actor cell amt => exact ⟨execFull_burn_authorized s s' actor cell amt h, burn_discloses⟩

/-! ## §10 — The whole-turn law: ledger across a transaction of `FullAction`s.

The transaction-level conservation: a committed `execFullTurn` moves `recTotal` by the SUM of the
per-action `ledgerDelta`s (mints add, burns subtract, the rest contribute `0`) — the executable
ledger equation across the FULL op-set, the record-world analog of `Unified.unified_ledger`. -/

/-- The net ledger delta of a turn = sum of per-action deltas. -/
def turnLedgerDelta (tt : List FullAction) : ℤ := (tt.map ledgerDelta).sum

/-- **`execFullTurn_ledger` — PROVED (transaction ledger).** A committed full-turn moves `recTotal`
by exactly the net of all per-action ledger deltas: `recTotal s'.kernel = recTotal s.kernel +
turnLedgerDelta tt`. Proved by induction on the turn, reusing `execFull_ledger`. -/
theorem execFullTurn_ledger :
    ∀ (s s' : RecChainedState) (tt : List FullAction), execFullTurn s tt = some s' →
      recTotal s'.kernel = recTotal s.kernel + turnLedgerDelta tt
  | s, s', [], h => by
      simp only [execFullTurn, Option.some.injEq] at h; subst h; simp [turnLedgerDelta]
  | s, s', a :: rest, h => by
      simp only [execFullTurn] at h
      cases ha : execFull s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead : recTotal s1.kernel = recTotal s.kernel + ledgerDelta a :=
            execFull_ledger s s1 a ha
          have htail : recTotal s'.kernel = recTotal s1.kernel + turnLedgerDelta rest :=
            execFullTurn_ledger s1 s' rest h
          rw [htail, hhead]
          simp only [turnLedgerDelta, List.map_cons, List.sum_cons]; ring

/-- **`execFullTurn_conserves` — PROVED.** A committed full-turn whose net ledger delta is `0`
(balance/authority only, or balanced mint/burn) preserves `recTotal`. The all-or-nothing transaction
conserves when the supply nets out. -/
theorem execFullTurn_conserves (s s' : RecChainedState) (tt : List FullAction)
    (h : execFullTurn s tt = some s') (hzero : turnLedgerDelta tt = 0) :
    recTotal s'.kernel = recTotal s.kernel := by
  rw [execFullTurn_ledger s s' tt h, hzero, add_zero]

/-- **Every action of a committed full-turn attests `fullActionInv` — PROVED.** Step-completeness
holds at EVERY action of the transaction, across all kinds: the per-action witness threaded along
the fold. The full-op-set generalization of `TurnExecutor.execTurn_each_attests`. -/
theorem execFullTurn_each_attests :
    ∀ (s s' : RecChainedState) (tt : List FullAction), execFullTurn s tt = some s' →
      ∀ fa ∈ tt, ∃ sa sa', execFull sa fa = some sa' ∧ fullActionInv sa fa sa'
  | _, _, [], _, fa, hfa => absurd hfa List.not_mem_nil
  | s, s', a :: rest, h, b, hb => by
      simp only [execFullTurn] at h
      cases ha : execFull s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          rcases List.mem_cons.mp hb with hbeq | hbrest
          · subst hbeq; exact ⟨s, s1, ha, execFull_attests ha⟩
          · exact execFullTurn_each_attests s1 s' rest h b hbrest

/-! ## §MA — The PER-ASSET full turn executor (the `CONSERVATION_VECTOR` wired into a transaction).

§4–§10 conserve ONE scalar (`recTotal`, the `balance` field). The genuine per-asset law
(`RecordKernel.recKExecAsset_conserves_per_asset`, §MULTI-ASSET) lives over `RecordKernelState.bal`.
Here we build the full-turn executor over THAT ledger — `balanceA`/`delegate`/`revoke`/`mintA`/`burnA`
— and prove the all-or-nothing transaction moves `recTotalAsset b` by EXACTLY the net per-asset
ledger delta, for EVERY asset `b` independently. This is the executable turn whose FFI export
(`dregg_exec_full_turn`) conserves PER-ASSET (`DREGG2-GAP-MAP.md FILL 1`), not the scalar. The
`delegate`/`revoke` kinds are REUSED verbatim (`recCDelegate`/`recCRevoke`); authority is
asset-orthogonal (it edits `caps`, leaving `bal` fixed), so it contributes `0` to every asset. -/

/-- **Single-cell, single-asset credit** on the per-asset ledger: add `amt` to cell `cell`'s asset
`a`, leaving every other (cell, asset) pair untouched. The per-asset analog of `recCreditCell`. -/
def recBalCredit (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun c b => if c = cell ∧ b = a then bal c b + amt else bal c b

/-- The per-asset ledger delta of a single-cell credit: asset `a`'s supply rises by `amt` (when
`cell` is live), every OTHER asset is literally untouched. The per-asset analog of
`recCreditCell_recTotal_delta`, reusing `sum_indicator`. PROVED. -/
theorem recBalCredit_recTotalAsset (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (cell : CellId) (a : AssetId) (amt : ℤ) (hc : cell ∈ acc) (b : AssetId) :
    (∑ c ∈ acc, recBalCredit bal cell a amt c b)
      = (∑ c ∈ acc, bal c b) + (if b = a then amt else 0) := by
  by_cases hb : b = a
  · rw [if_pos hb]
    have key : (∑ c ∈ acc, recBalCredit bal cell a amt c b) - (∑ c ∈ acc, bal c b) = amt := by
      rw [← Finset.sum_sub_distrib]
      have hg : ∀ c ∈ acc, recBalCredit bal cell a amt c b - bal c b = (if c = cell then amt else 0) := by
        intro c _
        unfold recBalCredit
        by_cases hcc : c = cell
        · rw [if_pos ⟨hcc, hb⟩, if_pos hcc]; ring
        · rw [if_neg (by rintro ⟨h, _⟩; exact hcc h), if_neg hcc]; ring
      rw [Finset.sum_congr rfl hg, sum_indicator acc cell amt hc]
    omega
  · rw [if_neg hb, add_zero]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold recBalCredit; rw [if_neg (by rintro ⟨_, h⟩; exact hb h)]

/-- **The privileged per-asset MINT** over the `bal` ledger. Same `mintAuthorizedB` gate as the
scalar mint (a `node`/`control` cap, not ownership); credits cell `cell`'s asset `a` by `amt`. -/
def recKMintAsset (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts then
    some { k with bal := recBalCredit k.bal cell a amt }
  else
    none

/-- **The privileged per-asset BURN** over the `bal` ledger. Debits cell `cell`'s asset `a` by `amt`
(a credit of `-amt`), gated on availability *in that asset* + mint authority. -/
def recKBurnAsset (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a ∧ cell ∈ k.accounts then
    some { k with bal := recBalCredit k.bal cell a (-amt) }
  else
    none

/-- **Per-asset mint inflow — PROVED.** A committed per-asset mint raises asset `a`'s supply by
`amt` and leaves EVERY OTHER asset untouched: `recTotalAsset k' b = recTotalAsset k b + (if b = a
then amt else 0)`. The per-asset refinement of `recKMint_delta` (which moved one scalar). -/
theorem recKMintAsset_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recKMintAsset k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b + (if b = a then amt else 0) := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hcell⟩ := hg
    show (∑ c ∈ k.accounts, recBalCredit k.bal cell a amt c b)
        = (∑ c ∈ k.accounts, k.bal c b) + (if b = a then amt else 0)
    exact recBalCredit_recTotalAsset k.accounts k.bal cell a amt hcell b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Per-asset burn outflow — PROVED.** A committed per-asset burn lowers asset `a`'s supply by
`amt` and leaves EVERY OTHER asset untouched: `recTotalAsset k' b = recTotalAsset k b + (if b = a
then -amt else 0)`. -/
theorem recKBurnAsset_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recKBurnAsset k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b + (if b = a then (-amt) else 0) := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hcell⟩ := hg
    show (∑ c ∈ k.accounts, recBalCredit k.bal cell a (-amt) c b)
        = (∑ c ∈ k.accounts, k.bal c b) + (if b = a then (-amt) else 0)
    exact recBalCredit_recTotalAsset k.accounts k.bal cell a (-amt) hcell b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- No per-asset mint without authority — PROVED. -/
theorem recKMintAsset_authorized (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKMintAsset k actor cell a amt = some k') :
    mintAuthorizedB k.caps actor cell = true := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The chained per-asset transfer/mint/burn** (thread the receipt chain, newest-first, exactly as
`recCexec`/`recCMint`/`recCBurn` do for the scalar kernel). -/
def recCexecAsset (s : RecChainedState) (t : Turn) (a : AssetId) : Option RecChainedState :=
  match recKExecAsset s.kernel t a with
  | some k' => some { kernel := k', log := t :: s.log }
  | none    => none

/-- Chained per-asset mint. -/
def recCMintAsset (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecChainedState :=
  match recKMintAsset s.kernel actor cell a amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := amt } :: s.log }
  | none    => none

/-- Chained per-asset burn (the receipt discloses `-amt`). -/
def recCBurnAsset (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecChainedState :=
  match recKBurnAsset s.kernel actor cell a amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := -amt } :: s.log }
  | none    => none

/-! ### §MA-supply — ACCOUNT-GROWTH on the per-asset dispatch: `createCell` (born EMPTY) + `spawn`.

dregg1's `Effect::CreateCell` (`turn/src/executor/apply.rs:748`) is the PRIVILEGED creation of a FRESH
cell, born with `balance == 0` (`apply.rs:757` rejects `CreateCellNonZeroBalance`) — so on the per-asset
ledger it is conservation-NEUTRAL (`ledgerDeltaAsset = 0` for EVERY asset). `Effect::SpawnWithDelegation`
(`apply.rs` / `EffectsSupply.spawnStep`) is `createCell` PLUS a delegated parent cap to the spawned child:
the spawner must already hold a live edge to `target`, and the child receives THAT concrete held cap.
The create leg is neutral and the cap copy is bal-orthogonal, so spawn is neutral too. We reuse the
`EffectsSupply` creation gate (`mintAuthorizedB` — creation is privileged supply — AND the freshness gate
`newCell ∉ accounts`), but add the parent-edge premise so child creation cannot manufacture authority to
an unrelated target. The account growth lives in `RecordKernel.createCellIntoAsset` (grow `accounts` +
RESET the fresh `bal` column to `0`), so neutrality is PROVED via `recTotalAsset_insert_fresh`, NOT
assumed. -/

/-- **`createCellChainA` — `CreateCell`'s per-asset chained semantics.** Fail-closed: an authorized
creator (`mintAuthorizedB actor newCell` — creation coins a fresh cell, privileged like mint) AND a FRESH
id (`newCell ∉ accounts`, the exact `hfresh` the conservation lemma consumes). On commit, insert the fresh
cell (born EMPTY in every asset via `createCellIntoAsset`) and append the creation receipt (newest-first).
The dregg1-faithful born-`balance == 0`: NO amount param, conservation-NEUTRAL. -/
def createCellChainA (s : RecChainedState) (actor newCell : CellId) : Option RecChainedState :=
  if mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts then
    some { kernel := createCellIntoAsset s.kernel newCell
           log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log }
  else
    none

/-- **`createCellChainA` factors through its gate — PROVED.** A committed creation implies the two gate
conjuncts held and pins the post-state. -/
theorem createCellChainA_factors {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧
      s' = { kernel := createCellIntoAsset s.kernel newCell
             log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log } := by
  unfold createCellChainA at h
  by_cases hg : mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts
  · rw [if_pos hg, Option.some.injEq] at h; exact ⟨hg.1, hg.2, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`spawnChainA` — `SpawnWithDelegation`'s per-asset chained semantics.** Fail-closed unless
the actor can both create the fresh `child` AND already holds a live cap edge to the parent `target`.
On commit, copy the actor's concrete held parent cap to the child. This is the least-amplifying
authority handoff: child creation no longer manufactures `Cap.node target`, and an endpoint-limited
parent cap remains endpoint-limited. The cap edit is bal-orthogonal — it touches `caps`, never
`bal`/`accounts` — so the per-asset measure is unmoved (neutral). The delegation lifecycle fields are
initialized so `refreshDelegationA` has a parent/snapshot to refresh from. -/
def spawnChainA (s : RecChainedState) (actor child target : CellId) : Option RecChainedState :=
  if (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
      target ∈ s.kernel.accounts then
    match createCellChainA s actor child with
    | some s1 =>
        some { s1 with kernel :=
          { s1.kernel with caps := fun l =>
              if l = child then heldCapTo s.kernel.caps actor target :: s1.kernel.caps l
              else s1.kernel.caps l
                           delegate := fun c => if c = child then some actor else s1.kernel.delegate c
                           delegations := fun c => if c = child then s1.kernel.caps actor
                                                   else s1.kernel.delegations c } }
    | none => none
  else
    none

/-- **`spawnChainA` factors through `createCellChainA` — PROVED.** A committed spawn is a committed
`createCellChainA` (into `s1`) whose parent target was already live and held by the actor, followed by
the concrete held-cap copy and initial delegation snapshot. -/
theorem spawnChainA_factors {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    ∃ s1, ((s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
             target ∈ s.kernel.accounts) ∧
      createCellChainA s actor child = some s1 ∧
      s' = { s1 with kernel :=
        { s1.kernel with caps := fun l =>
            if l = child then heldCapTo s.kernel.caps actor target :: s1.kernel.caps l
            else s1.kernel.caps l
                         delegate := fun c => if c = child then some actor else s1.kernel.delegate c
                         delegations := fun c => if c = child then s1.kernel.caps actor
                                                 else s1.kernel.delegations c } } := by
  unfold spawnChainA at h
  by_cases hg : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
      target ∈ s.kernel.accounts
  · rw [if_pos hg] at h
    cases hc : createCellChainA s actor child with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some s1 =>
        rw [hc] at h
        simp only [Option.some.injEq] at h
        exact ⟨s1, hg, rfl, h.symm⟩
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **`createCellChainA_neutral` — ACCOUNT-GROWTH IS CONSERVATION-NEUTRAL (PROVED).** A committed
`createCellChainA` leaves `recTotalAsset` UNCHANGED for EVERY asset `b`: the index set `accounts`
genuinely GREW (`createCellChainA_grows_accounts`), but the fresh cell is born EMPTY (`bal`-reset), so its
contribution is exactly `0` (`recTotalAsset_insert_fresh`, with `hfresh` from the freshness gate). The
account-growth neutrality the per-asset dispatch demands. -/
theorem createCellChainA_neutral {s s' : RecChainedState} {actor newCell : CellId} (b : AssetId)
    (h : createCellChainA s actor newCell = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hfresh, hs'⟩ := createCellChainA_factors h
  subst hs'
  exact recTotalAsset_insert_fresh s.kernel newCell b hfresh

/-- **`createCellChainA_grows_accounts` — the GROWTH has teeth (PROVED).** After a committed
`createCellChainA`, the new cell IS a live account (`newCell ∈ accounts`) — the index set genuinely grew,
so the neutrality theorem is NOT a no-op. -/
theorem createCellChainA_grows_accounts {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') : newCell ∈ s'.kernel.accounts := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'; exact createCellIntoAsset_grows_accounts s.kernel newCell

/-- **`createCellChainA_authorized` — PROVED (fail-closed integrity).** A committed creation implies the
creator held the privileged creation authority over the new cell (`mintAuthorizedB` — bare ownership is
NOT enough; creation coins a fresh cell). -/
theorem createCellChainA_authorized {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  (createCellChainA_factors h).1

/-- **`createCellChainA_unauthorized_fails` — PROVED (fail-closed).** Without creation authority, no cell
is minted. The confinement core. -/
theorem createCellChainA_unauthorized_fails (s : RecChainedState) (actor newCell : CellId)
    (h : mintAuthorizedB s.kernel.caps actor newCell = false) :
    createCellChainA s actor newCell = none := by
  unfold createCellChainA
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **`createCellChainA_chainlink` — PROVED.** A committed creation extends the receipt chain by EXACTLY
the (balance-`0`) creation row, newest-first. -/
theorem createCellChainA_chainlink {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    s'.log = { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h; subst hs'; rfl

/-- The spawn metadata/cap copy is bal-orthogonal — it edits `caps`, parent pointer, and delegation
snapshot, never `bal`/`accounts` — so the per-asset measure is literally unchanged (PROVED). -/
theorem spawnGrant_recTotalAsset (k : RecordKernelState) (actor child : CellId) (cap : Cap)
    (b : AssetId) :
    recTotalAsset { k with caps := fun l => if l = child then cap :: k.caps l else k.caps l
                           delegate := fun c => if c = child then some actor else k.delegate c
                           delegations := fun c => if c = child then k.caps actor else k.delegations c } b
      = recTotalAsset k b := rfl

/-- **`spawnChainA_neutral` — PROVED.** A committed spawn leaves `recTotalAsset` UNCHANGED for EVERY asset:
the create leg is neutral (born EMPTY), the cap grant is bal-orthogonal. -/
theorem spawnChainA_neutral {s s' : RecChainedState} {actor child target : CellId} (b : AssetId)
    (h : spawnChainA s actor child target = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors h
  subst hs'
  rw [spawnGrant_recTotalAsset s1.kernel actor child (heldCapTo s.kernel.caps actor target) b]
  exact createCellChainA_neutral b hc

/-- **`spawnChainA_authorized` — PROVED.** A committed spawn implies the spawner held creation authority
over the child. -/
theorem spawnChainA_authorized {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    mintAuthorizedB s.kernel.caps actor child = true := by
  obtain ⟨s1, _, hc, _⟩ := spawnChainA_factors h
  exact createCellChainA_authorized hc

/-- **`spawnChainA_grounds` — PROVED.** A committed spawn implies the actor already held a live
connectivity edge to the parent target. Child creation alone cannot introduce an unrelated edge. -/
theorem spawnChainA_grounds {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    Dregg2.Spec.execGraph s.kernel.caps actor
        (⟨target, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
      target ∈ s.kernel.accounts := by
  obtain ⟨_, hg, _, _⟩ := spawnChainA_factors h
  exact hg

/-- **`spawnChainA_provenance` (the DISCLOSED-AUTHORITY keystone — PROVED).** The spawned child receives
EXACTLY the concrete cap the actor already held to the parent target. This preserves rights (endpoint
rights stay endpoint rights) instead of manufacturing `node target` control. -/
theorem spawnChainA_provenance {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    heldCapTo s.kernel.caps actor target ∈ s'.kernel.caps child := by
  obtain ⟨s1, _, _, hs'⟩ := spawnChainA_factors h
  subst hs'
  simp

/-- **`spawnChainA_parent_snapshot` — PROVED.** Spawn initializes the delegation lifecycle: the child
records its parent (`actor`) and stores a birth snapshot of the parent's current c-list. -/
theorem spawnChainA_parent_snapshot {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    s'.kernel.delegate child = some actor ∧ s'.kernel.delegations child = s.kernel.caps actor := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors h
  subst hs'
  have hcaps : s1.kernel.caps = s.kernel.caps := by
    obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
    subst hs1
    rfl
  simp only [if_true, true_and]
  rw [hcaps]

/-- **`spawnChainA_chainlink` — PROVED.** A committed spawn extends the receipt chain by EXACTLY the
child's (balance-`0`) creation row (the cap grant edits only `caps`, not the log). -/
theorem spawnChainA_chainlink {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    s'.log = { actor := actor, src := child, dst := child, amt := 0 } :: s.log := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors h
  subst hs'
  show s1.log = { actor := actor, src := child, dst := child, amt := 0 } :: s.log
  exact createCellChainA_chainlink hc

/-! ### §MA-factory — `CreateCellFromFactory` (dregg1 `apply_create_cell_from_factory`, `apply.rs:3112`).

`CreateCellFromFactory` is `CreateCell` PLUS the factory's published contract: validate the factory
exists in the registry and the creation is within its declared constraints (`validate_and_record`,
`apply.rs:3140`), then mint a cell carrying the factory's initial fields, program VK, AND — the
load-bearing part — the factory's `slotCaveats` (its `program`, `apply.rs:3197`+), which the executor
then enforces on EVERY later `SetField`. Like `CreateCell`, the cell is born `balance == 0`
(`apply.rs:757` rejects nonzero balance) — conservation-NEUTRAL — but the CONSTRAINTS are the point:
the minted cell carries its lifetime invariants from birth, so a `nameservice`/`subscription` cell is
*registered-forever / monotone-head* the instant it exists. -/

/-- The factory's `programVk` field name (the installed VK hash slot, `apply.rs:3197`). -/
def factoryVkField : FieldName := "factory_program_vk"

/-- Write the factory's declared INITIAL fields `(field, value)` onto a cell record (a left fold of
named-field writes; the LAST write to a repeated field wins). Touches only the named fields — the
`balance` field is left at its born-`0` value (dregg1 forbids nonzero balance at creation). -/
def installInitialFields (cell : Value) : List (FieldName × Int) → Value
  | []            => cell
  | (f, v) :: rest => installInitialFields (setField f cell (.int v)) rest

/-- **`createCellFromFactoryChainA` — `CreateCellFromFactory`'s per-asset chained semantics.**
Fail-closed in lock-step with dregg1's `apply_create_cell_from_factory`:
  1. the factory must EXIST in the registry (`findFactory s.kernel.factories vk`, `apply.rs:3140`);
  2. its declared initial state must CONFORM to its own caveats (`FactoryEntry.conforms` — a factory
     cannot publish initial fields that already violate the invariants it claims, `validate_and_record`);
  3. the creator must hold privileged creation authority + the id must be fresh (reuses
     `createCellChainA`'s exact `mintAuthorizedB ∧ ∉ accounts` gate, `apply.rs:3179`/:757).
On commit: mint the fresh EMPTY cell (`createCellChainA`), write the factory's initial fields + the
program-VK slot, and INSTALL the factory's `slotCaveats` onto the minted cell — so its published
invariants are enforced for life. Balance-NEUTRAL (born `0`; initial fields are non-`balance` slots). -/
def createCellFromFactoryChainA (s : RecChainedState) (actor newCell : CellId) (vk : Int) :
    Option RecChainedState :=
  -- (0) REJECT a negative `vk` BEFORE the registry lookup: `findFactory … vk.toNat` would otherwise
  -- collapse every negative key to `0` (`Int.toNat (-1) = 0`), so a negative `vk` would silently ALIAS
  -- factory `0`. Fail-closed on `vk < 0` so the content-addressed key cannot be forged downward.
  if 0 ≤ vk then
  match findFactory s.kernel.factories vk.toNat with
  | none   => none                              -- (1) unknown factory: fail closed (`apply.rs:3140`)
  | some e =>
      if e.conforms = true then                 -- (2) the factory's own constraints validate
        match createCellChainA s actor newCell with   -- (3) the privileged + fresh creation gate
        | some s1 =>
            some { s1 with kernel :=
              { s1.kernel with
                  -- install the factory's initial fields + the program-VK slot onto the minted cell:
                  cell := fun c => if c = newCell then
                      setField factoryVkField
                        (installInitialFields (s1.kernel.cell newCell) e.initialFields) (.int e.programVk)
                    else s1.kernel.cell c
                  -- INSTALL the factory's slot caveats onto the minted cell (its lifetime program):
                  slotCaveats := fun c => if c = newCell then e.caveats else s1.kernel.slotCaveats c } }
        | none => none
      else none
  else none                                       -- (0) negative `vk`: fail closed (no factory aliasing)

/-- **`createCellFromFactoryChainA` factors through its gates — PROVED.** A committed factory creation
implies: the factory was found, it conformed, and the underlying `createCellChainA` committed (into an
intermediate `s1`), with the post-state EXACTLY the field+caveat install over `s1`. The bridge every
downstream factory theorem reuses. -/
theorem createCellFromFactoryChainA_factors {s s' : RecChainedState} {actor newCell : CellId} {vk : Int}
    (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    ∃ e s1, findFactory s.kernel.factories vk.toNat = some e ∧ e.conforms = true ∧
      createCellChainA s actor newCell = some s1 ∧
      s' = { s1 with kernel :=
        { s1.kernel with
            cell := fun c => if c = newCell then
                setField factoryVkField
                  (installInitialFields (s1.kernel.cell newCell) e.initialFields) (.int e.programVk)
              else s1.kernel.cell c
            slotCaveats := fun c => if c = newCell then e.caveats else s1.kernel.slotCaveats c } } := by
  unfold createCellFromFactoryChainA at h
  split at h                                      -- (0) the `0 ≤ vk` guard
  · split at h
    · exact absurd h (by simp)                   -- factory not found ⇒ `none`
    · next e he =>
        split at h
        · next hcf =>                            -- conforms = true
            split at h
            · next s1 hc =>
                simp only [Option.some.injEq] at h
                exact ⟨e, s1, he, hcf, hc, h.symm⟩
            · next hc => exact absurd h (by simp)-- createCell failed ⇒ `none`
        · exact absurd h (by simp)               -- non-conforming factory ⇒ `none`
  · exact absurd h (by simp)                     -- negative `vk` ⇒ `none`

/-- The field+caveat install over a born-EMPTY cell leaves `recTotalAsset` UNCHANGED — the installed
fields are named record slots (not the `bal` ledger), and `slotCaveats` is balance-orthogonal. PROVED. -/
theorem factoryInstall_recTotalAsset (k : RecordKernelState) (newCell : CellId)
    (cellVal : Value) (cav : List SlotCaveat) (b : AssetId) :
    recTotalAsset { k with cell := fun c => if c = newCell then cellVal else k.cell c
                           slotCaveats := fun c => if c = newCell then cav else k.slotCaveats c } b
      = recTotalAsset k b := rfl

/-- **`createCellFromFactoryChainA_neutral` — FACTORY CREATION IS CONSERVATION-NEUTRAL (PROVED).** A
committed factory creation leaves `recTotalAsset` UNCHANGED for EVERY asset: the cell is born EMPTY
(`createCellChainA_neutral`), and the field/caveat install is balance-orthogonal
(`factoryInstall_recTotalAsset`). The account-growth-with-program neutrality. -/
theorem createCellFromFactoryChainA_neutral {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (b : AssetId) (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨e, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  subst hs'
  rw [factoryInstall_recTotalAsset s1.kernel newCell _ _ b]
  exact createCellChainA_neutral b hc

/-- The factory creation install leaves `escrows` UNCHANGED (a creation never touches the holding-store),
hence the COMBINED measure moves exactly as `recTotalAsset` (PROVED). -/
theorem createCellFromFactoryChainA_neutralWithEscrow {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (b : AssetId) (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  obtain ⟨e, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  -- the field/caveat install leaves `escrows` UNTOUCHED (it edits only `cell`/`slotCaveats`), and the
  -- underlying createCell leaves `escrows` fixed too — so `escrowHeldAsset` is unchanged end to end.
  have hesc' : escrowHeldAsset s'.kernel b = escrowHeldAsset s.kernel b := by
    obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
    subst hs' hs1; rfl
  simp only [recTotalAssetWithEscrow]
  rw [hesc', show recTotalAsset s'.kernel b = recTotalAsset s.kernel b from
        createCellFromFactoryChainA_neutral b h]

/-- **`createCellFromFactoryChainA_authorized` — PROVED (fail-closed integrity).** A committed factory
creation implies the creator held privileged creation authority over the new cell (`mintAuthorizedB`). -/
theorem createCellFromFactoryChainA_authorized {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true := by
  obtain ⟨_, _, _, _, hc, _⟩ := createCellFromFactoryChainA_factors h
  exact createCellChainA_authorized hc

/-- **`createCellFromFactoryChainA_grows_accounts` — the GROWTH has teeth (PROVED).** After a committed
factory creation, the new cell IS a live account — the registry grew, the neutrality is NOT a no-op. -/
theorem createCellFromFactoryChainA_grows_accounts {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    newCell ∈ s'.kernel.accounts := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  -- the field/caveat install keeps `accounts := s1.kernel.accounts` (it edits only `cell`/`slotCaveats`):
  subst hs'
  show newCell ∈ s1.kernel.accounts
  exact createCellChainA_grows_accounts hc

/-- **`createCellFromFactoryChainA_installs_program` (THE FACTORY KEYSTONE — PROVED).** Every cell a
factory mints carries EXACTLY the factory's declared `slotCaveats` (its published program). So anyone
who knows the factory exists knows the cell's lifetime invariants — and the executor enforces them on
every later `SetField` (via `stateStepGuarded`, since `setFieldA` reads `slotCaveats`). The executable
shadow of `Factory.constructor_transparency`, now over the LIVE executor state. -/
theorem createCellFromFactoryChainA_installs_program {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    ∃ e, findFactory s.kernel.factories vk.toNat = some e ∧
      s'.kernel.slotCaveats newCell = e.caveats := by
  obtain ⟨e, s1, hfind, _, _, hs'⟩ := createCellFromFactoryChainA_factors h
  refine ⟨e, hfind, ?_⟩
  subst hs'; simp

/-- **`createCellFromFactoryChainA_unknown_factory_fails` — PROVED (fail-closed).** An unknown factory
VK never mints a cell (dregg1 `apply.rs:3140` `validate_and_record` errors `factory creation failed`). -/
theorem createCellFromFactoryChainA_unknown_factory_fails (s : RecChainedState) (actor newCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    createCellFromFactoryChainA s actor newCell vk = none := by
  simp only [createCellFromFactoryChainA, h, ite_self]

/-- **`createCellFromFactoryChainA_nonconforming_fails` — PROVED (fail-closed).** A factory whose own
declared initial state VIOLATES its own caveats never mints (the `validate_and_record` constraint
check rejects, `apply.rs:3140`). -/
theorem createCellFromFactoryChainA_nonconforming_fails (s : RecChainedState) (actor newCell : CellId)
    (vk : Int) (e : FactoryEntry) (hfind : findFactory s.kernel.factories vk.toNat = some e)
    (hbad : e.conforms = false) :
    createCellFromFactoryChainA s actor newCell vk = none := by
  simp only [createCellFromFactoryChainA, hfind, hbad, Bool.false_eq_true, if_false, ite_self]

/-- **`createCellFromFactoryChainA_balance_field_fails` — PROVED (fail-closed).** Factory initial fields
cannot initialize the reserved scalar `balance` field. The fresh per-asset ledger is born empty
separately; permitting a record-level `"balance"` initializer would split the scalar view from the
conserved asset ledger. -/
theorem createCellFromFactoryChainA_balance_field_fails (s : RecChainedState) (actor newCell : CellId)
    (vk : Int) (e : FactoryEntry) (hfind : findFactory s.kernel.factories vk.toNat = some e)
    (hbad : e.initialFieldsNoBalance = false) :
    createCellFromFactoryChainA s actor newCell vk = none := by
  have hconf : e.conforms = false := by
    unfold FactoryEntry.conforms
    rw [hbad]
    simp
  exact createCellFromFactoryChainA_nonconforming_fails s actor newCell vk e hfind hconf

/-- **`createCellFromFactoryChainA_chainlink` — PROVED.** A committed factory creation extends the
receipt chain by EXACTLY the (balance-`0`) creation row (the field/caveat install edits state, not
the log). -/
theorem createCellFromFactoryChainA_chainlink {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    s'.log = { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  subst hs'
  -- the field/caveat install edits only `kernel.cell`/`kernel.slotCaveats`, never `log`:
  show s1.log = { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log
  exact createCellChainA_chainlink hc

/-- **`createCellFromFactoryChainA_sideTables` — PROVED.** A committed factory creation leaves the
SET-shaped side-tables (`commitments`, `nullifiers`, `revoked`, `escrows`) UNTOUCHED: `createCell`
edits only `accounts`/`bal`, and the field/caveat install edits only `cell`/`slotCaveats`. The frame
the carried-forever crowns (`CellCommit`/`CellNullifier`/`CellConfine`) reuse for the new effect. -/
theorem createCellFromFactoryChainA_sideTables {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧
      s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.escrows = s.kernel.escrows := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
  subst hs' hs1
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`createCellFromFactoryChainA_caps_eq` — PROVED.** A committed factory creation leaves the cap
table UNTOUCHED: `createCell` edits `accounts`/`bal`, and the field/caveat install edits `cell`/
`slotCaveats` — never `caps`. The frame the confinement crown (`CellConfine`) reuses. -/
theorem createCellFromFactoryChainA_caps_eq {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
  subst hs' hs1; rfl

/-! ### §MA-state — the 5 PURE-STATE (field/log) effects on the per-asset dispatch.

dregg1's `turn/src/executor/apply.rs` runs FIVE effects that write the cell-RECORD (a named field)
or the LOG, and NEVER touch the per-asset `bal` ledger:

  * `SetField { cell, index, value }` (`apply_set_field` ~:497) — a state-slot write, gated by the
    `idx < STATE_SLOTS` bound + (for a cross-cell target) the `SetState` permission;
  * `EmitEvent { cell, event }` (`apply_emit_event` ~:703) — a journal append, gated ONLY by
    cell-existence (NO authority/cross-cell check — the integrity-free observation move);
  * `IncrementNonce { cell }` (`apply_increment_nonce` ~:719) — a monotone counter bump, gated by
    the `IncrementNonce` permission (cross-cell);
  * `SetPermissions { cell, new_permissions }` (`apply_set_permissions` ~:775) — the permission
    snapshot write, gated by the `SetPermissions` permission (dregg1 applies it LAST off the ORIGINAL
    permission snapshot — see the per-effect `stateAuthB` gate below);
  * `SetVerificationKey { cell, new_vk }` (`apply_set_verification_key` ~:803) — the VK-field write,
    gated by `SetVerificationKey` permission (the VK hash-integrity check is a §8 Prop-carrier
    portal, off this executable layer).

ALL FIVE carry `Effect::linearity ∈ {Neutral, Monotonic}` (`EffectsState §7`: `setField`/`emitEvent`/
`setPermissions`/`setVerificationKey` Neutral; `incrementNonce` Monotonic) — the NON-balance regime.
Their per-asset semantics are ALREADY proven in `Exec/EffectsState.lean` (`stateStep` + the
neutrality lemmas): the chained `stateStep` writes ONLY `kernel.cell` (a named field) + appends a
receipt, leaving `kernel.bal` and `kernel.accounts` literally untouched. So their `ledgerDeltaAsset`
is `0` for EVERY asset and `recTotalAsset` is UNCHANGED — balance-NEUTRALITY, proved (not assumed)
below. Here we WIRE those proven steps into the executed `execFullA` dispatch (we do NOT re-prove the
per-effect semantics). -/

/-- **Balance-NEUTRALITY of a field write over the per-asset ledger — PROVED (the load-bearing
keystone for the 5 pure-state effects).** `EffectsState.writeField` updates ONLY the record map
`cell` of the kernel; it touches NEITHER `bal` NOR `accounts`. So `recTotalAsset` (= `∑ c ∈
accounts, bal c b`) is LITERALLY UNCHANGED for EVERY asset `b`. THIS is what makes the 5 pure-state
effects per-asset conservation-trivial: a `nonce`/`status`/`permissions`/`vk` write cannot move ANY
asset's supply. (Contrast `recBalCredit_recTotalAsset`, which DOES move `bal` — these effects never
write `bal`.) -/
theorem writeField_recTotalAsset (k : RecordKernelState) (f : FieldName) (target : CellId)
    (v : Value) (b : AssetId) : recTotalAsset (writeField k f target v) b = recTotalAsset k b := by
  -- `writeField k f target v = { k with cell := … }`; `bal` and `accounts` are the SAME projections.
  rfl

/-- **Balance-NEUTRALITY of a committed `stateStep` over the per-asset ledger — PROVED.** A committed
`EffectsState.stateStep` (the chained field-write the 5 pure-state effects run) leaves `recTotalAsset
b` UNCHANGED for EVERY asset `b`: it writes a named record field, never the `bal` ledger. The
per-asset analog of `EffectsState.state_conserves` (which preserved the scalar `recTotal`); here it
holds for the asset VECTOR with NO side-condition on the field name (a write to ANY field, even
`balance`, leaves the `bal` ledger fixed — the `bal` ledger is independent of the `cell` record). -/
theorem stateStep_recTotalAsset {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (h : stateStep s f actor target v = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hs'⟩ := stateStep_factors h
  subst hs'
  exact writeField_recTotalAsset s.kernel f target v b

/-- **Balance-NEUTRALITY of a committed CAVEAT-GATED write over the COMBINED per-asset measure —
PROVED.** The slot-caveat gate (`EffectsState.stateStepGuarded`) commits EXACTLY the underlying
`stateStep` post-state (`stateStepGuarded_eq`), which writes a named record field and never the
`bal` ledger / `escrows` holding-store — so `recTotalAssetWithEscrow b` is UNCHANGED for EVERY asset.
The per-asset analog the `setFieldA` conservation arm reuses now that `setFieldA` routes through the
caveat gate (dregg1 `apply_set_field` → `RecordProgram::evaluate`). -/
theorem stateStepGuarded_recTotalAssetWithEscrow {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int} (h : stateStepGuarded s f actor target n = some s')
    (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h)
  subst hs'
  simp only [recTotalAssetWithEscrow]
  rw [writeField_recTotalAsset s.kernel f target (.int n) b,
      show escrowHeldAsset (writeField s.kernel f target (.int n)) b = escrowHeldAsset s.kernel b from rfl]

/-- **The `EmitEvent` raw chained step — log-only, authority-FREE (dregg1 `apply_emit_event` ~:703).**
Unlike the field-writing effects, `EmitEvent` runs NO authority/cross-cell check (in dregg1 the only
gate is cell-existence) and writes NO state — it appends an event receipt to the chain and nothing
else. We model the observation faithfully: a self-`Turn` receipt (amount `0`) carrying the event,
with the kernel UNCHANGED (so `bal`/`cell`/`caps`/`accounts` are all fixed). The `topic`/`data`
ride the receipt's `src`/`dst` as the event payload markers. The concrete `execFullA` branch gates
this raw append on `cell ∈ accounts`. -/
def emitStep (s : RecChainedState) (actor cell : CellId) (topic data : Int) : RecChainedState :=
  { kernel := s.kernel,
    log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }

/-- **`emitStep` is balance-NEUTRAL — PROVED.** `EmitEvent` leaves the kernel (hence `recTotalAsset
b` for EVERY asset `b`) UNCHANGED — it only appends a receipt. -/
theorem emitStep_recTotalAsset (s : RecChainedState) (actor cell : CellId) (topic data : Int)
    (b : AssetId) : recTotalAsset (emitStep s actor cell topic data).kernel b = recTotalAsset s.kernel b := rfl

/-- **`emitStep` advances the chain by exactly one row — PROVED** (the observation/replay clock). -/
theorem emitStep_obsadvance (s : RecChainedState) (actor cell : CellId) (topic data : Int) :
    (emitStep s actor cell topic data).log.length = s.log.length + 1 := by simp [emitStep]

/-- **The canonical field names the 4 field-writing pure-state effects target** (the metatheory's
named-field model of dregg1's `state.fields[index]` slot / `permissions` / `verification_key`). -/
def nonceField : FieldName := "nonce"
def permsField : FieldName := "permissions"
def vkField    : FieldName := "verification_key"

/-! ### §MA-seal — the 6 SIMPLE bal-neutral effects (Wave 6) on the per-asset dispatch.

dregg1's `turn/src/executor/apply.rs` runs a cluster of SIMPLE effects that flip a cell flag, write a
metadata field, or record a receipt/refusal — and NEVER touch the per-asset `bal` ledger. Each is
balance-NEUTRAL (`ledgerDeltaAsset = 0` for EVERY asset, `recTotalAsset` UNCHANGED), modeled FAITHFULLY
as a `stateStep` field-write (the SAME already-proven authority-gated record write the 5 pure-state
effects use) — the STATE move is real (a flag/marker/lifecycle field genuinely changes), while the §8
CRYPTO is an HONEST portal carried at the chain layer, NEVER proved sound here:

  * `Seal { pair_id, capability }` (`apply_seal` ~:2743) — store a sealed box (an AEAD ciphertext of a
    held cap). The STATE move is the record write; the AEAD itself is the §8 CryptoPortal. Authority:
    the actor holds the sealer cap over its cell (modeled as `stateAuthB actor cell` — the c-list read).
    Catalog: `Generative` (it generates a fresh sealed box).
  * `Unseal { sealed_box, recipient }` (`apply_unseal` ~:2874) — reveal the capability UNDER the §8 AEAD
    portal (the decrypt verify is the §8 carrier, NOT proved sound). The STATE move is the reveal record.
    Authority: holds the unsealer cap (`stateAuthB`). Catalog: `Generative`.
  * `CreateSealPair { sealer_holder, unsealer_holder }` (`apply_create_seal_pair` ~:2675) — establish a
    seal keypair (dregg1 grants sealer/unsealer caps; the AEAD KEYPAIR is the §8 portal). The STATE move
    is the metadata write recording the pair into the sealer-holder's record. Authority: `stateAuthB
    actor sealerHolder` (write to the holder's record). Catalog: `Generative`.
  * `MakeSovereign { cell }` (`apply_make_sovereign` ~:3084) — convert a cell to commitment-only
    (sovereign) REPRESENTATION. ASSESSED bal-neutral: dregg1's `ledger.make_sovereign` flips the HOSTING
    representation flag and PRESERVES balance/state/history (NO value moves into commitment-form on the
    per-asset ledger — it is a representation move, not an escrow). Modeled as the `stateStep` flag write.
    Authority: dregg1 requires `cell == action_target` (self-sovereign) ⇒ the cell's own authority
    (`stateAuthB actor cell`). Catalog: `Terminal` (one-way; no inverse). The commitment binding is the
    §8 portal at the chain layer (exactly as bridgeMint's foreign finality).
  * `Refusal { cell, … }` (`apply_refusal` ~:4114) — record a refusal witness: bump the nonce and write
    the refusal commitment into the audit field; dregg1 NEVER mutates balance/caps/value. bal-NEUTRAL.
    Authority: dregg1 gates a CROSS-cell refusal on `SetState` (modeled `stateAuthB actor cell`).
    Catalog: `Monotonic` (the nonce bump).
  * `ReceiptArchive { prefix_end_height, checkpoint }` (`apply_receipt_archive` ~:4441) — archive/prune
    the receipt-chain prefix: transition lifecycle to `Archived` (the cell stays live) + bind the
    checkpoint. A LOG/field operation; bal-NEUTRAL. Authority: dregg1 requires the checkpoint cell_id =
    action_target (`stateAuthB actor cell`). Catalog: `Terminal`.

ALL SIX route through `EffectsState.stateStep` (the ALREADY-PROVEN authority-gated field write), so
their per-asset balance-NEUTRALITY is PROVED off `writeField_recTotalAsset`/`stateStep_recTotalAsset`
(exactly as `setFieldA`/`incrementNonceA`/`setPermissionsA`/`setVKA`) — we do NOT re-prove the per-effect
step. The catalog COLORING (the faithful-mirror tripwire) is carried in the `fullActionInvA`
`KindObligation` per effect. -/

/-- The record fields the 5 simple field-writing bal-neutral effects target (the metatheory's
named-field model of dregg1's `sealed_box` store / `field[4]` refusal-audit slot / `lifecycle`).
The STATE move writes these; the §8 crypto (AEAD ciphertext) lives in the portal. (`MakeSovereign`
is NOT a field write but a whole-record VALUE-REBIND — FILL #133 below, `makeSovereignStep` — so it
has no field name; its commitment lands in `commitmentField`, not a `sovereign` flag.) -/
def sealField      : FieldName := "sealed_box"
def unsealField    : FieldName := "unsealed"
def sealPairField  : FieldName := "seal_pair"
def refusalField   : FieldName := "refusal"
def lifecycleField : FieldName := "lifecycle"

/-! ### §MA-sovereign (FILL #133) — `MakeSovereign` is a VALUE-REBIND, not a flag.

The wave-6 model wrote `sovereign := 1` (a status flag) and LEFT the cell's full record readable.
That is NOT what dregg1's `apply_make_sovereign` → `Ledger::make_sovereign` (`cell/src/ledger.rs:1014`)
does:

```rust
pub fn make_sovereign(&mut self, id: &CellId) -> Result<Cell, LedgerError> {
    let cell = self.cells.remove(id)?;              // the host DROPS the readable cell
    let commitment = cell.state_commitment();        // … and keeps ONLY a 32-byte commitment
    self.sovereign_commitments.insert(*id, commitment);
    self.dirty = true;
    Ok(cell)
}
```

The cell's full state is **REMOVED** from the host-readable `cells` map and **REPLACED** by a
commitment-only representation in `sovereign_commitments`. The host can no longer read the cell's
value/balance/nonce/permissions directly — to learn anything it must OPEN the commitment behind the
§8 CryptoPortal (the federation stores only the 32-byte hash; the sovereign agent holds the preimage).
That is the whole point of "making a cell sovereign": its state moves off the host and behind a
commitment. A flag write models NONE of this — the value stays right there, readable.

We re-model the value-rebind faithfully: `makeSovereignStep` REPLACES `target`'s entire `cell` record
with the commitment-only record `[(commitmentField, .dig (stateCommitment v))]`, where `v` is the
pre-state value and `stateCommitment` is the deterministic §8 hash (`cell.state_commitment()`). The
host-readable scalar fields (`balance`, `nonce`, …) become `none` (no longer directly readable — the
teeth, `makeSovereignStep_balance_unreadable`), while the commitment IS present and binds the preimage
(`makeSovereignStep_commitment_present`/`_binds_preimage`). It stays bal-NEUTRAL **on the per-asset
ledger**: `recTotalAsset`/`recTotalAssetWithEscrow` read `k.bal`/`k.escrows`, which are independent of
`k.cell` — so a value-rebind that touches ONLY `k.cell` cannot move any asset's supply (the SAME
`rfl`-grade conservation `writeField_recTotalAsset` enjoys, since it too touches only `k.cell`). The
commitment binding (collision-resistance of `state_commitment`) is the §8 chain-layer portal — NOT
proved sound here; what IS proved is the value-rebind itself: the readable state is genuinely gone. -/

/-- The field carrying the post-rebind state commitment (dregg1's `sovereign_commitments[id]` slot,
a 32-byte `cell.state_commitment()`). The commitment-only record carries EXACTLY this field. -/
def commitmentField : FieldName := "commitment"

/-- **`stateCommitment v`** — the metatheory's model of dregg1's `cell.state_commitment()`
(`cell/src/commitment.rs`): a DETERMINISTIC hash of the cell's FULL state into a digest tag. The
exact hash is the §8 CryptoPortal (collision-resistance ASSUMED, not proved); all the value-rebind
needs is that it is a *function of the whole pre-state value* (so distinct pre-states give distinct
commitment records — witnessed by the `#eval`s). A simple structural Gödel-style fold suffices for
the model: leaves hash to small tags, records fold their (field-position, sub-hash) pairs. -/
def stateCommitment : Value → Nat
  | .int i  => 2 * (Int.natAbs i) + (if i < 0 then 1 else 0) |>.succ.succ.succ
  | .dig d  => 7 * d + 3
  | .sym s  => 11 * s + 5
  | .record fs => 13 * (commitFields fs) + 1
where
  /-- Fold a record's fields into a hash, mixing each field's position so that field ORDER and the
  per-field sub-hash both contribute (a structural digest of the whole record). -/
  commitFields : List (FieldName × Value) → Nat
  | []             => 17
  | (_, v) :: rest => (commitFields rest) * 31 + (stateCommitment v) + 19

/-- **`sovereignRebind cell target`** — REPLACE `target`'s entire cell with the commitment-only
record `[(commitmentField, .dig (stateCommitment (cell target)))]`. The faithful kernel-level model of
`cells.remove(id)` + `sovereign_commitments.insert(id, cell.state_commitment())`: the readable record
is GONE; only the commitment remains. Every other cell untouched. (Contrast `writeField`, which keeps
the record and edits ONE field — the wave-6 flag model. THIS drops the whole record.) -/
def sovereignRebind (cell : CellId → Value) (target : CellId) : CellId → Value :=
  fun c => if c = target then .record [(commitmentField, .dig (stateCommitment (cell target)))]
           else cell c

/-- **`makeSovereignKernel k target`** — apply the value-rebind to the record kernel: the `cell`
function is replaced by `sovereignRebind`; `bal`/`accounts`/`caps`/`escrows`/side-tables ALL fixed
(the rebind is a pure host-representation move on `cell`, never the per-asset ledger). -/
def makeSovereignKernel (k : RecordKernelState) (target : CellId) : RecordKernelState :=
  { k with cell := sovereignRebind k.cell target }

/-- **`makeSovereignStep` — the executable semantics of `MakeSovereign` (PROVED computable).**
Fail-closed: commits only when the actor holds authority over `target` (dregg1's self-sovereign gate
`cell == action_target` ⇒ the cell's own authority, `stateAuthB`). On commit, REBIND `target` into
commitment-form (the readable state is dropped behind the §8 commitment) and extend the receipt chain
by one row (the metadata clock). NO `bal` move, NO cap edit — the regime invariant. -/
def makeSovereignStep (s : RecChainedState) (actor target : CellId) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor target = true then
    some { kernel := makeSovereignKernel s.kernel target,
           log    := { actor := actor, src := target, dst := target, amt := 0 } :: s.log }
  else
    none

/-- **`makeSovereignStep_factors` — PROVED.** A committed `makeSovereignStep` was authorized and
produced exactly the commitment-rebind post-state + a one-row chain extension. The bridge every
downstream `makeSovereign` theorem reuses (the analog of `stateStep_factors`). -/
theorem makeSovereignStep_factors {s s' : RecChainedState} {actor target : CellId}
    (h : makeSovereignStep s actor target = some s') :
    stateAuthB s.kernel.caps actor target = true ∧
    s' = { kernel := makeSovereignKernel s.kernel target,
           log    := { actor := actor, src := target, dst := target, amt := 0 } :: s.log } := by
  unfold makeSovereignStep at h
  by_cases hauth : stateAuthB s.kernel.caps actor target = true
  · rw [if_pos hauth] at h
    exact ⟨hauth, (Option.some.inj h).symm⟩
  · rw [if_neg hauth] at h; exact absurd h (by simp)

/-- **Balance-NEUTRALITY of the value-rebind over the per-asset ledger — PROVED (`rfl`-grade).** The
`makeSovereignKernel` rebind touches ONLY `k.cell`; `recTotalAsset` reads `k.bal`/`k.accounts`, which
are the SAME projections — so it is `rfl`-unchanged for EVERY asset. THIS is why making a cell
sovereign cannot move any asset's supply (the value moves behind the commitment on the host, not on
the per-asset ledger): the per-asset balance is a separate domain. The exact analog of
`writeField_recTotalAsset`, for the whole-record drop instead of a single-field write. -/
theorem makeSovereignKernel_recTotalAsset (k : RecordKernelState) (target : CellId) (b : AssetId) :
    recTotalAsset (makeSovereignKernel k target) b = recTotalAsset k b := rfl

/-- The rebound cell IS the commitment-only literal record (the bridge the teeth reuse). -/
theorem makeSovereignKernel_cell_eq (k : RecordKernelState) (target : CellId) :
    (makeSovereignKernel k target).cell target
      = .record [(commitmentField, .dig (stateCommitment (k.cell target)))] := by
  simp only [makeSovereignKernel, sovereignRebind, if_true]

/-- **THE FIDELITY TEETH (PROVED) — the readable balance is GONE.** After a committed
`makeSovereignStep`, the rebound cell's `balance` scalar is `none` (no longer directly readable —
the host dropped the record, keeping only the commitment). A FLAG model could NEVER prove this: with
a flag, `Value.scalar (post target) "balance"` is still the original balance. So the statement has
real teeth — it FAILS for the wave-6 flag model and HOLDS for the commitment-rebind. This is the
"§8 CryptoPortal opening" boundary: to read the value the host must now open the commitment. -/
theorem makeSovereignStep_balance_unreadable {s s' : RecChainedState} {actor target : CellId}
    (h : makeSovereignStep s actor target = some s') :
    Value.scalar (s'.kernel.cell target) balanceField = none := by
  obtain ⟨_, hs'⟩ := makeSovereignStep_factors h
  subst hs'
  -- the rebound cell is the literal `[(commitmentField, .dig …)]`; the only field is `commitment`,
  -- and `commitment ≠ balance` (closed string comparison) ⇒ the `balance` lookup misses ⇒ `none`
  -- (computes by `rfl`: the field-name match is decidable on closed strings, value irrelevant).
  rw [makeSovereignKernel_cell_eq s.kernel target]; rfl

/-- **THE FIDELITY TEETH (PROVED) — EVERY pre-state field is dropped.** After a committed
`makeSovereignStep`, ANY field `f` distinct from the commitment field reads `none` from the rebound
cell — `nonce`, `permissions`, `verification_key`, the value, all gone. The general form of
`_balance_unreadable`: the host-readable state is REPLACED, not merely flagged. -/
theorem makeSovereignStep_fields_dropped {s s' : RecChainedState} {actor target : CellId}
    (f : FieldName) (hf : f ≠ commitmentField)
    (h : makeSovereignStep s actor target = some s') :
    (s'.kernel.cell target).field f = none := by
  obtain ⟨_, hs'⟩ := makeSovereignStep_factors h
  subst hs'
  -- the only field of the rebound record is `commitment`; any `f ≠ commitment` misses ⇒ `none`.
  have hfb : ((commitmentField : FieldName) == f) = false :=
    beq_eq_false_iff_ne.2 (fun hc => hf hc.symm)
  rw [makeSovereignKernel_cell_eq s.kernel target]
  simp only [Value.field, List.find?_cons, hfb, List.find?_nil, Option.map_none]

/-- **THE COMMITMENT IS PRESENT — PROVED.** After a committed `makeSovereignStep`, the rebound cell
carries the commitment field as a digest of the PRE-state value: `cell.state_commitment()`. The
post-state binds the preimage (the §8 collision-resistance, ASSUMED, makes this binding sound; here
we prove the binding is in fact recorded). -/
theorem makeSovereignStep_commitment_present {s s' : RecChainedState} {actor target : CellId}
    (h : makeSovereignStep s actor target = some s') :
    (s'.kernel.cell target).field commitmentField
      = some (.dig (stateCommitment (s.kernel.cell target))) := by
  obtain ⟨_, hs'⟩ := makeSovereignStep_factors h
  subst hs'
  -- the head field of the rebound record IS `commitment`; the lookup hits it ⇒ `some (.dig …)`
  -- (computes by `rfl`: the field-name match is decidable on closed strings).
  rw [makeSovereignKernel_cell_eq s.kernel target]; rfl

/-- **`makeSovereignStep` authorized — PROVED.** A committed rebind implies the actor held authority
over `target` (dregg1's self-sovereign gate). -/
theorem makeSovereignStep_authorized {s s' : RecChainedState} {actor target : CellId}
    (h : makeSovereignStep s actor target = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  (makeSovereignStep_factors h).1

/-- **`makeSovereignStep` extends the chain by exactly one row — PROVED** (the metadata clock; the
chainlink the spine reuses). -/
theorem makeSovereignStep_chainlink {s s' : RecChainedState} {actor target : CellId}
    (h : makeSovereignStep s actor target = some s') :
    s'.log = { actor := actor, src := target, dst := target, amt := 0 } :: s.log := by
  obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; rfl

/-! ### §MA-auth — the 6 DISTINCT AUTHORITY effects on the per-asset dispatch.

dregg1's `turn/src/executor/apply.rs` runs a cluster of capability-graph effects BEYOND the bare
`delegate`/`revoke` already wired above. Each EDITS (or merely CHECKS) the `caps` cap-graph and
NEVER the `bal` ledger — so `ledgerDeltaAsset = 0` for EVERY asset and `recTotalAsset` is UNCHANGED
(balance-NEUTRAL). The HEADLINE obligation for this cluster is NON-AMPLIFICATION — the genuine
`capAuthConferred ⊆` over the REAL `List Auth` lattice (`attenuate_subset`), not a `()≤()` collapse.

  * `Introduce { introducer, recipient, target }` — the graph skeleton of the 3-party Granovetter
    introduce. Reuses the proven `recCDelegate` connectivity spine and copies the concrete held cap.
    The rights-carrying/narrowing form is `delegateAttenA` below.
  * `AttenuateCapability { cell, slot, narrower_permissions }` (`apply.rs:4377`) — monotonically
    NARROW a held cap in the actor's c-list (widening rejected). The purest non-amplification.
  * `DropRef { ref_id }` (`apply.rs:4034`) — a CapTP GC decrement: the holder drops its edge to the
    target. Reuses `recKRevokeTarget` (`removeEdge`); authority strictly shrinks.
  * `RevokeDelegation { child }` (`apply.rs:3044`) — a parent revokes a child's delegation. Reuses
    `recKRevokeTarget` (`removeEdge`). (Distinct dregg1 op from `DropRef`; same graph move.)
  * `ValidateHandoff { … }` (`apply.rs:4069`) — the graph-level consequence of accepting a
    two-signature CapTP handoff certificate. The executable action below carries only
    `(introducer, recipient, target)`, so it can prove the introduce skeleton by copying the held cap.
    The certificate's granted permissions / allowed-effect mask and the genuine
    `granted ⊆ held` check live in `Exec.CapTP.HandoffCert` and the swiss-table path, not in this
    three-field skeleton.
  * `ExerciseViaCapability { cap_slot, inner_effects }` (`apply.rs:2441`) — exercise a HELD cap. The
    cap graph is UNCHANGED (only connectivity begets connectivity); gated on holding the edge.

These REUSE the proofs of `Exec.EffectsAuthority` (which we cannot import — it sits DOWNSTREAM of
this module — so we re-found the two missing chained wrappers `attenuateStepA`/`exerciseStepA` here,
mirroring `recCDelegate`, and discharge the non-amplification directly from `Caps.attenuate_subset`,
the SAME proof `EffectsAuthority.attenuate_non_amplifying`/`introduce_non_amplifying` reuse). -/

/-- **`IsNonAmplifyingF held granted`** — the genuine non-amplification predicate over the REAL
rights lattice: the granted cap confers a `List Auth` SUBSET of the held cap's authority
(`is_attenuation(held, granted)`, `apply.rs:2835`). NOT a `()≤()` skeleton; an amplifying grant
(`granted ⊄ held`) makes it FALSE — the predicate has teeth (`amplifyingF_rejected`). The local twin
of `EffectsAuthority.IsNonAmplifying`. -/
def IsNonAmplifyingF (held granted : Cap) : Prop :=
  capAuthConferred granted ⊆ capAuthConferred held

/-- **`amplifyingF_rejected` — THE TEETH (PROVED).** A `granted` cap conferring an authority `a` the
`held` cap does NOT confer is REJECTED (`¬ IsNonAmplifyingF held granted`). So the non-amplification
gate genuinely discriminates — it is not vacuously true. -/
theorem amplifyingF_rejected (held granted : Cap) (a : Auth)
    (hgranted : a ∈ capAuthConferred granted) (hheld : a ∉ capAuthConferred held) :
    ¬ IsNonAmplifyingF held granted := fun hsub => hheld (hsub hgranted)

/-- **`attenuateF_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** The narrowed cap confers a
genuine `List Auth` SUBSET of the original: `capAuthConferred (attenuate keep c) ⊆ capAuthConferred
c`, via `Caps.attenuate_subset`. This is the executable `is_narrower_or_equal` (widening denied) —
the SAME proof `EffectsAuthority.attenuate_non_amplifying`/`introduce_non_amplifying` carry. -/
theorem attenuateF_non_amplifying (keep : List Auth) (c : Cap) :
    IsNonAmplifyingF c (attenuate keep c) :=
  Dregg2.Exec.attenuate_subset keep c

/-- Narrow the actor's slot in-place: replace the `idx`-th cap of `actor` with its `keep`-attenuation
(other caps/slots untouched). The executable `attenuate_in_place` (`apply.rs:4377`). -/
def attenuateSlotF (caps : Caps) (actor : CellId) (idx : Nat) (keep : List Auth) : Caps :=
  fun l => if l = actor then (caps l).modify idx (attenuate keep) else caps l

/-- **Chained attenuate.** Narrow the actor's `idx`-th cap to `keep`, append an authority receipt.
Always commits (attenuation cannot fail — at worst the identity, still narrower-or-equal). Mirrors
`recCDelegate`'s receipt threading; the local twin of `EffectsAuthority.attenuateStep`. -/
def attenuateStepA (s : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth) :
    RecChainedState :=
  { kernel := { s.kernel with caps := attenuateSlotF s.kernel.caps actor idx keep },
    log := authReceipt actor :: s.log }

/-- **Chained exercise.** Gate on the actor HOLDING an edge to `target` (the resolved c-list slot —
the SAME `confersEdgeTo` test `recKDelegate` uses), then append the receipt. The cap table is
UNCHANGED (exercising reads, never edits, the c-list). Fail-closed: no held edge ⇒ no exercise. The
local twin of `EffectsAuthority.exerciseStep`. -/
def exerciseStepA (s : RecChainedState) (actor target : CellId) : Option RecChainedState :=
  if (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true then
    some { s with log := authReceipt actor :: s.log }
  else
    none

theorem exerciseStepA_factors {s s' : RecChainedState} {actor target : CellId}
    (h : exerciseStepA s actor target = some s') :
    (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
      ∧ s' = { s with log := authReceipt actor :: s.log } := by
  unfold exerciseStepA at h
  by_cases hg : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §MA-lifecycle (Wave-3) — the cell LIFECYCLE state machine Live↔Sealed, Live→Destroyed.

dregg1's `apply_cell_seal`/`apply_cell_unseal`/`apply_cell_destroy` (`apply.rs:4218`/`:4251`/`:4283`)
drive the cell's `lifecycle : CellLifecycle` (`cell/src/lifecycle.rs`) through the cell-side primitives
`Cell::seal`/`unseal`/`destroy` (`cell.rs:528`/`:559`/`:583`):

  * `seal`  : Live/Archived → Sealed; REJECT if already Sealed (`AlreadySealed`) or terminal
              (Destroyed/Migrated, `Terminal`). A Sealed cell rejects new effects (`accepts_effects`,
              `lifecycle.rs:109`) but state/history survive — REVERSIBLE quiescence (`cell.rs:533-545`).
  * `unseal`: Sealed → Live; REJECT if NotSealed (`cell.rs:559-565`).
  * `destroy`: any NON-terminal → Destroyed, binding the `DeathCertificate` hash into the FINAL state
              (`cell.rs:587-597`); REJECT if already terminal (`Terminal`). TERMINAL — no further
              transition, and a Destroyed cell rejects every effect.

We model `lifecycle` by its stable discriminant (`0`=Live, `1`=Sealed, `3`=Destroyed; `cell/src/
lifecycle.rs:95`) in `k.lifecycle`, and bind the death-certificate hash in `k.deathCert`. Each is
authority-gated (dregg1 requires `target == action_target` — the self-lifecycle gate — so the cell's own
authority `stateAuthB actor cell`). All balance-NEUTRAL (edit `lifecycle`/`deathCert`, never `bal`). -/

/-- The three lifecycle discriminants Wave-3 covers (`CellLifecycle::discriminant`, `lifecycle.rs:95`). -/
def lcLive      : Nat := 0
def lcSealed    : Nat := 1
def lcDestroyed : Nat := 3

/-- **`acceptsEffects k cell`** — dregg1's `CellLifecycle::accepts_effects` (`lifecycle.rs:109`): does
`cell`'s lifecycle state admit new effects? `true` only for Live (Wave-3's modelled non-terminal,
non-sealed state; Archived `4` would also accept but is out of Wave-3 scope). A Sealed (`1`) or Destroyed
(`3`) cell is fail-closed REJECTED. The gate the lifecycle transitions read. -/
def acceptsEffects (k : RecordKernelState) (cell : CellId) : Bool := k.lifecycle cell == lcLive

/-- Set `cell`'s lifecycle discriminant to `lc` (the cell-side lifecycle write; every other cell and
field untouched — the lifecycle is a side-table, not a `cell` record field). -/
def setLifecycle (k : RecordKernelState) (cell : CellId) (lc : Nat) : RecordKernelState :=
  { k with lifecycle := fun c => if c = cell then lc else k.lifecycle c }

/-- **Chained cell SEAL** (`apply_cell_seal` → `Cell::seal`, `apply.rs:4218`/`cell.rs:528`): Live→Sealed.
FAIL-CLOSED on the authority gate (`stateAuthB actor cell`, the self-lifecycle gate) AND on the state
machine — only a LIVE cell may seal (`acceptsEffects`; a Sealed cell is `AlreadySealed`, a Destroyed cell
is `Terminal`). On commit, flip the discriminant to Sealed (`1`) and extend the chain. bal-NEUTRAL. -/
def cellSealChainA (s : RecChainedState) (actor cell : CellId) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
    some { kernel := setLifecycle s.kernel cell lcSealed,
           log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
  else none

/-- **Chained cell UNSEAL** (`apply_cell_unseal` → `Cell::unseal`, `apply.rs:4251`/`cell.rs:559`):
Sealed→Live. FAIL-CLOSED on authority AND on the state machine — only a SEALED cell may unseal
(`NotSealed` otherwise). On commit, flip the discriminant back to Live (`0`). bal-NEUTRAL. -/
def cellUnsealChainA (s : RecChainedState) (actor cell : CellId) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true ∧ s.kernel.lifecycle cell == lcSealed then
    some { kernel := setLifecycle s.kernel cell lcLive,
           log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
  else none

/-- **Chained cell DESTROY** (`apply_cell_destroy` → `Cell::destroy`, `apply.rs:4283`/`cell.rs:583`): any
NON-terminal → Destroyed, binding the disclosed `certHash` (the `DeathCertificate` hash, `cell.rs:593`)
into the FINAL state. FAIL-CLOSED on authority AND on the state machine — a cell already in a TERMINAL
state (Destroyed, discriminant `3`) is `Terminal`-rejected (a Live OR Sealed cell may be destroyed — seal
is the prelude to destruction). On commit, flip to Destroyed (`3`) and bind `certHash`; TERMINAL (no
further transition accepted, since `acceptsEffects`/`== lcSealed`/`!= lcDestroyed` all fail). bal-NEUTRAL. -/
def cellDestroyChainA (s : RecChainedState) (actor cell : CellId) (certHash : Nat) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true ∧ s.kernel.lifecycle cell != lcDestroyed then
    some { kernel := { (setLifecycle s.kernel cell lcDestroyed) with
                        deathCert := fun c => if c = cell then certHash else s.kernel.deathCert c },
           log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
  else none

/-- **`setLifecycle` is balance-NEUTRAL — PROVED (`rfl`-grade).** Editing the `lifecycle` side-table
leaves `bal`/`accounts`/`escrows` fixed, so `recTotalAssetWithEscrow` is unchanged for EVERY asset. -/
theorem setLifecycle_balNeutral (k : RecordKernelState) (cell : CellId) (lc : Nat) (b : AssetId) :
    recTotalAssetWithEscrow (setLifecycle k cell lc) b = recTotalAssetWithEscrow k b := rfl

/-- **`cellSealChainA` factors — PROVED.** A committed seal was authorized over a LIVE cell and produced
exactly the Sealed-flip post-state + a one-row chain extension. -/
theorem cellSealChainA_factors {s s' : RecChainedState} {actor cell : CellId}
    (h : cellSealChainA s actor cell = some s') :
    (stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true) ∧
      s' = { kernel := setLifecycle s.kernel cell lcSealed,
             log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  unfold cellSealChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`cellUnsealChainA` factors — PROVED.** A committed unseal was authorized over a SEALED cell. -/
theorem cellUnsealChainA_factors {s s' : RecChainedState} {actor cell : CellId}
    (h : cellUnsealChainA s actor cell = some s') :
    (stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true) ∧
      s' = { kernel := setLifecycle s.kernel cell lcLive,
             log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  unfold cellUnsealChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`cellDestroyChainA` factors — PROVED.** A committed destroy was authorized over a NON-terminal
cell and bound the disclosed `certHash` into the final state. -/
theorem cellDestroyChainA_factors {s s' : RecChainedState} {actor cell : CellId} {certHash : Nat}
    (h : cellDestroyChainA s actor cell certHash = some s') :
    (stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell != lcDestroyed) = true) ∧
      s' = { kernel := { (setLifecycle s.kernel cell lcDestroyed) with
                          deathCert := fun c => if c = cell then certHash else s.kernel.deathCert c },
             log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  unfold cellDestroyChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell != lcDestroyed) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`cellDestroyChainA_terminal_rejects` — THE TERMINALITY TEETH (PROVED).** A cell already Destroyed
(`lifecycle cell = lcDestroyed`) cannot be re-destroyed: the gate fails, so the leg returns `none` and no
effect commits. dregg1's `Terminal` rejection (`cell.rs:587`). NON-VACUOUS — keyed on committed state. -/
theorem cellDestroyChainA_terminal_rejects (s : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (h : s.kernel.lifecycle cell = lcDestroyed) :
    cellDestroyChainA s actor cell certHash = none := by
  unfold cellDestroyChainA
  rw [if_neg (by simp [h])]

/-- **`cellSealChainA_sealed_rejects` — THE SEAL-GATE TEETH (PROVED).** A cell NOT Live (Sealed or
Destroyed ⇒ `acceptsEffects = false`) cannot be sealed: dregg1's `AlreadySealed`/`Terminal` rejection. -/
theorem cellSealChainA_nonlive_rejects (s : RecChainedState) (actor cell : CellId)
    (h : acceptsEffects s.kernel cell = false) :
    cellSealChainA s actor cell = none := by
  unfold cellSealChainA
  rw [if_neg (by simp [h])]

/-! ### §MA-refresh (Wave-3) — self-only `refreshDelegation` snapshots the parent's CURRENT c-list.

dregg1's `apply_refresh_delegation` (`apply.rs:2991`) is a SELF-only refresh (the `action_target` IS the
child): read the child's `delegate` (parent) pointer, fail-closed if absent (`apply.rs:3004`
"cell has no delegate"), then take a FRESH snapshot of the PARENT's CURRENT c-list (`apply.rs:3022`
`parent.capabilities.iter().cloned().collect()`) into `child.delegation` (`apply.rs:3031`), journaling
the old. Distinct from `spawn` (which sets the INITIAL snapshot at birth) and `revokeDelegation` (which
CLEARS it). We model `delegations child` as the snapshot; refresh OVERWRITES it with `caps parent`.
Authority: dregg1 self-only (`action_target` = child) ⇒ the child's own authority (`stateAuthB actor
child`). bal-NEUTRAL (edits only the `delegations` side-table). -/

/-- The parent's current c-list, or `[]` if the child has no parent (the snapshot source). -/
def parentClist (k : RecordKernelState) (child : CellId) : List Cap :=
  match k.delegate child with | some p => k.caps p | none => []

/-- **Chained refreshDelegation** (`apply_refresh_delegation`, `apply.rs:2991`). FAIL-CLOSED on: the
self-authority gate (`stateAuthB actor child`, dregg1's self-only `action_target == child`), AND the
child genuinely having a parent (`delegate child ≠ none` — dregg1's `delegate.ok_or_else`,
`apply.rs:3004`). On commit, OVERWRITE `delegations child` with a FRESH snapshot of the parent's CURRENT
`caps` (`parentClist`) and extend the chain. bal-NEUTRAL. -/
def refreshDelegationChainA (s : RecChainedState) (actor child : CellId) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true then
    some { kernel := { s.kernel with
                        delegations := fun c => if c = child then parentClist s.kernel child
                                                else s.kernel.delegations c },
           log    := { actor := actor, src := child, dst := child, amt := 0 } :: s.log }
  else none

/-- **`refreshDelegationChainA` factors — PROVED.** A committed refresh was self-authorized over a child
with a parent and snapshotted the parent's CURRENT c-list. -/
theorem refreshDelegationChainA_factors {s s' : RecChainedState} {actor child : CellId}
    (h : refreshDelegationChainA s actor child = some s') :
    (stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true) ∧
      s' = { kernel := { s.kernel with
                          delegations := fun c => if c = child then parentClist s.kernel child
                                                  else s.kernel.delegations c },
             log := { actor := actor, src := child, dst := child, amt := 0 } :: s.log } := by
  unfold refreshDelegationChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`refreshDelegationChainA_noParent_rejects` — PROVED (the no-parent teeth).** A child with no
parent (`delegate child = none`) cannot refresh: dregg1's `delegate.ok_or_else` (`apply.rs:3004`). -/
theorem refreshDelegationChainA_noParent_rejects (s : RecChainedState) (actor child : CellId)
    (h : s.kernel.delegate child = none) :
    refreshDelegationChainA s actor child = none := by
  unfold refreshDelegationChainA
  rw [if_neg (by simp [h])]

/-- **`refreshDelegationChainA_snapshots_parent` — THE FRESH-SNAPSHOT TEETH (PROVED).** After a committed
refresh of a child with parent `p`, the child's delegation snapshot IS the parent's CURRENT c-list
(`delegations child = caps p`). A flag-flip could never witness this — the snapshot genuinely tracks the
live parent caps. -/
theorem refreshDelegationChainA_snapshots_parent {s s' : RecChainedState} {actor child p : CellId}
    (h : refreshDelegationChainA s actor child = some s') (hp : s.kernel.delegate child = some p) :
    s'.kernel.delegations child = s.kernel.caps p := by
  obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'
  show (if child = child then parentClist s.kernel child else s.kernel.delegations child) = s.kernel.caps p
  rw [if_pos rfl]; simp only [parentClist, hp]

/-! ### §MA-seal (Wave-3 DE-SHADOW) — seal/unseal/createSealPair as REAL capability movement.

The wave-6 model collapsed all three to a field flag (`stateStep s sealField cell (.int 1)`): NO cap ever
moved. dregg1 GENUINELY moves a capability through an AEAD box. We de-shadow:

  * `apply_create_seal_pair` (`apply.rs:2675`): GRANT a sealer cap to `sealerHolder` AND an unsealer cap
    to `unsealerHolder` (the AEAD keypair is the §8 portal; the two c-list grants are REAL). We model the
    sealer/unsealer caps as `endpoint`-to-the-pair caps carrying the `grant` right (so a holder can seal
    /unseal), keyed by the `pairId` — `sealerCap pairId` / `unsealerCap pairId`.
  * `apply_seal` (`apply.rs:2743`): look up the actor's HELD sealer cap (`lookup_by_target`,
    `apply.rs:2756`; fail-closed `CapabilityNotHeld` otherwise), then SEAL a HELD `payload` cap into a box
    keyed by `pairId` (the box BINDS the specific cap). The AEAD ciphertext is the §8 portal; WHICH cap is
    sealed is REAL (the box's `payload`).
  * `apply_unseal` (`apply.rs:2874`): look up the actor's HELD unsealer cap (`apply.rs:2891`), find the box
    by `pairId` (fail-closed if absent), then — under the §8 AEAD-open carrier — GRANT the recovered
    `payload` cap to the `recipient`'s c-list (`apply.rs:2926` `grant_with_breadstuff`). The cap GENUINELY
    MOVES out of the box into the recipient's slot. Only the crypto is portaled.

All bal-NEUTRAL (edit `caps`/`sealedBoxes`, never `bal`). -/

/-- The sealer cap for seal-pair `pid`: an `endpoint`-to-`pid` cap carrying `grant` (the authority to seal
into the pair). dregg1's `seal_capability_id(pid, true)` grant (`apply.rs:2701`). -/
def sealerCap (pid : Nat) : Cap := Cap.endpoint pid [Auth.grant]
/-- The unsealer cap for seal-pair `pid` (`seal_capability_id(pid, false)`, `apply.rs:2721`). -/
def unsealerCap (pid : Nat) : Cap := Cap.endpoint pid [Auth.reply]

/-- Does cap `c` confer the seal/unseal authority over pair `pid`? (Holds an `endpoint pid …` cap — the
`lookup_by_target` test, `apply.rs:2756`/`:2891`.) -/
def holdsSealCapFor (pid : Nat) (c : Cap) : Bool :=
  match c with | .endpoint t _ => t == pid | _ => false

/-- **Chained createSealPair** (`apply_create_seal_pair`, `apply.rs:2675`). Authority: `actor` holds
authority over `sealerHolder` (`stateAuthB`, the writer of the pair). On commit, GRANT the sealer cap to
`sealerHolder` AND the unsealer cap to `unsealerHolder` — TWO real c-list grants (`grant_with_breadstuff`,
`apply.rs:2705`/`:2725`). bal-NEUTRAL. -/
def createSealPairChainA (s : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder : CellId) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor sealerHolder = true then
    some { kernel := { s.kernel with
                        caps := grant (grant s.kernel.caps sealerHolder (sealerCap pid))
                                      unsealerHolder (unsealerCap pid) },
           log    := { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 } :: s.log }
  else none

/-- **Chained seal** (`apply_seal`, `apply.rs:2743`). FAIL-CLOSED on: the actor genuinely HOLDING the
sealer cap for `pid` (`lookup_by_target`, `apply.rs:2756`; `CapabilityNotHeld` otherwise — read off the
COMMITTED c-list, adversary-uncontrollable), AND the actor genuinely HOLDING the `payload` cap it is
seal-ing (you can only seal a cap you HOLD — dregg1's `capability: &CapabilityRef` is one of the actor's
own held caps; this makes the box payload a confined cap, so `unseal` cannot leak authority — the
CellConfine carry). On commit, INSERT a box binding the HELD `payload` cap keyed by `pid` (the box BINDS
the specific cap — REAL, not a flag). The AEAD ciphertext is the §8 portal. The sealer's own c-list is
unchanged (the cap is copied into the box, dregg1 leaves the sealer's caps intact). bal-NEUTRAL. -/
def sealChainA (s : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap) :
    Option RecChainedState :=
  if (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
      ∧ payload ∈ s.kernel.caps actor then
    some { kernel := { s.kernel with
                        sealedBoxes := { pairId := pid, sealer := actor, payload := payload }
                                       :: s.kernel.sealedBoxes },
           log    := { actor := actor, src := actor, dst := actor, amt := 0 } :: s.log }
  else none

/-- **Chained unseal** (`apply_unseal`, `apply.rs:2874`). FAIL-CLOSED on: the actor HOLDING the unsealer
cap for `pid` (`apply.rs:2891`), AND the box existing in the holding-store (`findSealedBox`; the box was
genuinely sealed). On commit — under the §8 AEAD-open carrier (the crypto is the portal) — GRANT the
recovered `payload` cap to the `recipient`'s c-list (`grant_with_breadstuff`, `apply.rs:2926`). The cap
GENUINELY MOVES out of the box into the recipient. bal-NEUTRAL. -/
def unsealChainA (s : RecChainedState) (pid : Nat) (actor recipient : CellId) :
    Option RecChainedState :=
  if (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true then
    match findSealedBox s.kernel.sealedBoxes pid with
    | some box => some { kernel := { s.kernel with caps := grant s.kernel.caps recipient box.payload },
                         log    := { actor := actor, src := recipient, dst := recipient, amt := 0 } :: s.log }
    | none     => none
  else none

/-- **`createSealPairChainA` factors — PROVED.** A committed pair-create was authorized over `sealerHolder`
and granted the sealer+unsealer caps to the two holders. -/
theorem createSealPairChainA_factors {s s' : RecChainedState} {pid : Nat}
    {actor sealerHolder unsealerHolder : CellId}
    (h : createSealPairChainA s pid actor sealerHolder unsealerHolder = some s') :
    stateAuthB s.kernel.caps actor sealerHolder = true ∧
      s' = { kernel := { s.kernel with
                          caps := grant (grant s.kernel.caps sealerHolder (sealerCap pid))
                                        unsealerHolder (unsealerCap pid) },
             log := { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 } :: s.log } := by
  unfold createSealPairChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor sealerHolder = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`sealChainA` factors — PROVED.** A committed seal had the actor holding the sealer cap AND holding
the `payload` cap it sealed, and inserted a box binding that held `payload`. -/
theorem sealChainA_factors {s s' : RecChainedState} {pid : Nat} {actor : CellId} {payload : Cap}
    (h : sealChainA s pid actor payload = some s') :
    ((s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧ payload ∈ s.kernel.caps actor) ∧
      s' = { kernel := { s.kernel with
                          sealedBoxes := { pairId := pid, sealer := actor, payload := payload }
                                         :: s.kernel.sealedBoxes },
             log := { actor := actor, src := actor, dst := actor, amt := 0 } :: s.log } := by
  unfold sealChainA at h
  by_cases hg : (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
      ∧ payload ∈ s.kernel.caps actor
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`unsealChainA` factors — PROVED.** A committed unseal had the actor holding the unsealer cap, found
the box, and granted the recovered `payload` to the recipient. -/
theorem unsealChainA_factors {s s' : RecChainedState} {pid : Nat} {actor recipient : CellId}
    (h : unsealChainA s pid actor recipient = some s') :
    ∃ box, findSealedBox s.kernel.sealedBoxes pid = some box ∧
      (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧
      s' = { kernel := { s.kernel with caps := grant s.kernel.caps recipient box.payload },
             log := { actor := actor, src := recipient, dst := recipient, amt := 0 } :: s.log } := by
  unfold unsealChainA at h
  by_cases hg : (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
  · rw [if_pos hg] at h
    -- destruct the box on a SEPARATE hypothesis `o` (not the goal's existential) to avoid the
    -- goal-rewrite the `match`/`cases` generalization would otherwise force.
    obtain ⟨box, hb⟩ : ∃ box, findSealedBox s.kernel.sealedBoxes pid = some box := by
      cases o : findSealedBox s.kernel.sealedBoxes pid with
      | none => rw [o] at h; exact absurd h (by simp)
      | some box => exact ⟨box, rfl⟩
    rw [hb] at h; simp only [Option.some.injEq] at h
    exact ⟨box, hb, hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`unsealChainA_grants_sealed_cap` — THE CAP-MOVEMENT TEETH (PROVED).** After a committed unseal, the
`recipient` HOLDS the box's `payload` cap (it is the head of their c-list). The capability genuinely MOVED
through the box into the recipient — a flag-flip could NEVER witness this. NON-VACUOUS: the granted cap is
EXACTLY the one `seal` bound into the box (read off `findSealedBox`), not an arbitrary one. -/
theorem unsealChainA_grants_sealed_cap {s s' : RecChainedState} {pid : Nat} {actor recipient : CellId}
    {box : SealedBoxRecord}
    (h : unsealChainA s pid actor recipient = some s')
    (hbox : findSealedBox s.kernel.sealedBoxes pid = some box) :
    box.payload ∈ s'.kernel.caps recipient := by
  obtain ⟨box', hbox', _, hs'⟩ := unsealChainA_factors h
  rw [hbox] at hbox'; cases hbox'
  subst hs'
  show box.payload ∈ grant s.kernel.caps recipient box.payload recipient
  simp only [grant, if_true]; exact List.mem_cons_self ..

/-- **`unsealChainA_noBox_rejects` — PROVED (fail-closed on absent box).** Unsealing a `pid` with NO box
in the holding-store returns `none`: no cap is granted (the cap must genuinely have been sealed first). -/
theorem unsealChainA_noBox_rejects (s : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (h : findSealedBox s.kernel.sealedBoxes pid = none) :
    unsealChainA s pid actor recipient = none := by
  unfold unsealChainA
  by_cases hg : (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
  · rw [if_pos hg, h]
  · rw [if_neg hg]

/-- The four Wave-3 seal/refresh chained steps are balance-NEUTRAL (edit `caps`/`sealedBoxes`/
`delegations`, never `bal`/`escrows`) — PROVED `rfl`-grade off the factoring lemmas. -/
theorem createSealPairChainA_balNeutral {s s' : RecChainedState} {pid : Nat}
    {actor sealerHolder unsealerHolder : CellId}
    (h : createSealPairChainA s pid actor sealerHolder unsealerHolder = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  obtain ⟨_, hs'⟩ := createSealPairChainA_factors h; subst hs'; rfl

theorem sealChainA_balNeutral {s s' : RecChainedState} {pid : Nat} {actor : CellId} {payload : Cap}
    (h : sealChainA s pid actor payload = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  obtain ⟨_, hs'⟩ := sealChainA_factors h; subst hs'; rfl

theorem unsealChainA_balNeutral {s s' : RecChainedState} {pid : Nat} {actor recipient : CellId}
    (h : unsealChainA s pid actor recipient = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors h; subst hs'; rfl

theorem refreshDelegationChainA_balNeutral {s s' : RecChainedState} {actor child : CellId}
    (h : refreshDelegationChainA s actor child = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; rfl

/-! ### §MA-escrow — the COMBINED PER-ASSET holding-store on the executed dispatch (`META-FILL C`).

dregg1's escrow/obligation/committed-escrow are NOT balance-conserving two-cell transfers: they DEBIT
ONE cell and park the value in an off-ledger side-table, conserving only the COMBINED total across the
create+settle PAIR (`RecordKernel §ESCROW`). On the per-asset `bal` ledger this is
`RecordKernel.createEscrowKAsset`/`releaseEscrowKAsset`/`refundEscrowKAsset`, which conserve the
COMBINED per-asset measure `recTotalAssetWithEscrow`. We re-found their CHAINED wrappers HERE (mirroring
`attenuateStepA`/`exerciseStepA`, since `EffectsPaired` sits parallel and is not imported), and wire
them into the executed `execFullA` dispatch. The escrow legs move the BARE `recTotalAsset` by ∓amount at
the locked asset (`ledgerDeltaAsset`), but conserve the COMBINED measure (`combinedDeltaAsset = 0`).
Note effects move SETS (nullifier/commitment), not `bal`, so both deltas are `0`. -/

/-- The escrow receipt (a self-`Turn` on the actor, amount `0` — the metadata clock row; the parked
amount/asset live in the off-ledger record, not the receipt). -/
def escrowReceiptA (actor : CellId) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }

/-- **Chained per-asset escrow create.** Run `RecordKernel.createEscrowKAsset` (single-cell, single-asset
debit at `asset` + park the asset-typed record), and on success extend the receipt chain. -/
def createEscrowChainA (s : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecChainedState :=
  match createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained per-asset escrow release** (single-cell credit to the recipient at the record's asset). -/
def releaseEscrowChainA (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match releaseEscrowKAsset s.kernel id with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained per-asset escrow refund** (single-cell credit back to the creator at the record's asset). -/
def refundEscrowChainA (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  match refundEscrowKAsset s.kernel id with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **Chained note-create** — grow the commitment SET (the §8 range-proof portal is the THEOREM-level
hypothesis, like bridgeMint's foreign finality; the ledger move is the grow-only insert). Always
commits at the ledger layer (a fresh commitment cannot conflict). -/
def noteCreateChainA (s : RecChainedState) (cm : Nat) (actor : CellId) : RecChainedState :=
  { kernel := noteCreateCommitment s.kernel cm, log := escrowReceiptA actor :: s.log }

/-- **Chained note-spend** — the ledger-side double-spend gate (`noteSpendNullifier`, fail-closed on a
repeated nullifier). The §8 STARK spending proof is the THEOREM-level portal. -/
def noteSpendChainA (s : RecChainedState) (nf : Nat) (actor : CellId) : Option RecChainedState :=
  match noteSpendNullifier s.kernel nf with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-! ### §MA-queue — the REAL ring-buffer FIFO queue effects (Wave-7 de-THIN). The chained wrappers over
`RecordKernel`'s `queueAllocateK`/`queueEnqueueK`/`queueDequeueK`/`queueResizeK`, EACH composed with a
REAL `stateAuthB actor cell` authority gate over the queue's representing cell (dregg1's writer-ACL /
owner gate, `apply.rs:3334,3433`) — fail-closed if the actor lacks authority. The kernel transition
carries the FIFO/capacity/owner/emptiness gates; the chained wrapper adds the c-list authority gate and
the receipt-chain row. ALL FOUR are balance-NEUTRAL: queues hold MESSAGES, never balance. -/

/-- **Chained queue allocate** — gate on `stateAuthB actor cell` (the actor may create a queue on its
cell) AND run `queueAllocateK` (fail-closed on a duplicate id). -/
def queueAllocateChainA (s : RecChainedState) (id : Nat) (actor cell : CellId) (capacity : Nat) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true then
    match queueAllocateK s.kernel id actor capacity with
    | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
    | none    => none
  else none

/-- **Chained queue enqueue** — gate on `stateAuthB actor cell` (the writer-ACL gate, `apply.rs:3334`)
AND run `queueEnqueueDepositK` (APPEND to the tail; fail-closed if absent OR FULL, `apply.rs:3348`; AND
PARK the refundable anti-spam `deposit` of asset `dAsset` from the `actor` sender into the holding-store
keyed by `depId`, fail-closed on `InsufficientBalance`, `apply.rs:3361`). The deposit move is
COMBINED-CONSERVING (the bare ledger DROPS, the holding-store rises) — Wave-8 closed the residual: it is
NO LONGER bal-neutral but combined-conserving, EXACTLY like a transfer. The receipt records the deposit
move (`amt := deposit`, `src := actor` sender, `dst := cell` queue owner). -/
def queueEnqueueChainA (s : RecChainedState) (id : Nat) (m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true then
    match queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
    | some k' => some { kernel := k', log := { actor := actor, src := actor, dst := cell, amt := deposit } :: s.log }
    | none    => none
  else none

/-- **Chained queue dequeue** — gate on `stateAuthB actor cell` (the c-list read) AND run
`queueDequeueRefundK` with `actor` as the dequeuer (REMOVE-FROM-FRONT in FIFO order; fail-closed if
absent, NOT the owner `apply.rs:3433`, OR EMPTY `apply.rs:3444`; AND REFUND the deposit record `depId`
to the dequeuer, `apply.rs:3483`). The refund is COMBINED-CONSERVING (the bare ledger of the dequeuer
RISES, the holding-store DROPS). The dequeued head message is dropped from the chained wrapper (it
surfaces in the kernel transition's `Nat`); the receipt records the deposit refund move. -/
def queueDequeueChainA (s : RecChainedState) (id : Nat) (actor cell : CellId) (depId : Nat) (deposit : ℤ) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true then
    match queueDequeueRefundK s.kernel id actor depId with
    | some (k', _) => some { kernel := k', log := { actor := actor, src := cell, dst := actor, amt := deposit } :: s.log }
    | none         => none
  else none

/-- **Chained queue resize** — gate on `stateAuthB actor cell` AND run `queueResizeK` (fail-closed if
absent OR shrinking below the current occupancy, `apply.rs:3534`). -/
def queueResizeChainA (s : RecChainedState) (id : Nat) (newCap : Nat) (actor cell : CellId) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true then
    match queueResizeK s.kernel id newCap with
    | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
    | none    => none
  else none

/-- **`queueChainA_factors` — PROVED.** A committed queue chained step (allocate/enqueue/dequeue/resize)
implies the actor was authorized over the queue cell AND the kernel transition committed. The bridge the
authority + bal-neutrality keystones reuse. Stated generically over the kernel `Option` result. -/
theorem queueEnqueueChainA_authorized {s s' : RecChainedState} {id m : Nat} {actor cell : CellId}
    {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueChainA s id m actor cell depId dAsset deposit = some s') :
    stateAuthB s.kernel.caps actor cell = true := by
  unfold queueEnqueueChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueDequeueChainA_authorized {s s' : RecChainedState} {id : Nat} {actor cell : CellId}
    {depId : Nat} {deposit : ℤ}
    (h : queueDequeueChainA s id actor cell depId deposit = some s') :
    stateAuthB s.kernel.caps actor cell = true := by
  unfold queueDequeueChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueAllocateChainA_authorized {s s' : RecChainedState} {id : Nat} {actor cell : CellId} {cap : Nat}
    (h : queueAllocateChainA s id actor cell cap = some s') :
    stateAuthB s.kernel.caps actor cell = true := by
  unfold queueAllocateChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueResizeChainA_authorized {s s' : RecChainedState} {id newCap : Nat} {actor cell : CellId}
    (h : queueResizeChainA s id newCap actor cell = some s') :
    stateAuthB s.kernel.caps actor cell = true := by
  unfold queueResizeChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`queueEnqueueChainA_balNeutral` — PROVED (Wave-8: now COMBINED-CONSERVING, not bal-neutral).** A
committed enqueue leaves the COMBINED per-asset measure UNCHANGED ∀ asset — but NO LONGER because it is
bal-neutral: the refundable deposit GENUINELY moves the bare `recTotalAsset` (parked off-ledger), and
the COMBINED measure is conserved because the parked value is counted in the holding-store. Reuses
`queueEnqueueDepositK_conserves_combined` (the residual close). -/
theorem queueEnqueueChainA_balNeutral {s s' : RecChainedState} {id m : Nat} {actor cell : CellId}
    {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueChainA s id m actor cell depId dAsset deposit = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold queueEnqueueChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        exact queueEnqueueDepositK_conserves_combined hk b
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueDequeueChainA_balNeutral {s s' : RecChainedState} {id : Nat} {actor cell : CellId}
    {depId : Nat} {deposit : ℤ}
    (h : queueDequeueChainA s id actor cell depId deposit = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold queueDequeueChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueDequeueRefundK s.kernel id actor depId with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some kr =>
        obtain ⟨k', m⟩ := kr
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        exact queueDequeueRefundK_conserves_combined hk b
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueAllocateChainA_balNeutral {s s' : RecChainedState} {id : Nat} {actor cell : CellId} {cap : Nat}
    (h : queueAllocateChainA s id actor cell cap = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold queueAllocateChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueAllocateK s.kernel id actor cap with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hr, he⟩ := queueAllocateK_balNeutral hk b
        simp only [recTotalAssetWithEscrow, hr, he]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueResizeChainA_balNeutral {s s' : RecChainedState} {id newCap : Nat} {actor cell : CellId}
    (h : queueResizeChainA s id newCap actor cell = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold queueResizeChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueResizeK s.kernel id newCap with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hr, he⟩ := queueResizeK_balNeutral hk b
        simp only [recTotalAssetWithEscrow, hr, he]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`queueEnqueueChainA_chainlink` — PROVED.** A committed enqueue appends EXACTLY one receipt row
(the deposit move `actor →(deposit)→ cell`). -/
theorem queueEnqueueChainA_chainlink {s s' : RecChainedState} {id m : Nat} {actor cell : CellId}
    {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueChainA s id m actor cell depId dAsset deposit = some s') :
    s'.log = { actor := actor, src := actor, dst := cell, amt := deposit } :: s.log := by
  unfold queueEnqueueChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueDequeueChainA_chainlink {s s' : RecChainedState} {id : Nat} {actor cell : CellId}
    {depId : Nat} {deposit : ℤ}
    (h : queueDequeueChainA s id actor cell depId deposit = some s') :
    s'.log = { actor := actor, src := cell, dst := actor, amt := deposit } :: s.log := by
  unfold queueDequeueChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueDequeueRefundK s.kernel id actor depId with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some kr => obtain ⟨k', m⟩ := kr; rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueAllocateChainA_chainlink {s s' : RecChainedState} {id : Nat} {actor cell : CellId} {cap : Nat}
    (h : queueAllocateChainA s id actor cell cap = some s') :
    s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log := by
  unfold queueAllocateChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueAllocateK s.kernel id actor cap with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem queueResizeChainA_chainlink {s s' : RecChainedState} {id newCap : Nat} {actor cell : CellId}
    (h : queueResizeChainA s id newCap actor cell = some s') :
    s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log := by
  unfold queueResizeChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg] at h
    cases hk : queueResizeK s.kernel id newCap with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §MA-queue-batch — WAVE 4: the ATOMIC cross-queue transaction + the PIPELINE fan-out step
(`QueueAtomicTx`/`QueuePipelineStep`, dregg1 `apply.rs:3586`/`:3747`). The atomic batch executes a LIST
of `QueueTxOp::{Enqueue,Dequeue}` ALL-OR-NOTHING against one or more queues (dregg1's journal-rollback
discipline, `apply.rs:3592` "On any failure, the journal handles rollback for the entire action"); the
pipeline step DEQUEUES the FIFO head from a source queue (owner-only) and RE-ENQUEUES it into each sink
(ACL-checked — `apply.rs:3812` BUG#114 sink-auth gate). Both ride the SAME proven chained queue kernel
ops (`queueEnqueueDepositK`/`queueDequeueRefundK`/`queueDequeueK`/`queueEnqueueK`), so the FIFO order,
capacity bound, owner gate, and per-asset combined-conservation are INHERITED — NOT re-modelled. -/

/-- **A single atomic-batch sub-op** (dregg1 `QueueTxOp`, `action.rs:1447`). `enqueue` PARKS a
refundable deposit (the writer-ACL path); `dequeue` REFUNDS it (the owner path). Each is exactly the
chained queue step it routes to (`queueEnqueueChainA`/`queueDequeueChainA`), so the batch is a
SEQUENCING of proven steps, never a new automaton. -/
inductive QueueTxOpA where
  /-- `QueueTxOp::Enqueue { queue, message_hash, deposit }` (`action.rs:1449`): append `m` to queue `id`
  + park the refundable `deposit` of `dAsset` from `actor`/`cell`, writer-ACL gated. -/
  | enqueue (id m : Nat) (actor cell : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
  /-- `QueueTxOp::Dequeue { queue }` (`action.rs:1456`): remove-from-front of queue `id` + refund the
  deposit `depId` to the dequeuer `actor`, owner gated. -/
  | dequeue (id : Nat) (actor cell : CellId) (depId : Nat) (deposit : ℤ)
  deriving Repr, DecidableEq

/-- **Run ONE atomic-batch sub-op** — route to the already-proven authority-gated chained queue step
(`queueEnqueueChainA` for the deposit-park, `queueDequeueChainA` for the refund). The sub-op's OWN
fail-closed gate (writer-ACL / owner / FULL / EMPTY / insufficient deposit) lives in the chained step;
this is just the discriminant. -/
def queueTxOpStepA (s : RecChainedState) : QueueTxOpA → Option RecChainedState
  | .enqueue id m actor cell depId dAsset deposit =>
      queueEnqueueChainA s id m actor cell depId dAsset deposit
  | .dequeue id actor cell depId deposit =>
      queueDequeueChainA s id actor cell depId deposit

/-- **`queueTxOpStepA_balNeutral` — PROVED.** Each atomic sub-op is COMBINED-conserving per asset (the
deposit park / refund moves the bare ledger but the combined measure is fixed) — read off the chained
queue step's `balNeutral`. -/
theorem queueTxOpStepA_balNeutral {s s' : RecChainedState} {op : QueueTxOpA}
    (h : queueTxOpStepA s op = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      exact queueEnqueueChainA_balNeutral h b
  | dequeue id actor cell depId deposit =>
      exact queueDequeueChainA_balNeutral h b

/-- **The ALL-OR-NOTHING atomic batch** (dregg1 `apply_queue_atomic_tx`, `apply.rs:3586`). Fold the
sub-ops left-to-right through the chained-state `Option` monad: the batch COMMITS iff EVERY sub-op
commits (each against the result of the prior). ANY sub-op failing ⇒ the WHOLE fold is `none` ⇒ the
batch rolls back (dregg1's journal-rollback for the entire action). The atomicity is the property: the
post-state is `some` exactly when the entire sequence would commit. -/
def queueAtomicTxChainA (s : RecChainedState) : List QueueTxOpA → Option RecChainedState
  | []        => some s
  | op :: ops =>
      match queueTxOpStepA s op with
      | some s' => queueAtomicTxChainA s' ops
      | none    => none

/-- **`queueAtomicTxChainA_balNeutral` — PROVED (the atomic batch is COMBINED-conserving per asset).**
A committed batch preserves `recTotalAssetWithEscrow` at EVERY asset: each sub-op is combined-neutral,
and the fold composes them. By induction on the op list. -/
theorem queueAtomicTxChainA_balNeutral {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none    => rw [hop] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hop] at h
          rw [ih h, queueTxOpStepA_balNeutral hop b]

/-- **`queueAtomicTxChainA_atomic_rollback` — PROVED (THE ATOMICITY TEETH).** If ANY prefix of the
batch fails (`queueTxOpStepA … = none` at some step), the WHOLE batch is `none` — no partial commit.
Concretely: a batch with a failing sub-op SOMEWHERE never returns `some`. We state it for the head and
the general "a failing op in the sequence aborts": once the fold hits a `none`, every extension is
`none`. -/
theorem queueAtomicTxChainA_head_fails {s : RecChainedState} {op : QueueTxOpA} {rest : List QueueTxOpA}
    (h : queueTxOpStepA s op = none) :
    queueAtomicTxChainA s (op :: rest) = none := by
  simp only [queueAtomicTxChainA, h]

/-- **`queueAtomicTxChainA_commits_iff_all` — PROVED (the all-or-nothing characterization).** The batch
commits iff the fold threads a `some` through every sub-op. For a `cons`, it commits iff the head
commits AND the tail commits against the head's result — so a single failing sub-op anywhere collapses
the whole batch (atomicity). -/
theorem queueAtomicTxChainA_commits_iff_all {s s' : RecChainedState} {op : QueueTxOpA}
    {rest : List QueueTxOpA} :
    queueAtomicTxChainA s (op :: rest) = some s'
      ↔ ∃ s1, queueTxOpStepA s op = some s1 ∧ queueAtomicTxChainA s1 rest = some s' := by
  simp only [queueAtomicTxChainA]
  cases hop : queueTxOpStepA s op with
  | none    => simp [hop]
  | some s1 => simp [hop]

/-- **The chained ATOMIC-TX step** — run the batch all-or-nothing AND, on success, extend the receipt
chain by ONE batch-commit row on the `actor` (the metadata clock row; the per-op moves already landed in
the per-op receipts inside the fold; the batch-commit row marks the transaction boundary). Fail-closed
if the batch rolls back. -/
def queueAtomicTxA (s : RecChainedState) (actor : CellId) (ops : List QueueTxOpA) :
    Option RecChainedState :=
  match queueAtomicTxChainA s ops with
  | some s' => some { kernel := s'.kernel, log := escrowReceiptA actor :: s'.log }
  | none    => none

/-- **`queueAtomicTxA_balNeutral` — PROVED.** The chained atomic-tx step is COMBINED-conserving per
asset (the batch fold is, and the receipt row is bal-neutral). -/
theorem queueAtomicTxA_balNeutral {s s' : RecChainedState} {actor : CellId} {ops : List QueueTxOpA}
    (h : queueAtomicTxA s actor ops = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold queueAtomicTxA at h
  cases hf : queueAtomicTxChainA s ops with
  | none    => rw [hf] at h; exact absurd h (by simp)
  | some s1 =>
      rw [hf] at h; simp only [Option.some.injEq] at h; subst h
      show recTotalAssetWithEscrow s1.kernel b = _
      exact queueAtomicTxChainA_balNeutral hf b

/-- **`queueAtomicTxA_chainlink` — PROVED.** A committed atomic-tx appends the batch-commit row on the
`actor` ATOP the per-op fold's log — so the pre-log is a suffix and the `actor` row is recorded. -/
theorem queueAtomicTxChainA_log_suffix {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') : s.log <:+ s'.log := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; exact List.suffix_refl _
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none    => rw [hop] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hop] at h
          have hstep : s.log <:+ s1.log := by
            cases op with
            | enqueue id m actor cell depId dAsset deposit =>
                rw [queueEnqueueChainA_chainlink hop]; exact List.suffix_cons _ _
            | dequeue id actor cell depId deposit =>
                rw [queueDequeueChainA_chainlink hop]; exact List.suffix_cons _ _
          exact hstep.trans (ih h)

theorem queueAtomicTxA_chainlink {s s' : RecChainedState} {actor : CellId} {ops : List QueueTxOpA}
    (h : queueAtomicTxA s actor ops = some s') :
    s.log <:+ s'.log ∧ escrowReceiptA actor ∈ s'.log := by
  unfold queueAtomicTxA at h
  cases hf : queueAtomicTxChainA s ops with
  | none    => rw [hf] at h; exact absurd h (by simp)
  | some s1 =>
      rw [hf] at h; simp only [Option.some.injEq] at h; subst h
      exact ⟨(queueAtomicTxChainA_log_suffix hf).trans (List.suffix_cons _ _), List.mem_cons_self⟩

theorem queueAtomicTxA_obsadvance {s s' : RecChainedState} {actor : CellId} {ops : List QueueTxOpA}
    (h : queueAtomicTxA s actor ops = some s') : s.log.length < s'.log.length := by
  unfold queueAtomicTxA at h
  cases hf : queueAtomicTxChainA s ops with
  | none    => rw [hf] at h; exact absurd h (by simp)
  | some s1 =>
      rw [hf] at h; simp only [Option.some.injEq] at h; subst h
      show s.log.length < (escrowReceiptA actor :: s1.log).length
      rw [List.length_cons]
      exact Nat.lt_succ_of_le (queueAtomicTxChainA_log_suffix hf).length_le

/-! ### §MA-queue-pipeline — WAVE 4: the PIPELINE fan-out step (dregg1 `apply_queue_pipeline_step`,
`apply.rs:3747`). DEQUEUE the FIFO head from a source queue (owner-only, `apply.rs:3754`) and RE-ENQUEUE
the moved head message into EACH sink (ACL-checked per sink, `apply.rs:3812` BUG#114 sink-auth gate). A
fan-out routing: one message in, one copy into each sink. ALL balance-NEUTRAL — the pipeline moves
MESSAGES, never balance. -/

/-- **Enqueue the moved message `m` into each sink in `sinks`** — fold `queueEnqueueK` over the sinks
ALL-OR-NOTHING, gated per sink on `stateAuthB actor sink` (the sink writer-ACL, `apply.rs:3823`). ANY
sink absent / FULL / unauthorized ⇒ the whole fan-out is `none` (atomic with the source dequeue). -/
def pipelineFanoutK (k : RecordKernelState) (actor : CellId) (m : Nat) :
    List CellId → List Nat → Option RecordKernelState
  | [], _ => some k
  | sink :: sinks, sid :: sids =>
      if stateAuthB k.caps actor sink = true then
        match queueEnqueueK k sid m with
        | some k' => pipelineFanoutK k' actor m sinks sids
        | none    => none
      else none
  | _ :: _, [] => none

/-- **`pipelineFanoutK_balNeutral` — PROVED.** The fan-out enqueue fold is balance-NEUTRAL (each
`queueEnqueueK` touches only `queues`) — `recTotalAsset`/`escrowHeldAsset` fixed ∀ asset. -/
theorem pipelineFanoutK_balNeutral {k k' : RecordKernelState} {actor : CellId} {m : Nat}
    {sinks : List CellId} {sids : List Nat}
    (h : pipelineFanoutK k actor m sinks sids = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h
          by_cases hg : stateAuthB k.caps actor sink = true
          · rw [if_pos hg] at h
            cases hq : queueEnqueueK k sid m with
            | none    => rw [hq] at h; exact absurd h (by simp)
            | some k1 =>
                rw [hq] at h
                obtain ⟨hb1, he1⟩ := queueEnqueueK_balNeutral hq b
                obtain ⟨hb2, he2⟩ := ih h
                exact ⟨by rw [hb2, hb1], by rw [he2, he1]⟩
          · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The chained PIPELINE-STEP** (dregg1 `apply_queue_pipeline_step`, `apply.rs:3747`). DEQUEUE the
head of source queue `srcId` (owner-only via `queueDequeueK` with `owner` as the dequeuer; fail-closed if
absent / not-owner / EMPTY — `apply.rs:3754`/`:3766`) and RE-ENQUEUE that moved head into EACH sink (the
fan-out, each sink ACL-gated; fail-closed if absent / FULL / unauthorized — `apply.rs:3812`). The
`sinkCells`/`sinkIds` are paired position-wise (the representing cell + the queue id of each sink).
Balance-NEUTRAL; the receipt row records the routing on the `owner` (the source dequeuer). -/
def queuePipelineStepA (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) : Option RecChainedState :=
  match queueDequeueK s.kernel srcId owner with
  | some (k1, m) =>
      match pipelineFanoutK k1 owner m sinkCells sinkIds with
      | some k2 => some { kernel := k2, log := { actor := owner, src := owner, dst := owner, amt := 0 } :: s.log }
      | none    => none
  | none => none

/-- **`queuePipelineStepA_balNeutral` — PROVED.** The pipeline step is COMBINED-conserving per asset:
the source dequeue is bal-neutral and the sink fan-out is bal-neutral, so the combined measure is fixed
∀ asset. -/
theorem queuePipelineStepA_balNeutral {s s' : RecChainedState} {srcId : Nat} {owner : CellId}
    {sinkCells : List CellId} {sinkIds : List Nat}
    (h : queuePipelineStepA s srcId owner sinkCells sinkIds = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold queuePipelineStepA at h
  cases hd : queueDequeueK s.kernel srcId owner with
  | none    => simp only [hd] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k1, m⟩ := kr
      simp only [hd] at h
      cases hf : pipelineFanoutK k1 owner m sinkCells sinkIds with
      | none    => simp only [hf] at h; exact absurd h (by simp)
      | some k2 =>
          simp only [hf, Option.some.injEq] at h; subst h
          obtain ⟨hbd, hed⟩ := queueDequeueK_balNeutral hd b
          obtain ⟨hbf, hef⟩ := pipelineFanoutK_balNeutral hf b
          show recTotalAssetWithEscrow k2 b = recTotalAssetWithEscrow s.kernel b
          simp only [recTotalAssetWithEscrow, hbf, hef, hbd, hed]

/-- **`queuePipelineStepA_chainlink` — PROVED.** A committed pipeline step appends EXACTLY one routing
row on the `owner` (the source dequeuer). -/
theorem queuePipelineStepA_chainlink {s s' : RecChainedState} {srcId : Nat} {owner : CellId}
    {sinkCells : List CellId} {sinkIds : List Nat}
    (h : queuePipelineStepA s srcId owner sinkCells sinkIds = some s') :
    s'.log = { actor := owner, src := owner, dst := owner, amt := 0 } :: s.log := by
  unfold queuePipelineStepA at h
  cases hd : queueDequeueK s.kernel srcId owner with
  | none    => simp only [hd] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k1, m⟩ := kr
      simp only [hd] at h
      cases hf : pipelineFanoutK k1 owner m sinkCells sinkIds with
      | none    => simp only [hf] at h; exact absurd h (by simp)
      | some k2 => simp only [hf, Option.some.injEq] at h; subst h; rfl

/-- **`queueAtomicTxA_atomic_witness` — PROVED (the ATOMICITY witness).** A committed atomic-tx step
factors as the all-or-nothing batch fold `queueAtomicTxChainA s ops = some s1` (EVERY sub-op committed)
plus the batch-commit receipt row on the `actor`. This is the step-completeness obligation the
`fullActionInvA` arm carries: the committed post-state IS the threaded fold. -/
theorem queueAtomicTxA_atomic_witness {s s' : RecChainedState} {actor : CellId} {ops : List QueueTxOpA}
    (h : queueAtomicTxA s actor ops = some s') :
    ∃ s1, queueAtomicTxChainA s ops = some s1 ∧
          s'.log = escrowReceiptA actor :: s1.log ∧ s'.kernel = s1.kernel := by
  unfold queueAtomicTxA at h
  cases hf : queueAtomicTxChainA s ops with
  | none    => rw [hf] at h; exact absurd h (by simp)
  | some s1 =>
      rw [hf] at h; simp only [Option.some.injEq] at h; subst h
      exact ⟨s1, rfl, rfl, rfl⟩

/-- **`queuePipelineStepA_routing_witness` — PROVED (the FAN-OUT routing witness).** A committed
pipeline step factors as the source-queue dequeue (`queueDequeueK = some (k1, m)`, owner-gated, the
moved FIFO head `m`) THEN the sink fan-out (`pipelineFanoutK k1 owner m … = some s'.kernel`, each sink
ACL-gated). The committed post-kernel IS the source-dequeue-then-fan-out — the step-completeness
obligation the `fullActionInvA` arm carries (NOT `True`; the message GENUINELY MOVED source→sinks). -/
theorem queuePipelineStepA_routing_witness {s s' : RecChainedState} {srcId : Nat} {owner : CellId}
    {sinkCells : List CellId} {sinkIds : List Nat}
    (h : queuePipelineStepA s srcId owner sinkCells sinkIds = some s') :
    ∃ k1 m, queueDequeueK s.kernel srcId owner = some (k1, m) ∧
            pipelineFanoutK k1 owner m sinkCells sinkIds = some s'.kernel := by
  unfold queuePipelineStepA at h
  cases hd : queueDequeueK s.kernel srcId owner with
  | none    => simp only [hd] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k1, m⟩ := kr
      simp only [hd] at h
      cases hf : pipelineFanoutK k1 owner m sinkCells sinkIds with
      | none    => simp only [hf] at h; exact absurd h (by simp)
      | some k2 =>
          simp only [hf, Option.some.injEq] at h; subst h
          exact ⟨k1, m, rfl, hf⟩

/-! ### §MA-swiss — the REAL CapTP export/enliven/handoff/GC swiss-table effects (Wave-8 de-THIN). The
chained wrappers over `RecordKernel`'s `swissExportK`/`swissEnlivenK`/`swissHandoffK`/`swissDropK`, EACH
composed with a REAL `stateAuthB actor exporter` authority gate over the exporting/holding cell (dregg1's
holder-of-the-cap / introducer gate, `apply.rs:3879`/`:4109`) — fail-closed if the actor lacks authority.
The kernel transition carries the membership / non-amplification / refcount-GC gates; the chained wrapper
adds the c-list authority gate and the receipt-chain row. ALL FOUR are balance-NEUTRAL: the swiss-table
moves REFERENCES (capability routing), never balance. -/

/-- **Chained swiss export** — gate on `stateAuthB actor exporter` (the holder of the cap may export it)
AND run `swissExportK` (INSERT a swiss→cap entry, refcount 1; fail-closed on duplicate OR amplification). -/
def swissExportChainA (s : RecChainedState) (sw : Nat) (actor exporter target : CellId)
    (rights : List Auth) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor exporter = true then
    match swissExportK s.kernel sw exporter target rights with
    | some k' => some { kernel := k', log := { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log }
    | none    => none
  else none

/-- **Chained swiss enliven** — gate on `stateAuthB actor exporter` (the c-list read over the exporting
cell) AND run `swissEnlivenK` (LOOKUP-fail-closed + validate non-amplification + bump refcount). -/
def swissEnlivenChainA (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps actor exporter = true then
    match swissEnlivenK s.kernel sw claimed with
    | some k' => some { kernel := k', log := { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log }
    | none    => none
  else none

/-- **Chained swiss handoff** — gate on `stateAuthB introducer exporter` (the 3-vat introducer holds the
cap) AND run `swissHandoffK` (bind the cert + bump refcount; fail-closed if absent). -/
def swissHandoffChainA (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId) :
    Option RecChainedState :=
  if stateAuthB s.kernel.caps introducer exporter = true then
    match swissHandoffK s.kernel sw certHash with
    | some k' => some { kernel := k', log := { actor := introducer, src := exporter, dst := exporter, amt := 0 } :: s.log }
    | none    => none
  else none

/-- **Chained swiss drop** — gate on `stateAuthB actor exporter` (the holder may GC its ref) AND run
`swissDropK` (decrement refcount, GC at 0; fail-closed if absent OR already-zero). -/
def swissDropChainA (s : RecChainedState) (sw : Nat) (actor exporter : CellId) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor exporter = true then
    match swissDropK s.kernel sw with
    | some k' => some { kernel := k', log := { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log }
    | none    => none
  else none

/-- **The 4 swiss chained steps are AUTHORIZED — PROVED.** A committed swiss step implies the actor held
authority over the exporting/holding cell. The bridge the D auth gate reuses. -/
theorem swissExportChainA_authorized {s s' : RecChainedState} {sw : Nat} {actor exporter target : CellId}
    {rights : List Auth} (h : swissExportChainA s sw actor exporter target rights = some s') :
    stateAuthB s.kernel.caps actor exporter = true := by
  unfold swissExportChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissEnlivenChainA_authorized {s s' : RecChainedState} {sw : Nat} {actor exporter : CellId}
    {claimed : List Auth} (h : swissEnlivenChainA s sw actor exporter claimed = some s') :
    stateAuthB s.kernel.caps actor exporter = true := by
  unfold swissEnlivenChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissHandoffChainA_authorized {s s' : RecChainedState} {sw certHash : Nat} {introducer exporter : CellId}
    (h : swissHandoffChainA s sw certHash introducer exporter = some s') :
    stateAuthB s.kernel.caps introducer exporter = true := by
  unfold swissHandoffChainA at h
  by_cases hg : stateAuthB s.kernel.caps introducer exporter = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissDropChainA_authorized {s s' : RecChainedState} {sw : Nat} {actor exporter : CellId}
    (h : swissDropChainA s sw actor exporter = some s') :
    stateAuthB s.kernel.caps actor exporter = true := by
  unfold swissDropChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The 4 swiss chained steps are balance-NEUTRAL — PROVED.** The swiss-table moves references, not
balance, so the COMBINED per-asset measure is UNCHANGED ∀ asset. Reuses the kernel `*K_balNeutral`. -/
theorem swissExportChainA_balNeutral {s s' : RecChainedState} {sw : Nat} {actor exporter target : CellId}
    {rights : List Auth} (h : swissExportChainA s sw actor exporter target rights = some s')
    (b : AssetId) : recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold swissExportChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at h
    cases hk : swissExportK s.kernel sw exporter target rights with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hr, he⟩ := swissExportK_balNeutral hk b
        simp only [recTotalAssetWithEscrow, hr, he]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissEnlivenChainA_balNeutral {s s' : RecChainedState} {sw : Nat} {actor exporter : CellId}
    {claimed : List Auth} (h : swissEnlivenChainA s sw actor exporter claimed = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold swissEnlivenChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at h
    cases hk : swissEnlivenK s.kernel sw claimed with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hr, he⟩ := swissEnlivenK_balNeutral hk b
        simp only [recTotalAssetWithEscrow, hr, he]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissHandoffChainA_balNeutral {s s' : RecChainedState} {sw certHash : Nat} {introducer exporter : CellId}
    (h : swissHandoffChainA s sw certHash introducer exporter = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold swissHandoffChainA at h
  by_cases hg : stateAuthB s.kernel.caps introducer exporter = true
  · rw [if_pos hg] at h
    cases hk : swissHandoffK s.kernel sw certHash with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hr, he⟩ := swissHandoffK_balNeutral hk b
        simp only [recTotalAssetWithEscrow, hr, he]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissDropChainA_balNeutral {s s' : RecChainedState} {sw : Nat} {actor exporter : CellId}
    (h : swissDropChainA s sw actor exporter = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold swissDropChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at h
    cases hk : swissDropK s.kernel sw with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hr, he⟩ := swissDropK_balNeutral hk b
        simp only [recTotalAssetWithEscrow, hr, he]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The 4 swiss chained steps each append EXACTLY one receipt row — PROVED (the chainlink).** -/
theorem swissExportChainA_chainlink {s s' : RecChainedState} {sw : Nat} {actor exporter target : CellId}
    {rights : List Auth} (h : swissExportChainA s sw actor exporter target rights = some s') :
    s'.log = { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log := by
  unfold swissExportChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at h
    cases hk : swissExportK s.kernel sw exporter target rights with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissEnlivenChainA_chainlink {s s' : RecChainedState} {sw : Nat} {actor exporter : CellId}
    {claimed : List Auth} (h : swissEnlivenChainA s sw actor exporter claimed = some s') :
    s'.log = { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log := by
  unfold swissEnlivenChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at h
    cases hk : swissEnlivenK s.kernel sw claimed with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissHandoffChainA_chainlink {s s' : RecChainedState} {sw certHash : Nat} {introducer exporter : CellId}
    (h : swissHandoffChainA s sw certHash introducer exporter = some s') :
    s'.log = { actor := introducer, src := exporter, dst := exporter, amt := 0 } :: s.log := by
  unfold swissHandoffChainA at h
  by_cases hg : stateAuthB s.kernel.caps introducer exporter = true
  · rw [if_pos hg] at h
    cases hk : swissHandoffK s.kernel sw certHash with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem swissDropChainA_chainlink {s s' : RecChainedState} {sw : Nat} {actor exporter : CellId}
    (h : swissDropChainA s sw actor exporter = some s') :
    s'.log = { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log := by
  unfold swissDropChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at h
    cases hk : swissDropK s.kernel sw with
    | none    => rw [hk] at h; exact absurd h (by simp)
    | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §MA-bridge — the cross-chain bridge lock/finalize/cancel on the SHARED escrow holding-store
(Wave-5 `PHASE-BRIDGE`). The chained wrappers over `RecordKernel`'s `bridgeLockKAsset` (≈ escrow-create,
combined-conserving), `bridgeFinalizeKAsset` (a no-credit resolve — the value LEFT for the other chain,
COMBINED DROPS by the bridged amount, a disclosed OUTFLOW like burn) and `bridgeCancelKAsset` (≈
escrow-refund, combined-conserving). bridgeMint (the inbound side) was already wired (reuses
`recCMintAsset`). The §8 confirmation receipt (the destination signature) is the THEOREM-level portal,
exactly as bridgeMint's foreign finality. -/

/-- **Chained per-asset bridge LOCK.** Run `RecordKernel.bridgeLockKAsset` (single-cell, single-asset
debit at `asset` + park the bridge-tagged record), and on success extend the receipt chain. -/
def bridgeLockChainA (s : RecChainedState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecChainedState :=
  match bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
  | none    => none

/-- **`bridgeAuthOK` — the bridge finalize/cancel AUTHORITY gate (the missing one the re-audit flagged:
"anyone can finalize/cancel any victim's lock by id").** Only a BRIDGE-tagged lock's RECORDED `creator`
(the originator, read from the committed side-table — adversary-UNCONTROLLABLE state) may finalize or
cancel it; a stranger who merely knows the `id` is fail-closed REJECTED. Ordinary escrow rows in the
shared holding-store are not bridge-authorizable. (A relayer-finalize-with-foreign-receipt is the §8
receipt portal, deferred to META-FILL E; creator-only is the sound CORE — the creator can always
finalize/cancel their own lock.) -/
def bridgeAuthOK (k : RecordKernelState) (id : Nat) (actor : CellId) : Bool :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => r.bridge == true && r.creator == actor
  | none   => false

/-- **Chained per-asset bridge FINALIZE** (the §8 confirmation arrived — the no-credit resolve; the
value LEFT for the other chain, COMBINED measure DROPS by the DISCLOSED bridged `(asset, amount)`).
FAIL-CLOSED on the AUTHORITY gate `bridgeAuthOK` (only the recorded creator) THEN the parked record
matching. -/
def bridgeFinalizeChainA (s : RecChainedState) (id : Nat) (actor : CellId) (asset : AssetId) (amount : ℤ) :
    Option RecChainedState :=
  if bridgeAuthOK s.kernel id actor then
    match bridgeFinalizeKAsset s.kernel id asset amount with
    | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
    | none    => none
  else none

/-- **Chained per-asset bridge CANCEL** (timeout/failure — single-cell credit back to the originator at
the record's asset; combined CONSERVED). FAIL-CLOSED on the AUTHORITY gate (only the recorded creator). -/
def bridgeCancelChainA (s : RecChainedState) (id : Nat) (actor : CellId) : Option RecChainedState :=
  if bridgeAuthOK s.kernel id actor then
    match bridgeCancelKAsset s.kernel id with
    | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
    | none    => none
  else none

/-- **`bridgeLockChainA_combined_neutral` — PROVED.** A committed bridge lock conserves the COMBINED
per-asset measure at EVERY asset `b` (the bal debit at `asset` is offset by the holding-store rise).
Reads off `RecordKernel.bridge_lock_conserves_combined_per_asset`. -/
theorem bridgeLockChainA_combined_neutral {s s' : RecChainedState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : bridgeLockChainA s id actor originator destination asset amount = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold bridgeLockChainA at h
  cases hc : bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact bridge_lock_conserves_combined_per_asset b hc

/-- **`bridgeLockChainA_bal_debits` — PROVED.** A committed bridge lock DROPS the BARE per-asset ledger
`recTotalAsset asset` by `amount` (a real per-asset debit — the value is now INACCESSIBLE in the lock,
awaiting the other chain). -/
theorem bridgeLockChainA_bal_debits {s s' : RecChainedState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockChainA s id actor originator destination asset amount = some s') :
    recTotalAsset s'.kernel asset = recTotalAsset s.kernel asset - amount := by
  unfold bridgeLockChainA at h
  cases hc : bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact (bridge_lock_debits_per_asset hc).1

/-- **`bridgeFinalizeChainA_burns_combined` — THE BRIDGE HEADLINE (PROVED).** A committed bridge finalize
MOVES the COMBINED per-asset measure DOWN by EXACTLY the DISCLOSED `amount` at the disclosed `asset`
(`b = asset`), leaving every OTHER asset LITERALLY FIXED — the value genuinely LEFT for the other chain.
Reads off `RecordKernel.bridgeFinalizeKAsset_moves_combined_per_asset`. NON-VACUOUS: the drop is a
per-asset DISCLOSED OUTFLOW guarded by `b = asset` (no cross-asset laundering at the bridge boundary). -/
theorem bridgeFinalizeChainA_burns_combined {s s' : RecChainedState} {id : Nat} {actor : CellId}
    {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : bridgeFinalizeChainA s id actor asset amount = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b - (if b = asset then amount else 0) := by
  unfold bridgeFinalizeChainA at h
  by_cases hg : bridgeAuthOK s.kernel id actor = true
  · rw [if_pos hg] at h
    cases hc : bridgeFinalizeKAsset s.kernel id asset amount with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some k' =>
        rw [hc] at h; simp only [Option.some.injEq] at h; subst h
        exact bridgeFinalizeKAsset_moves_combined_per_asset b hc
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridgeCancelChainA_combined_neutral` — PROVED (the refund round-trip).** A committed bridge cancel
conserves the COMBINED per-asset measure at EVERY asset (value returns to the LIVE, gate-checked
originator). Reads off `RecordKernel.bridge_cancel_conserves_combined_per_asset`. -/
theorem bridgeCancelChainA_combined_neutral {s s' : RecChainedState} {id : Nat} {actor : CellId}
    (b : AssetId) (h : bridgeCancelChainA s id actor = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold bridgeCancelChainA at h
  by_cases hg : bridgeAuthOK s.kernel id actor = true
  · rw [if_pos hg] at h
    cases hc : bridgeCancelKAsset s.kernel id with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some k' =>
        rw [hc] at h; simp only [Option.some.injEq] at h; subst h
        exact bridge_cancel_conserves_combined_per_asset b hc
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridgeFinalizeChainA_nonCreator_rejects` — THE BRIDGE AUTHORITY TEETH (PROVED).** The §8 finalize
is FAIL-CLOSED on `bridgeAuthOK`: if the parked record matching `id` was created by someone OTHER than
the caller (`r.creator ≠ actor` — the RECORDED owner, read off the COMMITTED `s.kernel.escrows`
side-table, NOT a caller-supplied parameter), the whole leg returns `none`: no `amount` moves and no
receipt is appended. Closes the re-audit's HIGH hole #4 ("anyone can finalize any victim's bridge lock
by id"). NON-VACUOUS: the rejection is keyed on adversary-uncontrollable state. -/
theorem bridgeFinalizeChainA_nonCreator_rejects {s : RecChainedState} {id : Nat}
    {actor : CellId} {asset : AssetId} {amount : ℤ} {r : EscrowRecord}
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hne : (r.creator == actor) = false) :
    bridgeFinalizeChainA s id actor asset amount = none := by
  have hgate : bridgeAuthOK s.kernel id actor = false := by
    unfold bridgeAuthOK
    rw [hfind]
    cases r.bridge <;> simp [hne]
  unfold bridgeFinalizeChainA
  rw [if_neg (by simp [hgate])]

/-- **`bridgeCancelChainA_nonCreator_rejects` — PROVED (the cancel-side teeth).** Same fail-closed gate
on the refund path: a non-creator cannot trigger the refund-to-originator of a victim's parked lock. -/
theorem bridgeCancelChainA_nonCreator_rejects {s : RecChainedState} {id : Nat}
    {actor : CellId} {r : EscrowRecord}
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hne : (r.creator == actor) = false) :
    bridgeCancelChainA s id actor = none := by
  have hgate : bridgeAuthOK s.kernel id actor = false := by
    unfold bridgeAuthOK
    rw [hfind]
    cases r.bridge <;> simp [hne]
  unfold bridgeCancelChainA
  rw [if_neg (by simp [hgate])]

/-- **`bridgeLockChainA_authorized` — PROVED.** A committed bridge lock required the actor to be
authorized over the debited originator cell (the SAME `authorizedB` gate as `transfer`). -/
theorem bridgeLockChainA_authorized {s s' : RecChainedState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockChainA s id actor originator destination asset amount = some s') :
    authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = true := by
  unfold bridgeLockChainA at h
  cases hc : bridgeLockKAsset s.kernel id actor originator destination asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' => exact bridgeLockKAsset_authorized hc

/-- **`createEscrowChainA_combined_neutral` — PROVED.** A committed per-asset escrow create conserves
the COMBINED per-asset measure at EVERY asset `b` (the bal debit at `asset` is offset by the
holding-store rise). Reads off `RecordKernel.escrow_create_conserves_combined_per_asset`. -/
theorem createEscrowChainA_combined_neutral {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : createEscrowChainA s id actor creator recipient asset amount = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold createEscrowChainA at h
  cases hc : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_create_conserves_combined_per_asset b hc

/-! ### §MA-committed-escrow-HONESTY — WAVE 4: make the committed (PRIVACY) escrow HONESTLY DISTINCT
from plain escrow (`#121` follow-up). TODAY `createCommittedEscrowA` was SILENTLY `createEscrowChainA` —
byte-identical to plain escrow, the Pedersen-commitment HIDING neither modelled nor disclosed. We make
it HONEST: the create carries an EXECUTABLE §8 hiding-portal witness `hidingProof : Bool` (the boolean
shadow of "the Pedersen range/opening proof verified", `apply_create_committed_escrow`'s
`verifier.verify(range_proof, "committed-escrow-range", …)`, dregg1 `apply.rs:2125`). The state move
commits ONLY when `hidingProof = true` — so the committed variant FAIL-CLOSED REQUIRES a hiding
obligation the plain escrow does NOT (a reader sees a DIFFERENT gate; a `#eval` shows
committed-with-false-portal REJECTS while plain commits). Under the discharged portal the lock automaton
is still the per-asset escrow (combined-conserving) — the privacy gate changes the DISCLOSURE, not the
conservation. -/

/-- **Chained COMMITTED-escrow create — the HONEST §8 hiding-portal gate.** `hidingProof` is the
executable boolean witness of the Pedersen range/opening proof (dregg1 `apply.rs:2125`). FAIL-CLOSED if
the portal does NOT hold (`hidingProof = false`) — the privacy boundary the plain escrow lacks. Under
the discharged portal the state move is the per-asset escrow lock (`createEscrowChainA`), so it INHERITS
combined-conservation. -/
def createCommittedEscrowChainA (s : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool) : Option RecChainedState :=
  if hidingProof = true then
    createEscrowChainA s id actor creator recipient asset amount
  else none

/-- **`createCommittedEscrowChainA_fails_without_hiding` — PROVED (THE PRIVACY-BOUNDARY TEETH).** No
committed-escrow create commits without the §8 hiding portal (`hidingProof = false` ⇒ `none`). This is
the gate plain escrow does NOT have — the committed variant is NOT silently identical. -/
theorem createCommittedEscrowChainA_fails_without_hiding {s : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (hp : hidingProof = false) :
    createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof = none := by
  simp only [createCommittedEscrowChainA, hp, if_neg (by decide : ¬ (false = true))]

/-- **`createCommittedEscrowChainA_combined_neutral` — PROVED.** Under the discharged hiding portal the
committed-escrow create CONSERVES the COMBINED per-asset total at EVERY asset (the holding-store park,
exactly as plain escrow) — the privacy gate does not change the conservation, only the disclosure. -/
theorem createCommittedEscrowChainA_combined_neutral {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} {hidingProof : Bool} (b : AssetId)
    (h : createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  unfold createCommittedEscrowChainA at h
  by_cases hp : hidingProof = true
  · rw [if_pos hp] at h; exact createEscrowChainA_combined_neutral b h
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-- **`createCommittedEscrowChainA_authorized` — PROVED.** A committed committed-escrow create implies
BOTH the §8 hiding portal held AND the creator was authorized over the debited cell — the conjunction
the plain escrow lacks its first (hiding) half of. -/
theorem createCommittedEscrowChainA_authorized {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} {hidingProof : Bool}
    (h : createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof = some s') :
    hidingProof = true ∧
    authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true := by
  unfold createCommittedEscrowChainA createEscrowChainA at h
  by_cases hp : hidingProof = true
  · rw [if_pos hp] at h
    cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some k' => exact ⟨hp, createEscrowKAsset_authorized hk⟩
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-- **`createEscrowChainA_bal_debits` — PROVED.** A committed per-asset escrow create DROPS the BARE
per-asset ledger `recTotalAsset asset` by `amount` (a real per-asset debit) — the bare-bal delta the
`ledgerDeltaAsset` arm discloses (combined-conserving, bare-debiting). -/
theorem createEscrowChainA_bal_debits {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowChainA s id actor creator recipient asset amount = some s') :
    recTotalAsset s'.kernel asset = recTotalAsset s.kernel asset - amount := by
  unfold createEscrowChainA at h
  cases hc : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact (escrow_create_debits_per_asset hc).1

/-- The bare-bal per-asset delta of a committed escrow create, for an arbitrary asset `b`: `−amount` at
`asset`, `0` elsewhere. (The other-asset legs of `createEscrowKAsset` are frame-untouched.) PROVED. -/
theorem createEscrowChainA_bal_delta {s s' : RecChainedState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : createEscrowChainA s id actor creator recipient asset amount = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = asset then (-amount) else 0) := by
  unfold createEscrowChainA at h
  cases hc : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k' =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      unfold createEscrowKAsset at hc
      by_cases hg : authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
          ∧ 0 ≤ amount ∧ amount ≤ s.kernel.bal creator asset ∧ creator ∈ s.kernel.accounts
          ∧ ¬ (∃ r ∈ s.kernel.escrows, r.id = id)
      · rw [if_pos hg] at hc; simp only [Option.some.injEq] at hc; subst hc
        obtain ⟨_, _, _, hlive, _⟩ := hg
        show (∑ x ∈ s.kernel.accounts, recBalCreditCell s.kernel.bal creator asset (-amount) x b) = _
        have := recBalCreditCell_recTotalAsset s.kernel.accounts s.kernel.bal creator asset (-amount) hlive b
        simpa [recTotalAsset] using this
      · rw [if_neg hg] at hc; exact absurd hc (by simp)

/-- The FULL per-asset op-set, as one sum (`META-FILL A`/`B`/`C`). The asset-typed analog of
`FullAction`. -/
inductive FullActionA where
  /-- A per-asset balance transfer: move asset `asset` per `turn`. -/
  | balanceA (turn : Turn) (asset : AssetId)
  /-- A Granovetter delegation (authority; bal-orthogonal). -/
  | delegate (delegator recipient t : CellId)
  /-- A target revocation (authority; bal-orthogonal). -/
  | revoke   (holder t : CellId)
  /-- A privileged per-asset supply mint. -/
  | mintA    (actor cell : CellId) (asset : AssetId) (amt : ℤ)
  /-- A privileged per-asset supply burn. -/
  | burnA    (actor cell : CellId) (asset : AssetId) (amt : ℤ)
  -- §MA-state: the 5 PURE-STATE (field/log) effects — they write the `cell` record or the LOG,
  -- NEVER the `bal` ledger, so `ledgerDeltaAsset = 0` for EVERY asset (balance-NEUTRAL).
  /-- `SetField { cell, index→field, value }` (dregg1 `apply_set_field`): write `actor`-authorized
  cell `cell`'s named state field `field` to `v`. Authority: `actor` holds authority over `cell`. -/
  | setFieldA       (actor cell : CellId) (field : FieldName) (v : Int)
  /-- `EmitEvent { cell, event }` (dregg1 `apply_emit_event`): append an event receipt. NO state
  write, NO authority gate (dregg1's only gate is cell-existence). -/
  | emitEventA      (actor cell : CellId) (topic data : Int)
  /-- `IncrementNonce { cell }` (dregg1 `apply_increment_nonce`): monotone nonce bump. The bumped
  counter value `newNonce` is written to the `nonce` field; `actor` holds authority over `cell`. -/
  | incrementNonceA (actor cell : CellId) (newNonce : Int)
  /-- `SetPermissions { cell, new_permissions }` (dregg1 `apply_set_permissions`, applied LAST off
  the ORIGINAL permission snapshot): write the `permissions` field to `perms`; `actor` holds
  authority over `cell`. -/
  | setPermissionsA (actor cell : CellId) (perms : Int)
  /-- `SetVerificationKey { cell, new_vk }` (dregg1 `apply_set_verification_key`): write the
  `verification_key` field to `vk`; `actor` holds authority over `cell` (the VK hash-integrity check
  is the §8 Prop-carrier portal, off this executable layer). -/
  | setVKA          (actor cell : CellId) (vk : Int)
  -- §MA-auth: the 6 DISTINCT AUTHORITY effects — they EDIT (or CHECK) the `caps` cap-graph, NEVER
  -- the `bal` ledger, so `ledgerDeltaAsset = 0` for EVERY asset (balance-NEUTRAL). The HEADLINE
  -- obligation is NON-AMPLIFICATION (genuine `capAuthConferred ⊆` / `removeEdge ⊆` / `addEdge`).
  /-- `Introduce { introducer, recipient, target }` (dregg1 `apply_introduce`, `apply.rs:2791`): the
  3-party Granovetter introduce. `introducer` (holding connectivity to `target`) hands `recipient` a
  NON-AMPLIFYING edge to `target`. Reuses the `recCDelegate` connectivity spine. -/
  | introduceA      (introducer recipient target : CellId)
  /-- `IntroduceAttenuated { delegator, recipient, target, keep }` — the RIGHTS-CARRYING Granovetter
  delegation (the faithful `apply_introduce`, `apply.rs:2829` `is_attenuation(held, granted)`): the
  `delegator` (holding a cap to `target`) hands `recipient` its held cap to `target` ATTENUATED to
  `keep` — REAL conferred rights `⊆` held (`recKDelegateAtten_non_amplifying`), stricter than the
  unattenuated held-cap copy used by `introduceA`. Routes to `recKDelegateAtten`. Balance-NEUTRAL
  (`caps`-only). -/
  | delegateAttenA  (delegator recipient target : CellId) (keep : List Auth)
  /-- `AttenuateCapability { cell→actor, slot→idx, narrower_permissions→keep }` (dregg1
  `apply_attenuate_capability`, `apply.rs:4377`): monotonically NARROW the actor's `idx`-th held cap
  to `keep` (widening rejected). The purest non-amplification (`capAuthConferred ⊆`). -/
  | attenuateA      (actor : CellId) (idx : Nat) (keep : List Auth)
  /-- `DropRef { ref_id }` (dregg1 `apply_drop_ref`, `apply.rs:4034`): a CapTP GC decrement — the
  `holder` drops its edge to `target`. Reuses `recKRevokeTarget` (`removeEdge`); authority shrinks. -/
  | dropRefA        (holder target : CellId)
  /-- `RevokeDelegation { child→holder }` (dregg1 `apply_revoke_delegation`, `apply.rs:3044`): a
  parent revokes a child's delegation — the `holder` loses its edge to `target`. Reuses
  `recKRevokeTarget` (`removeEdge`). A DISTINCT dregg1 op from `DropRef` (parent-revocation vs.
  holder-GC), sharing the graph move. -/
  | revokeDelegationA (holder target : CellId)
  /-- `ValidateHandoff { … }` (dregg1 `apply_validate_handoff`, `apply.rs:4069`): graph-level
  consequence of an accepted two-signature CapTP handoff certificate. This constructor intentionally
  carries only `(introducer, recipient, target)`, so its executable content is the introduce skeleton:
  run `recCDelegate` and copy the introducer's held cap to `target`. The real certificate permissions
  and `granted ⊆ held` attenuation check are modeled by `Exec.CapTP.HandoffCert` / the swiss-table
  handoff path (`swissHandoffA`), not by pretending this skeleton has an uncarried `keep` payload. -/
  | validateHandoffA (introducer recipient target : CellId)
  /-- `ExerciseViaCapability { cap_slot→target, inner_effects }` (dregg1 `apply_exercise_via_capability`,
  `apply.rs:2441`): exercise a HELD cap to RUN `inner` effects against the target cell. dregg1's
  structure is lookup→facet-mask(`allowed_effects`)→RECURSE: after verifying the actor HOLDS the cap to
  `target` (`apply.rs:2455` `lookup`) the cap graph is UNCHANGED (exercising reads, never edits, the
  c-list), then each inner effect is APPLIED against the cap's target cell (`apply.rs:2647`
  `apply_effect(inner_effect, …, &cap_target, …)`). The exercise is thus a SUB-FOREST: `execFullA`
  recurses through `inner` (the mutual `execInnerA` fold below), fail-closed if the hold-gate fails or
  ANY inner effect fails. NON-shadow: the combined per-asset delta SUMS the inner deltas (like
  `execFullTurnA`). The facet-mask (`allowed_effects`) restriction is carried at the §8/theorem layer
  (the E-language facet view), distinct from the executable hold-gate + recurse. -/
  | exerciseA       (actor target : CellId) (inner : List FullActionA)
  -- §MA-supply: the 3 ACCOUNT-GROWTH / SUPPLY effects (`META-FILL C`). createCell/spawn GROW
  -- `accounts` (born EMPTY ⇒ conservation-NEUTRAL, `ledgerDeltaAsset = 0`); bridgeMint is the §8
  -- PORTAL inflow (disclosed `+value` at ONE asset).
  /-- `CreateCell { public_key, token_id, balance }` (dregg1 `apply_create_cell`, `apply.rs:748`):
  PRIVILEGED creation of a FRESH live cell, born `balance == 0` (`apply.rs:757` rejects
  `CreateCellNonZeroBalance`) — born EMPTY in every asset, so conservation-NEUTRAL. NO amount param
  (the dregg1-faithful choice); authority: `mintAuthorizedB actor newCell` + the freshness gate. -/
  | createCellA     (actor newCell : CellId)
  /-- `CreateCellFromFactory { factory_vk, … params }` (dregg1 `apply_create_cell_from_factory`,
  `apply.rs:3112`): mint a fresh cell from a PUBLISHED factory `vk`. Validates the factory exists in
  the registry + its declared initial state conforms to its own caveats (`validate_and_record`), then
  mints the cell (born EMPTY) carrying the factory's initial fields, program VK, AND its `slotCaveats`
  (the lifetime program enforced on every later `SetField`). Conservation-NEUTRAL (born empty), but the
  CONSTRAINTS are the point: the cell is *registered-forever / monotone-head* from birth. -/
  | createCellFromFactoryA (actor newCell : CellId) (vk : Int)
  /-- `SpawnWithDelegation { … }` (dregg1 `apply_spawn_with_delegation`): `createCell` (born EMPTY) PLUS
  a copy of the actor's already-held parent cap to `target`. The create leg is neutral; the cap copy is
  bal-orthogonal, so spawn is conservation-NEUTRAL too, without manufacturing authority to unrelated
  targets. -/
  | spawnA          (actor child target : CellId)
  /-- `BridgeMint { cell, value, asset_type, nullifier }` (dregg1 `apply_bridge_mint`, `apply.rs:1106`):
  the §8 PORTAL inflow — credit `cell`'s asset `asset` by a disclosed `value` observed off a FOREIGN
  chain. GENERATIVE (disclosed `+value` at asset `asset` ONLY). dregg2 cannot verify foreign consensus,
  so foreign finality is the §8 `Prop` carrier (off this executable layer); the LOCAL credit reuses the
  per-asset mint `recCMintAsset` verbatim. -/
  | bridgeMintA     (actor cell : CellId) (asset : AssetId) (value : ℤ)
  -- §MA-escrow: the off-ledger holding-store + commitment/nullifier SET effects (`META-FILL C`,
  -- closing `#121`). escrow/obligation/committed-escrow DEBIT one cell at one asset and PARK the value
  -- (combined per-asset conserving, bare-bal debiting); notes move the nullifier/commitment SET (not
  -- `bal`). The §8 crypto (committed-escrow opening, note range/spending proofs) is the THEOREM-level
  -- portal (off this executable layer, exactly as bridgeMint's foreign finality).
  /-- `CreateEscrow { id, creator, recipient, asset, amount }` (dregg1 `apply_create_escrow`): lock
  `amount` of `asset` from `creator` into the off-ledger holding-store (single-cell debit + parked
  record). Combined per-asset conserving; bare per-asset ledger DEBITED at `asset`. -/
  | createEscrowA   (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
  /-- `ReleaseEscrow { id }` (dregg1 `apply_release_escrow`): credit the recipient at the record's asset
  + mark resolved. Combined per-asset conserving. -/
  | releaseEscrowA  (id : Nat) (actor : CellId)
  /-- `RefundEscrow { id }` (dregg1 `apply_refund_escrow`): credit the creator (refund target) + mark
  resolved. Combined per-asset conserving. -/
  | refundEscrowA   (id : Nat) (actor : CellId)
  /-- `CreateObligation { id, obligor, beneficiary, stake }` (dregg1 `apply_create_obligation`): the
  SAME holding-store as escrow (single-cell stake debit + parked record). Dispatch-ALIASED to
  `createEscrowA` (obligor=creator, beneficiary=recipient, stake=amount). -/
  | createObligationA (id : Nat) (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
  /-- `FulfillObligation { obligation_id, proof }` (dregg1 `apply_fulfill_obligation`, `apply.rs:1483`):
  the obligor met the condition (the §8 proof carrier, `apply.rs:1547` `verifier.verify`) — RETURN the
  staked amount to the obligor from the holding-store and mark resolved (`apply.rs:1574-1594`). Only the
  obligor may fulfill (`apply.rs:1525` `action_target != record.obligor`) and only BEFORE the deadline
  (`apply.rs:1534`); those gates are carried at the §8/theorem layer (block-height + obligor identity).
  Since the parked obligation record IS an `EscrowRecord` (`creator = obligor`, `recipient = beneficiary`,
  `amount = stake`), the stake-return-to-obligor leg is EXACTLY the per-asset escrow REFUND (credit the
  `creator`/obligor at the record's asset + mark resolved) — combined per-asset CONSERVING. Routes to
  `refundEscrowChainA`. DISTINCT from `refundEscrowA` by the obligor-only fulfill gate (vs. escrow's
  by-creator refund). -/
  | fulfillObligationA (id : Nat) (actor : CellId)
  /-- `SlashObligation { obligation_id }` (dregg1 `apply_slash_obligation`, `apply.rs:1599`): the
  deadline passed without fulfillment (`apply.rs:1637` `block_height <= deadline_height` rejects) — the
  stake is TRANSFERRED from the holding-store to the BENEFICIARY and the record marked resolved
  (`apply.rs:1645-1667`). The deadline gate is carried at the §8/theorem layer (block-height). Since the
  parked record IS an `EscrowRecord` (`recipient = beneficiary`, `amount = stake`), the stake-to-
  beneficiary leg is EXACTLY the per-asset escrow RELEASE (credit the `recipient`/beneficiary at the
  record's asset + mark resolved) — combined per-asset CONSERVING. Routes to `releaseEscrowChainA`.
  DISTINCT from `releaseEscrowA` by the post-deadline slash gate (vs. escrow's condition-met release). -/
  | slashObligationA  (id : Nat) (actor : CellId)
  /-- `NoteSpend { nullifier }` (dregg1 `apply_note_spend`): the nullifier-SET insert with double-spend
  rejection (the ledger anti-replay gate). The §8 STARK spending proof is the THEOREM-level portal.
  bal-NEUTRAL. -/
  | noteSpendA      (nf : Nat) (actor : CellId)
  /-- `NoteCreate { commitment }` (dregg1 `apply_note_create`): the grow-only commitment-SET insert (the
  dual of noteSpend). The §8 range proof is the THEOREM-level portal. bal-NEUTRAL. -/
  | noteCreateA     (cm : Nat) (actor : CellId)
  /-- `CreateCommittedEscrow { id, …, value_commitment, range_proof, amount }` (`#121` + WAVE 4
  HONESTY): a PRIVACY escrow whose amount is hidden behind a Pedersen commitment (the record `id` is the
  commitment key). **NO LONGER silently identical to plain escrow** — it carries an EXPLICIT §8
  hiding-portal witness `hidingProof : Bool` (the executable boolean shadow of the Pedersen range/opening
  proof, dregg1 `apply_create_committed_escrow`'s `verifier.verify(range_proof, …)`, `apply.rs:2125`).
  FAIL-CLOSED if the portal does NOT hold (`hidingProof = false`): the committed variant REQUIRES a
  hiding obligation the plain `createEscrowA` does not. Under the discharged portal the lock automaton is
  the per-asset escrow, so it inherits the combined-conservation. -/
  | createCommittedEscrowA (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
      (hidingProof : Bool)
  /-- `ReleaseCommittedEscrow { id }` (`#121`): portal-gated release of a committed escrow. -/
  | releaseCommittedEscrowA (id : Nat) (actor : CellId)
  /-- `RefundCommittedEscrow { id }` (`#121`): portal-gated refund of a committed escrow. -/
  | refundCommittedEscrowA  (id : Nat) (actor : CellId)
  -- §MA-bridge: the cross-chain two-phase bridge (Wave-5 `PHASE-BRIDGE`) on the SHARED escrow
  -- holding-store (a `bridge := true`-tagged record). bridgeMint (the INBOUND side) is already done
  -- (`bridgeMintA`, above — reuses `recCMintAsset`). These are the OUTBOUND legs:
  /-- `BridgeLock { nullifier, destination, value, asset_type, timeout_height, spending_proof }`
  (dregg1 `apply_bridge_lock`, `cell/src/note_bridge.rs::initiate_bridge`): lock `amount` of `asset`
  from `originator` into the off-ledger holding-store — value INACCESSIBLE, AWAITING the other-chain
  confirmation (single-cell debit + parked bridge-tagged record). Combined per-asset CONSERVING; bare
  per-asset ledger DEBITED at `asset` (≈ escrow create). The §8 spending proof is the THEOREM-level
  portal. -/
  | bridgeLockA     (id : Nat) (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
  /-- `BridgeFinalize { nullifier, receipt }` (dregg1 `apply_bridge_finalize`,
  `cell/src/note_bridge.rs::finalize_bridge`): the §8 confirmation receipt arrived (the
  destination-federation signature — `verify_bridge_receipt`, the §8 portal); the lock RESOLVES and the
  value LEAVES for the other chain — a BURN on this side (no credit). COMBINED per-asset measure DROPS by
  the bridged amount (a disclosed OUTFLOW). The ONE holding-store resolution that does NOT conserve, and
  honestly so. The receipt DISCLOSES the bridged `(asset, amount)` — carried on the action so the
  per-asset conservation VECTOR can state the `-amount` move at `asset`; the executor gates on the parked
  record's `(asset, amount)` MATCHING the disclosed pair (fail-closed otherwise, exactly as dregg1's
  finalize checks the receipt against the pending bridge). -/
  | bridgeFinalizeA (id : Nat) (actor : CellId) (asset : AssetId) (amount : ℤ)
  /-- `BridgeCancel { nullifier }` (dregg1 `apply_bridge_cancel`,
  `cell/src/note_bridge.rs::cancel_bridge`): the timeout was reached without a receipt; the note is
  UNLOCKED and the value REFUNDED to the originator (single-cell credit + resolve). COMBINED per-asset
  CONSERVING (≈ escrow refund). The timeout gate is carried at the theorem layer. -/
  | bridgeCancelA   (id : Nat) (actor : CellId)
  -- §MA-seal: the 6 SIMPLE bal-NEUTRAL effects (Wave 6). Each writes a cell flag/metadata field or
  -- records a refusal — and NEVER touches the `bal` ledger, so `ledgerDeltaAsset = 0` for EVERY asset.
  -- The §8 crypto (AEAD for seal/unseal, the commitment for makeSovereign) is the CHAIN-LAYER portal.
  /-- `Seal { pair_id, capability }` (dregg1 `apply_seal`, `apply.rs:2743`): **DE-SHADOWED (Wave-3).** Look
  up the actor's HELD sealer cap for `pid` (`lookup_by_target`, `apply.rs:2756`; fail-closed
  `CapabilityNotHeld`), then SEAL a HELD `payload` cap into a box keyed by `pid` — the box BINDS the
  SPECIFIC cap (REAL, not a `sealed_box := 1` flag). The AEAD ciphertext is the §8 portal; WHICH cap is
  sealed is REAL. Routes to `sealChainA`. Generative. bal-NEUTRAL. -/
  | sealA           (pid : Nat) (actor : CellId) (payload : Cap)
  /-- `Unseal { sealed_box, recipient }` (dregg1 `apply_unseal`, `apply.rs:2874`): **DE-SHADOWED (Wave-3).**
  Look up the actor's HELD unsealer cap for `pid` + find the box (fail-closed if absent), then UNDER the §8
  AEAD-open carrier GRANT the recovered `payload` cap to the `recipient`'s c-list (`grant_with_breadstuff`,
  `apply.rs:2926`) — the capability GENUINELY MOVES out of the box into the recipient. Routes to
  `unsealChainA`. Generative. bal-NEUTRAL. -/
  | unsealA         (pid : Nat) (actor recipient : CellId)
  /-- `CreateSealPair { sealer_holder, unsealer_holder }` (dregg1 `apply_create_seal_pair`, `apply.rs:2675`):
  **DE-SHADOWED (Wave-3).** GRANT a sealer cap to `sealerHolder` AND an unsealer cap to `unsealerHolder` —
  TWO real c-list grants (`grant_with_breadstuff`, `apply.rs:2705`/`:2725`; the AEAD keypair is the §8
  portal), NOT a `seal_pair := 1` flag. Authority: `stateAuthB actor sealerHolder`. Routes to
  `createSealPairChainA`. Generative. bal-NEUTRAL. -/
  | createSealPairA (pid : Nat) (actor sealerHolder unsealerHolder : CellId)
  /-- `MakeSovereign { cell }` (dregg1 `apply_make_sovereign`): flip `cell` to commitment-only
  (sovereign) REPRESENTATION. ASSESSED bal-neutral: dregg1's `make_sovereign` PRESERVES balance/state
  (a representation move, NOT an escrow — no value moves into commitment-form on the per-asset ledger).
  Authority: dregg1 requires `cell == action_target` (self-sovereign) ⇒ the cell's own authority
  (`stateAuthB actor cell`). Terminal. bal-NEUTRAL. The commitment binding is the §8 portal. -/
  | makeSovereignA  (actor cell : CellId)
  /-- `Refusal { cell, … }` (dregg1 `apply_refusal`): record a refusal witness — bump the nonce + write
  the refusal commitment into the audit field; dregg1 NEVER mutates balance/caps/value. Authority:
  dregg1 gates a cross-cell refusal on `SetState` (`stateAuthB actor cell`). Monotonic. bal-NEUTRAL. -/
  | refusalA        (actor cell : CellId)
  /-- `ReceiptArchive { prefix_end_height, checkpoint }` (dregg1 `apply_receipt_archive`): archive/prune
  the receipt-chain prefix — transition lifecycle to `Archived` (cell stays live) + bind the checkpoint.
  A LOG/field operation. Authority: dregg1 requires checkpoint cell_id = action_target (`stateAuthB
  actor cell`). Terminal. bal-NEUTRAL. -/
  | receiptArchiveA (actor cell : CellId)
  -- §MA-queue: the 4 REAL ring-buffer FIFO QUEUE effects (Wave-7 de-THIN). Each touches ONLY the queue
  -- side-table (`queues`), NEVER the `bal` ledger — queues hold MESSAGES (content hashes / capability
  -- invocations, `CapInbox`), NOT balance — so `ledgerDeltaAsset = 0` for EVERY asset (bal-NEUTRAL).
  -- The FIFO ORDER + capacity bound + emptiness fail-closed are the REAL automaton (`qbufEnqueue`/
  -- `qbufDequeue` + the kernel `queue*K` transitions), PROVED — a flag/no-op shadow would have NO order
  -- and NO bound (the GROUND-STORAGE de-THIN requirement).
  /-- `QueueAllocate { capacity, program_vk }` (dregg1 `apply_queue_allocate`, `apply.rs:3227`): create a
  fresh queue (id `id`, owner = `cell`'s actor) with `capacity` and an EMPTY buffer. Authority: `actor`
  holds authority over the queue's representing `cell` (`stateAuthB`). Generative. bal-NEUTRAL. -/
  | queueAllocateA  (id : Nat) (actor cell : CellId) (capacity : Nat)
  /-- `QueueEnqueue { queue, message_hash, deposit }` (dregg1 `apply_queue_enqueue`, `apply.rs:3310`):
  APPEND message hash `m` to the TAIL of queue `id`'s FIFO buffer AND PARK a REFUNDABLE anti-spam
  `deposit` of asset `dAsset` from the `actor` sender into the holding-store keyed by `depId`. Fail-closed
  if the queue is absent OR FULL (`apply.rs:3348`), OR the sender lacks the deposit (`InsufficientBalance`,
  `apply.rs:3361`). Authority: `actor` holds authority over the queue `cell` (the writer-ACL gate,
  `apply.rs:3334`). **Wave-8 residual close**: the deposit is NO LONGER unmodeled — it GENUINELY moves
  the bare `recTotalAsset` (parked off-ledger) while the COMBINED measure is CONSERVED (a refundable
  transfer-like move). Conservative, combined-conserving. -/
  | queueEnqueueA   (id : Nat) (m : Nat) (actor cell : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
  /-- `QueueDequeue { queue }` (dregg1 `apply_queue_dequeue`, `apply.rs:3420`): REMOVE-FROM-FRONT of
  queue `id`'s FIFO buffer (the OLDEST waiting message) AND REFUND the deposit record `depId` to the
  dequeuer (`apply.rs:3483`). Fail-closed if absent, the actor is NOT the queue owner (`apply.rs:3433`),
  the buffer is EMPTY (`apply.rs:3444`), OR the deposit record is absent. Authority: `actor` holds
  authority over the queue `cell` AND is the kernel-level owner. **Wave-8**: the refund RETURNS the
  deposit to the dequeuer's ledger (combined-conserving). Conservative. -/
  | queueDequeueA   (id : Nat) (actor cell : CellId) (depId : Nat) (deposit : ℤ)
  /-- `QueueResize { queue, new_capacity }` (dregg1 `apply_queue_resize`, `apply.rs:3507`): change queue
  `id`'s capacity to `newCap`. Fail-closed if absent OR shrinking below the current occupancy
  (`apply.rs:3534`, "can't shrink below current occupancy"). Authority: `actor` holds authority over the
  queue `cell`. Generative. bal-NEUTRAL. -/
  | queueResizeA    (id : Nat) (newCap : Nat) (actor cell : CellId)
  -- §MA-queue-batch (WAVE 4): the ATOMIC cross-queue transaction + the PIPELINE fan-out step.
  /-- `QueueAtomicTx { operations }` (dregg1 `apply_queue_atomic_tx`, `apply.rs:3586`): execute a BATCH
  of `QueueTxOp::{Enqueue,Dequeue}` ALL-OR-NOTHING against one or more queues. The batch COMMITS iff
  EVERY sub-op commits (each against the prior's result); ANY sub-op failing ⇒ the WHOLE batch rolls back
  (dregg1's journal-rollback, `apply.rs:3592`). The ATOMICITY is the proven property
  (`queueAtomicTxChainA_commits_iff_all`). Each sub-op is the proven combined-conserving chained queue
  step, so the batch is combined-conserving. Conservative. -/
  | queueAtomicTxA  (actor : CellId) (ops : List QueueTxOpA)
  /-- `QueuePipelineStep { pipeline_id, source, sinks }` (dregg1 `apply_queue_pipeline_step`,
  `apply.rs:3747`): DEQUEUE the FIFO head from a source queue `srcId` (owner-only, `apply.rs:3754`) and
  RE-ENQUEUE the moved head message into EACH sink (each ACL-checked per-sink, `apply.rs:3812` BUG#114
  sink-auth gate). Fan-out routing: one message in, one copy into each sink. Fail-closed if the source is
  absent / not-owned / EMPTY, or any sink absent / FULL / unauthorized. `sinkCells`/`sinkIds` pair the
  representing cell + queue id of each sink position-wise. bal-NEUTRAL (moves messages, not balance). -/
  | queuePipelineStepA (srcId : Nat) (owner : CellId) (sinkCells : List CellId) (sinkIds : List Nat)
  /-- `PipelinedSend { target : EventualRef, action }` (dregg1 `apply_pipelined_send`, `apply.rs:2657`):
  E-style PROMISE PIPELINING — dispatch an `action` to the RESULT of a prior turn (an `EventualRef` slot
  the producer fills). dregg1's `apply_pipelined_send` is a HARD ERROR at apply time (`apply.rs:2663`
  "unresolved PipelinedSend … turn must be executed within a pipeline") — the resolution happens in the
  PIPELINE EXECUTOR's resolution pass BEFORE the turn reaches `apply_effect`. The faithful model: the
  `EventualRef`→prior-result resolution is the SEPARATE batch machinery in `ConditionalTurn.lean` (the
  topological-order producer-slot fill the consumer reads); AT apply time the resolved action has already
  run, so the apply-time effect is NEUTRAL (no state move) — exactly dregg1's apply-time no-op-or-error.
  We model the apply-time Neutral step (a clock row, no ledger move); the deferred dispatch + resolution
  is `ConditionalTurn`'s `ConditionalBatch`/`Slots`/topo-order (documented in the report mapping). -/
  | pipelinedSendA  (actor : CellId)
  -- §MA-swiss: the 4 REAL CapTP swiss-table effects (Wave-8 de-THIN). Each touches ONLY the swiss
  -- side-table (`swiss`), NEVER the `bal` ledger — the swiss-table moves REFERENCES (capability routing),
  -- not balance, so `ledgerDeltaAsset = 0` for EVERY asset (bal-NEUTRAL). The export-INSERT /
  -- enliven-LOOKUP-fail-closed / handoff-cert-bind / refcount-GC are the REAL registry (`swiss*K`), PROVED.
  /-- `ExportSturdyRef { swiss_number, target, permissions }` (dregg1 `apply_export_sturdy_ref`,
  `apply.rs:3879`): the holder `exporter` mints a sturdy ref — INSERT a swiss→cap entry (`sw` → `target`
  with `rights`, refcount 1). Fail-closed on duplicate swiss OR on amplification (`rights ⊄` the exporter's
  REAL committed rights `heldAuths s.kernel exporter`, `apply.rs:3917`). **SOUNDNESS:** the held bound is
  read from the EXECUTED c-list `s.kernel.caps exporter`, NOT a caller-supplied parameter — so no
  capability amplification. Authority: `actor` holds authority over the `exporter` cell (holder of the cap).
  Monotonic. bal-NEUTRAL. -/
  | exportSturdyRefA (sw : Nat) (actor exporter target : CellId) (rights : List Auth)
  /-- `EnlivenRef { swiss_number, bearer, expected_cell_id, expected_permissions }` (dregg1
  `apply_enliven_ref`, `apply.rs:3955`): VALIDATE a presented swiss number against the committed
  swiss-table (fail-closed if absent) + validate non-amplification (`claimed ⊆ entry.rights`,
  `apply.rs:3999`) + BUMP the refcount (a new live reference). Authority: `actor` over the `exporter` cell.
  Monotonic. bal-NEUTRAL. -/
  | enlivenRefA      (sw : Nat) (actor exporter : CellId) (claimed : List Auth)
  /-- `ValidateHandoff { cert_hash, … }` (dregg1 `apply_validate_handoff`, `apply.rs:4109`): bind a 3-vat
  introduce CERT to the swiss entry `sw` + bump the refcount (the recipient's new live ref). Fail-closed
  if absent. Authority: the `introducer` holds authority over the `exporter` cell. The two-signature
  crypto is the §8 portal. Monotonic. bal-NEUTRAL. -/
  | swissHandoffA    (sw certHash : Nat) (introducer exporter : CellId)
  /-- `DropRef { ref_id }` (dregg1 `apply_drop_ref`, `apply.rs:4035`): GC a reference — DECREMENT the
  swiss entry `sw`'s refcount, REMOVING the entry when it hits 0. Fail-closed if absent OR already-zero
  (`apply.rs:4051`). Authority: `actor` over the `exporter` cell. Terminal (the last drop GCs).
  bal-NEUTRAL. -/
  | swissDropA       (sw : Nat) (actor exporter : CellId)
  -- §MA-lifecycle (Wave-3): the cell LIFECYCLE state machine + refresh-delegation. Each edits a
  -- side-table (`lifecycle`/`deathCert`/`delegations`), NEVER the `bal` ledger ⇒ `ledgerDeltaAsset = 0`
  -- for EVERY asset (balance-NEUTRAL). The §8 crypto (the death-certificate hash) is the CHAIN-LAYER
  -- portal; the STATE MACHINE (Live↔Sealed/Destroyed, the c-list snapshot) is REAL.
  /-- `CellSeal { target, reason }` (dregg1 `apply_cell_seal` → `Cell::seal`, `apply.rs:4218`/
  `cell.rs:528`): Live→Sealed. Fail-closed on authority (`stateAuthB`) AND on the state machine — only a
  LIVE cell may seal (a Sealed cell is `AlreadySealed`, a terminal cell is `Terminal`). Routes to
  `cellSealChainA`. bal-NEUTRAL. -/
  | cellSealA       (actor cell : CellId)
  /-- `CellUnseal { target }` (dregg1 `apply_cell_unseal` → `Cell::unseal`, `apply.rs:4251`/`cell.rs:559`):
  Sealed→Live. Fail-closed on authority AND on the state machine — only a SEALED cell may unseal
  (`NotSealed` otherwise). Routes to `cellUnsealChainA`. bal-NEUTRAL. -/
  | cellUnsealA     (actor cell : CellId)
  /-- `CellDestroy { target, certificate }` (dregg1 `apply_cell_destroy` → `Cell::destroy`,
  `apply.rs:4283`/`cell.rs:583`): any NON-terminal → Destroyed, binding the `DeathCertificate` hash
  `certHash` into the FINAL state. Fail-closed on authority AND on the state machine — a Destroyed cell is
  `Terminal`-rejected (TERMINAL: no further effect accepted). Routes to `cellDestroyChainA`. bal-NEUTRAL. -/
  | cellDestroyA    (actor cell : CellId) (certHash : Nat)
  /-- `RefreshDelegation { }` (dregg1 `apply_refresh_delegation`, `apply.rs:2991`): SELF-only refresh — take
  a FRESH snapshot of the parent's CURRENT c-list into the child's delegation, journaling the old. Distinct
  from spawn (INITIAL snapshot) and revokeDelegation (CLEAR). Fail-closed on the self-authority gate AND the
  child having a parent (`delegate child ≠ 0`). Routes to `refreshDelegationChainA`. bal-NEUTRAL. -/
  | refreshDelegationA (actor child : CellId)

/-- **The per-asset COMBINED ledger delta of a `FullActionA`, indexed by asset `b`** — the move of the
COMBINED measure `recTotalAssetWithEscrow` (= `bal`-ledger + per-asset holding-store). Transfer and
authority are conservation-trivial (`0` for every asset); `mintA a` adds `amt` to asset `a` only;
`burnA a` subtracts from asset `a` only. The 5 PURE-STATE effects write the `cell` record / the LOG,
never `bal` — so `0`. The escrow/obligation/committed-escrow legs DEBIT the bare `bal` ledger by
∓amount at the locked asset BUT park exactly that into the per-asset holding-store, so their COMBINED
delta is `0` (combined-conserving, even though the bare ledger genuinely moves — that bare debit is
witnessed by `createEscrowChainA_bal_debits`). Notes move the nullifier/commitment SET, not `bal`, so
`0`. A FAMILY indexed by `AssetId` — never one aggregate scalar. -/
def ledgerDeltaAsset : FullActionA → AssetId → ℤ
  | .balanceA _ _,        _ => 0
  | .delegate _ _ _,      _ => 0
  | .revoke _ _,          _ => 0
  | .mintA _ _ a amt,     b => if b = a then amt else 0
  | .burnA _ _ a amt,     b => if b = a then (-amt) else 0
  | .setFieldA _ _ _ _,   _ => 0
  | .emitEventA _ _ _ _,  _ => 0
  | .incrementNonceA _ _ _, _ => 0
  | .setPermissionsA _ _ _, _ => 0
  | .setVKA _ _ _,        _ => 0
  -- §MA-auth: the 6 authority effects EDIT/CHECK `caps`, NEVER `bal` — so `0` for EVERY asset.
  | .introduceA _ _ _,    _ => 0
  | .delegateAttenA _ _ _ _, _ => 0
  | .attenuateA _ _ _,    _ => 0
  | .dropRefA _ _,        _ => 0
  | .revokeDelegationA _ _, _ => 0
  | .validateHandoffA _ _ _, _ => 0
  -- exercise RECURSES through `inner` against the cap's target — so its COMBINED per-asset delta is the
  -- SUM of the inner effects' deltas (a sub-forest, exactly like `turnLedgerDeltaAsset`). The bare
  -- hold-gate + receipt are bal-neutral; the move is whatever `inner` moves.
  | .exerciseA _ _ inner, b => (inner.map (fun fa => ledgerDeltaAsset fa b)).sum
  -- §MA-supply: createCell/spawn GROW `accounts` but the fresh cell is born EMPTY (bal-reset) — so `0`
  -- for EVERY asset (account-growth NEUTRALITY). bridgeMint discloses `+value` at the targeted asset ONLY.
  | .createCellA _ _,     _ => 0
  -- factory creation mints a BORN-EMPTY cell (balance 0 in every asset) + installs its program — so
  -- the COMBINED measure is unmoved for EVERY asset (account-growth-with-program NEUTRALITY).
  | .createCellFromFactoryA _ _ _, _ => 0
  | .spawnA _ _ _,        _ => 0
  | .bridgeMintA _ _ a value, b => if b = a then value else 0
  -- §MA-escrow: escrow/obligation/committed-escrow are COMBINED-conserving (bal debit offset by the
  -- holding-store park), so their COMBINED delta is `0`; notes move SETs, not `bal`, so `0`.
  | .createEscrowA _ _ _ _ _ _,   _ => 0
  | .releaseEscrowA _ _,          _ => 0
  | .refundEscrowA _ _,           _ => 0
  | .createObligationA _ _ _ _ _ _, _ => 0
  -- fulfill returns the stake to the obligor (≈ escrow refund) / slash transfers it to the beneficiary
  -- (≈ escrow release): both SETTLE the parked record back onto the ledger, COMBINED per-asset conserving.
  | .fulfillObligationA _ _,      _ => 0
  | .slashObligationA _ _,        _ => 0
  | .noteSpendA _ _,              _ => 0
  | .noteCreateA _ _,             _ => 0
  | .createCommittedEscrowA _ _ _ _ _ _ _, _ => 0
  | .releaseCommittedEscrowA _ _, _ => 0
  | .refundCommittedEscrowA _ _,  _ => 0
  -- §MA-bridge: LOCK is COMBINED-conserving (bal debit offset by the holding-store park), so its COMBINED
  -- delta is `0`; CANCEL refunds the originator (combined fixed), so `0`; FINALIZE is the ONE disclosed
  -- OUTFLOW — the value LEFT for the other chain, so the COMBINED measure DROPS by the DISCLOSED `amount`
  -- at the disclosed `asset` ONLY (like burn, `-amount`), every other asset fixed.
  | .bridgeLockA _ _ _ _ _ _,     _ => 0
  | .bridgeFinalizeA _ _ a amount, b => if b = a then (-amount) else 0
  | .bridgeCancelA _ _,           _ => 0
  -- §MA-seal: the DE-SHADOWED seal/unseal/createSealPair MOVE capabilities (edit `caps`/`sealedBoxes`),
  -- NEVER `bal` — so `0` for EVERY asset (balance-NEUTRAL). makeSovereign/refusal/receiptArchive write
  -- the `cell` record / lifecycle field, also `0`. The §8 crypto is the chain-layer portal, off the ledger.
  | .sealA _ _ _,                 _ => 0
  | .unsealA _ _ _,               _ => 0
  | .createSealPairA _ _ _ _,     _ => 0
  | .makeSovereignA _ _,          _ => 0
  | .refusalA _ _,                _ => 0
  | .receiptArchiveA _ _,         _ => 0
  -- §MA-queue: the 4 queue effects touch ONLY the `queues` side-table (messages, not balance), NEVER
  -- `bal`/`escrows` — so `0` for EVERY asset (balance-NEUTRAL; `recTotalAssetWithEscrow` UNCHANGED).
  | .queueAllocateA _ _ _ _,      _ => 0
  | .queueEnqueueA _ _ _ _ _ _ _, _ => 0
  | .queueDequeueA _ _ _ _ _,     _ => 0
  | .queueResizeA _ _ _ _,        _ => 0
  -- §MA-queue-batch (WAVE 4): the atomic batch sequences combined-conserving sub-ops (each `0`), so its
  -- combined delta is `0`; the pipeline step moves a MESSAGE source→sinks (no balance) ⇒ `0`; the
  -- pipelined-send apply-time effect is NEUTRAL (the resolved action already ran) ⇒ `0`.
  | .queueAtomicTxA _ _,          _ => 0
  | .queuePipelineStepA _ _ _ _,  _ => 0
  | .pipelinedSendA _,            _ => 0
  -- §MA-swiss: the 4 CapTP swiss-table effects move REFERENCES, never balance ⇒ `0` at every asset.
  | .exportSturdyRefA _ _ _ _ _, _ => 0
  | .enlivenRefA _ _ _ _,          _ => 0
  | .swissHandoffA _ _ _ _,        _ => 0
  | .swissDropA _ _ _,             _ => 0
  -- §MA-lifecycle (Wave-3): seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits
  -- `delegations` — all side-tables, NEVER `bal`/`escrows` ⇒ `0` at every asset (balance-NEUTRAL).
  | .cellSealA _ _,                _ => 0
  | .cellUnsealA _ _,              _ => 0
  | .cellDestroyA _ _ _,           _ => 0
  | .refreshDelegationA _ _,       _ => 0

mutual
/-- **The per-asset full executor.** Dispatch each kind to its chained per-asset primitive. ONE
executor over the per-asset op-set; the asset-typed analog of `execFull`. The 5 pure-state effects
route to `EffectsState.stateStep` (the authority-gated field write — `setFieldA`/`incrementNonceA`/
`setPermissionsA`/`setVKA`) or to `emitStep` (the authority-free log append — `emitEventA`), the
ALREADY-PROVEN per-effect steps. `exerciseA` RECURSES through its carried `inner` effects (the mutual
`execInnerA` fold), so `execFullA` is self-referential — but only through STRUCTURAL subterms of the
`exerciseA` constructor, so Lean derives termination automatically (the same shape as
`execFullForestA`/`execFullChildrenA`). -/
def execFullA (s : RecChainedState) : FullActionA → Option RecChainedState
  | .balanceA t a           => recCexecAsset s t a
  | .delegate del rec t      => recCDelegate s del rec t
  | .revoke holder t         => some (recCRevoke s holder t)
  | .mintA actor cell a amt   => recCMintAsset s actor cell a amt
  | .burnA actor cell a amt   => recCBurnAsset s actor cell a amt
  -- §SLOT-CAVEAT: the developer-facing `SetField` is the one effect dregg1 routes through the cell's
  -- `RecordProgram::evaluate` per-slot caveats (`apply_set_field` → `cell/src/program.rs:1314`+). So
  -- `setFieldA` dispatches to the CAVEAT-GATED write `stateStepGuarded` (NOT the bare `stateStep`):
  -- a write violating an Immutable/MonotonicSequence/Monotonic/WriteOnce/SenderAuthorized/BoundedBy
  -- caveat on slot `f` of `cell` is REJECTED (fail-closed). The other field writes (nonce/perms/vk —
  -- protocol-managed slots, not developer SetField) stay on the bare authority-gated `stateStep`.
  | .setFieldA actor cell f v        => stateStepGuarded s f actor cell v
  | .emitEventA actor cell topic data =>
      if cell ∈ s.kernel.accounts then some (emitStep s actor cell topic data) else none
  | .incrementNonceA actor cell n     => stateStep s nonceField actor cell (.int n)
  | .setPermissionsA actor cell p     => stateStep s permsField actor cell (.int p)
  | .setVKA actor cell vk             => stateStep s vkField actor cell (.int vk)
  -- §MA-auth: the 6 authority effects route to the (reused/re-founded) chained authority steps.
  | .introduceA intro rec t          => recCDelegate s intro rec t
  | .delegateAttenA del rec t keep   => recCDelegateAtten s del rec t keep
  | .attenuateA actor idx keep       => some (attenuateStepA s actor idx keep)
  | .dropRefA holder t               => some (recCRevoke s holder t)
  | .revokeDelegationA holder t      => some (recCRevoke s holder t)
  | .validateHandoffA intro rec t    => recCDelegate s intro rec t
  -- exercise: gate on the actor HOLDING the cap-edge to `target` (`exerciseStepA`, the §8 cap lookup),
  -- THEN recurse — run the `inner` effects against the target via `execInnerA` (dregg1 `apply.rs:2647`
  -- folds `apply_effect(inner, …, &cap_target, …)`). Fail-closed: no held edge ⇒ `exerciseStepA = none`;
  -- any inner effect fails ⇒ the fold is `none` ⇒ the whole exercise rejects. No more SHADOW.
  | .exerciseA actor t inner         =>
      match exerciseStepA s actor t with
      | some s' => execInnerA s' inner
      | none    => none
  -- §MA-supply: createCell/spawn route to the account-growth chained steps (born EMPTY); bridgeMint
  -- reuses the per-asset mint `recCMintAsset` verbatim (the §8 portal hypothesis is carried on the
  -- conservation keystone, not checked here).
  | .createCellA actor newCell       => createCellChainA s actor newCell
  -- §MA-factory: mint from a published factory — validate registry+constraints, then create the cell
  -- carrying the factory's caveats/initial-fields/programVk (dregg1 `apply_create_cell_from_factory`).
  | .createCellFromFactoryA actor newCell vk => createCellFromFactoryChainA s actor newCell vk
  | .spawnA actor child target       => spawnChainA s actor child target
  | .bridgeMintA actor cell a value  => recCMintAsset s actor cell a value
  -- §MA-escrow: escrow/obligation/committed route to the chained per-asset holding-store steps;
  -- obligation/committed are dispatch-ALIASED to the escrow steps (same automaton, §8 portal at the
  -- theorem layer). Notes route to the SET-insert steps.
  | .createEscrowA id actor creator recipient asset amount =>
      createEscrowChainA s id actor creator recipient asset amount
  | .releaseEscrowA id actor          => releaseEscrowChainA s id actor
  | .refundEscrowA id actor           => refundEscrowChainA s id actor
  | .createObligationA id actor obligor beneficiary asset stake =>
      createEscrowChainA s id actor obligor beneficiary asset stake
  -- fulfill: the obligor met the condition — RETURN the stake to the obligor (= the record's
  -- `creator`), exactly the per-asset escrow REFUND (`apply.rs:1574` credits `record.obligor`). The
  -- obligor-only + before-deadline gates are §8/theorem-layer carriers.
  | .fulfillObligationA id actor      => refundEscrowChainA s id actor
  -- slash: the deadline passed — TRANSFER the stake to the BENEFICIARY (= the record's `recipient`),
  -- exactly the per-asset escrow RELEASE (`apply.rs:1656` credits `record.beneficiary`). The
  -- post-deadline gate is the §8/theorem-layer carrier.
  | .slashObligationA id actor        => releaseEscrowChainA s id actor
  | .noteSpendA nf actor              => noteSpendChainA s nf actor
  | .noteCreateA cm actor             => some (noteCreateChainA s cm actor)
  -- WAVE 4 HONESTY: committed-escrow create routes to the §8 hiding-portal-GATED chained step — NOT
  -- silently `createEscrowChainA`. FAIL-CLOSED if `hidingProof = false` (the privacy boundary plain
  -- escrow lacks). Under the discharged portal it inherits the per-asset escrow lock.
  | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof
  | .releaseCommittedEscrowA id actor => releaseEscrowChainA s id actor
  | .refundCommittedEscrowA id actor  => refundEscrowChainA s id actor
  -- §MA-bridge: lock/finalize/cancel route to the chained per-asset bridge steps over the SHARED escrow
  -- holding-store. bridgeMint (the inbound side) routes to `recCMintAsset` (already done, above).
  | .bridgeLockA id actor originator destination asset amount =>
      bridgeLockChainA s id actor originator destination asset amount
  | .bridgeFinalizeA id actor asset amount => bridgeFinalizeChainA s id actor asset amount
  | .bridgeCancelA id actor                => bridgeCancelChainA s id actor
  -- §MA-seal: the 6 simple bal-neutral effects route to the ALREADY-PROVEN authority-gated field write
  -- (`stateStep`), each into its named record field. The §8 crypto (AEAD ciphertext / commitment) is
  -- the chain-layer portal — the STATE move is the field write recorded here, NOT the crypto verify.
  -- §MA-seal (Wave-3 DE-SHADOW): seal/unseal/createSealPair route to the REAL capability-movement
  -- chained steps (the cap genuinely moves through the box / two real grants), NOT a flag flip. The
  -- AEAD crypto is the §8 chain-layer portal; the WHICH-cap binding + c-list grant are REAL.
  | .sealA pid actor payload      => sealChainA s pid actor payload
  | .unsealA pid actor recipient  => unsealChainA s pid actor recipient
  | .createSealPairA pid actor sealerHolder unsealerHolder => createSealPairChainA s pid actor sealerHolder unsealerHolder
  -- FILL #133: MakeSovereign is a VALUE-REBIND, not a flag — the readable record is DROPPED behind a
  -- commitment (`cells.remove(id)` + `sovereign_commitments.insert(id, cell.state_commitment())`).
  | .makeSovereignA actor cell    => makeSovereignStep s actor cell
  | .refusalA actor cell          => stateStep s refusalField actor cell (.int 1)
  | .receiptArchiveA actor cell   => stateStep s lifecycleField actor cell (.int 1)
  -- §MA-queue: the 4 queue effects route to the chained ring-buffer FIFO steps (authority-gated +
  -- the kernel-level capacity/owner/emptiness gates). The REAL FIFO automaton, NOT a flag.
  | .queueAllocateA id actor cell cap   => queueAllocateChainA s id actor cell cap
  | .queueEnqueueA id m actor cell depId dAsset deposit => queueEnqueueChainA s id m actor cell depId dAsset deposit
  | .queueDequeueA id actor cell depId deposit          => queueDequeueChainA s id actor cell depId deposit
  | .queueResizeA id newCap actor cell  => queueResizeChainA s id newCap actor cell
  -- §MA-queue-batch (WAVE 4): the atomic batch folds its sub-ops ALL-OR-NOTHING; the pipeline step
  -- dequeues source→fan-out sinks; pipelinedSend's apply-time effect is NEUTRAL (a clock row, the
  -- resolved action already ran — dregg1's apply-time no-op, the resolution is `ConditionalTurn`).
  | .queueAtomicTxA actor ops           => queueAtomicTxA s actor ops
  | .queuePipelineStepA srcId owner sinkCells sinkIds => queuePipelineStepA s srcId owner sinkCells sinkIds
  | .pipelinedSendA actor               => some { kernel := s.kernel, log := escrowReceiptA actor :: s.log }
  -- §MA-swiss: the 4 CapTP swiss-table effects route to the authority-gated swiss registry steps.
  | .exportSturdyRefA sw actor exporter target rights => swissExportChainA s sw actor exporter target rights
  | .enlivenRefA sw actor exporter claimed                 => swissEnlivenChainA s sw actor exporter claimed
  | .swissHandoffA sw certHash introducer exporter         => swissHandoffChainA s sw certHash introducer exporter
  | .swissDropA sw actor exporter                          => swissDropChainA s sw actor exporter
  -- §MA-lifecycle (Wave-3): the cell lifecycle state machine + self-only refresh route to the chained
  -- authority-gated lifecycle/refresh steps (Live↔Sealed/Destroyed + the fresh c-list snapshot). REAL
  -- state transitions, NOT flag flips.
  | .cellSealA actor cell          => cellSealChainA s actor cell
  | .cellUnsealA actor cell        => cellUnsealChainA s actor cell
  | .cellDestroyA actor cell ch    => cellDestroyChainA s actor cell ch
  | .refreshDelegationA actor child => refreshDelegationChainA s actor child

/-- **The inner-effect fold an `exerciseA` recurses through** (dregg1 `apply.rs:2647`: the `for
inner_effect in inner_effects` loop applying each against the cap's target). Folds `execFullA`
left-to-right, all-or-nothing — the definitional twin of `execFullTurnA` (proved equal below,
`execInnerA_eq_execFullTurnA`), re-founded HERE inside the `mutual` so `exerciseA`'s recursion is
STRUCTURAL (each inner element is a subterm of the `exerciseA` constructor). -/
def execInnerA (s : RecChainedState) : List FullActionA → Option RecChainedState
  | []        => some s
  | a :: rest =>
    match execFullA s a with
    | some s' => execInnerA s' rest
    | none    => none
end

mutual
/-- **`execFullA_ledger_per_asset` — PROVED (the COMBINED per-asset conservation VECTOR).** Every
committed `FullActionA` moves the COMBINED per-asset measure `recTotalAssetWithEscrow b` (= `bal`-ledger
+ per-asset holding-store) by EXACTLY `ledgerDeltaAsset fa b`, for EVERY asset `b` independently: `0`
for transfer/authority (the moved asset cancels; authority/notes leave `bal` AND `escrows` fixed), `±amt`
at the targeted asset for mint/burn/bridge (escrows fixed ⇒ combined = bare-bal), and `0` for the
escrow/obligation/committed-escrow legs — they DEBIT the bare `bal` by ∓amount but PARK exactly that into
the per-asset holding-store, so the COMBINED measure is fixed (combined-conserving). THIS is the law a
SCALAR kernel cannot state — it would let a mint of asset B net against a burn of asset A, or an escrow
of asset A launder into asset B. The per-asset COMBINED family forbids both. -/
theorem execFullA_ledger_per_asset (s s' : RecChainedState) (fa : FullActionA) (b : AssetId)
    (h : execFullA s fa = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + ledgerDeltaAsset fa b := by
  -- For the NON-holding-store kinds, the post-state leaves `escrows` fixed, so `escrowHeldAsset` is
  -- unchanged and the combined move equals the bare-`bal` move; for the escrow/note legs we read the
  -- combined-conservation off the per-asset holding-store lemmas (combined delta `0`). `exerciseA`
  -- recurses through the mutual `execInnerA_ledger_per_asset` (its combined delta SUMS the inner deltas).
  cases fa with
  | balanceA t a =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCexecAsset at h
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' =>
          rw [hx] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recTransferBal s.kernel.bal t.src t.dst a t.amt } from by
                      unfold recKExecAsset at hx; split at hx
                      · simpa only [Option.some.injEq] using hx.symm
                      · exact absurd hx (by simp)]; rfl,
              recKExecAsset_conserves_per_asset s.kernel k' t a hx b]; ring
  | delegate del rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | revoke holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, recKRevokeTarget]; ring
  | mintA actor cell a amt =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + _
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recBalCredit s.kernel.bal cell a amt } from by
                      unfold recKMintAsset at hm; split at hm
                      · simpa only [Option.some.injEq] using hm.symm
                      · exact absurd hm (by simp)]; rfl,
              recKMintAsset_delta s.kernel k' actor cell a amt hm b]; ring
  | burnA actor cell a amt =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCBurnAsset at h
      cases hb : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + _
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recBalCredit s.kernel.bal cell a (-amt) } from by
                      unfold recKBurnAsset at hb; split at hb
                      · simpa only [Option.some.injEq] using hb.symm
                      · exact absurd hb (by simp)]; rfl,
              recKBurnAsset_delta s.kernel k' actor cell a amt hb b]; ring
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: `setFieldA` now routes through the caveat-gated write `stateStepGuarded`. A
      -- committed guarded write commits exactly `stateStep`'s post-state (a named-field write), so it
      -- leaves the COMBINED per-asset measure UNCHANGED — `ledgerDeltaAsset (.setFieldA …) = 0`.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [stateStepGuarded_recTotalAssetWithEscrow h b]; ring
  | emitEventA actor cell topic data =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, emitStep]; ring
      · rw [if_neg hlive] at h
        exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel nonceField cell (.int n)) b + escrowHeldAsset (writeField s.kernel nonceField cell (.int n)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel nonceField cell (.int n) b,
          show escrowHeldAsset (writeField s.kernel nonceField cell (.int n)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | setPermissionsA actor cell p =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel permsField cell (.int p)) b + escrowHeldAsset (writeField s.kernel permsField cell (.int p)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel permsField cell (.int p) b,
          show escrowHeldAsset (writeField s.kernel permsField cell (.int p)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | setVKA actor cell vk =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel vkField cell (.int vk)) b + escrowHeldAsset (writeField s.kernel vkField cell (.int vk)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel vkField cell (.int vk) b,
          show escrowHeldAsset (writeField s.kernel vkField cell (.int vk)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | introduceA intro rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegateAtten at h
      cases hd : recKDelegateAtten s.kernel del rec t keep with
      | none => reject_none h hd
      | some k' =>
          commit_subst h hd
          unfold recKDelegateAtten at hd
          gate_peel hd with bal_neutral
  | attenuateA actor idx keep =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h
      simp only [attenuateStepA, recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
  | dropRefA holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, recKRevokeTarget]; ring
  | revokeDelegationA holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset, recKRevokeTarget]; ring
  | validateHandoffA intro rec t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCDelegate at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; simp only [Option.some.injEq] at h; subst h
          unfold recKDelegate at hd
          by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | exerciseA actor t inner =>
      -- the hold-gate is bal-neutral (the c-list is read, not edited); the move is whatever `inner`
      -- moves, read off the mutual `execInnerA_ledger_per_asset` (the per-asset sum of inner deltas).
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      cases hg : exerciseStepA s actor t with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hg] at h
          obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
          -- `s1 = { s with log := … }` ⇒ `s1.kernel = s.kernel`: the move is exactly the inner sum.
          have hinner := execInnerA_ledger_per_asset s1 s' inner b h
          rw [hinner, hs1]
  | createCellA actor newCell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      -- combined = recTotalAsset (escrows unchanged by the fresh-cell insert) + neutral recTotalAsset.
      have hesc : escrowHeldAsset s'.kernel b = escrowHeldAsset s.kernel b := by
        obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
        subst hs'; rfl
      unfold recTotalAssetWithEscrow
      rw [hesc, createCellChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: born-EMPTY cell + balance-orthogonal field/caveat install ⇒ COMBINED measure fixed.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createCellFromFactoryChainA_neutralWithEscrow b (by simpa only [execFullA] using h)]; ring
  | spawnA actor child target =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      have hesc : escrowHeldAsset s'.kernel b = escrowHeldAsset s.kernel b := by
        obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
        subst hs'
        obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
      unfold recTotalAssetWithEscrow
      rw [hesc, spawnChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | bridgeMintA actor cell a value =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + _
          rw [show escrowHeldAsset k' b = escrowHeldAsset s.kernel b from by
                rw [show k' = { s.kernel with bal := recBalCredit s.kernel.bal cell a value } from by
                      unfold recKMintAsset at hm; split at hm
                      · simpa only [Option.some.injEq] using hm.symm
                      · exact absurd hm (by simp)]; rfl,
              recKMintAsset_delta s.kernel k' actor cell a value hm b]; ring
  -- §MA-escrow: the holding-store legs are COMBINED-conserving (combined delta `0`); notes are bal-NEUTRAL.
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createEscrowChainA_combined_neutral b h, add_zero]
  | releaseEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [releaseEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | refundEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [refundEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createEscrowChainA_combined_neutral b h, add_zero]
  -- fulfill = the per-asset escrow REFUND (stake → obligor/creator): combined-conserving.
  | fulfillObligationA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [refundEscrowKAsset_conserves_combined_per_asset b hk]; ring
  -- slash = the per-asset escrow RELEASE (stake → beneficiary/recipient): combined-conserving.
  | slashObligationA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [releaseEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | noteSpendA nf actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          -- noteSpend grows ONLY `nullifiers` — `bal` and `escrows` fixed.
          show recTotalAsset k' b + escrowHeldAsset k' b = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
          rw [show k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } from by
                unfold noteSpendNullifier at hk; split at hk
                · exact absurd hk (by simp)
                · simpa only [Option.some.injEq] using hk.symm]
          simp only [recTotalAsset, escrowHeldAsset]; ring
  | noteCreateA cm actor =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h
      -- noteCreate grows ONLY `commitments` — `bal` and `escrows` fixed.
      simp only [noteCreateChainA, noteCreateCommitment, recTotalAssetWithEscrow, recTotalAsset,
                 escrowHeldAsset]; ring
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      -- WAVE 4 HONESTY: under the §8 hiding portal the lock is the per-asset escrow (combined `0`).
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createCommittedEscrowChainA_combined_neutral b h, add_zero]
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [releaseEscrowKAsset_conserves_combined_per_asset b hk]; ring
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAssetWithEscrow k' b = _ + 0
          rw [refundEscrowKAsset_conserves_combined_per_asset b hk]; ring
  -- §MA-bridge: lock/cancel are COMBINED-conserving (combined delta `0`); finalize is the disclosed
  -- OUTFLOW (combined DROPS by `-amount` at the disclosed asset — the value LEFT for the other chain).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [bridgeLockChainA_combined_neutral b h, add_zero]
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [bridgeFinalizeChainA_burns_combined b h]
      by_cases hba : b = asset <;> simp only [hba, if_true, if_false] <;> ring
  | bridgeCancelA id actor =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [bridgeCancelChainA_combined_neutral b h, add_zero]
  -- §MA-seal (Wave-3 DE-SHADOW): seal/unseal/createSealPair MOVE capabilities (edit `caps`/`sealedBoxes`)
  -- — `bal` AND `escrows` fixed, so the COMBINED measure is UNCHANGED for EVERY asset (balance-NEUTRAL),
  -- read off the chained balNeutral lemmas (exactly as the swiss/queue arms).
  | sealA pid actor payload =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            sealChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | unsealA pid actor recipient =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            unsealChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            createSealPairChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | makeSovereignA actor cell =>
      -- FILL #133: the value-REBIND (whole-record drop) is bal-NEUTRAL on the per-asset ledger —
      -- `recTotalAsset`/`escrowHeldAsset` read `bal`/`escrows`, both fixed by the `cell`-only rebind.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'
      show recTotalAsset (makeSovereignKernel s.kernel cell) b + escrowHeldAsset (makeSovereignKernel s.kernel cell) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [makeSovereignKernel_recTotalAsset s.kernel cell b,
          show escrowHeldAsset (makeSovereignKernel s.kernel cell) b = escrowHeldAsset s.kernel b from rfl]; ring
  | refusalA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel refusalField cell (.int 1)) b + escrowHeldAsset (writeField s.kernel refusalField cell (.int 1)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel refusalField cell (.int 1) b,
          show escrowHeldAsset (writeField s.kernel refusalField cell (.int 1)) b = escrowHeldAsset s.kernel b from rfl]; ring
  | receiptArchiveA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel lifecycleField cell (.int 1)) b + escrowHeldAsset (writeField s.kernel lifecycleField cell (.int 1)) b
         = recTotalAsset s.kernel b + escrowHeldAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel lifecycleField cell (.int 1) b,
          show escrowHeldAsset (writeField s.kernel lifecycleField cell (.int 1)) b = escrowHeldAsset s.kernel b from rfl]; ring
  -- §MA-queue: each queue effect is balance-NEUTRAL — read the COMBINED measure off the chained
  -- balNeutral lemma (`recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b`), and
  -- `ledgerDeltaAsset = 0`. The FIFO/capacity/owner gates live in the kernel transition; here the move
  -- is `+0` at every asset (queues hold messages, not balance).
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            queueAllocateChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            queueEnqueueChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | queueDequeueA id actor cell depId deposit =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            queueDequeueChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            queueResizeChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  -- §MA-queue-batch (WAVE 4): the atomic batch / pipeline step / pipelined-send are all combined-NEUTRAL
  -- (read off `queueAtomicTxA_balNeutral` / `queuePipelineStepA_balNeutral`; pipelinedSend leaves the
  -- kernel UNCHANGED — only a clock row), and `ledgerDeltaAsset = 0`.
  | queueAtomicTxA actor ops =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            queueAtomicTxA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            queuePipelineStepA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | pipelinedSendA actor =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h; simp only [recTotalAssetWithEscrow]; ring
  -- §MA-swiss: each swiss-table effect is balance-NEUTRAL (moves references, not balance) ⇒ `+0`.
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            swissExportChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            swissEnlivenChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            swissHandoffChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  | swissDropA sw actor exporter =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            swissDropChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring
  -- §MA-lifecycle (Wave-3): each lifecycle/refresh effect is balance-NEUTRAL (edits a side-table, not
  -- `bal`/`escrows`) — read the COMBINED measure off the chained balNeutral lemma, `ledgerDeltaAsset = 0`.
  | cellSealA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from by
            obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'; rfl]; ring
  | cellUnsealA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from by
            obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'; rfl]; ring
  | cellDestroyA actor cell ch =>
      -- destroy sets `lifecycle` AND `deathCert`; both side-tables ⇒ `bal`/`escrows` fixed ⇒ rfl-neutral.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from by
            obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'; rfl]; ring
  | refreshDelegationA actor child =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b from
            refreshDelegationChainA_balNeutral h b]
      simp only [recTotalAssetWithEscrow]; ring

/-- **`execInnerA_ledger_per_asset` — the inner-fold conservation an `exerciseA` reads (PROVED).** A
committed `execInnerA` (the inner-effect fold an exercise recurses through) moves the COMBINED per-asset
measure by exactly the SUM of the inner effects' deltas — the per-asset analog of
`execFullTurnA_ledger_per_asset`, re-founded MUTUALLY with `execFullA_ledger_per_asset` so the exercise
arm above can close (each inner element's per-action delta comes from the mutual `execFullA` case). -/
theorem execInnerA_ledger_per_asset (s s' : RecChainedState) (inner : List FullActionA) (b : AssetId)
    (h : execInnerA s inner = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b + (inner.map (fun fa => ledgerDeltaAsset fa b)).sum := by
  cases inner with
  | nil =>
      simp only [execInnerA, Option.some.injEq] at h; subst h; simp
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead := execFullA_ledger_per_asset s s1 a b ha
          have htail := execInnerA_ledger_per_asset s1 s' rest b h
          rw [htail, hhead]
          simp only [List.map_cons, List.sum_cons]; ring
end

/-- **The per-asset full turn executor.** A transaction of `FullActionA`s, all-or-nothing. -/
def execFullTurnA (s : RecChainedState) : List FullActionA → Option RecChainedState
  | []        => some s
  | a :: rest =>
    match execFullA s a with
    | some s' => execFullTurnA s' rest
    | none    => none

/-- The net per-asset ledger delta of a turn, for asset `b`: the SUM of the per-action deltas. -/
def turnLedgerDeltaAsset (tt : List FullActionA) (b : AssetId) : ℤ :=
  (tt.map (fun fa => ledgerDeltaAsset fa b)).sum

/-- **`execFullTurnA_ledger_per_asset` — PROVED (the transaction COMBINED conservation vector).** A
committed per-asset full-turn moves the COMBINED measure `recTotalAssetWithEscrow b` by exactly the net
of all per-action deltas in asset `b`, for EVERY asset `b`. Proved by induction on the turn, reusing
`execFullA_ledger_per_asset`. The asset-indexed analog of `execFullTurn_ledger`. -/
theorem execFullTurnA_ledger_per_asset :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId), execFullTurnA s tt = some s' →
      recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + turnLedgerDeltaAsset tt b
  | s, s', [], b, h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; simp [turnLedgerDeltaAsset]
  | s, s', a :: rest, b, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead : recTotalAssetWithEscrow s1.kernel b = recTotalAssetWithEscrow s.kernel b + ledgerDeltaAsset a b :=
            execFullA_ledger_per_asset s s1 a b ha
          have htail : recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s1.kernel b + turnLedgerDeltaAsset rest b :=
            execFullTurnA_ledger_per_asset s1 s' rest b h
          rw [htail, hhead]
          simp only [turnLedgerDeltaAsset, List.map_cons, List.sum_cons]; ring

/-- **`execFullTurnA_conserves_per_asset` — PROVED.** A committed per-asset full-turn whose net
ledger delta is `0` *in asset `b`* preserves asset `b`'s total supply. Applied with `∀ b, … = 0`
this gives FULL per-asset conservation: a transfer/authority-only turn (or one whose per-asset
mint/burn nets out in EACH asset) conserves EVERY asset class. The `CONSERVATION_VECTOR` at the
transaction level. -/
theorem execFullTurnA_conserves_per_asset (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId)
    (h : execFullTurnA s tt = some s') (hzero : turnLedgerDeltaAsset tt b = 0) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  rw [execFullTurnA_ledger_per_asset s s' tt b h, hzero, add_zero]

/-! ## §MB — `execFullTurnA_append` + the per-asset PER-NODE attestation carrier.

The forest lift in `Exec/FullForest.lean` rests on the same `execTurn_append` shape `TurnForest.lean`
uses for the narrow executor — here re-founded for the per-asset `execFullTurnA`. We then build the
per-asset analog of `fullActionInv` (`fullActionInvA`) whose **Ledger** conjunct is the full per-asset
VECTOR (`∀ b, recTotalAsset … = … + ledgerDeltaAsset fa b`, never one aggregate scalar — the FILL-1
no-laundering carrier), with ChainLink/ObsAdvance/KindObligation reused per-kind (these are
asset-orthogonal: they edit the log / `caps`, not the `bal` ledger). `execFullTurnA_each_attests`
then threads the per-node witness along the all-or-nothing fold, so the forest's per-node
attestation (`FullForest.execFullForestA_each_attests`) lifts straight off the bridge. -/

/-- **`execFullTurnA_append` — PROVED.** Running a concatenated per-asset turn equals running the
prefix and, on success, the suffix (the `execTurn_append` shape for `execFullTurnA`). The
associativity the forest pre-order flattening rests on. Mirrors `TurnForest.execTurn_append` verbatim
with `recCexec`→`execFullA`, induction on `xs`. -/
theorem execFullTurnA_append (s : RecChainedState) (xs ys : List FullActionA) :
    execFullTurnA s (xs ++ ys)
      = (match execFullTurnA s xs with
         | some s' => execFullTurnA s' ys
         | none    => none) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a rest ih =>
      show execFullTurnA s (a :: (rest ++ ys))
          = (match execFullTurnA s (a :: rest) with
             | some s' => execFullTurnA s' ys
             | none    => none)
      rw [show execFullTurnA s (a :: (rest ++ ys))
            = (match execFullA s a with
               | some s1 => execFullTurnA s1 (rest ++ ys)
               | none    => none) from rfl,
          show execFullTurnA s (a :: rest)
            = (match execFullA s a with
               | some s1 => execFullTurnA s1 rest
               | none    => none) from rfl]
      cases execFullA s a with
      | none    => rfl
      | some s1 => exact ih s1

/-- The receipt a committed `FullActionA` appends (newest-first): a per-asset transfer appends its
`turn`; authority appends its `authReceipt`; mint/burn append a self-`Turn` carrying the disclosed
per-asset supply delta. The per-asset analog of `fullReceipt`. -/
def fullReceiptA : FullActionA → Turn
  | .balanceA t _          => t
  | .delegate del _ _      => authReceipt del
  | .revoke holder _       => authReceipt holder
  | .mintA actor cell _ amt  => { actor := actor, src := cell, dst := cell, amt := amt }
  | .burnA actor cell _ amt  => { actor := actor, src := cell, dst := cell, amt := -amt }
  -- §MA-state: every pure-state effect appends a balance-`0` self-`Turn` on the target `cell` (the
  -- metadata clock row that `stateStep`/`emitStep` thread; no balance delta).
  | .setFieldA actor cell _ _   => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .emitEventA actor cell _ _  => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .incrementNonceA actor cell _ => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .setPermissionsA actor cell _ => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .setVKA actor cell _        => { actor := actor, src := cell, dst := cell, amt := 0 }
  -- §MA-auth: each authority effect appends exactly its `authReceipt` (a self-`Turn`, amount `0`).
  | .introduceA intro _ _       => authReceipt intro
  | .delegateAttenA del _ _ _   => authReceipt del
  | .attenuateA actor _ _       => authReceipt actor
  | .dropRefA holder _          => authReceipt holder
  | .revokeDelegationA holder _ => authReceipt holder
  | .validateHandoffA intro _ _ => authReceipt intro
  | .exerciseA actor _ _        => authReceipt actor
  -- §MA-supply: createCell/spawn append the fresh cell's (balance-`0`) creation row; bridgeMint
  -- appends a self-`Turn` carrying the disclosed `+value`.
  | .createCellA actor newCell  => { actor := actor, src := newCell, dst := newCell, amt := 0 }
  | .createCellFromFactoryA actor newCell _ => { actor := actor, src := newCell, dst := newCell, amt := 0 }
  | .spawnA actor child _       => { actor := actor, src := child, dst := child, amt := 0 }
  | .bridgeMintA actor cell _ value => { actor := actor, src := cell, dst := cell, amt := value }
  -- §MA-escrow: every escrow/obligation/committed/note effect appends a self-`Turn` on the `actor`
  -- (the metadata clock row; the parked amount/asset live in the off-ledger record/SET, not the receipt).
  | .createEscrowA _ actor _ _ _ _   => escrowReceiptA actor
  | .releaseEscrowA _ actor          => escrowReceiptA actor
  | .refundEscrowA _ actor           => escrowReceiptA actor
  | .createObligationA _ actor _ _ _ _ => escrowReceiptA actor
  | .fulfillObligationA _ actor      => escrowReceiptA actor
  | .slashObligationA _ actor        => escrowReceiptA actor
  | .noteSpendA _ actor              => escrowReceiptA actor
  | .noteCreateA _ actor             => escrowReceiptA actor
  | .createCommittedEscrowA _ actor _ _ _ _ _ => escrowReceiptA actor
  | .releaseCommittedEscrowA _ actor => escrowReceiptA actor
  | .refundCommittedEscrowA _ actor  => escrowReceiptA actor
  -- §MA-bridge: each bridge leg appends a self-`Turn` on the `actor` (the metadata clock row; the
  -- bridged amount/asset live in the off-ledger record / the disclosed action params, not the receipt).
  | .bridgeLockA _ actor _ _ _ _     => escrowReceiptA actor
  | .bridgeFinalizeA _ actor _ _     => escrowReceiptA actor
  | .bridgeCancelA _ actor           => escrowReceiptA actor
  -- §MA-seal (Wave-3 DE-SHADOW): seal appends a self-`Turn` on the sealing `actor`; unseal on the
  -- `recipient` (the cap's new holder); createSealPair on the `sealerHolder` — matching the chained-step
  -- receipts. The §8 crypto / box live in the portal/side-table, not the receipt.
  | .sealA _ actor _                 => { actor := actor, src := actor, dst := actor, amt := 0 }
  | .unsealA _ actor recipient       => { actor := actor, src := recipient, dst := recipient, amt := 0 }
  | .createSealPairA _ actor sealerHolder _ => { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 }
  | .makeSovereignA actor cell       => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .refusalA actor cell             => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .receiptArchiveA actor cell      => { actor := actor, src := cell, dst := cell, amt := 0 }
  -- §MA-queue: allocate/resize append a balance-`0` self-`Turn` on the queue `cell`; enqueue/dequeue
  -- append the REFUNDABLE DEPOSIT move (Wave-8): enqueue is `actor →(deposit)→ cell` (the deposit
  -- parked from the sender into the queue), dequeue is `cell →(deposit)→ actor` (the refund to the
  -- dequeuer). The message lives in the off-ledger FIFO buffer, not the receipt.
  | .queueAllocateA _ actor cell _   => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .queueEnqueueA _ _ actor cell _ _ deposit => { actor := actor, src := actor, dst := cell, amt := deposit }
  | .queueDequeueA _ actor cell _ deposit     => { actor := actor, src := cell, dst := actor, amt := deposit }
  | .queueResizeA _ _ actor cell     => { actor := actor, src := cell, dst := cell, amt := 0 }
  -- §MA-queue-batch (WAVE 4): the atomic batch appends a batch-commit row on the `actor` (the per-op
  -- rows landed inside the fold); the pipeline step a routing row on the `owner` (the source dequeuer);
  -- pipelinedSend a clock row on the `actor` (the apply-time neutral marker).
  | .queueAtomicTxA actor _          => escrowReceiptA actor
  | .queuePipelineStepA _ owner _ _  => { actor := owner, src := owner, dst := owner, amt := 0 }
  | .pipelinedSendA actor            => escrowReceiptA actor
  -- §MA-swiss: each swiss-table effect appends a balance-`0` self-`Turn` on the exporting `exporter`
  -- cell (the metadata clock row; the swiss entry lives in the off-ledger registry, not the receipt).
  | .exportSturdyRefA _ actor exporter _ _ => { actor := actor, src := exporter, dst := exporter, amt := 0 }
  | .enlivenRefA _ actor exporter _          => { actor := actor, src := exporter, dst := exporter, amt := 0 }
  | .swissHandoffA _ _ introducer exporter   => { actor := introducer, src := exporter, dst := exporter, amt := 0 }
  | .swissDropA _ actor exporter             => { actor := actor, src := exporter, dst := exporter, amt := 0 }
  -- §MA-lifecycle (Wave-3): seal/unseal/destroy append a self-`Turn` on the `cell`; refresh on the
  -- `child` — matching the chained-step receipts (the lifecycle/snapshot lives in the side-table).
  | .cellSealA actor cell            => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .cellUnsealA actor cell          => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .cellDestroyA actor cell _       => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .refreshDelegationA actor child  => { actor := actor, src := child, dst := child, amt := 0 }

/-- **`execFullA_chainlinkExact` — PROVED (the one-row chainlink for every NON-recursive kind).** A
committed NON-exercise, NON-atomic-batch `FullActionA` extends the receipt chain by EXACTLY its
`fullReceiptA`, newest-first, with no fork or rewrite. `exerciseA` is excluded (`hne`) because it
RECURSES, and `queueAtomicTxA` (`hnb`) because it FOLDS a BATCH — both grow the log by their own receipt
PLUS the sub-effects' rows (the honest append-only suffix, captured by `execFullA_chainlink` below). The
per-action generalization across the per-asset op-set (asset-orthogonal: it touches only the `log`). -/
theorem execFullA_chainlinkExact (s s' : RecChainedState) (fa : FullActionA)
    (hne : ∀ a t inner, fa ≠ .exerciseA a t inner)
    (hnb : ∀ actor ops, fa ≠ .queueAtomicTxA actor ops)
    (h : execFullA s fa = some s') : s'.log = fullReceiptA fa :: s.log := by
  cases fa with
  | exerciseA a t inner => exact absurd rfl (hne a t inner)
  | queueAtomicTxA actor ops => exact absurd rfl (hnb actor ops)
  | balanceA t a =>
      simp only [execFullA, recCexecAsset, fullReceiptA] at h ⊢
      cases hx : recKExecAsset s.kernel t a with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | delegate del rec t =>
      simp only [execFullA, recCDelegate, fullReceiptA] at h ⊢
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | revoke holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset, fullReceiptA] at h ⊢
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset, fullReceiptA] at h ⊢
      cases hb : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' => rw [hb] at h; simp only [Option.some.injEq] at h; subst h; rfl
  -- §MA-state: each pure-state effect appends exactly the metadata clock row (`stateStep`/`emitStep`).
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: `setFieldA` runs the caveat-gated write; a committed guarded write IS a
      -- committed `stateStep` (`stateStepGuarded_eq`), so the chain-row factoring is identical.
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h); subst hs'; rfl
  | emitEventA actor cell topic data =>
      simp only [execFullA, fullReceiptA] at h ⊢
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h
        simp only [Option.some.injEq] at h
        subst h; rfl
      · rw [if_neg hlive] at h
        exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setPermissionsA actor cell p =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setVKA actor cell vk =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §MA-auth: each authority effect appends exactly its `authReceipt` (the metadata clock row).
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate, fullReceiptA] at h ⊢
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten, fullReceiptA] at h ⊢
      cases hd : recKDelegateAtten s.kernel del rec t keep with
      | none => reject_none h hd
      | some k' => commit_subst h hd; rfl
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA, fullReceiptA, Option.some.injEq] at h ⊢
      subst h; rfl
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate, fullReceiptA] at h ⊢
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; subst h; rfl
  -- §MA-supply: createCell/spawn append the fresh cell's creation row; bridgeMint the disclosed credit.
  | createCellA actor newCell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      exact createCellChainA_chainlink h
  | createCellFromFactoryA actor newCell vk =>
      simp only [execFullA, fullReceiptA] at h ⊢
      exact createCellFromFactoryChainA_chainlink h
  | spawnA actor child target =>
      simp only [execFullA, fullReceiptA] at h ⊢
      exact spawnChainA_chainlink h
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset, fullReceiptA] at h ⊢
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; subst h; rfl
  -- §MA-escrow: each escrow/note effect appends exactly its `escrowReceiptA` (the metadata clock row).
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA, fullReceiptA] at h ⊢
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | releaseEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA, fullReceiptA] at h ⊢
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | refundEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA, fullReceiptA] at h ⊢
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA, fullReceiptA] at h ⊢
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | fulfillObligationA id actor =>
      simp only [execFullA, refundEscrowChainA, fullReceiptA] at h ⊢
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | slashObligationA id actor =>
      simp only [execFullA, releaseEscrowChainA, fullReceiptA] at h ⊢
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA, fullReceiptA] at h ⊢
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, fullReceiptA, Option.some.injEq] at h ⊢
      subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      -- WAVE 4 HONESTY: through the §8 hiding-portal gate, then the per-asset escrow lock.
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA, fullReceiptA] at h ⊢
      by_cases hp : hidingProof = true
      · rw [if_pos hp] at h
        cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA, fullReceiptA] at h ⊢
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA, fullReceiptA] at h ⊢
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  -- §MA-bridge: each bridge leg appends exactly its `escrowReceiptA` (the metadata clock row).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA, fullReceiptA] at h ⊢
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA, fullReceiptA] at h ⊢
      by_cases hg : bridgeAuthOK s.kernel id actor = true
      · rw [if_pos hg] at h
        cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hg] at h; exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA, fullReceiptA] at h ⊢
      by_cases hg : bridgeAuthOK s.kernel id actor = true
      · rw [if_pos hg] at h
        cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hg] at h; exact absurd h (by simp)
  -- §MA-seal (Wave-3 DE-SHADOW): each de-shadowed seal step appends exactly its metadata clock row
  -- (read off the chained-step factoring lemma, which gives the full post-state incl. the log).
  | sealA pid actor payload =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := sealChainA_factors h; subst hs'; rfl
  | unsealA pid actor recipient =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors h; subst hs'; rfl
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := createSealPairChainA_factors h; subst hs'; rfl
  | makeSovereignA actor cell =>
      -- FILL #133: the rebind appends EXACTLY the same self-`Turn` clock row (`makeSovereignStep`).
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; rfl
  | refusalA actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | receiptArchiveA actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §MA-queue: each queue chained step appends EXACTLY its `fullReceiptA` row (the chainlink lemma).
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact queueAllocateChainA_chainlink h
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact queueEnqueueChainA_chainlink h
  | queueDequeueA id actor cell depId deposit =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact queueDequeueChainA_chainlink h
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact queueResizeChainA_chainlink h
  -- §MA-queue-batch (WAVE 4): the pipeline step appends the `owner` routing row (the chainlink lemma);
  -- pipelinedSend the `actor` clock row. (queueAtomicTxA is excluded — `hnb` — it folds a BATCH.)
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact queuePipelineStepA_chainlink h
  | pipelinedSendA actor =>
      simp only [execFullA, fullReceiptA, Option.some.injEq] at h ⊢; subst h; rfl
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact swissExportChainA_chainlink h
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact swissEnlivenChainA_chainlink h
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact swissHandoffChainA_chainlink h
  | swissDropA sw actor exporter =>
      simp only [execFullA, fullReceiptA] at h ⊢; exact swissDropChainA_chainlink h
  -- §MA-lifecycle (Wave-3): each lifecycle/refresh step appends exactly its self-`Turn` clock row
  -- (read off the chained-step factoring lemma, which gives the full post-state incl. the log).
  | cellSealA actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'; rfl
  | cellUnsealA actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'; rfl
  | cellDestroyA actor cell ch =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'; rfl
  | refreshDelegationA actor child =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; rfl

mutual
/-- **`execFullA_log_suffix` / `execInnerA_log_suffix` — PROVED (the append-only audit chain).** A
committed `FullActionA` (resp. the inner-effect fold) only EXTENDS the log: the pre-log is a SUFFIX of
the post-log. Mutual because `exerciseA` recurses through `execInnerA`. NON-recursive kinds extend by
exactly one row (`execFullA_chainlinkExact`); exercise extends by its own receipt PLUS the inner
fold's rows. -/
theorem execFullA_log_suffix (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.log <:+ s'.log := by
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨a, t, inner, rfl⟩ := hex
    -- exercise: the hold-gate prepends `authReceipt a`, then the inner fold extends further.
    simp only [execFullA] at h
    cases hg : exerciseStepA s a t with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some s1 =>
        rw [hg] at h
        obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
        have hstep : s.log <:+ s1.log := by rw [hs1]; exact List.suffix_cons _ _
        exact hstep.trans (execInnerA_log_suffix s1 s' inner h)
  · by_cases hbatch : ∃ actor ops, fa = .queueAtomicTxA actor ops
    · -- §MA-queue-batch (WAVE 4): the atomic batch folds its sub-ops then prepends the commit row —
      -- append-only (the fold's suffix-extension carried by `queueAtomicTxA_chainlink`).
      obtain ⟨actor, ops, rfl⟩ := hbatch
      simp only [execFullA] at h
      exact (queueAtomicTxA_chainlink h).1
    · -- non-exercise, non-batch: extend by exactly one row.
      rw [execFullA_chainlinkExact s s' fa (fun a t inner heq => hex ⟨a, t, inner, heq⟩)
            (fun actor ops heq => hbatch ⟨actor, ops, heq⟩) h]
      exact List.suffix_cons _ _

theorem execInnerA_log_suffix (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') : s.log <:+ s'.log := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact List.suffix_refl _
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact (execFullA_log_suffix s s1 a ha).trans (execInnerA_log_suffix s1 s' rest h)
end

/-- **`execFullA_chainlink` — PROVED (the honest append-only chainlink across the WHOLE op-set).** A
committed `FullActionA` extends the receipt chain (the pre-log is a SUFFIX of the post-log) AND records
its own `fullReceiptA` row in the post-log. For NON-recursive kinds this is the exact one-row extension
(`execFullA_chainlinkExact`); for `exerciseA` the own-receipt is followed by the inner effects' rows —
still append-only, still recording the exercise receipt. No fork, no rewrite. -/
theorem execFullA_chainlink (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.log <:+ s'.log ∧ fullReceiptA fa ∈ s'.log := by
  refine ⟨execFullA_log_suffix s s' fa h, ?_⟩
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨a, t, inner, rfl⟩ := hex
    -- exercise: `authReceipt a = fullReceiptA (exerciseA …)` is appended by the hold-gate, then the
    -- inner fold (a suffix-extension) keeps it present.
    simp only [execFullA] at h
    cases hg : exerciseStepA s a t with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some s1 =>
        rw [hg] at h
        obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
        have hmem : fullReceiptA (.exerciseA a t inner) ∈ s1.log := by
          rw [hs1]; exact List.mem_cons_self
        exact (execInnerA_log_suffix s1 s' inner h).mem hmem
  · by_cases hbatch : ∃ actor ops, fa = .queueAtomicTxA actor ops
    · -- §MA-queue-batch (WAVE 4): the batch-commit row IS `fullReceiptA (queueAtomicTxA …)`, recorded.
      obtain ⟨actor, ops, rfl⟩ := hbatch
      simp only [execFullA, fullReceiptA] at h ⊢
      exact (queueAtomicTxA_chainlink h).2
    · rw [execFullA_chainlinkExact s s' fa (fun a t inner heq => hex ⟨a, t, inner, heq⟩)
            (fun actor ops heq => hbatch ⟨actor, ops, heq⟩) h]
      exact List.mem_cons_self

/-- **`execFullA_obsadvance` — PROVED.** A committed `FullActionA` STRICTLY grows the chain (≥ one row),
so a replayed action (which would re-append its receipt) is detectable. Non-recursive kinds grow by
exactly one row; a committed exercise grows by `1 + |inner|`. -/
theorem execFullA_obsadvance (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.log.length < s'.log.length := by
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨a, t, inner, rfl⟩ := hex
    simp only [execFullA] at h
    cases hg : exerciseStepA s a t with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some s1 =>
        rw [hg] at h
        obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
        have h1 : s.log.length < s1.log.length := by
          rw [hs1, List.length_cons]; exact Nat.lt_succ_self _
        exact Nat.lt_of_lt_of_le h1 (execInnerA_log_suffix s1 s' inner h).length_le
  · by_cases hbatch : ∃ actor ops, fa = .queueAtomicTxA actor ops
    · -- §MA-queue-batch (WAVE 4): the batch grows by ≥ 1 row (the commit row over the fold's suffix).
      obtain ⟨actor, ops, rfl⟩ := hbatch
      simp only [execFullA] at h
      exact queueAtomicTxA_obsadvance h
    · rw [execFullA_chainlinkExact s s' fa (fun a t inner heq => hex ⟨a, t, inner, heq⟩)
            (fun actor ops heq => hbatch ⟨actor, ops, heq⟩) h, List.length_cons]
      exact Nat.lt_succ_self _

/-- **Per-asset balance authorized — PROVED.** A committed per-asset transfer was authorized
(`authorizedB` at the pre-state), via `recKExecAsset_authorized`. -/
theorem execFullA_balance_authorized (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execFullA s (.balanceA t a) = some s') : authorizedB s.kernel.caps t = true := by
  simp only [execFullA, recCexecAsset] at h
  cases hx : recKExecAsset s.kernel t a with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some k' => exact recKExecAsset_authorized s.kernel k' t a hx

/-- **Per-asset delegation grounds — PROVED.** A committed per-asset-turn delegation HOLDS the
Granovetter source edge `delegator ⟶ ⟨t,()⟩` on `execGraph` (REUSES the same `recCDelegate`/
`recKDelegate_grounds` the scalar executor does). -/
theorem execFullA_delegate_grounds (s s' : RecChainedState) (del rec t : CellId)
    (h : execFullA s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' del rec t hd

/-- **Per-asset delegation IS `addEdge` — PROVED.** REUSES `recKDelegate_execGraph`. -/
theorem execFullA_delegate_addEdge (s s' : RecChainedState) (del rec t : CellId)
    (h : execFullA s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps del rec t hg
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **Per-asset delegation grants the copied held cap — PROVED.** The concrete authority move copies
the delegator's held witness cap; the abstract graph still sees exactly `addEdge`. -/
theorem execFullA_delegate_grants_held_cap (s s' : RecChainedState) (del rec t : CellId)
    (h : execFullA s (.delegate del rec t) = some s') :
    heldCapTo s.kernel.caps del t ∈ s'.kernel.caps rec := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h
      simp only [Option.some.injEq] at h
      subst h
      exact recKDelegate_grants s.kernel k' del rec t hd

/-- **Per-asset revocation IS `removeEdge` — PROVED.** REUSES `recKRevokeTarget_execGraph`. -/
theorem execFullA_revoke_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.revoke holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **Per-asset mint authorized — PROVED.** A committed per-asset mint implies the privileged mint
authority (`recKMintAsset_authorized`). -/
theorem execFullA_mintA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.mintA actor cell a amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_authorized s.kernel k' actor cell a amt hm

/-- **`recKBurnAsset_authorized` — PROVED.** A committed per-asset burn implies the privileged mint
authority (the per-asset analog of `recKBurn_authorized`). -/
theorem recKBurnAsset_authorized (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKBurnAsset k actor cell a amt = some k') :
    mintAuthorizedB k.caps actor cell = true := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Per-asset burn authorized — PROVED.** A committed per-asset burn implies the privileged mint
authority over `cell`. -/
theorem execFullA_burnA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.burnA actor cell a amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFullA, recCBurnAsset] at h
  cases hb : recKBurnAsset s.kernel actor cell a amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' => exact recKBurnAsset_authorized s.kernel k' actor cell a amt hb

/-! ### §MA-supply authority obligations — `bridgeMint` is PRIVILEGED supply (`mintAuthorizedB`), the
LOCAL gate independent of the §8 foreign-finality portal; `createCell`/`spawn` carry their privileged
creation authority + the freshness gate (proved earlier as `createCellChainA_authorized` /
`spawnChainA_authorized`). -/

/-- **`execFullA_bridgeMintA_authorized` — PROVED.** A committed per-asset bridge-mint implies the
privileged mint authority over `cell` (the LOCAL gate — the foreign finality is the §8 portal,
discharged outside Lean). REUSES `recKMintAsset_authorized`. -/
theorem execFullA_bridgeMintA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_authorized s.kernel k' actor cell a value hm

/-- **`execFullA_bridgeMintA_unauthorized_fails` — PROVED (fail-closed).** Without mint authority, no
bridge-mint commits (regardless of foreign finality). The confinement core. -/
theorem execFullA_bridgeMintA_unauthorized_fails (s : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (h : mintAuthorizedB s.kernel.caps actor cell = false) :
    execFullA s (.bridgeMintA actor cell a value) = none := by
  simp only [execFullA, recCMintAsset, recKMintAsset]
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **`execFullA_createCellA_neutral_per_asset` — THE ACCOUNT-GROWTH NEUTRALITY KEYSTONE (PROVED).** A
committed `createCellA` leaves `recTotalAsset` UNCHANGED for EVERY asset `b`. NON-VACUOUS: the index set
`accounts` genuinely GREW (`execFullA_createCellA_grows_accounts` — the new cell IS live afterward), yet
supply is conserved BECAUSE the fresh cell is born EMPTY (the `bal`-reset). This is the createCell
account-growth neutrality META-FILL C demands — the dregg1-faithful `balance == 0` creation as a
conservation-NEUTRAL move on the per-asset ledger. -/
theorem execFullA_createCellA_neutral_per_asset (s s' : RecChainedState) (actor newCell : CellId)
    (b : AssetId) (h : execFullA s (.createCellA actor newCell) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellChainA_neutral b (by simpa only [execFullA] using h)

/-- **`execFullA_createCellA_grows_accounts` — the GROWTH has teeth (PROVED).** After a committed
`createCellA`, the new cell IS a live account: `newCell ∈ s'.kernel.accounts`. Witnesses that the
neutrality keystone is NOT a no-op — the conserved-measure index set genuinely grew. -/
theorem execFullA_createCellA_grows_accounts (s s' : RecChainedState) (actor newCell : CellId)
    (h : execFullA s (.createCellA actor newCell) = some s') :
    newCell ∈ s'.kernel.accounts :=
  createCellChainA_grows_accounts (by simpa only [execFullA] using h)

/-- **`execFullA_spawnA_neutral_per_asset` — PROVED.** A committed `spawnA` (createCell born EMPTY + a
bal-orthogonal cap grant) is likewise conservation-NEUTRAL for EVERY asset. -/
theorem execFullA_spawnA_neutral_per_asset (s s' : RecChainedState) (actor child target : CellId)
    (b : AssetId) (h : execFullA s (.spawnA actor child target) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  spawnChainA_neutral b (by simpa only [execFullA] using h)

/-- **`execFullA_bridgeMintA_discloses_per_asset` — PROVED (the §8 portal disclosed delta).** A committed
`bridgeMintA actor cell a value` raises asset `a`'s supply by EXACTLY the disclosed `value` and leaves
EVERY OTHER asset literally UNCHANGED: `recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = a
then value else 0)`. The disclosed generative inflow (NOT a conservation claim) — the per-asset
no-cross-asset-laundering content at the bridge boundary. -/
theorem execFullA_bridgeMintA_discloses_per_asset (s s' : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (b : AssetId)
    (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = a then value else 0) := by
  -- bridgeMint reuses the per-asset mint kernel step (`recKMintAsset_delta`) over the BARE `bal` ledger.
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' =>
      rw [hm] at h; simp only [Option.some.injEq] at h; subst h
      exact recKMintAsset_delta s.kernel k' actor cell a value hm b

/-! ### §MA-state authority obligations — the 4 field-writing pure-state effects WERE authorized;
`emitEventA` is authority-FREE (dregg1 `apply_emit_event` runs NO cap check). The field-writing
effects reuse `EffectsState.state_authorized` (the `stateAuthB` gate over the target cell — the
faithful model of dregg1's `check_cross_cell_permission`/ownership), so the gate is REAL, not
vacuous: an actor without authority over `cell` cannot commit a field write (see the fail-closed
`#eval`s in §13-state). -/

/-- **`setFieldA` authorized — PROVED.** A committed `setFieldA` implies the actor held authority over
`cell` (`stateAuthB` — the faithful model of dregg1's `SetState` cross-cell / ownership gate). -/
theorem execFullA_setFieldA_authorized (s s' : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) (h : execFullA s (.setFieldA actor cell f v) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  -- §SLOT-CAVEAT: peel the caveat gate first (`stateStepGuarded_eq`), then the authority gate.
  state_authorized (stateStepGuarded_eq (by simpa only [execFullA] using h))

/-- **`incrementNonceA` authorized — PROVED.** Implies the actor held authority over `cell` (the
`IncrementNonce` cross-cell / ownership gate). -/
theorem execFullA_incrementNonceA_authorized (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`setPermissionsA` authorized — PROVED.** Implies the actor held authority over `cell` (the
`SetPermissions` gate; dregg1 applies the permission write LAST off the ORIGINAL snapshot, so the
gate is evaluated against the PRE-state caps — exactly `stateAuthB s.kernel.caps`, the pre-state). -/
theorem execFullA_setPermissionsA_authorized (s s' : RecChainedState) (actor cell : CellId) (p : Int)
    (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`setVKA` authorized — PROVED.** Implies the actor held authority over `cell` (the
`SetVerificationKey` gate). -/
theorem execFullA_setVKA_authorized (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (h : execFullA s (.setVKA actor cell vk) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-! ### §MA-seal authority obligations — the 6 simple bal-neutral effects carry their REAL `stateAuthB`
authority gate (the faithful model of dregg1's sealer-cap / self-sovereign / `SetState` / archive
gate). NON-VACUOUS: an actor without authority over the written cell cannot commit (see the fail-closed
`#eval`s in §13-seal). The §8 crypto (AEAD / commitment) is the chain-layer portal, NOT an authority
claim. -/

/-- **`sealA` HOLDS the sealer cap — PROVED (Wave-3 DE-SHADOW).** A committed `seal` implies the actor
genuinely HELD the sealer cap for `pid` in its committed c-list (dregg1's `lookup_by_target`,
`apply.rs:2756`; `CapabilityNotHeld` otherwise). The faithful gate — NOT a generic `stateAuthB cell`. -/
theorem execFullA_sealA_authorized (s s' : RecChainedState) (pid : Nat) (actor : CellId) (payload : Cap)
    (h : execFullA s (.sealA pid actor payload) = some s') :
    (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true :=
  (sealChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`unsealA` HOLDS the unsealer cap — PROVED (Wave-3 DE-SHADOW).** Implies the actor genuinely HELD
the unsealer cap for `pid` (`apply.rs:2891`). The §8 AEAD decrypt verify is the chain-layer portal. -/
theorem execFullA_unsealA_authorized (s s' : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (h : execFullA s (.unsealA pid actor recipient) = some s') :
    (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true := by
  obtain ⟨_, _, hheld, _⟩ := unsealChainA_factors (by simpa only [execFullA] using h); exact hheld

/-- **`createSealPairA` authorized — PROVED.** Implies the actor held authority over the
`sealerHolder` cell (the writer of the pair). The §8 AEAD keypair is the portal. -/
theorem execFullA_createSealPairA_authorized (s s' : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId)
    (h : execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s') :
    stateAuthB s.kernel.caps actor sealerHolder = true :=
  (createSealPairChainA_factors (by simpa only [execFullA] using h)).1

/-- **`makeSovereignA` authorized — PROVED.** Implies the actor held authority over `cell` (dregg1's
self-sovereign gate: `cell == action_target` ⇒ the cell's own authority). FILL #133: the action is a
VALUE-REBIND (the readable state is dropped behind the §8 commitment), so the gate routes through
`makeSovereignStep_authorized`, not the generic `stateStep`. -/
theorem execFullA_makeSovereignA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.makeSovereignA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  makeSovereignStep_authorized (by simpa only [execFullA] using h)

/-- **`refusalA` authorized — PROVED.** Implies the actor held authority over `cell` (dregg1's
cross-cell `SetState` gate). Refusal NEVER mutates balance/caps/value — the move is the audit write. -/
theorem execFullA_refusalA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.refusalA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`receiptArchiveA` authorized — PROVED.** Implies the actor held authority over `cell` (dregg1's
checkpoint cell_id = action_target gate). The archive is a lifecycle/log write. -/
theorem execFullA_receiptArchiveA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.receiptArchiveA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-! ### §MA-queue authority obligations — the 4 ring-buffer FIFO queue effects carry their REAL
`stateAuthB actor cell` authority gate over the queue's representing cell (dregg1's writer-ACL / owner
gate, `apply.rs:3334,3433`). NON-VACUOUS: an actor without authority over the queue cell cannot commit
(witnessed by the fail-closed `#eval`s + `queueDequeueK_wrong_owner_rejects`). The FIFO ORDER + capacity
bound + emptiness gate are the SEPARATE kernel-level obligation (`qbuf_fifo_order` /
`queueEnqueueK_full_rejects` / `queueDequeueK_empty_rejects`). Every conjunct has teeth, NOT `True`. -/

/-- **`queueAllocateA` authorized — PROVED.** A committed allocate implies the actor held authority over
the queue's representing `cell`. -/
theorem execFullA_queueAllocateA_authorized (s s' : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (h : execFullA s (.queueAllocateA id actor cell cap) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  queueAllocateChainA_authorized (by simpa only [execFullA] using h)

/-- **`queueEnqueueA` authorized — PROVED.** A committed enqueue implies the actor held authority over
the queue `cell` (dregg1's writer-ACL gate). -/
theorem execFullA_queueEnqueueA_authorized (s s' : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
    (h : execFullA s (.queueEnqueueA id m actor cell depId dAsset deposit) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  queueEnqueueChainA_authorized (by simpa only [execFullA] using h)

/-- **`queueDequeueA` authorized — PROVED.** A committed dequeue implies the actor held authority over
the queue `cell` (AND was the kernel-level owner — the `queueDequeueK` `actor = owner` gate). -/
theorem execFullA_queueDequeueA_authorized (s s' : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (deposit : ℤ)
    (h : execFullA s (.queueDequeueA id actor cell depId deposit) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  queueDequeueChainA_authorized (by simpa only [execFullA] using h)

/-- **`queueResizeA` authorized — PROVED.** A committed resize implies the actor held authority over the
queue `cell`. -/
theorem execFullA_queueResizeA_authorized (s s' : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (h : execFullA s (.queueResizeA id newCap actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  queueResizeChainA_authorized (by simpa only [execFullA] using h)

/-! ### §MA-swiss authority obligations — the 4 CapTP swiss-table effects carry their REAL
`stateAuthB actor exporter` authority gate over the exporting/holding cell (dregg1's holder-of-the-cap /
introducer gate). The membership / non-amplification / refcount-GC gates are the SEPARATE kernel-level
obligation (`swissExportK_amplification_rejects` / `swissEnlivenK_absent_rejects` /
`swissDropK_gc_at_one`, in `RecordKernel`). Every conjunct has teeth, NOT `True`. -/

/-- **`exportSturdyRefA` authorized — PROVED.** A committed export implies the actor held authority over
the `exporter` cell (the holder of the cap). -/
theorem execFullA_exportSturdyRefA_authorized (s s' : RecChainedState) (sw : Nat)
    (actor exporter target : CellId) (rights : List Auth)
    (h : execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s') :
    stateAuthB s.kernel.caps actor exporter = true :=
  swissExportChainA_authorized (by simpa only [execFullA] using h)

/-- **`enlivenRefA` authorized — PROVED.** A committed enliven implies the actor held authority over the
`exporter` cell. -/
theorem execFullA_enlivenRefA_authorized (s s' : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    stateAuthB s.kernel.caps actor exporter = true :=
  swissEnlivenChainA_authorized (by simpa only [execFullA] using h)

/-- **`swissHandoffA` authorized — PROVED.** A committed handoff implies the introducer held authority
over the `exporter` cell. -/
theorem execFullA_swissHandoffA_authorized (s s' : RecChainedState) (sw certHash : Nat)
    (introducer exporter : CellId)
    (h : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s') :
    stateAuthB s.kernel.caps introducer exporter = true :=
  swissHandoffChainA_authorized (by simpa only [execFullA] using h)

/-- **`swissDropA` authorized — PROVED.** A committed drop implies the actor held authority over the
`exporter` cell. -/
theorem execFullA_swissDropA_authorized (s s' : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (h : execFullA s (.swissDropA sw actor exporter) = some s') :
    stateAuthB s.kernel.caps actor exporter = true :=
  swissDropChainA_authorized (by simpa only [execFullA] using h)

/-! ### §MA-lifecycle authority obligations (Wave-3) — the cell lifecycle + refresh effects carry their
REAL `stateAuthB actor cell` self-lifecycle gate. The state-machine guard (Live↔Sealed/Destroyed) +
the no-parent / fresh-snapshot guards are the SEPARATE kernel-level obligations
(`cellSealChainA_nonlive_rejects` / `cellDestroyChainA_terminal_rejects` /
`refreshDelegationChainA_noParent_rejects` / `refreshDelegationChainA_snapshots_parent`). -/

/-- **`cellSealA` authorized — PROVED.** A committed seal implies the actor held authority over `cell`. -/
theorem execFullA_cellSealA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.cellSealA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (cellSealChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`cellUnsealA` authorized — PROVED.** -/
theorem execFullA_cellUnsealA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.cellUnsealA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (cellUnsealChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`cellDestroyA` authorized — PROVED.** -/
theorem execFullA_cellDestroyA_authorized (s s' : RecChainedState) (actor cell : CellId) (ch : Nat)
    (h : execFullA s (.cellDestroyA actor cell ch) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (cellDestroyChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`refreshDelegationA` authorized — PROVED.** A committed refresh implies the actor held the
self-authority over the `child` (dregg1's self-only `action_target == child` gate). -/
theorem execFullA_refreshDelegationA_authorized (s s' : RecChainedState) (actor child : CellId)
    (h : execFullA s (.refreshDelegationA actor child) = some s') :
    stateAuthB s.kernel.caps actor child = true :=
  (refreshDelegationChainA_factors (by simpa only [execFullA] using h)).1.1

/-! ### §MA-auth authority obligations — the 6 distinct authority effects carry their REAL,
NON-VACUOUS integrity content (grounding / `addEdge` / `removeEdge` / non-amplification / held-cap).
These REUSE the `recKDelegate`/`recKRevokeTarget` spine lemmas and `Caps.attenuate_subset` — exactly
the proofs `Exec.EffectsAuthority` carries (which we cannot import, being downstream). -/

/-- **`execFullA_introduceA_grounds` — PROVED.** A committed introduce HOLDS the Granovetter source
edge `introducer ⟶ ⟨target,()⟩` (only connectivity begets connectivity). REUSES `recKDelegate_grounds`. -/
theorem execFullA_introduceA_grounds (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps intro (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' intro rec t hd

/-- **`execFullA_introduceA_addEdge` — PROVED.** A committed introduce edits the graph by EXACTLY
`addEdge … rec ⟨t,()⟩`. REUSES `recKDelegate_execGraph`. -/
theorem execFullA_introduceA_addEdge (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps intro rec t hg
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **`execFullA_introduceA_holds_real_cap` — PROVED.** A committed introduce WITNESSES the concrete
held cap behind the connectivity edge: the introducer holds, in its real c-list, an `Authority.Cap`
`held` conferring an edge to `target`. This recovers the REAL `List Auth` rights the genuine
non-amplification reads (the seam `EffectsAuthority.exercise_holds_real_cap` opens). -/
theorem execFullA_introduceA_holds_real_cap (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    ∃ held : Cap, held ∈ s.kernel.caps intro ∧ confersEdgeTo t held = true := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
      · rw [List.any_eq_true] at hg
        obtain ⟨held, hmem, hconf⟩ := hg
        exact ⟨held, hmem, hconf⟩
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **`execFullA_introduceA_grants_held_cap` — PROVED.** A committed introduce grants the recipient
the concrete held cap selected by `heldCapTo`; no endpoint cap is widened into `node`/control. -/
theorem execFullA_introduceA_grants_held_cap (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    heldCapTo s.kernel.caps intro t ∈ s'.kernel.caps rec := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h
      simp only [Option.some.injEq] at h
      subst h
      exact recKDelegate_grants s.kernel k' intro rec t hd

/-- **`execFullA_introduceA_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** The actual executable
grant made by `introduceA` is a copy of the introducer's held cap to `t`, hence it is non-amplifying
over the exact cap it copied. Explicit narrowing belongs to `delegateAttenA`; this theorem states the
concrete copy branch rather than an uncarried attenuation payload. -/
theorem execFullA_introduceA_non_amplifying (s s' : RecChainedState) (intro rec t : CellId)
    (_h : execFullA s (.introduceA intro rec t) = some s') :
    IsNonAmplifyingF (heldCapTo s.kernel.caps intro t) (heldCapTo s.kernel.caps intro t) :=
  fun _ ha => ha

/-- **`execFullA_attenuateA_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** Whatever cap the
actor narrows, the narrowed cap confers a genuine `List Auth` SUBSET of the original:
`∀ c, IsNonAmplifyingF c (attenuate keep c)`, via `Caps.attenuate_subset`. The executable
`is_narrower_or_equal` (widening denied). -/
theorem execFullA_attenuateA_non_amplifying (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execFullA s (.attenuateA actor idx keep) = some s') :
    ∀ c : Cap, IsNonAmplifyingF c (attenuate keep c) :=
  fun c => attenuateF_non_amplifying keep c

/-- **`execFullA_attenuateA_confined` — PROVED.** Attenuation edits ONLY the actor's OWN slot; every
OTHER holder's slot is untouched (the confinement face of "you can only narrow what you hold"). -/
theorem execFullA_attenuateA_confined (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execFullA s (.attenuateA actor idx keep) = some s') :
    ∀ l, l ≠ actor → s'.kernel.caps l = s.kernel.caps l := by
  simp only [execFullA, attenuateStepA, Option.some.injEq] at h
  subst h
  intro l hl; simp only [attenuateSlotF, if_neg hl]

/-- **`execFullA_dropRefA_removeEdge` — PROVED.** A committed DropRef edits the graph by EXACTLY
`removeEdge … holder ⟨t,()⟩` (the GC of a remote reference). REUSES `recKRevokeTarget_execGraph`. -/
theorem execFullA_dropRefA_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.dropRefA holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **`execFullA_revokeDelegationA_removeEdge` — PROVED.** A committed RevokeDelegation edits the
graph by EXACTLY `removeEdge … holder ⟨t,()⟩` (the parent drops the child's edge). REUSES
`recKRevokeTarget_execGraph`. -/
theorem execFullA_revokeDelegationA_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.revokeDelegationA holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **`execFullA_validateHandoffA_grounds` — PROVED.** A committed handoff HOLDS the Granovetter
source edge `introducer ⟶ ⟨target,()⟩` (the handoff IS an introduce). REUSES `recKDelegate_grounds`. -/
theorem execFullA_validateHandoffA_grounds (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.validateHandoffA intro rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps intro (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' intro rec t hd

/-- **`execFullA_validateHandoffA_addEdge` — PROVED.** A committed handoff edits the reconstructed
authority graph by exactly `addEdge … rec ⟨t,()⟩`, because it routes through the same held-cap
delegation primitive as `introduceA`. -/
theorem execFullA_validateHandoffA_addEdge (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.validateHandoffA intro rec t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      unfold recKDelegate at hd
      by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
      · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
        exact recKDelegate_execGraph s.kernel.caps intro rec t hg
      · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **`execFullA_validateHandoffA_grants_held_cap` — PROVED.** A committed handoff grants the concrete
held cap selected by `heldCapTo`; it does not widen endpoint authority into `node`/control. -/
theorem execFullA_validateHandoffA_grants_held_cap (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.validateHandoffA intro rec t) = some s') :
    heldCapTo s.kernel.caps intro t ∈ s'.kernel.caps rec := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h
      simp only [Option.some.injEq] at h
      subst h
      exact recKDelegate_grants s.kernel k' intro rec t hd

/-- **`execFullA_validateHandoffA_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** The actual cap
granted by `validateHandoffA` is the introducer's held cap to `t`, hence it is non-amplifying over the
real `List Auth` lattice by reflexivity of `⊆`. -/
theorem execFullA_validateHandoffA_non_amplifying (s s' : RecChainedState) (intro rec t : CellId)
    (_h : execFullA s (.validateHandoffA intro rec t) = some s') :
    IsNonAmplifyingF (heldCapTo s.kernel.caps intro t) (heldCapTo s.kernel.caps intro t) :=
  fun _ ha => ha

/-- **`execFullA_delegateAttenA_grounds` — PROVED.** A committed rights-delegation HOLDS the abstract
source edge `del ⟶ ⟨t,()⟩` (the Granovetter connectivity premise — the delegator could already reach
`t`). Reads `recKDelegateAtten_grounds`. -/
theorem execFullA_delegateAttenA_grounds (s s' : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegateAtten] at h
  cases hd : recKDelegateAtten s.kernel del rec t keep with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegateAtten_grounds s.kernel k' del rec t keep hd

/-- **`execFullA_delegateAttenA_grants` — PROVED.** On commit, the `recipient` GENUINELY HOLDS the
delegator's held cap to `t` ATTENUATED to `keep` (the executable `grant_with_expiry` landed the
attenuated permission). Reads `recKDelegateAtten_grants`. -/
theorem execFullA_delegateAttenA_grants (s s' : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    attenuate keep (heldCapTo s.kernel.caps del t) ∈ s'.kernel.caps rec := by
  simp only [execFullA, recCDelegateAtten] at h
  cases hd : recKDelegateAtten s.kernel del rec t keep with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' =>
      rw [hd] at h; simp only [Option.some.injEq] at h; subst h
      exact recKDelegateAtten_grants s.kernel k' del rec t keep hd

/-- **`execFullA_delegateAttenA_non_amplifying` — THE HEADLINE (PROVED, GENUINE & EXECUTED).** The cap
the recipient actually RECEIVES confers a `List Auth` SUBSET of the delegator's held cap to `t`
(`granted ⊆ held`) — `is_attenuation(held, granted)` over the EXECUTED grant, NOT a `()≤()` collapse.
Reads `attenuate_subset`. -/
theorem execFullA_delegateAttenA_non_amplifying (s s' : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (_h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    IsNonAmplifyingF (heldCapTo s.kernel.caps del t) (attenuate keep (heldCapTo s.kernel.caps del t)) := by
  unfold IsNonAmplifyingF
  exact attenuate_subset keep (heldCapTo s.kernel.caps del t)

/-- **`execFullA_exerciseA_authorized` — PROVED.** A committed exercise HOLDS the source edge:
`actor ⟶ ⟨target,()⟩` on `execGraph` (the resolved c-list slot — only the holder may exercise). The
hold-gate (`exerciseStepA`) authorizes regardless of what the inner effects do. -/
theorem execFullA_exerciseA_authorized (s s' : RecChainedState) (actor t : CellId) (inner : List FullActionA)
    (h : execFullA s (.exerciseA actor t inner) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps actor (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA] at h
  cases hg : exerciseStepA s actor t with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some s1 =>
      obtain ⟨hgg, _⟩ := exerciseStepA_factors hg
      rw [execGraph_eq_any]; exact hgg

/-- **`execFullA_exerciseA_recurses` — PROVED (the DE-SHADOW witness).** A committed exercise actually
RAN its inner effects: there is a gate-state `s1` (the hold-gate's result) from which the inner fold
`execInnerA s1 inner` committed to `s'`. This is the teeth that distinguish a real exercise from the old
no-op shadow — the `inner` effects genuinely executed against the cap's target. -/
theorem execFullA_exerciseA_recurses (s s' : RecChainedState) (actor t : CellId) (inner : List FullActionA)
    (h : execFullA s (.exerciseA actor t inner) = some s') :
    ∃ s1, exerciseStepA s actor t = some s1 ∧ execInnerA s1 inner = some s' := by
  simp only [execFullA] at h
  cases hg : exerciseStepA s actor t with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some s1 => rw [hg] at h; exact ⟨s1, rfl, h⟩

/-! ### §MA-escrow authority/membership obligations — the create-side carries the REAL `authorizedB`
creator gate (over the debited cell); noteSpend/noteCreate carry the genuine SET-membership witness. -/

/-- **`execFullA_createEscrowA_authorized` — PROVED.** A committed escrow create required the actor to be
authorized over the debited `creator` cell (the SAME `authorizedB` gate as `transfer`). -/
theorem execFullA_createEscrowA_authorized (s s' : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA s (.createEscrowA id actor creator recipient asset amount) = some s') :
    authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true := by
  simp only [execFullA, createEscrowChainA] at h
  cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' => exact createEscrowKAsset_authorized hk

/-- **`execFullA_createObligationA_authorized` — PROVED** (the obligation alias of the create gate). -/
theorem execFullA_createObligationA_authorized (s s' : RecChainedState) (id : Nat)
    (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
    (h : execFullA s (.createObligationA id actor obligor beneficiary asset stake) = some s') :
    authorizedB s.kernel.caps { actor := actor, src := obligor, dst := beneficiary, amt := stake } = true := by
  simp only [execFullA, createEscrowChainA] at h
  cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' => exact createEscrowKAsset_authorized hk

/-- **`execFullA_noteSpendA_inserts` — PROVED.** A committed noteSpend inserts `nf` into the nullifier
SET (so a subsequent spend of `nf` fails-closed — the anti-replay teeth). -/
theorem execFullA_noteSpendA_inserts (s s' : RecChainedState) (nf : Nat) (actor : CellId)
    (h : execFullA s (.noteSpendA nf actor) = some s') : nf ∈ s'.kernel.nullifiers := by
  simp only [execFullA, noteSpendChainA] at h
  cases hk : noteSpendNullifier s.kernel nf with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact note_spend_inserts hk

/-- **`execFullA_noteCreateA_inserts` — PROVED.** A committed noteCreate inserts `cm` into the grow-only
commitment SET. -/
theorem execFullA_noteCreateA_inserts (s s' : RecChainedState) (cm : Nat) (actor : CellId)
    (h : execFullA s (.noteCreateA cm actor) = some s') : cm ∈ s'.kernel.commitments := by
  simp only [execFullA, noteCreateChainA, Option.some.injEq] at h
  subst h; exact noteCreate_inserts s.kernel cm

/-! ### §MA-bridge authority/portal obligations (Wave-5). The bridge LOCK carries the REAL `authorizedB`
originator gate (over the debited cell — the §8 spending proof is the THEOREM-level portal); FINALIZE
carries the disclosed OUTFLOW witness (combined DROPS by the disclosed `-amount` — the §8 confirmation
receipt is the THEOREM-level portal, a genuine portal on a REACHABLE path, exactly as bridgeMint's foreign
finality); CANCEL carries the refund-conservation witness. -/

/-- **`execFullA_bridgeLockA_authorized` — PROVED.** A committed bridge lock required the actor to be
authorized over the debited originator cell (the SAME `authorizedB` gate as `transfer`/escrow-create). The
LOCAL gate independent of the §8 spending-proof portal (carried at the theorem layer). -/
theorem execFullA_bridgeLockA_authorized (s s' : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA s (.bridgeLockA id actor originator destination asset amount) = some s') :
    authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = true := by
  simp only [execFullA] at h
  exact bridgeLockChainA_authorized h

/-- **`execFullA_bridgeLockA_unauthorized_fails` — PROVED (fail-closed).** Without authority over the
originator, no bridge lock commits (regardless of the §8 spending proof). The confinement core: the value
cannot be locked-and-bridged out of a cell the actor does not control. -/
theorem execFullA_bridgeLockA_unauthorized_fails (s : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = false) :
    execFullA s (.bridgeLockA id actor originator destination asset amount) = none := by
  simp only [execFullA, bridgeLockChainA, bridgeLockKAsset]
  rw [if_neg (by rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp))]

/-- **`execFullA_bridgeFinalizeA_burns_per_asset` — THE BRIDGE OUTFLOW WITNESS (PROVED).** A committed
bridge finalize DROPS the COMBINED per-asset measure by EXACTLY the disclosed `amount` at the disclosed
`asset` and leaves EVERY OTHER asset literally fixed — the value genuinely LEFT for the other chain (a
disclosed OUTFLOW, NOT a conservation claim). The §8 confirmation receipt is the THEOREM-level portal. -/
theorem execFullA_bridgeFinalizeA_burns_per_asset (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (asset : AssetId) (amount : ℤ) (b : AssetId)
    (h : execFullA s (.bridgeFinalizeA id actor asset amount) = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b - (if b = asset then amount else 0) :=
  bridgeFinalizeChainA_burns_combined b (by simpa only [execFullA] using h)

/-- **`execFullA_bridgeCancelA_conserves_per_asset` — PROVED (the refund round-trip).** A committed bridge
cancel conserves the COMBINED per-asset measure at EVERY asset (the value returns to the LIVE, gate-checked
originator). The timeout gate is carried at the theorem layer. -/
theorem execFullA_bridgeCancelA_conserves_per_asset (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (b : AssetId) (h : execFullA s (.bridgeCancelA id actor) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  bridgeCancelChainA_combined_neutral b (by simpa only [execFullA] using h)

/-- **The per-`FullActionA` `StepInv`** — the per-asset analog of `fullActionInv`, true of every
committed per-asset action across all kinds. Its **Ledger** conjunct is the full per-asset VECTOR (a
`∀ b`, never an aggregate scalar — the FILL-1 carrier that forbids cross-asset laundering):
  * **Ledger (vector)** — for EVERY asset `b`, `recTotalAsset … b` moved by EXACTLY `ledgerDeltaAsset
    fa b` (`0` for transfer/authority, `±amt` at the targeted asset only for mint/burn);
  * **ChainLink** — the chain extends by exactly `fullReceiptA fa` (newest-first), no fork/rewrite;
  * **ObsAdvance** — the chain grew by exactly one row (replay-detectable);
  * **KindObligation** — the kind-specific integrity content (asset-orthogonal): balanceA ⇒
    `authorizedB`; delegate ⇒ grounds in the source edge AND edits the graph by `addEdge`; revoke ⇒
    `removeEdge`; mintA/burnA ⇒ `mintAuthorizedB` AND the Generative/Annihilative disclosure. -/
def fullActionInvA (s : RecChainedState) (fa : FullActionA) (s' : RecChainedState) : Prop :=
  -- Ledger: the per-asset COMBINED conservation VECTOR (∀ b — never one aggregate scalar). The UNIFORM
  -- measure across ALL kinds is `recTotalAssetWithEscrow` (= `bal`-ledger + per-asset holding-store);
  -- non-escrow kinds leave `escrows` fixed so their combined delta = bare-`bal` delta, escrow/note legs
  -- are combined-conserving (combined delta `0`) — the FILL-1/META-FILL-C no-laundering carrier.
  (∀ b, recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + ledgerDeltaAsset fa b) ∧
  -- ChainLink: the pre-log is a SUFFIX of the post-log (append-only) AND the kind's own receipt is
  -- recorded in the post-log. For every NON-recursive kind this is the exact one-row extension
  -- `fullReceiptA fa :: s.log`; for `exerciseA` (which RECURSES through `inner`) the kind's own
  -- `authReceipt` is followed by the inner effects' receipts — still append-only, still records the
  -- exercise receipt. The honest append-only audit-chain law across the WHOLE op-set.
  (s.log <:+ s'.log ∧ fullReceiptA fa ∈ s'.log) ∧
  -- ObsAdvance: the chain STRICTLY grows (≥ one row — exactly one for non-recursive kinds, `1 + |inner|`
  -- for a committed exercise), so a replayed action is detectable.
  (s.log.length < s'.log.length) ∧
  -- KindObligation: the kind-specific authority/graph/disclosure content (asset-orthogonal).
  (match fa with
   | .balanceA t _       => authorizedB s.kernel.caps t = true
   | .delegate del rec t =>
       Dregg2.Spec.execGraph s.kernel.caps del
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩
   | .revoke holder t    =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .mintA actor cell _ _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity mintEffect).is_disclosed_non_conservation = true
   | .burnA actor cell _ _  =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity burnEffect).is_disclosed_non_conservation = true
   -- §MA-state: the field-writing pure-state effects carry their REAL authority gate
   -- (`stateAuthB` over the cell) ∧ their `Neutral`/`Monotonic` linearity coloring (the
   -- faithful-mirror tripwire). `emitEventA` is authority-FREE (dregg1 runs no cap check), but it
   -- carries the dregg1 cell-existence gate plus its `Neutral` coloring — honestly NOT an authority claim.
   | .setFieldA actor cell _ _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .setField = LinearityClass.Neutral
   | .emitEventA _ cell _ _ =>
       cell ∈ s.kernel.accounts ∧
       effectLinearity .emitEvent = LinearityClass.Neutral
   | .incrementNonceA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .incrementNonce = LinearityClass.Monotonic
   | .setPermissionsA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .setPermissions = LinearityClass.Neutral
   | .setVKA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .setVerificationKey = LinearityClass.Neutral
   -- §MA-auth: the 6 authority effects carry their REAL, NON-VACUOUS obligation. The HEADLINE is
   -- NON-AMPLIFICATION — the GENUINE `capAuthConferred ⊆` over the real `List Auth` lattice
   -- (`IsNonAmplifyingF`, witnessed against a HELD cap), NOT a `()≤()` collapse — and the `addEdge`/
   -- `removeEdge`/graph-unchanged graph move + grounding in held connectivity.
   | .introduceA intro rec t =>
       -- (a) grounds in held connectivity, (b) edits the graph by `addEdge`, (c) grants the concrete
       -- held cap selected by the executable lookup, and (d) that actual copied cap is non-amplifying.
       -- Explicit attenuation is the separate `delegateAttenA` branch.
       Dregg2.Spec.execGraph s.kernel.caps intro
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩ ∧
       heldCapTo s.kernel.caps intro t ∈ s'.kernel.caps rec ∧
       IsNonAmplifyingF (heldCapTo s.kernel.caps intro t) (heldCapTo s.kernel.caps intro t)
   | .attenuateA _ idx keep =>
       -- GENUINE non-amplification: narrowing to `keep` confers a `List Auth` SUBSET of ANY cap.
       ∀ c : Cap, IsNonAmplifyingF c (attenuate keep c)
   | .dropRefA holder t =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .revokeDelegationA holder t =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   | .validateHandoffA intro rec t =>
       -- Graph-level handoff consequence: (a) grounds in held connectivity, (b) edits the graph by
       -- `addEdge`, (c) grants the concrete held cap, and (d) the actual executable grant is a
       -- non-amplifying copy. The richer certificate-level `granted ≤ held` obligation is carried by
       -- `Exec.CapTP.HandoffCert`/`swissHandoffA`, where permissions and effect masks actually exist.
       Dregg2.Spec.execGraph s.kernel.caps intro
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩ ∧
       heldCapTo s.kernel.caps intro t ∈ s'.kernel.caps rec ∧
       IsNonAmplifyingF (heldCapTo s.kernel.caps intro t) (heldCapTo s.kernel.caps intro t)
   | .delegateAttenA del rec t keep =>
       -- (a) grounds in held connectivity, (b) the recipient GENUINELY HOLDS the delegator's held
       -- cap to `t` ATTENUATED to `keep` (the EXECUTED rights handoff — `recKDelegateAtten_grants`,
       -- NOT a static claim), (c) GENUINE rights non-amplification: that granted cap confers a
       -- `List Auth` SUBSET of the held cap (`is_attenuation(held, granted)`, `apply.rs:2829`).
       Dregg2.Spec.execGraph s.kernel.caps del
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       attenuate keep (heldCapTo s.kernel.caps del t) ∈ s'.kernel.caps rec ∧
       IsNonAmplifyingF (heldCapTo s.kernel.caps del t) (attenuate keep (heldCapTo s.kernel.caps del t))
   | .exerciseA actor t inner =>
       -- authorized BY the held edge (only the holder may exercise) AND the exercise RECURSED — the
       -- `inner` effects actually RAN against the target (de-SHADOW: there EXISTS a gate-state `s1`
       -- reached by the hold-gate from which `execInnerA s1 inner = some s'` committed). NO graph-frozen
       -- claim: an inner effect MAY legitimately edit the cap-graph (e.g. an inner delegate), exactly as
       -- dregg1 `apply.rs:2647` applies each inner effect against the cap's target.
       Dregg2.Spec.execGraph s.kernel.caps actor
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       (∃ s1, exerciseStepA s actor t = some s1 ∧ execInnerA s1 inner = some s')
   -- §MA-supply: createCell/spawn carry the REAL privileged-creation gate (`mintAuthorizedB` — bare
   -- ownership is NOT enough) AND the REAL freshness gate (`newCell ∉ accounts`, fail-closed: a
   -- non-fresh id is rejected) AND the Generative disclosure coloring; bridgeMint carries the
   -- privileged mint gate AND the §8 Generative disclosure. NOT `True` — every conjunct has teeth.
   | .createCellA actor newCell =>
       mintAuthorizedB s.kernel.caps actor newCell = true ∧
       newCell ∉ s.kernel.accounts ∧
       newCell ∈ s'.kernel.accounts ∧
       (effectLinearity .createCell).is_disclosed_non_conservation = true
   -- §MA-factory: factory creation carries the REAL privileged-creation gate AND — the load-bearing
   -- claim — the INSTALLED-PROGRAM keystone: the minted cell carries EXACTLY some registered factory's
   -- slot caveats (its published lifetime program), so the executor enforces them on every later
   -- `SetField`. NOT `True`: the program-install witnesses the factory was found + the cell registered.
   | .createCellFromFactoryA actor newCell vk =>
       mintAuthorizedB s.kernel.caps actor newCell = true ∧
       newCell ∈ s'.kernel.accounts ∧
       (∃ e, findFactory s.kernel.factories vk.toNat = some e ∧
              s'.kernel.slotCaveats newCell = e.caveats) ∧
       (effectLinearity .createCellFromFactory).is_disclosed_non_conservation = true
   | .spawnA actor child target =>
       mintAuthorizedB s.kernel.caps actor child = true ∧
       child ∉ s.kernel.accounts ∧
       target ∈ s.kernel.accounts ∧
       Dregg2.Spec.execGraph s.kernel.caps actor
         (⟨target, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       heldCapTo s.kernel.caps actor target ∈ s'.kernel.caps child ∧
       IsNonAmplifyingF (heldCapTo s.kernel.caps actor target) (heldCapTo s.kernel.caps actor target) ∧
       s'.kernel.delegate child = some actor ∧
       s'.kernel.delegations child = s.kernel.caps actor ∧
       (effectLinearity .spawnWithDelegation).is_disclosed_non_conservation = true
   | .bridgeMintA actor cell _ _ =>
       mintAuthorizedB s.kernel.caps actor cell = true ∧
       (effectLinearity mintEffect).is_disclosed_non_conservation = true
   -- §MA-escrow: create-side obligations carry the REAL `authorizedB` creator gate (over the debited
   -- cell) ∧ the `Conservative` coloring; the settle-side and notes carry the genuine SET/store
   -- membership witness — every conjunct has teeth (NOT `True`).
   | .createEscrowA _ actor creator recipient _ amount =>
       authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true ∧
       effectLinearity .createEscrow = LinearityClass.Conservative
   | .releaseEscrowA _ _ =>
       effectLinearity .releaseEscrow = LinearityClass.Conservative
   | .refundEscrowA _ _ =>
       effectLinearity .refundEscrow = LinearityClass.Conservative
   | .createObligationA _ actor obligor beneficiary _ stake =>
       authorizedB s.kernel.caps { actor := actor, src := obligor, dst := beneficiary, amt := stake } = true ∧
       effectLinearity .createObligation = LinearityClass.Conservative
   -- fulfill/slash SETTLE the parked obligation record back onto the ledger (combined-conserving): the
   -- `Conservative` coloring. The obligor-only (fulfill) / post-deadline (slash) gates are the
   -- §8/theorem-layer carriers (block-height + obligor identity), off this executable layer.
   | .fulfillObligationA _ _ =>
       effectLinearity .fulfillObligation = LinearityClass.Conservative
   | .slashObligationA _ _ =>
       effectLinearity .slashObligation = LinearityClass.Conservative
   | .noteSpendA nf _ =>
       -- anti-replay: the spent nullifier is now IN the set (a subsequent spend fails-closed).
       nf ∈ s'.kernel.nullifiers ∧ effectLinearity .noteSpend = LinearityClass.Conservative
   | .noteCreateA cm _ =>
       -- the fresh commitment is now IN the grow-only commitment set.
       cm ∈ s'.kernel.commitments ∧ effectLinearity .noteCreate = LinearityClass.Conservative
   | .createCommittedEscrowA _ actor creator recipient _ amount hidingProof =>
       -- WAVE 4 HONESTY: the committed variant carries the §8 HIDING-PORTAL obligation `hidingProof =
       -- true` that plain escrow does NOT — the privacy boundary made EXPLICIT (NOT silently identical)
       -- ∧ the REAL `authorizedB` creator gate ∧ the `Conservative` coloring.
       hidingProof = true ∧
       authorizedB s.kernel.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true ∧
       effectLinearity .createCommittedEscrow = LinearityClass.Conservative
   | .releaseCommittedEscrowA _ _ =>
       effectLinearity .releaseCommittedEscrow = LinearityClass.Conservative
   | .refundCommittedEscrowA _ _ =>
       effectLinearity .refundCommittedEscrow = LinearityClass.Conservative
   -- §MA-bridge: LOCK carries the REAL `authorizedB` originator gate (over the debited cell) ∧ the
   -- `Conservative` coloring (combined-conserving lock). FINALIZE carries the genuine DISCLOSED-OUTFLOW
   -- witness — the COMBINED measure MOVED DOWN by the disclosed `-amount` at the disclosed `asset`
   -- (`∀ b`, the §8 confirmation portal having fired; NOT a `True`, the move has teeth) ∧ the
   -- `Annihilative` coloring (the value left for the other chain — a disclosed burn, NOT conserved).
   -- CANCEL carries the refund-CONSERVATION witness (combined fixed `∀ b`) ∧ the coloring. Teeth.
   | .bridgeLockA _ actor originator destination _ amount =>
       authorizedB s.kernel.caps { actor := actor, src := originator, dst := destination, amt := amount } = true ∧
       effectLinearity .bridgeLock = LinearityClass.Conservative
   | .bridgeFinalizeA _ _ asset amount =>
       (∀ b, recTotalAssetWithEscrow s'.kernel b
          = recTotalAssetWithEscrow s.kernel b - (if b = asset then amount else 0)) ∧
       effectLinearity .bridgeFinalize = LinearityClass.Annihilative
   | .bridgeCancelA _ _ =>
       (∀ b, recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b) ∧
       effectLinearity .bridgeCancel = LinearityClass.Conservative
   -- §MA-seal (Wave-3 DE-SHADOW): seal/unseal carry their REAL c-list HOLD gate (the actor genuinely
   -- HOLDS the sealer/unsealer cap for `pid` — `lookup_by_target`, `apply.rs:2756`/`:2891`), createSealPair
   -- its `stateAuthB actor sealerHolder` writer gate ∧ their catalog COLORING (all Generative). The §8 AEAD
   -- crypto is the chain-layer portal — NOT an authority claim. Every conjunct has teeth (NOT `True`).
   | .sealA pid actor _ =>
       (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧
       effectLinearity .seal = LinearityClass.Generative
   | .unsealA pid actor _ =>
       (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true ∧
       effectLinearity .unseal = LinearityClass.Generative
   | .createSealPairA _ actor sealerHolder _ =>
       stateAuthB s.kernel.caps actor sealerHolder = true ∧
       effectLinearity .createSealPair = LinearityClass.Generative
   | .makeSovereignA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .makeSovereign = LinearityClass.Terminal
   | .refusalA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .refusal = LinearityClass.Monotonic
   | .receiptArchiveA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .receiptArchive = LinearityClass.Terminal
   -- §MA-queue: the 4 ring-buffer FIFO queue effects carry their REAL `stateAuthB actor cell` authority
   -- gate over the queue's representing cell (dregg1's writer-ACL / owner gate) ∧ their catalog COLORING
   -- (the faithful-mirror tripwire: queueAllocate/queueResize Generative, queueEnqueue/queueDequeue
   -- Conservative). The FIFO ORDER + capacity bound + emptiness gate are the SEPARATE kernel-level
   -- obligation (`qbuf_fifo_order` / `queueEnqueueK_full_rejects` / `queueDequeueK_empty_rejects`, in
   -- `RecordKernel`). Every conjunct has teeth, NOT `True`.
   | .queueAllocateA _ actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .queueAllocate = LinearityClass.Generative
   | .queueEnqueueA _ _ actor cell _ _ _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .queueEnqueue = LinearityClass.Conservative
   | .queueDequeueA _ actor cell _ _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .queueDequeue = LinearityClass.Conservative
   | .queueResizeA _ _ actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .queueResize = LinearityClass.Generative
   -- §MA-queue-batch (WAVE 4): the atomic batch carries the ATOMICITY witness — the committed post-state
   -- IS the all-or-nothing fold of the sub-ops over `s` (`queueAtomicTxChainA s ops = some s'` modulo the
   -- batch-commit receipt row, so EVERY sub-op committed; a failing sub-op would have collapsed the whole
   -- batch) ∧ the `Conservative` coloring. The pipeline step carries the source-dequeue + fan-out witness
   -- (the committed post-kernel IS the source dequeue then the sink fan-out) ∧ the `Conservative`
   -- coloring. pipelinedSend carries the apply-time NEUTRAL coloring (the `EventualRef` resolution is the
   -- SEPARATE `ConditionalTurn` batch — authority-free at apply, dregg1's apply-time no-op). Teeth, not `True`.
   | .queueAtomicTxA actor ops =>
       (∃ s1, queueAtomicTxChainA s ops = some s1 ∧
              s'.log = escrowReceiptA actor :: s1.log ∧ s'.kernel = s1.kernel) ∧
       effectLinearity .queueAtomicTx = LinearityClass.Conservative
   | .queuePipelineStepA srcId owner sinkCells sinkIds =>
       (∃ k1 m, queueDequeueK s.kernel srcId owner = some (k1, m) ∧
                pipelineFanoutK k1 owner m sinkCells sinkIds = some s'.kernel) ∧
       effectLinearity .queuePipelineStep = LinearityClass.Conservative
   | .pipelinedSendA _ =>
       effectLinearity .pipelinedSend = LinearityClass.Neutral
   -- §MA-swiss: the 4 CapTP swiss-table effects carry their REAL `stateAuthB actor exporter` authority
   -- gate over the exporting cell ∧ their catalog COLORING (export/enliven/handoff Monotonic, drop
   -- Terminal). The membership / non-amplification / refcount-GC are the SEPARATE kernel obligation
   -- (`swissExportK_amplification_rejects` / `swissEnlivenK_absent_rejects` / `swissDropK_gc_at_one`).
   | .exportSturdyRefA _ actor exporter _ _ =>
       stateAuthB s.kernel.caps actor exporter = true ∧
       effectLinearity .exportSturdyRef = LinearityClass.Monotonic
   | .enlivenRefA _ actor exporter _ =>
       stateAuthB s.kernel.caps actor exporter = true ∧
       effectLinearity .enlivenRef = LinearityClass.Monotonic
   | .swissHandoffA _ _ introducer exporter =>
       stateAuthB s.kernel.caps introducer exporter = true ∧
       effectLinearity .validateHandoff = LinearityClass.Monotonic
   | .swissDropA _ actor exporter =>
       stateAuthB s.kernel.caps actor exporter = true ∧
       effectLinearity .dropRef = LinearityClass.Terminal
   -- §MA-lifecycle (Wave-3): cellSeal/Unseal carry their `stateAuthB actor cell` self-lifecycle gate ∧
   -- their catalog COLORING (cellSeal/cellUnseal/cellDestroy Terminal, refreshDelegation Neutral). The
   -- state-machine guard (Live↔Sealed/Destroyed) is the SEPARATE kernel obligation
   -- (`cellSealChainA_nonlive_rejects` / `cellDestroyChainA_terminal_rejects`). cellDestroy also reads
   -- the self gate; refreshDelegation the self gate (over the `child`). Every conjunct has teeth.
   | .cellSealA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .cellSeal = LinearityClass.Terminal
   | .cellUnsealA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .cellUnseal = LinearityClass.Terminal
   | .cellDestroyA actor cell _ =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .cellDestroy = LinearityClass.Terminal
   | .refreshDelegationA actor child =>
       stateAuthB s.kernel.caps actor child = true ∧
       effectLinearity .refreshDelegation = LinearityClass.Neutral)

/-- **`execFullA_attests_per_asset` — THE PER-ASSET OP-SET IS STEP-COMPLETE BY CONSTRUCTION
(PROVED).** Every committed `FullActionA` attests its full `StepInv` content: the per-asset ledger
VECTOR ∧ ChainLink ∧ ObsAdvance ∧ the kind-specific obligation. The per-asset analog of
`execFull_attests`, carrying the conservation VECTOR (not the scalar). -/
theorem execFullA_attests_per_asset {s s' : RecChainedState} {fa : FullActionA}
    (h : execFullA s fa = some s') : fullActionInvA s fa s' := by
  refine ⟨fun b => execFullA_ledger_per_asset s s' fa b h,
          execFullA_chainlink s s' fa h, execFullA_obsadvance s s' fa h, ?_⟩
  cases fa with
  | balanceA t a => exact execFullA_balance_authorized s s' t a h
  | delegate del rec t =>
      exact ⟨execFullA_delegate_grounds s s' del rec t h, execFullA_delegate_addEdge s s' del rec t h⟩
  | revoke holder t => exact execFullA_revoke_removeEdge s s' holder t h
  | mintA actor cell a amt => exact ⟨execFullA_mintA_authorized s s' actor cell a amt h, mint_discloses⟩
  | burnA actor cell a amt => exact ⟨execFullA_burnA_authorized s s' actor cell a amt h, burn_discloses⟩
  -- §MA-state: discharge the field-writing effects' (authority ∧ coloring) obligation; emitEvent's
  -- live-cell ∧ coloring obligation (authority-free, but not ghost-cell-free).
  | setFieldA actor cell f v => exact ⟨execFullA_setFieldA_authorized s s' actor cell f v h, rfl⟩
  | emitEventA actor cell topic data =>
      by_cases hlive : cell ∈ s.kernel.accounts
      · exact ⟨hlive, rfl⟩
      · simp only [execFullA, hlive, if_false] at h
        cases h
  | incrementNonceA actor cell n => exact ⟨execFullA_incrementNonceA_authorized s s' actor cell n h, rfl⟩
  | setPermissionsA actor cell p => exact ⟨execFullA_setPermissionsA_authorized s s' actor cell p h, rfl⟩
  | setVKA actor cell vk => exact ⟨execFullA_setVKA_authorized s s' actor cell vk h, rfl⟩
  -- §MA-auth: discharge the 6 authority effects' REAL obligation (grounding/addEdge/removeEdge/
  -- graph-unchanged ∧ the GENUINE `capAuthConferred ⊆` non-amplification).
  | introduceA intro rec t =>
      exact ⟨execFullA_introduceA_grounds s s' intro rec t h,
             execFullA_introduceA_addEdge s s' intro rec t h,
             execFullA_introduceA_grants_held_cap s s' intro rec t h,
             execFullA_introduceA_non_amplifying s s' intro rec t h⟩
  | delegateAttenA del rec t keep =>
      exact ⟨execFullA_delegateAttenA_grounds s s' del rec t keep h,
             execFullA_delegateAttenA_grants s s' del rec t keep h,
             execFullA_delegateAttenA_non_amplifying s s' del rec t keep h⟩
  | attenuateA actor idx keep => exact execFullA_attenuateA_non_amplifying s s' actor idx keep h
  | dropRefA holder t => exact execFullA_dropRefA_removeEdge s s' holder t h
  | revokeDelegationA holder t => exact execFullA_revokeDelegationA_removeEdge s s' holder t h
  | validateHandoffA intro rec t =>
      exact ⟨execFullA_validateHandoffA_grounds s s' intro rec t h,
             execFullA_validateHandoffA_addEdge s s' intro rec t h,
             execFullA_validateHandoffA_grants_held_cap s s' intro rec t h,
             execFullA_validateHandoffA_non_amplifying s s' intro rec t h⟩
  | exerciseA actor t inner =>
      exact ⟨execFullA_exerciseA_authorized s s' actor t inner h,
             execFullA_exerciseA_recurses s s' actor t inner h⟩
  -- §MA-supply: discharge createCell/spawn's (privileged-creation gate ∧ freshness ∧ growth/provenance
  -- ∧ Generative disclosure) and bridgeMint's (privileged mint gate ∧ §8 Generative disclosure).
  | createCellA actor newCell =>
      simp only [execFullA] at h
      obtain ⟨hauth, hfresh, _⟩ := createCellChainA_factors h
      exact ⟨hauth, hfresh, createCellChainA_grows_accounts h,
             Dregg2.CatalogEffects.generative_discloses .createCell Dregg2.CatalogEffects.g_createCell⟩
  -- §MA-factory: discharge the (privileged-creation gate ∧ growth ∧ INSTALLED-PROGRAM keystone ∧
  -- Generative disclosure). The program-install witnesses the factory was found and the cell registered.
  | createCellFromFactoryA actor newCell vk =>
      simp only [execFullA] at h
      exact ⟨createCellFromFactoryChainA_authorized h,
             createCellFromFactoryChainA_grows_accounts h,
             createCellFromFactoryChainA_installs_program h,
             Dregg2.CatalogEffects.generative_discloses .createCellFromFactory
               Dregg2.CatalogEffects.g_createCellFromFactory⟩
  | spawnA actor child target =>
      simp only [execFullA] at h
      obtain ⟨s1, _, hc, _⟩ := spawnChainA_factors h
      have hground := spawnChainA_grounds (by simpa only [execFullA] using h)
      have hsnap := spawnChainA_parent_snapshot (by simpa only [execFullA] using h)
      exact ⟨createCellChainA_authorized hc, (createCellChainA_factors hc).2.1,
             hground.2, hground.1,
             spawnChainA_provenance (by simpa only [execFullA] using h),
             (fun _ ha => ha),
             hsnap.1, hsnap.2,
             Dregg2.CatalogEffects.generative_discloses .spawnWithDelegation
               Dregg2.CatalogEffects.g_spawnWithDelegation⟩
  | bridgeMintA actor cell a value =>
      exact ⟨execFullA_bridgeMintA_authorized s s' actor cell a value h, mint_discloses⟩
  -- §MA-escrow: discharge the create-side `authorizedB` gate + Conservative coloring, the settle-side
  -- coloring, and the noteSpend/noteCreate SET-membership witness.
  | createEscrowA id actor creator recipient asset amount =>
      exact ⟨execFullA_createEscrowA_authorized s s' id actor creator recipient asset amount h, rfl⟩
  | releaseEscrowA id actor => exact rfl
  | refundEscrowA id actor => exact rfl
  | createObligationA id actor obligor beneficiary asset stake =>
      exact ⟨execFullA_createObligationA_authorized s s' id actor obligor beneficiary asset stake h, rfl⟩
  | fulfillObligationA id actor => exact rfl
  | slashObligationA id actor => exact rfl
  | noteSpendA nf actor => exact ⟨execFullA_noteSpendA_inserts s s' nf actor h, rfl⟩
  | noteCreateA cm actor => exact ⟨execFullA_noteCreateA_inserts s s' cm actor h, rfl⟩
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      -- WAVE 4 HONESTY: discharge the §8 hiding-portal witness ∧ the `authorizedB` creator gate ∧ coloring.
      simp only [execFullA] at h
      obtain ⟨hhide, hauth⟩ := createCommittedEscrowChainA_authorized h
      exact ⟨hhide, hauth, rfl⟩
  | releaseCommittedEscrowA id actor => exact rfl
  | refundCommittedEscrowA id actor => exact rfl
  -- §MA-bridge: discharge LOCK's (authority ∧ Conservative coloring), FINALIZE's (disclosed-OUTFLOW
  -- move ∧ coloring), CANCEL's (refund-conservation ∧ coloring).
  | bridgeLockA id actor originator destination asset amount =>
      exact ⟨execFullA_bridgeLockA_authorized s s' id actor originator destination asset amount h, rfl⟩
  | bridgeFinalizeA id actor asset amount =>
      exact ⟨fun b => execFullA_bridgeFinalizeA_burns_per_asset s s' id actor asset amount b h, rfl⟩
  | bridgeCancelA id actor =>
      exact ⟨fun b => execFullA_bridgeCancelA_conserves_per_asset s s' id actor b h, rfl⟩
  -- §MA-seal (Wave-3 DE-SHADOW): discharge seal/unseal's REAL c-list HOLD gate, createSealPair's writer
  -- gate ∧ each catalog coloring.
  | sealA pid actor payload => exact ⟨execFullA_sealA_authorized s s' pid actor payload h, rfl⟩
  | unsealA pid actor recipient => exact ⟨execFullA_unsealA_authorized s s' pid actor recipient h, rfl⟩
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      exact ⟨execFullA_createSealPairA_authorized s s' pid actor sealerHolder unsealerHolder h, rfl⟩
  | makeSovereignA actor cell => exact ⟨execFullA_makeSovereignA_authorized s s' actor cell h, rfl⟩
  | refusalA actor cell => exact ⟨execFullA_refusalA_authorized s s' actor cell h, rfl⟩
  | receiptArchiveA actor cell => exact ⟨execFullA_receiptArchiveA_authorized s s' actor cell h, rfl⟩
  -- §MA-queue: discharge each queue effect's (REAL `stateAuthB` authority gate ∧ the catalog coloring).
  | queueAllocateA id actor cell cap =>
      exact ⟨execFullA_queueAllocateA_authorized s s' id actor cell cap h, rfl⟩
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      exact ⟨execFullA_queueEnqueueA_authorized s s' id m actor cell depId dAsset deposit h, rfl⟩
  | queueDequeueA id actor cell depId deposit =>
      exact ⟨execFullA_queueDequeueA_authorized s s' id actor cell depId deposit h, rfl⟩
  | queueResizeA id newCap actor cell =>
      exact ⟨execFullA_queueResizeA_authorized s s' id newCap actor cell h, rfl⟩
  -- §MA-queue-batch (WAVE 4): discharge the atomic batch's ATOMICITY witness ∧ coloring; the pipeline
  -- step's source-dequeue + fan-out routing witness ∧ coloring; pipelinedSend's apply-time Neutral coloring.
  | queueAtomicTxA actor ops =>
      simp only [execFullA] at h
      exact ⟨queueAtomicTxA_atomic_witness h, rfl⟩
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA] at h
      exact ⟨queuePipelineStepA_routing_witness h, rfl⟩
  | pipelinedSendA actor => exact rfl
  -- §MA-swiss: discharge each swiss effect's (REAL `stateAuthB` authority gate ∧ the catalog coloring).
  | exportSturdyRefA sw actor exporter target rights =>
      exact ⟨execFullA_exportSturdyRefA_authorized s s' sw actor exporter target rights h, rfl⟩
  | enlivenRefA sw actor exporter claimed =>
      exact ⟨execFullA_enlivenRefA_authorized s s' sw actor exporter claimed h, rfl⟩
  | swissHandoffA sw certHash introducer exporter =>
      exact ⟨execFullA_swissHandoffA_authorized s s' sw certHash introducer exporter h, rfl⟩
  | swissDropA sw actor exporter =>
      exact ⟨execFullA_swissDropA_authorized s s' sw actor exporter h, rfl⟩
  -- §MA-lifecycle (Wave-3): discharge each lifecycle/refresh effect's REAL `stateAuthB` self-gate ∧ coloring.
  | cellSealA actor cell => exact ⟨execFullA_cellSealA_authorized s s' actor cell h, rfl⟩
  | cellUnsealA actor cell => exact ⟨execFullA_cellUnsealA_authorized s s' actor cell h, rfl⟩
  | cellDestroyA actor cell ch => exact ⟨execFullA_cellDestroyA_authorized s s' actor cell ch h, rfl⟩
  | refreshDelegationA actor child => exact ⟨execFullA_refreshDelegationA_authorized s s' actor child h, rfl⟩

/-- **`execFullTurnA_each_attests` — PROVED.** Step-completeness holds at EVERY action of a committed
per-asset transaction, across all kinds: the per-node `fullActionInvA` witness threaded along the
all-or-nothing fold. The per-asset analog of `execFullTurn_each_attests` — the carrier the forest's
per-node attestation (`FullForest.execFullForestA_each_attests`) lifts off the bridge. -/
theorem execFullTurnA_each_attests :
    ∀ (s s' : RecChainedState) (tt : List FullActionA), execFullTurnA s tt = some s' →
      ∀ fa ∈ tt, ∃ sa sa', execFullA sa fa = some sa' ∧ fullActionInvA sa fa sa'
  | _, _, [], _, fa, hfa => absurd hfa List.not_mem_nil
  | s, s', a :: rest, h, b, hb => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          rcases List.mem_cons.mp hb with hbeq | hbrest
          · subst hbeq; exact ⟨s, s1, ha, execFullA_attests_per_asset ha⟩
          · exact execFullTurnA_each_attests s1 s' rest h b hbrest

/-! ## §11 — Axiom-hygiene tripwires (the honesty pins over the widened replacement's keystones). -/

#assert_axioms recKMint_delta
#assert_axioms recKBurn_delta
#assert_axioms recKMint_authorized
#assert_axioms recKBurn_authorized
#assert_axioms recKMint_unauthorized_fails
#assert_axioms recKBurn_unauthorized_fails
#assert_axioms mint_discloses
#assert_axioms burn_discloses
#assert_axioms execFull_ledger
#assert_axioms execFull_conserves
#assert_axioms execFull_balance_domain_conserves
#assert_axioms execFull_balance_authorized
#assert_axioms execFull_delegate_grounds
#assert_axioms execFull_mint_authorized
#assert_axioms execFull_burn_authorized
#assert_axioms execFull_delegate_addEdge
#assert_axioms execFull_delegate_grants_held_cap
#assert_axioms execFull_revoke_removeEdge
#assert_axioms execFull_chainlink
#assert_axioms execFull_obsadvance
#assert_axioms execFull_attests
#assert_axioms execFullTurn_ledger
#assert_axioms execFullTurn_conserves
#assert_axioms execFullTurn_each_attests
-- The PER-ASSET conservation-vector keystones (FILL 1, phase 2) over the executable turn:
#assert_axioms recBalCredit_recTotalAsset
#assert_axioms recKMintAsset_delta
#assert_axioms recKBurnAsset_delta
#assert_axioms recKMintAsset_authorized
#assert_axioms execFullA_ledger_per_asset
#assert_axioms execFullTurnA_ledger_per_asset
#assert_axioms execFullTurnA_conserves_per_asset
-- The per-asset PER-NODE attestation carrier (the forest lift, §MB) keystones:
#assert_axioms execFullTurnA_append
#assert_axioms execFullA_chainlink
#assert_axioms execFullA_obsadvance
#assert_axioms execFullA_balance_authorized
#assert_axioms execFullA_delegate_grounds
#assert_axioms execFullA_delegate_addEdge
#assert_axioms execFullA_delegate_grants_held_cap
#assert_axioms execFullA_revoke_removeEdge
#assert_axioms execFullA_mintA_authorized
#assert_axioms recKBurnAsset_authorized
#assert_axioms execFullA_burnA_authorized
#assert_axioms execFullA_attests_per_asset
#assert_axioms execFullTurnA_each_attests
-- META-FILL B Wave 1: the 5 PURE-STATE (field/log) effects on the per-asset dispatch.
-- The balance-NEUTRALITY keystone (a field/log write moves NO asset's supply) + the per-effect
-- authority gates + the (re-extended) per-asset spine arms all pinned kernel-clean.
#assert_axioms writeField_recTotalAsset
#assert_axioms stateStep_recTotalAsset
#assert_axioms emitStep_recTotalAsset
#assert_axioms emitStep_obsadvance
#assert_axioms execFullA_setFieldA_authorized
#assert_axioms execFullA_incrementNonceA_authorized
#assert_axioms execFullA_setPermissionsA_authorized
#assert_axioms execFullA_setVKA_authorized

-- §MA-seal (Wave 6): the 6 SIMPLE bal-neutral effects (seal/unseal/createSealPair/makeSovereign/
-- refusal/receiptArchive) — each a `stateStep` field write, balance-NEUTRAL (`recTotalAssetWithEscrow`
-- UNCHANGED ∀ asset), authority-gated (`stateAuthB` over the written cell). The §8 crypto (AEAD /
-- commitment) is the chain-layer portal, honestly NOT proved sound. The keystone
-- `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by construction
-- (FullForestA spine UNCHANGED — only `targetOf` gained arms).
#assert_axioms execFullA_sealA_authorized
#assert_axioms execFullA_unsealA_authorized
#assert_axioms execFullA_createSealPairA_authorized
#assert_axioms execFullA_makeSovereignA_authorized
#assert_axioms execFullA_refusalA_authorized
#assert_axioms execFullA_receiptArchiveA_authorized
-- FILL #133: MakeSovereign is a VALUE-REBIND (commitment-form), NOT a flag. The faithful kernel move
-- (`cells.remove(id)` + `sovereign_commitments.insert(id, cell.state_commitment())`) + its TEETH: the
-- readable balance/fields are GONE (a flag model CANNOT prove this), the commitment IS present and
-- binds the pre-state, and it stays bal-NEUTRAL on the per-asset ledger (`cell`-only ⇒ `bal` fixed).
#assert_axioms makeSovereignStep_factors
#assert_axioms makeSovereignKernel_recTotalAsset
#assert_axioms makeSovereignKernel_cell_eq
#assert_axioms makeSovereignStep_authorized
#assert_axioms makeSovereignStep_chainlink
#assert_axioms makeSovereignStep_balance_unreadable
#assert_axioms makeSovereignStep_fields_dropped
#assert_axioms makeSovereignStep_commitment_present
-- §MA-queue (Wave 7 de-THIN): the 4 REAL ring-buffer FIFO queue effects (queueAllocate/queueEnqueue/
-- queueDequeue/queueResize). Each carries its REAL `stateAuthB` authority gate over the queue cell
-- AND its bal-neutrality / chainlink — all pinned kernel-clean. The FIFO ORDER + capacity bound +
-- emptiness fail-closed are PROVED in `RecordKernel` (`qbuf_fifo_order` / `queueEnqueueK_full_rejects` /
-- `queueDequeueK_empty_rejects`, with their own `#assert_axioms`). The de-THIN content a flag-only
-- model lacks: NO order, NO bound. The keystone `execFullA_attests_per_asset` (re-extended above)
-- carries ALL into the forest by construction (FullForestA spine UNCHANGED — only `targetOf` gains arms).
#assert_axioms execFullA_queueAllocateA_authorized
#assert_axioms execFullA_queueEnqueueA_authorized
#assert_axioms execFullA_queueDequeueA_authorized
#assert_axioms execFullA_queueResizeA_authorized
#assert_axioms queueEnqueueChainA_balNeutral
#assert_axioms queueDequeueChainA_balNeutral
#assert_axioms queueEnqueueChainA_chainlink
-- WAVE 4: the ATOMIC batch (all-or-nothing fold) + the PIPELINE fan-out step + the committed-escrow
-- HONESTY (the §8 hiding portal making it DISTINCT from plain escrow). The atomicity, combined-
-- conservation, routing-witness, and fail-closed-without-hiding keystones pinned kernel-clean.
#assert_axioms queueAtomicTxChainA_balNeutral
#assert_axioms queueAtomicTxChainA_commits_iff_all
#assert_axioms queueAtomicTxChainA_head_fails
#assert_axioms queueAtomicTxA_balNeutral
#assert_axioms queueAtomicTxA_atomic_witness
#assert_axioms pipelineFanoutK_balNeutral
#assert_axioms queuePipelineStepA_balNeutral
#assert_axioms queuePipelineStepA_routing_witness
#assert_axioms createCommittedEscrowChainA_fails_without_hiding
#assert_axioms createCommittedEscrowChainA_combined_neutral
#assert_axioms createCommittedEscrowChainA_authorized
-- Wave-8 residual close: the REFUNDABLE anti-spam DEPOSIT on queue enqueue/dequeue. The deposit
-- GENUINELY moves the bare `recTotalAsset` (parked off-ledger) while the COMBINED measure is
-- CONSERVED (a refundable transfer-like move, NOT bal-neutral) — the wave-7 residual, closed.
#assert_axioms queueEnqueueDepositK_conserves_combined
#assert_axioms queueEnqueueDepositK_debits
#assert_axioms queueDequeueRefundK_conserves_combined
-- Wave-8 §MA-swiss: the 4 REAL CapTP swiss-table effects (export/enliven/handoff/drop) on the per-asset
-- dispatch. Each carries its REAL `stateAuthB actor exporter` authority gate over the exporting cell ∧
-- the catalog coloring; the membership / non-amplification / refcount-GC are PROVED in `RecordKernel`
-- (`swissExportK_amplification_rejects` / `swissEnlivenK_absent_rejects` / `swissEnlivenK_bumps_refcount`
-- / `swissDropK_gc_at_one`, with their own `#assert_axioms`). The de-THIN content a flag-shadow lacks.
#assert_axioms execFullA_exportSturdyRefA_authorized
#assert_axioms execFullA_enlivenRefA_authorized
#assert_axioms execFullA_swissHandoffA_authorized
#assert_axioms execFullA_swissDropA_authorized
#assert_axioms swissExportChainA_balNeutral
#assert_axioms swissEnlivenChainA_balNeutral
#assert_axioms swissHandoffChainA_balNeutral
#assert_axioms swissDropChainA_balNeutral
#assert_axioms swissExportChainA_chainlink
#assert_axioms swissEnlivenChainA_chainlink
-- META-FILL B Wave 2: the 6 DISTINCT AUTHORITY effects on the per-asset dispatch. The headline
-- NON-AMPLIFICATION (genuine `capAuthConferred ⊆` over the real `List Auth` lattice) + the
-- teeth (amplifying grant rejected) + grounding/addEdge/removeEdge/graph-unchanged graph moves,
-- all pinned kernel-clean. The keystone `execFullA_attests_per_asset` (re-extended above) carries
-- ALL of these into the forest by construction (FullForestA spine UNCHANGED).
#assert_axioms amplifyingF_rejected
#assert_axioms attenuateF_non_amplifying
#assert_axioms exerciseStepA_factors
#assert_axioms execFullA_introduceA_grounds
#assert_axioms execFullA_introduceA_addEdge
#assert_axioms execFullA_introduceA_holds_real_cap
#assert_axioms execFullA_introduceA_grants_held_cap
#assert_axioms execFullA_introduceA_non_amplifying
#assert_axioms execFullA_attenuateA_non_amplifying
#assert_axioms execFullA_attenuateA_confined
#assert_axioms execFullA_dropRefA_removeEdge
#assert_axioms execFullA_revokeDelegationA_removeEdge
#assert_axioms execFullA_validateHandoffA_grounds
#assert_axioms execFullA_validateHandoffA_addEdge
#assert_axioms execFullA_validateHandoffA_grants_held_cap
#assert_axioms execFullA_validateHandoffA_non_amplifying
#assert_axioms execFullA_delegateAttenA_grounds
#assert_axioms execFullA_delegateAttenA_grants
#assert_axioms execFullA_delegateAttenA_non_amplifying
#assert_axioms execFullA_exerciseA_authorized
#assert_axioms execFullA_exerciseA_recurses
#assert_axioms execInnerA_ledger_per_asset
#assert_axioms execFullA_log_suffix
#assert_axioms execInnerA_log_suffix
#assert_axioms execFullA_chainlinkExact
-- META-FILL C Wave 3: accounts-GROWTH (`createCell`/`spawn`, born EMPTY ⇒ conservation-NEUTRAL) +
-- the SUPPLY inflow (`bridgeMint`, §8-portal disclosed `+value` at ONE asset). The account-growth
-- NEUTRALITY keystone (`recTotalAsset` unchanged BECAUSE the fresh cell is born empty, the index set
-- genuinely grew) + the disclosed bridge inflow + the per-effect gates, all pinned kernel-clean. The
-- keystone `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by
-- construction (FullForestA spine UNCHANGED — only `targetOf` gains arms).
#assert_axioms recTotalAsset_insert_fresh
#assert_axioms createCellIntoAsset_grows_accounts
#assert_axioms createCellChainA_factors
#assert_axioms createCellChainA_neutral
#assert_axioms createCellChainA_grows_accounts
#assert_axioms createCellChainA_authorized
#assert_axioms createCellChainA_unauthorized_fails
#assert_axioms createCellChainA_chainlink
-- §MA-factory: the `CreateCellFromFactory` keystones (validation + program-install + frames).
#assert_axioms createCellFromFactoryChainA_factors
#assert_axioms createCellFromFactoryChainA_neutralWithEscrow
#assert_axioms createCellFromFactoryChainA_authorized
#assert_axioms createCellFromFactoryChainA_grows_accounts
#assert_axioms createCellFromFactoryChainA_installs_program
#assert_axioms createCellFromFactoryChainA_unknown_factory_fails
#assert_axioms createCellFromFactoryChainA_nonconforming_fails
#assert_axioms createCellFromFactoryChainA_balance_field_fails
#assert_axioms createCellFromFactoryChainA_caps_eq
#assert_axioms createCellFromFactoryChainA_sideTables
#assert_axioms spawnChainA_factors
#assert_axioms spawnChainA_neutral
#assert_axioms spawnChainA_authorized
#assert_axioms spawnChainA_grounds
#assert_axioms spawnChainA_provenance
#assert_axioms spawnChainA_parent_snapshot
#assert_axioms spawnChainA_chainlink
#assert_axioms execFullA_bridgeMintA_authorized
#assert_axioms execFullA_bridgeMintA_unauthorized_fails
#assert_axioms execFullA_createCellA_neutral_per_asset
#assert_axioms execFullA_createCellA_grows_accounts
#assert_axioms execFullA_spawnA_neutral_per_asset
#assert_axioms execFullA_bridgeMintA_discloses_per_asset
-- META-FILL C: the COMBINED per-asset escrow/note chained wrappers + the executed-dispatch obligations.
#assert_axioms createEscrowChainA_combined_neutral
#assert_axioms createEscrowChainA_bal_debits
#assert_axioms createEscrowChainA_bal_delta
#assert_axioms execFullA_createEscrowA_authorized
#assert_axioms execFullA_createObligationA_authorized
#assert_axioms execFullA_noteSpendA_inserts
#assert_axioms execFullA_noteCreateA_inserts
-- Wave-5 PHASE-BRIDGE: the cross-chain bridge lock/finalize/cancel on the SHARED escrow holding-store.
-- LOCK is COMBINED-conserving (bal debit offset by the holding-store park); FINALIZE is the disclosed
-- OUTFLOW (COMBINED DROPS by the disclosed -amount at the bridged asset — the value LEFT for the other
-- chain, like burn); CANCEL refunds the originator (combined conserved). The §8 confirmation receipt is
-- the THEOREM-level portal. The keystone `execFullA_attests_per_asset` (re-extended above) carries ALL of
-- these into the forest by construction (FullForestA spine UNCHANGED — only `targetOf` gains arms).
#assert_axioms bridge_lock_conserves_combined_per_asset
#assert_axioms bridge_lock_debits_per_asset
#assert_axioms bridgeLockKAsset_authorized
#assert_axioms bridge_finalize_moves_combined_per_asset
#assert_axioms bridgeFinalizeKAsset_moves_combined_per_asset
#assert_axioms bridge_cancel_conserves_combined_per_asset
#assert_axioms bridgeLockChainA_combined_neutral
#assert_axioms bridgeLockChainA_bal_debits
#assert_axioms bridgeFinalizeChainA_burns_combined
#assert_axioms bridgeCancelChainA_combined_neutral
#assert_axioms bridgeFinalizeChainA_nonCreator_rejects
#assert_axioms bridgeCancelChainA_nonCreator_rejects
#assert_axioms bridgeLockChainA_authorized
#assert_axioms execFullA_bridgeLockA_authorized
#assert_axioms execFullA_bridgeLockA_unauthorized_fails
#assert_axioms execFullA_bridgeFinalizeA_burns_per_asset
#assert_axioms execFullA_bridgeCancelA_conserves_per_asset
-- §MA-lifecycle (Wave-3) keystones: the lifecycle state machine + the de-shadowed seal cap-movement.
#assert_axioms cellSealChainA_nonlive_rejects
#assert_axioms cellDestroyChainA_terminal_rejects
#assert_axioms refreshDelegationChainA_noParent_rejects
#assert_axioms refreshDelegationChainA_snapshots_parent
#assert_axioms unsealChainA_grants_sealed_cap
#assert_axioms unsealChainA_noBox_rejects
#assert_axioms execFullA_cellSealA_authorized
#assert_axioms execFullA_refreshDelegationA_authorized

/-! ## §12 — Non-vacuity: each kind commits with the right invariant; unauthorized rejected.

Reuses `AuthTurn.rsCap` (delegator 0 holds a `node 7` cap) lifted to a `RecChainedState`, and a
minting state where actor 9 holds the privileged `node 0` cap. -/

/-- A chained record state: cells 0,1 with balances 100,5; actor 9 holds a `node 0` mint cap;
delegator 0 holds a `node 7` connectivity cap. Empty receipt chain. -/
def fs0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0]
                         else if l = 0 then [Cap.node 7] else [] }
    log := [] }

-- A DELEGATE turn commits (delegator 0 holds a `node 7` cap ⇒ can delegate connectivity to 7):
#eval (execFull fs0 (.delegate 0 1 7)).isSome                       -- true
-- ...is conservation-trivial (`recTotal` unchanged) and grows the chain by one:
#eval (execFull fs0 (.delegate 0 1 7)).map (fun s => recTotal s.kernel)  -- some 105 (FIXED)
#eval (execFull fs0 (.delegate 0 1 7)).map (fun s => s.log.length)       -- some 1
-- ...and recipient 1 now holds the `node 7` cap (the new authority edge):
#eval ((execFull fs0 (.delegate 0 1 7)).map (fun s => s.kernel.caps 1)).getD []  -- [Cap.node 7]
-- A delegator with no connectivity to the target cannot delegate it (fail-closed):
#eval (execFull fs0 (.delegate 5 1 9)).isSome                       -- false

-- A MINT turn commits (actor 9 holds the privileged `node 0` cap ⇒ may coin cell 0's supply):
#eval (execFull fs0 (.mint 9 0 50)).isSome                          -- true
-- ...raises `recTotal` by exactly +50 (disclosed non-conservation), chain grows by one:
#eval (execFull fs0 (.mint 9 0 50)).map (fun s => recTotal s.kernel)  -- some 155 (= 105 + 50)
#eval (execFull fs0 (.mint 9 0 50)).map (fun s => s.log.length)       -- some 1
-- ...and the minted receipt carries the disclosed delta +50:
#eval ((execFull fs0 (.mint 9 0 50)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0  -- 50
-- An actor without the privileged mint cap cannot mint (bare ownership is NOT enough):
#eval (execFull fs0 (.mint 0 0 50)).isSome                          -- false (actor 0 lacks `node 0`)

-- A BURN turn commits (actor 9 authorized; cell 0 has ≥ 40 balance):
#eval (execFull fs0 (.burn 9 0 40)).isSome                          -- true
-- ...lowers `recTotal` by exactly -40 (disclosed), chain grows by one:
#eval (execFull fs0 (.burn 9 0 40)).map (fun s => recTotal s.kernel)  -- some 65 (= 105 - 40)
-- Over-burn (more than available) is rejected (availability gate):
#eval (execFull fs0 (.burn 9 0 999)).isSome                         -- false
-- Unauthorized burn rejected:
#eval (execFull fs0 (.burn 0 0 10)).isSome                          -- false

-- A REVOKE turn always commits (it only subtracts authority) and is conservation-trivial:
#eval (execFull fs0 (.revoke 0 7)).isSome                           -- true
#eval (execFull fs0 (.revoke 0 7)).map (fun s => recTotal s.kernel)   -- some 105 (FIXED)
-- ...after which holder 0's `node 7` cap is gone:
#eval ((execFull fs0 (.revoke 0 7)).map (fun s => s.kernel.caps 0)).getD []  -- []

-- A BALANCE turn (reusing the catalog-typed `Action`) commits and conserves:
#eval (execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).isSome           -- true
#eval (execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).map (fun s => recTotal s.kernel)  -- some 105

-- A MIXED full-turn: mint +50, then transfer (conserves), then burn -50 → nets to 0, conserves.
def mixedTurn : List FullAction :=
  [ .mint 9 0 50
  , .balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩
  , .burn 9 0 50 ]

#eval (execFullTurn fs0 mixedTurn).isSome                           -- true (all-or-nothing commits)
#eval turnLedgerDelta mixedTurn                                     -- 0 (+50 +0 -50)
#eval (execFullTurn fs0 mixedTurn).map (fun s => recTotal s.kernel)   -- some 105 (CONSERVED: net 0)
#eval (execFullTurn fs0 mixedTurn).map (fun s => s.log.length)        -- some 3 (chain grew by count)

-- An all-or-nothing transaction with a bad action ROLLS BACK the whole turn:
def badMixedTurn : List FullAction :=
  [ .mint 9 0 50, .burn 0 0 10 ]   -- second action unauthorized ⇒ whole turn none
#eval (execFullTurn fs0 badMixedTurn).isSome                        -- false (rollback)

/-! ## §13 — Non-vacuity for the PER-ASSET executor: conservation holds, laundering is CAUGHT. -/

/-- A chained state with a genuine 2-asset `bal` ledger: cell 0 holds 100 of asset 0 and 7 of asset
1; cell 1 holds 5 of asset 0. Actor 9 holds the privileged `node 0` mint cap over cell 0. -/
def fma0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

#eval recTotalAsset fma0.kernel 0     -- 105 (asset 0 supply)
#eval recTotalAsset fma0.kernel 1     -- 7   (asset 1 supply)
-- A pure per-asset TRANSFER of asset 0 (actor 0 owns src 0) conserves BOTH assets:
#eval (execFullTurnA fma0 [.balanceA ⟨0, 0, 1, 30⟩ 0]).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))   -- some (105, 7)

/-- The scalar-LAUNDERING turn a single-aggregate kernel would WRONGLY accept as conserving: mint 50
of asset 1 while burning 50 of asset 0 (cell 0). Aggregate scalar delta = -50 + 50 = 0 ("conserved"
— the BUG). The per-asset VECTOR delta is nonzero in EACH asset, so it cannot be passed off as a
conservative turn. -/
def launderTurn : List FullActionA :=
  [ .mintA 9 0 1 50      -- +50 of asset 1
  , .burnA 9 0 0 50 ]    -- -50 of asset 0

#eval turnLedgerDeltaAsset launderTurn 0     -- -50 (NOT 0 — a scalar aggregate would hide this)
#eval turnLedgerDeltaAsset launderTurn 1     -- 50  (NOT 0)
-- the per-asset ledger AFTER the launder turn: asset 0 fell to 55, asset 1 rose to 57 (CAUGHT):
#eval (execFullTurnA fma0 launderTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))   -- some (55, 57)

/-! ## §13-state — Non-vacuity for the 5 PURE-STATE effects: the cell record/log moves, but
`recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); authority is REAL
(an unauthorized field write fails-closed); `emitEvent` is authority-FREE. -/

/-- A genuine 2-asset state whose cells ALSO carry a `nonce`/`status`/`permissions`/`verification_key`
record (so the pure-state field writes are OBSERVABLE). Cell 0 holds 100 of asset 0 + 7 of asset 1;
cell 1 holds 5 of asset 0. Empty cap table ⇒ authority is by OWNERSHIP (actor = cell). -/
def fmaS : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 0), ("nonce", .int 0),
                                                ("status", .int 0), ("permissions", .int 0),
                                                ("verification_key", .int 0)]
                         else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#eval (recTotalAsset fmaS.kernel 0, recTotalAsset fmaS.kernel 1)                     -- (105, 7)

-- ★ THE KEYSTONE WITNESS: a `setFieldA` that changes cell 0's `nonce` field to 42 COMMITS,
--   yet `recTotalAsset` is UNCHANGED at (105, 7) for BOTH assets (balance-NEUTRALITY):
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).isSome                            -- true
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map
        (fun s => fieldOf "nonce" (s.kernel.cell 0))                                 -- some 42 (CHANGED)
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (UNCHANGED)
-- ...and grows the receipt chain by exactly one row (the metadata clock):
#eval (execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map (fun s => s.log.length)       -- some 1
-- An UNAUTHORIZED actor (9 owns nothing, empty caps) cannot write cell 0's field (fail-closed):
#eval (execFullA fmaS (.setFieldA 9 0 "nonce" 42)).isSome                            -- false

-- IncrementNonce (Monotonic): bump cell 0's nonce 0→1, balance-neutral:
#eval (execFullA fmaS (.incrementNonceA 0 0 1)).map (fun s => fieldOf "nonce" (s.kernel.cell 0))  -- some 1
#eval (execFullA fmaS (.incrementNonceA 0 0 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)

-- SetPermissions / SetVerificationKey (Neutral): field writes, balance-neutral:
#eval (execFullA fmaS (.setPermissionsA 0 0 3)).map (fun s => fieldOf "permissions" (s.kernel.cell 0))  -- some 3
#eval (execFullA fmaS (.setVKA 0 0 99)).map (fun s => fieldOf "verification_key" (s.kernel.cell 0))     -- some 99
#eval (execFullA fmaS (.setVKA 0 0 99)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)

-- EmitEvent: authority-FREE (even actor 9, who owns nothing, commits — dregg1 runs NO cap check)
--   but cell-existence-gated; writes NO state, grows the chain by one, balance-neutral:
#eval (execFullA fmaS (.emitEventA 9 0 7 123)).isSome                                -- true (authority-free)
#eval (execFullA fmaS (.emitEventA 9 0 7 123)).map (fun s => s.log.length)           -- some 1
#eval (execFullA fmaS (.emitEventA 9 0 7 123)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)
-- Non-live event targets reject: no ghost-cell event rows.
#eval (execFullA fmaS (.emitEventA 9 99 7 123)).isSome                               -- false

-- A MIXED per-asset turn interleaving pure-state effects with a transfer: ALL balance-neutral
--   (the transfer conserves; the field writes/emit move no asset) ⇒ (105, 7) preserved:
def stateMixedTurn : List FullActionA :=
  [ .setFieldA 0 0 "status" 5
  , .balanceA ⟨0, 0, 1, 30⟩ 0     -- transfer 30 of asset 0, cell 0 → cell 1 (conserves)
  , .incrementNonceA 0 0 1
  , .emitEventA 0 0 1 0
  , .setVKA 0 0 7 ]

#eval (execFullTurnA fmaS stateMixedTurn).isSome                                     -- true (all commit)
#eval (turnLedgerDeltaAsset stateMixedTurn 0, turnLedgerDeltaAsset stateMixedTurn 1) -- (0, 0)
#eval (execFullTurnA fmaS stateMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (CONSERVED)
#eval (execFullTurnA fmaS stateMixedTurn).map (fun s => s.log.length)                -- some 5 (chain grew by node count)

/-! ## §13-auth — Non-vacuity for the 6 DISTINCT AUTHORITY effects: the cap-graph moves (or is
checked), but `recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); the
HEADLINE non-amplification has TEETH (an attenuation STRICTLY drops a right; an amplifying grant is
REJECTED); fail-closed (introduce/exercise without held connectivity ⇒ none). -/

/-- A 2-asset state whose actor 0 ALSO holds REAL caps: `node 7` (connectivity, for introduce/
exercise/handoff to target 7) and `endpoint 9 [read, write]` (rights-carrying, for attenuation
teeth; the `write` makes it confer connectivity to 9 too). Asset 0 = 105, asset 1 = 7. -/
def fmaA : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 7, Cap.endpoint 9 [Auth.read, Auth.write]] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#eval (recTotalAsset fmaA.kernel 0, recTotalAsset fmaA.kernel 1)                      -- (105, 7)

-- (1) INTRODUCE: actor 0 (holds `node 7`) introduces recipient 1 to target 7. COMMITS, and
--   `recTotalAsset` is UNCHANGED in BOTH assets (caps change, bal does NOT — balance-NEUTRALITY):
#eval (execFullA fmaA (.introduceA 0 1 7)).isSome                                     -- true
#eval (execFullA fmaA (.introduceA 0 1 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (UNCHANGED)
-- ...and recipient 1 now holds the `node 7` cap (the new authority EDGE — caps DID move):
#eval ((execFullA fmaA (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []   -- [Cap.node 7]
-- An introducer with NO connectivity to the target cannot introduce it (FAIL-CLOSED ⇒ none):
#eval (execFullA fmaA (.introduceA 5 1 7)).isSome                                     -- false

/-- Actor 0 holds only endpoint-write connectivity to target 7. -/
def fmaEndpointIntro : RecChainedState :=
  { fmaA with
    kernel := { fmaA.kernel with
      caps := fun l => if l = 0 then [Cap.endpoint 7 [Auth.write]] else [] } }

-- INTRODUCE from an endpoint witness copies the endpoint cap; it does not upgrade to `node`/control.
#eval ((execFullA fmaEndpointIntro (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []
-- [Cap.endpoint 7 [Auth.write]]

-- (1') THE TEETH — genuine rights NON-AMPLIFICATION over the real `List Auth` lattice.
-- Attenuating the held `endpoint 9 [read, write]` to keep only `[read]` STRICTLY DROPS `write`:
#eval capAuthConferred (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write]))  -- [read] ⊊ [read,write]
-- the genuine non-amplification fires on this concrete held cap (granted ⊆ held, REAL rights):
example : IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write])
    (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])) :=
  attenuateF_non_amplifying [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])
-- ...and an AMPLIFYING grant is genuinely REJECTED: a `node 9` cap confers `control`, which the
-- held `endpoint 9 [read, write]` cap does NOT confer ⇒ it FAILS the non-amplification predicate:
example : ¬ IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9) :=
  amplifyingF_rejected (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9)
    Auth.control (by decide) (by decide)

-- (2) ATTENUATE: narrow actor 0's slot-1 cap (`endpoint 9 [read, write]`) to keep only `read`.
--   COMMITS, balance-neutral, and the slot's cap is genuinely narrowed:
#eval (execFullA fmaA (.attenuateA 0 1 [Auth.read])).isSome                           -- true
#eval ((execFullA fmaA (.attenuateA 0 1 [Auth.read])).map (fun s => s.kernel.caps 0)).getD []
--                                                       -- [node 7, endpoint 9 [read]] (write DROPPED)
#eval (execFullA fmaA (.attenuateA 0 1 [Auth.read])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (UNCHANGED)

-- (3) DROP-REF: holder 0 GC-drops its reference to 7. Always commits, balance-neutral, edge gone:
#eval (execFullA fmaA (.dropRefA 0 7)).isSome                                         -- true
#eval (execFullA fmaA (.dropRefA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)

-- (4) REVOKE-DELEGATION: parent drops child 0's edge to 7. Always commits, balance-neutral:
#eval (execFullA fmaA (.revokeDelegationA 0 7)).isSome                                -- true
#eval (execFullA fmaA (.revokeDelegationA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)

-- (5) VALIDATE-HANDOFF: actor 0 (holds connectivity to 7) accepts the graph-level consequence of a
--   handoff introducing 1 to 7. COMMITS (the handoff consequence IS a Granovetter introduce),
--   balance-neutral. A handoff consequence with no held source connectivity is REJECTED ⇒ none:
#eval (execFullA fmaA (.validateHandoffA 0 1 7)).isSome                               -- true
#eval (execFullA fmaA (.validateHandoffA 0 1 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7)
#eval ((execFullA fmaEndpointIntro (.validateHandoffA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []
-- [Cap.endpoint 7 [Auth.write]]
#eval (execFullA fmaA (.validateHandoffA 5 1 7)).isSome                               -- false (FAIL-CLOSED)

-- (6) EXERCISE (DE-SHADOWED): actor 0 (holds `node 7`) exercises its cap to target 7 to RUN inner
--   effects against it (dregg1 `apply.rs:2647`: each inner effect applied against the cap's target).
--   The inner effect (an `emitEvent` against 7) GENUINELY RUNS — the log grows by 2 (the exercise's
--   own receipt + the inner emit receipt), proving it is NO LONGER a no-op shadow. An actor without
--   the held edge FAILS-CLOSED; a FAILING inner effect aborts the whole exercise (fail-closed):
#eval (execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).isSome                 -- true
#eval ((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).map (fun s => s.log.length)).getD 0
--                                                       -- 2 (exercise receipt + INNER emit receipt RAN)
#eval (execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (bal-neutral inner)
-- a committed exercise carrying a balance-MOVING inner (mint 3 of asset 1 into a live cell, by an actor
--   that holds the privileged `node`-cap): the inner mint actually CREDITS — combined delta sums the inner.
#eval (execFullA fmaA (.exerciseA 0 7 [])).isSome                                     -- true (empty inner: pure hold-check)
#eval ((execFullA fmaA (.exerciseA 0 7 [])).map (fun s => s.log.length)).getD 0       -- 1 (only the exercise receipt)
#eval (execFullA fmaA (.exerciseA 5 7 [.emitEventA 0 7 99 1])).isSome                 -- false (FAIL-CLOSED: no held edge)

-- A MIXED authority turn: introduce (adds edge) + attenuate (narrows) + exercise (RUNS inner emit) +
--   revoke-delegation (removes) — ALL balance-neutral ⇒ (105, 7) preserved across the turn:
def authMixedTurn : List FullActionA :=
  [ .introduceA 0 1 7
  , .attenuateA 0 1 [Auth.read]
  , .exerciseA 0 7 [.emitEventA 0 7 99 1]
  , .revokeDelegationA 0 7 ]

#eval (execFullTurnA fmaA authMixedTurn).isSome                                       -- true (all commit)
#eval (turnLedgerDeltaAsset authMixedTurn 0, turnLedgerDeltaAsset authMixedTurn 1)    -- (0, 0)
#eval (execFullTurnA fmaA authMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))               -- some (105, 7) (CONSERVED)

/-! ## §13-supply (META-FILL C Wave 3) — Non-vacuity for ACCOUNT-GROWTH + SUPPLY: `createCell` GROWS
`accounts` yet `recTotalAsset` is UNCHANGED (born EMPTY ⇒ NEUTRAL); `bridgeMint` discloses `+value` at
ONE asset and leaves every other asset FIXED (no cross-asset laundering); unauthorized create/mint
FAIL-CLOSED. A 2-asset state where actor 9 holds the privileged `node 0`/`node 1`/`node 2` caps (can mint
into live cells 0,1 and create the fresh cell 2). -/

/-- The supply fixture: accounts {0,1}; cell 0 = 100 of asset 0 + 7 of asset 1, cell 1 = 5 of asset 0.
Actor 9 holds `node 0`,`node 1`,`node 2` (create/mint authority over cells 0,1 and the fresh 2). -/
def fmaSup : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply + account set: asset 0 = 105, asset 1 = 7, accounts {0,1}.
#eval (recTotalAsset fmaSup.kernel 0, recTotalAsset fmaSup.kernel 1)                  -- (105, 7)
#eval (decide (0 ∈ fmaSup.kernel.accounts), decide (1 ∈ fmaSup.kernel.accounts),
       decide (2 ∈ fmaSup.kernel.accounts))                                          -- (true, true, false)

-- ★ THE ACCOUNT-GROWTH WITNESS: actor 9 (holds `node 2`) creates the FRESH cell 2 — COMMITS,
--   `accounts` GROWS {0,1} → {0,1,2} (cell 2 now live), YET `recTotalAsset` is UNCHANGED at (105, 7)
--   for BOTH assets (born EMPTY ⇒ conservation-NEUTRAL):
#eval (execFullA fmaSup (.createCellA 9 2)).isSome                                    -- true
#eval (execFullA fmaSup (.createCellA 9 2)).map (fun s => decide (2 ∈ s.kernel.accounts))  -- some true (GREW)
#eval (execFullA fmaSup (.createCellA 9 2)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (NEUTRAL)
-- ...and the fresh cell 2 is born EMPTY in every asset (bal-reset):
#eval (execFullA fmaSup (.createCellA 9 2)).map (fun s => (s.kernel.bal 2 0, s.kernel.bal 2 1))  -- some (0, 0)
-- ...and grows the receipt chain by exactly one row:
#eval (execFullA fmaSup (.createCellA 9 2)).map (fun s => s.log.length)               -- some 1
-- An UNAUTHORIZED creator (actor 0 holds no create cap) is REJECTED (fail-closed):
#eval (execFullA fmaSup (.createCellA 0 2)).isSome                                    -- false
-- A NON-FRESH id (cell 1 already live) is REJECTED (the freshness gate has TEETH):
#eval (execFullA fmaSup (.createCellA 9 1)).isSome                                    -- false

-- SPAWN: child creation alone cannot mint authority to an unheld/non-live target:
#eval (execFullA fmaSup (.spawnA 9 2 7)).isSome                                       -- false
-- ...but actor 9 can spawn child 2 (born EMPTY) with a COPY of its held parent `node 1` cap — COMMITS,
--   NEUTRAL, and the child carries the concrete copied parent cap (`node 1`):
#eval (execFullA fmaSup (.spawnA 9 2 1)).isSome                                       -- true
#eval (execFullA fmaSup (.spawnA 9 2 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (NEUTRAL)
#eval ((execFullA fmaSup (.spawnA 9 2 1)).map (fun s => s.kernel.caps 2)).getD []     -- [Cap.node 1]
#eval (execFullA fmaSup (.spawnA 9 2 1)).map (fun s => decide (2 ∈ s.kernel.accounts))  -- some true (GREW)
#eval (execFullA fmaSup (.spawnA 9 2 1)).map
        (fun s => (s.kernel.delegate 2, s.kernel.delegations 2))                    -- some (some 9, [Cap.node 0, Cap.node 1, Cap.node 2])
#eval ((execFullA fmaSup (.spawnA 9 2 1)).bind
        (fun s => execFullA s (.refreshDelegationA 2 2))).isSome                    -- true (spawn initialized parent)

-- ★ THE BRIDGE-MINT DISCLOSURE WITNESS: actor 9 (holds `node 0`) bridge-mints +40 of ASSET 1 into the
--   live cell 0 — COMMITS, asset 1 RISES by exactly 40 (7 → 47) while asset 0 is LEFT FIXED (105):
#eval (execFullA fmaSup (.bridgeMintA 9 0 1 40)).isSome                               -- true
#eval (execFullA fmaSup (.bridgeMintA 9 0 1 40)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 47) (+40 at asset 1 ONLY)
-- ...the disclosed delta is `+40` at asset 1, `0` everywhere else (no cross-asset laundering):
#eval (ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 0, ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 1)  -- (0, 40)
-- ...and the bridge receipt discloses the +40 inflow:
#eval ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0  -- 40
-- An UNAUTHORIZED bridge-mint (actor 0, no mint cap) is REJECTED (the LOCAL gate, independent of the
--   §8 foreign-finality portal):
#eval (execFullA fmaSup (.bridgeMintA 0 0 1 40)).isSome                               -- false

-- A MIXED supply turn: createCell 2 (neutral growth) + bridgeMint +40 of asset 1 into cell 0
--   (disclosed) → asset 0 conserved (105), asset 1 rises by exactly 40 (7 → 47):
def supplyMixedTurn : List FullActionA :=
  [ .createCellA 9 2
  , .bridgeMintA 9 0 1 40 ]

#eval (execFullTurnA fmaSup supplyMixedTurn).isSome                                   -- true (all commit)
#eval (turnLedgerDeltaAsset supplyMixedTurn 0, turnLedgerDeltaAsset supplyMixedTurn 1)  -- (0, 40)
#eval (execFullTurnA fmaSup supplyMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 47)

/-! ### §MA-escrow #eval — the COMBINED per-asset holding-store on the executed dispatch (`META-FILL C`,
closing `#121`): a committed-escrow lock+settle conserves `recTotalAssetWithEscrow` per-asset (with the
held value genuinely non-zero at the locked asset, the OTHER asset untouched); noteCreate→noteSpend
round-trip; double-spend fail-closed. -/

-- ★ COMMITTED-ESCROW LOCK of 5 of ASSET 1 from cell 0 (holds 7 of asset 1) → recipient 1 (id 9),
--   actor 9 authorized over 0, §8 HIDING PORTAL HELD (hidingProof = true): bare ledger DROPS at asset 1
--   (7→2), held RISES to 5, COMBINED FIXED at 7.
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 true)).isSome             -- true
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 true)).map
        (fun s => (recTotalAsset s.kernel 1, escrowHeldAsset s.kernel 1))             -- some (2, 5) — bare DOWN, held UP at asset 1
-- ...the COMBINED per-asset measure is CONSERVED at asset 1 AND asset 0 (no cross-asset laundering):
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 true)).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0))  -- some (7, 105) — CONSERVED both
-- ...the COMBINED ledgerDeltaAsset is 0 at every asset (combined-conserving, NOT bare-bal-conserving):
#eval (ledgerDeltaAsset (.createCommittedEscrowA 9 9 0 1 1 5 true) 0,
       ledgerDeltaAsset (.createCommittedEscrowA 9 9 0 1 1 5 true) 1)                 -- (0, 0)
-- ★ SETTLE (release to recipient 1, live): COMBINED stays (105, 7), held returns to 0.
#eval ((execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 true)).bind
        (fun s => execFullA s (.releaseCommittedEscrowA 9 9))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0,
                   escrowHeldAsset s.kernel 1))                                       -- some (7, 105, 0) — round-trip CONSERVED
-- ...the held value at asset 1 is GENUINELY non-zero mid-flight while asset 0 is untouched (guard):
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 true)).map
        (fun s => (escrowHeldAsset s.kernel 1, escrowHeldAsset s.kernel 0))           -- some (5, 0)
-- ★★ WAVE 4 HONESTY TEETH — the committed escrow is DISTINGUISHABLE from plain escrow: WITHOUT the §8
--   hiding portal (hidingProof = FALSE) the committed create is REJECTED (the privacy boundary plain
--   escrow LACKS), even though the IDENTICAL plain escrow with the same params COMMITS:
#eval (execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 false)).isSome            -- false — HIDING PORTAL fail-closed
#eval (execFullA fmaSup (.createEscrowA 9 9 0 1 1 5)).isSome                           -- true — plain escrow has NO hiding gate
-- ...so committed (no portal) and plain are NOT silently identical — exactly the WAVE 4 obligation:
#eval ((execFullA fmaSup (.createCommittedEscrowA 9 9 0 1 1 5 false)).isSome,
       (execFullA fmaSup (.createEscrowA 9 9 0 1 1 5)).isSome)                         -- (false, true) — DISTINGUISHED
-- ★ NOTE CREATE→SPEND round-trip: create grows commitments (42), spend grows nullifiers (77) — distinct sets;
--   the executed dispatch is bal-NEUTRAL (combined fixed):
#eval ((execFullA fmaSup (.noteCreateA 42 9)).bind (fun s => execFullA s (.noteSpendA 77 9))).map
        (fun s => (s.kernel.commitments.contains 42, s.kernel.nullifiers.contains 77,
                   recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1))  -- some (true, true, 105, 7)
-- ★ DOUBLE-SPEND fail-closed: spending nullifier 77 twice on the executed dispatch REJECTS:
#eval ((execFullA fmaSup (.noteSpendA 77 9)).bind (fun s => execFullA s (.noteSpendA 77 9))).isSome  -- false

/-! ### §MA-bridge #eval (Wave-5 PHASE-BRIDGE) — the cross-chain bridge lock/finalize/cancel on the
executed dispatch over the SHARED escrow holding-store. LOCK conserves the COMBINED measure (debit + park
the bridge-tagged record); FINALIZE BURNS it (the value LEFT for the other chain — COMBINED DROPS by the
disclosed amount at the bridged asset, the OTHER asset fixed); CANCEL refunds (combined conserved);
unauthorized/double-finalize fail-closed. `fmaSup`: cell 0 holds 100 of asset 0 + 7 of asset 1; actor 9
holds `node 0` (authority over cell 0). -/

-- ★ BRIDGE LOCK of 30 of ASSET 1 from cell 0 → destination 1 (bridge id 7), actor 9 authorized over 0:
--   bare ledger DROPS at asset 1 (7→ wait: cell0 has 7 of asset1, lock 5), held RISES, COMBINED FIXED.
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).isSome                              -- true
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).map
        (fun s => (recTotalAsset s.kernel 1, escrowHeldAsset s.kernel 1))              -- some (2, 5) — bare DOWN, held UP at asset 1
-- ...the COMBINED per-asset measure is CONSERVED at asset 1 AND asset 0 (the lock is combined-neutral):
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0))  -- some (7, 105) — CONSERVED both
-- ...the parked record carries the BRIDGE tag (it is in the SHARED escrow store, tagged true):
#eval (execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).map
        (fun s => s.kernel.escrows.map (fun r => (r.id, r.amount, r.asset, r.bridge)))  -- some [(7, 5, 1, true)]
-- ...the LOCK's COMBINED ledgerDeltaAsset is 0 at every asset (combined-conserving):
#eval (ledgerDeltaAsset (.bridgeLockA 7 9 0 1 1 5) 0, ledgerDeltaAsset (.bridgeLockA 7 9 0 1 1 5) 1)  -- (0, 0)
-- ★ LOCK then CANCEL (refund to originator 0, live): COMBINED stays (105, 7); held returns to 0; the
--   bare bal at asset 1 returns to 7 (the value came BACK):
#eval ((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeCancelA 7 9))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0,
                   escrowHeldAsset s.kernel 1, recTotalAsset s.kernel 1))             -- some (7, 105, 0, 7) — REFUND round-trip CONSERVED
-- ★ LOCK then FINALIZE (the §8 confirmation arrived — the value LEFT for the other chain): COMBINED
--   DROPS by exactly 5 at asset 1 (7→2), asset 0 FIXED at 105; held drops to 0; bare bal stays at 2:
#eval ((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 5))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 1, recTotalAssetWithEscrow s.kernel 0,
                   escrowHeldAsset s.kernel 1, recTotalAsset s.kernel 1))             -- some (2, 105, 0, 2) — COMBINED -5 at asset 1, asset 0 FIXED
-- ...the FINALIZE's disclosed delta is -5 at asset 1, 0 at asset 0 (the disclosed OUTFLOW, no laundering):
#eval (ledgerDeltaAsset (.bridgeFinalizeA 7 9 1 5) 0, ledgerDeltaAsset (.bridgeFinalizeA 7 9 1 5) 1)  -- (0, -5)
-- DOUBLE-FINALIZE fail-closed (the record is already resolved):
#eval (((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 5))).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 5))).isSome                      -- false
-- MISMATCHED-amount finalize fail-closed (disclosed 99 ≠ parked 5 — the receipt-vs-pending check):
#eval ((execFullA fmaSup (.bridgeLockA 7 9 0 1 1 5)).bind
        (fun s => execFullA s (.bridgeFinalizeA 7 9 1 99))).isSome                     -- false
-- UNAUTHORIZED lock fail-closed (actor 0 holds no authority over... actually owns itself; use actor 5):
#eval (execFullA fmaSup (.bridgeLockA 7 5 0 1 1 5)).isSome                             -- false (actor 5 unauthorized over cell 0)
-- A MIXED bridge turn: lock 5 of asset 1 then finalize it → asset 1 net -5 (7→2), asset 0 conserved:
def bridgeMixedTurn : List FullActionA :=
  [ .bridgeLockA 7 9 0 1 1 5
  , .bridgeFinalizeA 7 9 1 5 ]

#eval (execFullTurnA fmaSup bridgeMixedTurn).isSome                                    -- true (all commit)
#eval (turnLedgerDeltaAsset bridgeMixedTurn 0, turnLedgerDeltaAsset bridgeMixedTurn 1) -- (0, -5)
#eval (execFullTurnA fmaSup bridgeMixedTurn).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1))  -- some (105, 2) — asset 0 fixed, asset 1 -5

/-! ## §13-seal (Wave 6) — Non-vacuity for the 6 SIMPLE bal-neutral effects: the cell flag/metadata/
refusal record MOVES (a flag genuinely flips), yet `recTotalAsset` is UNCHANGED in EVERY asset
(balance-NEUTRALITY witnessed by an `#eval`); authority is REAL (an unauthorized actor fails-closed);
the §8 crypto (AEAD for seal/unseal, the commitment for makeSovereign) is the HONEST chain-layer
portal — NOT exercised here, NEVER faked sound. -/

-- Reuse `fmaS` (cell 0 carries a record; empty caps ⇒ authority by OWNERSHIP, actor = cell).
-- Pre-state per-asset supply: asset 0 = 105, asset 1 = 7.

-- ★ WAVE-3 DE-SHADOW: seal/unseal/createSealPair now MOVE capabilities through a real box — NOT a flag.
-- `fmaW3` gives cell 0 a SEALER cap for pair 5 and an UNSEALER cap (so it can seal AND unseal), plus a
-- delegation parent (cell 0 is the parent of child 1) for refresh. Asset 0 = 105, asset 1 = 7 (as fmaS).
def fmaW3 : RecChainedState :=
  { kernel :=
      { fmaS.kernel with
        caps := fun l => if l = 0 then [sealerCap 5, unsealerCap 5] else []
        delegate := fun c => if c = 1 then some 0 else none }   -- child 1's parent is cell 0
    log := [] }

-- CreateSealPair: GRANT a sealer cap to holder 0 AND an unsealer cap to holder 1 — TWO real c-list
-- grants (NOT a `seal_pair := 1` flag). Authority over `sealerHolder` (cell 0 owns itself):
#eval (execFullA fmaS (.createSealPairA 5 0 0 1)).isSome                              -- true
#eval (execFullA fmaS (.createSealPairA 5 0 0 1)).map (fun s => (s.kernel.caps 0).length)  -- some 1 (sealer cap granted)
#eval (execFullA fmaS (.createSealPairA 5 0 0 1)).map (fun s => (s.kernel.caps 1).length)  -- some 1 (unsealer cap granted)
#eval (execFullA fmaS (.createSealPairA 5 0 0 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (bal-NEUTRAL)
#eval (execFullA fmaS (.createSealPairA 5 9 0 1)).isSome                              -- false (FAIL-CLOSED: 9 ∤ 0)

-- Seal: cell 0 HOLDS the sealer cap for pair 5, so it can SEAL a payload cap (here `Cap.node 42`) into a
-- box bound to pair 5 — the box BINDS the SPECIFIC cap (REAL). Balance-NEUTRAL:
#eval (execFullA fmaW3 (.sealA 5 0 (Cap.node 42))).isSome                             -- true
#eval (execFullA fmaW3 (.sealA 5 0 (Cap.node 42))).map (fun s => s.kernel.sealedBoxes.length)  -- some 1 (BOX STORED)
#eval (execFullA fmaW3 (.sealA 5 0 (Cap.node 42))).map
        (fun s => (findSealedBox s.kernel.sealedBoxes 5).map (·.payload))            -- some (some (Cap.node 42)) (THE cap)
#eval (execFullA fmaW3 (.sealA 5 0 (Cap.node 42))).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (bal-NEUTRAL)
-- FAIL-CLOSED: a cell NOT holding the sealer cap for pair 5 (cell 9, empty caps) cannot seal:
#eval (execFullA fmaW3 (.sealA 5 9 (Cap.node 42))).isSome                             -- false (CapabilityNotHeld)

-- ★ WAVE-3 NON-VACUITY: UNSEAL actually GRANTS the sealed cap to the recipient. Seal `Cap.node 42`
-- into pair 5, then unseal to recipient 1 — recipient 1 ends up HOLDING `Cap.node 42` (the cap MOVED
-- through the box; a flag could NEVER witness this):
def fmaW3Sealed : Option RecChainedState := execFullA fmaW3 (.sealA 5 0 (Cap.node 42))
#eval (fmaW3Sealed.bind (fun s => execFullA s (.unsealA 5 0 1))).map
        (fun s => s.kernel.caps 1)                                                   -- some [Cap.node 42] (CAP MOVED TO RECIPIENT)
#eval (fmaW3Sealed.bind (fun s => execFullA s (.unsealA 5 0 1))).map
        (fun s => (s.kernel.caps 1).contains (Cap.node 42))                          -- some true (recipient HOLDS the sealed cap)
-- FAIL-CLOSED: unseal of a pair with NO box returns none (the cap must genuinely have been sealed):
#eval (execFullA fmaW3 (.unsealA 5 0 1)).isSome                                       -- false (no box for pair 5)
-- FAIL-CLOSED: a cell NOT holding the unsealer cap cannot unseal even an existing box:
#eval (fmaW3Sealed.bind (fun s => execFullA s (.unsealA 5 9 1))).isSome               -- false (CapabilityNotHeld)

-- ★ WAVE-3 NON-VACUITY: the cell LIFECYCLE state machine. Seal cell 0 (Live→Sealed), then a destroyed
-- cell REJECTS a follow-on effect (terminal). First, a Live cell seals; a Sealed cell's seal-gate FIRES:
#eval (execFullA fmaS (.cellSealA 0 0)).isSome                                        -- true (Live→Sealed)
#eval (execFullA fmaS (.cellSealA 0 0)).map (fun s => s.kernel.lifecycle 0)           -- some 1 (Sealed)
-- a SEALED cell's lifecycle gate FIRES: it rejects a SECOND seal (AlreadySealed):
#eval ((execFullA fmaS (.cellSealA 0 0)).bind (fun s => execFullA s (.cellSealA 0 0))).isSome  -- false (gate fires)
-- but a SEALED cell CAN be unsealed (Sealed→Live) or destroyed (seal is the prelude to destruction):
#eval ((execFullA fmaS (.cellSealA 0 0)).bind (fun s => execFullA s (.cellUnsealA 0 0))).map
        (fun s => s.kernel.lifecycle 0)                                              -- some 0 (back to Live)
-- ★ A DESTROYED cell is TERMINAL — it REJECTS a follow-on effect. Destroy cell 0 (binds cert 777):
#eval (execFullA fmaS (.cellDestroyA 0 0 777)).map (fun s => s.kernel.lifecycle 0)    -- some 3 (Destroyed)
#eval (execFullA fmaS (.cellDestroyA 0 0 777)).map (fun s => s.kernel.deathCert 0)    -- some 777 (cert bound into final state)
-- a DESTROYED cell rejects a follow-on seal/unseal/destroy (terminal — no further transition):
#eval ((execFullA fmaS (.cellDestroyA 0 0 777)).bind (fun s => execFullA s (.cellSealA 0 0))).isSome     -- false
#eval ((execFullA fmaS (.cellDestroyA 0 0 777)).bind (fun s => execFullA s (.cellDestroyA 0 0 888))).isSome  -- false (terminal)
-- FAIL-CLOSED: an unauthorized actor cannot drive the lifecycle:
#eval (execFullA fmaS (.cellSealA 9 0)).isSome                                        -- false

-- ★ WAVE-3 NON-VACUITY: refreshDelegation SNAPSHOTS the parent's CURRENT c-list. Child 1's parent is
-- cell 0 (which holds [sealerCap 5, unsealerCap 5]); refresh writes that snapshot into child 1's delegation:
#eval (execFullA fmaW3 (.refreshDelegationA 1 1)).isSome                              -- true (self-authorized, has parent 0)
#eval (execFullA fmaW3 (.refreshDelegationA 1 1)).map (fun s => (s.kernel.delegations 1).length)  -- some 2 (parent's 2 caps snapshotted)
-- FAIL-CLOSED: a cell with NO parent (cell 0, delegate = 0) cannot refresh:
#eval (execFullA fmaW3 (.refreshDelegationA 0 0)).isSome                              -- false (no parent)

-- ★ FILL #133 — MakeSovereign is a VALUE-REBIND, not a flag. dregg1's `make_sovereign` REMOVES the
--   readable cell (`cells.remove(id)`) and keeps ONLY a 32-byte commitment (`sovereign_commitments`).
--   The rebound cell carries the commitment-only record; the host can NO LONGER read its state.
-- (a) it commits (the self-sovereign authority gate holds: actor = cell = owner):
#eval (execFullA fmaS (.makeSovereignA 0 0)).isSome                                  -- true
-- (b) ★ THE TEETH: the pre-state `balance` is NO LONGER directly readable — the record was DROPPED
--     behind the commitment (a flag model leaves it readable; this is the §8-portal boundary):
#eval (execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => Value.scalar (s.kernel.cell 0) "balance")                          -- some none (UNREADABLE)
#eval (execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => ((s.kernel.cell 0).field "nonce", (s.kernel.cell 0).field "permissions"))  -- some (none, none) (ALL DROPPED)
-- (c) the COMMITMENT is present — a digest of the FULL pre-state value (`cell.state_commitment()`):
#eval (execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => (s.kernel.cell 0).field "commitment")                             -- some (some (Value.dig …)) (PRESENT)
#eval ((fmaS.kernel.cell 0) |> stateCommitment, sovereignRebind fmaS.kernel.cell 0 0)  -- the rebound record IS commitment-only
-- ...and DISTINCT pre-states give DISTINCT commitments (the binding is a function of the whole value):
#eval (stateCommitment (.record [("balance", .int 0)]) == stateCommitment (.record [("balance", .int 1)]))  -- false (binds value)
-- (d) bal-NEUTRAL on the per-asset ledger (the value moves behind the commitment on the HOST, not the
--     per-asset supply — `recTotalAsset` reads `bal`, independent of the rebound `cell` record):
#eval (execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (SUPPLY PRESERVED)
-- (e) FAIL-CLOSED: an unauthorized actor (9 owns nothing) cannot make cell 0 sovereign:
#eval (execFullA fmaS (.makeSovereignA 9 0)).isSome                                  -- false (FAIL-CLOSED)

-- Refusal: write the `refusal` audit record (dregg1 bumps nonce + records commitment; NEVER touches
--   balance/caps/value), balance-neutral:
#eval (execFullA fmaS (.refusalA 0 0)).map (fun s => fieldOf "refusal" (s.kernel.cell 0))  -- some 1
#eval (execFullA fmaS (.refusalA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)
#eval (execFullA fmaS (.refusalA 9 0)).isSome                                        -- false (FAIL-CLOSED)

-- ReceiptArchive: transition the `lifecycle` field to Archived (a log/prune op), balance-neutral:
#eval (execFullA fmaS (.receiptArchiveA 0 0)).map (fun s => fieldOf "lifecycle" (s.kernel.cell 0))  -- some 1
#eval (execFullA fmaS (.receiptArchiveA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)
#eval (execFullA fmaS (.receiptArchiveA 9 0)).isSome                                 -- false (FAIL-CLOSED)

-- Every seal/lifecycle/refresh effect's per-asset ledgerDelta is 0 at every asset (balance-NEUTRAL):
#eval (ledgerDeltaAsset (.sealA 5 0 (Cap.node 42)) 0, ledgerDeltaAsset (.cellSealA 0 0) 1,
       ledgerDeltaAsset (.cellDestroyA 0 0 777) 0, ledgerDeltaAsset (.refreshDelegationA 1 1) 1)  -- (0, 0, 0, 0)

-- A MIXED per-asset turn interleaving the DE-SHADOWED seal/lifecycle effects with a transfer: ALL
--   balance-neutral ⇒ (105, 7) preserved; the chain grows by node count; the §8 crypto stays in the portal:
def sealMixedTurn : List FullActionA :=
  [ .createSealPairA 5 0 0 0            -- grant BOTH sealer + unsealer caps to cell 0 (two real grants)
  , .sealA 5 0 (Cap.node 42)           -- seal Cap.node 42 into pair 5 (real box)
  , .balanceA ⟨0, 0, 1, 30⟩ 0          -- transfer 30 of asset 0, cell 0 → cell 1 (conserves)
  , .unsealA 5 0 1                      -- grant the sealed cap to recipient 1 (real cap move)
  , .cellSealA 0 0                      -- Live→Sealed lifecycle transition
  , .receiptArchiveA 0 0 ]

#eval (execFullTurnA fmaS sealMixedTurn).isSome                                      -- true (all commit)
#eval (turnLedgerDeltaAsset sealMixedTurn 0, turnLedgerDeltaAsset sealMixedTurn 1)   -- (0, 0)
#eval (execFullTurnA fmaS sealMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7) (CONSERVED)
#eval (execFullTurnA fmaS sealMixedTurn).map (fun s => s.log.length)                 -- some 6 (chain grew by node count)
-- the cap genuinely moved: recipient 1 holds Cap.node 42 after the turn:
#eval (execFullTurnA fmaS sealMixedTurn).map (fun s => (s.kernel.caps 1).contains (Cap.node 42))  -- some true

/-! ## §13-obligation (WAVE 1) — Non-vacuity for the OBLIGATION LIFECYCLE. createObligation LOCKS the
stake off-ledger (obligor's `bal` debited, combined measure conserved); FULFILL returns the stake to the
OBLIGOR (combined conserved, distinct from escrow refund only by the obligor-only gate); SLASH transfers
it to the BENEFICIARY (combined conserved, distinct from escrow release only by the deadline gate). The
obligor=creator=0 (fmaS, self-authorized over its own cell), beneficiary=1, stake=20 of asset 0. -/

-- CREATE the obligation (id 700): the obligor's bare `bal` at asset 0 DROPS by 20 (100→80), but the
-- COMBINED per-asset measure (`recTotalAssetWithEscrow`) is CONSERVED (the 20 is parked off-ledger).
#eval (execFullA fmaS (.createObligationA 700 0 0 1 0 20)).isSome                     -- true
#eval (execFullA fmaS (.createObligationA 700 0 0 1 0 20)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAssetWithEscrow s.kernel 0))     -- some (85, 105): bare DROPPED, combined CONSERVED
-- FULFILL: from the post-create state, the stake RETURNS to the obligor (cell 0) — bare bal back to 105.
#eval ((execFullA fmaS (.createObligationA 700 0 0 1 0 20)).bind
        (fun s => execFullA s (.fulfillObligationA 700 0))).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7): STAKE RETURNED to obligor
-- SLASH: from the post-create state, the stake TRANSFERS to the BENEFICIARY (cell 1) — cell 1's asset 0
-- bal RISES by 20 (5→25), obligor stays debited; the bare per-asset total returns to 105 (settled).
#eval ((execFullA fmaS (.createObligationA 700 0 0 1 0 20)).bind
        (fun s => execFullA s (.slashObligationA 700 0))).map
        (fun s => (s.kernel.bal 1 0, recTotalAsset s.kernel 0))                       -- some (25, 105): STAKE MOVED to beneficiary
-- the obligation per-asset deltas are 0 (combined-conserving) — like escrow create/settle:
#eval (ledgerDeltaAsset (.fulfillObligationA 700 0) 0, ledgerDeltaAsset (.slashObligationA 700 0) 0)  -- (0, 0)

/-! ## §MA-factory NON-VACUITY — `createCellFromFactoryA` validates + installs the program, end-to-end.

A `subscription` factory (vk 42) publishes: `head` is `Monotonic` (the subscription head only advances),
`owner` is `Immutable` (registered forever), with conforming initial fields. We show: an UNKNOWN vk
rejects; the conforming factory MINTS a fresh cell + INSTALLS its caveats; and a later `SetField` to the
minted cell that VIOLATES an installed caveat is REJECTED BY THE EXECUTOR (the whole point — the
published app-safety is enforced, not merely carried). -/

/-- A subscription factory: `head` Monotonic, `owner` Immutable; born `head=0, owner=9` (conforming). -/
def subFactory : FactoryEntry :=
  { caveats := [.monotonic "head", .immutable "owner"]
    initialFields := [("head", 0), ("owner", 9)]
    programVk := 7 }

/-- The factory registry maps vk 42 → `subFactory`; actor 0 holds the PRIVILEGED minter cap
`Cap.node 5` over the fresh cell 5 (creation is privileged supply — `mintAuthorizedB`, not ownership). -/
def facS : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => .record [("balance", .int 0)]
                caps := fun l => if l = 0 then [Cap.node 5] else []
                factories := [(42, subFactory)] }
    log := [] }

/-- A malformed factory attempting to initialize the reserved scalar `balance` field. -/
def badBalanceFactory : FactoryEntry :=
  { caveats := []
    initialFields := [(balanceField, 999)]
    programVk := 7 }

def facBadBalanceS : RecChainedState :=
  { facS with kernel := { facS.kernel with factories := [(43, badBalanceFactory)] } }

-- The factory's own declared initial state CONFORMS to its own caveats (validate_and_record):
#eval subFactory.conforms                                                         -- true
-- A factory cannot smuggle scalar `balance` through initial fields; per-asset `bal` is born empty:
#eval badBalanceFactory.conforms                                                  -- false
#eval (execFullA facBadBalanceS (.createCellFromFactoryA 0 5 43)).isSome           -- false
-- An UNKNOWN factory vk (99 ∉ registry) is REJECTED (fail-closed, apply.rs:3140):
#eval (execFullA facS (.createCellFromFactoryA 0 5 99)).isSome                     -- false
-- The conforming factory (vk 42) MINTS the fresh cell 5 (born EMPTY ⇒ conservation-neutral):
#eval (execFullA facS (.createCellFromFactoryA 0 5 42)).isSome                     -- true
-- ...and INSTALLS the factory's slot caveats onto the minted cell (the constructor-transparency keystone):
#eval (execFullA facS (.createCellFromFactoryA 0 5 42)).map
        (fun s => reprStr (s.kernel.slotCaveats 5))                                -- some "[…monotonic head, immutable owner]"
-- ...and writes the factory's initial fields + program VK onto the cell:
#eval (execFullA facS (.createCellFromFactoryA 0 5 42)).map
        (fun s => (fieldOf "head" (s.kernel.cell 5), fieldOf "owner" (s.kernel.cell 5),
                   fieldOf factoryVkField (s.kernel.cell 5)))                       -- some (0, 9, 7)

-- THE TEETH: from the MINTED cell, a later `SetField` to the installed-caveat slots is gated BY THE
-- EXECUTOR — an Immutable `owner` rewrite (9→8) is REJECTED; a non-monotone `head` write (0→ −1 would
-- decrease) is REJECTED; a monotone `head` advance (0→3) is ADMITTED:
#eval ((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "owner" 8))).isSome                  -- false (Immutable owner: registered forever)
#eval ((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "head" (-1)))).isSome                -- false (Monotonic head: cannot decrease)
#eval ((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "head" 3))).map
        (fun s => fieldOf "head" (s.kernel.cell 5))                                -- some 3 (monotone advance admitted)
-- A factory whose OWN initial state violates its caveats is REJECTED at mint (validate_and_record):
#eval (FactoryEntry.conforms { caveats := [.boundedBy "x" 0 10], initialFields := [("x", 99)], programVk := 0 })  -- false

-- §MA-factory NEGATIVE-VK ATTACK (codex P1): `findFactory … vk.toNat` would map every negative `vk`
-- to key `0` (`Int.toNat (-1) = 0`), so a negative `vk` could ALIAS factory `0`. `fac0S` parks the
-- subscription factory at key `0` (the alias target); the guard rejects `vk = -1` BEFORE the lookup.
def fac0S : RecChainedState :=
  { facS with kernel := { facS.kernel with factories := [(0, subFactory)] } }
-- The honest call with the real non-negative key `0` MINTS (the factory genuinely lives at `0`):
#eval (execFullA fac0S (.createCellFromFactoryA 0 5 0)).isSome                      -- true
-- THE ATTACK: `vk = -1` no longer aliases factory `0` — it is REJECTED before `findFactory`:
#eval (execFullA fac0S (.createCellFromFactoryA 0 5 (-1))).isSome                   -- false (no aliasing)
-- ...and is rejected even when the alias target is a conforming, mintable factory at key `0`:
#eval (createCellFromFactoryChainA fac0S 0 5 (-1)).isSome                           -- false
-- A legit non-negative `vk` against the original (key-42) registry still works unchanged:
#eval (execFullA facS (.createCellFromFactoryA 0 5 42)).isSome                      -- true

/-! ### §MA-queue-batch #eval (WAVE 4) — the ATOMIC cross-queue transaction + the PIPELINE fan-out step
on the executed dispatch. The atomic batch is ALL-OR-NOTHING (a single failing sub-op rolls back the
WHOLE batch); the pipeline step DEQUEUES a source head and RE-ENQUEUES it into each sink (fan-out
routing). Fixture `fmaQ`: actor 0 owns/holds caps over cells {0,1,2}, with THREE queues — source `q=10`
(owner 0, capacity 3, holding the FIFO message `[111]`), sinks `q=11`/`q=12` (owner 0, capacity 3,
EMPTY). All balance-neutral (queues hold messages, not balance). -/

def fmaQ : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
        bal := fun c a => if c = 0 ∧ a = 0 then 50 else 0
        queues :=
          [ { id := 10, owner := 0, capacity := 3, buffer := [111] }
          , { id := 11, owner := 0, capacity := 3, buffer := [] }
          , { id := 12, owner := 0, capacity := 3, buffer := [] } ] }
    log := [] }

-- ★ ATOMIC BATCH — ALL SUCCEED: enqueue 222 into q=10 (deposit 0) THEN dequeue from q=10 (refund 0).
--   Both sub-ops commit ⇒ the batch COMMITS. (The 222 enqueues to the tail, then the head 111 dequeues.)
#eval (queueAtomicTxA fmaQ 0
        [ .enqueue 10 222 0 0 0 0 0, .dequeue 10 0 0 0 0 ]).isSome                     -- true — all-or-nothing COMMITS

-- ★★ ATOMICITY TEETH — ONE FAILING SUB-OP ROLLS BACK ALL: the SAME first enqueue, but the second sub-op
--   dequeues from a NON-EXISTENT queue id 99 (fail-closed). The WHOLE batch is `none` — the first
--   enqueue is ROLLED BACK (no partial commit), exactly dregg1's journal-rollback for the entire action:
#eval (queueAtomicTxA fmaQ 0
        [ .enqueue 10 222 0 0 0 0 0, .dequeue 99 0 0 0 0 ]).isSome                     -- false — ATOMIC ROLLBACK
-- ...and a failing sub-op FIRST also collapses the batch (the second never runs — the fold short-circuits):
#eval (queueAtomicTxA fmaQ 0
        [ .dequeue 99 0 0 0 0, .enqueue 10 222 0 0 0 0 0 ]).isSome                     -- false — head failure aborts
-- ...the all-or-nothing is balance-neutral when it commits (the COMBINED measure is FIXED ∀ asset):
#eval (queueAtomicTxA fmaQ 0 [ .enqueue 10 222 0 0 0 0 0, .dequeue 10 0 0 0 0 ]).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1))  -- some (50, 0) — CONSERVED

-- ★ PIPELINE STEP — MOVE SOURCE→SINKS: dequeue the head 111 from source q=10 and fan it out into sinks
--   q=11 and q=12. The source LOSES the message (buffer [111] → []); EACH sink GAINS it (buffer [] → [111]):
#eval (queuePipelineStepA fmaQ 10 0 [1, 2] [11, 12]).isSome                            -- true — routing COMMITS
#eval (queuePipelineStepA fmaQ 10 0 [1, 2] [11, 12]).map
        (fun s => ((findQueue s.kernel.queues 10).map (·.buffer),
                   (findQueue s.kernel.queues 11).map (·.buffer),
                   (findQueue s.kernel.queues 12).map (·.buffer)))                     -- some (some [], some [111], some [111]) — MOVED source→sinks
-- ...the pipeline step is balance-NEUTRAL (the COMBINED measure is FIXED ∀ asset — moves a MESSAGE, not balance):
#eval (queuePipelineStepA fmaQ 10 0 [1, 2] [11, 12]).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1))  -- some (50, 0) — CONSERVED

-- ★★ PIPELINE TEETH — source EMPTY rejects (the FIFO emptiness gate): route from q=11 (empty) ⇒ `none`:
#eval (queuePipelineStepA fmaQ 11 0 [2] [12]).isSome                                   -- false — empty source rejected
-- ...and a SINK the owner does NOT control is rejected (the BUG#114 sink-ACL gate): actor 0 holds no cap
--   to cell 5, so fanning into a sink represented by cell 5 fail-closes:
#eval (queuePipelineStepA fmaQ 10 0 [5] [11]).isSome                                   -- false — unauthorized sink rejected
-- ...and a NON-OWNER source dequeue is rejected: cell 1 is not the owner of q=10 ⇒ `none`:
#eval (queuePipelineStepA fmaQ 10 1 [1] [11]).isSome                                   -- false — non-owner source rejected

-- ★ PIPELINED-SEND — the apply-time NEUTRAL marker (the EventualRef resolution is `ConditionalTurn`'s
--   batch; AT apply the resolved action already ran, so this is a balance-neutral clock row that COMMITS):
#eval (execFullA fmaQ (.pipelinedSendA 0)).isSome                                      -- true — apply-time neutral commits
#eval (execFullA fmaQ (.pipelinedSendA 0)).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, s.log.length))                  -- some (50, 1) — NEUTRAL + one clock row

end Dregg2.Exec.TurnExecutorFull
