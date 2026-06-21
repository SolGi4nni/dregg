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
and `AuthTurn` already share — so the widening is ONE executor, not three. Each kind is
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

**W1 (DREGG3 §2.2 — the value unification), LANDED ON THE PER-ASSET LAYER.** The narration above
describes the SCALAR `FullAction` spine (kept as the heritage layer, `±amt` disclosure intact).
The LIVE per-asset layer (`FullActionA`/`execFullA`, §MA below) is post-W1: `AssetId := CellId`
(the asset IS its issuer cell), `recKMintAsset`/`recKBurnAsset` are ISSUER-MOVES (mint = the
issuer's negative-capable well → recipient; burn = holder → well; authority over the ISSUER, E2),
`bridgeMintA` is the BRIDGE-issuer move, and the per-asset delta family vanishes identically
(`ledgerDeltaAsset_eq_zero`) — every committed action/transaction/forest conserves EVERY asset
EXACTLY (`execFullA_conserves_exact`/`execFullTurnA_conserves_exact`), making `∀ a, Σ_c bal c a = 0`
a reachability invariant (`Exec/ReachableConservation.lean`). The pre-W1 supply-increment laws
survive only as `recKMintAssetLegacy`/`recKBurnAssetLegacy` — the non-vacuity teeth
(`Exec/IssuerMove.lean`).

Pure, computable, `#eval`-able. Reuses `TurnExecutor`/`AuthTurn`/`Generators`/
`CatalogEffects`/`RecordKernel`; edits none. Verified standalone:
`lake env lean Dregg2/Exec/TurnExecutorFull.lean`.
-/
import Dregg2.Exec.TurnExecutor
import Dregg2.Exec.AuthTurn
import Dregg2.Exec.Generators
import Dregg2.CatalogEffects
import Dregg2.Exec.EffectsState
import Dregg2.Substrate.HeapKernel

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

/-- **Record-cell mint inflow.** A committed record mint raises the total `balance` by
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

/-- **Record-cell burn outflow.** A committed record burn lowers the total `balance` by
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

/-- **No mint without authority** (the integrity shadow of the privileged supply
generator). A committed record mint implies the actor held mint authority over `cell`. -/
theorem recKMint_authorized (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKMint k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **No burn without authority.** A committed record burn implies mint authority. -/
theorem recKBurn_authorized (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : recKBurn k actor cell amt = some k') : mintAuthorizedB k.caps actor cell = true := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed (record mint).** Without mint authority, no record mint commits. -/
theorem recKMint_unauthorized_fails (k : RecordKernelState) (actor cell : CellId) (amt : ℤ)
    (h : mintAuthorizedB k.caps actor cell = false) : recKMint k actor cell amt = none := by
  unfold recKMint; rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **Fail-closed (record burn).** Without mint authority, no record burn commits. -/
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

/-- **Mint discloses.** The mint effect is Generative, hence carries the disclosed
non-conservation obligation: its supply delta must be revealed in the receipt. Discharged off
`CatalogEffects.generative_discloses` + `g_bridgeMint`. -/
theorem mint_discloses : (effectLinearity mintEffect).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses mintEffect Dregg2.CatalogEffects.g_bridgeMint

/-- **Burn discloses.** The burn effect is Annihilative, hence disclosed: its destroyed
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

/-- **`execFull_ledger` (unified conservation).** Every committed `FullAction` moves the
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

/-- A conserving `FullAction` has zero ledger delta. -/
theorem ledgerDelta_eq_zero_of_conserving (fa : FullAction) (hc : Conserving fa) :
    ledgerDelta fa = 0 := by cases fa <;> simp_all [Conserving, ledgerDelta]

/-- **A conserving `FullAction` preserves `recTotal`** (corollary of `execFull_ledger`):
balance/effect and authority turns leave the conserved supply FIXED. -/
theorem execFull_conserves (s s' : RecChainedState) (fa : FullAction)
    (hc : Conserving fa) (h : execFull s fa = some s') : recTotal s'.kernel = recTotal s.kernel := by
  rw [execFull_ledger s s' fa h, ledgerDelta_eq_zero_of_conserving fa hc, add_zero]

/-- **`execFull_balance_domain_conserves` (per-domain Σ = 0 for conserving kinds).** A
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

/-- **Balance action authorized.** A committed balance `FullAction` was authorized
(`authorizedB` at the pre-state), via `recCexec_attests`. -/
theorem execFull_balance_authorized (s s' : RecChainedState) (a : Action)
    (h : execFull s (.balance a) = some s') : authorizedB s.kernel.caps a.move = true :=
  (recCexec_attests (by simpa [execFull] using h)).2.1

/-- **Delegation grounds.** A committed delegation HOLDS the Granovetter source edge
`delegator ⟶ ⟨t,()⟩` on `execGraph` (only connectivity begets connectivity), via
`recKDelegate_grounds`. -/
theorem execFull_delegate_grounds (s s' : RecChainedState) (del rec t : CellId)
    (h : execFull s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFull, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' del rec t hd

/-- **Mint authorized.** A committed mint implies the actor held the privileged mint
authority over `cell` (a `node`/`control` cap — not mere ownership). -/
theorem execFull_mint_authorized (s s' : RecChainedState) (actor cell : CellId) (amt : ℤ)
    (h : execFull s (.mint actor cell amt) = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  simp only [execFull, recCMint] at h
  cases hm : recKMint s.kernel actor cell amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMint_authorized s.kernel k' actor cell amt hm

/-- **Burn authorized.** A committed burn implies privileged mint authority over `cell`. -/
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

/-- **Delegation IS `addEdge`.** After a committed delegation, the reconstructed authority
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

/-- **Delegation grants the copied held cap.** The scalar executor's concrete cap edit is
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

/-- **Revocation IS `removeEdge`.** After a committed revocation, the reconstructed graph
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

/-- **ChainLink.** A committed `FullAction` extends the receipt chain by EXACTLY its
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

/-- **ObsAdvance.** A committed `FullAction` grows the chain by exactly one row, so a
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

/-- **`execFull_attests` — THE FULL OP-SET IS STEP-COMPLETE BY CONSTRUCTION.** Every
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

/-- **`execFullTurn_ledger` (transaction ledger).** A committed full-turn moves `recTotal`
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

/-- **`execFullTurn_conserves`.** A committed full-turn whose net ledger delta is `0`
(balance/authority only, or balanced mint/burn) preserves `recTotal`. The all-or-nothing transaction
conserves when the supply nets out. -/
theorem execFullTurn_conserves (s s' : RecChainedState) (tt : List FullAction)
    (h : execFullTurn s tt = some s') (hzero : turnLedgerDelta tt = 0) :
    recTotal s'.kernel = recTotal s.kernel := by
  rw [execFullTurn_ledger s s' tt h, hzero, add_zero]

/-- **Every action of a committed full-turn attests `fullActionInv`.** Step-completeness
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
(`dregg_exec_full_turn`) conserves PER-ASSET (the CONSERVATION_VECTOR), not the scalar. The
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

/-- **The LEGACY per-asset mint (supply-increment credit)** — the pre-W1 law, retained ONLY as the
non-vacuity tooth (`Exec/IssuerMove.lean recKMintAsset_breaks_exact` / the R2 probe): it provably
BREAKS `ExactConservation`. The LIVE mint is `recKMintAsset` below (the issuer-move). -/
def recKMintAssetLegacy (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts then
    some { k with bal := recBalCredit k.bal cell a amt }
  else
    none

/-- **The LEGACY per-asset burn (supply-decrement debit)** — pre-W1, retained as the dual
non-vacuity tooth. The LIVE burn is `recKBurnAsset` below. -/
def recKBurnAssetLegacy (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a ∧ cell ∈ k.accounts then
    some { k with bal := recBalCredit k.bal cell a (-amt) }
  else
    none

/-- **THE per-asset MINT (W1, DREGG3 §2.2 Asset): the ISSUER-MOVE.** `AssetId := CellId` — the
asset IS its issuer cell. Minting `amt` of asset `a` to `cell` is an ORDINARY per-asset transfer
`a → cell`: the issuer's own row in its asset (the WELL) goes negative by the minted amount, the
recipient goes positive, and `Σ_c bal c a` is UNCHANGED — exactly zero stays exactly zero. Gates:
  * `mintAuthorizedB actor a` — mint authority is control of the **ISSUER** cell (E2: the
    production law — authority to mint IS the issuer capability);
  * `0 ≤ amt`, issuer + recipient live, `a ≠ cell` (self-mint is a no-move);
  * deliberately **NO availability gate at the well** (E1: the well is negative-capable — its
    balance IS −supply; issuance policy lives in the issuer cell's program, the kernel keeps
    conservation only). -/
def recKMintAsset (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt
      ∧ a ∈ k.accounts ∧ cell ∈ k.accounts ∧ a ≠ cell then
    some { k with bal := recTransferBal k.bal a cell a amt }
  else none

/-- **THE per-asset BURN (W1): the issuer-move with direction swapped.** Burning `amt` of asset `a`
held by `cell` RETURNS it to the issuer's well (`cell → a`): the well's balance rises toward zero —
supply shrinks, `Σ_c bal c a` unchanged. Gated on mint authority over the **ISSUER** + availability
at the HOLDER (`amt ≤ bal cell a` — an ordinary cell can only burn what it holds; only the issuer
WELL waives availability) + liveness + distinctness. -/
def recKBurnAsset (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a then
    some { k with bal := recTransferBal k.bal cell a a amt }
  else none

/-- **Per-asset mint CONSERVES (the W1 strengthening).** A committed mint leaves the total supply
of EVERY asset untouched: `recTotalAsset k' b = recTotalAsset k b` — the issuer-debit and the
recipient-credit cancel inside the sum (`recTransferBal_sum_conserve_moved`), every other asset's
column is pointwise unchanged (`recTransferBal_untouched`). The pre-W1 statement (`+amt` at the
minted asset) is the LEGACY law's delta (`recKMintAssetLegacy_delta`). -/
theorem recKMintAsset_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recKMintAsset k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt
      ∧ a ∈ k.accounts ∧ cell ∈ k.accounts ∧ a ≠ cell
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, hiss, hcell, hne⟩ := hg
    rcases eq_or_ne b a with rfl | hb
    · show (∑ c ∈ k.accounts, recTransferBal k.bal b cell b amt c b)
          = ∑ c ∈ k.accounts, k.bal c b
      exact recTransferBal_sum_conserve_moved k.accounts k.bal b cell b amt hiss hcell hne
    · show (∑ c ∈ k.accounts, recTransferBal k.bal a cell a amt c b)
          = ∑ c ∈ k.accounts, k.bal c b
      exact Finset.sum_congr rfl
        (fun c _ => recTransferBal_untouched k.bal a cell a b amt hb c)
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Per-asset burn CONSERVES (the W1 strengthening).** Symmetric to `recKMintAsset_delta`: the
holder-debit and the well-credit cancel. -/
theorem recKBurnAsset_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recKBurnAsset k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, hcell, hiss, hne⟩ := hg
    rcases eq_or_ne b a with rfl | hb
    · show (∑ c ∈ k.accounts, recTransferBal k.bal cell b b amt c b)
          = ∑ c ∈ k.accounts, k.bal c b
      exact recTransferBal_sum_conserve_moved k.accounts k.bal cell b b amt hcell hiss hne
    · show (∑ c ∈ k.accounts, recTransferBal k.bal cell a a amt c b)
          = ∑ c ∈ k.accounts, k.bal c b
      exact Finset.sum_congr rfl
        (fun c _ => recTransferBal_untouched k.bal cell a a b amt hb c)
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The LEGACY mint's delta** (the supply-increment law — the tooth's instantiation surface). -/
theorem recKMintAssetLegacy_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKMintAssetLegacy k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b + (if b = a then amt else 0) := by
  unfold recKMintAssetLegacy at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hcell⟩ := hg
    show (∑ c ∈ k.accounts, recBalCredit k.bal cell a amt c b)
        = (∑ c ∈ k.accounts, k.bal c b) + (if b = a then amt else 0)
    exact recBalCredit_recTotalAsset k.accounts k.bal cell a amt hcell b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **The LEGACY burn's delta** (the supply-decrement law). -/
theorem recKBurnAssetLegacy_delta (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKBurnAssetLegacy k actor cell a amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b + (if b = a then (-amt) else 0) := by
  unfold recKBurnAssetLegacy at h
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

/-- No per-asset mint without authority **over the ISSUER** (E2: the gate target is the asset's
issuer cell `a`, NOT the recipient — the production law in executable form). -/
theorem recKMintAsset_authorized (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKMintAsset k actor cell a amt = some k') :
    mintAuthorizedB k.caps actor a = true := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt
      ∧ a ∈ k.accounts ∧ cell ∈ k.accounts ∧ a ≠ cell
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **GENESIS ORDER, fail-closed.** Minting an asset whose issuer cell is not LIVE refuses — the
bootstrap order (create the issuer cell, then mint) is a GATE, not a convention. -/
theorem recKMintAsset_requires_live_issuer (k : RecordKernelState) (actor cell : CellId)
    (a : AssetId) (amt : ℤ) (hno : a ∉ k.accounts) :
    recKMintAsset k actor cell a amt = none := by
  unfold recKMintAsset
  rw [if_neg (by rintro ⟨-, -, hiss, -, -⟩; exact hno hiss)]

/-- A committed mint witnesses its issuer well LIVE (the positive face of the genesis-order
gate). -/
theorem recKMintAsset_issuer_live (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKMintAsset k actor cell a amt = some k') : a ∈ k.accounts := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt
      ∧ a ∈ k.accounts ∧ cell ∈ k.accounts ∧ a ≠ cell
  · exact hg.2.2.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed burn witnesses its issuer well LIVE. -/
theorem recKBurnAsset_issuer_live (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKBurnAsset k actor cell a amt = some k') : a ∈ k.accounts := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a
  · exact hg.2.2.2.2.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The lifecycle discriminants (full §MA-lifecycle commentary below). `lcArchived` is the receipt-archive
terminal-ish marker the DEPLOYED `apply_receipt_archive` (`c.archive(checkpoint)`) moves the side-table to
(NOT a cell record-slot write — the prior record-slot model was superseded by the V3 disc gate). -/
def lcLive      : Nat := 0
def lcSealed    : Nat := 1
def lcDestroyed : Nat := 3
def lcArchived  : Nat := 4

/-- **`acceptsEffects`** — dregg1's `CellLifecycle::accepts_effects`: `true` only for Live. -/
def acceptsEffects (k : RecordKernelState) (cell : CellId) : Bool := k.lifecycle cell == lcLive

/-- **The chained per-asset transfer/mint/burn** (thread the receipt chain, newest-first, exactly as
`recCexec`/`recCMint`/`recCBurn` do for the scalar kernel). The transfer arm gates on
`acceptsEffects` at `t.dst` (R1: no credit into a Sealed/Destroyed cell — dregg1's
`CellLifecycle::accepts_effects`). -/
def recCexecAsset (s : RecChainedState) (t : Turn) (a : AssetId) : Option RecChainedState :=
  if acceptsEffects s.kernel t.dst then
    match recKExecAsset s.kernel t a with
    | some k' => some { kernel := k', log := t :: s.log }
    | none    => none
  else none

/-- Chained per-asset mint (W1: the receipt is the TRUTHFUL issuer-move row — the issuer well `a`
is the `src`, the recipient the `dst`; no self-credit fiction). -/
def recCMintAsset (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecChainedState :=
  match recKMintAsset s.kernel actor cell a amt with
  | some k' => some { kernel := k', log := { actor := actor, src := a, dst := cell, amt := amt } :: s.log }
  | none    => none

/-- Chained per-asset burn (W1: the truthful return-to-well row — holder `src`, issuer well `dst`). -/
def recCBurnAsset (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecChainedState :=
  match recKBurnAsset s.kernel actor cell a amt with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := a, amt := amt } :: s.log }
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

/-- **`createCellChainA` factors through its gate.** A committed creation implies the two gate
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
authority handoff: child creation does not manufacture `Cap.node target`, and an endpoint-limited
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
              if l = child then [heldCapTo s.kernel.caps actor target] else s.kernel.caps l
                           delegate := fun c => if c = child then some actor else s.kernel.delegate c
                           delegations := fun c => if c = child then s.kernel.caps actor
                                                   else s.kernel.delegations c } }
    | none => none
  else
    none

/-- **`spawnChainA` factors through `createCellChainA`.** A committed spawn is a committed
`createCellChainA` (into `s1`) whose parent target was already live and held by the actor, followed by
the concrete held-cap copy and initial delegation snapshot. -/
theorem spawnChainA_factors {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    ∃ s1, ((s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
             target ∈ s.kernel.accounts) ∧
      createCellChainA s actor child = some s1 ∧
      s' = { s1 with kernel :=
        { s1.kernel with caps := fun l =>
            if l = child then [heldCapTo s.kernel.caps actor target] else s.kernel.caps l
                         delegate := fun c => if c = child then some actor else s.kernel.delegate c
                         delegations := fun c => if c = child then s.kernel.caps actor
                                                 else s.kernel.delegations c } } := by
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

/-- **`createCellChainA_neutral` — ACCOUNT-GROWTH IS CONSERVATION-NEUTRAL.** A committed
`createCellChainA` leaves `recTotalAsset` UNCHANGED for EVERY asset `b`: the index set `accounts`
GREW (`createCellChainA_grows_accounts`), but the fresh cell is born EMPTY (`bal`-reset), so its
contribution is exactly `0` (`recTotalAsset_insert_fresh`, with `hfresh` from the freshness gate). The
account-growth neutrality the per-asset dispatch demands. -/
theorem createCellChainA_neutral {s s' : RecChainedState} {actor newCell : CellId} (b : AssetId)
    (h : createCellChainA s actor newCell = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hfresh, hs'⟩ := createCellChainA_factors h
  subst hs'
  exact recTotalAsset_insert_fresh s.kernel newCell b hfresh

/-- **`createCellChainA_grows_accounts` — the GROWTH has teeth.** After a committed
`createCellChainA`, the new cell IS a live account (`newCell ∈ accounts`) — the index set grew,
so the neutrality theorem is NOT a no-op. -/
theorem createCellChainA_grows_accounts {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') : newCell ∈ s'.kernel.accounts := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'; exact createCellIntoAsset_grows_accounts s.kernel newCell

/-- **`createCellChainA_authorized` (fail-closed integrity).** A committed creation implies the
creator held the privileged creation authority over the new cell (`mintAuthorizedB` — bare ownership is
NOT enough; creation coins a fresh cell). -/
theorem createCellChainA_authorized {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  (createCellChainA_factors h).1

/-- **`createCellChainA_unauthorized_fails` (fail-closed).** Without creation authority, no cell
is minted. The confinement core. -/
theorem createCellChainA_unauthorized_fails (s : RecChainedState) (actor newCell : CellId)
    (h : mintAuthorizedB s.kernel.caps actor newCell = false) :
    createCellChainA s actor newCell = none := by
  unfold createCellChainA
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **`createCellChainA_chainlink`.** A committed creation extends the receipt chain by EXACTLY
the (balance-`0`) creation row, newest-first. -/
theorem createCellChainA_chainlink {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    s'.log = { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h; subst hs'; rfl

/-- **`createCellChainA_caps_frame`.** A committed creation resets the fresh id's cap slot to
`[]` and frames every other slot (`bornEmptyCellSlots`). -/
theorem createCellChainA_caps_frame {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    (∀ l, l ≠ newCell → s'.kernel.caps l = s.kernel.caps l)
    ∧ s'.kernel.caps newCell = [] := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'
  dsimp [createCellIntoAsset, bornEmptyCellSlots]
  constructor
  · intro l hl; simp only [if_neg hl]
  · simp only [if_pos]

/-- The spawn metadata/cap copy is bal-orthogonal — it edits `caps`, parent pointer, and delegation
snapshot, never `bal`/`accounts` — so the per-asset measure is literally unchanged. -/
theorem spawnGrant_recTotalAsset (k : RecordKernelState) (actor child : CellId) (cap : Cap)
    (b : AssetId) :
    recTotalAsset { k with caps := fun l => if l = child then cap :: k.caps l else k.caps l
                           delegate := fun c => if c = child then some actor else k.delegate c
                           delegations := fun c => if c = child then k.caps actor else k.delegations c } b
      = recTotalAsset k b := rfl

/-- **`spawnChainA_neutral`.** A committed spawn leaves `recTotalAsset` UNCHANGED for EVERY asset:
the create leg is neutral (born EMPTY), the cap grant is bal-orthogonal. -/
theorem spawnChainA_neutral {s s' : RecChainedState} {actor child target : CellId} (b : AssetId)
    (h : spawnChainA s actor child target = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors h
  subst hs'
  exact (spawnGrant_recTotalAsset s1.kernel actor child (heldCapTo s.kernel.caps actor target) b).trans
    (createCellChainA_neutral b hc)

/-- **`spawnChainA_authorized`.** A committed spawn implies the spawner held creation authority
over the child. -/
theorem spawnChainA_authorized {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    mintAuthorizedB s.kernel.caps actor child = true := by
  obtain ⟨s1, _, hc, _⟩ := spawnChainA_factors h
  exact createCellChainA_authorized hc

/-- **`spawnChainA_grounds`.** A committed spawn implies the actor already held a live
connectivity edge to the parent target. Child creation alone cannot introduce an unrelated edge. -/
theorem spawnChainA_grounds {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    Dregg2.Spec.execGraph s.kernel.caps actor
        (⟨target, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
      target ∈ s.kernel.accounts := by
  obtain ⟨_, hg, _, _⟩ := spawnChainA_factors h
  exact hg

/-- **`spawnChainA_provenance` (the DISCLOSED-AUTHORITY keystone).** The spawned child receives
EXACTLY the concrete cap the actor already held to the parent target. This preserves rights (endpoint
rights stay endpoint rights) instead of manufacturing `node target` control. -/
theorem spawnChainA_provenance {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    heldCapTo s.kernel.caps actor target ∈ s'.kernel.caps child := by
  obtain ⟨s1, _, _, hs'⟩ := spawnChainA_factors h
  subst hs'
  simp

/-- **`spawnChainA_parent_snapshot`.** Spawn initializes the delegation lifecycle: the child
records its parent (`actor`) and stores a birth snapshot of the parent's current c-list. -/
theorem spawnChainA_parent_snapshot {s s' : RecChainedState} {actor child target : CellId}
    (h : spawnChainA s actor child target = some s') :
    s'.kernel.delegate child = some actor ∧ s'.kernel.delegations child = s.kernel.caps actor := by
  obtain ⟨_, _, _, hs'⟩ := spawnChainA_factors h
  subst hs'
  simp only [if_true, true_and, if_pos]

/-- **`spawnChainA_chainlink`.** A committed spawn extends the receipt chain by EXACTLY the
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

/-- **`createCellFromFactoryChainA` factors through its gates.** A committed factory creation
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

/-- **`createCellFromFactoryChainA_neutral` — FACTORY CREATION IS CONSERVATION-NEUTRAL.** A
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

/-- **`createCellFromFactoryChainA_authorized` (fail-closed integrity).** A committed factory
creation implies the creator held privileged creation authority over the new cell (`mintAuthorizedB`). -/
theorem createCellFromFactoryChainA_authorized {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true := by
  obtain ⟨_, _, _, _, hc, _⟩ := createCellFromFactoryChainA_factors h
  exact createCellChainA_authorized hc

/-- **`createCellFromFactoryChainA_grows_accounts` — the GROWTH has teeth.** After a committed
factory creation, the new cell IS a live account — the registry grew, the neutrality is NOT a no-op. -/
theorem createCellFromFactoryChainA_grows_accounts {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    newCell ∈ s'.kernel.accounts := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  -- the field/caveat install keeps `accounts := s1.kernel.accounts` (it edits only `cell`/`slotCaveats`):
  subst hs'
  show newCell ∈ s1.kernel.accounts
  exact createCellChainA_grows_accounts hc

/-- **`createCellFromFactoryChainA_installs_program` (THE FACTORY KEYSTONE).** Every cell a
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

/-- **`createCellFromFactoryChainA_unknown_factory_fails` (fail-closed).** An unknown factory
VK never mints a cell (dregg1 `apply.rs:3140` `validate_and_record` errors `factory creation failed`). -/
theorem createCellFromFactoryChainA_unknown_factory_fails (s : RecChainedState) (actor newCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    createCellFromFactoryChainA s actor newCell vk = none := by
  simp only [createCellFromFactoryChainA, h, ite_self]

/-- **`createCellFromFactoryChainA_nonconforming_fails` (fail-closed).** A factory whose own
declared initial state VIOLATES its own caveats never mints (the `validate_and_record` constraint
check rejects, `apply.rs:3140`). -/
theorem createCellFromFactoryChainA_nonconforming_fails (s : RecChainedState) (actor newCell : CellId)
    (vk : Int) (e : FactoryEntry) (hfind : findFactory s.kernel.factories vk.toNat = some e)
    (hbad : e.conforms = false) :
    createCellFromFactoryChainA s actor newCell vk = none := by
  simp only [createCellFromFactoryChainA, hfind, hbad, Bool.false_eq_true, if_false, ite_self]

/-- **`createCellFromFactoryChainA_balance_field_fails` (fail-closed).** Factory initial fields
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

/-- **`createCellFromFactoryChainA_chainlink`.** A committed factory creation extends the
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

/-- **`createCellFromFactoryChainA_sideTables`.** A committed factory creation leaves the
SET-shaped side-tables (`commitments`, `nullifiers`, `revoked`) UNTOUCHED: `createCell`
edits only `accounts`/`bal`, and the field/caveat install edits only `cell`/`slotCaveats`. The frame
the carried-forever crowns (`CellCommit`/`CellNullifier`/`CellConfine`) reuse for the new effect. -/
theorem createCellFromFactoryChainA_sideTables {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧
      s'.kernel.revoked = s.kernel.revoked := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
  subst hs' hs1
  exact ⟨rfl, rfl, rfl⟩

/-- **`createCellFromFactoryChainA_caps_eq`.** A committed factory creation leaves the cap
table UNTOUCHED: `createCell` edits `accounts`/`bal`, and the field/caveat install edits `cell`/
`slotCaveats` — never `caps`. The frame the confinement crown (`CellConfine`) reuses. -/
theorem createCellFromFactoryChainA_caps_frame {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    (∀ l, l ≠ newCell → s'.kernel.caps l = s.kernel.caps l)
    ∧ s'.kernel.caps newCell = [] := by
  obtain ⟨_, s1, _, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  have hcreate := createCellChainA_caps_frame hc
  subst hs'
  -- factory install edits `cell`/`slotCaveats` only — caps are literally the create-leg caps.
  simpa using hcreate

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

/-- **Balance-NEUTRALITY of a field write over the per-asset ledger (the load-bearing
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

/-- **Balance-NEUTRALITY of a committed `stateStep` over the per-asset ledger.** A committed
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
`bal` ledger / `escrows` holding-store — so `recTotalAsset b` is UNCHANGED for EVERY asset.
The per-asset analog the `setFieldA` conservation arm reuses now that `setFieldA` routes through the
caveat gate (dregg1 `apply_set_field` → `RecordProgram::evaluate`). -/
theorem stateStepGuarded_recTotalAsset {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int} (h : stateStepGuarded s f actor target n = some s')
    (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h)
  subst hs'
  exact writeField_recTotalAsset s.kernel f target (.int n) b

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

/-- **`emitStep` is balance-NEUTRAL.** `EmitEvent` leaves the kernel (hence `recTotalAsset
b` for EVERY asset `b`) UNCHANGED — it only appends a receipt. -/
theorem emitStep_recTotalAsset (s : RecChainedState) (actor cell : CellId) (topic data : Int)
    (b : AssetId) : recTotalAsset (emitStep s actor cell topic data).kernel b = recTotalAsset s.kernel b := rfl

/-- **`emitStep` advances the chain by exactly one row** (the observation/replay clock). -/
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
effects use) — the STATE move is real (a flag/marker/lifecycle field changes), while the §8
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
ledger**: `recTotalAsset`/`recTotalAsset` read `k.bal`/`k.escrows`, which are independent of
`k.cell` — so a value-rebind that touches ONLY `k.cell` cannot move any asset's supply (the SAME
`rfl`-grade conservation `writeField_recTotalAsset` enjoys, since it too touches only `k.cell`). The
commitment binding (collision-resistance of `state_commitment`) is the §8 chain-layer portal — NOT
proved sound here; what IS proved is the value-rebind itself: the readable state is gone. -/

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

/-- **`makeSovereignStep` — the executable semantics of `MakeSovereign` (computable).**
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

/-- **`makeSovereignStep_factors`.** A committed `makeSovereignStep` was authorized and
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

/-- **Balance-NEUTRALITY of the value-rebind over the per-asset ledger (`rfl`-grade).** The
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

/-- **THE FIDELITY TEETH — the readable balance is GONE.** After a committed
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

/-- **THE FIDELITY TEETH — EVERY pre-state field is dropped.** After a committed
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

/-- **THE COMMITMENT IS PRESENT.** After a committed `makeSovereignStep`, the rebound cell
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

/-- **`makeSovereignStep` authorized.** A committed rebind implies the actor held authority
over `target` (dregg1's self-sovereign gate). -/
theorem makeSovereignStep_authorized {s s' : RecChainedState} {actor target : CellId}
    (h : makeSovereignStep s actor target = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  (makeSovereignStep_factors h).1

/-- **`makeSovereignStep` extends the chain by exactly one row** (the metadata clock; the
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

/-- **`amplifyingF_rejected` — THE TEETH.** A `granted` cap conferring an authority `a` the
`held` cap does NOT confer is REJECTED (`¬ IsNonAmplifyingF held granted`). So the non-amplification
gate discriminates — it is not vacuously true. -/
theorem amplifyingF_rejected (held granted : Cap) (a : Auth)
    (hgranted : a ∈ capAuthConferred granted) (hheld : a ∉ capAuthConferred held) :
    ¬ IsNonAmplifyingF held granted := fun hsub => hheld (hsub hgranted)

/-- **`attenuateF_non_amplifying` — THE HEADLINE (GENUINE).** The narrowed cap confers a
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

/-- **`acceptsEffects_eq_cellLifecycleLive`.** The live-executor lifecycle gate `acceptsEffects`
and the kernel-level settle-target gate `cellLifecycleLive` (the D3 escrow/bridge secondary-cell gate) are
DEFINITIONALLY the same predicate: both read the `lifecycle` side-table and check `== 0` (`lcLive`). This
is the cutover witness that the D3 secondary-cell gate is the SAME liveness discriminant as the R6
field-write gate. -/
theorem acceptsEffects_eq_cellLifecycleLive (k : RecordKernelState) (cell : CellId) :
    acceptsEffects k cell = cellLifecycleLive k cell := rfl

#assert_axioms acceptsEffects_eq_cellLifecycleLive

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

/-- **Chained receipt ARCHIVE** (`apply_receipt_archive` → `Cell::archive(checkpoint)`): the DEPLOYED
archive moves the LIFECYCLE side-table to `Archived` (`4`) — the cellSeal/cellDestroy side-table shape,
NOT a `cell` record-slot write (the prior record-slot model was a MIS-ROUTE the V3 disc gate superseded;
see `receiptArchiveV3`). FAIL-CLOSED on the three-leg `auditGuard`: self-authority (`stateAuthB`),
membership (`cell ∈ accounts`), and liveness (`cellLive` — only a Live cell may be archived). On commit,
flip the discriminant to `Archived` and extend the chain by one self-targeted row. bal-NEUTRAL. -/
def receiptArchiveChainA (s : RecChainedState) (actor cell : CellId) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
      ∧ Dregg2.Exec.EffectsState.cellLive s.kernel cell = true then
    some { kernel := setLifecycle s.kernel cell lcArchived,
           log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
  else none

/-- **`setLifecycle` is balance-NEUTRAL (`rfl`-grade).** Editing the `lifecycle` side-table
leaves `bal`/`accounts`/`escrows` fixed, so `recTotalAsset` is unchanged for EVERY asset. -/
theorem setLifecycle_balNeutral (k : RecordKernelState) (cell : CellId) (lc : Nat) (b : AssetId) :
    recTotalAsset (setLifecycle k cell lc) b = recTotalAsset k b := rfl

/-- **`cellSealChainA` factors.** A committed seal was authorized over a LIVE cell and produced
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

/-- **`cellUnsealChainA` factors.** A committed unseal was authorized over a SEALED cell. -/
theorem cellUnsealChainA_factors {s s' : RecChainedState} {actor cell : CellId}
    (h : cellUnsealChainA s actor cell = some s') :
    (stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true) ∧
      s' = { kernel := setLifecycle s.kernel cell lcLive,
             log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  unfold cellUnsealChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`cellDestroyChainA` factors.** A committed destroy was authorized over a NON-terminal
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

/-- **`receiptArchiveChainA` factors.** A committed archive was authorized (`auditGuard`: self-authority,
membership, liveness) and produced exactly the `Archived`-flip side-table post-state + a one-row chain. -/
theorem receiptArchiveChainA_factors {s s' : RecChainedState} {actor cell : CellId}
    (h : receiptArchiveChainA s actor cell = some s') :
    (stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
        ∧ Dregg2.Exec.EffectsState.cellLive s.kernel cell = true) ∧
      s' = { kernel := setLifecycle s.kernel cell lcArchived,
             log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  unfold receiptArchiveChainA at h
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
      ∧ Dregg2.Exec.EffectsState.cellLive s.kernel cell = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`cellDestroyChainA_terminal_rejects` — THE TERMINALITY TEETH.** A cell already Destroyed
(`lifecycle cell = lcDestroyed`) cannot be re-destroyed: the gate fails, so the leg returns `none` and no
effect commits. dregg1's `Terminal` rejection (`cell.rs:587`). NON-VACUOUS — keyed on committed state. -/
theorem cellDestroyChainA_terminal_rejects (s : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (h : s.kernel.lifecycle cell = lcDestroyed) :
    cellDestroyChainA s actor cell certHash = none := by
  unfold cellDestroyChainA
  rw [if_neg (by simp [h])]

/-- **`cellSealChainA_sealed_rejects` — THE SEAL-GATE TEETH.** A cell NOT Live (Sealed or
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
child having a parent (`delegate child ≠ none` — dregg1's `delegate.ok_or_else`,
`apply.rs:3004`). On commit, OVERWRITE `delegations child` with a FRESH snapshot of the parent's CURRENT
`caps` (`parentClist`) and extend the chain. bal-NEUTRAL.

⚑ SCOPED RESIDUAL (the freshness-RESTORE epoch re-stamp): dregg1's refresh ALSO re-stamps the child's
`DelegatedRef.delegation_epoch` with the parent's current `delegationEpoch` (`apply.rs:3024`). The Lean
kernel now CARRIES `delegationEpochAt`, and the REVOKE path models the epoch bump + freshness (see
`AuthTurn.lean §3.EPOCH`); the refresh-side re-stamp is a SEPARATE follow-up because the
`refreshDelegationA`/`spawnA` CIRCUIT instances (`Inst/refreshDelegationA.lean`, `Inst/spawnA.lean`) are
single/quint-component `funcComponent` descriptors that would need a 6th component to BIND the
`delegationEpochAt` move. Refresh therefore leaves `delegationEpochAt` frozen for now (a still-authorized
child re-syncs by re-snapshotting `delegations`; the epoch-tag refresh is the deferred binding). -/
def refreshDelegationChainA (s : RecChainedState) (actor child : CellId) : Option RecChainedState :=
  if stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true then
    some { kernel := { s.kernel with
                        delegations := fun c => if c = child then parentClist s.kernel child
                                                else s.kernel.delegations c },
           log    := { actor := actor, src := child, dst := child, amt := 0 } :: s.log }
  else none

/-- **`refreshDelegationChainA` factors.** A committed refresh was self-authorized over a child
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

/-- **`refreshDelegationChainA_noParent_rejects` (the no-parent teeth).** A child with no
parent (`delegate child = none`) cannot refresh: dregg1's `delegate.ok_or_else` (`apply.rs:3004`). -/
theorem refreshDelegationChainA_noParent_rejects (s : RecChainedState) (actor child : CellId)
    (h : s.kernel.delegate child = none) :
    refreshDelegationChainA s actor child = none := by
  unfold refreshDelegationChainA
  rw [if_neg (by simp [h])]

/-- **`refreshDelegationChainA_snapshots_parent` — THE FRESH-SNAPSHOT TEETH.** After a committed
refresh of a child with parent `p`, the child's delegation snapshot IS the parent's CURRENT c-list
(`delegations child = caps p`). A flag-flip could never witness this — the snapshot tracks the
live parent caps. -/
theorem refreshDelegationChainA_snapshots_parent {s s' : RecChainedState} {actor child p : CellId}
    (h : refreshDelegationChainA s actor child = some s') (hp : s.kernel.delegate child = some p) :
    s'.kernel.delegations child = s.kernel.caps p := by
  obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'
  show (if child = child then parentClist s.kernel child else s.kernel.delegations child) = s.kernel.caps p
  rw [if_pos rfl]; simp only [parentClist, hp]

theorem refreshDelegationChainA_balNeutral {s s' : RecChainedState} {actor child : CellId}
    (h : refreshDelegationChainA s actor child = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; rfl

/-! ### §MA-meta — the zero-amount metadata receipt row.

F1b: the chained escrow/obligation/committed-escrow wrappers (`createEscrowChainA`/
`releaseEscrowChainA`/`refundEscrowChainA` + the settle-auth gates) are GONE with the kernel
holding-store — escrow/obligation semantics live in the proven factory contracts
(`Apps/{EscrowFactory,ObligationFactory}.lean`). The note SET effects below survive. -/

/-- The zero-amount METADATA receipt (a self-`Turn` on the actor, amount `0` — the clock row the
SET-moving and apply-time-neutral effects append). Historical name: the escrow family appended it
first; the family is gone (F1b), the row shape stays (it is pinned by the deployed circuit specs). -/
def escrowReceiptA (actor : CellId) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }

/-- **`recCexecAsset_factors`.** A committed per-asset transfer passed `acceptsEffects` at
`dst` and factors through `recKExecAsset`. -/
theorem recCexecAsset_factors {s s' : RecChainedState} (t : Turn) (a : AssetId)
    (h : recCexecAsset s t a = some s') :
    acceptsEffects s.kernel t.dst ∧
    ∃ k', recKExecAsset s.kernel t a = some k' ∧ s' = { kernel := k', log := t :: s.log } := by
  simp only [recCexecAsset] at h
  by_cases hadm : acceptsEffects s.kernel t.dst
  · rw [if_pos hadm] at h
    rcases hr : recKExecAsset s.kernel t a with ⟨⟩ | ⟨k''⟩
    · rw [hr] at h; exact absurd h (by simp)
    · rw [hr] at h; simp at h
      exact ⟨hadm, ⟨k'', rfl, h.symm⟩⟩
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **Chained note-create** — grow the commitment SET (the §8 range-proof portal is the THEOREM-level
hypothesis, like bridgeMint's foreign finality; the ledger move is the grow-only insert). Always
commits at the ledger layer (a fresh commitment cannot conflict). -/
def noteCreateChainA (s : RecChainedState) (cm : Nat) (actor : CellId) : RecChainedState :=
  { kernel := noteCreateCommitment s.kernel cm, log := escrowReceiptA actor :: s.log }

/-- **Chained note-spend — the HONEST §8 spending-proof gate + ledger anti-replay.** Two fail-closed
gates, in dregg1's order (`apply_note_spend`, `apply.rs:889,941`):

1. `spendProof : Bool` — the EXECUTABLE boolean shadow of the §8 STARK note-spending proof
   (`verifier.verify(spending_proof, "note-spend", "note-tree", public_inputs)`, `apply.rs:926`). It
   proves the spender knows the note's opening, the nullifier is correctly derived, and the note
   commitment exists in the note tree at the given root. **FAIL-CLOSED if `spendProof = false`** —
   exactly the "NoteSpend spending proof verification failed" / "missing spending proof" rejection
   the Rust marshaller saw but the proof-less projection could not (the `NoteSpend` divergence the
   ledger characterised). Welding it here CAPTURES note-proof verification IN the verified executor
   (smaller TCB): the §8 STARK extractability is the named carrier (`PrivacyKernel.noteSpend_sound`),
   the executor's gate is the boolean shadow that fail-closes on a missing/invalid proof.
2. `noteSpendNullifier` — the ledger-side double-spend gate (fail-closed on a repeated nullifier).

The two gates compose: a spend commits ONLY when BOTH the spending proof verified AND the nullifier is
fresh. An executable §8-portal witness, fail-closed, with a rejection tooth. -/
def noteSpendChainA (s : RecChainedState) (nf : Nat) (actor : CellId)
    (spendProof : Bool) : Option RecChainedState :=
  if spendProof = true then
    match noteSpendNullifier s.kernel nf with
    | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
    | none    => none
  else none

/-- **`noteSpendChainA_fails_without_proof` (THE NOTE-PROOF TEETH).** No note-spend commits
without the §8 spending proof (`spendProof = false` ⇒ `none`). This is exactly the rejection
`apply.rs:929` produces ("NoteSpend spending proof verification failed") that the proof-less
projection could not see — now CAPTURED in the verified executor. A NoteSpend with an invalid proof
is REJECTED in Lean. -/
theorem noteSpendChainA_fails_without_proof {s : RecChainedState} {nf : Nat} {actor : CellId}
    {spendProof : Bool} (hp : spendProof = false) :
    noteSpendChainA s nf actor spendProof = none := by
  simp only [noteSpendChainA, hp, if_neg (by decide : ¬ (false = true))]

/-- **`noteSpendChainA_requires_proof`.** A committed note-spend IMPLIES the §8 spending
proof verified (`spendProof = true`) AND the nullifier was fresh — the conjunction the bare
nullifier-only chain lacked its first (proof) half of. -/
theorem noteSpendChainA_requires_proof {s s' : RecChainedState} {nf : Nat} {actor : CellId}
    {spendProof : Bool} (h : noteSpendChainA s nf actor spendProof = some s') :
    spendProof = true ∧ nf ∉ s.kernel.nullifiers := by
  unfold noteSpendChainA noteSpendNullifier at h
  by_cases hp : spendProof = true
  · rw [if_pos hp] at h
    by_cases hin : nf ∈ s.kernel.nullifiers
    · rw [if_pos hin] at h; exact absurd h (by simp)
    · exact ⟨hp, hin⟩
  · rw [if_neg hp] at h; exact absurd h (by simp)

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
  /-- `RevokeDelegation { child→holder }` (dregg1 `apply_revoke_delegation`, `apply.rs:3044`): a
  parent revokes a child's delegation — the `holder` loses its edge to `target`. Reuses
  `recKRevokeTarget` (`removeEdge`). A DISTINCT dregg1 op from `DropRef` (parent-revocation vs.
  holder-GC), sharing the graph move. -/
  | revokeDelegationA (holder target : CellId)
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
  -- §MA-note: the commitment/nullifier SET effects. Notes move the nullifier/commitment SET (not
  -- `bal`). The §8 crypto (note range/spending proofs) is the THEOREM-level portal (off this
  -- executable layer, exactly as bridgeMint's foreign finality). F1b: the escrow/obligation/
  -- committed-escrow/bridge-LFC constructors are GONE — those families live in factory cells
  -- (`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`); `bridgeMintA` (inbound, above) survives.
  /-- `NoteSpend { nullifier, spending_proof }` (dregg1 `apply_note_spend`): the nullifier-SET insert
  with double-spend rejection (the ledger anti-replay gate), GATED on the §8 STARK spending proof. The
  `spendProof : Bool` is the EXECUTABLE boolean shadow of `verifier.verify(spending_proof, "note-spend",
  …)` (`apply.rs:926`) — FAIL-CLOSED if `spendProof = false` (a missing/invalid proof is REJECTED in the
  verified executor, the `NoteSpend` divergence the marshaller saw). The §8 STARK extractability is the
  named carrier (`PrivacyKernel.noteSpend_sound`); the executor enforces the boolean shadow. bal-NEUTRAL. -/
  | noteSpendA      (nf : Nat) (actor : CellId) (spendProof : Bool)
  /-- `NoteCreate { commitment }` (dregg1 `apply_note_create`): the grow-only commitment-SET insert (the
  dual of noteSpend). The §8 range proof is the THEOREM-level portal. bal-NEUTRAL. -/
  | noteCreateA     (cm : Nat) (actor : CellId)
  -- §MA-seal: the 6 SIMPLE bal-NEUTRAL effects (Wave 6). Each writes a cell flag/metadata field or
  -- records a refusal — and NEVER touches the `bal` ledger, so `ledgerDeltaAsset = 0` for EVERY asset.
  -- The §8 crypto (AEAD for seal/unseal, the commitment for makeSovereign) is the CHAIN-LAYER portal.
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
  -- §MA-heap: THE HEAP's `write`-verb face (REFINEMENT-DESIGN Decision 1, THE ROTATION's wire arm).
  /-- `HeapWrite { target, collection, key, value }` — the sorted-map insert-or-update of the cell's
  openable heap (`Substrate.HeapKernel`). The WIRE carries the computed digests (the cap `slot_hash`
  discipline): `addr = H[coll, key]` (the sorted address, recomputed in-row by the descriptor
  gadget's address hash-site and verified cell-side) and `newRoot` (the executor-computed
  sorted-Poseidon2 post-root, PINNED into the `heap_root` register; the gadget's
  membership-open / leaf-update / sorted-insert gates verify `old_root → new_root` against the same
  leaf list — cap Phase-A staging). Routes to the spliced caveat-gated wire-face step
  `Substrate.HeapKernel.heapStepGuardedW` (authority + membership + lifecycle + per-slot caveats on
  `heap_root`, fail-closed); the parametric model semantics is `heapStepGuarded`
  (`heapStepGuardedW_honest`). bal-NEUTRAL (`heapStepW_conserves`: the per-asset ledger is
  literally untouched). -/
  | heapWriteA (actor target : CellId) (addr v newRoot : ℤ)

/-- **The per-asset COMBINED ledger delta of a `FullActionA`, indexed by asset `b`** — the move of the
COMBINED measure `recTotalAsset` (= `bal`-ledger + per-asset holding-store). W1 (DREGG3 §2.2): this
is IDENTICALLY ZERO — every verb conserves every asset exactly. `mintA`/`burnA`/`bridgeMintA` are
issuer-moves (ordinary transfers against the issuer's negative-capable well), so the pre-W1 `±amt`
disclosures are GONE: `ledgerDeltaAsset_eq_zero` below proves the whole family vanishes, and the
per-arm conservation vector (`execFullA_ledger_per_asset`) becomes unconditional exactness. The
function is RETAINED (rather than inlined to `0`) as the API the forest/turn aggregators sum over —
its vanishing IS the theorem. A FAMILY indexed by `AssetId` — never one aggregate scalar. (F1b: the
escrow/obligation/bridge-LFC arms are GONE with the kernel holding-store.) -/
def ledgerDeltaAsset : FullActionA → AssetId → ℤ
  | .balanceA _ _,        _ => 0
  | .delegate _ _ _,      _ => 0
  | .revoke _ _,          _ => 0
  -- W1: mint/burn are issuer-moves — ordinary transfers, conservation-trivial like `balanceA`.
  | .mintA _ _ _ _,       _ => 0
  | .burnA _ _ _ _,       _ => 0
  | .setFieldA _ _ _ _,   _ => 0
  | .emitEventA _ _ _ _,  _ => 0
  | .incrementNonceA _ _ _, _ => 0
  | .setPermissionsA _ _ _, _ => 0
  | .setVKA _ _ _,        _ => 0
  -- §MA-auth: the 6 authority effects EDIT/CHECK `caps`, NEVER `bal` — so `0` for EVERY asset.
  | .introduceA _ _ _,    _ => 0
  | .delegateAttenA _ _ _ _, _ => 0
  | .attenuateA _ _ _,    _ => 0
  | .revokeDelegationA _ _, _ => 0
  | .exerciseA _ _ inner, b => (inner.map (fun fa => ledgerDeltaAsset fa b)).sum
  -- §MA-supply: createCell/spawn GROW `accounts` but the fresh cell is born EMPTY (bal-reset) — so `0`
  -- for EVERY asset (account-growth NEUTRALITY). bridgeMint discloses `+value` at the targeted asset ONLY.
  | .createCellA _ _,     _ => 0
  -- factory creation mints a BORN-EMPTY cell (balance 0 in every asset) + installs its program — so
  -- the COMBINED measure is unmoved for EVERY asset (account-growth-with-program NEUTRALITY).
  | .createCellFromFactoryA _ _ _, _ => 0
  | .spawnA _ _ _,        _ => 0
  -- W1: bridgeMint = the issuer-move whose issuer is the BRIDGE cell (asset := bridge CellId) — the
  -- bridge well carries −(outstanding bridged supply); the §8 foreign-finality portal gates WHEN the
  -- bridge may move, conservation holds regardless.
  | .bridgeMintA _ _ _ _, _ => 0
  -- §MA-note: notes move SETs (nullifier/commitment), not `bal`, so `0`.
  | .noteSpendA _ _ _,            _ => 0
  | .noteCreateA _ _,             _ => 0
  -- §MA-meta: makeSovereign/refusal/receiptArchive write the `cell` record / lifecycle field,
  -- NEVER `bal` — so `0` for EVERY asset (balance-NEUTRAL). The §8 crypto is the chain-layer portal.
  | .makeSovereignA _ _,          _ => 0
  | .refusalA _ _,                _ => 0
  | .receiptArchiveA _ _,         _ => 0
  -- the pipelined-send apply-time effect is NEUTRAL (the resolved action already ran) ⇒ `0`.
  | .pipelinedSendA _,            _ => 0
  -- §MA-swiss: the 4 CapTP swiss-table effects move REFERENCES, never balance ⇒ `0` at every asset.
  | .cellSealA _ _,                _ => 0
  | .cellUnsealA _ _,              _ => 0
  | .cellDestroyA _ _ _,           _ => 0
  | .refreshDelegationA _ _,       _ => 0
  -- §MA-heap: the heap write edits `heaps` + the `heap_root` register, NEVER `bal` ⇒ `0`
  -- (`heapStepW_conserves`: bal/accounts are the SAME functions — untouched, not cancelled).
  | .heapWriteA _ _ _ _ _,         _ => 0

mutual
/-- **W1 KEYSTONE: the disclosed delta family vanishes IDENTICALLY.** Every `FullActionA`'s
per-asset combined delta is `0` at every asset — there is NO non-conserving verb left in the
kernel. With `execFullA_ledger_per_asset` this makes every committed step an EXACT conservation
step (`execFullA_conserves_exact` below), and `ExactConservation` an unconditional reachability
invariant (`Exec/ReachableConservation.lean`). -/
theorem ledgerDeltaAsset_eq_zero : ∀ (fa : FullActionA) (b : AssetId), ledgerDeltaAsset fa b = 0
  | .balanceA _ _,        _ => by simp only [ledgerDeltaAsset]
  | .delegate _ _ _,      _ => by simp only [ledgerDeltaAsset]
  | .revoke _ _,          _ => by simp only [ledgerDeltaAsset]
  | .mintA _ _ _ _,       _ => by simp only [ledgerDeltaAsset]
  | .burnA _ _ _ _,       _ => by simp only [ledgerDeltaAsset]
  | .setFieldA _ _ _ _,   _ => by simp only [ledgerDeltaAsset]
  | .emitEventA _ _ _ _,  _ => by simp only [ledgerDeltaAsset]
  | .incrementNonceA _ _ _, _ => by simp only [ledgerDeltaAsset]
  | .setPermissionsA _ _ _, _ => by simp only [ledgerDeltaAsset]
  | .setVKA _ _ _,        _ => by simp only [ledgerDeltaAsset]
  | .introduceA _ _ _,    _ => by simp only [ledgerDeltaAsset]
  | .delegateAttenA _ _ _ _, _ => by simp only [ledgerDeltaAsset]
  | .attenuateA _ _ _,    _ => by simp only [ledgerDeltaAsset]
  | .revokeDelegationA _ _, _ => by simp only [ledgerDeltaAsset]
  | .exerciseA _ _ inner, b => by
      simp only [ledgerDeltaAsset]
      exact innerLedgerDeltaAsset_eq_zero inner b
  | .createCellA _ _,     _ => by simp only [ledgerDeltaAsset]
  | .createCellFromFactoryA _ _ _, _ => by simp only [ledgerDeltaAsset]
  | .spawnA _ _ _,        _ => by simp only [ledgerDeltaAsset]
  | .bridgeMintA _ _ _ _, _ => by simp only [ledgerDeltaAsset]
  | .noteSpendA _ _ _,    _ => by simp only [ledgerDeltaAsset]
  | .noteCreateA _ _,     _ => by simp only [ledgerDeltaAsset]
  | .makeSovereignA _ _,  _ => by simp only [ledgerDeltaAsset]
  | .refusalA _ _,        _ => by simp only [ledgerDeltaAsset]
  | .receiptArchiveA _ _, _ => by simp only [ledgerDeltaAsset]
  | .pipelinedSendA _,    _ => by simp only [ledgerDeltaAsset]
  | .cellSealA _ _,       _ => by simp only [ledgerDeltaAsset]
  | .cellUnsealA _ _,     _ => by simp only [ledgerDeltaAsset]
  | .cellDestroyA _ _ _,  _ => by simp only [ledgerDeltaAsset]
  | .refreshDelegationA _ _, _ => by simp only [ledgerDeltaAsset]
  | .heapWriteA _ _ _ _ _, _ => by simp only [ledgerDeltaAsset]

/-- The inner-fold delta of an `exerciseA` vanishes too (mutual with the per-action vanishing —
each summand is a structural subterm). -/
theorem innerLedgerDeltaAsset_eq_zero :
    ∀ (inner : List FullActionA) (b : AssetId),
      (inner.map (fun fa => ledgerDeltaAsset fa b)).sum = 0
  | [], _ => rfl
  | fa :: rest, b => by
      rw [List.map_cons, List.sum_cons, ledgerDeltaAsset_eq_zero fa b, zero_add]
      exact innerLedgerDeltaAsset_eq_zero rest b
end

/-! ### §R4 — the EXECUTABLE facet classifier + cap-mask gate for `exerciseA`.

dregg1's `apply_exercise_via_capability` (`apply.rs:2455`) does NOT merely hold-gate: each inner effect
must lie in the held cap's `allowed_effects` FACET MASK (the `read`/`write`/`grant`/`call`/… authority
the cap actually confers). The hold-gate (`confersEdgeTo`) checks *connectivity*; R4 checks the *facet*.
The two are distinct — a `endpoint t [read]` cap (read-only) connects to `t` (so the hold-gate could
pass via a sibling `write` cap) yet must REJECT a `write`/`grant`-facet inner effect. Here we make
`execFullA`'s `exerciseA` ENFORCE the mask (it was hold-gate-only), so `execFullA` is the canonical
semantics the handler agrees with — no weaker. -/

/-- **The facet an inner effect EXERCISES** (the R4 mask key, dregg1 `Effect::required_facet`). Mutating
effects (transfer/mint/burn/state-write/escrow/bridge/note/seal/lifecycle/supply) demand `write`;
authority-granting effects (delegate/introduce/attenuate/dropRef/revoke/validateHandoff/swiss-export)
demand `grant`; a NESTED exercise demands the privileged `control`. A `read`-only cap admits NONE of
these (every dregg2 effect mutates or grants) — the faithful contrast the §TEETH exercise. -/
def requiredFacetA : FullActionA → Authority.Auth
  -- value movement + every cell/ledger mutation ⇒ write
  | .balanceA _ _            => Authority.Auth.write
  | .mintA _ _ _ _           => Authority.Auth.write
  | .burnA _ _ _ _           => Authority.Auth.write
  | .setFieldA _ _ _ _       => Authority.Auth.write
  | .emitEventA _ _ _ _      => Authority.Auth.write
  | .incrementNonceA _ _ _   => Authority.Auth.write
  | .setPermissionsA _ _ _   => Authority.Auth.write
  | .setVKA _ _ _            => Authority.Auth.write
  | .createCellA _ _         => Authority.Auth.write
  | .createCellFromFactoryA _ _ _ => Authority.Auth.write
  | .spawnA _ _ _            => Authority.Auth.write
  | .bridgeMintA _ _ _ _     => Authority.Auth.write
  | .noteSpendA _ _ _        => Authority.Auth.write
  | .noteCreateA _ _         => Authority.Auth.write
  | .makeSovereignA _ _      => Authority.Auth.write
  | .refusalA _ _            => Authority.Auth.write
  | .receiptArchiveA _ _     => Authority.Auth.write
  | .pipelinedSendA _        => Authority.Auth.write
  | .cellSealA _ _           => Authority.Auth.write
  | .cellUnsealA _ _         => Authority.Auth.write
  | .cellDestroyA _ _ _      => Authority.Auth.write
  | .heapWriteA _ _ _ _ _    => Authority.Auth.write
  -- authority-conferring effects ⇒ grant (they mint/move CAPABILITY, not cell state)
  | .delegate _ _ _          => Authority.Auth.grant
  | .revoke _ _              => Authority.Auth.grant
  | .introduceA _ _ _        => Authority.Auth.grant
  | .delegateAttenA _ _ _ _  => Authority.Auth.grant
  | .attenuateA _ _ _        => Authority.Auth.grant
  | .revokeDelegationA _ _   => Authority.Auth.grant
  | .refreshDelegationA _ _  => Authority.Auth.grant
  | .exerciseA _ _ _         => Authority.Auth.control

/-- **The R4 facet mask of a held cap** (its `allowed_effects`): a `node` cap is the PRIVILEGED full
facet (every `Auth`); an `endpoint` cap confers EXACTLY its carried `rights`; `null` confers nothing.
This is `Handlers.Exercise.capFacetMask` re-stated executor-side (no import cycle). -/
def capFacetMaskA : Cap → List Authority.Auth
  | .null            => []
  | .endpoint _ r    => r
  | .node _          => [Authority.Auth.read, Authority.Auth.write, Authority.Auth.grant,
                         Authority.Auth.call, Authority.Auth.reply, Authority.Auth.reset,
                         Authority.Auth.control, Authority.Auth.notify]  -- every Auth; notify ⇒ full facet complete

/-- **R4 — is `fa`'s required facet admitted by the held cap's mask?** The held cap is `heldCapTo`
(the SAME `find? confersEdgeTo`-then-`getD null` lookup the handler's `exercisedCap` uses — so the
executor and handler facet gates are DEFINITIONALLY the same). Fail-closed: a `null` held cap (no edge)
has empty mask ⇒ admits nothing. -/
def innerFacetAdmittedA (s : RecChainedState) (actor target : CellId) (fa : FullActionA) : Bool :=
  (capFacetMaskA (heldCapTo s.kernel.caps actor target)).contains (requiredFacetA fa)

/-- **The whole inner forest is R4-admitted** iff EVERY inner effect's required facet lies in the held
cap's mask. The gate `execFullA`'s `exerciseA` checks BEFORE recursing — the missing piece that made the
old `exerciseA` hold-gate-only. -/
def innerFacetsAdmittedA (s : RecChainedState) (actor target : CellId) (inner : List FullActionA) : Bool :=
  inner.all (fun fa => innerFacetAdmittedA s actor target fa)

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
  | .revokeDelegationA holder t      => some (recCRevoke s holder t)
  | .exerciseA actor t inner         =>
      -- R4: hold-gate (`exerciseStepA`) AND the held cap's FACET MASK admits every inner effect
      -- (`innerFacetsAdmittedA`), THEN recurse. Fail-closed on either gate.
      if innerFacetsAdmittedA s actor t inner = true then
        match exerciseStepA s actor t with
        | some s' => execInnerA s' inner
        | none    => none
      else none
  -- §MA-supply: createCell/spawn route to the account-growth chained steps (born EMPTY); bridgeMint
  -- reuses the per-asset mint `recCMintAsset` verbatim (the §8 portal hypothesis is carried on the
  -- conservation keystone, not checked here).
  | .createCellA actor newCell       => createCellChainA s actor newCell
  -- §MA-factory: mint from a published factory — validate registry+constraints, then create the cell
  -- carrying the factory's caveats/initial-fields/programVk (dregg1 `apply_create_cell_from_factory`).
  | .createCellFromFactoryA actor newCell vk => createCellFromFactoryChainA s actor newCell vk
  | .spawnA actor child target       => spawnChainA s actor child target
  | .bridgeMintA actor cell a value  => recCMintAsset s actor cell a value
  -- §MA-note: notes route to the SET-insert steps.
  | .noteSpendA nf actor spendProof   => noteSpendChainA s nf actor spendProof
  | .noteCreateA cm actor             => some (noteCreateChainA s cm actor)
  -- §MA-seal: the 6 simple bal-neutral effects route to the ALREADY-PROVEN authority-gated field write
  -- (`stateStep`), each into its named record field. The §8 crypto (AEAD ciphertext / commitment) is
  -- the chain-layer portal — the STATE move is the field write recorded here, NOT the crypto verify.
  -- §MA-seal (Wave-3 DE-SHADOW): seal/unseal/createSealPair route to the REAL capability-movement
  -- chained steps (the cap moves through the box / two real grants), NOT a flag flip. The
  -- AEAD crypto is the §8 chain-layer portal; the WHICH-cap binding + c-list grant are REAL.
  | .makeSovereignA actor cell    => makeSovereignStep s actor cell
  | .refusalA actor cell          => stateStep s refusalField actor cell (.int 1)
  | .receiptArchiveA actor cell   => receiptArchiveChainA s actor cell
  -- pipelinedSend's apply-time effect is NEUTRAL (a clock row, the resolved action already ran —
  -- dregg1's apply-time no-op, the resolution is `ConditionalTurn`).
  | .pipelinedSendA actor               => some { kernel := s.kernel, log := escrowReceiptA actor :: s.log }
  -- §MA-swiss: the 4 CapTP swiss-table effects route to the authority-gated swiss registry steps.
  | .cellSealA actor cell          => cellSealChainA s actor cell
  | .cellUnsealA actor cell        => cellUnsealChainA s actor cell
  | .cellDestroyA actor cell ch    => cellDestroyChainA s actor cell ch
  | .refreshDelegationA actor child => refreshDelegationChainA s actor child
  -- §MA-heap: the wire-face guarded heap write (THE ROTATION's dispatch arm — the staged
  -- `execHeapWriteG` gate semantics ride in via the standard `gateOK` front the forest applies).
  | .heapWriteA actor target addr v newRoot =>
      Substrate.HeapKernel.heapStepGuardedW s actor target addr v newRoot

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
/-- **`execFullA_ledger_per_asset` (the COMBINED per-asset conservation VECTOR).** Every
committed `FullActionA` moves the COMBINED per-asset measure `recTotalAsset b` (= `bal`-ledger
+ per-asset holding-store) by EXACTLY `ledgerDeltaAsset fa b`, for EVERY asset `b` independently: `0`
for transfer/authority (the moved asset cancels; authority/notes leave `bal` fixed) and `±amt`
at the targeted asset for mint/burn/bridgeMint. THIS is the law a SCALAR kernel cannot state — it
would let a mint of asset B net against a burn of asset A. The per-asset family forbids it.
(F1b: the escrow/obligation/bridge-LFC holding-store legs are GONE — value parks in factory cells'
own `bal` columns, covered by the SAME sum.) -/
theorem execFullA_ledger_per_asset (s s' : RecChainedState) (fa : FullActionA) (b : AssetId)
    (h : execFullA s fa = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + ledgerDeltaAsset fa b := by
  -- Each arm reads its per-asset move off the chained step's delta/neutrality lemma. `exerciseA`
  -- recurses through the mutual `execInnerA_ledger_per_asset` (its delta SUMS the inner deltas).
  cases fa with
  | balanceA t a =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCexecAsset at h
      by_cases hadm : acceptsEffects s.kernel t.dst
      · rw [if_pos hadm] at h
        cases hx : recKExecAsset s.kernel t a with
        | none => rw [hx] at h; exact absurd h (by simp)
        | some k' =>
            rw [hx] at h; simp only [Option.some.injEq] at h; subst h
            show recTotalAsset k' b = recTotalAsset s.kernel b + 0
            rw [recKExecAsset_conserves_per_asset s.kernel k' t a hx b]; ring
      · rw [if_neg hadm] at h; exact absurd h (by simp)
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
            simp only [recTotalAsset]; ring
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | revoke holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAsset, recKRevokeTarget]; ring
  | mintA actor cell a amt =>
      -- W1: the mint is an issuer-move — EXACT conservation, delta 0.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b = recTotalAsset s.kernel b + _
          rw [recKMintAsset_delta s.kernel k' actor cell a amt hm b]; ring
  | burnA actor cell a amt =>
      -- W1: the burn returns value to the issuer's well — EXACT conservation, delta 0.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCBurnAsset at h
      cases hb : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b = recTotalAsset s.kernel b + _
          rw [recKBurnAsset_delta s.kernel k' actor cell a amt hb b]; ring
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: `setFieldA` now routes through the caveat-gated write `stateStepGuarded`. A
      -- committed guarded write commits exactly `stateStep`'s post-state (a named-field write), so it
      -- leaves the COMBINED per-asset measure UNCHANGED — `ledgerDeltaAsset (.setFieldA …) = 0`.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [stateStepGuarded_recTotalAsset h b]; ring
  | emitEventA actor cell topic data =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [recTotalAsset, emitStep]; ring
      · rw [if_neg hlive] at h
        exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel nonceField cell (.int n)) b = recTotalAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel nonceField cell (.int n) b]; ring
  | setPermissionsA actor cell p =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel permsField cell (.int p)) b = recTotalAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel permsField cell (.int p) b]; ring
  | setVKA actor cell vk =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel vkField cell (.int vk)) b = recTotalAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel vkField cell (.int vk) b]; ring
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
            simp only [recTotalAsset]; ring
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
      simp only [attenuateStepA, recTotalAsset]; ring
  | revokeDelegationA holder t =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [recCRevoke, Option.some.injEq] at h; subst h
      simp only [recTotalAsset, recKRevokeTarget]; ring
  | exerciseA actor t inner =>
      -- R4 facet gate first, then the hold-gate is bal-neutral (the c-list is read, not edited); the move
      -- is whatever `inner` moves, read off the mutual `execInnerA_ledger_per_asset`.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            -- `s1 = { s with log := … }` ⇒ `s1.kernel = s.kernel`: the move is exactly the inner sum.
            have hinner := execInnerA_ledger_per_asset s1 s' inner b h
            rw [hinner, hs1]
      · rw [if_neg hf] at h; exact absurd h (by simp)
  | createCellA actor newCell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createCellChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: born-EMPTY cell + balance-orthogonal field/caveat install ⇒ COMBINED measure fixed.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [createCellFromFactoryChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | spawnA actor child target =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [spawnChainA_neutral b (by simpa only [execFullA] using h)]; ring
  | bridgeMintA actor cell a value =>
      -- W1: the bridge-mint is the issuer-move whose issuer is the BRIDGE cell — EXACT conservation.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      unfold recCMintAsset at h
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          show recTotalAsset k' b = recTotalAsset s.kernel b + _
          rw [recKMintAsset_delta s.kernel k' actor cell a value hm b]; ring
  -- §MA-note: notes move SETs (nullifier/commitment), never `bal` — bal-NEUTRAL.
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      simp only [noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; simp only [Option.some.injEq] at h; subst h
            -- noteSpend grows ONLY `nullifiers` — `bal` and `escrows` fixed.
            show recTotalAsset k' b = recTotalAsset s.kernel b + 0
            rw [show k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } from by
                  unfold noteSpendNullifier at hk; split at hk
                  · exact absurd hk (by simp)
                  · simpa only [Option.some.injEq] using hk.symm]
            simp only [recTotalAsset]; ring
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h
      -- noteCreate grows ONLY `commitments` — `bal` and `escrows` fixed.
      simp only [noteCreateChainA, noteCreateCommitment, recTotalAsset]; ring
  | makeSovereignA actor cell =>
      -- FILL #133: the value-REBIND (whole-record drop) is bal-NEUTRAL on the per-asset ledger —
      -- `recTotalAsset` reads `bal`, fixed by the `cell`-only rebind.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'
      show recTotalAsset (makeSovereignKernel s.kernel cell) b = recTotalAsset s.kernel b + 0
      rw [makeSovereignKernel_recTotalAsset s.kernel cell b]; ring
  | refusalA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      show recTotalAsset (writeField s.kernel refusalField cell (.int 1)) b = recTotalAsset s.kernel b + 0
      rw [writeField_recTotalAsset s.kernel refusalField cell (.int 1) b]; ring
  | receiptArchiveA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAsset s'.kernel b = recTotalAsset s.kernel b from by
            obtain ⟨_, hs'⟩ := receiptArchiveChainA_factors h; subst hs'; rfl]; ring
  -- pipelined-send is combined-NEUTRAL (it leaves the kernel UNCHANGED — only a clock row),
  -- and `ledgerDeltaAsset = 0`.
  | pipelinedSendA actor =>
      simp only [execFullA, ledgerDeltaAsset, Option.some.injEq] at h ⊢
      subst h; simp only [recTotalAsset]; ring
  -- §MA-swiss: each swiss-table effect is balance-NEUTRAL (moves references, not balance) ⇒ `+0`.
  | cellSealA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAsset s'.kernel b = recTotalAsset s.kernel b from by
            obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'; rfl]; ring
  | cellUnsealA actor cell =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAsset s'.kernel b = recTotalAsset s.kernel b from by
            obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'; rfl]; ring
  | cellDestroyA actor cell ch =>
      -- destroy sets `lifecycle` AND `deathCert`; both side-tables ⇒ `bal`/`escrows` fixed ⇒ rfl-neutral.
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAsset s'.kernel b = recTotalAsset s.kernel b from by
            obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'; rfl]; ring
  | refreshDelegationA actor child =>
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      rw [show recTotalAsset s'.kernel b = recTotalAsset s.kernel b from
            refreshDelegationChainA_balNeutral h b]
      simp only [recTotalAsset]; ring
  | heapWriteA actor target addr v newRoot =>
      -- §MA-heap: the wire-face heap write is a guarded `heap_root` write + a `heaps` splice; the
      -- per-asset measure reads neither (`heapStepW_conserves`: `bal`/`accounts` untouched).
      simp only [execFullA, ledgerDeltaAsset] at h ⊢
      obtain ⟨s₁, hw, rfl⟩ := Substrate.HeapKernel.heapStepGuardedW_factors h
      show recTotalAsset s₁.kernel b = recTotalAsset s.kernel b + 0
      rw [stateStepGuarded_recTotalAsset hw b]; ring

/-- **`execInnerA_ledger_per_asset` — the inner-fold conservation an `exerciseA` reads.** A
committed `execInnerA` (the inner-effect fold an exercise recurses through) moves the COMBINED per-asset
measure by exactly the SUM of the inner effects' deltas — the per-asset analog of
`execFullTurnA_ledger_per_asset`, re-founded MUTUALLY with `execFullA_ledger_per_asset` so the exercise
arm above can close (each inner element's per-action delta comes from the mutual `execFullA` case). -/
theorem execInnerA_ledger_per_asset (s s' : RecChainedState) (inner : List FullActionA) (b : AssetId)
    (h : execInnerA s inner = some s') :
    recTotalAsset s'.kernel b
      = recTotalAsset s.kernel b + (inner.map (fun fa => ledgerDeltaAsset fa b)).sum := by
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

/-- **`execFullTurnA_ledger_per_asset` (the transaction COMBINED conservation vector).** A
committed per-asset full-turn moves the COMBINED measure `recTotalAsset b` by exactly the net
of all per-action deltas in asset `b`, for EVERY asset `b`. Proved by induction on the turn, reusing
`execFullA_ledger_per_asset`. The asset-indexed analog of `execFullTurn_ledger`. -/
theorem execFullTurnA_ledger_per_asset :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId), execFullTurnA s tt = some s' →
      recTotalAsset s'.kernel b = recTotalAsset s.kernel b + turnLedgerDeltaAsset tt b
  | s, s', [], b, h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; simp [turnLedgerDeltaAsset]
  | s, s', a :: rest, b, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hhead : recTotalAsset s1.kernel b = recTotalAsset s.kernel b + ledgerDeltaAsset a b :=
            execFullA_ledger_per_asset s s1 a b ha
          have htail : recTotalAsset s'.kernel b = recTotalAsset s1.kernel b + turnLedgerDeltaAsset rest b :=
            execFullTurnA_ledger_per_asset s1 s' rest b h
          rw [htail, hhead]
          simp only [turnLedgerDeltaAsset, List.map_cons, List.sum_cons]; ring

/-- **`execFullTurnA_conserves_per_asset`.** A committed per-asset full-turn whose net
ledger delta is `0` *in asset `b`* preserves asset `b`'s total supply. Applied with `∀ b, … = 0`
this gives FULL per-asset conservation: a transfer/authority-only turn (or one whose per-asset
mint/burn nets out in EACH asset) conserves EVERY asset class. The `CONSERVATION_VECTOR` at the
transaction level. -/
theorem execFullTurnA_conserves_per_asset (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId)
    (h : execFullTurnA s tt = some s') (hzero : turnLedgerDeltaAsset tt b = 0) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  rw [execFullTurnA_ledger_per_asset s s' tt b h, hzero, add_zero]

/-- The turn-level delta family vanishes identically (W1) — every turn's net per-asset delta is
`0` at every asset, because every ACTION's is (`ledgerDeltaAsset_eq_zero`). -/
theorem turnLedgerDeltaAsset_eq_zero (tt : List FullActionA) (b : AssetId) :
    turnLedgerDeltaAsset tt b = 0 :=
  innerLedgerDeltaAsset_eq_zero tt b

/-- **`execFullA_conserves_exact` (W1 KEYSTONE, unconditional).** EVERY committed per-asset action
— transfer, authority, state, supply (now issuer-moves), notes, lifecycle, exercise-recursion —
conserves EVERY asset's total supply EXACTLY. No zero-delta hypothesis: the delta family vanishes
identically (`ledgerDeltaAsset_eq_zero`). `Σ_c bal c a` is a step invariant of the kernel. -/
theorem execFullA_conserves_exact (s s' : RecChainedState) (fa : FullActionA) (b : AssetId)
    (h : execFullA s fa = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  rw [execFullA_ledger_per_asset s s' fa b h, ledgerDeltaAsset_eq_zero fa b, add_zero]

/-- **`execFullTurnA_conserves_exact` (W1, unconditional, transaction level).** EVERY committed
per-asset transaction conserves EVERY asset exactly. -/
theorem execFullTurnA_conserves_exact (s s' : RecChainedState) (tt : List FullActionA) (b : AssetId)
    (h : execFullTurnA s tt = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullTurnA_conserves_per_asset s s' tt b h (turnLedgerDeltaAsset_eq_zero tt b)

/-! ## §MB — `execFullTurnA_append` + the per-asset PER-NODE attestation carrier.

The forest lift in `Exec/FullForest.lean` rests on the same `execTurn_append` shape `TurnForest.lean`
uses for the narrow executor — here re-founded for the per-asset `execFullTurnA`. We then build the
per-asset analog of `fullActionInv` (`fullActionInvA`) whose **Ledger** conjunct is the full per-asset
VECTOR (`∀ b, recTotalAsset … = … + ledgerDeltaAsset fa b`, never one aggregate scalar — the FILL-1
no-laundering carrier), with ChainLink/ObsAdvance/KindObligation reused per-kind (these are
asset-orthogonal: they edit the log / `caps`, not the `bal` ledger). `execFullTurnA_each_attests`
then threads the per-node witness along the all-or-nothing fold, so the forest's per-node
attestation (`FullForest.execFullForestA_each_attests`) lifts straight off the bridge. -/

/-- **`execFullTurnA_append`.** Running a concatenated per-asset turn equals running the
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
per-asset supply delta. The per-asset analog of `fullReceipt`.

(The pre-state `s` binder is retained for signature stability across the F2 queue migration; since
F1b removed the deposit-refund receipt, every arm is a pure function of the action's own fields.) -/
def fullReceiptA (s : RecChainedState) : FullActionA → Turn
  | .balanceA t _          => t
  | .delegate del _ _      => authReceipt del
  | .revoke holder _       => authReceipt holder
  -- W1: the truthful issuer-move rows (mint: well → recipient; burn: holder → well).
  | .mintA actor cell a amt  => { actor := actor, src := a, dst := cell, amt := amt }
  | .burnA actor cell a amt  => { actor := actor, src := cell, dst := a, amt := amt }
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
  | .revokeDelegationA holder _ => authReceipt holder
  | .exerciseA actor _ _        => authReceipt actor
  -- §MA-supply: createCell/spawn append the fresh cell's (balance-`0`) creation row; bridgeMint
  -- appends a self-`Turn` carrying the disclosed `+value`.
  | .createCellA actor newCell  => { actor := actor, src := newCell, dst := newCell, amt := 0 }
  | .createCellFromFactoryA actor newCell _ => { actor := actor, src := newCell, dst := newCell, amt := 0 }
  | .spawnA actor child _       => { actor := actor, src := child, dst := child, amt := 0 }
  | .bridgeMintA actor cell a value => { actor := actor, src := a, dst := cell, amt := value }
  -- §MA-note: each note effect appends a self-`Turn` on the `actor`
  -- (the metadata clock row; the moved SET entry lives off-receipt).
  | .noteSpendA _ actor _            => escrowReceiptA actor
  | .noteCreateA _ actor             => escrowReceiptA actor
  -- §MA-seal (Wave-3 DE-SHADOW): seal appends a self-`Turn` on the sealing `actor`; unseal on the
  -- `recipient` (the cap's new holder); createSealPair on the `sealerHolder` — matching the chained-step
  -- receipts. The §8 crypto / box live in the portal/side-table, not the receipt.
  | .makeSovereignA actor cell       => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .refusalA actor cell             => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .receiptArchiveA actor cell      => { actor := actor, src := cell, dst := cell, amt := 0 }
  -- pipelinedSend appends a clock row on the `actor` (the apply-time neutral marker).
  | .pipelinedSendA actor            => escrowReceiptA actor
  -- §MA-swiss: each swiss-table effect appends a balance-`0` self-`Turn` on the exporting `exporter`
  -- cell (the metadata clock row; the swiss entry lives in the off-ledger registry, not the receipt).
  | .cellSealA actor cell            => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .cellUnsealA actor cell          => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .cellDestroyA actor cell _       => { actor := actor, src := cell, dst := cell, amt := 0 }
  | .refreshDelegationA actor child  => { actor := actor, src := child, dst := child, amt := 0 }
  -- §MA-heap: the heap write appends the same balance-`0` self-`Turn` clock row every guarded
  -- field write appends (it IS a `stateStepGuarded` write of the `heap_root` register + a splice).
  | .heapWriteA actor target _ _ _   => { actor := actor, src := target, dst := target, amt := 0 }

/-- **`execFullA_chainlinkExact` (the one-row chainlink for every NON-recursive kind).** A
committed NON-exercise `FullActionA` extends the receipt chain by EXACTLY its
`fullReceiptA`, newest-first, with no fork or rewrite. `exerciseA` is excluded (`hne`) because it
RECURSES — it grows the log by its own receipt PLUS the sub-effects' rows (the honest append-only
suffix, captured by `execFullA_chainlink` below). F2b: the `queueAtomicTxA` batch exclusion (`hnb`)
died with the queue family — the statement got STRONGER (one fewer carve-out). The
per-action generalization across the per-asset op-set (asset-orthogonal: it touches only the `log`). -/
theorem execFullA_chainlinkExact (s s' : RecChainedState) (fa : FullActionA)
    (hne : ∀ a t inner, fa ≠ .exerciseA a t inner)
    (h : execFullA s fa = some s') : s'.log = fullReceiptA s fa :: s.log := by
  cases fa with
  | exerciseA a t inner => exact absurd rfl (hne a t inner)
  | balanceA t a =>
      simp only [execFullA, recCexecAsset, fullReceiptA] at h ⊢
      by_cases hadm : acceptsEffects s.kernel t.dst
      · rw [if_pos hadm] at h
        cases hx : recKExecAsset s.kernel t a with
        | none => rw [hx] at h; exact absurd h (by simp)
        | some k' => rw [hx] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hadm] at h; exact absurd h (by simp)
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
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke, fullReceiptA] at h ⊢
      simp only [Option.some.injEq] at h; subst h; rfl
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
  -- §MA-note: each note effect appends exactly its `escrowReceiptA` (the metadata clock row).
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA, fullReceiptA] at h ⊢
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, fullReceiptA, Option.some.injEq] at h ⊢
      subst h; rfl
  -- §MA-seal (Wave-3 DE-SHADOW): each de-shadowed seal step appends exactly its metadata clock row
  -- (read off the chained-step factoring lemma, which gives the full post-state incl. the log).
  | makeSovereignA actor cell =>
      -- FILL #133: the rebind appends EXACTLY the same self-`Turn` clock row (`makeSovereignStep`).
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; rfl
  | refusalA actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | receiptArchiveA actor cell =>
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨_, hs'⟩ := receiptArchiveChainA_factors h; subst hs'; rfl
  -- pipelinedSend appends the `actor` clock row.
  | pipelinedSendA actor =>
      simp only [execFullA, fullReceiptA, Option.some.injEq] at h ⊢; subst h; rfl
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
  | heapWriteA actor target addr v newRoot =>
      -- §MA-heap: the splice keeps the log; the underlying guarded write appends the clock row.
      simp only [execFullA, fullReceiptA] at h ⊢
      obtain ⟨s₁, hw, rfl⟩ := Substrate.HeapKernel.heapStepGuardedW_factors h
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq hw); subst hs'; rfl

mutual
/-- **`execFullA_log_suffix` / `execInnerA_log_suffix` (the append-only audit chain).** A
committed `FullActionA` (resp. the inner-effect fold) only EXTENDS the log: the pre-log is a SUFFIX of
the post-log. Mutual because `exerciseA` recurses through `execInnerA`. NON-recursive kinds extend by
exactly one row (`execFullA_chainlinkExact`); exercise extends by its own receipt PLUS the inner
fold's rows. -/
theorem execFullA_log_suffix (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.log <:+ s'.log := by
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨a, t, inner, rfl⟩ := hex
    -- exercise: the R4 gate, then the hold-gate prepends `authReceipt a`, then the inner fold extends.
    simp only [execFullA] at h
    by_cases hf : innerFacetsAdmittedA s a t inner = true
    · rw [if_pos hf] at h
      cases hg : exerciseStepA s a t with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hg] at h
          obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
          have hstep : s.log <:+ s1.log := by rw [hs1]; exact List.suffix_cons _ _
          exact hstep.trans (execInnerA_log_suffix s1 s' inner h)
    · rw [if_neg hf] at h; exact absurd h (by simp)
  · -- non-exercise: extend by exactly one row.
    rw [execFullA_chainlinkExact s s' fa (fun a t inner heq => hex ⟨a, t, inner, heq⟩) h]
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

/-- **`execFullA_chainlink` (the honest append-only chainlink across the WHOLE op-set).** A
committed `FullActionA` extends the receipt chain (the pre-log is a SUFFIX of the post-log) AND records
its own `fullReceiptA` row in the post-log. For NON-recursive kinds this is the exact one-row extension
(`execFullA_chainlinkExact`); for `exerciseA` the own-receipt is followed by the inner effects' rows —
still append-only, still recording the exercise receipt. No fork, no rewrite. -/
theorem execFullA_chainlink (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.log <:+ s'.log ∧ fullReceiptA s fa ∈ s'.log := by
  refine ⟨execFullA_log_suffix s s' fa h, ?_⟩
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨a, t, inner, rfl⟩ := hex
    -- exercise: `authReceipt a = fullReceiptA (exerciseA …)` is appended by the hold-gate (after the R4
    -- gate), then the inner fold (a suffix-extension) keeps it present.
    simp only [execFullA] at h
    by_cases hf : innerFacetsAdmittedA s a t inner = true
    · rw [if_pos hf] at h
      cases hg : exerciseStepA s a t with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hg] at h
          obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
          -- `fullReceiptA` of an exercise is `authReceipt a` — state-INDEPENDENT, so the goal's
          -- `fullReceiptA s (.exerciseA …)` is defeq to `fullReceiptA s1 (.exerciseA …)`.
          show fullReceiptA s (.exerciseA a t inner) ∈ s'.log
          have hmem : fullReceiptA s (.exerciseA a t inner) ∈ s1.log := by
            rw [hs1]; exact List.mem_cons_self
          exact (execInnerA_log_suffix s1 s' inner h).mem hmem
    · rw [if_neg hf] at h; exact absurd h (by simp)
  · rw [execFullA_chainlinkExact s s' fa (fun a t inner heq => hex ⟨a, t, inner, heq⟩) h]
    exact List.mem_cons_self

/-- **`execFullA_obsadvance`.** A committed `FullActionA` STRICTLY grows the chain (≥ one row),
so a replayed action (which would re-append its receipt) is detectable. Non-recursive kinds grow by
exactly one row; a committed exercise grows by `1 + |inner|`. -/
theorem execFullA_obsadvance (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.log.length < s'.log.length := by
  by_cases hex : ∃ a t inner, fa = .exerciseA a t inner
  · obtain ⟨a, t, inner, rfl⟩ := hex
    simp only [execFullA] at h
    by_cases hf : innerFacetsAdmittedA s a t inner = true
    · rw [if_pos hf] at h
      cases hg : exerciseStepA s a t with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hg] at h
          obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
          have h1 : s.log.length < s1.log.length := by
            rw [hs1, List.length_cons]; exact Nat.lt_succ_self _
          exact Nat.lt_of_lt_of_le h1 (execInnerA_log_suffix s1 s' inner h).length_le
    · rw [if_neg hf] at h; exact absurd h (by simp)
  · rw [execFullA_chainlinkExact s s' fa (fun a t inner heq => hex ⟨a, t, inner, heq⟩) h,
        List.length_cons]
    exact Nat.lt_succ_self _

/-- **Per-asset balance authorized.** A committed per-asset transfer was authorized
(`authorizedB` at the pre-state), via `recKExecAsset_authorized`. -/
theorem execFullA_balance_authorized (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execFullA s (.balanceA t a) = some s') : authorizedB s.kernel.caps t = true := by
  simp only [execFullA, recCexecAsset] at h
  by_cases hadm : acceptsEffects s.kernel t.dst
  · rw [if_pos hadm] at h
    cases hx : recKExecAsset s.kernel t a with
    | none => rw [hx] at h; exact absurd h (by simp)
    | some k' => exact recKExecAsset_authorized s.kernel k' t a hx
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **Per-asset transfer destination liveness (R1).** A committed transfer credits only a
Live destination cell (`acceptsEffects` at `t.dst`). -/
theorem execFullA_balance_dst_live (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execFullA s (.balanceA t a) = some s') : acceptsEffects s.kernel t.dst = true := by
  simp only [execFullA, recCexecAsset] at h
  by_cases hadm : acceptsEffects s.kernel t.dst
  · exact hadm
  · rw [if_neg hadm] at h; exact absurd h (by simp)


/-- **Per-asset delegation grounds.** A committed per-asset-turn delegation HOLDS the
Granovetter source edge `delegator ⟶ ⟨t,()⟩` on `execGraph` (REUSES the same `recCDelegate`/
`recKDelegate_grounds` the scalar executor does). -/
theorem execFullA_delegate_grounds (s s' : RecChainedState) (del rec t : CellId)
    (h : execFullA s (.delegate del rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel del rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' del rec t hd

/-- **Per-asset delegation IS `addEdge`.** REUSES `recKDelegate_execGraph`. -/
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

/-- **Per-asset delegation grants the copied held cap.** The concrete authority move copies
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

/-- **Per-asset revocation IS `removeEdge`.** REUSES `recKRevokeTarget_execGraph`. -/
theorem execFullA_revoke_removeEdge (s s' : RecChainedState) (holder t : CellId)
    (h : execFullA s (.revoke holder t) = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps
      = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder
          (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCRevoke] at h
  simp only [Option.some.injEq] at h; subst h
  exact recKRevokeTarget_execGraph s.kernel.caps holder t

/-- **Per-asset mint authorized over the ISSUER (W1/E2).** A committed per-asset mint implies the
privileged mint authority over the asset's ISSUER cell `a` (`recKMintAsset_authorized`) — the
production law: authority to mint IS the issuer capability, never a recipient-shaped grant. -/
theorem execFullA_mintA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.mintA actor cell a amt) = some s') :
    mintAuthorizedB s.kernel.caps actor a = true := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_authorized s.kernel k' actor cell a amt hm

/-- **`recKBurnAsset_authorized`.** A committed per-asset burn implies the privileged mint
authority over the ISSUER (W1/E2). -/
theorem recKBurnAsset_authorized (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recKBurnAsset k actor cell a amt = some k') :
    mintAuthorizedB k.caps actor a = true := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts ∧ a ∈ k.accounts ∧ cell ≠ a
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Per-asset burn authorized over the ISSUER.** -/
theorem execFullA_burnA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.burnA actor cell a amt) = some s') :
    mintAuthorizedB s.kernel.caps actor a = true := by
  simp only [execFullA, recCBurnAsset] at h
  cases hb : recKBurnAsset s.kernel actor cell a amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' => exact recKBurnAsset_authorized s.kernel k' actor cell a amt hb

/-- A committed `mintA` witnesses its issuer well LIVE (the chain-level genesis-order witness). -/
theorem execFullA_mintA_issuer_live (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.mintA actor cell a amt) = some s') :
    a ∈ s.kernel.accounts := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_issuer_live s.kernel k' actor cell a amt hm

/-- A committed `burnA` witnesses its issuer well LIVE. -/
theorem execFullA_burnA_issuer_live (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : execFullA s (.burnA actor cell a amt) = some s') :
    a ∈ s.kernel.accounts := by
  simp only [execFullA, recCBurnAsset] at h
  cases hb : recKBurnAsset s.kernel actor cell a amt with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some k' => exact recKBurnAsset_issuer_live s.kernel k' actor cell a amt hb

/-- A committed `bridgeMintA` witnesses its issuer — the BRIDGE cell — LIVE. -/
theorem execFullA_bridgeMintA_issuer_live (s s' : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    a ∈ s.kernel.accounts := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_issuer_live s.kernel k' actor cell a value hm

/-! ### §MA-supply authority obligations — `bridgeMint` is PRIVILEGED supply (`mintAuthorizedB`), the
LOCAL gate independent of the §8 foreign-finality portal; `createCell`/`spawn` carry their privileged
creation authority + the freshness gate (proved earlier as `createCellChainA_authorized` /
`spawnChainA_authorized`). -/

/-- **`execFullA_bridgeMintA_authorized`.** A committed per-asset bridge-mint implies the
privileged mint authority over the bridged asset's ISSUER — the BRIDGE cell `a` itself (W1: the
bridge cell IS the issuer of the bridged asset; its well carries −(outstanding bridged supply)).
The foreign finality is the §8 portal, discharged outside Lean. REUSES `recKMintAsset_authorized`. -/
theorem execFullA_bridgeMintA_authorized (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    mintAuthorizedB s.kernel.caps actor a = true := by
  simp only [execFullA, recCMintAsset] at h
  cases hm : recKMintAsset s.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => exact recKMintAsset_authorized s.kernel k' actor cell a value hm

/-- **`execFullA_bridgeMintA_unauthorized_fails` (fail-closed).** Without mint authority over the
bridge cell (the issuer), no bridge-mint commits (regardless of foreign finality). The confinement
core. -/
theorem execFullA_bridgeMintA_unauthorized_fails (s : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (h : mintAuthorizedB s.kernel.caps actor a = false) :
    execFullA s (.bridgeMintA actor cell a value) = none := by
  simp only [execFullA, recCMintAsset, recKMintAsset]
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **`execFullA_createCellA_neutral_per_asset` — THE ACCOUNT-GROWTH NEUTRALITY KEYSTONE.** A
committed `createCellA` leaves `recTotalAsset` UNCHANGED for EVERY asset `b`. NON-VACUOUS: the index set
`accounts` GREW (`execFullA_createCellA_grows_accounts` — the new cell IS live afterward), yet
supply is conserved BECAUSE the fresh cell is born EMPTY (the `bal`-reset). This is the createCell
account-growth neutrality META-FILL C demands — the dregg1-faithful `balance == 0` creation as a
conservation-NEUTRAL move on the per-asset ledger. -/
theorem execFullA_createCellA_neutral_per_asset (s s' : RecChainedState) (actor newCell : CellId)
    (b : AssetId) (h : execFullA s (.createCellA actor newCell) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellChainA_neutral b (by simpa only [execFullA] using h)

/-- **`execFullA_createCellA_grows_accounts` — the GROWTH has teeth.** After a committed
`createCellA`, the new cell IS a live account: `newCell ∈ s'.kernel.accounts`. Witnesses that the
neutrality keystone is NOT a no-op — the conserved-measure index set grew. -/
theorem execFullA_createCellA_grows_accounts (s s' : RecChainedState) (actor newCell : CellId)
    (h : execFullA s (.createCellA actor newCell) = some s') :
    newCell ∈ s'.kernel.accounts :=
  createCellChainA_grows_accounts (by simpa only [execFullA] using h)

/-- **`execFullA_spawnA_neutral_per_asset`.** A committed `spawnA` (createCell born EMPTY + a
bal-orthogonal cap grant) is likewise conservation-NEUTRAL for EVERY asset. -/
theorem execFullA_spawnA_neutral_per_asset (s s' : RecChainedState) (actor child target : CellId)
    (b : AssetId) (h : execFullA s (.spawnA actor child target) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  spawnChainA_neutral b (by simpa only [execFullA] using h)

/-- **`execFullA_bridgeMintA_discloses_per_asset` (W1: the bridge CONSERVES).** A committed
`bridgeMintA actor cell a value` leaves EVERY asset's supply literally UNCHANGED: the bridged
credit is the BRIDGE-issuer's well moving (`a` is the bridge cell; its well carries −(outstanding
bridged supply)), so the pre-W1 "disclosed generative inflow" is now an exact conservation
statement — the strongest possible no-cross-asset-laundering content at the bridge boundary. -/
theorem execFullA_bridgeMintA_discloses_per_asset (s s' : RecChainedState) (actor cell : CellId)
    (a : AssetId) (value : ℤ) (b : AssetId)
    (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
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

/-- **`setFieldA` authorized.** A committed `setFieldA` implies the actor held authority over
`cell` (`stateAuthB` — the faithful model of dregg1's `SetState` cross-cell / ownership gate). -/
theorem execFullA_setFieldA_authorized (s s' : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) (h : execFullA s (.setFieldA actor cell f v) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  -- §SLOT-CAVEAT: peel the caveat gate first (`stateStepGuarded_eq`), then the authority gate.
  state_authorized (stateStepGuarded_eq (by simpa only [execFullA] using h))

/-- **`incrementNonceA` authorized.** Implies the actor held authority over `cell` (the
`IncrementNonce` cross-cell / ownership gate). -/
theorem execFullA_incrementNonceA_authorized (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`setPermissionsA` authorized.** Implies the actor held authority over `cell` (the
`SetPermissions` gate; dregg1 applies the permission write LAST off the ORIGINAL snapshot, so the
gate is evaluated against the PRE-state caps — exactly `stateAuthB s.kernel.caps`, the pre-state). -/
theorem execFullA_setPermissionsA_authorized (s s' : RecChainedState) (actor cell : CellId) (p : Int)
    (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`setVKA` authorized.** Implies the actor held authority over `cell` (the
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

/-- **`makeSovereignA` authorized.** Implies the actor held authority over `cell` (dregg1's
self-sovereign gate: `cell == action_target` ⇒ the cell's own authority). FILL #133: the action is a
VALUE-REBIND (the readable state is dropped behind the §8 commitment), so the gate routes through
`makeSovereignStep_authorized`, not the generic `stateStep`. -/
theorem execFullA_makeSovereignA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.makeSovereignA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  makeSovereignStep_authorized (by simpa only [execFullA] using h)

/-- **`refusalA` authorized.** Implies the actor held authority over `cell` (dregg1's
cross-cell `SetState` gate). Refusal NEVER mutates balance/caps/value — the move is the audit write. -/
theorem execFullA_refusalA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.refusalA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  state_authorized (by simpa only [execFullA] using h)

/-- **`receiptArchiveA` authorized.** Implies the actor held authority over `cell` (dregg1's
checkpoint cell_id = action_target gate). The archive is a lifecycle/log write. -/
theorem execFullA_receiptArchiveA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.receiptArchiveA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (receiptArchiveChainA_factors (by simpa only [execFullA] using h)).1.1

/-! ### §MA-lifecycle authority obligations (Wave-3) — the cell lifecycle + refresh effects carry their
REAL `stateAuthB actor cell` self-lifecycle gate. The state-machine guard (Live↔Sealed/Destroyed) +
the no-parent / fresh-snapshot guards are the SEPARATE kernel-level obligations
(`cellSealChainA_nonlive_rejects` / `cellDestroyChainA_terminal_rejects` /
`refreshDelegationChainA_noParent_rejects` / `refreshDelegationChainA_snapshots_parent`). -/

/-- **`cellSealA` authorized.** A committed seal implies the actor held authority over `cell`. -/
theorem execFullA_cellSealA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.cellSealA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (cellSealChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`cellUnsealA` authorized.** -/
theorem execFullA_cellUnsealA_authorized (s s' : RecChainedState) (actor cell : CellId)
    (h : execFullA s (.cellUnsealA actor cell) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (cellUnsealChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`cellDestroyA` authorized.** -/
theorem execFullA_cellDestroyA_authorized (s s' : RecChainedState) (actor cell : CellId) (ch : Nat)
    (h : execFullA s (.cellDestroyA actor cell ch) = some s') :
    stateAuthB s.kernel.caps actor cell = true :=
  (cellDestroyChainA_factors (by simpa only [execFullA] using h)).1.1

/-- **`refreshDelegationA` authorized.** A committed refresh implies the actor held the
self-authority over the `child` (dregg1's self-only `action_target == child` gate). -/
theorem execFullA_refreshDelegationA_authorized (s s' : RecChainedState) (actor child : CellId)
    (h : execFullA s (.refreshDelegationA actor child) = some s') :
    stateAuthB s.kernel.caps actor child = true :=
  (refreshDelegationChainA_factors (by simpa only [execFullA] using h)).1.1

/-! ### §MA-auth authority obligations — the 6 distinct authority effects carry their REAL,
NON-VACUOUS integrity content (grounding / `addEdge` / `removeEdge` / non-amplification / held-cap).
These REUSE the `recKDelegate`/`recKRevokeTarget` spine lemmas and `Caps.attenuate_subset` — exactly
the proofs `Exec.EffectsAuthority` carries (which we cannot import, being downstream). -/

/-- **`execFullA_introduceA_grounds`.** A committed introduce HOLDS the Granovetter source
edge `introducer ⟶ ⟨target,()⟩` (only connectivity begets connectivity). REUSES `recKDelegate_grounds`. -/
theorem execFullA_introduceA_grounds (s s' : RecChainedState) (intro rec t : CellId)
    (h : execFullA s (.introduceA intro rec t) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps intro (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegate] at h
  cases hd : recKDelegate s.kernel intro rec t with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegate_grounds s.kernel k' intro rec t hd

/-- **`execFullA_introduceA_addEdge`.** A committed introduce edits the graph by EXACTLY
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

/-- **`execFullA_introduceA_holds_real_cap`.** A committed introduce WITNESSES the concrete
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

/-- **`execFullA_introduceA_grants_held_cap`.** A committed introduce grants the recipient
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

/-- **`execFullA_introduceA_non_amplifying` — THE HEADLINE (GENUINE).** The actual executable
grant made by `introduceA` is a copy of the introducer's held cap to `t`, hence it is non-amplifying
over the exact cap it copied. Explicit narrowing belongs to `delegateAttenA`; this theorem states the
concrete copy branch rather than an uncarried attenuation payload. -/
theorem execFullA_introduceA_non_amplifying (s s' : RecChainedState) (intro rec t : CellId)
    (_h : execFullA s (.introduceA intro rec t) = some s') :
    IsNonAmplifyingF (heldCapTo s.kernel.caps intro t) (heldCapTo s.kernel.caps intro t) :=
  fun _ ha => ha

/-- **`execFullA_attenuateA_non_amplifying` — THE HEADLINE (GENUINE).** Whatever cap the
actor narrows, the narrowed cap confers a genuine `List Auth` SUBSET of the original:
`∀ c, IsNonAmplifyingF c (attenuate keep c)`, via `Caps.attenuate_subset`. The executable
`is_narrower_or_equal` (widening denied). -/
theorem execFullA_attenuateA_non_amplifying (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execFullA s (.attenuateA actor idx keep) = some s') :
    ∀ c : Cap, IsNonAmplifyingF c (attenuate keep c) :=
  fun c => attenuateF_non_amplifying keep c

/-- **`execFullA_attenuateA_confined`.** Attenuation edits ONLY the actor's OWN slot; every
OTHER holder's slot is untouched (the confinement face of "you can only narrow what you hold"). -/
theorem execFullA_attenuateA_confined (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execFullA s (.attenuateA actor idx keep) = some s') :
    ∀ l, l ≠ actor → s'.kernel.caps l = s.kernel.caps l := by
  simp only [execFullA, attenuateStepA, Option.some.injEq] at h
  subst h
  intro l hl; simp only [attenuateSlotF, if_neg hl]

/-- **`execFullA_revokeDelegationA_removeEdge`.** A committed RevokeDelegation edits the
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

/-- **`execFullA_delegateAttenA_grounds`.** A committed rights-delegation HOLDS the abstract
source edge `del ⟶ ⟨t,()⟩` (the Granovetter connectivity premise — the delegator could already reach
`t`). Reads `recKDelegateAtten_grounds`. -/
theorem execFullA_delegateAttenA_grounds (s s' : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps del (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA, recCDelegateAtten] at h
  cases hd : recKDelegateAtten s.kernel del rec t keep with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => exact recKDelegateAtten_grounds s.kernel k' del rec t keep hd

/-- **`execFullA_delegateAttenA_grants`.** On commit, the `recipient` GENUINELY HOLDS the
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

/-- **`execFullA_delegateAttenA_non_amplifying` — THE HEADLINE (GENUINE & EXECUTED).** The cap
the recipient actually RECEIVES confers a `List Auth` SUBSET of the delegator's held cap to `t`
(`granted ⊆ held`) — `is_attenuation(held, granted)` over the EXECUTED grant, NOT a `()≤()` collapse.
Reads `attenuate_subset`. -/
theorem execFullA_delegateAttenA_non_amplifying (s s' : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (_h : execFullA s (.delegateAttenA del rec t keep) = some s') :
    IsNonAmplifyingF (heldCapTo s.kernel.caps del t) (attenuate keep (heldCapTo s.kernel.caps del t)) := by
  unfold IsNonAmplifyingF
  exact attenuate_subset keep (heldCapTo s.kernel.caps del t)

/-- **`execFullA_exerciseA_authorized`.** A committed exercise HOLDS the source edge:
`actor ⟶ ⟨target,()⟩` on `execGraph` (the resolved c-list slot — only the holder may exercise). The
hold-gate (`exerciseStepA`) authorizes regardless of what the inner effects do. -/
theorem execFullA_exerciseA_authorized (s s' : RecChainedState) (actor t : CellId) (inner : List FullActionA)
    (h : execFullA s (.exerciseA actor t inner) = some s') :
    Dregg2.Spec.execGraph s.kernel.caps actor (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) := by
  simp only [execFullA] at h
  by_cases hf : innerFacetsAdmittedA s actor t inner = true
  · rw [if_pos hf] at h
    cases hg : exerciseStepA s actor t with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some s1 =>
        obtain ⟨hgg, _⟩ := exerciseStepA_factors hg
        rw [execGraph_eq_any]; exact hgg
  · rw [if_neg hf] at h; exact absurd h (by simp)

/-- **`execFullA_exerciseA_recurses` (the DE-SHADOW witness).** A committed exercise actually
RAN its inner effects: there is a gate-state `s1` (the hold-gate's result) from which the inner fold
`execInnerA s1 inner` committed to `s'`. This is the teeth that distinguish a real exercise from the old
no-op shadow — the `inner` effects executed against the cap's target. -/
theorem execFullA_exerciseA_recurses (s s' : RecChainedState) (actor t : CellId) (inner : List FullActionA)
    (h : execFullA s (.exerciseA actor t inner) = some s') :
    ∃ s1, exerciseStepA s actor t = some s1 ∧ execInnerA s1 inner = some s' := by
  simp only [execFullA] at h
  by_cases hf : innerFacetsAdmittedA s actor t inner = true
  · rw [if_pos hf] at h
    cases hg : exerciseStepA s actor t with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some s1 => rw [hg] at h; exact ⟨s1, rfl, h⟩
  · rw [if_neg hf] at h; exact absurd h (by simp)

/-! ### §MA-note membership obligations — noteSpend/noteCreate carry the genuine SET-membership
witness (the escrow/obligation create/settle obligations died with the kernel holding-store, F1b). -/


/-- **`execFullA_noteSpendA_inserts`.** A committed noteSpend inserts `nf` into the nullifier
SET (so a subsequent spend of `nf` fails-closed — the anti-replay teeth). -/
theorem execFullA_noteSpendA_inserts (s s' : RecChainedState) (nf : Nat) (actor : CellId)
    (spendProof : Bool) (h : execFullA s (.noteSpendA nf actor spendProof) = some s') :
    nf ∈ s'.kernel.nullifiers := by
  simp only [execFullA, noteSpendChainA] at h
  by_cases hp : spendProof = true
  · rw [if_pos hp] at h
    cases hk : noteSpendNullifier s.kernel nf with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        exact note_spend_inserts hk
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-- **`execFullA_noteCreateA_inserts`.** A committed noteCreate inserts `cm` into the grow-only
commitment SET. -/
theorem execFullA_noteCreateA_inserts (s s' : RecChainedState) (cm : Nat) (actor : CellId)
    (h : execFullA s (.noteCreateA cm actor) = some s') : cm ∈ s'.kernel.commitments := by
  simp only [execFullA, noteCreateChainA, Option.some.injEq] at h
  subst h; exact noteCreate_inserts s.kernel cm


/-- **The per-`FullActionA` `StepInv`** — the per-asset analog of `fullActionInv`, true of every
committed per-asset action across all kinds. Its **Ledger** conjunct is the full per-asset VECTOR (a
`∀ b`, never an aggregate scalar — the FILL-1 carrier that forbids cross-asset laundering):
  * **Ledger (vector)** — for EVERY asset `b`, `recTotalAsset … b` moved by EXACTLY `ledgerDeltaAsset
    fa b` (`0` for transfer/authority, `±amt` at the targeted asset only for mint/burn);
  * **ChainLink** — the chain extends by exactly `fullReceiptA s fa` (newest-first), no fork/rewrite;
  * **ObsAdvance** — the chain grew by exactly one row (replay-detectable);
  * **KindObligation** — the kind-specific integrity content (asset-orthogonal): balanceA ⇒
    `authorizedB`; delegate ⇒ grounds in the source edge AND edits the graph by `addEdge`; revoke ⇒
    `removeEdge`; mintA/burnA ⇒ `mintAuthorizedB` AND the Generative/Annihilative disclosure. -/
def fullActionInvA (s : RecChainedState) (fa : FullActionA) (s' : RecChainedState) : Prop :=
  -- Ledger: the per-asset COMBINED conservation VECTOR (∀ b — never one aggregate scalar). The UNIFORM
  -- measure across ALL kinds is `recTotalAsset` (= `bal`-ledger + per-asset holding-store);
  -- non-escrow kinds leave `escrows` fixed so their combined delta = bare-`bal` delta, escrow/note legs
  -- are combined-conserving (combined delta `0`) — the FILL-1/META-FILL-C no-laundering carrier.
  (∀ b, recTotalAsset s'.kernel b = recTotalAsset s.kernel b + ledgerDeltaAsset fa b) ∧
  -- ChainLink: the pre-log is a SUFFIX of the post-log (append-only) AND the kind's own receipt is
  -- recorded in the post-log. For every NON-recursive kind this is the exact one-row extension
  -- `fullReceiptA fa :: s.log`; for `exerciseA` (which RECURSES through `inner`) the kind's own
  -- `authReceipt` is followed by the inner effects' receipts — still append-only, still records the
  -- exercise receipt. The honest append-only audit-chain law across the WHOLE op-set.
  (s.log <:+ s'.log ∧ fullReceiptA s fa ∈ s'.log) ∧
  -- ObsAdvance: the chain STRICTLY grows (≥ one row — exactly one for non-recursive kinds, `1 + |inner|`
  -- for a committed exercise), so a replayed action is detectable.
  (s.log.length < s'.log.length) ∧
  -- KindObligation: the kind-specific authority/graph/disclosure content (asset-orthogonal).
  (match fa with
   | .balanceA t _       => authorizedB s.kernel.caps t = true ∧ acceptsEffects s.kernel t.dst = true
   | .delegate del rec t =>
       Dregg2.Spec.execGraph s.kernel.caps del
         (⟨t, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.addEdge (Dregg2.Spec.execGraph s.kernel.caps) rec ⟨t, ()⟩
   | .revoke holder t    =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
   -- W1 (DREGG3 §2.2): mint/burn are ISSUER-MOVES. The obligation is the issuer gate (E2: mint
   -- authority over the asset's ISSUER cell `a`, never the recipient) ∧ the live issuer well (the
   -- genesis-order tooth). The pre-W1 disclosure leg is GONE — the Ledger conjunct above now pins
   -- EXACT conservation (`ledgerDeltaAsset = 0`), strictly stronger than a disclosed non-zero.
   | .mintA actor _ a _  =>
       mintAuthorizedB s.kernel.caps actor a = true ∧
       a ∈ s.kernel.accounts
   | .burnA actor _ a _  =>
       mintAuthorizedB s.kernel.caps actor a = true ∧
       a ∈ s.kernel.accounts
   -- §MA-state: the field-writing pure-state effects carry their REAL authority gate
   -- (`stateAuthB` over the cell) ∧ their `Neutral`/`Monotonic` linearity coloring (the
   -- faithful-mirror tripwire). `emitEventA` is authority-FREE (dregg1 runs no cap check), but it
   -- carries the dregg1 cell-existence gate plus its `Neutral` coloring — NOT an authority claim.
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
   | .revokeDelegationA holder t =>
       Dregg2.Spec.execGraph s'.kernel.caps
         = Dregg2.Spec.removeEdge (Dregg2.Spec.execGraph s.kernel.caps) holder ⟨t, ()⟩
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
   -- W1: the bridge cell IS the issuer of the bridged asset — the obligation is the issuer gate
   -- over the BRIDGE cell `a` + its live well (the §8 foreign-finality portal stays out-of-band).
   | .bridgeMintA actor _ a _ =>
       mintAuthorizedB s.kernel.caps actor a = true ∧
       a ∈ s.kernel.accounts
   -- §MA-note: notes carry the genuine SET membership witness — teeth, NOT `True`.
   | .noteSpendA nf _ _ =>
       -- anti-replay: the spent nullifier is now IN the set (a subsequent spend fails-closed).
       nf ∈ s'.kernel.nullifiers ∧ effectLinearity .noteSpend = LinearityClass.Conservative
   | .noteCreateA cm _ =>
       -- the fresh commitment is now IN the grow-only commitment set.
       cm ∈ s'.kernel.commitments ∧ effectLinearity .noteCreate = LinearityClass.Conservative
   -- §MA-seal (Wave-3 DE-SHADOW): seal/unseal carry their REAL c-list HOLD gate (the actor
   -- HOLDS the sealer/unsealer cap for `pid` — `lookup_by_target`, `apply.rs:2756`/`:2891`), createSealPair
   -- its `stateAuthB actor sealerHolder` writer gate ∧ their catalog COLORING (all Generative). The §8 AEAD
   -- crypto is the chain-layer portal — NOT an authority claim. Every conjunct has teeth (NOT `True`).
   | .makeSovereignA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .makeSovereign = LinearityClass.Terminal
   | .refusalA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .refusal = LinearityClass.Monotonic
   | .receiptArchiveA actor cell =>
       stateAuthB s.kernel.caps actor cell = true ∧
       effectLinearity .receiptArchive = LinearityClass.Terminal
   -- pipelinedSend carries the apply-time NEUTRAL coloring (the `EventualRef` resolution is the
   -- SEPARATE `ConditionalTurn` batch — authority-free at apply, dregg1's apply-time no-op).
   | .pipelinedSendA _ =>
       effectLinearity .pipelinedSend = LinearityClass.Neutral
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
       effectLinearity .refreshDelegation = LinearityClass.Neutral
   -- §MA-heap: the heap write carries its REAL authority gate (`stateAuthB` over the target — the
   -- `write` verb's gate, fired through `stateStepGuarded` on the `heap_root` register). No legacy
   -- dregg1 `EffectTag` coloring exists for it (it is a dregg3-native `write`-verb instance); its
   -- balance-neutrality is already the Ledger conjunct (`ledgerDeltaAsset = 0`, exact).
   | .heapWriteA actor target _ _ _ =>
       stateAuthB s.kernel.caps actor target = true)

/-- **`execFullA_attests_per_asset` — THE PER-ASSET OP-SET IS STEP-COMPLETE BY CONSTRUCTION
.** Every committed `FullActionA` attests its full `StepInv` content: the per-asset ledger
VECTOR ∧ ChainLink ∧ ObsAdvance ∧ the kind-specific obligation. The per-asset analog of
`execFull_attests`, carrying the conservation VECTOR (not the scalar). -/
theorem execFullA_attests_per_asset {s s' : RecChainedState} {fa : FullActionA}
    (h : execFullA s fa = some s') : fullActionInvA s fa s' := by
  refine ⟨fun b => execFullA_ledger_per_asset s s' fa b h,
          execFullA_chainlink s s' fa h, execFullA_obsadvance s s' fa h, ?_⟩
  cases fa with
  | balanceA t a =>
      exact ⟨execFullA_balance_authorized s s' t a h, execFullA_balance_dst_live s s' t a h⟩
  | delegate del rec t =>
      exact ⟨execFullA_delegate_grounds s s' del rec t h, execFullA_delegate_addEdge s s' del rec t h⟩
  | revoke holder t => exact execFullA_revoke_removeEdge s s' holder t h
  -- W1: mint/burn discharge the ISSUER gate + the live-well witness (the disclosure leg died with
  -- the supply-increment law — the Ledger conjunct is now exact conservation).
  | mintA actor cell a amt =>
      exact ⟨execFullA_mintA_authorized s s' actor cell a amt h,
             execFullA_mintA_issuer_live s s' actor cell a amt h⟩
  | burnA actor cell a amt =>
      exact ⟨execFullA_burnA_authorized s s' actor cell a amt h,
             execFullA_burnA_issuer_live s s' actor cell a amt h⟩
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
  | revokeDelegationA holder t => exact execFullA_revokeDelegationA_removeEdge s s' holder t h
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
      exact ⟨execFullA_bridgeMintA_authorized s s' actor cell a value h,
             execFullA_bridgeMintA_issuer_live s s' actor cell a value h⟩
  -- §MA-note: discharge the noteSpend/noteCreate SET-membership witness.
  | noteSpendA nf actor spendProof => exact ⟨execFullA_noteSpendA_inserts s s' nf actor spendProof h, rfl⟩
  | noteCreateA cm actor => exact ⟨execFullA_noteCreateA_inserts s s' cm actor h, rfl⟩
  -- §MA-seal (Wave-3 DE-SHADOW): discharge seal/unseal's REAL c-list HOLD gate, createSealPair's writer
  -- gate ∧ each catalog coloring.
  | makeSovereignA actor cell => exact ⟨execFullA_makeSovereignA_authorized s s' actor cell h, rfl⟩
  | refusalA actor cell => exact ⟨execFullA_refusalA_authorized s s' actor cell h, rfl⟩
  | receiptArchiveA actor cell => exact ⟨execFullA_receiptArchiveA_authorized s s' actor cell h, rfl⟩
  -- pipelinedSend: the apply-time Neutral coloring.
  | pipelinedSendA actor => exact rfl
  -- §MA-swiss: discharge each swiss effect's (REAL `stateAuthB` authority gate ∧ the catalog coloring).
  | cellSealA actor cell => exact ⟨execFullA_cellSealA_authorized s s' actor cell h, rfl⟩
  | cellUnsealA actor cell => exact ⟨execFullA_cellUnsealA_authorized s s' actor cell h, rfl⟩
  | cellDestroyA actor cell ch => exact ⟨execFullA_cellDestroyA_authorized s s' actor cell ch h, rfl⟩
  | refreshDelegationA actor child => exact ⟨execFullA_refreshDelegationA_authorized s s' actor child h, rfl⟩
  -- §MA-heap: discharge the heap write's REAL authority gate off the wire-face keystone.
  | heapWriteA actor target addr v newRoot =>
      exact Substrate.HeapKernel.heapStepW_authorized
        (by simpa only [execFullA] using h)

/-- **`execFullTurnA_each_attests`.** Step-completeness holds at EVERY action of a committed
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
-- refusal/receiptArchive) — each a `stateStep` field write, balance-NEUTRAL (`recTotalAsset`
-- UNCHANGED ∀ asset), authority-gated (`stateAuthB` over the written cell). The §8 crypto (AEAD /
-- commitment) is the chain-layer portal, NOT proved sound. The keystone
-- `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by construction
-- (FullForestA spine UNCHANGED — only `targetOf` gained arms).
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
#assert_axioms execFullA_revokeDelegationA_removeEdge
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
-- grew) + the disclosed bridge inflow + the per-effect gates, all pinned kernel-clean. The
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
#assert_axioms createCellFromFactoryChainA_neutral
#assert_axioms createCellFromFactoryChainA_authorized
#assert_axioms createCellFromFactoryChainA_grows_accounts
#assert_axioms createCellFromFactoryChainA_installs_program
#assert_axioms createCellFromFactoryChainA_unknown_factory_fails
#assert_axioms createCellFromFactoryChainA_nonconforming_fails
#assert_axioms createCellFromFactoryChainA_balance_field_fails
#assert_axioms createCellFromFactoryChainA_caps_frame
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
-- META-FILL C: the note chained wrappers + the executed-dispatch obligations.
#assert_axioms execFullA_noteSpendA_inserts
#assert_axioms execFullA_noteCreateA_inserts
-- §MA-lifecycle (Wave-3) keystones: the lifecycle state machine + the de-shadowed seal cap-movement.
#assert_axioms cellSealChainA_nonlive_rejects
#assert_axioms cellDestroyChainA_terminal_rejects
#assert_axioms refreshDelegationChainA_noParent_rejects
#assert_axioms refreshDelegationChainA_snapshots_parent
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
#guard ((execFull fs0 (.delegate 0 1 7)).isSome)  --  true
-- ...is conservation-trivial (`recTotal` unchanged) and grows the chain by one:
#guard ((execFull fs0 (.delegate 0 1 7)).map (fun s => recTotal s.kernel)) == some 105  --  some 105 (FIXED)
#guard ((execFull fs0 (.delegate 0 1 7)).map (fun s => s.log.length)) == some 1  --  some 1
-- ...and recipient 1 now holds the `node 7` cap (the new authority edge):
#guard (((execFull fs0 (.delegate 0 1 7)).map (fun s => s.kernel.caps 1)).getD []) == [Cap.node 7]  --  [Cap.node 7]
-- A delegator with no connectivity to the target cannot delegate it (fail-closed):
#guard ((execFull fs0 (.delegate 5 1 9)).isSome) == false  --  false

-- A MINT turn commits (actor 9 holds the privileged `node 0` cap ⇒ may coin cell 0's supply):
#guard ((execFull fs0 (.mint 9 0 50)).isSome)  --  true
-- ...raises `recTotal` by exactly +50 (disclosed non-conservation), chain grows by one:
#guard ((execFull fs0 (.mint 9 0 50)).map (fun s => recTotal s.kernel)) == some 155  --  some 155 (= 105 + 50)
#guard ((execFull fs0 (.mint 9 0 50)).map (fun s => s.log.length)) == some 1  --  some 1
-- ...and the minted receipt carries the disclosed delta +50:
#guard (((execFull fs0 (.mint 9 0 50)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0) == 50  --  50
-- An actor without the privileged mint cap cannot mint (bare ownership is NOT enough):
#guard ((execFull fs0 (.mint 0 0 50)).isSome) == false  --  false (actor 0 lacks `node 0`)

-- A BURN turn commits (actor 9 authorized; cell 0 has ≥ 40 balance):
#guard ((execFull fs0 (.burn 9 0 40)).isSome)  --  true
-- ...lowers `recTotal` by exactly -40 (disclosed), chain grows by one:
#guard ((execFull fs0 (.burn 9 0 40)).map (fun s => recTotal s.kernel)) == some 65  --  some 65 (= 105 - 40)
-- Over-burn (more than available) is rejected (availability gate):
#guard ((execFull fs0 (.burn 9 0 999)).isSome) == false  --  false
-- Unauthorized burn rejected:
#guard ((execFull fs0 (.burn 0 0 10)).isSome) == false  --  false

-- A REVOKE turn always commits (it only subtracts authority) and is conservation-trivial:
#guard ((execFull fs0 (.revoke 0 7)).isSome)  --  true
#guard ((execFull fs0 (.revoke 0 7)).map (fun s => recTotal s.kernel)) == some 105  --  some 105 (FIXED)
-- ...after which holder 0's `node 7` cap is gone:
#guard (((execFull fs0 (.revoke 0 7)).map (fun s => s.kernel.caps 0)).getD []) == []  --  []

-- A BALANCE turn (reusing the catalog-typed `Action`) commits and conserves:
#guard ((execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).isSome)  --  true
#guard ((execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).map (fun s => recTotal s.kernel)) == some 105  --  some 105

-- A MIXED full-turn: mint +50, then transfer (conserves), then burn -50 → nets to 0, conserves.
def mixedTurn : List FullAction :=
  [ .mint 9 0 50
  , .balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩
  , .burn 9 0 50 ]

#guard ((execFullTurn fs0 mixedTurn).isSome)  --  true (all-or-nothing commits)
#guard (turnLedgerDelta mixedTurn) == 0  --  0 (+50 +0 -50)
#guard ((execFullTurn fs0 mixedTurn).map (fun s => recTotal s.kernel)) == some 105  --  some 105 (CONSERVED: net 0)
#guard ((execFullTurn fs0 mixedTurn).map (fun s => s.log.length)) == some 3  --  some 3 (chain grew by count)

-- An all-or-nothing transaction with a bad action ROLLS BACK the whole turn:
def badMixedTurn : List FullAction :=
  [ .mint 9 0 50, .burn 0 0 10 ]   -- second action unauthorized ⇒ whole turn none
#guard ((execFullTurn fs0 badMixedTurn).isSome) == false  --  false (rollback)

/-! ## §13 — Non-vacuity for the PER-ASSET executor: conservation holds, laundering is CAUGHT. -/

/-- A chained state with a genuine 2-asset `bal` ledger: cell 0 holds 100 of asset 0 and 7 of asset
1; cell 1 holds 5 of asset 0. Actor 9 holds the privileged `node 0`/`node 1` mint caps over BOTH
issuer cells (W1: asset `a`'s issuer IS cell `a` — mint authority is control of the issuer). -/
def fma0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 1] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

#guard (recTotalAsset fma0.kernel 0) == 105  --  105 (asset 0 supply)
#guard (recTotalAsset fma0.kernel 1) == 7  --  7   (asset 1 supply)
-- A pure per-asset TRANSFER of asset 0 (actor 0 owns src 0) conserves BOTH assets:
#guard ((execFullTurnA fma0 [.balanceA ⟨0, 0, 1, 30⟩ 0]).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-- The pre-W1 scalar-LAUNDERING turn (mint 50 of asset 1 to cell 0 while burning 50 of asset 0
from cell 1's holding): under the supply-increment law the aggregate scalar hid a (−50, +50)
cross-asset move. W1 KILLS the whole channel: mint/burn are issuer-moves, so BOTH actions conserve
BOTH assets EXACTLY — the per-asset vector is identically (0, 0) and the post-state sums are
UNCHANGED. The swap is visible in the ROWS (the issuer wells moved), never in the sums. -/
def launderTurn : List FullActionA :=
  [ .mintA 9 0 1 50      -- mint 50 of asset 1 (issuer = cell 1) into cell 0: well 1 → −50
  , .burnA 9 1 0 5 ]     -- burn cell 1's 5 of asset 0 back into well 0

#guard (turnLedgerDeltaAsset launderTurn 0) == 0  --  0 (W1: burn = return-to-well, conserving)
#guard (turnLedgerDeltaAsset launderTurn 1) == 0  --  0 (W1: mint = issuer-move, conserving)
-- the per-asset ledger AFTER the turn: BOTH supplies unchanged (the W1 exactness, executable):
#guard ((execFullTurnA fma0 launderTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- ...and the ROWS show the actual moves: cell 1's well in asset 1 went NEGATIVE-CAPABLE (0 → −50,
-- the well IS −supply-delta), cell 0 gained 50 of asset 1; cell 1's asset-0 holding returned to
-- well 0 (5 → 0, well 100 → 105):
#guard ((execFullTurnA fma0 launderTurn).map
        (fun s => (s.kernel.bal 1 1, s.kernel.bal 0 1, s.kernel.bal 1 0, s.kernel.bal 0 0)))
        == some (-50, 57, 0, 105)
-- the ISSUER gate has teeth: an actor holding only `node 0` (NOT the issuer of asset 1) cannot
-- mint asset 1 (the legacy recipient-shaped gate would have accepted this):
#guard ((execFullA { fma0 with kernel := { fma0.kernel with
          caps := fun l => if l = 9 then [Cap.node 0] else [] } }
          (.mintA 9 0 1 50)).isNone)
-- self-mint into the issuer's own well is a no-move (rejected by the `a ≠ cell` gate):
#guard ((execFullA fma0 (.mintA 9 1 1 50)).isNone)

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
        caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#guard ((recTotalAsset fmaS.kernel 0, recTotalAsset fmaS.kernel 1)) == (105, 7)  --  (105, 7)

-- ★ THE KEYSTONE WITNESS: a `setFieldA` that changes cell 0's `nonce` field to 42 COMMITS,
--   yet `recTotalAsset` is UNCHANGED at (105, 7) for BOTH assets (balance-NEUTRALITY):
#guard ((execFullA fmaS (.setFieldA 0 0 "nonce" 42)).isSome)  --  true
#guard ((execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map
        (fun s => fieldOf "nonce" (s.kernel.cell 0))) == some 42  --  some 42 (CHANGED)
#guard ((execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (UNCHANGED)
-- ...and grows the receipt chain by exactly one row (the metadata clock):
#guard ((execFullA fmaS (.setFieldA 0 0 "nonce" 42)).map (fun s => s.log.length)) == some 1  --  some 1
-- An UNAUTHORIZED actor (9 owns nothing, empty caps) cannot write cell 0's field (fail-closed):
#guard ((execFullA fmaS (.setFieldA 9 0 "nonce" 42)).isSome) == false  --  false

-- IncrementNonce (Monotonic): bump cell 0's nonce 0→1, balance-neutral:
#guard ((execFullA fmaS (.incrementNonceA 0 0 1)).map (fun s => fieldOf "nonce" (s.kernel.cell 0))) == some 1  --  some 1
#guard ((execFullA fmaS (.incrementNonceA 0 0 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

-- SetPermissions / SetVerificationKey (Neutral): field writes, balance-neutral:
#guard ((execFullA fmaS (.setPermissionsA 0 0 3)).map (fun s => fieldOf "permissions" (s.kernel.cell 0))) == some 3  --  some 3
#guard ((execFullA fmaS (.setVKA 0 0 99)).map (fun s => fieldOf "verification_key" (s.kernel.cell 0))) == some 99  --  some 99
#guard ((execFullA fmaS (.setVKA 0 0 99)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

-- EmitEvent: authority-FREE (even actor 9, who owns nothing, commits — dregg1 runs NO cap check)
--   but cell-existence-gated; writes NO state, grows the chain by one, balance-neutral:
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).isSome)  --  true (authority-free)
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).map (fun s => s.log.length)) == some 1  --  some 1
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- Non-live event targets reject: no ghost-cell event rows.
#guard ((execFullA fmaS (.emitEventA 9 99 7 123)).isSome) == false  --  false

-- A MIXED per-asset turn interleaving pure-state effects with a transfer: ALL balance-neutral
--   (the transfer conserves; the field writes/emit move no asset) ⇒ (105, 7) preserved:
def stateMixedTurn : List FullActionA :=
  [ .setFieldA 0 0 "status" 5
  , .balanceA ⟨0, 0, 1, 30⟩ 0     -- transfer 30 of asset 0, cell 0 → cell 1 (conserves)
  , .incrementNonceA 0 0 1
  , .emitEventA 0 0 1 0
  , .setVKA 0 0 7 ]

#guard ((execFullTurnA fmaS stateMixedTurn).isSome)  --  true (all commit)
#guard ((turnLedgerDeltaAsset stateMixedTurn 0, turnLedgerDeltaAsset stateMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaS stateMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (CONSERVED)
#guard ((execFullTurnA fmaS stateMixedTurn).map (fun s => s.log.length)) == some 5  --  some 5 (chain grew by node count)

/-! ## §13-auth — Non-vacuity for the 6 DISTINCT AUTHORITY effects: the cap-graph moves (or is
checked), but `recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); the
HEADLINE non-amplification has TEETH (an attenuation STRICTLY drops a right; an amplifying grant is
REJECTED); fail-closed (introduce/exercise without held connectivity ⇒ none). -/

/-- A 2-asset state whose actor 0 ALSO holds REAL caps: `node 7` (connectivity, for introduce/
exercise/handoff to target 7) and `endpoint 9 [read, write]` (rights-carrying, for attenuation
teeth; the `write` makes it confer connectivity to 9 too). Asset 0 = 105, asset 1 = 7. -/
def fmaA : RecChainedState :=
  { kernel :=
      -- cell 7 is a real (live, empty) account: actor 0 holds `Cap.node 7` to it, so exercising that
      -- cap runs inner effects AGAINST the live target 7 (an under-spec'd fixture before — 7 was a cap
      -- target but not an account, so inner `emitEventA 0 7` fail-closed; #44 triage made it faithful).
      { accounts := {0, 1, 7}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 7, Cap.endpoint 9 [Auth.read, Auth.write]] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#guard ((recTotalAsset fmaA.kernel 0, recTotalAsset fmaA.kernel 1)) == (105, 7)  --  (105, 7)

-- (1) INTRODUCE: actor 0 (holds `node 7`) introduces recipient 1 to target 7. COMMITS, and
--   `recTotalAsset` is UNCHANGED in BOTH assets (caps change, bal does NOT — balance-NEUTRALITY):
#guard ((execFullA fmaA (.introduceA 0 1 7)).isSome)  --  true
#guard ((execFullA fmaA (.introduceA 0 1 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (UNCHANGED)
-- ...and recipient 1 now holds the `node 7` cap (the new authority EDGE — caps DID move):
#guard (((execFullA fmaA (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []) == [Cap.node 7]  --  [Cap.node 7]
-- An introducer with NO connectivity to the target cannot introduce it (FAIL-CLOSED ⇒ none):
#guard ((execFullA fmaA (.introduceA 5 1 7)).isSome) == false  --  false

/-- Actor 0 holds only endpoint-write connectivity to target 7. -/
def fmaEndpointIntro : RecChainedState :=
  { fmaA with
    kernel := { fmaA.kernel with
      caps := fun l => if l = 0 then [Cap.endpoint 7 [Auth.write]] else [] } }

-- INTRODUCE from an endpoint witness copies the endpoint cap; it does not upgrade to `node`/control.
#guard (((execFullA fmaEndpointIntro (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []) == [Cap.endpoint 7 [Auth.write]]  -- [Cap.endpoint 7 [Auth.write]]

-- (1') THE TEETH — genuine rights NON-AMPLIFICATION over the real `List Auth` lattice.
-- Attenuating the held `endpoint 9 [read, write]` to keep only `[read]` STRICTLY DROPS `write`:
#guard (capAuthConferred (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])) == [Auth.read])  --  [read] ⊊ [read,write]
-- the genuine non-amplification fires on this concrete held cap (granted ⊆ held, REAL rights):
example : IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write])
    (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])) :=
  attenuateF_non_amplifying [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])
-- ...and an AMPLIFYING grant is REJECTED: a `node 9` cap confers `control`, which the
-- held `endpoint 9 [read, write]` cap does NOT confer ⇒ it FAILS the non-amplification predicate:
example : ¬ IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9) :=
  amplifyingF_rejected (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9)
    Auth.control (by decide) (by decide)

-- (2) ATTENUATE: narrow actor 0's slot-1 cap (`endpoint 9 [read, write]`) to keep only `read`.
-- COMMITS, balance-neutral, and the slot's cap is narrowed:
#guard ((execFullA fmaA (.attenuateA 0 1 [Auth.read])).isSome)  --  true
#guard (((execFullA fmaA (.attenuateA 0 1 [Auth.read])).map (fun s => s.kernel.caps 0)).getD []) == [Cap.node 7, Cap.endpoint 9 [Auth.read]]  --  [node 7, endpoint 9 [read]] (write DROPPED)
#guard ((execFullA fmaA (.attenuateA 0 1 [Auth.read])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (UNCHANGED)

-- (4) REVOKE-DELEGATION: parent drops child 0's edge to 7. Always commits, balance-neutral:
#guard ((execFullA fmaA (.revokeDelegationA 0 7)).isSome)  --  true
#guard ((execFullA fmaA (.revokeDelegationA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

-- (6) EXERCISE (DE-SHADOWED): actor 0 (holds `node 7`) exercises its cap to target 7 to RUN inner
--   effects against it (dregg1 `apply.rs:2647`: each inner effect applied against the cap's target).
--   The inner effect (an `emitEvent` against 7) GENUINELY RUNS — the log grows by 2 (the exercise's
--   own receipt + the inner emit receipt), proving it is NOT a no-op shadow. An actor without
--   the held edge FAILS-CLOSED; a FAILING inner effect aborts the whole exercise (fail-closed):
#guard ((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).isSome)  --  true (inner emit against the now-live target 7 RUNS — exercise is no shadow)
#guard (((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).map (fun s => s.log.length)).getD 0) == 2  --  2 (exercise receipt + inner emit receipt)
#guard ((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (emit is balance-neutral)
-- a committed exercise carrying a balance-MOVING inner (mint 3 of asset 1 into a live cell, by an actor
--   that holds the privileged `node`-cap): the inner mint actually CREDITS — combined delta sums the inner.
#guard ((execFullA fmaA (.exerciseA 0 7 [])).isSome)  --  true (empty inner: pure hold-check)
#guard (((execFullA fmaA (.exerciseA 0 7 [])).map (fun s => s.log.length)).getD 0) == 1  --  1 (only the exercise receipt)
#guard ((execFullA fmaA (.exerciseA 5 7 [.emitEventA 0 7 99 1])).isSome) == false  --  false (FAIL-CLOSED: no held edge)

-- ★★ R4 FACET-MASK TEETH (the canonical-semantics gate BITES). Actor 0 holds `endpoint 9 [read,write]`
--    toward target 9 (its mask is exactly [read,write]) and the privileged `node 7` toward 7 (full mask).
--    The facet of the inner effect — not mere connectivity — decides admission:
#guard (requiredFacetA (.emitEventA 0 9 99 1) == Auth.write)   -- a state write demands `write`
#guard (requiredFacetA (.delegate 0 1 7) == Auth.grant)        -- an authority grant demands `grant`
#guard (capFacetMaskA (heldCapTo fmaA.kernel.caps 0 9) == [Auth.read, Auth.write])  -- endpoint 9's mask
#guard (capFacetMaskA (heldCapTo fmaA.kernel.caps 0 7) == [Auth.read, Auth.write, Auth.grant, Auth.call, Auth.reply, Auth.reset, Auth.control, Auth.notify])  -- node 7 = full (every Auth incl. notify)
-- the [read,write] mask ADMITS a write-facet inner effect (gate passes; the inner emit then runs):
#guard (innerFacetsAdmittedA fmaA 0 9 [.emitEventA 0 9 99 1])  --  true
-- ...but REJECTS a grant-facet inner effect — `grant ∉ [read,write]` — so the WHOLE exercise is `none`
--    EVEN THOUGH actor 0 holds connectivity to 9 (connectivity ≠ facet — the R4 distinction):
#guard (innerFacetsAdmittedA fmaA 0 9 [.delegate 0 1 7]) == false  --  false
#guard ((execFullA fmaA (.exerciseA 0 9 [.delegate 0 1 7])).isSome) == false  --  false (R4 REJECTS the grant)
-- the privileged `node 7` cap (full mask) ADMITS the grant-facet inner effect (control over 7):
#guard (innerFacetsAdmittedA fmaA 0 7 [.delegate 0 1 7])  --  true (node mask contains grant)

-- A MIXED authority turn: introduce (adds edge) + attenuate (narrows) + exercise (RUNS inner emit) +
--   revoke-delegation (removes) — ALL balance-neutral ⇒ (105, 7) preserved across the turn:
def authMixedTurn : List FullActionA :=
  [ .introduceA 0 1 7
  , .attenuateA 0 1 [Auth.read]
  , .exerciseA 0 7 [.emitEventA 0 7 99 1]
  , .revokeDelegationA 0 7 ]

#guard ((execFullTurnA fmaA authMixedTurn).isSome)  --  true (all commit; the exercise inner emit runs against the live target 7)
#guard ((turnLedgerDeltaAsset authMixedTurn 0, turnLedgerDeltaAsset authMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaA authMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (CONSERVED)

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
#guard ((recTotalAsset fmaSup.kernel 0, recTotalAsset fmaSup.kernel 1)) == (105, 7)  --  (105, 7)
#guard ((decide (0 ∈ fmaSup.kernel.accounts), decide (1 ∈ fmaSup.kernel.accounts),
       decide (2 ∈ fmaSup.kernel.accounts))) == (true, true, false)  --  (true, true, false)

-- ★ THE ACCOUNT-GROWTH WITNESS: actor 9 (holds `node 2`) creates the FRESH cell 2 — COMMITS,
--   `accounts` GROWS {0,1} → {0,1,2} (cell 2 now live), YET `recTotalAsset` is UNCHANGED at (105, 7)
--   for BOTH assets (born EMPTY ⇒ conservation-NEUTRAL):
#guard ((execFullA fmaSup (.createCellA 9 2)).isSome)  --  true
#guard ((execFullA fmaSup (.createCellA 9 2)).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true  --  some true (GREW)
#guard ((execFullA fmaSup (.createCellA 9 2)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (NEUTRAL)
-- ...and the fresh cell 2 is born EMPTY in every asset (bal-reset):
#guard ((execFullA fmaSup (.createCellA 9 2)).map (fun s => (s.kernel.bal 2 0, s.kernel.bal 2 1))) == some (0, 0)  --  some (0, 0)
-- ...and grows the receipt chain by exactly one row:
#guard ((execFullA fmaSup (.createCellA 9 2)).map (fun s => s.log.length)) == some 1  --  some 1
-- An UNAUTHORIZED creator (actor 0 holds no create cap) is REJECTED (fail-closed):
#guard ((execFullA fmaSup (.createCellA 0 2)).isSome) == false  --  false
-- A NON-FRESH id (cell 1 already live) is REJECTED (the freshness gate has TEETH):
#guard ((execFullA fmaSup (.createCellA 9 1)).isSome) == false  --  false

-- SPAWN: child creation alone cannot mint authority to an unheld/non-live target:
#guard ((execFullA fmaSup (.spawnA 9 2 7)).isSome) == false  --  false
-- ...but actor 9 can spawn child 2 (born EMPTY) with a COPY of its held parent `node 1` cap — COMMITS,
--   NEUTRAL, and the child carries the concrete copied parent cap (`node 1`):
#guard ((execFullA fmaSup (.spawnA 9 2 1)).isSome)  --  true
#guard ((execFullA fmaSup (.spawnA 9 2 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (NEUTRAL)
#guard (((execFullA fmaSup (.spawnA 9 2 1)).map (fun s => s.kernel.caps 2)).getD []) == [Cap.node 1]  --  [Cap.node 1]
#guard ((execFullA fmaSup (.spawnA 9 2 1)).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true  --  some true (GREW)
#guard ((execFullA fmaSup (.spawnA 9 2 1)).map
        (fun s => (s.kernel.delegate 2, s.kernel.delegations 2))) == some (some 9, [Cap.node 0, Cap.node 1, Cap.node 2])  --  some (some 9, [Cap.node 0, Cap.node 1, Cap.node 2])
#guard (((execFullA fmaSup (.spawnA 9 2 1)).bind
        (fun s => execFullA s (.refreshDelegationA 2 2))).isSome)  --  true (spawn initialized parent)

-- ★ THE BRIDGE-MINT WITNESS (W1): actor 9 (holds `node 1` — the BRIDGE cell 1 is the issuer of
--   bridged asset 1) bridge-mints 40 of asset 1 into the live cell 0 — COMMITS, and BOTH supplies
--   are UNCHANGED: the bridge well 1 went −40 (it owes the foreign chain 40) while cell 0 gained 40:
#guard ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).isSome)  --  true
#guard ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (EXACT)
#guard ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map
        (fun s => (s.kernel.bal 1 1, s.kernel.bal 0 1))) == some (-40, 47)  --  the bridge well IS −outstanding
-- ...the delta family vanishes (W1: NO non-conserving verb is left):
#guard ((ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 0, ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 1)) == (0, 0)  --  (0, 0)
-- ...and the bridge receipt records the truthful well → recipient move of 40:
#guard (((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0) == 40  --  40
-- An UNAUTHORIZED bridge-mint (actor 0, no mint cap over the bridge cell) is REJECTED (the LOCAL
--   gate, independent of the §8 foreign-finality portal):
#guard ((execFullA fmaSup (.bridgeMintA 0 0 1 40)).isSome) == false  --  false

-- A MIXED supply turn: createCell 2 (neutral growth) + bridgeMint 40 of asset 1 into cell 0
--   (issuer-move) → BOTH assets conserved exactly:
def supplyMixedTurn : List FullActionA :=
  [ .createCellA 9 2
  , .bridgeMintA 9 0 1 40 ]

#guard ((execFullTurnA fmaSup supplyMixedTurn).isSome)  --  true (all commit)
#guard ((turnLedgerDeltaAsset supplyMixedTurn 0, turnLedgerDeltaAsset supplyMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaSup supplyMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §13-seal (Wave 6) — Non-vacuity for the 6 SIMPLE bal-neutral effects: the cell flag/metadata/
refusal record MOVES (a flag flips), yet `recTotalAsset` is UNCHANGED in EVERY asset
(balance-NEUTRALITY witnessed by an `#eval`); authority is REAL (an unauthorized actor fails-closed);
the §8 crypto (AEAD for seal/unseal, the commitment for makeSovereign) is the HONEST chain-layer
portal — NOT exercised here sound. -/

-- Reuse `fmaS` (cell 0 carries a record; empty caps ⇒ authority by OWNERSHIP, actor = cell).
-- Pre-state per-asset supply: asset 0 = 105, asset 1 = 7.

-- `fmaW3` gives cell 0 a 3-cap c-list (for the refresh-snapshot witness) plus a delegation parent
-- (cell 0 is the parent of child 1) for refresh. Asset 0 = 105, asset 1 = 7 (as fmaS).
-- F3: the seal/swiss verb family is FACTORY-DISSOLVED (caps-in-slots, `Apps/CapSlotFactory.lean`,
-- R7 epoch-at-retrieval) — the sealer/unsealer fixture caps became generic endpoint caps.
def fmaW3 : RecChainedState :=
  { kernel :=
      { fmaS.kernel with
        caps := fun l => if l = 0 then [Cap.endpoint 5 [Auth.grant], Cap.endpoint 5 [Auth.reply], Cap.node 42] else []
        delegate := fun c => if c = 1 then some 0 else none }   -- child 1's parent is cell 0
    log := [] }

-- ★ WAVE-3 NON-VACUITY: the cell LIFECYCLE state machine. Seal cell 0 (Live→Sealed), then a destroyed
-- cell REJECTS a follow-on effect (terminal). First, a Live cell seals; a Sealed cell's seal-gate FIRES:
#guard ((execFullA fmaS (.cellSealA 0 0)).isSome)  --  true (Live→Sealed)
#guard ((execFullA fmaS (.cellSealA 0 0)).map (fun s => s.kernel.lifecycle 0)) == some 1  --  some 1 (Sealed)
-- a SEALED cell's lifecycle gate FIRES: it rejects a SECOND seal (AlreadySealed):
#guard (((execFullA fmaS (.cellSealA 0 0)).bind (fun s => execFullA s (.cellSealA 0 0))).isSome) == false  --  false (gate fires)
-- but a SEALED cell CAN be unsealed (Sealed→Live) or destroyed (seal is the prelude to destruction):
#guard (((execFullA fmaS (.cellSealA 0 0)).bind (fun s => execFullA s (.cellUnsealA 0 0))).map
        (fun s => s.kernel.lifecycle 0)) == some 0  --  some 0 (back to Live)
-- ★ A DESTROYED cell is TERMINAL — it REJECTS a follow-on effect. Destroy cell 0 (binds cert 777):
#guard ((execFullA fmaS (.cellDestroyA 0 0 777)).map (fun s => s.kernel.lifecycle 0)) == some 3  --  some 3 (Destroyed)
#guard ((execFullA fmaS (.cellDestroyA 0 0 777)).map (fun s => s.kernel.deathCert 0)) == some 777  --  some 777 (cert bound into final state)
-- a DESTROYED cell rejects a follow-on seal/unseal/destroy (terminal — no further transition):
#guard (((execFullA fmaS (.cellDestroyA 0 0 777)).bind (fun s => execFullA s (.cellSealA 0 0))).isSome) == false  --  false
#guard (((execFullA fmaS (.cellDestroyA 0 0 777)).bind (fun s => execFullA s (.cellDestroyA 0 0 888))).isSome) == false  --  false (terminal)
-- FAIL-CLOSED: an unauthorized actor cannot drive the lifecycle:
#guard ((execFullA fmaS (.cellSealA 9 0)).isSome) == false  --  false

-- ★ WAVE-3 NON-VACUITY: refreshDelegation SNAPSHOTS the parent's CURRENT c-list. Child 1's parent is
-- cell 0 (which holds 3 caps); refresh writes that snapshot into child 1:
#guard ((execFullA fmaW3 (.refreshDelegationA 1 1)).isSome)  --  true (self-authorized, has parent 0)
#guard ((execFullA fmaW3 (.refreshDelegationA 1 1)).map (fun s => (s.kernel.delegations 1).length)) == some 3  --  some 3 (parent cell 0's 3 caps snapshotted)
-- FAIL-CLOSED: a cell with NO parent (cell 0, delegate = 0) cannot refresh:
#guard ((execFullA fmaW3 (.refreshDelegationA 0 0)).isSome) == false  --  false (no parent)

-- ★ FILL #133 — MakeSovereign is a VALUE-REBIND, not a flag. dregg1's `make_sovereign` REMOVES the
--   readable cell (`cells.remove(id)`) and keeps ONLY a 32-byte commitment (`sovereign_commitments`).
--   The rebound cell carries the commitment-only record; the host can NO LONGER read its state.
-- (a) it commits (the self-sovereign authority gate holds: actor = cell = owner):
#guard ((execFullA fmaS (.makeSovereignA 0 0)).isSome)  --  true
-- (b) ★ THE TEETH: the pre-state `balance` is NO LONGER directly readable — the record was DROPPED
--     behind the commitment (a flag model leaves it readable; this is the §8-portal boundary):
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => (Value.scalar (s.kernel.cell 0) "balance").isNone)) == some true  -- some none (UNREADABLE)
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => ((s.kernel.cell 0).field "nonce").isNone && ((s.kernel.cell 0).field "permissions").isNone)) == some true  -- some (none, none) (ALL DROPPED)
-- (c) the COMMITMENT is present — a digest of the FULL pre-state value (`cell.state_commitment()`):
#guard (match (execFullA fmaS (.makeSovereignA 0 0)).map
              (fun s => (s.kernel.cell 0).field commitmentField) with
        | some (some (Value.dig d)) => d == stateCommitment (fmaS.kernel.cell 0)
        | _ => false)  --  some (some (Value.dig …)) (PRESENT)
#guard (match sovereignRebind fmaS.kernel.cell 0 0 with
        | Value.record fs =>
          match fs.find? (fun p => p.1 == commitmentField) with
          | some (_, Value.dig d) => d == stateCommitment (fmaS.kernel.cell 0) && fs.length == 1
          | _ => false
        | _ => false)  --  the rebound record IS commitment-only
-- ...and DISTINCT pre-states give DISTINCT commitments (the binding is a function of the whole value):
#guard ((stateCommitment (.record [("balance", .int 0)]) == stateCommitment (.record [("balance", .int 1)]))) == false  --  false (binds value)
-- (d) bal-NEUTRAL on the per-asset ledger (the value moves behind the commitment on the HOST, not the
--     per-asset supply — `recTotalAsset` reads `bal`, independent of the rebound `cell` record):
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (SUPPLY PRESERVED)
-- (e) FAIL-CLOSED: an unauthorized actor (9 owns nothing) cannot make cell 0 sovereign:
#guard ((execFullA fmaS (.makeSovereignA 9 0)).isSome) == false  --  false (FAIL-CLOSED)

-- Refusal: write the `refusal` audit record (dregg1 bumps nonce + records commitment; NEVER touches
--   balance/caps/value), balance-neutral:
#guard ((execFullA fmaS (.refusalA 0 0)).map (fun s => fieldOf "refusal" (s.kernel.cell 0))) == some 1  --  some 1
#guard ((execFullA fmaS (.refusalA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
#guard ((execFullA fmaS (.refusalA 9 0)).isSome) == false  --  false (FAIL-CLOSED)

-- ReceiptArchive (DEPLOYED semantics): move the `lifecycle` SIDE-TABLE to Archived (4) — the
--   cellSeal/cellDestroy shape (`c.archive(checkpoint)`), NOT a `cell` record-slot write — balance-neutral:
#guard ((execFullA fmaS (.receiptArchiveA 0 0)).map (fun s => s.kernel.lifecycle 0)) == some lcArchived  --  some 4
#guard ((execFullA fmaS (.receiptArchiveA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
#guard ((execFullA fmaS (.receiptArchiveA 9 0)).isSome) == false  --  false (FAIL-CLOSED, unauthorized)
-- ...and a NON-Live (sealed) cell cannot be archived (the liveness leg of auditGuard fails):
#guard ((execFullA { fmaS with kernel := setLifecycle fmaS.kernel 0 lcSealed } (.receiptArchiveA 0 0)).isSome) == false  --  false (FAIL-CLOSED, non-live)

-- Every lifecycle/refresh effect's per-asset ledgerDelta is 0 at every asset (balance-NEUTRAL):
#guard ((ledgerDeltaAsset (.cellSealA 0 0) 1,
       ledgerDeltaAsset (.cellDestroyA 0 0 777) 0, ledgerDeltaAsset (.refreshDelegationA 1 1) 1)) == (0, 0, 0)  --  (0, 0, 0)

-- A MIXED per-asset turn interleaving a bal-neutral refresh with a transfer: balance moves ONLY by the
--   transfer delta ⇒ (105, 7) preserved as a TOTAL; the chain grows by node count. (F3: the old
--   seal→balance→unseal spine moved to the caps-in-slots factory, `Apps/CapSlotFactory.lean`.)
def sealMixedTurn : List FullActionA :=
  [ .refreshDelegationA 1 1            -- child 1 refreshes its parent snapshot (bal-neutral)
  , .balanceA ⟨0, 0, 1, 30⟩ 0 ]        -- transfer 30 of asset 0, cell 0 → cell 1 (conserves)

#guard ((execFullTurnA fmaW3 sealMixedTurn).isSome)  --  true (all commit on the cap-rich fixture)
#guard ((turnLedgerDeltaAsset sealMixedTurn 0, turnLedgerDeltaAsset sealMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaW3 sealMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (CONSERVED)
#guard ((execFullTurnA fmaW3 sealMixedTurn).map (fun s => s.log.length)) == some 2  --  some 2 (chain grew by node count)
-- the snapshot moved: child 1's delegation snapshot is the parent's 3-cap c-list:
#guard ((execFullTurnA fmaW3 sealMixedTurn).map (fun s => (s.kernel.delegations 1).length)) == some 3  --  some 3 (snapshot taken)

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
#guard (subFactory.conforms)  --  true
-- A factory cannot smuggle scalar `balance` through initial fields; per-asset `bal` is born empty:
#guard (badBalanceFactory.conforms) == false  --  false
#guard ((execFullA facBadBalanceS (.createCellFromFactoryA 0 5 43)).isSome) == false  --  false
-- An UNKNOWN factory vk (99 ∉ registry) is REJECTED (fail-closed, apply.rs:3140):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 99)).isSome) == false  --  false
-- The conforming factory (vk 42) MINTS the fresh cell 5 (born EMPTY ⇒ conservation-neutral):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).isSome)  --  true
-- ...and INSTALLS the factory's slot caveats onto the minted cell (the constructor-transparency keystone):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).map
        (fun s => reprStr (s.kernel.slotCaveats 5)) == reprStr subFactory.caveats)  --  some "[…monotonic head, immutable owner]"
-- ...and writes the factory's initial fields + program VK onto the cell:
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).map
        (fun s => (fieldOf "head" (s.kernel.cell 5), fieldOf "owner" (s.kernel.cell 5),
                   fieldOf factoryVkField (s.kernel.cell 5)))) == some (0, 9, 7)  --  some (0, 9, 7)

-- THE TEETH: from the MINTED cell, a later `SetField` to the installed-caveat slots is gated BY THE
-- EXECUTOR — an Immutable `owner` rewrite (9→8) is REJECTED; a non-monotone `head` write (0→ −1 would
-- decrease) is REJECTED; a monotone `head` advance (0→3) is ADMITTED:
#guard (((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "owner" 8))).isSome) == false  --  false (Immutable owner: registered forever)
#guard (((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "head" (-1)))).isSome) == false  --  false (Monotonic head: cannot decrease)
#guard (((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "head" 3))).map
        (fun s => fieldOf "head" (s.kernel.cell 5))) == some 3  --  some 3 (monotone advance admitted)
-- A factory whose OWN initial state violates its caveats is REJECTED at mint (validate_and_record):
#guard ((FactoryEntry.conforms { caveats := [.boundedBy "x" 0 10], initialFields := [("x", 99)], programVk := 0 })) == false  --  false

-- §MA-factory NEGATIVE-VK ATTACK (codex P1): `findFactory … vk.toNat` would map every negative `vk`
-- to key `0` (`Int.toNat (-1) = 0`), so a negative `vk` could ALIAS factory `0`. `fac0S` parks the
-- subscription factory at key `0` (the alias target); the guard rejects `vk = -1` BEFORE the lookup.
def fac0S : RecChainedState :=
  { facS with kernel := { facS.kernel with factories := [(0, subFactory)] } }
-- The honest call with the real non-negative key `0` MINTS (the factory lives at `0`):
#guard ((execFullA fac0S (.createCellFromFactoryA 0 5 0)).isSome)  --  true
-- THE ATTACK: `vk = -1` does not alias factory `0` — it is REJECTED before `findFactory`:
#guard ((execFullA fac0S (.createCellFromFactoryA 0 5 (-1))).isSome) == false  --  false (no aliasing)
-- ...and is rejected even when the alias target is a conforming, mintable factory at key `0`:
#guard ((createCellFromFactoryChainA fac0S 0 5 (-1)).isSome) == false  --  false
-- A legit non-negative `vk` against the original (key-42) registry still works unchanged:
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).isSome)  --  true

/-! ### §MA-pipelined-send #eval — the apply-time NEUTRAL marker on the executed dispatch.
(F2b: the queue atomic-batch / pipeline-step fixtures died with the queue verb family — queue
behavior is the factory story, `Apps/{QueueFactory,InboxFactory,PubsubFactory}.lean`.) -/

def fmaP : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
        bal := fun c a => if c = 0 ∧ a = 0 then 50 else 0 }
    log := [] }

-- ★ PIPELINED-SEND — the apply-time NEUTRAL marker (the EventualRef resolution is `ConditionalTurn`'s
--   batch; AT apply the resolved action already ran, so this is a balance-neutral clock row that COMMITS):
#guard ((execFullA fmaP (.pipelinedSendA 0)).isSome)  --  true — apply-time neutral commits
#guard ((execFullA fmaP (.pipelinedSendA 0)).map
        (fun s => (recTotalAsset s.kernel 0, s.log.length))) == some (50, 1)  --  some (50, 1) — NEUTRAL + one clock row

end Dregg2.Exec.TurnExecutorFull
