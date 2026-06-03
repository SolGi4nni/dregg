/-
# Dregg2.Apps.AgentOrchestration — verified multi-agent orchestration; the orchestration is a theorem.

An orchestrator cell spawns least-privilege sub-agent workers, delegates each an attenuated slice of its
authority, the workers run real per-asset transfers, an out-of-scope worker is provably rejected, two
agents move value through an escrow, a credential+caveat gate fail-closes on a forged credential or
failing caveat, and the whole run is assembled into one call-forest certified by Lean theorems.

The executable turn (`Exec/TurnExecutorFull`, `Exec/FullForest`, `Exec/FullForestAuth`, `Exec/Caps`) is
pure computable Lean: `main` runs the scenes by calling the real executor, and every ✓ printed is backed
by one of the theorems below.

## Honesty label

What is genuine: every theorem is a real, non-vacuous fact about the concrete run —
  * conservation: per-asset `recTotalAssetWithEscrow` vector over the actual forest (a scalar aggregate
    could not state it);
  * fail-closed: a real proved `execFullForestA … = none` for the concrete bad worker turn, not an `#eval`;
  * non-amplification: `capAuthConferred (attenuate keep c) ⊆ capAuthConferred c` (`derive_no_amplify`),
    with a strict attenuation witness (`write` literally dropped);
  * escrow combined-conservation: `execFullA_ledger_per_asset` with `ledgerDeltaAsset = 0`;
  * auth gate committed⇒(credential ∧ caveats): `execFullForestG_root_attests` on the gated tree.

What is a portal (NOT a Lean law, by design): `credentialValid` is the §8 `AuthPortal` oracle (the
circuit's obligation, never proved sound inside Lean — the seL4 floor). We prove the gate discipline
(fail-closed on a forged/revoked credential), not the crypto.

The scenario is intra-cell: the cross-cell axis is in `Exec/CrossCellForest.lean`.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Every keystone is `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest
import Dregg2.Exec.FullForestAuth
import Dregg2.Exec.Caps

namespace Dregg2.Apps.AgentOrchestration

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority

/-! ## §0 — Ledger: orchestrator + two assets.

The starting ledger is `TurnExecutorFull.fma0` — a 2-asset ledger:
  * cell **0** (orchestrator): holds 100 of asset 0 and 7 of asset 1;
  * cell **1** (counterparty): holds 5 of asset 0;
  * actor **9** holds the privileged `node 0` mint cap over cell 0 (the supply authority).
Authority for balance transfers is by ownership (`actor = src`). Asset-0 supply = 105, asset-1 = 7. -/

/-- The orchestrator cell id (broad authority, the assets). -/
abbrev orchestrator : CellId := 0
/-- The counterparty cell id. -/
abbrev counterparty : CellId := 1
/-- The privileged supply-authority holder (holds the `node 0` mint cap in `fma0`). -/
abbrev minter : CellId := 9

/-- The starting ledger — `fma0`'s 2-asset accounts with the orchestrator's cap table grounded so
delegation edges pass the `recCDelegateAtten` gate. Cell **0** holds `endpoint 1 [read,write]` and
`endpoint 0 [read,write]`, but NOT `node 0`, so the `mintAuthorizedB` gate still rejects actor 0's
out-of-scope mint (only `minter` = 9 holds the supply cap, as in `fma0`). -/
def world : RecChainedState :=
  { fma0 with kernel :=
      { fma0.kernel with
        caps := fun l => if l = 0 then [Cap.endpoint 1 [Auth.read, Auth.write], Cap.endpoint 0 [Auth.read, Auth.write]]
                         else fma0.kernel.caps l } }

/-! ## §1 — Spawn least-privilege workers + the non-amplification theorem.

The orchestrator delegates each worker an attenuated slice of its authority via `FullChildA`
(`holder`, `keep`, `parentCap`): the parent hands the worker `attenuate keep parentCap`. The
Granovetter no-amplification law (`derive_no_amplify`) bounds the worker's conferred authority to
a subset of the parent's. The attenuation used here is strict: the parent cap confers `[read, write]`,
the worker keeps only `[read]` — `write` is literally dropped. -/

/-- The orchestrator's broad endpoint cap over the counterparty cell: `[read, write]`. -/
def orchestratorCap : Cap := .endpoint counterparty [Auth.read, Auth.write]

/-- The attenuated slice a worker is delegated: keep only `[read]` (drop `write`). -/
def workerKeep : List Auth := [Auth.read]

/-- **`worker_authority_subset_orchestrator` — ① non-amplification.** The authority conferred to a
delegated worker (`attenuate workerKeep orchestratorCap`) is a subset of the orchestrator's: a worker
cannot exceed the authority it was handed. This is `Caps.derive_no_amplify` (= `attenuate_subset`),
inherited, not re-proved. -/
theorem worker_authority_subset_orchestrator :
    capAuthConferred (attenuate workerKeep orchestratorCap) ⊆ capAuthConferred orchestratorCap :=
  derive_no_amplify workerKeep orchestratorCap

/-- **`worker_attenuation_is_strict` — the subset is strict (non-vacuous).** `write` is conferred by
the orchestrator's cap but not by the attenuated worker cap — the subset above is a genuine drop. -/
theorem worker_attenuation_is_strict :
    Auth.write ∈ capAuthConferred orchestratorCap ∧
    Auth.write ∉ capAuthConferred (attenuate workerKeep orchestratorCap) := by
  decide

/-! ## §2 — Execute real per-asset transfers + the conservation theorem.

Workers run genuine per-asset balance transfers (`balanceA`). The per-asset conservation vector
(`execFullForestA_conserves_per_asset`) certifies that every asset's total supply is preserved. -/

/-- **`workForest`** — the orchestrator (root) transfers 30 of asset 0 to the counterparty; a delegated
worker transfers 5 of asset 0 back; each under an attenuated, non-amplifying cap. Both transfers
conserve asset 0 (and trivially asset 1), so the whole forest conserves per-asset. -/
def workForest : FullForestA :=
  ⟨ .balanceA ⟨orchestrator, orchestrator, counterparty, 30⟩ 0
  , [ { holder := counterparty, keep := workerKeep, parentCap := orchestratorCap
      , sub := ⟨ .balanceA ⟨counterparty, counterparty, orchestrator, 5⟩ 0, [] ⟩ } ] ⟩

/-- **`workForest_delta0` / `workForest_delta1` — per-asset net is `0` in both assets.** Transfers move
value within the cell set; no minting or burning. These discharge the `hzero` premise of conservation.
Non-vacuous: a mint would make them nonzero. -/
theorem workForest_delta0 : turnLedgerDeltaAsset (lowerForestA workForest) 0 = 0 := by decide
theorem workForest_delta1 : turnLedgerDeltaAsset (lowerForestA workForest) 1 = 0 := by decide

/-- **`workForest_conserves` — ② conservation.** A committed work forest preserves every asset's total
supply (`recTotalAssetWithEscrow … b` for every `b`): the per-asset conservation vector across the whole
tree. This is `execFullForestA_conserves_per_asset`, discharged by `workForest_delta0`/`_delta1`.
Non-vacuous: a scalar aggregate could not even state it. -/
theorem workForest_conserves (s' : RecChainedState) (b : AssetId)
    (h : execFullForestA world workForest = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow world.kernel b := by
  -- Per-asset net is 0 in each asset (the two assets the ledger carries; others trivially 0).
  have hzero : turnLedgerDeltaAsset (lowerForestA workForest) b = 0 := by
    -- `balanceA` transfers have `ledgerDeltaAsset = 0` at EVERY asset, so the turn delta is 0 for any b.
    simp only [workForest, lowerForestA, lowerChildrenA, capTarget, orchestratorCap,
               List.cons_append, List.nil_append, turnLedgerDeltaAsset,
               List.map_cons, List.map_nil, List.append_nil, List.sum_cons, List.sum_nil,
               ledgerDeltaAsset, add_zero]
  exact execFullForestA_conserves_per_asset world s' workForest b h hzero

/-! ## §3 — Denied: the out-of-scope worker is provably rejected.

A worker attempts an unauthorized supply mint (actor 0 lacks the `node 0` mint cap — only `minter` = 9
holds it). The executor's `mintAuthorizedB` gate rejects it, and the all-or-nothing rollback discipline
rejects the whole forest. This is a real proved fact (`execFullA … = none`, `execFullForestA … = none`),
not an `#eval` observation. -/

/-- **`badWorkerForest`** — a delegated worker (actor 0) attempts to mint +50 of asset 1 on cell 0, but
lacks the `node 0` mint cap. The `execFullA` mint-authorization gate rejects the worker node, rolling
back the whole forest. -/
def badWorkerForest : FullForestA :=
  ⟨ .balanceA ⟨orchestrator, orchestrator, counterparty, 30⟩ 0
  , [ { holder := orchestrator, keep := workerKeep, parentCap := orchestratorCap
      , sub := ⟨ .mintA orchestrator orchestrator 1 50, [] ⟩ } ] ⟩   -- actor 0 lacks the node-0 mint cap

/-- **`unauthorized_mint_rejected`** — the worker's unauthorized mint returns `none`: the `mintAuthorizedB`
gate fail-closes because actor 0 holds no mint cap over cell 0. -/
theorem unauthorized_mint_rejected :
    execFullA world (.mintA orchestrator orchestrator 1 50) = none := by decide

/-- **`badWorkerForest_fails_closed` — ③ fail-closed.** The whole bad-worker forest is rejected: no
post-state. The all-or-nothing discipline rolls back the entire forest because the delegated worker's
mint is unauthorized — a real `execFullForestA … = none`, not a demo `if`. -/
theorem badWorkerForest_fails_closed :
    execFullForestA world badWorkerForest = none := by decide

/-- **`recKExecAsset_fail_closed_reused`** — the kernel-level fail-closed primitive (`recKExecAsset_unauthorized_fails`)
named directly so the denied scene rests on the same proved primitive the whole executor uses. -/
theorem recKExecAsset_fail_closed_reused (turn : Turn) (a : AssetId)
    (h : authorizedB world.kernel.caps turn = false) :
    recKExecAsset world.kernel turn a = none :=
  recKExecAsset_unauthorized_fails world.kernel turn a h

/-! ## §4 — Escrow: atomic value-move between two agents + combined-conservation.

The orchestrator locks 5 of asset 1 into escrow (bare ledger drops, holding-store rises). The combined
per-asset measure `recTotalAssetWithEscrow` (= ledger + holding-store) is conserved across the lock —
value is parked, never created or destroyed. This is `execFullA_ledger_per_asset` with
`ledgerDeltaAsset = 0` on the escrow leg. -/

/-- The escrow lock: orchestrator (actor `minter`, authorized over cell 0) locks 5 of asset 1 from the
orchestrator cell to the counterparty, escrow id 1. -/
def escrowLock : FullActionA :=
  .createEscrowA 1 minter orchestrator counterparty 1 5

/-- **`escrowLock_combined_conserves` — ④ escrow combined-conservation.** A committed escrow lock
preserves the combined per-asset measure `recTotalAssetWithEscrow b` at every asset: the bare ledger
debit at asset 1 is offset by the holding-store rise. `execFullA_ledger_per_asset` with the escrow
leg's `ledgerDeltaAsset = 0`. Non-vacuous: the bare ledger genuinely drops at the locked asset while
the combined measure holds. -/
theorem escrowLock_combined_conserves (s' : RecChainedState) (b : AssetId)
    (h : execFullA world escrowLock = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow world.kernel b := by
  have hdelta : ledgerDeltaAsset escrowLock b = 0 := by
    simp only [escrowLock, ledgerDeltaAsset]
  rw [execFullA_ledger_per_asset world s' escrowLock b h, hdelta, add_zero]

/-! ## §5 — Auth gate: credential + caveat + committed⇒(credential ∧ caveats).

A gated node commits iff `credentialValid` (the §8 portal) ∧ cap-authority ∧ caveats discharge. The
keystone `execFullForestG_root_attests` gives the attestation on a committed node; `execFullForestG_unauthorized_fails`
is the fail-closed half. `FullForestAuth.Demo` instances provide the concrete test cases. -/

open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForestAuth.Demo

/-- The `Verifiable` seam `execFullForestG`'s type requires over the Demo carriers (`St = Wt = Nat`).
`FullForestAuth`'s own `demoVerifiable` is `local`; this re-pins the same trivial seam so the gated
executor resolves. -/
instance demoVerifiableAO : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-- **`gate_committed_implies_credential_and_caveats` — ⑤ auth gate: committed ⇒ credential validated
∧ caveats discharged.** If the good gated forest commits, its root attests `gatedActionInvG`:
credential passed the §8 `AuthPortal` oracle, cap-authority held, and caveats discharged.
`execFullForestG_root_attests` on the concrete `goodFullForestG`. -/
theorem gate_committed_implies_credential_and_caveats (s' : RecChainedState)
    (h : execFullForestG world goodFullForestG = some s') :
    ∃ sa sa', execFullAGated sa goodFullForestG.auth goodFullForestG.action = some sa' ∧
              credentialValidG goodFullForestG.auth = true ∧
              capAuthorityG goodFullForestG.auth = true ∧
              caveatsDischarged goodFullForestG.auth sa = true := by
  -- `gatedActionInvG` is `credentialValidG ∧ capAuthorityG ∧ caveatsDischarged ∧ fullActionInvA`;
  -- we forward the first three auth conjuncts (the per-asset `fullActionInvA` is the §6 headline).
  obtain ⟨sa, sa', hrun, hcred, hcap, hcav, _hinv⟩ :=
    execFullForestG_root_attests world s' goodFullForestG h
  exact ⟨sa, sa', hrun, hcred, hcap, hcav⟩

/-- **`forged_credential_denied`** — a node whose credential does not pass the §8 portal is denied:
the whole forest rejects, even if the caps would otherwise admit. `execFullForestG_unauthorized_fails`
with `gateOK = false` because `credentialValidG = false`. Non-vacuous: the forged credential
genuinely fails the portal. -/
theorem forged_credential_denied :
    execFullForestG world forgedCredForestG = none := by
  apply execFullForestG_unauthorized_fails
  -- The gate fails on the WHO leg: the forged credential does not echo under the §8 portal, so
  -- `credentialValidG = false` (reduces definitionally) ⇒ the whole `gateOK` conjunction is false.
  have hcred : credentialValidG forgedCredForestG.auth = false := rfl
  show gateOK forgedCredForestG.auth world = false
  simp only [gateOK, hcred, Bool.false_and]

/-- **`false_caveat_denied`** — a node whose caveat does not discharge on the pre-state is denied.
Non-vacuous: the false caveat (cell 0 holds ≥ 10000 of asset 0, but it holds 100) genuinely fails. -/
theorem false_caveat_denied :
    execFullForestG world falseCaveatForestG = none := by
  apply execFullForestG_unauthorized_fails
  -- The gate fails on the CAVEAT leg: the false caveat (cell 0 ≥ 10000) is false on `world` (bal=100).
  have hcav : caveatsDischarged falseCaveatForestG.auth world = false := by
    simp only [caveatsDischarged, falseCaveatForestG, mkAuth, falseCaveat, List.all_cons,
               List.all_nil, GatedCaveat.holds, chainGateG, Bool.and_true, world]
    decide
  show gateOK falseCaveatForestG.auth world = false
  simp only [gateOK, hcav, Bool.and_false, Bool.false_and]

/-! ## §6 — The whole orchestration is a theorem.

Three theorems certify the assembled run at once:
  * **conserves every asset** — `execFullForestA_conserves_per_asset` (per-asset vector);
  * **no agent amplified authority** — `execFullForestA_no_amplify` (every delegation edge non-amplifying);
  * **every committed node attested its StepInv** — `execFullForestA_each_attests` (per-asset ledger
    vector ∧ ChainLink ∧ ObsAdvance ∧ the kind obligation). -/

/-- **`orchestration`** — the whole multi-agent run as one call-forest:
  * root (`minter`): mint +50 of asset 1 on cell 0;
  * worker A (delegated, `[read] ⊊ [read,write]`): transfer 30 of asset 0;
  * worker B (delegated, deeper): burn −50 of asset 1 (`minter`).
Per-asset net is `0` in both assets (asset 1: +50 −50 = 0; asset 0: 0). Every delegation edge is
non-amplifying. -/
def orchestration : FullForestA :=
  ⟨ .mintA minter orchestrator 1 50
  , [ { holder := counterparty, keep := workerKeep, parentCap := orchestratorCap
      , sub := ⟨ .balanceA ⟨orchestrator, orchestrator, counterparty, 30⟩ 0
               , [ { holder := minter, keep := [], parentCap := .endpoint orchestrator [Auth.read]
                   , sub := ⟨ .burnA minter orchestrator 1 50, [] ⟩ } ] ⟩ } ] ⟩

/-- **`orchestration_conserves` — ⑥a the whole run conserves every asset.** For every asset `b`, the
committed orchestration preserves `recTotalAssetWithEscrow … b`. The mint and burn net to `0` in asset 1;
the transfer is internal. `execFullForestA_conserves_per_asset` on the concrete run. -/
theorem orchestration_conserves (s' : RecChainedState) (b : AssetId)
    (h : execFullForestA world orchestration = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow world.kernel b := by
  have hzero : turnLedgerDeltaAsset (lowerForestA orchestration) b = 0 := by
    -- asset 1: +50 (mint) − 50 (burn) = 0; asset 0: 0; every other asset: 0.
    simp only [orchestration, lowerForestA, lowerChildrenA, capTarget, orchestratorCap,
               List.cons_append, List.nil_append, turnLedgerDeltaAsset,
               List.map_cons, List.map_nil, List.append_nil, List.sum_cons, List.sum_nil,
               ledgerDeltaAsset, add_zero]
    by_cases hb : b = 1
    · subst hb; decide
    · simp only [if_neg hb, add_zero]
  exact execFullForestA_conserves_per_asset world s' orchestration b h hzero

/-- **`orchestration_no_amplify` — ⑥b no agent amplified authority.** Every delegation edge is
non-amplifying: for each `(keep, parentCap)` edge the cap handed to the worker confers ⊆ the parent's
authority. `execFullForestA_no_amplify` on the concrete run, inherited. -/
theorem orchestration_no_amplify :
    ∀ e ∈ forestEdgesA orchestration,
      capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 :=
  execFullForestA_no_amplify orchestration

/-- **`orchestration_each_attests` — ⑥c every committed node attested its StepInv.** Every node attests
`fullActionInvA`: per-asset ledger vector ∧ ChainLink ∧ ObsAdvance ∧ kind-specific authority obligation.
`execFullForestA_each_attests` on the concrete run, inherited. -/
theorem orchestration_each_attests (s' : RecChainedState)
    (h : execFullForestA world orchestration = some s') :
    ∀ fa ∈ lowerForestA orchestration,
      ∃ sa sa', execFullA sa fa = some sa' ∧ fullActionInvA sa fa sa' :=
  execFullForestA_each_attests world s' orchestration h

/-- **`orchestration_runs`** — the whole assembled orchestration genuinely commits (`isSome`): the
conservation/no-amplify/attestation theorems are not vacuously quantified over a never-committing
forest — there is a post-state. -/
theorem orchestration_runs : (execFullForestA world orchestration).isSome = true := by decide

/-! ## §7 — Axiom-hygiene — every scenario keystone pinned to the three standard kernel axioms. -/

#assert_axioms worker_authority_subset_orchestrator
#assert_axioms worker_attenuation_is_strict
#assert_axioms workForest_delta0
#assert_axioms workForest_delta1
#assert_axioms workForest_conserves
#assert_axioms unauthorized_mint_rejected
#assert_axioms badWorkerForest_fails_closed
#assert_axioms recKExecAsset_fail_closed_reused
#assert_axioms escrowLock_combined_conserves
#assert_axioms gate_committed_implies_credential_and_caveats
#assert_axioms forged_credential_denied
#assert_axioms false_caveat_denied
#assert_axioms orchestration_conserves
#assert_axioms orchestration_no_amplify
#assert_axioms orchestration_each_attests
#assert_axioms orchestration_runs

/-! ## §8 — The runnable demonstrator.

`main` calls the real executor on the concrete scenes and after each scene names the Lean theorem that
certifies it. Deterministic; pure computable Lean. -/

/-! ### ANSI palette (deterministic escape codes). -/

/-- Reset. -/ def aRESET : String := "\x1b[0m"
/-- Bold. -/  def aBOLD  : String := "\x1b[1m"
/-- Dim. -/   def aDIM   : String := "\x1b[2m"
/-- Green. -/ def aGREEN : String := "\x1b[32m"
/-- Red. -/   def aRED   : String := "\x1b[31m"
/-- Cyan. -/  def aCYAN  : String := "\x1b[36m"
/-- Yellow. -/def aYEL   : String := "\x1b[33m"
/-- Magenta (headers). -/ def aMAG : String := "\x1b[35m"

/-- A bold scene header with a rule. -/
def scene (n : String) (title : String) : IO Unit := do
  IO.println ""
  IO.println s!"{aBOLD}{aMAG}━━ {n}  {title} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{aRESET}"

/-- A green ✓ commit line. -/
def ok (msg : String) : IO Unit := IO.println s!"  {aGREEN}✓ {msg}{aRESET}"
/-- A red ✗ DENIED line. -/
def denied (msg : String) : IO Unit := IO.println s!"  {aRED}✗ DENIED  {msg}{aRESET}"
/-- A cyan delegation/auth line. -/
def cyan (msg : String) : IO Unit := IO.println s!"  {aCYAN}⇒ {msg}{aRESET}"
/-- A yellow escrow line. -/
def yellow (msg : String) : IO Unit := IO.println s!"  {aYEL}⛁ {msg}{aRESET}"
/-- A dim detail line. -/
def detail (msg : String) : IO Unit := IO.println s!"    {aDIM}{msg}{aRESET}"
/-- The theorem-citation line for a scene. -/
def certifies (thm : String) : IO Unit :=
  IO.println s!"    {aDIM}└─ certified by{aRESET} {aBOLD}{thm}{aRESET}"

/-- The per-asset supply pair `(asset 0, asset 1)` of a post-state, as a string. -/
def supplyStr (s : RecChainedState) : String :=
  s!"(asset0={recTotalAsset s.kernel 0}, asset1={recTotalAsset s.kernel 1})"

/-- The COMBINED per-asset measure pair of a post-state, as a string. -/
def combinedStr (s : RecChainedState) : String :=
  s!"(asset0={recTotalAssetWithEscrow s.kernel 0}, asset1={recTotalAssetWithEscrow s.kernel 1})"

def main : IO Unit := do
  IO.println ""
  IO.println s!"{aBOLD}{aMAG}╔══════════════════════════════════════════════════════════════════╗{aRESET}"
  IO.println s!"{aBOLD}{aMAG}║   dregg2 · VERIFIED MULTI-AGENT ORCHESTRATION                     ║{aRESET}"
  IO.println s!"{aBOLD}{aMAG}║   \"the orchestration is a theorem\"                                ║{aRESET}"
  IO.println s!"{aBOLD}{aMAG}╚══════════════════════════════════════════════════════════════════╝{aRESET}"
  detail s!"ledger: orchestrator(cell 0)=100·a0 + 7·a1, counterparty(cell 1)=5·a0; minter(9) holds node-0 cap"
  detail s!"pre-state per-asset supply {supplyStr world}"

  -- ① SPAWN least-privilege workers + NON-AMPLIFICATION
  scene "①" "SPAWN least-privilege workers — attenuated delegation"
  cyan s!"orchestrator delegates a worker: parentCap confers {repr (capAuthConferred orchestratorCap)}"
  cyan s!"worker keeps only {repr workerKeep} ⇒ conferred {repr (capAuthConferred (attenuate workerKeep orchestratorCap))}"
  detail s!"write ∈ orchestrator-cap? {capAuthConferred orchestratorCap |>.contains Auth.write}   write ∈ worker-cap? {(capAuthConferred (attenuate workerKeep orchestratorCap)).contains Auth.write}  (STRICT drop)"
  ok "worker authority ⊆ orchestrator authority — no amplification"
  certifies "worker_authority_subset_orchestrator (= Caps.derive_no_amplify)"
  certifies "worker_attenuation_is_strict (write LITERALLY dropped — non-vacuous)"

  -- ② EXECUTE real transfers + CONSERVATION
  scene "②" "EXECUTE — workers run real per-asset transfers"
  match execFullForestA world workForest with
  | some s =>
      ok s!"work forest committed: {(lowerForestA workForest).length} agent actions ran"
      detail s!"post-state per-asset supply {supplyStr s}   (pre {supplyStr world})"
      detail s!"per-asset net delta: a0={turnLedgerDeltaAsset (lowerForestA workForest) 0}, a1={turnLedgerDeltaAsset (lowerForestA workForest) 1}"
      ok "every asset's total supply preserved — per-asset CONSERVATION VECTOR"
  | none => denied "work forest unexpectedly rejected"
  certifies "workForest_conserves (= execFullForestA_conserves_per_asset)"

  -- ③ DENIED — out-of-scope worker
  scene "③" "DENIED — a worker acts OUTSIDE its scope (the money shot)"
  cyan "delegated worker (actor 0) attempts mint +50·a1 — but holds NO node-0 mint cap"
  detail s!"execFullA(worker mint) = {repr (execFullA world (.mintA orchestrator orchestrator 1 50)).isSome}  (none ⇒ fail-closed)"
  match execFullForestA world badWorkerForest with
  | some _ => ok "unexpected commit"
  | none =>
      denied "the unauthorized mint is rejected — whole forest rolls back (all-or-nothing)"
      detail "the orchestrator's own transfer would have committed; one bad beat aborts the run"
  certifies "badWorkerForest_fails_closed (execFullForestA … = none, PROVED)"
  certifies "unauthorized_mint_rejected + recKExecAsset_unauthorized_fails (the kernel fail-closed law)"

  -- ④ ESCROW — atomic value-move
  scene "④" "ESCROW — atomic value-move between two agents"
  match execFullA world escrowLock with
  | some s =>
      yellow s!"orchestrator LOCKS 5·a1 into escrow id 1 → counterparty"
      detail s!"bare per-asset supply {supplyStr s}   held(a1)={escrowHeldAsset s.kernel 1}  (value PARKED)"
      detail s!"COMBINED measure {combinedStr s}   (pre {combinedStr world})"
      ok "combined per-asset measure conserved across the lock — value parked, not created/destroyed"
  | none => denied "escrow lock unexpectedly rejected"
  certifies "escrowLock_combined_conserves (= execFullA_ledger_per_asset, escrow leg δ=0)"

  -- ⑤ AUTH GATE — credential + caveat
  scene "⑤" "AUTH GATE — credential + caveat (META-FILL D)"
  match execFullForestG world goodFullForestG with
  | some _ =>
      cyan s!"good node: credentialValid={credentialValidG goodFullForestG.auth}  caveatsDischarged={caveatsDischarged goodFullForestG.auth world}"
      ok "gated forest commits ⇒ credential validated ∧ caveats discharged"
  | none => denied "good gated forest unexpectedly rejected"
  detail s!"FORGED credential: credentialValid={credentialValidG forgedCredForestG.auth} ⇒ gate fails"
  match execFullForestG world forgedCredForestG with
  | some _ => ok "unexpected commit"
  | none => denied "forged-credential node rejected (credential-orthogonality)"
  detail s!"FAILING caveat: caveatsDischarged={caveatsDischarged falseCaveatForestG.auth world} ⇒ gate fails"
  match execFullForestG world falseCaveatForestG with
  | some _ => ok "unexpected commit"
  | none => denied "failing-caveat node rejected (caveat-orthogonality)"
  certifies "gate_committed_implies_credential_and_caveats (= execFullForestG_root_attests)"
  certifies "forged_credential_denied + false_caveat_denied (= execFullForestG_unauthorized_fails)"

  -- ⑥ THE WHOLE ORCHESTRATION IS A THEOREM
  scene "⑥" "THE WHOLE ORCHESTRATION — assembled, run, certified"
  match execFullForestA world orchestration with
  | some s =>
      ok s!"orchestration committed: {(lowerForestA orchestration).length} agent actions (mint / transfer / burn)"
      detail s!"post-state per-asset supply {supplyStr s}   (pre {supplyStr world}) — every asset conserved"
      detail s!"per-asset net delta: a0={turnLedgerDeltaAsset (lowerForestA orchestration) 0}, a1={turnLedgerDeltaAsset (lowerForestA orchestration) 1}  (mint+50 − burn50 = 0)"
      detail s!"delegation edges (all non-amplifying): {(forestEdgesA orchestration).length} edges"
      detail s!"receipt chain length after run: {s.log.length}  (one row per committed node)"
      ok "∀ asset conserved  ∧  ∀ edge non-amplifying  ∧  ∀ node attested its StepInv"
  | none => denied "orchestration unexpectedly rejected"
  certifies "orchestration_conserves ∧ orchestration_no_amplify ∧ orchestration_each_attests"

  IO.println ""
  IO.println s!"{aBOLD}{aGREEN}Every ✓ above is a Lean theorem, checked by the kernel — this file{aRESET}"
  IO.println s!"{aBOLD}{aGREEN}compiling IS the proof. The orchestration is sound by construction.{aRESET}"
  IO.println ""

end Dregg2.Apps.AgentOrchestration

/-- Top-level entry so `lake env lean --run Dregg2/Apps/AgentOrchestration.lean` runs the colored
demonstrator. Delegates to the namespaced `main` above (the orchestration scenes). -/
def main : IO Unit := Dregg2.Apps.AgentOrchestration.main
