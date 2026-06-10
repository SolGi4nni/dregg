import Dregg2.Circuit.Argus.Stmt
import Dregg2.Exec.Admission
import Dregg2.Exec.TurnAdmission

/-!
# Argus — the TURN-WRAPPER (the asymmetric prologue/epilogue over the effect body)

`Stmt.lean` gives the Argus effect-BODY: a reified state transformer `RecStmt` whose `interp`
*is* the verified executor and whose `compile` *is* the circuit. The body is all-or-nothing.

But a real turn is **not** `seq` of effects. `execute.rs` wraps the credential-gated call-forest in
an *asymmetric* prologue/epilogue, and the abstract spec must encode that faithfully:

  * **ADMISSION GATES** (before anything runs): empty-forest, expiration, agent-live, NONCE-match
    (anti-replay), fee-coverage, freeze-set, receipt-chain binding, silo budget. Modelled by
    `Dregg2.Exec.Admission.admissible` (the eleven `execute.rs:54-177` gates, `&&`-folded,
    fail-closed) — REUSED here verbatim, not reinvented.
  * **PROLOGUE** (commits UNCONDITIONALLY — NEVER rolled back even if the body fails): fee debit +
    **NONCE TICK** + budget debit. Modelled by `Admission.commitPrologue` (`execute.rs:182-195`
    "PHASE 1: Commit fee + nonce (NEVER rolled back)"). The **nonce tick lives HERE**, which resolves
    the per-effect nonce divergence: a per-effect Argus circuit/executor (`Stmt.interp`) FREEZES the
    nonce (`RecStmt` has no nonce constructor), and the turn ticks it ONCE in the prologue.
  * **BODY**: the credential-gated call-forest (here, an Argus `RecStmt` lifted to the chained
    state). All-or-nothing — on any failure the BODY rolls back but the prologue PERSISTS.
  * **EPILOGUE** (only on body commit): fee DISTRIBUTION — proposer 50% / treasury 30% / burn ~20%
    (`Admission.distributeFee`, `execute.rs::distribute_fee_shares`). So conservation is
    **modulo-burn**: the fee-triple changes by `−feeBurned`, NOT by `0`.

The headline of this wrapper is the **THREE-WAY OUTCOME** (`TurnOutcome`), which fuses the
status with the state. A 2-way `ok`/`none` is the bug `boundary-P1 bug 2` (cf.
`TurnAdmission.TurnStatus`): it collapses `prologueCommittedBodyFailed` (fee gone + nonce ticked,
body reverted, turn NOT accepted) into the accepted `bodyCommitted`, taking a forged-credential
turn's word that its body succeeded. `TurnOutcome` keeps the three states distinct and CARRIES the
post-state in each non-trivial constructor.

This file OWNS only the Argus-namespace wrapper; the prologue/epilogue mechanism and its A2/replay
laws live in `Dregg2.Exec.Admission` and are REUSED (cited at each step), not duplicated.
-/

namespace Dregg2.Circuit.Argus

open Dregg2.Exec (balOf)
open Dregg2.Exec.EffectTransfer (nonceOf)
open Dregg2.Exec.Admission
  (AdmCtx TurnHdr admissible commitPrologue distributeFee feeBurned feeTriSum
   proposerShare treasuryShare
   admissible_rejects_replay admissible_nonceMatch storedNonce
   commitPrologue_nonce commitPrologue_balance commitPrologue_frame
   distributeFee_frame creditCell_balance creditCell_frame creditOpt)

/-! ## §1 — Lifting the Argus body to the chained state.

`Stmt.interp` is the body semantics on `RecordKernelState`. The prologue/epilogue mechanism lives on
`RecChainedState` (`{ kernel, log }`) because it edits the agent cell's balance/nonce and the fee
cells. `interpChained` lifts the body onto the chained state, editing only the `kernel` (the body
does not touch the receipt log — the prologue's commit, not the body, is what the chain records).

Because `interpChained` is `Stmt.interp` post-composed with a `kernel`-update, the cornerstone
`interp_transferStmt_eq_recKExec` lifts to it (`interpChained_transferStmt`): the lifted body of the
transfer term IS the verified `recKExec` on the kernel, by construction. -/

/-- The Argus effect body lifted to the chained state: run `interp` on the kernel, keep the log. -/
def interpChained (st : RecStmt) (s : Dregg2.Exec.RecChainedState) :
    Option Dregg2.Exec.RecChainedState :=
  (interp st s.kernel).map (fun k => { s with kernel := k })

/-- `interpChained` commits IFF `interp` commits on the kernel; the post-kernel is `interp`'s. -/
theorem interpChained_some_iff (st : RecStmt) (s s' : Dregg2.Exec.RecChainedState) :
    interpChained st s = some s'
      ↔ (interp st s.kernel = some s'.kernel ∧ s'.log = s.log) := by
  unfold interpChained
  constructor
  · intro h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨k, hk, hs'⟩ := h
    subst hs'
    exact ⟨hk, rfl⟩
  · intro ⟨hk, hlog⟩
    rw [hk]
    simp only [Option.map_some]
    -- `s'` is `{ s with kernel := s'.kernel }` since only the kernel moved and the log is `s.log`.
    cases s; cases s'
    simp_all

/-- The lifted body of the **transfer term** IS the verified executor `recKExec` on the kernel — the
cornerstone (`Stmt.interp_transferStmt_eq_recKExec`) survives the lift to the chained state. The body
the wrapper runs is, by construction, the meaning of the term. -/
theorem interpChained_transferStmt (turn : Dregg2.Exec.Turn) (s : Dregg2.Exec.RecChainedState) :
    interpChained (transferStmt turn) s
      = (Dregg2.Exec.recKExec s.kernel turn).map (fun k => { s with kernel := k }) := by
  unfold interpChained
  rw [interp_transferStmt_eq_recKExec]

/-! ## §2 — `TurnOutcome`: the THREE-WAY result (status FUSED with state).

The faithful turn result. A 2-way `ok`/`none` is WRONG (`boundary-P1 bug 2`): `bodyCommitted` (the
turn is accepted, fee distributed) and `prologueCommittedBodyFailed` (the fee/nonce prologue survives
but the BODY reverted — anti-spam, NOT an accepted turn) are DIFFERENT outcomes that a 2-way result
conflates. We keep them distinct and carry the post-state in each.

This is the state-carrying sibling of `Dregg2.Exec.TurnAdmission.TurnStatus` (a bare enum paired with
a separate `Option`); fusing the state in removes the "which `Option` goes with which tag" seam. -/

/-- **The three-way turn outcome.** `rejected`: admission failed, NO state change. `prologueCommitted
BodyFailed s`: admission passed, the prologue (fee debit + nonce tick) committed to `s` and is NEVER
rolled back, but the BODY failed (the turn is NOT accepted — anti-spam only). `bodyCommitted s`:
admission passed AND the body committed; `s` is the accepted post-state (fee distributed). -/
inductive TurnOutcome where
  /-- Admission rejected the turn: no state edit, no fee charged. -/
  | rejected
  /-- Admission passed; the prologue (fee + nonce tick) committed to this state and is never rolled
  back, but the body FAILED. The turn is REJECTED (anti-spam), not accepted. -/
  | prologueCommittedBodyFailed (s : Dregg2.Exec.RecChainedState)
  /-- Admission passed AND the body committed: the turn is ACCEPTED, this is the post-state. -/
  | bodyCommitted (s : Dregg2.Exec.RecChainedState)

/-- The state an outcome commits to (`none` only for `rejected`). The projection a node reads to
apply the result; `accepted?` says whether to treat it as an accepted turn. -/
def TurnOutcome.state? : TurnOutcome → Option Dregg2.Exec.RecChainedState
  | .rejected                        => none
  | .prologueCommittedBodyFailed s   => some s
  | .bodyCommitted s                 => some s

/-- Whether the outcome is an ACCEPTED turn. ONLY `bodyCommitted` — a `prologueCommittedBodyFailed`
charged the fee but is NOT accepted (the boundary must not be tricked by a forged-credential body). -/
def TurnOutcome.accepted? : TurnOutcome → Bool
  | .bodyCommitted _ => true
  | _                => false

/-! ## §3 — `runTurn`: admission ∘ committed-prologue ∘ rollback-able Argus body ∘ fee-epilogue.

The full `execute.rs` shape over an Argus `RecStmt` body, producing the three-way `TurnOutcome`. The
prologue commits the fee + NONCE TICK + budget (the budget gate is in `admissible`); the body is the
lifted Argus term (rollback-able); on body commit the epilogue distributes the fee. -/

/-- **The Argus turn wrapper.** `admissible` (the eleven gates) → on pass commit the prologue (fee
debit + nonce tick, never rolled back) → run the Argus body `interpChained st` on the post-prologue
state → on body `some s'` distribute the fee and yield `bodyCommitted (distributeFee … s')`; on body
`none` yield `prologueCommittedBodyFailed (commitPrologue …)` (prologue survives); on admission fail
yield `rejected`. -/
def runTurn (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : Dregg2.Exec.RecChainedState) :
    TurnOutcome :=
  if admissible ctx h s = true then
    let s₁ := commitPrologue s h.agent h.fee        -- PROLOGUE: fee debit + NONCE TICK (never rolled back)
    match interpChained st s₁ with                  -- BODY: the gated Argus term (rollback-able)
    | some s' => TurnOutcome.bodyCommitted (distributeFee ctx s' h.fee)   -- EPILOGUE: fee distribution
    | none    => TurnOutcome.prologueCommittedBodyFailed s₁               -- body reverted; prologue persists
  else
    TurnOutcome.rejected

/-! ### §3a — The outcome characterisation (the wrapper does exactly what it says). -/

/-- An inadmissible turn is `rejected` with NO state edit (the agent is never charged for a turn that
fails a pre-flight gate). -/
theorem runTurn_rejected (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : Dregg2.Exec.RecChainedState)
    (hbad : admissible ctx h s = false) : runTurn ctx h st s = TurnOutcome.rejected := by
  simp only [runTurn, hbad, if_neg (by simp : ¬ (false = true))]

/-- On admission pass + a FAILING body, the outcome is `prologueCommittedBodyFailed (commitPrologue
…)` — the never-rolled-back prologue state. -/
theorem runTurn_body_failed (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : Dregg2.Exec.RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = none) :
    runTurn ctx h st s = TurnOutcome.prologueCommittedBodyFailed (commitPrologue s h.agent h.fee) := by
  simp only [runTurn, if_pos hadm, hbody]

/-- On admission pass + a COMMITTING body, the outcome is `bodyCommitted (distributeFee … s')` — the
body's post-state with the fee distributed (proposer +fee/2, treasury +fee*3/10, residue burned). -/
theorem runTurn_body_committed (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : Dregg2.Exec.RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = some s') :
    runTurn ctx h st s = TurnOutcome.bodyCommitted (distributeFee ctx s' h.fee) := by
  simp only [runTurn, if_pos hadm, hbody]

/-- **`accepted?` IFF the body committed.** The turn is ACCEPTED exactly when admission passed AND the
Argus body returned `some` — a turn whose body FAILS (forged credential, violated guard, double-spend)
is NEVER accepted. The state-carrying analog of `TurnStatus.runTurnStatus_bodyCommitted_iff`. -/
theorem runTurn_accepted_iff (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : Dregg2.Exec.RecChainedState) :
    (runTurn ctx h st s).accepted? = true
      ↔ admissible ctx h s = true ∧ (interpChained st (commitPrologue s h.agent h.fee)).isSome := by
  unfold runTurn
  by_cases hadm : admissible ctx h s = true
  · simp only [hadm, if_true, true_and]
    cases interpChained st (commitPrologue s h.agent h.fee) <;>
      simp [TurnOutcome.accepted?]
  · simp only [if_neg hadm]
    constructor
    · intro h'; exact absurd h' (by simp [TurnOutcome.accepted?])
    · intro ⟨hc, _⟩; exact absurd hc hadm

/-! ## §4 — KEYSTONE (a): PROLOGUE PERSISTENCE on a failed body.

The asymmetry is the point: on `prologueCommittedBodyFailed`, the fee IS debited and the nonce IS
ticked — the prologue is **not** rolled back even though the body reverted. This is the anti-DoS
commit (`Admission.prologue_survives_failed_body`), surfaced through the Argus `TurnOutcome`. -/

/-- **PROLOGUE PERSISTENCE (a).** On an admissible turn whose Argus body FAILS, `runTurn` yields a
`prologueCommittedBodyFailed s_p` whose state `s_p` has the agent's balance dropped by EXACTLY the fee
and the nonce ticked by EXACTLY one. The committed prologue survives the body's rollback (the agent
cannot run an expensive-but-failing turn for free). REUSES `Admission.commitPrologue_balance/nonce`. -/
theorem prologue_persists_on_body_failure (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s : Dregg2.Exec.RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = none) :
    ∃ sp, runTurn ctx h st s = TurnOutcome.prologueCommittedBodyFailed sp ∧
      balOf (sp.kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee ∧
      nonceOf (sp.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  refine ⟨commitPrologue s h.agent h.fee, runTurn_body_failed ctx h st s hadm hbody, ?_, ?_⟩
  · exact commitPrologue_balance s h.agent h.fee
  · exact commitPrologue_nonce s h.agent h.fee

/-! ## §5 — KEYSTONE (b): ANTI-REPLAY — a ticked nonce kills the same-nonce turn.

The nonce tick lives in the PROLOGUE, so it commits on BOTH non-rejected outcomes (failed body OR
committed body). In either case, the post-state's stored nonce advanced past the header's nonce, so
the SAME header is no longer admissible (`NonceMatch` fails). A turn closes its own replay window. -/

/-- The agent's stored nonce after the prologue advanced by exactly one (relative to `s`); so a header
whose `nonce` matched `s` no longer matches the post-prologue state. REUSES `commitPrologue_nonce`. -/
private theorem storedNonce_after_prologue (s : Dregg2.Exec.RecChainedState) (agent : Dregg2.Exec.CellId)
    (fee : Int) :
    storedNonce (commitPrologue s agent fee) agent = storedNonce s agent + 1 := by
  unfold storedNonce
  exact commitPrologue_nonce s agent fee

/-- A header admissible at `s` whose nonce thereby matched `storedNonce s`, is INADMISSIBLE at the
post-prologue state (the nonce ticked). The replay gate (`admissible_rejects_replay`) fires. -/
private theorem prologue_closes_replay (ctx : AdmCtx) (h : TurnHdr) (s : Dregg2.Exec.RecChainedState)
    (hadm : admissible ctx h s = true) :
    admissible ctx h (commitPrologue s h.agent h.fee) = false := by
  apply admissible_rejects_replay
  have hmatch : h.nonce = storedNonce s h.agent := admissible_nonceMatch ctx h s hadm
  rw [storedNonce_after_prologue, hmatch]; omega

/-- **ANTI-REPLAY (b) — failed body.** After a turn whose body FAILED ticks the nonce (in the surviving
prologue), the SAME header is no longer admissible against the committed state. The failed turn closes
its own replay window. -/
theorem replay_closed_after_body_failure (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s : Dregg2.Exec.RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = none) :
    ∀ sp, runTurn ctx h st s = TurnOutcome.prologueCommittedBodyFailed sp →
      admissible ctx h sp = false := by
  intro sp hrun
  rw [runTurn_body_failed ctx h st s hadm hbody] at hrun
  -- the outcome's carried state IS `commitPrologue s h.agent h.fee`.
  injection hrun with hsp
  subst hsp
  exact prologue_closes_replay ctx h s hadm

/-- **ANTI-REPLAY (b) — committed body.** The nonce tick lives in the PROLOGUE, so it also bites on a
COMMITTED turn: the same header is no longer admissible against the accepted post-state. This needs the
body to leave the AGENT'S nonce alone (`hbodyNonce`) — the honest, true condition, since the Argus
effect body moves balances/cells and the nonce is the prologue's exclusive concern (`RecStmt` has no
nonce constructor). The fee epilogue (`distributeFee`) touches only {proposer, treasury}, never the
agent (`distributeFee_frame`), so the ticked nonce is preserved into the accepted state. -/
theorem replay_closed_after_body_commit (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : Dregg2.Exec.RecChainedState) (p t : Dregg2.Exec.CellId)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t)
    -- the body left the agent's nonce at its post-prologue value (the body is metadata-nonce-neutral
    -- on the agent — balances/cells move, the nonce does not):
    (hbodyNonce : nonceOf (s'.kernel.cell h.agent)
                    = nonceOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent)) :
    ∀ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so → admissible ctx h so = false := by
  intro so hrun
  rw [runTurn_body_committed ctx h st s s' hadm hbody] at hrun
  injection hrun with hsf; subst hsf
  apply admissible_rejects_replay
  have hmatch : h.nonce = storedNonce s h.agent := admissible_nonceMatch ctx h s hadm
  -- distributeFee frames out the agent cell; then the body-neutrality + prologue tick give +1.
  have hframe : (distributeFee ctx s' h.fee).kernel.cell h.agent = s'.kernel.cell h.agent :=
    distributeFee_frame ctx s' h.fee p t h.agent hp ht hap hat
  have hgoal : storedNonce (distributeFee ctx s' h.fee) h.agent = storedNonce s h.agent + 1 := by
    unfold storedNonce
    rw [hframe, hbodyNonce, commitPrologue_nonce]
  rw [hgoal, hmatch]; omega

/-! ## §6 — LEGACY-SCALAR corollary (c): CONSERVATION-MODULO-BURN on a committed body.

⚠ W1 RETIREMENT: this is no longer the fee keystone. The W1 value unification (§6' below) lands
the fee legs on the PER-ASSET ledger with the burn residue credited to a burn-pot CELL, making the
fee QUADRUPLE {agent, proposer, treasury, burn-pot} EXACTLY conserved (`runTurnV_quadruple_exact`,
KEYSTONE (c′)) — the modulo dies. The theorem below stays as the LEGACY-SCALAR corollary describing
the deployed `runTurn` wrapper until the W1 VK rotation swaps the executor onto `runTurnV`.

The epilogue distributes the fee — proposer 50%, treasury 30%, the residue BURNED. So the fee-relevant
triple {agent, proposer, treasury} does NOT come back to its pre-turn total: it drops by EXACTLY
`feeBurned fee` — NOT `0` (that would be silent fee creation) and NOT the whole `fee` (that would be
silent loss; the proposer/treasury are credited). This is `Admission.fee_conservation_modulo
_burn` surfaced through the Argus `bodyCommitted` outcome. The body is assumed triple-neutral on the
three fee cells (the usual case: an Argus effect whose body does not itself move balances among the
fee cells), exactly as `TurnAdmission.runGatedForestTurn_conserves_modulo_burn`. -/

/-- **CONSERVATION-MODULO-BURN (c).** On an admissible turn whose Argus body commits over THREE DISTINCT
fee cells, `runTurn` yields `bodyCommitted so` whose fee-triple total over {agent, p, t} equals the
PRE-TURN total MINUS exactly `feeBurned h.fee`. The proposer/treasury are credited (`fee − feeBurned`
total) on top of the prologue's `−fee`, so net the triple loses exactly the burn — conserved modulo the
protocol sink, with NO silent loss and NO silent creation. The body is assumed to leave the three fee
cells at their post-prologue balances. -/
theorem conservation_modulo_burn_on_commit (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : Dregg2.Exec.RecChainedState) (p t : Dregg2.Exec.CellId)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t) (hpt : p ≠ t)
    -- the body left the three fee cells' BALANCES at their post-prologue values:
    (hbA : balOf (s'.kernel.cell h.agent) = balOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent))
    (hbP : balOf (s'.kernel.cell p) = balOf ((commitPrologue s h.agent h.fee).kernel.cell p))
    (hbT : balOf (s'.kernel.cell t) = balOf ((commitPrologue s h.agent h.fee).kernel.cell t)) :
    ∃ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so ∧
      feeTriSum so h.agent p t = feeTriSum s h.agent p t - feeBurned h.fee := by
  refine ⟨distributeFee ctx s' h.fee, runTurn_body_committed ctx h st s s' hadm hbody, ?_⟩
  -- distributeFee credits p (+fee/2) and t (+fee*3/10); the agent cell is framed out.
  have hagent : balOf ((distributeFee ctx s' h.fee).kernel.cell h.agent) = balOf (s'.kernel.cell h.agent) := by
    rw [distributeFee_frame ctx s' h.fee p t h.agent hp ht hap hat]
  have hprop : balOf ((distributeFee ctx s' h.fee).kernel.cell p)
      = balOf (s'.kernel.cell p) + proposerShare h.fee := by
    simp only [distributeFee, creditOpt, hp, ht]
    rw [creditCell_frame _ _ _ _ hpt, creditCell_balance]
  have htreas : balOf ((distributeFee ctx s' h.fee).kernel.cell t)
      = balOf (s'.kernel.cell t) + treasuryShare h.fee := by
    simp only [distributeFee, creditOpt, hp, ht]
    rw [creditCell_balance, creditCell_frame _ _ _ _ (Ne.symm hpt)]
  -- the prologue's effect on the triple cells (agent −fee, p/t untouched):
  have hpA : balOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee :=
    commitPrologue_balance s h.agent h.fee
  have hpP : balOf ((commitPrologue s h.agent h.fee).kernel.cell p) = balOf (s.kernel.cell p) :=
    congrArg balOf (commitPrologue_frame s h.agent h.fee p (Ne.symm hap))
  have hpT : balOf ((commitPrologue s h.agent h.fee).kernel.cell t) = balOf (s.kernel.cell t) :=
    congrArg balOf (commitPrologue_frame s h.agent h.fee t (Ne.symm hat))
  simp only [feeTriSum, hagent, hprop, htreas, hbA, hbP, hbT, hpA, hpP, hpT, feeBurned]; ring

/-! ## §7 — Axiom-hygiene tripwires (the keystones are `{propext, Classical.choice, Quot.sound}`-clean). -/

#assert_axioms interpChained_some_iff
#assert_axioms interpChained_transferStmt
#assert_axioms runTurn_rejected
#assert_axioms runTurn_body_failed
#assert_axioms runTurn_body_committed
#assert_axioms runTurn_accepted_iff
#assert_axioms prologue_persists_on_body_failure       -- KEYSTONE (a)
#assert_axioms replay_closed_after_body_failure        -- KEYSTONE (b), failed-body
#assert_axioms replay_closed_after_body_commit         -- KEYSTONE (b), committed-body
#assert_axioms conservation_modulo_burn_on_commit      -- KEYSTONE (c)

/-! ## §8 — NON-VACUITY (`#eval`/`#guard`): all THREE outcomes are exhibited.

We exhibit a concrete turn for each of the three outcomes — `rejected`, `prologueCommittedBodyFailed`,
`bodyCommitted` — so the three-way is not vacuous: each branch is reachable, the prologue
persists on the failing body, and the committed turn conserves modulo burn (drop = the burn,
not `0`, not the whole fee). Agent cell 7 (balance 100, nonce 3), proposer 20, treasury 30. -/

/-- Pre-state: agent 7 (bal 100, nonce 3), proposer 20 (bal 0), treasury 30 (bal 0) — three distinct
cells, all live accounts. -/
def es0 : Dregg2.Exec.RecChainedState :=
  { kernel := { accounts := {7, 20, 30}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 100), ("nonce", .int 3)]
                                 else .record [("balance", .int 0)] },
    log := [] }

/-- Host context: clock 50, nothing frozen, head `some 42`, budget 1000, fee → proposer 20 + treasury 30. -/
def ec0 : AdmCtx :=
  { now := 50, frozen := [], storedHead := some 42, budget := 1000,
    proposer := some 20, treasury := some 30 }

/-- Well-formed header: agent 7, nonce 3 (matches), fee 10, valid until 100, prevReceipt 42 (matches
head), write-set {7}, non-empty forest. -/
def eh0 : TurnHdr :=
  { agent := 7, nonce := 3, fee := 10, validUntil := some 100, prevReceipt := some 42,
    writeSet := [7], forestNonEmpty := true }

/-- A body that ALWAYS commits without touching the fee cells: a `skip` (the identity Argus term). -/
def bodyOK : RecStmt := RecStmt.skip

/-- A body that ALWAYS fails: a `guard` whose predicate is `false` (an inadmissible effect). -/
def bodyFail : RecStmt := RecStmt.guard (fun _ => false)

-- OUTCOME 1 — `rejected`: a replay turn (nonce 99 ≠ stored 3) is rejected even with a committing body.
#guard (match runTurn ec0 { eh0 with nonce := 99 } bodyOK es0 with
        | .rejected => true | _ => false)
-- ...and `rejected` carries NO state, and is NOT accepted:
#guard ((runTurn ec0 { eh0 with nonce := 99 } bodyOK es0).state?.isNone)
#guard ((runTurn ec0 { eh0 with nonce := 99 } bodyOK es0).accepted? == false)

-- OUTCOME 2 — `prologueCommittedBodyFailed`: admissible turn, FAILING body. Prologue persists.
#guard (match runTurn ec0 eh0 bodyFail es0 with
        | .prologueCommittedBodyFailed _ => true | _ => false)
-- The prologue committed: agent 7 balance 100 → 90, nonce 3 → 4 (NEVER rolled back):
#guard ((runTurn ec0 eh0 bodyFail es0).state?.map
        (fun sp => (balOf (sp.kernel.cell 7), nonceOf (sp.kernel.cell 7)))) == some (90, 4)
-- ...but it is NOT an accepted turn (anti-spam fee charged, body reverted):
#guard ((runTurn ec0 eh0 bodyFail es0).accepted? == false)
-- ...and the fee was NOT distributed on a failed body (proposer 20 / treasury 30 stay 0):
#guard ((runTurn ec0 eh0 bodyFail es0).state?.map
        (fun sp => (balOf (sp.kernel.cell 20), balOf (sp.kernel.cell 30)))) == some (0, 0)
-- ...replay is closed: the SAME header is no longer admissible against the prologue state:
#guard ((runTurn ec0 eh0 bodyFail es0).state?.map (fun sp => admissible ec0 eh0 sp)) == some false

-- OUTCOME 3 — `bodyCommitted`: admissible turn, COMMITTING body. Fee distributed, accepted.
#guard (match runTurn ec0 eh0 bodyOK es0 with
        | .bodyCommitted _ => true | _ => false)
-- It IS accepted:
#guard ((runTurn ec0 eh0 bodyOK es0).accepted? == true)
-- The agent paid the full fee (100 → 90), nonce ticked (3 → 4):
#guard ((runTurn ec0 eh0 bodyOK es0).state?.map
        (fun sf => (balOf (sf.kernel.cell 7), nonceOf (sf.kernel.cell 7)))) == some (90, 4)
-- The epilogue FIRED: proposer 20 gained 5 (50%), treasury 30 gained 3 (30%) of fee 10:
#guard ((runTurn ec0 eh0 bodyOK es0).state?.map
        (fun sf => (balOf (sf.kernel.cell 20), balOf (sf.kernel.cell 30)))) == some (5, 3)
-- THE (c) TEETH: the {7,20,30} fee-triple drops by EXACTLY the burn (2), not 0, not the whole fee (10):
#guard ((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => feeTriSum sf 7 20 30)) == some 98  --  100 → 98 (−2 burn)
#guard (feeTriSum es0 7 20 30 == 100)                                                          --  before
-- TAMPER: the WRONG "fully conserved" claim (triple unchanged = 100) is FALSE — the burn is real:
#guard (((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => feeTriSum sf 7 20 30)) == some 100) == false
-- ...and the OLD broken "whole fee silently gone" (triple = 90) is ALSO FALSE — the fee distributes:
#guard (((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => feeTriSum sf 7 20 30)) == some 90) == false

-- The three outcomes are GENUINELY DIFFERENT (the three-way is not a collapsed 2-way):
#guard ((runTurn ec0 { eh0 with nonce := 99 } bodyOK es0).accepted?
        != (runTurn ec0 eh0 bodyOK es0).accepted?)                       --  rejected ≠ bodyCommitted
#guard ((runTurn ec0 eh0 bodyFail es0).accepted?
        == (runTurn ec0 { eh0 with nonce := 99 } bodyOK es0).accepted?)  --  both NOT accepted...
#guard (((runTurn ec0 eh0 bodyFail es0).state?.isSome)
        != ((runTurn ec0 { eh0 with nonce := 99 } bodyOK es0).state?.isSome))  -- ...but differ on state (fee charged vs not)

/-! ### §8b — The cornerstone survives the lift (a real transfer term as the BODY).

`interpChained_transferStmt` says the lifted body of a transfer term IS `recKExec` on the kernel. Here
we run that body INSIDE a `bodyCommitted` turn end-to-end. Agent/src cell 7 (bal 100), dst cell 8 (bal
0, a live non-fee account), proposer 20, treasury 30. Fee 10, transfer amt 5: prologue debits 7 by the
fee (100→90) and ticks the nonce (3→4), the transfer body debits 7 by 5 (90→85) and credits 8 (0→5),
the epilogue credits proposer 20 (+5) and treasury 30 (+3). All distinct, so nothing collides. -/

/-- Transfer-demo state: cells 7 (agent/src, bal 100, nonce 3), 8 (dst, bal 0), 20/30 (proposer/treasury,
bal 0) — four distinct live accounts. -/
def ts0 : Dregg2.Exec.RecChainedState :=
  { kernel := { accounts := {7, 8, 20, 30}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 100), ("nonce", .int 3)]
                                 else .record [("balance", .int 0)] },
    log := [] }

-- The transfer term run as a turn BODY: a `bodyCommitted` whose state moves BOTH balances AND ticks the
-- nonce (src 7: 100 −10 fee −5 transfer = 85; dst 8: 0 +5 = 5; nonce 3→4):
#guard (match runTurn ec0 eh0 (transferStmt { actor := 7, src := 7, dst := 8, amt := 5 }) ts0 with
        | .bodyCommitted sf =>
            (balOf (sf.kernel.cell 7), balOf (sf.kernel.cell 8), nonceOf (sf.kernel.cell 7)) == (85, 5, 4)
        | _ => false)
-- ...and the fee still distributed (proposer 20 +5, treasury 30 +3) on this committing transfer turn:
#guard (match runTurn ec0 eh0 (transferStmt { actor := 7, src := 7, dst := 8, amt := 5 }) ts0 with
        | .bodyCommitted sf => (balOf (sf.kernel.cell 20), balOf (sf.kernel.cell 30)) == (5, 3)
        | _ => false)

/-! ## §6' — W1 VALUE UNIFICATION: the fee QUADRUPLE on the PER-ASSET ledger, EXACT.

KEYSTONE (c) above (`conservation_modulo_burn_on_commit`) is the LEGACY-SCALAR fee law: the fee
moves the scalar `balance` field, and the burn residue leaves the supply — conservation MODULO the
protocol sink. The R2 probe killed both defects (`IssuerSupplyProbe §4`, E5): the burn residue is an
ordinary MOVE to a burn-pot CELL (whose program is the burn policy), and the fee legs belong on the
per-asset `bal` ledger so ONE law (`ExactConservation`) covers fees too. THIS section lands that
wrapper:

  * `commitPrologueV` — fee debit ON THE PER-ASSET LEDGER (at the designated fee asset `fa`) +
    the same NONCE TICK (never rolled back);
  * `distributeFeeV` — proposer 50% / treasury 30% / burn-pot RESIDUE, all three as per-asset
    moves: NOTHING leaves the ledger;
  * `admissibleV` — the same eight gates with FeeCoverage reading `bal agent fa` (E5 dies at
    admission too) PLUS the E6 pot-genesis gate (proposer/treasury/burn-pot must be wired —
    fail-closed, so no share can vanish off-ledger);
  * `runTurnV` — the value-unified turn wrapper. ONE deliberate divergence from the scalar
    `runTurn`: the anti-spam fee of a FAILED body is also DISTRIBUTED (not parked) — exactness
    holds on EVERY non-rejected outcome, and the fee is proposer/treasury/pot revenue, never
    destruction;
  * KEYSTONE (c′): the fee quadruple {agent, proposer, treasury, burn-pot} is EXACTLY conserved
    on both non-rejected outcomes (`runTurnV_quadruple_exact`, `…_on_body_failure`) — Σδ = 0, no
    modulo — and the whole law rides the turn (`runTurnV_preserves_exact`): a conserved pre-state
    stays conserved through prologue ∘ body ∘ epilogue.

`conservation_modulo_burn_on_commit` RETIRES as keystone: it remains above as the legacy-scalar
corollary describing the deployed wrapper until the W1 VK rotation swaps the executor onto
`runTurnV`. -/

section ValueUnify

open Dregg2.Exec (CellId AssetId RecChainedState recBalCreditCell recBalCreditCell_recTotalAsset
  recTotalAsset ExactConservation)
open Dregg2.Exec.Admission (isFrozen admissionClock)

/-- Credit `amt` of asset `fa` to cell `c` on the PER-ASSET ledger (`recBalCreditCell`); negative
`amt` is the debit. Touches ONLY `kernel.bal` — cells/log/accounts/escrows are untouched. -/
def creditBalV (s : RecChainedState) (c : CellId) (fa : AssetId) (amt : Int) : RecChainedState :=
  { s with kernel := { s.kernel with bal := recBalCreditCell s.kernel.bal c fa amt } }

/-- Optionally credit a recipient on the per-asset ledger (`none` ⇒ no edit; the exact wrapper's
admission gate refuses unwired pots, so `none` is unreachable on the committed path). -/
def creditBalOptV (s : RecChainedState) (rcpt : Option CellId) (fa : AssetId) (amt : Int) :
    RecChainedState :=
  match rcpt with
  | some c => creditBalV s c fa amt
  | none => s

/-- **The W1 prologue**: NONCE TICK (the same `commitPrologue` mechanism, fee `0` so the scalar
balance is untouched) + the fee DEBIT on the per-asset ledger at the fee asset `fa`. Never rolled
back. -/
def commitPrologueV (s : RecChainedState) (agent : CellId) (fa : AssetId) (fee : Int) :
    RecChainedState :=
  creditBalV (commitPrologue s agent 0) agent fa (-fee)

/-- **The W1 epilogue**: distribute the fee as per-asset moves — proposer `fee/2`, treasury
`fee*3/10`, and the RESIDUE to the burn-pot cell. Nothing leaves the ledger. -/
def distributeFeeV (ctx : AdmCtx) (s : RecChainedState) (fa : AssetId) (fee : Int) :
    RecChainedState :=
  creditBalOptV
    (creditBalOptV (creditBalOptV s ctx.proposer fa (proposerShare fee))
      ctx.treasury fa (treasuryShare fee))
    ctx.burnPot fa (feeBurned fee)

/-- **The W1 admission predicate**: the eight `admissible` gates with FeeCoverage reading the
PER-ASSET ledger (`bal agent fa` — E5 dies at admission), plus the E6 pot-genesis gate: the fee
quadruple's pot cells must be WIRED, fail-closed, so no fee share can vanish off-ledger. -/
def admissibleV (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) (fa : AssetId) : Bool :=
  -- 1. EmptyForest
  h.forestNonEmpty &&
  -- 2. AgentLive
  decide (h.agent ∈ s.kernel.accounts) &&
  -- 3. Expiry
  (match h.validUntil with | none => true | some vu => decide (admissionClock ctx ≤ vu)) &&
  -- 4. NonceMatch
  decide (h.nonce = storedNonce s h.agent) &&
  -- 5. FeeCoverage — on the PER-ASSET ledger (E5)
  decide (0 ≤ h.fee) && decide (h.fee ≤ s.kernel.bal h.agent fa) &&
  -- 6. NotFrozen (agent + write-set)
  (!isFrozen ctx h.agent) && (h.writeSet.all (fun c => !isFrozen ctx c)) &&
  -- 7. ChainHead
  decide (h.prevReceipt = ctx.storedHead) &&
  -- 8. Budget
  decide (h.fee ≤ (ctx.budget : Int)) &&
  -- 9. POT GENESIS (E6): the quadruple must exist — no share may vanish off-ledger
  ctx.proposer.isSome && ctx.treasury.isSome && ctx.burnPot.isSome

/-- **`runTurnV` — the value-unified turn wrapper.** `admissibleV` → per-asset prologue (fee debit
at `fa` + nonce tick, never rolled back) → the Argus body → fee distribution to the quadruple on
BOTH non-rejected outcomes (a failed body's anti-spam fee is revenue, not destruction — exactness
everywhere). -/
def runTurnV (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : RecChainedState) (fa : AssetId) :
    TurnOutcome :=
  if admissibleV ctx h s fa = true then
    let s₁ := commitPrologueV s h.agent fa h.fee
    match interpChained st s₁ with
    | some s' => TurnOutcome.bodyCommitted (distributeFeeV ctx s' fa h.fee)
    | none    => TurnOutcome.prologueCommittedBodyFailed (distributeFeeV ctx s₁ fa h.fee)
  else
    TurnOutcome.rejected

/-! ### §6'a — the per-asset move's pointwise/aggregate laws. -/

/-- The credited cell's column moves by exactly `amt`. -/
theorem creditBalV_bal_self (s : RecChainedState) (c : CellId) (fa : AssetId) (amt : Int) :
    (creditBalV s c fa amt).kernel.bal c fa = s.kernel.bal c fa + amt := by
  show recBalCreditCell s.kernel.bal c fa amt c fa = _
  unfold recBalCreditCell
  rw [if_pos ⟨rfl, rfl⟩]

/-- Every other (cell, asset) entry is untouched. -/
theorem creditBalV_bal_frame (s : RecChainedState) (c : CellId) (fa : AssetId) (amt : Int)
    (c' : CellId) (b : AssetId) (h : ¬ (c' = c ∧ b = fa)) :
    (creditBalV s c fa amt).kernel.bal c' b = s.kernel.bal c' b := by
  show recBalCreditCell s.kernel.bal c fa amt c' b = _
  unfold recBalCreditCell
  rw [if_neg h]

/-- The aggregate law: a live-cell credit moves the per-asset measure by `amt` at the
credited asset only (instantiates `recBalCreditCell_recTotalAsset`). -/
theorem creditBalV_measure (s : RecChainedState) (c : CellId) (fa : AssetId) (amt : Int)
    (hc : c ∈ s.kernel.accounts) (b : AssetId) :
    recTotalAsset (creditBalV s c fa amt).kernel b
      = recTotalAsset s.kernel b + (if b = fa then amt else 0) := by
  unfold Dregg2.Exec.recTotalAsset
  show (∑ x ∈ s.kernel.accounts, recBalCreditCell s.kernel.bal c fa amt x b) = _
  exact recBalCreditCell_recTotalAsset s.kernel.accounts s.kernel.bal c fa amt hc b

/-- The W1 prologue ticks the nonce by exactly one (the anti-replay tick — `creditBalV` never
touches the cell record, `commitPrologue` at fee `0` never touches the balance). -/
theorem commitPrologueV_nonce (s : RecChainedState) (agent : CellId) (fa : AssetId) (fee : Int) :
    nonceOf ((commitPrologueV s agent fa fee).kernel.cell agent)
      = nonceOf (s.kernel.cell agent) + 1 := by
  show nonceOf ((commitPrologue s agent 0).kernel.cell agent) = _
  exact commitPrologue_nonce s agent 0

/-- The W1 prologue debits the agent's fee-asset column by exactly the fee. -/
theorem commitPrologueV_bal_agent (s : RecChainedState) (agent : CellId) (fa : AssetId)
    (fee : Int) :
    (commitPrologueV s agent fa fee).kernel.bal agent fa = s.kernel.bal agent fa - fee := by
  unfold commitPrologueV
  rw [creditBalV_bal_self]
  show s.kernel.bal agent fa + (-fee) = _
  ring

/-- The W1 prologue leaves every other (cell, asset) ledger entry untouched. -/
theorem commitPrologueV_bal_frame (s : RecChainedState) (agent : CellId) (fa : AssetId)
    (fee : Int) (c' : CellId) (b : AssetId) (h : ¬ (c' = agent ∧ b = fa)) :
    (commitPrologueV s agent fa fee).kernel.bal c' b = s.kernel.bal c' b := by
  unfold commitPrologueV
  rw [creditBalV_bal_frame _ _ _ _ _ _ h]
  rfl

/-- The W1 prologue's aggregate law: the combined measure drops by the fee at the fee asset only. -/
theorem commitPrologueV_measure (s : RecChainedState) (agent : CellId) (fa : AssetId) (fee : Int)
    (hagent : agent ∈ s.kernel.accounts) (b : AssetId) :
    recTotalAsset (commitPrologueV s agent fa fee).kernel b
      = recTotalAsset s.kernel b - (if b = fa then fee else 0) := by
  unfold commitPrologueV
  rw [creditBalV_measure _ _ _ _ (show agent ∈ (commitPrologue s agent 0).kernel.accounts
        from hagent) b]
  have hpro : recTotalAsset (commitPrologue s agent 0).kernel b
      = recTotalAsset s.kernel b := rfl
  rw [hpro]
  by_cases hb : b = fa
  · rw [if_pos hb, if_pos hb]; ring
  · rw [if_neg hb, if_neg hb]; ring

/-- The W1 epilogue's aggregate law: with the quadruple's pot cells wired and live, distributing
the fee RAISES the combined measure by exactly the fee at the fee asset (the three shares sum to
the whole — `proposerShare + treasuryShare + feeBurned = fee`). -/
theorem distributeFeeV_measure (ctx : AdmCtx) (s : RecChainedState) (fa : AssetId) (fee : Int)
    (p t pot : CellId)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t) (hpot : ctx.burnPot = some pot)
    (hpm : p ∈ s.kernel.accounts) (htm : t ∈ s.kernel.accounts)
    (hpotm : pot ∈ s.kernel.accounts) (b : AssetId) :
    recTotalAsset (distributeFeeV ctx s fa fee).kernel b
      = recTotalAsset s.kernel b + (if b = fa then fee else 0) := by
  unfold distributeFeeV creditBalOptV
  rw [hp, ht, hpot]
  rw [creditBalV_measure _ _ _ _ (show pot ∈ (creditBalV (creditBalV s p fa (proposerShare fee))
        t fa (treasuryShare fee)).kernel.accounts from hpotm) b,
      creditBalV_measure _ _ _ _ (show t ∈ (creditBalV s p fa
        (proposerShare fee)).kernel.accounts from htm) b,
      creditBalV_measure _ _ _ _ hpm b]
  unfold feeBurned
  by_cases hb : b = fa
  · rw [if_pos hb, if_pos hb, if_pos hb, if_pos hb]; ring
  · rw [if_neg hb, if_neg hb, if_neg hb, if_neg hb]; ring

/-! ### §6'b — admission extraction + anti-replay. -/

/-- Extract the load-bearing gates from a passing `admissibleV`. -/
theorem admissibleV_extract {ctx : AdmCtx} {h : TurnHdr} {s : RecChainedState} {fa : AssetId}
    (hadm : admissibleV ctx h s fa = true) :
    h.agent ∈ s.kernel.accounts ∧ h.nonce = storedNonce s h.agent
      ∧ 0 ≤ h.fee ∧ h.fee ≤ s.kernel.bal h.agent fa
      ∧ ctx.proposer.isSome = true ∧ ctx.treasury.isSome = true
      ∧ ctx.burnPot.isSome = true := by
  unfold admissibleV at hadm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hadm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, _⟩, h4⟩, h5⟩, h6⟩, _⟩, _⟩, _⟩, _⟩, h11⟩, h12⟩, h13⟩ := hadm
  exact ⟨h2, h4, h5, h6, h11, h12, h13⟩

/-- A nonce mismatch is inadmissible (the replay gate, V-side). -/
theorem admissibleV_rejects_replay {ctx : AdmCtx} {h : TurnHdr} {s : RecChainedState}
    {fa : AssetId} (hbad : h.nonce ≠ storedNonce s h.agent) :
    admissibleV ctx h s fa = false := by
  unfold admissibleV
  simp [hbad]

/-- **ANTI-REPLAY (V).** The W1 prologue's nonce tick closes the turn's own replay window: the
same header is inadmissible against the post-prologue state (hence against both non-rejected
outcomes' bases). -/
theorem commitPrologueV_closes_replay {ctx : AdmCtx} {h : TurnHdr} {s : RecChainedState}
    {fa : AssetId} (hadm : admissibleV ctx h s fa = true) :
    admissibleV ctx h (commitPrologueV s h.agent fa h.fee) fa = false := by
  apply admissibleV_rejects_replay
  have hmatch : h.nonce = storedNonce s h.agent := (admissibleV_extract hadm).2.1
  have htick : storedNonce (commitPrologueV s h.agent fa h.fee) h.agent
      = storedNonce s h.agent + 1 := commitPrologueV_nonce s h.agent fa h.fee
  rw [htick, hmatch]
  omega

/-! ### §6'c — outcome characterisation. -/

/-- Inadmissible ⇒ `rejected`, no state edit. -/
theorem runTurnV_rejected (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : RecChainedState)
    (fa : AssetId) (hbad : admissibleV ctx h s fa = false) :
    runTurnV ctx h st s fa = TurnOutcome.rejected := by
  simp only [runTurnV, hbad, if_neg (by simp : ¬ (false = true))]

/-- Admission + committing body ⇒ `bodyCommitted (distributeFeeV …)`. -/
theorem runTurnV_body_committed (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : RecChainedState) (fa : AssetId)
    (hadm : admissibleV ctx h s fa = true)
    (hbody : interpChained st (commitPrologueV s h.agent fa h.fee) = some s') :
    runTurnV ctx h st s fa = TurnOutcome.bodyCommitted (distributeFeeV ctx s' fa h.fee) := by
  simp only [runTurnV, if_pos hadm, hbody]

/-- Admission + failing body ⇒ `prologueCommittedBodyFailed (distributeFeeV (prologue) …)` — the
prologue persists AND the anti-spam fee is distributed (never destroyed). -/
theorem runTurnV_body_failed (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt) (s : RecChainedState)
    (fa : AssetId)
    (hadm : admissibleV ctx h s fa = true)
    (hbody : interpChained st (commitPrologueV s h.agent fa h.fee) = none) :
    runTurnV ctx h st s fa = TurnOutcome.prologueCommittedBodyFailed
      (distributeFeeV ctx (commitPrologueV s h.agent fa h.fee) fa h.fee) := by
  simp only [runTurnV, if_pos hadm, hbody]

/-! ### §6'd — KEYSTONE (c′): the fee quadruple is EXACT, and the law rides the turn. -/

/-- The fee quadruple's per-asset measure: the four fee cells' `fa` columns. -/
def feeQuadBal (s : RecChainedState) (fa : AssetId) (agent p t pot : CellId) : Int :=
  s.kernel.bal agent fa + s.kernel.bal p fa + s.kernel.bal t fa + s.kernel.bal pot fa

/-- The epilogue's pointwise effect on the four fee cells (distinct): agent untouched, proposer
`+fee/2`, treasury `+fee*3/10`, pot `+feeBurned`. -/
private theorem distributeFeeV_quad (ctx : AdmCtx) (s : RecChainedState) (fa : AssetId)
    (fee : Int) (agent p t pot : CellId)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t) (hpot : ctx.burnPot = some pot)
    (hap : agent ≠ p) (hat : agent ≠ t) (hapot : agent ≠ pot)
    (hpt : p ≠ t) (hppot : p ≠ pot) (htpot : t ≠ pot) :
    (distributeFeeV ctx s fa fee).kernel.bal agent fa = s.kernel.bal agent fa
    ∧ (distributeFeeV ctx s fa fee).kernel.bal p fa = s.kernel.bal p fa + proposerShare fee
    ∧ (distributeFeeV ctx s fa fee).kernel.bal t fa = s.kernel.bal t fa + treasuryShare fee
    ∧ (distributeFeeV ctx s fa fee).kernel.bal pot fa = s.kernel.bal pot fa + feeBurned fee := by
  unfold distributeFeeV creditBalOptV
  rw [hp, ht, hpot]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hapot he),
        creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hat he),
        creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hap he)]
  · rw [creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hppot he),
        creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hpt he),
        creditBalV_bal_self]
  · rw [creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact htpot he),
        creditBalV_bal_self,
        creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hpt he.symm)]
  · rw [creditBalV_bal_self,
        creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact htpot he.symm),
        creditBalV_bal_frame _ _ _ _ _ _ (by rintro ⟨he, -⟩; exact hppot he.symm)]

/-- **KEYSTONE (c′) — THE FEE QUADRUPLE IS EXACT (committed body).** On an admissible W1 turn
whose body commits over FOUR DISTINCT fee cells (and leaves their fee-asset balances at the
post-prologue values), the quadruple total is UNCHANGED: `Σδ = 0` exactly — the agent's `−fee` is
the proposer/treasury/pot's `+fee`, nothing leaves the ledger. The modulo dies. -/
theorem runTurnV_quadruple_exact (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : RecChainedState) (fa : AssetId) (p t pot : CellId)
    (hadm : admissibleV ctx h s fa = true)
    (hbody : interpChained st (commitPrologueV s h.agent fa h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t) (hpot : ctx.burnPot = some pot)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t) (hapot : h.agent ≠ pot)
    (hpt : p ≠ t) (hppot : p ≠ pot) (htpot : t ≠ pot)
    (hbA : s'.kernel.bal h.agent fa = (commitPrologueV s h.agent fa h.fee).kernel.bal h.agent fa)
    (hbP : s'.kernel.bal p fa = (commitPrologueV s h.agent fa h.fee).kernel.bal p fa)
    (hbT : s'.kernel.bal t fa = (commitPrologueV s h.agent fa h.fee).kernel.bal t fa)
    (hbPot : s'.kernel.bal pot fa = (commitPrologueV s h.agent fa h.fee).kernel.bal pot fa) :
    ∃ so, runTurnV ctx h st s fa = TurnOutcome.bodyCommitted so ∧
      feeQuadBal so fa h.agent p t pot = feeQuadBal s fa h.agent p t pot := by
  refine ⟨distributeFeeV ctx s' fa h.fee, runTurnV_body_committed ctx h st s s' fa hadm hbody, ?_⟩
  obtain ⟨hqA, hqP, hqT, hqPot⟩ :=
    distributeFeeV_quad ctx s' fa h.fee h.agent p t pot hp ht hpot
      hap hat hapot hpt hppot htpot
  have hproP : (commitPrologueV s h.agent fa h.fee).kernel.bal p fa = s.kernel.bal p fa :=
    commitPrologueV_bal_frame s h.agent fa h.fee p fa (by rintro ⟨he, -⟩; exact hap he.symm)
  have hproT : (commitPrologueV s h.agent fa h.fee).kernel.bal t fa = s.kernel.bal t fa :=
    commitPrologueV_bal_frame s h.agent fa h.fee t fa (by rintro ⟨he, -⟩; exact hat he.symm)
  have hproPot : (commitPrologueV s h.agent fa h.fee).kernel.bal pot fa
      = s.kernel.bal pot fa :=
    commitPrologueV_bal_frame s h.agent fa h.fee pot fa (by rintro ⟨he, -⟩; exact hapot he.symm)
  unfold feeQuadBal
  rw [hqA, hqP, hqT, hqPot, hbA, hbP, hbT, hbPot,
      commitPrologueV_bal_agent, hproP, hproT, hproPot]
  unfold feeBurned
  ring

/-- **KEYSTONE (c′) — EXACT on the FAILED body too.** The anti-spam fee of a failed body is
distributed to the same quadruple, so `Σδ = 0` exactly on the `prologueCommittedBodyFailed`
outcome as well — the W1 wrapper NEVER destroys value (the scalar wrapper's failed-body fee just
vanished from the triple). -/
theorem runTurnV_quadruple_exact_on_body_failure (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s : RecChainedState) (fa : AssetId) (p t pot : CellId)
    (hadm : admissibleV ctx h s fa = true)
    (hbody : interpChained st (commitPrologueV s h.agent fa h.fee) = none)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t) (hpot : ctx.burnPot = some pot)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t) (hapot : h.agent ≠ pot)
    (hpt : p ≠ t) (hppot : p ≠ pot) (htpot : t ≠ pot) :
    ∃ sp, runTurnV ctx h st s fa = TurnOutcome.prologueCommittedBodyFailed sp ∧
      feeQuadBal sp fa h.agent p t pot = feeQuadBal s fa h.agent p t pot := by
  refine ⟨distributeFeeV ctx (commitPrologueV s h.agent fa h.fee) fa h.fee,
    runTurnV_body_failed ctx h st s fa hadm hbody, ?_⟩
  obtain ⟨hqA, hqP, hqT, hqPot⟩ :=
    distributeFeeV_quad ctx (commitPrologueV s h.agent fa h.fee) fa h.fee h.agent p t pot
      hp ht hpot hap hat hapot hpt hppot htpot
  have hproP : (commitPrologueV s h.agent fa h.fee).kernel.bal p fa = s.kernel.bal p fa :=
    commitPrologueV_bal_frame s h.agent fa h.fee p fa (by rintro ⟨he, -⟩; exact hap he.symm)
  have hproT : (commitPrologueV s h.agent fa h.fee).kernel.bal t fa = s.kernel.bal t fa :=
    commitPrologueV_bal_frame s h.agent fa h.fee t fa (by rintro ⟨he, -⟩; exact hat he.symm)
  have hproPot : (commitPrologueV s h.agent fa h.fee).kernel.bal pot fa
      = s.kernel.bal pot fa :=
    commitPrologueV_bal_frame s h.agent fa h.fee pot fa (by rintro ⟨he, -⟩; exact hapot he.symm)
  unfold feeQuadBal
  rw [hqA, hqP, hqT, hqPot, commitPrologueV_bal_agent, hproP, hproT, hproPot]
  unfold feeBurned
  ring

/-- **THE LAW RIDES THE TURN.** A conserved pre-state stays conserved through the WHOLE W1 wrapper
(prologue ∘ committed body ∘ epilogue): the prologue's `−fee` and the epilogue's `+fee` cancel at
the fee asset, every other asset is untouched, and the body preserves the combined measure (every
welded effect does — that is `RecordKernel §VALUE-UNIFY`). `ExactConservation` is a turn-level
invariant of `runTurnV`, with NO modulo and NO exemption. -/
theorem runTurnV_preserves_exact (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : RecChainedState) (fa : AssetId) (p t pot : CellId)
    (hadm : admissibleV ctx h s fa = true)
    (hbody : interpChained st (commitPrologueV s h.agent fa h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t) (hpot : ctx.burnPot = some pot)
    (hpm : p ∈ s'.kernel.accounts) (htm : t ∈ s'.kernel.accounts)
    (hpotm : pot ∈ s'.kernel.accounts)
    -- the body preserved the combined per-asset measure (what every welded kernel verb proves):
    (hbodyCons : ∀ b, recTotalAsset s'.kernel b
        = recTotalAsset (commitPrologueV s h.agent fa h.fee).kernel b)
    (hex : ExactConservation s.kernel) :
    ∃ so, runTurnV ctx h st s fa = TurnOutcome.bodyCommitted so ∧ ExactConservation so.kernel := by
  refine ⟨distributeFeeV ctx s' fa h.fee, runTurnV_body_committed ctx h st s s' fa hadm hbody, ?_⟩
  intro b
  rw [distributeFeeV_measure ctx s' fa h.fee p t pot hp ht hpot hpm htm hpotm b,
      hbodyCons b,
      commitPrologueV_measure s h.agent fa h.fee (admissibleV_extract hadm).1 b]
  have hzero := hex b
  by_cases hb : b = fa
  · rw [if_pos hb]; omega
  · rw [if_neg hb]; omega

end ValueUnify

/-! ### §7' — axiom hygiene (the W1 keystones). -/

#assert_axioms creditBalV_measure
#assert_axioms commitPrologueV_nonce
#assert_axioms commitPrologueV_measure
#assert_axioms distributeFeeV_measure
#assert_axioms admissibleV_extract
#assert_axioms commitPrologueV_closes_replay
#assert_axioms runTurnV_rejected
#assert_axioms runTurnV_body_committed
#assert_axioms runTurnV_body_failed
#assert_axioms runTurnV_quadruple_exact                    -- KEYSTONE (c′), committed
#assert_axioms runTurnV_quadruple_exact_on_body_failure    -- KEYSTONE (c′), failed body
#assert_axioms runTurnV_preserves_exact                    -- THE LAW rides the turn

/-! ### §8' — non-vacuity (`#guard`): the quadruple is EXACT where the triple lost the burn.

Agent 7 holds 100 of fee-asset 0 on the PER-ASSET ledger (nonce 3 in the cell record); proposer 20 /
treasury 30 / burn-pot 40 are live. Same header `eh0` (fee 10). The scalar §8 run showed the triple
drop 100 → 98 (modulo-burn); the W1 quadruple stays EXACTLY 100 on BOTH non-rejected outcomes. -/

/-- The W1 host context: `ec0` + the wired burn-pot 40. -/
def ecV0 : AdmCtx := { ec0 with burnPot := some 40 }

/-- W1 pre-state: agent 7 with 100 of asset 0 on the `bal` ledger (+ nonce 3 in the cell record);
proposer 20, treasury 30, burn-pot 40 live and empty. -/
def esV0 : Dregg2.Exec.RecChainedState :=
  { kernel := { accounts := {7, 20, 30, 40}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 0), ("nonce", .int 3)]
                                 else .record [("balance", .int 0)],
                bal := fun c a => if c = 7 ∧ a = 0 then 100 else 0 },
    log := [] }

-- COMMITTED body: accepted, and the QUADRUPLE is EXACT (100 → 100; agent 90 / 20 +5 / 30 +3 / 40 +2):
#guard (match runTurnV ecV0 eh0 bodyOK esV0 0 with | .bodyCommitted _ => true | _ => false)
#guard ((runTurnV ecV0 eh0 bodyOK esV0 0).state?.map
        (fun sf => (sf.kernel.bal 7 0, sf.kernel.bal 20 0, sf.kernel.bal 30 0, sf.kernel.bal 40 0)))
        == some (90, 5, 3, 2)
#guard (feeQuadBal esV0 0 7 20 30 40 == 100)
#guard ((runTurnV ecV0 eh0 bodyOK esV0 0).state?.map (fun sf => feeQuadBal sf 0 7 20 30 40))
        == some 100
-- TAMPER: the scalar wrapper's modulo-burn value (98) is FALSE here — nothing left the ledger:
#guard (((runTurnV ecV0 eh0 bodyOK esV0 0).state?.map (fun sf => feeQuadBal sf 0 7 20 30 40))
        == some 98) == false
-- FAILED body: prologue persists, the anti-spam fee is DISTRIBUTED, the quadruple is STILL exact:
#guard (match runTurnV ecV0 eh0 bodyFail esV0 0 with
        | .prologueCommittedBodyFailed _ => true | _ => false)
#guard ((runTurnV ecV0 eh0 bodyFail esV0 0).state?.map (fun sf => feeQuadBal sf 0 7 20 30 40))
        == some 100
-- ...and the replay window is closed against the committed state:
#guard ((runTurnV ecV0 eh0 bodyFail esV0 0).state?.map (fun sp => admissibleV ecV0 eh0 sp 0))
        == some false
-- E6 POT-GENESIS TOOTH: with NO burn-pot wired (`ec0`), the W1 wrapper REJECTS (fail-closed — a
-- missing pot would silently destroy the burn residue):
#guard (match runTurnV ec0 eh0 bodyOK esV0 0 with | .rejected => true | _ => false)
-- E5 TOOTH: fee coverage reads the PER-ASSET ledger — an agent with an empty asset-0 column is
-- rejected regardless of any scalar `balance` field:
#guard (match runTurnV ecV0 eh0 bodyOK
          { esV0 with kernel := { esV0.kernel with bal := fun _ _ => 0 } } 0 with
        | .rejected => true | _ => false)

/-- The W1 pre-state WITH the issuer well: cell 1 carries −100 (the issuer of asset 0), so the
whole state satisfies `ExactConservation` — and the committed turn PRESERVES it. -/
def esVX : Dregg2.Exec.RecChainedState :=
  { esV0 with kernel := { esV0.kernel with
      accounts := {1, 7, 20, 30, 40},
      bal := fun c a => if c = 7 ∧ a = 0 then 100 else if c = 1 ∧ a = 0 then -100 else 0 } }

#guard (Dregg2.Exec.recTotalAsset esVX.kernel 0 == 0)  -- exact BEFORE
#guard ((runTurnV ecV0 eh0 bodyOK esVX 0).state?.map
        (fun sf => Dregg2.Exec.recTotalAsset sf.kernel 0)) == some 0  -- exact AFTER

end Dregg2.Circuit.Argus