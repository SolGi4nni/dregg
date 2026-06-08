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

/-! ## §6 — KEYSTONE (c): CONSERVATION-MODULO-BURN on a committed body.

The epilogue distributes the fee — proposer 50%, treasury 30%, the residue BURNED. So the fee-relevant
triple {agent, proposer, treasury} does NOT come back to its pre-turn total: it drops by EXACTLY
`feeBurned fee` — NOT `0` (that would be silent fee creation) and NOT the whole `fee` (that would be
silent loss; the proposer/treasury are genuinely credited). This is `Admission.fee_conservation_modulo
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
`bodyCommitted` — so the three-way is not vacuous: each branch is reachable, the prologue genuinely
persists on the failing body, and the committed turn genuinely conserves modulo burn (drop = the burn,
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
-- The prologue genuinely committed: agent 7 balance 100 → 90, nonce 3 → 4 (NEVER rolled back):
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

end Dregg2.Circuit.Argus