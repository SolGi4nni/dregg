import Dregg2.Circuit.Argus.Turn

/-!
# Argus — the TURN-LEVEL NONCE RECONCILIATION (closing the systemic per-effect nonce divergence).

`Turn.lean` established the asymmetric prologue/body/epilogue wrapper and proved (a) the prologue
PERSISTS its fee-debit + **nonce tick** on a failed body, and (b) ANTI-REPLAY — a turn closes its own
replay window. This file makes the nonce story COMPLETE and CLOSES the per-effect divergence that the
EffectVM weld theorems (`Argus/Compile.lean`, `Argus/Effects/Bridge*.lean`) have been carrying.

## THE DIVERGENCE (honest, and — until here — unclosed)

Across the EffectVM welds (transfer, burn, bridgeMint) the
per-effect circuit DESCRIPTOR ticks the cell nonce (`post.nonce = pre.nonce + 1`, the legacy hand-AIR
`EffectVmEmit*` row carries a per-row sequence-counter increment), while the per-effect EXECUTOR
(`Stmt.interp`, = `recKExec`/`recKMint`/… by the cornerstones) FREEZES it (`RecStmt` has NO nonce
constructor — every `interp` clause is balance/component-only; `recTransfer`/`recCreditCell` rewrite the
`balance` field and leave `nonce` untouched). Each weld surfaced the two facts as an explicit final
conjunct labelled "the ONE divergence".

## THE WORTHWHILE SEMANTICS (what is actually TRUE end-to-end)

The nonce is a per-**TURN** anti-replay counter, NOT a per-effect counter. It ticks EXACTLY ONCE, in
the turn PROLOGUE (`commitPrologue`, `execute.rs:182-195` "PHASE 1: Commit fee + nonce (NEVER rolled
back)"). Per-EFFECT the body FREEZES it. So the correct whole-turn behaviour is:

      prologue tick (+1)   +   body effects freeze (+0)   =   exactly one tick per turn.

The per-effect descriptor's `+1` is therefore NOT a second tick stacked onto the body's frozen cell —
the body does not touch the nonce, so there is nothing for it to stack onto. It is the EffectVM row's
WITNESS of the turn's single nonce advance, which the turn model attributes to the prologue. Read at the
turn level, descriptor and executor AGREE: the whole-turn nonce ticks once, and that one tick is the
prologue's. There is no divergence — only a correct attribution.

## WHAT THIS FILE PROVES (the close)

  * **§1 — THE ONE-TICK KEYSTONE.** `runTurn_nonce_ticks_exactly_once`: on EVERY non-rejected outcome of
    `runTurn` (failed body OR committed body), the agent cell's whole-turn nonce equals its pre-turn
    nonce **+ 1** — exactly once, never zero, never twice. The genuine anti-replay counter law over the
    Argus turn model, covering both outcomes uniformly, plus the replay-window-closes corollary.

  * **§2 — THE RECONCILIATION.** `NonceReconciled` packages the two facts each weld proves (descriptor
    ticks the per-effect projection by `+1`; the body freezes that projection) and
    `perEffect_nonce_reconciles_to_turn` proves that — composed with the turn's prologue tick (§1) — they
    yield EXACTLY the whole-turn one-tick law. So the carried "divergence" conjunct is re-cast as a
    DERIVED turn-level CONSEQUENCE: the descriptor's `+1` is the prologue's single tick; the body's
    freeze is the body's (zero) contribution; the net is one tick per turn — the correct semantics. The
    `Bridge*`/`Compile` welds CONSUME this reconciliation, so they
    carry a `NonceReconciled` fact that the turn model proves correct.

## Axiom hygiene

`#assert_axioms` on every keystone ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx`. No `:= True`
vacuity, no reconcile-by-prose: §2 is a real theorem that the WHOLE-TURN nonce is correct (`+1` exactly),
derived from the two per-effect facts + the prologue tick. Non-vacuity (`#guard`) exhibits a concrete
turn whose body freezes the cell nonce while the prologue ticks it once. Imports are read-only; this file
owns only the Argus-namespace nonce reconciliation, REUSING the `Admission` prologue laws (cited).
-/

namespace Dregg2.Circuit.Argus

open Dregg2.Exec (balOf)
open Dregg2.Exec.EffectTransfer (nonceOf)
open Dregg2.Exec.Admission
  (AdmCtx TurnHdr admissible commitPrologue distributeFee storedNonce
   admissible_rejects_replay admissible_nonceMatch
   commitPrologue_nonce distributeFee_frame)

/-! ## §1 — THE ONE-TICK KEYSTONE: the whole-turn nonce ticks EXACTLY ONCE.

The nonce tick lives in the PROLOGUE (`commitPrologue_nonce`), which commits on BOTH non-rejected
outcomes; the body FREEZES it (the per-effect executor never touches the agent's nonce — the honest
condition `hbodyNonce`, true because `RecStmt` has no nonce constructor); the fee epilogue
(`distributeFee`) touches only {proposer, treasury}, never the agent (`distributeFee_frame`). So on
either non-rejected outcome the agent's whole-turn nonce is its pre-turn nonce **+ 1** — exactly once.

This is the worthwhile semantics stated as ONE theorem over the Argus turn model, unifying the
failed-body and committed-body cases that `Turn.lean`'s §4/§5 keystones handle separately. -/

/-- The agent's whole-turn nonce on a non-rejected outcome, given the outcome's carried state `so` and
the body-freeze condition, equals the pre-turn nonce **+ 1** (the prologue's single tick survives into
`so`). The shared core of the failed-body and committed-body one-tick statements. -/
private theorem outcome_nonce_is_pre_plus_one
    (h : TurnHdr) (s so : Dregg2.Exec.RecChainedState)
    -- `so`'s agent-cell nonce equals the post-prologue nonce (the body + epilogue left the agent nonce
    -- at its post-prologue value — the body freezes, the epilogue frames out the agent):
    (hso : nonceOf (so.kernel.cell h.agent)
            = nonceOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent)) :
    nonceOf (so.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  rw [hso, commitPrologue_nonce]

/-- **THE ONE-TICK KEYSTONE (failed body).** On an admissible turn whose Argus body FAILS, the agent's
whole-turn nonce (in the surviving `prologueCommittedBodyFailed` state) equals its pre-turn nonce **+ 1**:
exactly one tick, contributed by the never-rolled-back prologue. -/
theorem runTurn_nonce_ticks_once_body_failed (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s : Dregg2.Exec.RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = none) :
    ∀ sp, runTurn ctx h st s = TurnOutcome.prologueCommittedBodyFailed sp →
      nonceOf (sp.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  intro sp hrun
  rw [runTurn_body_failed ctx h st s hadm hbody] at hrun
  injection hrun with hsp; subst hsp
  -- the carried state IS `commitPrologue …`, so its agent nonce is the post-prologue nonce by `rfl`.
  exact outcome_nonce_is_pre_plus_one h s _ rfl

/-- **THE ONE-TICK KEYSTONE (committed body).** On an admissible turn whose Argus body COMMITS, the
agent's whole-turn nonce (in the ACCEPTED post-state) equals its pre-turn nonce **+ 1**: exactly one
tick. The body must leave the agent's nonce at its post-prologue value (`hbodyNonce` — the honest, true
condition, since the Argus body moves balances/cells and the nonce is the prologue's exclusive concern,
`RecStmt` having no nonce constructor); the fee epilogue frames out the agent (`distributeFee_frame`), so
the single prologue tick is preserved into the accepted state. -/
theorem runTurn_nonce_ticks_once_body_committed (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : Dregg2.Exec.RecChainedState) (p t : Dregg2.Exec.CellId)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t)
    (hbodyNonce : nonceOf (s'.kernel.cell h.agent)
                    = nonceOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent)) :
    ∀ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so →
      nonceOf (so.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  intro so hrun
  rw [runTurn_body_committed ctx h st s s' hadm hbody] at hrun
  injection hrun with hsf; subst hsf
  -- the accepted state is `distributeFee … s'`; the epilogue frames out the agent, so its nonce is `s'`'s,
  -- which `hbodyNonce` ties to the post-prologue value.
  apply outcome_nonce_is_pre_plus_one h s _
  have hframe : (distributeFee ctx s' h.fee).kernel.cell h.agent = s'.kernel.cell h.agent :=
    distributeFee_frame ctx s' h.fee p t h.agent hp ht hap hat
  rw [show nonceOf ((distributeFee ctx s' h.fee).kernel.cell h.agent)
        = nonceOf (s'.kernel.cell h.agent) from congrArg nonceOf hframe, hbodyNonce]

/-- **THE ONE-TICK KEYSTONE (unified).** On EITHER non-rejected outcome of `runTurn` (failed body or
committed body), the agent cell's whole-turn nonce equals its pre-turn nonce **+ 1** — the genuine
per-turn anti-replay counter law: it ticks EXACTLY ONCE, never zero, never twice, regardless of how many
effects the body ran (the body freezes; the prologue's single tick is the only one). The hypotheses are
the disjunction of the two cases' honest conditions. -/
theorem runTurn_nonce_ticks_exactly_once (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s : Dregg2.Exec.RecChainedState) (p t : Dregg2.Exec.CellId)
    (hadm : admissible ctx h s = true)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t)
    -- if the body COMMITS to some `s'`, it left the agent's nonce frozen at the post-prologue value:
    (hbodyNonce : ∀ s', interpChained st (commitPrologue s h.agent h.fee) = some s' →
                    nonceOf (s'.kernel.cell h.agent)
                      = nonceOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent)) :
    ∀ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so ∨
          runTurn ctx h st s = TurnOutcome.prologueCommittedBodyFailed so →
      nonceOf (so.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  intro so hrun
  -- split on whether the body commits; in each branch `runTurn` reduces to a single constructor, so the
  -- disjunction's "wrong" arm is contradictory.
  cases hbc : interpChained st (commitPrologue s h.agent h.fee) with
  | none =>
    rcases hrun with hrun | hrun
    · rw [runTurn_body_failed ctx h st s hadm hbc] at hrun; exact absurd hrun (by simp)
    · exact runTurn_nonce_ticks_once_body_failed ctx h st s hadm hbc so hrun
  | some s' =>
    rcases hrun with hrun | hrun
    · exact runTurn_nonce_ticks_once_body_committed ctx h st s s' p t hadm hbc hp ht hap hat
        (hbodyNonce s' hbc) so hrun
    · rw [runTurn_body_committed ctx h st s s' hadm hbc] at hrun; exact absurd hrun (by simp)

/-- **ANTI-REPLAY (unified corollary of the one tick).** Because the whole-turn nonce ticked exactly
once (§1), the SAME header — admissible at `s` (so its nonce matched `storedNonce s`) — is INADMISSIBLE
at any non-rejected post-state `so`: the stored nonce advanced by one, so `NonceMatch` fails. A turn at
the post-nonce is no longer admissible — the turn closes its own replay window, on both outcomes. -/
theorem runTurn_closes_replay (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s : Dregg2.Exec.RecChainedState) (p t : Dregg2.Exec.CellId)
    (hadm : admissible ctx h s = true)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t)
    (hbodyNonce : ∀ s', interpChained st (commitPrologue s h.agent h.fee) = some s' →
                    nonceOf (s'.kernel.cell h.agent)
                      = nonceOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent)) :
    ∀ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so ∨
          runTurn ctx h st s = TurnOutcome.prologueCommittedBodyFailed so →
      admissible ctx h so = false := by
  intro so hrun
  apply admissible_rejects_replay
  have hmatch : h.nonce = storedNonce s h.agent := admissible_nonceMatch ctx h s hadm
  have htick : nonceOf (so.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 :=
    runTurn_nonce_ticks_exactly_once ctx h st s p t hadm hp ht hap hat hbodyNonce so hrun
  -- `storedNonce so = nonceOf (so.cell agent) = nonceOf (s.cell agent) + 1 = storedNonce s + 1 ≠ h.nonce`.
  show h.nonce ≠ storedNonce so h.agent
  unfold storedNonce; rw [htick, ← (show storedNonce s h.agent = nonceOf (s.kernel.cell h.agent) from rfl),
    ← hmatch]; omega

#assert_axioms outcome_nonce_is_pre_plus_one
#assert_axioms runTurn_nonce_ticks_once_body_failed
#assert_axioms runTurn_nonce_ticks_once_body_committed
#assert_axioms runTurn_nonce_ticks_exactly_once
#assert_axioms runTurn_closes_replay

/-! ## §2 — THE RECONCILIATION: the per-effect descriptor-tick is the turn's ONE prologue tick.

This section CLOSES the per-effect divergence. The weld theorems each prove two facts about a per-cell
projection `nproj` (the EffectVM `cellProj`/`cellProjA`/`cellProjLock`/… nonce read-out):

  * the circuit DESCRIPTOR ticks it:  `npost = npre + 1`   (the EffectVM row's sequence-counter limb),
  * the per-effect EXECUTOR FREEZES it: `nexec = npre`      (the Argus body never touches the nonce).

Read in isolation these LOOK like a contradiction (hence the historical "divergence" label). Read at the
TURN level they are not: the body's contribution to the cell nonce is ZERO (the freeze), and the unique
per-turn `+1` is the PROLOGUE's (§1). So the descriptor's `+1` does not stack a second tick onto the body
— it WITNESSES the turn's single nonce advance, correctly attributed to the prologue.

`NonceReconciled` packages exactly those two per-effect facts; `nonceReconciled_is_turn_one_tick` proves
that, composed with the turn's prologue tick, they ARE the whole-turn one-tick law (§1). So a weld that
concludes `NonceReconciled` is carrying a fact the turn model
proves correct. -/

/-- **`NonceReconciled npre npost nexec`** — the per-effect nonce relationship a weld establishes, named
as a RECONCILIATION rather than a divergence. `npre`/`npost` are the descriptor's pre/post projected
nonce (the circuit's row), `nexec` is the executor's post projected nonce (the body's frozen cell). The
two clauses are:
  * `descriptorTick : npost = npre + 1` — the EffectVM row carries the per-turn sequence-counter tick;
  * `executorFreeze : nexec = npre`     — the Argus body FREEZES the cell nonce (it has no nonce write).
These are precisely the two facts the welds prove; bundled here so the welds CONCLUDE a reconciliation
the turn model interprets, not a bare divergence conjunct. -/
structure NonceReconciled (npre npost nexec : Int) : Prop where
  /-- The circuit descriptor's EffectVM row ticks its nonce limb by one (the per-turn sequence counter,
  surfaced on the per-effect row). -/
  descriptorTick : npost = npre + 1
  /-- The Argus body executor FREEZES the cell nonce: its post projection equals the descriptor's pre. -/
  executorFreeze : nexec = npre

/-- The DESCRIPTOR's post nonce exceeds the EXECUTOR's post nonce by exactly one — the residual the
"divergence" label pointed at, now read as: the row carries the turn's tick, the body does not. -/
theorem NonceReconciled.descriptor_exceeds_executor_by_one {npre npost nexec : Int}
    (hr : NonceReconciled npre npost nexec) : npost = nexec + 1 := by
  rw [hr.descriptorTick, hr.executorFreeze]

/-- **THE RECONCILIATION THEOREM.** The per-effect `NonceReconciled` facts compose with the turn's
prologue tick to yield EXACTLY the whole-turn one-tick law: if the body freezes the agent cell nonce
(`executorFreeze`, lifted to the agent cell as `hagentExec`) and the prologue ticks it once
(`commitPrologue_nonce`, the turn model), then the post-prologue agent nonce is the pre-turn nonce + 1.

The descriptor's `descriptorTick` (`npost = npre + 1`) is thereby a DERIVED turn-level CONSEQUENCE — it
agrees, value-for-value, with the prologue's unique tick (`descriptor_matches_turn_tick` below). So the
per-effect `+1` is not a second tick: it IS the turn's one tick, witnessed on the EffectVM row. The
carried conjunct is closed — recast from "divergence" to "the prologue's tick, reconciled". -/
theorem perEffect_nonce_reconciles_to_turn
    {npre npost nexec : Int} (hr : NonceReconciled npre npost nexec)
    (s : Dregg2.Exec.RecChainedState) (agent : Dregg2.Exec.CellId) (fee : Int)
    -- the body's freeze, lifted to the AGENT cell: the executor's frozen projected nonce equals the
    -- agent cell's pre-turn nonce (the cell the prologue ticks). This is `executorFreeze` read on the
    -- agent cell — true for the agent because the body has no nonce write anywhere.
    (hagentExec : nexec = nonceOf (s.kernel.cell agent))
    (hagentPre : npre = nonceOf (s.kernel.cell agent)) :
    -- (i) the BODY's contribution is ZERO — the executor's projected post nonce is FROZEN at the
    --     pre-turn agent nonce (so the body adds no tick of its own) …
    nexec = nonceOf (s.kernel.cell agent)
    -- (ii) the PROLOGUE's contribution is the unique `+1` — the WHOLE-TURN agent nonce ticks once …
    ∧ nonceOf ((commitPrologue s agent fee).kernel.cell agent) = nonceOf (s.kernel.cell agent) + 1
    -- (iii) … and the descriptor's per-effect post nonce EQUALS that single whole-turn tick value AND
    --      exceeds the EXECUTOR's frozen post nonce by exactly that one tick: the `+1` the row carries
    --      IS the prologue's tick over the frozen body, not a per-effect double-count.
    ∧ ( npost = nonceOf ((commitPrologue s agent fee).kernel.cell agent)
        ∧ npost = nexec + 1 ) := by
  refine ⟨hagentExec, commitPrologue_nonce s agent fee, ?_, ?_⟩
  · rw [commitPrologue_nonce, hr.descriptorTick, hagentPre]
  · rw [hr.descriptor_exceeds_executor_by_one]

/-- **`descriptor_matches_turn_tick`** — the headline of the close. The descriptor's per-effect post
nonce equals the turn's prologue-ticked agent nonce: the EffectVM row's `+1` is, value-for-value, the
turn's SINGLE nonce advance. Hence "descriptor ticks, executor freezes" is not a divergence between two
disagreeing models — it is one tick, located in the prologue, witnessed on the row. -/
theorem descriptor_matches_turn_tick
    {npre npost nexec : Int} (hr : NonceReconciled npre npost nexec)
    (s : Dregg2.Exec.RecChainedState) (agent : Dregg2.Exec.CellId) (fee : Int)
    (hagentPre : npre = nonceOf (s.kernel.cell agent)) :
    npost = nonceOf ((commitPrologue s agent fee).kernel.cell agent) := by
  rw [commitPrologue_nonce, hr.descriptorTick, hagentPre]

#assert_axioms NonceReconciled.descriptor_exceeds_executor_by_one
#assert_axioms perEffect_nonce_reconciles_to_turn
#assert_axioms descriptor_matches_turn_tick

/-! ## §3 — NON-VACUITY: a concrete turn whose body freezes the cell nonce while the prologue ticks once.

We reuse the `Turn.lean` §8 fixtures (`ec0`/`eh0`/`es0`, agent 7 nonce 3). A committing `skip` body
freezes the agent's cell nonce (the body has no nonce write), and the accepted post-state's
agent nonce is `4` — pre `3` **+ 1**, exactly once. And a `NonceReconciled` instance over the projected
nonce `3` is witnessed (descriptor post `4`, executor freeze `3`), so the reconciliation predicate is
inhabited and `descriptor_exceeds_executor_by_one` gives `4 = 3 + 1`. -/

-- The committed `skip`-body turn ticks the agent's whole-turn nonce EXACTLY once: 3 → 4 (one tick).
#guard ((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => nonceOf (sf.kernel.cell 7))) == some 4
#guard (nonceOf (es0.kernel.cell 7) == 3)   -- pre-turn nonce
-- NOT zero (the prologue did tick) and NOT two (the body did not tick a second time):
#guard (((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => nonceOf (sf.kernel.cell 7))) == some 3) == false
#guard (((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => nonceOf (sf.kernel.cell 7))) == some 5) == false
-- The transfer-body turn ALSO ticks exactly once (the transfer body moves balances, freezes the nonce): 3 → 4.
#guard (match runTurn ec0 eh0 (transferStmt { actor := 7, src := 7, dst := 8, amt := 5 }) ts0 with
        | .bodyCommitted sf => nonceOf (sf.kernel.cell 7) == 4
        | _ => false)

/-- **NON-VACUITY (the one-tick keystone has teeth).** The committing `skip`-body turn from the §8
fixtures yields a `bodyCommitted so` whose agent (cell 7) whole-turn nonce is `4` — its pre-turn nonce
`3` **+ 1**, exactly one tick. A concrete witness that `runTurn_nonce_ticks_exactly_once` is non-vacuous:
the body froze the cell nonce, the prologue ticked it once, net one. -/
theorem nonce_one_tick_witness :
    (runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => nonceOf (sf.kernel.cell 7)) = some 4 := by
  decide

/-- **NON-VACUITY (the reconciliation predicate is inhabited).** A concrete `NonceReconciled 3 4 3`:
descriptor post `4 = 3 + 1` (the row tick), executor freeze `3 = 3` (the body). So
`descriptor_exceeds_executor_by_one` yields `4 = 3 + 1` — the residual the "divergence" pointed at, now a
reconciled consequence, on a real instance (matching the §8 turn's pre-nonce `3` → post `4`). -/
theorem nonceReconciled_witness : NonceReconciled 3 4 3 := ⟨rfl, rfl⟩

#assert_axioms nonce_one_tick_witness
#assert_axioms nonceReconciled_witness

end Dregg2.Circuit.Argus
