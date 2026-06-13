/-
# Dregg2.Distributed.FeeHistory — the Argus FEE-WRAPPED history conserves MODULO THE BURN.

**The gap this closes** (the apex inventory's exact statement; HORIZONLOG "Argus fee-wrapper
conservation"). `Distributed/HistoryAggregation.lean` proves `wellformed_history_conserves`: a
chain of BARE executor steps (`recCexec`, the body executor) conserves `recTotal` EXACTLY over
the whole history. But the deployed turn is not the bare body: `Circuit/Argus/Turn.lean`'s
`runTurn` wraps it in the committed fee/nonce PROLOGUE and the fee-distribution EPILOGUE
(proposer 50% / treasury 30% / residue BURNED), so the per-turn law is conservation-MODULO-BURN
(`conservation_modulo_burn_on_commit`, stated there on the fee triple). The whole-HISTORY
composition of that wrapper law was missing — the strand the light client checks is welded at the
BODY level (`Circuit/Argus/Aggregate.lean` SCOPE gap 1), and the wrapper "composes alongside",
with no theorem saying what the composed wrapper chain conserves.

THIS module is that theorem. A `FeeChainStep` is one ACCEPTED full Argus turn
(`commits : runTurn ctx hdr (transferStmt turn) pre = .bodyCommitted post`, with the fee cells
wired, live, and distinct); `wellformed_history_conserves_modulo_burn` proves that over any
state-chained sequence of such steps,

    recTotal (lastStateOfF g steps).kernel + totalBurn steps = recTotal g.kernel

— the ledger total at the endpoint plus the SUM OF THE PER-TURN BURNS is exactly the genesis
total. Nothing is silently lost (the whole fee does not vanish: proposer/treasury credits come
back) and nothing is silently created (the burn genuinely leaves): the only leak over an
arbitrary-length fee-wrapped history is the named protocol sink, additively.

## What is CONSUMED vs OWNED

* CONSUMED, not re-proved: `argus_full_turn_body_links` (`Aggregate.lean` §6) — each accepted
  fee-wrapped step EXPOSES its body as a genuine `recCexec` step the strand layer eats
  (`feeStep_exposes_body_strand_step`), so this fee chain sits ON the same body strand the light
  client verifies; `recKExec_conserves`/`recKExec_frame` (the body's exact conservation);
  `commitPrologue_*`/`creditCell_*`/`distributeFee_*` (the wrapper's pointwise laws,
  `Exec/Admission.lean`); the `runTurn` outcome characterisation (`Turn.lean` §3a).
* OWNED here: the `recTotal`-level accounting of the wrapper (prologue `−fee`, epilogue
  `+fee − burn`: `recTotal_commitPrologue`/`recTotal_distributeFee`), the `runTurn` ACCEPTED-
  outcome inversion (`runTurn_bodyCommitted_inv`), the per-step keystone
  (`feeStep_conserves_modulo_burn`), and the whole-history fold.

## SCOPE (honest)

* The step's body is the TRANSFER term (`transferStmt`), the same beachhead the Aggregate strand
  is built on — the body's `recTotal`-neutrality is `recKExec_conserves`. Widening to every
  welded effect body is the same per-effect motion as the strand's.
* This is the LEGACY-SCALAR fee law composed over history (`recTotal`, the scalar `balance`
  measure — the deployed `runTurn`). The W1 value-unified wrapper (`runTurnV`, fee quadruple
  EXACT on the per-asset ledger) retires the modulo per-turn (`runTurnV_quadruple_exact`); when
  the executor swaps onto it at the VK rotation, this history law collapses to `totalBurn = 0`
  paid to the burn-pot cell — the statement here is the deployed wrapper's, not the target's.
* The fee-cell wiring/distinctness/liveness hypotheses are carried as `FeeChainStep` FIELDS
  (a node whose proposer = agent would genuinely break the accounting — the hypotheses are
  load-bearing, not decorative).

l4v bar: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every keystone; no
`sorry`, no `:= True`, no `native_decide`. Non-vacuity both polarities, `#guard`-EXECUTED over a
REAL accepted fee-wrapped transfer turn (the burn is 2, not 0 and not the whole fee 10).
Verified with `lake build Dregg2.Distributed.FeeHistory`.
-/
import Dregg2.Circuit.Argus.Aggregate

namespace Dregg2.Distributed.FeeHistory

open Dregg2.Exec
  (RecChainedState RecordKernelState CellId Turn recTotal balOf recCexec
   recKExec_conserves recKExec_frame sum_indicator)
open Dregg2.Exec.Admission
  (AdmCtx TurnHdr admissible commitPrologue distributeFee feeBurned proposerShare treasuryShare
   creditCell creditOpt commitPrologue_balance commitPrologue_frame commitPrologue_accounts
   creditCell_balance creditCell_frame creditCell_accounts distributeFee_accounts
   admissible_rejects_no_agent)
open Dregg2.Circuit.Argus
  (RecStmt interp transferStmt interpChained interpChained_transferStmt runTurn TurnOutcome
   runTurn_rejected runTurn_body_failed runTurn_body_committed)
open Dregg2.Circuit.Argus.Aggregate (argusPost argus_full_turn_body_links)

/-! ## §1 — The `recTotal` accounting of the wrapper (the sum-level laws Admission's pointwise
laws compose into). -/

/-- A single-cell balance edit moves `recTotal` by exactly its delta (accounts fixed, every other
cell framed out). The one sum lemma the prologue/epilogue accounting reuses; rides
`sum_indicator` (the same single-point cancellation the kernel's conservation core uses). -/
theorem recTotal_point_update (k k' : RecordKernelState) (c : CellId) (δ : ℤ)
    (hacc : k'.accounts = k.accounts) (hc : c ∈ k.accounts)
    (hbal : balOf (k'.cell c) = balOf (k.cell c) + δ)
    (hframe : ∀ x, x ≠ c → k'.cell x = k.cell x) :
    recTotal k' = recTotal k + δ := by
  unfold Dregg2.Exec.recTotal
  rw [hacc]
  have hsum : ∀ x ∈ k.accounts,
      balOf (k'.cell x) = balOf (k.cell x) + (if x = c then δ else 0) := by
    intro x _
    by_cases hxc : x = c
    · subst hxc; rw [if_pos rfl]; exact hbal
    · rw [if_neg hxc, hframe x hxc]; ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, sum_indicator k.accounts c δ hc]

/-- **The PROLOGUE debits the total by exactly the fee** (the agent is a live account; the
prologue edits only the agent cell). -/
theorem recTotal_commitPrologue (s : RecChainedState) (agent : CellId) (fee : Int)
    (hm : agent ∈ s.kernel.accounts) :
    recTotal (commitPrologue s agent fee).kernel = recTotal s.kernel - fee := by
  have h := recTotal_point_update s.kernel (commitPrologue s agent fee).kernel agent (-fee)
    (commitPrologue_accounts s agent fee) hm
    (by rw [commitPrologue_balance]; ring)
    (fun x hx => commitPrologue_frame s agent fee x hx)
  rw [h]; ring

/-- A live-cell credit raises the total by exactly the credit. -/
theorem recTotal_creditCell (s : RecChainedState) (c : CellId) (amt : Int)
    (hm : c ∈ s.kernel.accounts) :
    recTotal (creditCell s c amt).kernel = recTotal s.kernel + amt :=
  recTotal_point_update s.kernel (creditCell s c amt).kernel c amt
    (creditCell_accounts s c amt) hm
    (creditCell_balance s c amt)
    (fun x hx => creditCell_frame s c amt x hx)

/-- **The EPILOGUE credits the total by exactly the distributed shares** (`fee − burn`): the
proposer and treasury are wired, live, distinct cells. The undistributed residue — `feeBurned`
— is exactly what does NOT come back. -/
theorem recTotal_distributeFee (ctx : AdmCtx) (s : RecChainedState) (fee : Int)
    (p t : CellId) (hp : ctx.proposer = some p) (ht : ctx.treasury = some t) (hpt : p ≠ t)
    (hpm : p ∈ s.kernel.accounts) (htm : t ∈ s.kernel.accounts) :
    recTotal (distributeFee ctx s fee).kernel
      = recTotal s.kernel + proposerShare fee + treasuryShare fee := by
  simp only [distributeFee, creditOpt, hp, ht]
  rw [recTotal_creditCell _ _ _
        (show t ∈ (creditCell s p (proposerShare fee)).kernel.accounts from htm),
      recTotal_creditCell _ _ _ hpm]

/-- **The transfer BODY is `recTotal`-neutral and account-preserving** — the lifted cornerstone
(`interpChained_transferStmt` = `recKExec` on the kernel) composed with the kernel's exact
conservation and frame. -/
theorem transfer_body_total_frame {turn : Turn} {s₁ s' : RecChainedState}
    (hbody : interpChained (transferStmt turn) s₁ = some s') :
    recTotal s'.kernel = recTotal s₁.kernel ∧ s'.kernel.accounts = s₁.kernel.accounts := by
  rw [interpChained_transferStmt] at hbody
  rw [Option.map_eq_some_iff] at hbody
  obtain ⟨k', hk, hs'⟩ := hbody
  subst hs'
  exact ⟨recKExec_conserves s₁.kernel k' turn hk, (recKExec_frame s₁.kernel k' turn hk).1⟩

#assert_axioms recTotal_point_update
#assert_axioms recTotal_commitPrologue
#assert_axioms recTotal_distributeFee
#assert_axioms transfer_body_total_frame

/-! ## §2 — `FeeChainStep`: one ACCEPTED fee-wrapped Argus turn + the inversion. -/

/-- **One accepted fee-wrapped turn of the history**: the host context, the turn header, the
transfer body's turn, the pre/post chained states, and the executor witness `commits` — the FULL
Argus wrapper `runTurn` ACCEPTED the turn (`bodyCommitted post`). The fee-cell wiring fields are
load-bearing hypotheses (a deployment whose proposer IS the agent genuinely breaks the per-turn
accounting): proposer/treasury wired (`hp`/`ht`), distinct from the agent and each other
(`hap`/`hat`/`hpt`), and live accounts at the pre-state (`hpm`/`htm`). -/
structure FeeChainStep where
  /-- The host admission context (proposer/treasury wiring, clock, budget). -/
  ctx : AdmCtx
  /-- The turn header (agent, nonce, fee, expiry, chain link). -/
  hdr : TurnHdr
  /-- The transfer the body runs. -/
  turn : Turn
  /-- The pre-state chained record. -/
  pre : RecChainedState
  /-- The accepted post-state chained record (fee distributed). -/
  post : RecChainedState
  /-- The wired proposer cell. -/
  proposer : CellId
  /-- The wired treasury cell. -/
  treasury : CellId
  hp : ctx.proposer = some proposer
  ht : ctx.treasury = some treasury
  hap : hdr.agent ≠ proposer
  hat : hdr.agent ≠ treasury
  hpt : proposer ≠ treasury
  hpm : proposer ∈ pre.kernel.accounts
  htm : treasury ∈ pre.kernel.accounts
  /-- **The executor witness**: the full Argus turn wrapper ACCEPTED this turn. -/
  commits : runTurn ctx hdr (transferStmt turn) pre = TurnOutcome.bodyCommitted post

/-- **`runTurn` ACCEPTED-outcome inversion** — an accepted outcome decodes into its three phases:
admission passed, the body committed on the post-prologue state, and the post-state is the
epilogue of the body's. (The converse of `runTurn_body_committed`.) -/
theorem runTurn_bodyCommitted_inv {ctx : AdmCtx} {hdr : TurnHdr} {st : RecStmt}
    {s post : RecChainedState}
    (hrun : runTurn ctx hdr st s = TurnOutcome.bodyCommitted post) :
    admissible ctx hdr s = true
      ∧ ∃ s', interpChained st (commitPrologue s hdr.agent hdr.fee) = some s'
          ∧ post = distributeFee ctx s' hdr.fee := by
  by_cases hadm : admissible ctx hdr s = true
  · cases hbody : interpChained st (commitPrologue s hdr.agent hdr.fee) with
    | none =>
        rw [runTurn_body_failed ctx hdr st s hadm hbody] at hrun
        exact TurnOutcome.noConfusion hrun
    | some s' =>
        rw [runTurn_body_committed ctx hdr st s s' hadm hbody] at hrun
        injection hrun with h
        exact ⟨hadm, s', rfl, h.symm⟩
  · rw [runTurn_rejected ctx hdr st s (Bool.eq_false_iff.mpr hadm)] at hrun
    exact TurnOutcome.noConfusion hrun

/-- **THE PER-STEP KEYSTONE — an accepted fee-wrapped turn moves `recTotal` by exactly
`−feeBurned`.** Prologue `−fee` (agent live, from admission) ∘ exactly-conserving transfer body ∘
epilogue `+ (fee − burn)`: the composed wrapper loses precisely the protocol sink — not `0`
(the burn is real) and not the whole fee (the shares come back). The per-turn
`conservation_modulo_burn_on_commit` lifted from the fee TRIPLE to the WHOLE ledger measure. -/
theorem feeStep_conserves_modulo_burn (s : FeeChainStep) :
    recTotal s.post.kernel = recTotal s.pre.kernel - feeBurned s.hdr.fee := by
  obtain ⟨hadm, s', hbody, hpost⟩ := runTurn_bodyCommitted_inv s.commits
  -- the agent is live (admission gate 2, read off the passing gate).
  have hagent : s.hdr.agent ∈ s.pre.kernel.accounts := by
    by_contra hgone
    rw [admissible_rejects_no_agent s.ctx s.hdr s.pre hgone] at hadm
    exact Bool.noConfusion hadm
  -- the three phases' accounting.
  have hpro : recTotal (commitPrologue s.pre s.hdr.agent s.hdr.fee).kernel
      = recTotal s.pre.kernel - s.hdr.fee :=
    recTotal_commitPrologue s.pre s.hdr.agent s.hdr.fee hagent
  obtain ⟨hbodyTot, hbodyAcc⟩ := transfer_body_total_frame hbody
  have hpm' : s.proposer ∈ s'.kernel.accounts := by rw [hbodyAcc]; exact s.hpm
  have htm' : s.treasury ∈ s'.kernel.accounts := by rw [hbodyAcc]; exact s.htm
  have hepi := recTotal_distributeFee s.ctx s' s.hdr.fee s.proposer s.treasury
    s.hp s.ht s.hpt hpm' htm'
  rw [hpost, hepi, hbodyTot, hpro]
  unfold Dregg2.Exec.Admission.feeBurned
  ring

#assert_axioms runTurn_bodyCommitted_inv
#assert_axioms feeStep_conserves_modulo_burn

/-! ## §3 — Each fee step EXPOSES the body strand step (consuming `Aggregate` §6, not
re-proving it): the fee-wrapped history sits ON the body-executor strand the light client
verifies. -/

/-- **The boundary, consumed.** An accepted `FeeChainStep` decomposes into the body step the
strand layer eats: the body committed on the post-prologue state, that body IS a genuine
`recCexec` step (via `argus_full_turn_body_links`, reused verbatim), and the accepted post-state
is its fee epilogue. The fee chain and the light-client strand speak about the SAME executor
steps — the wrapper composes alongside, exactly as `Aggregate` SCOPE gap 1 states. -/
theorem feeStep_exposes_body_strand_step (s : FeeChainStep) :
    ∃ sBody,
      interpChained (transferStmt s.turn) (commitPrologue s.pre s.hdr.agent s.hdr.fee)
          = some sBody
      ∧ recCexec (commitPrologue s.pre s.hdr.agent s.hdr.fee) s.turn
          = some (argusPost s.turn (commitPrologue s.pre s.hdr.agent s.hdr.fee) sBody)
      ∧ s.post = distributeFee s.ctx sBody s.hdr.fee := by
  obtain ⟨hadm, sBody, hbody, hpost⟩ := runTurn_bodyCommitted_inv s.commits
  obtain ⟨-, hlink⟩ := argus_full_turn_body_links s.ctx s.hdr s.turn s.pre sBody hadm hbody
  exact ⟨sBody, hbody, hlink, hpost⟩

#assert_axioms feeStep_exposes_body_strand_step

/-! ## §4 — The whole-history fold: conservation MODULO the summed burn. -/

/-- The fee steps form a contiguous chain from genesis `g` (each accepted post-state is the next
step's pre-state) — the fee-wrapped sibling of `HistoryAggregation.StateChained`. -/
def StateChainedF (g : RecChainedState) : List FeeChainStep → Prop
  | [] => True
  | s :: rest => s.pre = g ∧ StateChainedF s.post rest

/-- The state the fee chain reaches from `g` (genesis if empty, else the last accepted post). -/
def lastStateOfF (g : RecChainedState) : List FeeChainStep → RecChainedState
  | [] => g
  | s :: rest => lastStateOfF s.post rest

/-- **The total burn of the history**: the sum of each accepted turn's burned fee residue. -/
def totalBurn (steps : List FeeChainStep) : ℤ :=
  (steps.map (fun s => feeBurned s.hdr.fee)).sum

/-- **THE KEYSTONE — `wellformed_history_conserves_modulo_burn`.** Over ANY state-chained
fee-wrapped history, the endpoint ledger total PLUS the summed per-turn burns equals the genesis
total: `recTotal (lastStateOfF g steps).kernel + totalBurn steps = recTotal g.kernel`. The
whole-history composition of the per-turn fee law: arbitrary-length histories leak EXACTLY the
named protocol sink, additively — no silent creation, no silent loss. (The bare body strand's
`wellformed_history_conserves` is the `totalBurn = 0` face of this.) -/
theorem wellformed_history_conserves_modulo_burn (g : RecChainedState)
    (steps : List FeeChainStep) (hch : StateChainedF g steps) :
    recTotal (lastStateOfF g steps).kernel + totalBurn steps = recTotal g.kernel := by
  induction steps generalizing g with
  | nil => simp [lastStateOfF, totalBurn]
  | cons s rest ih =>
      obtain ⟨hpre, hrest⟩ := hch
      subst hpre
      have hstep := feeStep_conserves_modulo_burn s
      have htail := ih s.post hrest
      show recTotal (lastStateOfF s.post rest).kernel + totalBurn (s :: rest)
        = recTotal s.pre.kernel
      have hburn : totalBurn (s :: rest) = feeBurned s.hdr.fee + totalBurn rest := by
        simp [totalBurn]
      rw [hburn]
      omega

#assert_axioms wellformed_history_conserves_modulo_burn

/-! ## §5 — NON-VACUITY (both polarities, `#guard`-EXECUTED): a REAL accepted fee-wrapped
transfer turn, whose burn is `2` — not `0` and not the whole fee `10`.

Reuses `Turn.lean`'s §8b concrete world: agent/src cell 7 (bal 100, nonce 3), dst cell 8,
proposer 20, treasury 30 (`ts0`/`ec0`/`eh0`), transfer amount 5, fee 10. -/

open Dregg2.Circuit.Argus (ts0 ec0 eh0)

/-- The demo transfer: cell 7 sends 5 to cell 8. -/
def demoTurn : Turn := { actor := 7, src := 7, dst := 8, amt := 5 }

/-- The demo turn is ACCEPTED (shape check, kernel-evaluated). -/
theorem demo_outcome_shape :
    (match runTurn ec0 eh0 (transferStmt demoTurn) ts0 with
      | TurnOutcome.bodyCommitted _ => true
      | _ => false) = true := by decide

/-- The accepted post-state of the demo turn (extracted from the outcome). -/
def demoPost : RecChainedState :=
  match runTurn ec0 eh0 (transferStmt demoTurn) ts0 with
  | TurnOutcome.bodyCommitted s => s
  | _ => ts0

/-- The demo turn's executor witness: `runTurn` accepts it AT `demoPost`. -/
theorem demo_commits :
    runTurn ec0 eh0 (transferStmt demoTurn) ts0 = TurnOutcome.bodyCommitted demoPost := by
  have h := demo_outcome_shape
  unfold demoPost
  revert h
  cases runTurn ec0 eh0 (transferStmt demoTurn) ts0 with
  | rejected => intro h; exact Bool.noConfusion h
  | prologueCommittedBodyFailed s => intro h; exact Bool.noConfusion h
  | bodyCommitted s => intro _; rfl

/-- The demo fee chain step — a REAL inhabitant of `FeeChainStep` (the structure is not empty;
every wiring hypothesis is discharged by `decide` on the concrete world). -/
def demoStep : FeeChainStep where
  ctx := ec0
  hdr := eh0
  turn := demoTurn
  pre := ts0
  post := demoPost
  proposer := 20
  treasury := 30
  hp := rfl
  ht := rfl
  hap := by decide
  hat := by decide
  hpt := by decide
  hpm := by decide
  htm := by decide
  commits := demo_commits

-- the pre-state total is 100 (cell 7's balance; 8/20/30 empty):
#guard recTotal ts0.kernel == 100
-- THE LAW, executed: the accepted turn drops the total by EXACTLY the burn (fee 10 → burn 2):
#guard recTotal demoPost.kernel == 98
-- NEG (no silent creation): the "fully conserved" claim (total still 100) is FALSE — the burn is real:
#guard (recTotal demoPost.kernel == 100) == false
-- NEG (no silent loss): the "whole fee gone" claim (total 90) is ALSO FALSE — the shares come back:
#guard (recTotal demoPost.kernel == 90) == false

/-- The per-step keystone FIRES on the real accepted turn. -/
theorem demo_step_conserves_modulo_burn :
    recTotal demoPost.kernel = recTotal ts0.kernel - feeBurned eh0.fee :=
  feeStep_conserves_modulo_burn demoStep

/-- The whole-history keystone FIRES on the (one-step) real fee chain. -/
theorem demo_history_conserves_modulo_burn :
    recTotal (lastStateOfF ts0 [demoStep]).kernel + totalBurn [demoStep]
      = recTotal ts0.kernel :=
  wellformed_history_conserves_modulo_burn ts0 [demoStep] ⟨rfl, trivial⟩

#assert_axioms demo_commits
#assert_axioms demo_step_conserves_modulo_burn
#assert_axioms demo_history_conserves_modulo_burn

end Dregg2.Distributed.FeeHistory
