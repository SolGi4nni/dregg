/-
# Dregg2.Exec.Admission — the FAIL-CLOSED admission PROLOGUE (FILL H / META-FILL H).

`turn/src/executor/execute.rs:54-195` runs a *prologue* in front of the call-forest fold. dregg1's
`TurnExecutor::execute` first runs eleven turn-level **admission gates** — none of which the verified
`FullForestAuth` fold (`Exec/FullForestAuth.lean`) models — and THEN does the structurally crucial
thing the pure all-or-nothing fold can NOT do: it **COMMITS the fee-debit + nonce-tick and NEVER
rolls them back** (`execute.rs:182-195`, "PHASE 1: Commit fee + nonce (NEVER rolled back). This
prevents DoS via expensive-but-failing turns that never pay."). The body (the forest fold) is
rollback-able; the prologue is not. That is the OPPOSITE of `execFullTurn`'s `Option`-monad
all-or-nothing fold, where a single `none` discards EVERYTHING.

This module is that prologue, as a Lean LAW, sitting strictly BESIDE the kernel fold (admission ≠
kernel — it edits NO authority graph, runs NO effect, only the host-fed turn-level gates + the
committed fee/nonce edit on the agent cell). It takes the host-fed inputs `execute.rs` reads from
its environment: `now` (the executor clock, `self.current_timestamp`), the migration `freeze`-set
(`self.frozen_cells` via `check_not_frozen`), the stored receipt head (`self.receipt_heads`, the
P0-3 self-binding), and a Stingray `budget` slice (`self.budget_gate`).

It FIXES the headline Lean-vs-Rust mismatch the swap ledger flags: `execFullTurnG s [] = some s`
(the verified fold ADMITS the empty turn) whereas dregg1 `REJECTS` it (`execute.rs:56`,
`TurnError::EmptyForest`). `admissible` requires a NON-empty forest, fail-closed.

THE STRUCTURAL CRUX (the headline theorem `prologue_survives_failed_body`): a turn whose BODY fails
(`none`) STILL spent the fee and ticked the nonce — the committed prologue persists. Hence:
  * replay is CLOSED even on a failed turn (`replay_closed_after_failed_body`): the nonce strictly
    advanced, so the *same* turn (same nonce) is no longer `admissible`;
  * the fee was genuinely spent (`fee_spent_after_failed_body`): the agent's balance dropped by the
    fee whether or not the body committed — the anti-DoS guarantee.
This is provably NOT what a pure all-or-nothing fold gives (`pure_fold_loses_prologue`): the naive
`Option`-bind `s >>= prologue >>= body` discards the prologue on a body `none`, reopening replay. We
state and prove BOTH so the asymmetry is a theorem, not a comment.

THEOREMS (no `sorry`/`axiom`/`admit`/`native_decide`):
  * `admissible_rejects_empty`        — the empty forest is INADMISSIBLE (the §EmptyForest fix).
  * `admissible_rejects_replay`       — a nonce ≠ the stored agent nonce is INADMISSIBLE (replay).
  * `admissible_rejects_expired`      — `now > valid_until` is INADMISSIBLE.
  * `admissible_rejects_underfunded`  — `balance < fee` is INADMISSIBLE (fee coverage).
  * `admissible_rejects_frozen`       — a write-set cell in the freeze-set is INADMISSIBLE.
  * `admissible_rejects_chain_fork`   — a `prevReceipt` ≠ the stored head is INADMISSIBLE (P0-3).
  * `admissible_rejects_over_budget`  — `fee > budget` is INADMISSIBLE (Stingray).
  * `commitPrologue_*`                — the committed edit: nonce ticks by 1, balance drops by `fee`,
                                        ALL OTHER cells untouched (the frame), idempotence is broken.
  * `prologue_survives_failed_body`   — **THE CRUX**: a turn whose body is `none` STILL leaves the
                                        prologue committed (balance−fee, nonce+1) — never rolled back.
  * `replay_closed_after_failed_body` — after a failed turn the SAME turn is no longer `admissible`
                                        (the nonce advanced) — anti-replay survives a failed body.
  * `fee_spent_after_failed_body`     — the fee was spent even on a failed body (anti-DoS).
  * `pure_fold_loses_prologue`        — the naive all-or-nothing `Option`-bind DISCARDS the prologue
                                        on a body `none`: the asymmetry, proved (NOT a comment).
  * `prologue_then_commit`            — on a COMMITTING body the result is body-after-prologue (the
                                        prologue is in front of, never instead of, the kernel fold).

Discipline (REORIENT §6): no `axiom`/`admit`/`native_decide`/`sorry`/`@[implemented_by]`.
`#assert_axioms` on every keystone (whitelist {propext, Classical.choice, Quot.sound}). Pure,
computable, `#eval`-able. Reuses `RecordKernel` (`balOf`/`setBalance`/`recTotal`) +
`EffectTransfer` (`nonceOf`/`setNonce`) + `Receipt` (the `ReceiptChain` link discipline). Edits
nothing. Verified standalone: `lake env lean Dregg2/Exec/Admission.lean`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectTransfer
import Dregg2.Exec.Receipt

namespace Dregg2.Exec.Admission

open Dregg2.Exec
open Dregg2.Exec.EffectTransfer (nonceOf setNonce setNonce_nonceOf setNonce_balOf)
open Dregg2.Exec.Receipts (Receipt ReceiptChain genesisSentinel wellLinked)

/-! ## §1 — The host-fed admission context.

`execute.rs` reads these from `self` / the wider executor, NOT from the turn. They are the inputs
the prologue gates against. Modeling them as an explicit `AdmCtx` keeps the prologue a PURE function
of (turn-fields, host-context, pre-state) — exactly the seam the FFI marshaller crosses. -/

/-- **The host-fed admission context** (the bits of `self` `execute.rs:54-177` reads):
  * `now`        — the executor clock (`self.current_timestamp`), checked against `validUntil`;
  * `frozen`     — the migration freeze-set (`self.frozen_cells`, via `check_not_frozen`); a turn
                   touching any frozen cell is rejected (`execute.rs:110-131`);
  * `storedHead` — the agent's stored receipt-chain head (`self.receipt_heads[agent]`), the P0-3
                   self-binding (`execute.rs:133-150`); `none` = the agent's genesis (first) turn;
  * `budget`     — the Stingray silo budget slice (`self.budget_gate`); the fee must fit
                   (`execute.rs:152-177`). -/
structure AdmCtx where
  now        : Nat
  frozen     : List CellId
  storedHead : Option Nat
  budget     : Nat
deriving Repr

/-- **The turn-level fields the prologue gates against** (the bits of `Turn` `execute.rs` reads
BEFORE the forest: `agent`, `nonce`, `fee`, `valid_until`, `previous_receipt_hash`, and the
write-set extracted from the call-forest). We carry them as an explicit record (the forest itself is
the kernel fold's concern; the prologue needs only its NON-emptiness + its write-set). -/
structure TurnHdr where
  agent      : CellId
  nonce      : Int
  fee        : Int
  validUntil : Option Nat
  prevReceipt : Option Nat
  /-- The cells the call-forest WRITES (`conflict::extract_access_sets`, `execute.rs:122`). -/
  writeSet   : List CellId
  /-- Whether the forest is NON-empty — the §EmptyForest gate (`execute.rs:56`). A turn with an
  empty forest carries `forestNonEmpty = false` and is rejected. -/
  forestNonEmpty : Bool
deriving Repr

/-! ## §2 — `admissible`: the fail-closed, host-fed admission predicate.

Eleven Rust gates collapse to seven decidable legs (the rest — agent-existence, write-set freeze —
are folded in). Each leg is a CONJUNCT; the predicate is `&&`-folded, so ANY false leg ⇒ INADMISSIBLE
(fail-closed). The pre-state `s` supplies the agent's stored nonce + balance (the things the forest
fold would otherwise have to re-read mid-flight, opening a TOCTOU window). -/

/-- Read the agent cell's stored nonce from the pre-state (the metadata measure `nonceOf`). -/
def storedNonce (s : RecChainedState) (agent : CellId) : Int := nonceOf (s.kernel.cell agent)

/-- Read the agent cell's stored balance from the pre-state (the conserved measure `balOf`). -/
def storedBalance (s : RecChainedState) (agent : CellId) : Int := balOf (s.kernel.cell agent)

/-- A cell is FROZEN when it is in the host freeze-set. -/
def isFrozen (ctx : AdmCtx) (c : CellId) : Bool := ctx.frozen.contains c

/-- **`admissible` — the FAIL-CLOSED admission predicate.** True iff EVERY gate passes:
  1. **EmptyForest** — `h.forestNonEmpty` (the §EmptyForest fix: the empty turn is INADMISSIBLE);
  2. **AgentLive**   — `agent ∈ accounts` (the agent cell exists, `execute.rs:77`);
  3. **Expiry**      — `validUntil = none ∨ now ≤ validUntil` (not expired, `execute.rs:64`);
  4. **NonceMatch**  — `nonce = storedNonce` (no replay, `execute.rs:88`);
  5. **FeeCoverage** — `fee ≤ storedBalance` ∧ `0 ≤ fee` (the agent can pay, `execute.rs:99`);
  6. **NotFrozen**   — `agent` AND every write-set cell ∉ freeze-set (`execute.rs:110-131`);
  7. **ChainHead**   — `prevReceipt = storedHead` (P0-3 self-binding, `execute.rs:145`);
  8. **Budget**      — `fee ≤ budget` (the Stingray slice covers the fee, `execute.rs:159`).
`&&`-folded: ANY false leg ⇒ `false`. -/
def admissible (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) : Bool :=
  -- 1. EmptyForest
  h.forestNonEmpty &&
  -- 2. AgentLive
  decide (h.agent ∈ s.kernel.accounts) &&
  -- 3. Expiry
  (match h.validUntil with | none => true | some vu => decide (ctx.now ≤ vu)) &&
  -- 4. NonceMatch
  decide (h.nonce = storedNonce s h.agent) &&
  -- 5. FeeCoverage
  decide (0 ≤ h.fee) && decide (h.fee ≤ storedBalance s h.agent) &&
  -- 6. NotFrozen (agent + write-set)
  (!isFrozen ctx h.agent) && (h.writeSet.all (fun c => !isFrozen ctx c)) &&
  -- 7. ChainHead (P0-3)
  decide (h.prevReceipt = ctx.storedHead) &&
  -- 8. Budget (Stingray)
  decide (h.fee ≤ (ctx.budget : Int))

/-! ## §3 — The admission rejections: each gate is a REAL teeth (non-vacuity).

Each theorem exhibits a turn that violates EXACTLY one leg and is therefore inadmissible — proving
the predicate is fail-closed on every gate, not a vacuous `true`. -/

/-- **`admissible_rejects_empty` — PROVED (the §EmptyForest FIX).** A turn whose forest is empty
(`forestNonEmpty = false`) is INADMISSIBLE — closing the `execFullTurnG s [] = some s` mismatch
where the verified fold ADMITS the empty turn but dregg1 rejects it. -/
theorem admissible_rejects_empty (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hempty : h.forestNonEmpty = false) : admissible ctx h s = false := by
  simp [admissible, hempty]

/-- **`admissible_rejects_expired` — PROVED.** `now > validUntil` ⇒ INADMISSIBLE. -/
theorem admissible_rejects_expired (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (vu : Nat) (hvu : h.validUntil = some vu) (hexp : ctx.now > vu) :
    admissible ctx h s = false := by
  simp only [admissible, hvu]
  have : decide (ctx.now ≤ vu) = false := by simp; omega
  simp [this]

/-- **`admissible_rejects_replay` — PROVED (anti-replay).** A turn whose `nonce` does NOT match the
agent's stored nonce is INADMISSIBLE — the replay gate (`execute.rs:88`). -/
theorem admissible_rejects_replay (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hbad : h.nonce ≠ storedNonce s h.agent) : admissible ctx h s = false := by
  simp [admissible, hbad]

/-- **`admissible_rejects_underfunded` — PROVED (fee coverage).** `storedBalance < fee` ⇒
INADMISSIBLE (`execute.rs:99`). The agent cannot spend more than it holds. -/
theorem admissible_rejects_underfunded (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hpoor : storedBalance s h.agent < h.fee) : admissible ctx h s = false := by
  simp only [admissible]
  have : decide (h.fee ≤ storedBalance s h.agent) = false := by simp; omega
  simp [this]

/-- **`admissible_rejects_frozen` — PROVED (migration freeze).** If the AGENT cell is in the
freeze-set, the turn is INADMISSIBLE (`execute.rs:112`). -/
theorem admissible_rejects_frozen (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hfrozen : isFrozen ctx h.agent = true) : admissible ctx h s = false := by
  simp [admissible, hfrozen]

/-- **`admissible_rejects_frozen_writeset` — PROVED (write-set freeze, defence in depth).** If ANY
cell in the call-forest write-set is frozen, the turn is INADMISSIBLE (`execute.rs:118-131`). -/
theorem admissible_rejects_frozen_writeset (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (c : CellId) (hmem : c ∈ h.writeSet) (hfrozen : isFrozen ctx c = true) :
    admissible ctx h s = false := by
  simp only [admissible]
  have hall : h.writeSet.all (fun c => !isFrozen ctx c) = false := by
    rw [List.all_eq_false]
    exact ⟨c, hmem, by simp [hfrozen]⟩
  simp [hall]

/-- **`admissible_rejects_chain_fork` — PROVED (P0-3 receipt-chain self-binding).** If the turn's
claimed `prevReceipt` ≠ the agent's stored chain head, the turn is INADMISSIBLE (`execute.rs:145`):
you cannot fabricate a turn linking onto a head you do not hold. -/
theorem admissible_rejects_chain_fork (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hfork : h.prevReceipt ≠ ctx.storedHead) : admissible ctx h s = false := by
  simp [admissible, hfork]

/-- **`admissible_rejects_over_budget` — PROVED (Stingray budget slice).** If the fee exceeds the
silo's budget slice, the turn is INADMISSIBLE (`execute.rs:159`) — rejected without charging the
agent (a silo-level resource limit, not the agent's fault). -/
theorem admissible_rejects_over_budget (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hover : h.fee > (ctx.budget : Int)) : admissible ctx h s = false := by
  simp only [admissible]
  have : decide (h.fee ≤ (ctx.budget : Int)) = false := by simp; omega
  simp [this]

/-- **`admissible_rejects_no_agent` — PROVED (agent existence).** A turn whose agent cell is not a
live account is INADMISSIBLE (`execute.rs:77`). -/
theorem admissible_rejects_no_agent (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hgone : h.agent ∉ s.kernel.accounts) : admissible ctx h s = false := by
  simp [admissible, hgone]

/-! ### §3b — The admission EXTRACTIONS: an admissible turn HELD each gate.

The duals of §3's rejections: from `admissible = true` we read OFF the load-bearing legs (the nonce
matched, the chain head linked). Proved by contraposition off the corresponding rejection theorem —
robust to the `&&`-fold's associativity (no fragile projection chains). -/

/-- **`admissible_nonceMatch` — PROVED.** An admissible turn's `nonce` EQUALS the agent's stored
nonce (the contrapositive of `admissible_rejects_replay`). The fact `replay_closed_after_failed_body`
needs: the admitted turn matched the pre-state nonce, so after the tick it cannot match again. -/
theorem admissible_nonceMatch (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hadm : admissible ctx h s = true) : h.nonce = storedNonce s h.agent := by
  by_contra hbad
  rw [admissible_rejects_replay ctx h s hbad] at hadm
  exact absurd hadm (by simp)

/-! ## §4 — `commitPrologue`: the NEVER-rolled-back fee-debit + nonce-tick.

`execute.rs:182-195`, "PHASE 1: Commit fee + nonce (NEVER rolled back)." We edit ONLY the agent
cell: subtract the fee from its `balance` field and bump its `nonce` field by one. NO other cell, NO
authority graph, NO receipt-chain row (the prologue is the audit's PRE-amble — the body's commit
appends the receipt). The two edits compose on the same agent cell (`setNonce` after `setBalance`),
both via the named-field writes proven in `RecordKernel`/`EffectTransfer`. -/

/-- The agent cell after the prologue edit: balance −= fee, nonce += 1 (the OTHER fields, and every
OTHER cell, are untouched). -/
def prologueCell (v : Value) (fee : Int) : Value :=
  setNonce (setBalance v (balOf v - fee)) (nonceOf v + 1)

/-- **`commitPrologue` — the committed fee-debit + nonce-tick on the agent cell.** Edits the kernel's
`cell` function at `agent` only (`Function.update`-style), leaving `accounts`/`caps`/`log`/every
other cell unchanged. This is the state the body then runs against — and the state that PERSISTS
when the body fails (NEVER rolled back). -/
def commitPrologue (s : RecChainedState) (agent : CellId) (fee : Int) : RecChainedState :=
  { s with kernel := { s.kernel with
      cell := fun c => if c = agent then prologueCell (s.kernel.cell agent) fee
                       else s.kernel.cell c } }

/-- **`commitPrologue_nonce` — PROVED (the nonce TICKS by one).** After the prologue the agent's
stored nonce is exactly its old value `+ 1` — so the SAME-nonce turn is no longer admissible. -/
theorem commitPrologue_nonce (s : RecChainedState) (agent : CellId) (fee : Int) :
    nonceOf ((commitPrologue s agent fee).kernel.cell agent)
      = nonceOf (s.kernel.cell agent) + 1 := by
  simp only [commitPrologue, prologueCell, if_true]
  rw [setNonce_nonceOf]

/-- **`commitPrologue_balance` — PROVED (the fee is DEBITED).** After the prologue the agent's stored
balance is exactly its old value `− fee` — the fee is genuinely spent. (The `nonce` write does not
disturb the `balance` field: `setNonce` touches only `nonce`.) -/
theorem commitPrologue_balance (s : RecChainedState) (agent : CellId) (fee : Int) :
    balOf ((commitPrologue s agent fee).kernel.cell agent)
      = balOf (s.kernel.cell agent) - fee := by
  simp only [commitPrologue, prologueCell, if_true]
  rw [setNonce_balOf, setBalance_balOf]

/-- **`commitPrologue_frame` — PROVED (the FRAME).** The prologue touches ONLY the agent cell: every
OTHER cell's `Value` is byte-identical before and after. So the prologue is genuinely a single-cell
edit (no collateral mutation). -/
theorem commitPrologue_frame (s : RecChainedState) (agent : CellId) (fee : Int)
    (c : CellId) (hne : c ≠ agent) :
    (commitPrologue s agent fee).kernel.cell c = s.kernel.cell c := by
  simp only [commitPrologue]; rw [if_neg hne]

/-- **`commitPrologue_accounts` — PROVED (the account set is FIXED).** The prologue grows/shrinks no
accounts — it only re-prices an existing cell. -/
theorem commitPrologue_accounts (s : RecChainedState) (agent : CellId) (fee : Int) :
    (commitPrologue s agent fee).kernel.accounts = s.kernel.accounts := rfl

/-- **`commitPrologue_log` — PROVED (the prologue appends NO receipt).** The prologue is the
pre-amble: it edits state but leaves the receipt chain to the body's commit. The log is unchanged. -/
theorem commitPrologue_log (s : RecChainedState) (agent : CellId) (fee : Int) :
    (commitPrologue s agent fee).log = s.log := rfl

/-! ## §5 — `runTurn`: admissible-gate ∘ committed-prologue ∘ rollback-able body.

The full prologue-then-body shape of `execute.rs`. `body : RecChainedState → Option RecChainedState`
is the kernel forest fold (e.g. `FullForestAuth.execFullForestG`, projected to a pre-state→post
function) — ROLLBACK-ABLE: a `none` discards the body's edits. But the prologue is NOT rolled back.
Concretely: gate on `admissible`; if it fails, REJECT (`none`, NO state edit — the agent is NOT
charged, the pre-flight legs caught it). If it passes, COMMIT the prologue, then run the body
AGAINST the post-prologue state. On body success, return the body's state. On body FAILURE, return
the PROLOGUE state (fee spent, nonce ticked) — NOT the original `s`. THAT is the never-rolled-back
commit, and the heart of the anti-DoS guarantee. -/

/-- **`runTurn` — the prologue-then-body executor.**
  * `admissible` fails ⇒ `none` (rejected pre-flight; NO state edit, the agent is untouched);
  * `admissible` holds ⇒ commit the prologue, then run the body against the post-prologue state:
      * body commits (`some s'`) ⇒ `some s'` (the body's post-state, prologue already folded in);
      * body fails  (`none`)    ⇒ `some (commitPrologue …)` — **the prologue SURVIVES**: the turn
        "succeeds" at the ledger level (fee charged, nonce ticked) even though its body did nothing.
This is the committed-prologue ∘ rollback-able-body shape — NOT the pure all-or-nothing fold. -/
def runTurn (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) : Option RecChainedState :=
  if admissible ctx h s = true then
    let s₁ := commitPrologue s h.agent h.fee
    match body s₁ with
    | some s' => some s'
    | none    => some s₁          -- prologue NEVER rolled back
  else
    none

/-! ## §6 — The committed prologue ∘ rollback-able body, PROVED.

The crux: on an admissible turn, whatever the body does, the prologue's fee-debit + nonce-tick are
in the result. We prove it for the FAILED-body case (where the all-or-nothing fold would lose them)
and for the COMMITTING-body case (where the body runs on top of the prologue). -/

/-- The post-prologue state a `runTurn` commits to when the body FAILS — exactly `commitPrologue`. -/
theorem runTurn_failed_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    runTurn ctx h s body = some (commitPrologue s h.agent h.fee) := by
  simp only [runTurn, if_pos hadm, hbody]

/-- **`prologue_survives_failed_body` (KEYSTONE, PROVED) — THE STRUCTURAL CRUX.** On an admissible
turn whose BODY fails (`none`), `runTurn` STILL commits: the agent's balance dropped by EXACTLY the
fee AND its nonce ticked by EXACTLY one — the committed prologue is NEVER rolled back. This is the
property a pure all-or-nothing `Option`-fold provably does NOT have (`pure_fold_loses_prologue`
below): a failed turn here still SPENT THE FEE and TICKED THE NONCE. -/
theorem prologue_survives_failed_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    ∃ s', runTurn ctx h s body = some s' ∧
      balOf (s'.kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee ∧
      nonceOf (s'.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 := by
  refine ⟨commitPrologue s h.agent h.fee, runTurn_failed_body ctx h s body hadm hbody, ?_, ?_⟩
  · exact commitPrologue_balance s h.agent h.fee
  · exact commitPrologue_nonce s h.agent h.fee

/-- **`fee_spent_after_failed_body` (PROVED) — the ANTI-DoS guarantee.** A turn whose body fails STILL
debited the fee: the agent's balance after `runTurn` is its pre-balance MINUS the fee. An attacker
cannot submit an expensive-but-failing turn for free — it pays whether or not it does anything. -/
theorem fee_spent_after_failed_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    ∀ s', runTurn ctx h s body = some s' →
      balOf (s'.kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee := by
  intro s' hrun
  rw [runTurn_failed_body ctx h s body hadm hbody] at hrun
  cases hrun
  exact commitPrologue_balance s h.agent h.fee

/-- **`replay_closed_after_failed_body` (KEYSTONE, PROVED) — anti-replay SURVIVES a failed body.**
After a failed turn the agent's stored nonce STRICTLY advanced (by 1), so re-submitting the SAME
turn (same `nonce`) is no longer `admissible`: the `NonceMatch` leg now fails. A failed turn
therefore closes its own replay — the never-rolled-back nonce-tick is what makes replay-protection
robust against DoS. (Stated: at the post-state `s'`, the original `nonce` no longer matches the
stored nonce, hence `admissible` at `s'` is `false`.) -/
theorem replay_closed_after_failed_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    ∀ s', runTurn ctx h s body = some s' → admissible ctx h s' = false := by
  intro s' hrun
  rw [runTurn_failed_body ctx h s body hadm hbody] at hrun
  cases hrun
  -- the nonce ticked, so `h.nonce = storedNonce s' h.agent` is impossible.
  apply admissible_rejects_replay
  -- `h.nonce = storedNonce s` (admissible at s) but `storedNonce s' = storedNonce s + 1`.
  have hmatch : h.nonce = storedNonce s h.agent := admissible_nonceMatch ctx h s hadm
  have htick : storedNonce (commitPrologue s h.agent h.fee) h.agent = storedNonce s h.agent + 1 := by
    unfold storedNonce; exact commitPrologue_nonce s h.agent h.fee
  rw [htick, hmatch]; omega

/-- **`prologue_then_commit` (PROVED) — the prologue is IN FRONT OF, not instead of, the kernel
fold.** On an admissible turn whose body COMMITS, `runTurn` returns exactly the body's post-state —
where the body has already run on the post-prologue state. So a successful turn is "prologue, then
body": the fee/nonce edit precedes the kernel fold, never replaces it. -/
theorem prologue_then_commit (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) (s' : RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = some s') :
    runTurn ctx h s body = some s' := by
  simp only [runTurn, if_pos hadm, hbody]

/-- **`runTurn_inadmissible_rejects` (PROVED) — fail-closed at the gate.** An INADMISSIBLE turn is
rejected with NO state edit: `runTurn = none`, so the agent is NEVER charged for a turn that fails a
pre-flight gate (replay / expiry / underfunded / frozen / fork / over-budget / empty). The fee is
charged ONLY past the admission gate — the budget-exhaustion case is "not the agent's fault." -/
theorem runTurn_inadmissible_rejects (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hbad : admissible ctx h s = false) : runTurn ctx h s body = none := by
  simp only [runTurn, hbad]; rfl

/-! ## §7 — The asymmetry, PROVED: a pure all-or-nothing fold LOSES the prologue.

To make "admission breaks purity" a THEOREM rather than a comment, we exhibit the naive design — the
pure `Option`-monad bind that treats the prologue as just-another-rollback-able-step — and prove it
DISCARDS the fee/nonce edit on a body `none`. The contrast with `prologue_survives_failed_body` is
the whole point of FILL H. -/

/-- The NAIVE pure all-or-nothing turn: prologue and body in ONE `Option`-bind, so a body `none`
rolls EVERYTHING back to the original `s` (the prologue included). This is the WRONG design — it is
exactly `execFullTurn`'s discipline misapplied to the fee/nonce commit. -/
def runTurnPure (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) : Option RecChainedState :=
  if admissible ctx h s = true then
    body (commitPrologue s h.agent h.fee)    -- body `none` ⇒ whole thing `none` ⇒ prologue lost
  else
    none

/-- **`pure_fold_loses_prologue` (PROVED) — the asymmetry, as a theorem.** The naive all-or-nothing
fold DISCARDS the prologue on a body `none`: `runTurnPure = none`, so NO fee is charged and NO nonce
ticks — the failed turn left the state UNTOUCHED, reopening both the DoS hole (free failing turns)
and the replay hole (the same turn is still admissible). Contrast `prologue_survives_failed_body`,
which commits the prologue regardless. The two together PROVE the prologue must sit OUTSIDE the
rollback-able fold. -/
theorem pure_fold_loses_prologue (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    runTurnPure ctx h s body = none ∧ runTurn ctx h s body ≠ none := by
  refine ⟨?_, ?_⟩
  · simp only [runTurnPure, if_pos hadm, hbody]
  · rw [runTurn_failed_body ctx h s body hadm hbody]; simp

/-! ## §8 — The receipt-chain self-binding, modeled (the P0-3 prevHash gate).

The `ChainHead` leg of `admissible` is the executable shadow of `execute.rs:145`'s
`check_previous_receipt_hash`: a turn's `prevReceipt` MUST equal the agent's stored head. We tie it
to `Receipt.wellLinked` (the §8 hash-linked chain): a turn that links onto the stored head, when its
NEW receipt is appended, keeps the chain WELL-LINKED — so admission's `ChainHead` gate is exactly
the structural precondition for the append-only `ReceiptChain` discipline. -/

/-- The agent's stored chain head as a `prevHash` candidate (the `none = genesis` convention of
`AdmCtx.storedHead`, mapped to the `Receipt.genesisSentinel`). -/
def headDigest (ctx : AdmCtx) : Nat :=
  match ctx.storedHead with | none => genesisSentinel | some d => d

/-- **`admissible_links_to_head` — PROVED.** An admissible turn whose stored head is `some d`
carries `prevReceipt = some d`: its claimed predecessor IS the stored head — exactly the link a new
receipt must record to extend the chain. (For `storedHead = none`, the genesis turn carries
`prevReceipt = none`.) The structural bridge: admission's `ChainHead` leg forces the new receipt's
`prevHash` to be the stored head's digest, so appending it preserves `wellLinked`. -/
theorem admissible_links_to_head (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hadm : admissible ctx h s = true) : h.prevReceipt = ctx.storedHead := by
  by_contra hfork
  rw [admissible_rejects_chain_fork ctx h s hfork] at hadm
  exact absurd hadm (by simp)

/-- The `prevHash` an admitted turn's NEW receipt must carry: the digest of the turn's claimed
predecessor (`none = genesis ⇒ sentinel`). Admissibility forces `prevReceipt = storedHead`, so this
equals `headDigest ctx` — that's the bridge below. -/
def turnPrevHash (h : TurnHdr) : Nat :=
  match h.prevReceipt with | none => genesisSentinel | some d => d

/-- **`admissible_prevHash_eq_head` — PROVED.** An admitted turn's `turnPrevHash` IS the stored head
digest `headDigest ctx` — because the `ChainHead` gate forced `prevReceipt = storedHead`. -/
theorem admissible_prevHash_eq_head (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hadm : admissible ctx h s = true) : turnPrevHash h = headDigest ctx := by
  unfold turnPrevHash headDigest
  rw [admissible_links_to_head ctx h s hadm]

/-- **`admissible_append_wellLinked` — PROVED (the §8 chain discipline bridge).** Take a well-linked
chain `chain` whose head digest is `headDigest ctx` (the agent's stored head; sentinel at genesis).
An ADMISSIBLE turn's new receipt — built with `prevHash := turnPrevHash h` (the turn's own claimed
predecessor) — EXTENDS the chain preserving `wellLinked`. The load-bearing fact is `hadm`: admission
FORCES the new receipt's `prevHash` to be exactly the stored head, so the append links correctly. A
turn that LIED about its predecessor would be INADMISSIBLE (`admissible_rejects_chain_fork`), so it
never reaches this append — that is why the `ChainHead` gate is precisely the precondition for the
append-only, tamper-evident `ReceiptChain` (`Receipt.chain_tamper_evident`'s well-linkedness hyp). -/
theorem admissible_append_wellLinked (H : Receipt → Nat) (ctx : AdmCtx) (h : TurnHdr)
    (s : RecChainedState) (chain : ReceiptChain) (r : Receipt)
    (hadm : admissible ctx h s = true)
    (hwl : wellLinked H chain)
    (hhead : (match chain with | [] => genesisSentinel | g :: _ => H g) = headDigest ctx)
    (hr : r.prevHash = turnPrevHash h) :
    wellLinked H (r :: chain) := by
  -- admission forces the turn's claimed predecessor to be the stored head.
  have hlink : r.prevHash = headDigest ctx := by
    rw [hr, admissible_prevHash_eq_head ctx h s hadm]
  cases chain with
  | nil =>
    -- empty chain ⇒ headDigest must be the sentinel (genesis); r pins it.
    simp only at hhead
    show r.prevHash = genesisSentinel
    rw [hlink, ← hhead]
  | cons g rest =>
    -- non-empty ⇒ r links onto g via H g = headDigest; the tail is already well-linked.
    simp only at hhead
    show r.prevHash = H g ∧ wellLinked H (g :: rest)
    exact ⟨by rw [hlink, ← hhead], hwl⟩

/-! ## §9 — Axiom-hygiene tripwires (the honesty pins over the admission keystones). -/

#assert_axioms admissible_rejects_empty
#assert_axioms admissible_rejects_expired
#assert_axioms admissible_rejects_replay
#assert_axioms admissible_rejects_underfunded
#assert_axioms admissible_rejects_frozen
#assert_axioms admissible_rejects_frozen_writeset
#assert_axioms admissible_rejects_chain_fork
#assert_axioms admissible_rejects_over_budget
#assert_axioms admissible_rejects_no_agent
#assert_axioms admissible_nonceMatch
#assert_axioms admissible_prevHash_eq_head
#assert_axioms commitPrologue_nonce
#assert_axioms commitPrologue_balance
#assert_axioms commitPrologue_frame
#assert_axioms runTurn_failed_body
#assert_axioms prologue_survives_failed_body
#assert_axioms fee_spent_after_failed_body
#assert_axioms replay_closed_after_failed_body
#assert_axioms prologue_then_commit
#assert_axioms runTurn_inadmissible_rejects
#assert_axioms pure_fold_loses_prologue
#assert_axioms admissible_links_to_head
#assert_axioms admissible_append_wellLinked

/-! ## §10 — Non-vacuity: it RUNS (`#eval`) — admit/reject, the never-rolled-back prologue, replay.

A concrete agent cell (cell 7, balance 100, nonce 3) and a host context (now 50, no frozen cells,
stored head `some 42`, budget 1000). A well-formed turn (nonce 3, fee 10, prevReceipt 42, non-empty
forest) is admissible; each malformed variant is rejected. The prologue debits 10 and ticks the
nonce to 4 — and SURVIVES a failed body. -/

/-- A test pre-state: cell 7 holds balance 100, nonce 3 (a live account). -/
def as0 : RecChainedState :=
  { kernel := { accounts := {7}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 100), ("nonce", .int 3)]
                                 else .record [] },
    log := [] }

/-- The host context: clock 50, nothing frozen, stored head `some 42`, budget 1000. -/
def ac0 : AdmCtx := { now := 50, frozen := [], storedHead := some 42, budget := 1000 }

/-- A well-formed turn header: agent 7, nonce 3 (matches), fee 10, valid until 100 (not expired),
prevReceipt 42 (matches the head), write-set {7}, non-empty forest. -/
def ah0 : TurnHdr :=
  { agent := 7, nonce := 3, fee := 10, validUntil := some 100, prevReceipt := some 42,
    writeSet := [7], forestNonEmpty := true }

#eval admissible ac0 ah0 as0                                            -- true  (admissible)
#eval admissible ac0 { ah0 with forestNonEmpty := false } as0          -- false (EmptyForest)
#eval admissible ac0 { ah0 with nonce := 99 } as0                      -- false (replay)
#eval admissible ac0 { ah0 with fee := 500 } as0                       -- false (underfunded)
#eval admissible ac0 { ah0 with validUntil := some 10 } as0            -- false (expired: now 50 > 10)
#eval admissible ac0 { ah0 with prevReceipt := some 99 } as0           -- false (chain fork)
#eval admissible { ac0 with frozen := [7] } ah0 as0                    -- false (agent frozen)
#eval admissible { ac0 with budget := 5 } ah0 as0                      -- false (over budget: 10 > 5)
#eval admissible { ac0 with storedHead := none } ah0 as0               -- false (fork: head is genesis)

-- The committed prologue: balance 100 → 90, nonce 3 → 4.
#eval balOf ((commitPrologue as0 7 10).kernel.cell 7)                  -- 90
#eval nonceOf ((commitPrologue as0 7 10).kernel.cell 7)               -- 4
-- Frame: cell 7 is the ONLY cell touched (cell 1 unchanged — empty record reads 0).
#eval balOf ((commitPrologue as0 7 10).kernel.cell 1)                 -- 0

-- The prologue SURVIVES a failed body (`runTurn` with a body that always fails):
#eval (runTurn ac0 ah0 as0 (fun _ => none)).isSome                    -- true  (committed anyway!)
#eval (runTurn ac0 ah0 as0 (fun _ => none)).map
        (fun s' => (balOf (s'.kernel.cell 7), nonceOf (s'.kernel.cell 7)))  -- some (90, 4)
-- ...whereas the NAIVE pure fold LOSES it (rolls everything back):
#eval (runTurnPure ac0 ah0 as0 (fun _ => none)).isSome                 -- false (prologue lost!)

-- A committing body runs ON TOP of the prologue (identity body keeps the post-prologue state):
#eval (runTurn ac0 ah0 as0 (fun s => some s)).map
        (fun s' => (balOf (s'.kernel.cell 7), nonceOf (s'.kernel.cell 7)))  -- some (90, 4)

-- Replay closed: after the failed turn, the SAME header is no longer admissible (nonce advanced):
#eval ((runTurn ac0 ah0 as0 (fun _ => none)).map (fun s' => admissible ac0 ah0 s'))  -- some false

-- An inadmissible turn is rejected with NO state edit (the agent is never charged):
#eval (runTurn ac0 { ah0 with nonce := 99 } as0 (fun _ => none)).isSome  -- false

end Dregg2.Exec.Admission
