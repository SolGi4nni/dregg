/-
# Dregg2.Exec.Admission — the fail-closed turn prologue.

`execute.rs:54-195` runs a prologue before the call-forest fold: eleven turn-level admission gates
followed by a **committed fee-debit + nonce-tick that is NEVER rolled back** (dregg1 "PHASE 1").
The forest body is rollback-able; the prologue is not — the opposite of a pure all-or-nothing fold.

This module is that prologue as a Lean law, sitting beside the kernel fold. It fixes the key
Lean-vs-Rust mismatch: `execFullTurnG s [] = some s` (the verified fold admits the empty turn)
whereas dregg1 rejects it (`execute.rs:56`, `TurnError::EmptyForest`). `admissible` requires a
non-empty forest, fail-closed.

Headline theorems (no `sorry`/`axiom`/`admit`/`native_decide`):
  * admission rejection theorems — each gate rejects the violating case.
  * `prologue_survives_failed_body` — on a failed body the fee is still debited and the nonce still
    ticks; `replay_closed_after_failed_body` and `fee_spent_after_failed_body` follow.
  * `pure_fold_loses_prologue` — the naive all-or-nothing fold DISCARDS the prologue on a body
    `none`: the asymmetry is a theorem, not a comment.

`#assert_axioms` on every keystone. Pure, computable, `#eval`-able. Reuses `RecordKernel`,
`EffectTransfer`, and `Receipt`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectTransfer
import Dregg2.Exec.Receipt

namespace Dregg2.Exec.Admission

open Dregg2.Exec
open Dregg2.Exec.EffectTransfer (nonceOf setNonce setNonce_nonceOf setNonce_balOf)
open Dregg2.Exec.Receipts (Receipt ReceiptChain genesisSentinel wellLinked)

/-! ## §1 — The host-fed admission context.

`execute.rs` reads these from `self` / the wider executor, not from the turn. Modeling them as an
explicit `AdmCtx` keeps the prologue a pure function of (turn-fields, host-context, pre-state) —
exactly the seam the FFI marshaller crosses. -/

/-- The host-fed admission context (the bits of `self` that `execute.rs:54-177` reads):
  * `now`        — the executor clock (`self.current_timestamp`), checked against `validUntil`;
  * `frozen`     — the migration freeze-set (`self.frozen_cells`); a turn touching any frozen cell
                   is rejected;
  * `storedHead` — the agent's stored receipt-chain head (`self.receipt_heads[agent]`), the P0-3
                   self-binding; `none` = the agent's genesis turn;
  * `budget`     — the Stingray silo budget slice; the fee must fit. -/
structure AdmCtx where
  now        : Nat
  frozen     : List CellId
  storedHead : Option Nat
  budget     : Nat
deriving Repr

/-- The turn-level fields the prologue gates against: `agent`, `nonce`, `fee`, `valid_until`,
`previous_receipt_hash`, and the write-set extracted from the call-forest. The forest itself is the
kernel fold's concern; the prologue needs only its non-emptiness and its write-set. -/
structure TurnHdr where
  agent      : CellId
  nonce      : Int
  fee        : Int
  validUntil : Option Nat
  prevReceipt : Option Nat
  /-- The cells the call-forest writes (`conflict::extract_access_sets`). -/
  writeSet   : List CellId
  /-- Whether the forest is non-empty — the empty-forest gate (`execute.rs:56`). A turn with an
  empty forest carries `forestNonEmpty = false` and is rejected. -/
  forestNonEmpty : Bool
deriving Repr

/-! ## §2 — `admissible`: the fail-closed admission predicate.

The eleven Rust gates collapse to eight decidable conjuncts, `&&`-folded so any false leg yields
`false`. The pre-state `s` supplies the agent's stored nonce + balance. -/

/-- Read the agent cell's stored nonce from the pre-state (the metadata measure `nonceOf`). -/
def storedNonce (s : RecChainedState) (agent : CellId) : Int := nonceOf (s.kernel.cell agent)

/-- Read the agent cell's stored balance from the pre-state (the conserved measure `balOf`). -/
def storedBalance (s : RecChainedState) (agent : CellId) : Int := balOf (s.kernel.cell agent)

/-- A cell is FROZEN when it is in the host freeze-set. -/
def isFrozen (ctx : AdmCtx) (c : CellId) : Bool := ctx.frozen.contains c

/-- The fail-closed admission predicate. True iff every gate passes:
  1. **EmptyForest** — `h.forestNonEmpty` (empty turn is inadmissible);
  2. **AgentLive**   — `agent ∈ accounts`;
  3. **Expiry**      — `validUntil = none ∨ now ≤ validUntil`;
  4. **NonceMatch**  — `nonce = storedNonce` (replay check);
  5. **FeeCoverage** — `0 ≤ fee ∧ fee ≤ storedBalance`;
  6. **NotFrozen**   — `agent` and every write-set cell ∉ freeze-set;
  7. **ChainHead**   — `prevReceipt = storedHead` (P0-3 receipt-chain self-binding);
  8. **Budget**      — `fee ≤ budget` (Stingray silo slice). -/
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

/-! ## §3 — Admission rejection theorems: each gate has real teeth.

Each theorem exhibits a turn that violates exactly one leg and is therefore inadmissible — the
predicate is fail-closed on every gate, not a vacuous `true`. -/

/-- A turn with an empty forest (`forestNonEmpty = false`) is inadmissible. This closes the
mismatch where the verified fold admits the empty turn but dregg1 rejects it. -/
theorem admissible_rejects_empty (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hempty : h.forestNonEmpty = false) : admissible ctx h s = false := by
  simp [admissible, hempty]

/-- `now > validUntil` implies inadmissible. -/
theorem admissible_rejects_expired (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (vu : Nat) (hvu : h.validUntil = some vu) (hexp : ctx.now > vu) :
    admissible ctx h s = false := by
  simp only [admissible, hvu]
  have : decide (ctx.now ≤ vu) = false := by simp; omega
  simp [this]

/-- A turn whose `nonce` does not match the agent's stored nonce is inadmissible (replay gate). -/
theorem admissible_rejects_replay (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hbad : h.nonce ≠ storedNonce s h.agent) : admissible ctx h s = false := by
  simp [admissible, hbad]

/-- `storedBalance < fee` implies inadmissible. The agent cannot pay more than it holds. -/
theorem admissible_rejects_underfunded (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hpoor : storedBalance s h.agent < h.fee) : admissible ctx h s = false := by
  simp only [admissible]
  have : decide (h.fee ≤ storedBalance s h.agent) = false := by simp; omega
  simp [this]

/-- If the agent cell is in the freeze-set, the turn is inadmissible. -/
theorem admissible_rejects_frozen (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hfrozen : isFrozen ctx h.agent = true) : admissible ctx h s = false := by
  simp [admissible, hfrozen]

/-- If any cell in the call-forest write-set is frozen, the turn is inadmissible. -/
theorem admissible_rejects_frozen_writeset (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (c : CellId) (hmem : c ∈ h.writeSet) (hfrozen : isFrozen ctx c = true) :
    admissible ctx h s = false := by
  simp only [admissible]
  have hall : h.writeSet.all (fun c => !isFrozen ctx c) = false := by
    rw [List.all_eq_false]
    exact ⟨c, hmem, by simp [hfrozen]⟩
  simp [hall]

/-- If `prevReceipt` ≠ the stored chain head, the turn is inadmissible. You cannot link a turn
onto a head you do not hold (P0-3 receipt-chain self-binding). -/
theorem admissible_rejects_chain_fork (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hfork : h.prevReceipt ≠ ctx.storedHead) : admissible ctx h s = false := by
  simp [admissible, hfork]

/-- If the fee exceeds the silo's budget slice, the turn is inadmissible — rejected without
charging the agent (a silo-level resource limit). -/
theorem admissible_rejects_over_budget (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hover : h.fee > (ctx.budget : Int)) : admissible ctx h s = false := by
  simp only [admissible]
  have : decide (h.fee ≤ (ctx.budget : Int)) = false := by simp; omega
  simp [this]

/-- A turn whose agent cell is not a live account is inadmissible. -/
theorem admissible_rejects_no_agent (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hgone : h.agent ∉ s.kernel.accounts) : admissible ctx h s = false := by
  simp [admissible, hgone]

/-! ### §3b — Admission extractions: from `admissible = true`, recover each gate's fact.

Duals of §3's rejections, proved by contraposition. -/

/-- An admissible turn's `nonce` equals the agent's stored nonce (contrapositive of
`admissible_rejects_replay`). Used by `replay_closed_after_failed_body`: after the nonce ticks,
the same nonce can never match again. -/
theorem admissible_nonceMatch (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hadm : admissible ctx h s = true) : h.nonce = storedNonce s h.agent := by
  by_contra hbad
  rw [admissible_rejects_replay ctx h s hbad] at hadm
  exact absurd hadm (by simp)

/-! ## §4 — `commitPrologue`: the never-rolled-back fee-debit + nonce-tick.

`execute.rs:182-195` "PHASE 1: Commit fee + nonce (NEVER rolled back)." We edit only the agent
cell: subtract the fee from `balance` and bump `nonce` by one. No other cell, no authority graph,
no receipt-chain row (the body's commit appends the receipt). -/

/-- The agent cell after the prologue edit: balance −= fee, nonce += 1. All other fields and cells
are untouched. -/
def prologueCell (v : Value) (fee : Int) : Value :=
  setNonce (setBalance v (balOf v - fee)) (nonceOf v + 1)

/-- The committed fee-debit + nonce-tick on the agent cell. Edits `cell` at `agent` only, leaving
`accounts`/`caps`/`log`/every other cell unchanged. This is the state that persists when the body
fails — it is never rolled back. -/
def commitPrologue (s : RecChainedState) (agent : CellId) (fee : Int) : RecChainedState :=
  { s with kernel := { s.kernel with
      cell := fun c => if c = agent then prologueCell (s.kernel.cell agent) fee
                       else s.kernel.cell c } }

/-- After the prologue the agent's nonce equals its old value + 1, so the same-nonce turn is no
longer admissible. -/
theorem commitPrologue_nonce (s : RecChainedState) (agent : CellId) (fee : Int) :
    nonceOf ((commitPrologue s agent fee).kernel.cell agent)
      = nonceOf (s.kernel.cell agent) + 1 := by
  simp only [commitPrologue, prologueCell, if_true]
  rw [setNonce_nonceOf]

/-- After the prologue the agent's balance equals its old value − fee. (`setNonce` touches only
`nonce`, so the balance field is undisturbed by the nonce write.) -/
theorem commitPrologue_balance (s : RecChainedState) (agent : CellId) (fee : Int) :
    balOf ((commitPrologue s agent fee).kernel.cell agent)
      = balOf (s.kernel.cell agent) - fee := by
  simp only [commitPrologue, prologueCell, if_true]
  rw [setNonce_balOf, setBalance_balOf]

/-- The prologue touches only the agent cell: every other cell's `Value` is unchanged. -/
theorem commitPrologue_frame (s : RecChainedState) (agent : CellId) (fee : Int)
    (c : CellId) (hne : c ≠ agent) :
    (commitPrologue s agent fee).kernel.cell c = s.kernel.cell c := by
  simp only [commitPrologue]; rw [if_neg hne]

/-- The prologue does not grow or shrink the account set — it only reprices an existing cell. -/
theorem commitPrologue_accounts (s : RecChainedState) (agent : CellId) (fee : Int) :
    (commitPrologue s agent fee).kernel.accounts = s.kernel.accounts := rfl

/-- The prologue appends no receipt: it edits state but leaves the receipt chain to the body. -/
theorem commitPrologue_log (s : RecChainedState) (agent : CellId) (fee : Int) :
    (commitPrologue s agent fee).log = s.log := rfl

/-! ## §5 — `runTurn`: admissible-gate ∘ committed-prologue ∘ rollback-able body.

The full prologue-then-body shape of `execute.rs`. The `body` is the kernel forest fold —
rollback-able (`none` discards its edits). The prologue is NOT rolled back. If `admissible` fails,
return `none` with no state edit. If it passes, commit the prologue, then run the body against the
post-prologue state. On body success return the body's state; on body failure return the prologue
state (fee spent, nonce ticked) — the never-rolled-back anti-DoS commit. -/

/-- The prologue-then-body executor. If `admissible` fails, returns `none` (no state edit). If it
holds, commits the prologue, then runs `body`: on `some s'` returns `s'`; on `none` returns
`some (commitPrologue …)` — the prologue survives the body failure (fee charged, nonce ticked). -/
def runTurn (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) : Option RecChainedState :=
  if admissible ctx h s = true then
    let s₁ := commitPrologue s h.agent h.fee
    match body s₁ with
    | some s' => some s'
    | none    => some s₁          -- prologue NEVER rolled back
  else
    none

/-! ## §6 — The committed-prologue / rollback-able-body theorems.

On an admissible turn, the prologue's fee-debit + nonce-tick are in the result regardless of what
the body does. We prove both the failed-body case (where an all-or-nothing fold would lose them)
and the committing-body case. -/

/-- The post-prologue state a `runTurn` commits to when the body FAILS — exactly `commitPrologue`. -/
theorem runTurn_failed_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    runTurn ctx h s body = some (commitPrologue s h.agent h.fee) := by
  simp only [runTurn, if_pos hadm, hbody]

/-- On an admissible turn whose body fails, `runTurn` still commits: balance dropped by the fee and
nonce ticked by one. The committed prologue is never rolled back. A pure all-or-nothing fold would
not have this property (`pure_fold_loses_prologue`). -/
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

/-- Anti-DoS: a turn whose body fails still debited the fee. The agent cannot submit an
expensive-but-failing turn for free — it pays whether or not the body does anything. -/
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

/-- Anti-replay survives a failed body: after a failed turn the nonce advanced, so the same turn is
no longer admissible (`NonceMatch` fails). A failed turn closes its own replay window. -/
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

/-- On an admissible turn whose body commits, `runTurn` returns the body's post-state, which ran
on the post-prologue state. The prologue precedes the kernel fold, never replaces it. -/
theorem prologue_then_commit (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) (s' : RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = some s') :
    runTurn ctx h s body = some s' := by
  simp only [runTurn, if_pos hadm, hbody]

/-- An inadmissible turn is rejected with no state edit: `runTurn = none`. The agent is never
charged for a turn that fails a pre-flight gate. -/
theorem runTurn_inadmissible_rejects (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hbad : admissible ctx h s = false) : runTurn ctx h s body = none := by
  simp only [runTurn, hbad]; rfl

/-! ## §7 — The asymmetry as a theorem: a pure fold loses the prologue.

We exhibit the naive design — the pure `Option`-monad bind — and prove it discards the fee/nonce
edit on a body `none`. The contrast with `prologue_survives_failed_body` is the point. -/

/-- The naive pure all-or-nothing turn: prologue and body in one `Option`-bind, so a body `none`
rolls everything back including the prologue. This is the wrong design for fee/nonce commits. -/
def runTurnPure (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState) : Option RecChainedState :=
  if admissible ctx h s = true then
    body (commitPrologue s h.agent h.fee)    -- body `none` ⇒ whole thing `none` ⇒ prologue lost
  else
    none

/-- The naive fold discards the prologue on a body `none`: `runTurnPure = none` (no fee charged, no
nonce tick), while `runTurn` still commits. Together, these prove the prologue must sit outside the
rollback-able fold. -/
theorem pure_fold_loses_prologue (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (body : RecChainedState → Option RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : body (commitPrologue s h.agent h.fee) = none) :
    runTurnPure ctx h s body = none ∧ runTurn ctx h s body ≠ none := by
  refine ⟨?_, ?_⟩
  · simp only [runTurnPure, if_pos hadm, hbody]
  · rw [runTurn_failed_body ctx h s body hadm hbody]; simp

/-! ## §8 — The receipt-chain self-binding (the P0-3 prevHash gate).

The `ChainHead` leg of `admissible` mirrors `execute.rs:145`'s `check_previous_receipt_hash`: a
turn's `prevReceipt` must equal the agent's stored head. We connect it to `Receipt.wellLinked`: a
turn that links onto the stored head, when its new receipt is appended, keeps the chain well-linked.
The `ChainHead` gate is exactly the precondition for the append-only `ReceiptChain` discipline. -/

/-- The agent's stored chain head as a `prevHash` candidate (the `none = genesis` convention of
`AdmCtx.storedHead`, mapped to the `Receipt.genesisSentinel`). -/
def headDigest (ctx : AdmCtx) : Nat :=
  match ctx.storedHead with | none => genesisSentinel | some d => d

/-- An admissible turn carries `prevReceipt = storedHead`: the claimed predecessor is the stored
head — exactly the link a new receipt must record to extend the chain. Admission's `ChainHead` leg
forces the new receipt's `prevHash` to be the stored head's digest, preserving `wellLinked`. -/
theorem admissible_links_to_head (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hadm : admissible ctx h s = true) : h.prevReceipt = ctx.storedHead := by
  by_contra hfork
  rw [admissible_rejects_chain_fork ctx h s hfork] at hadm
  exact absurd hadm (by simp)

/-- The `prevHash` an admitted turn's new receipt must carry: digest of the claimed predecessor
(`none = genesis ⇒ sentinel`). Admissibility forces `prevReceipt = storedHead`, so this equals
`headDigest ctx`. -/
def turnPrevHash (h : TurnHdr) : Nat :=
  match h.prevReceipt with | none => genesisSentinel | some d => d

/-- An admitted turn's `turnPrevHash` equals `headDigest ctx` (the `ChainHead` gate forced
`prevReceipt = storedHead`). -/
theorem admissible_prevHash_eq_head (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hadm : admissible ctx h s = true) : turnPrevHash h = headDigest ctx := by
  unfold turnPrevHash headDigest
  rw [admissible_links_to_head ctx h s hadm]

/-- An admissible turn's new receipt extends a well-linked chain preserving `wellLinked`. Admission
forces `prevHash = headDigest ctx`, so the append links correctly. A turn that lied about its
predecessor would be inadmissible (`admissible_rejects_chain_fork`), so the `ChainHead` gate is the
exact precondition for the append-only, tamper-evident `ReceiptChain`. -/
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

/-! ## §9 — Axiom-hygiene tripwires. -/

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

/-! ## §10 — Non-vacuity (`#eval`): admit/reject, the never-rolled-back prologue, replay.

Agent cell 7 (balance 100, nonce 3), host context (now 50, no frozen cells, head `some 42`,
budget 1000). A well-formed turn is admissible; each malformed variant is rejected. The prologue
debits 10 and ticks the nonce to 4, and survives a failed body. -/

/-- Pre-state: cell 7 holds balance 100, nonce 3 (a live account). -/
def as0 : RecChainedState :=
  { kernel := { accounts := {7}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 100), ("nonce", .int 3)]
                                 else .record [] },
    log := [] }

/-- Host context: clock 50, nothing frozen, stored head `some 42`, budget 1000. -/
def ac0 : AdmCtx := { now := 50, frozen := [], storedHead := some 42, budget := 1000 }

/-- Well-formed turn header: agent 7, nonce 3 (matches), fee 10, valid until 100, prevReceipt 42
(matches head), write-set {7}, non-empty forest. -/
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
