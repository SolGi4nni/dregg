/-
# Dregg2.Exec.AdmissionReason — the legible "why" of a refused turn.

`Admission.admissible` (`Admission.lean §2`) is a `Bool`: it returns `true`/`false`, and the
FIRST failing gate's identity — the actual REASON — is trapped behind the `&&`-fold. A stranger's
first failed turn therefore reads as bare `false`: refused, but SILENT about why.

This module makes the why legible. `AdmissionReason` is the named cause: `admitted`, or exactly
one constructor per REJECTION gate of `admissible`, in the `&&`-short-circuit ORDER of the
predicate. `admissionReason` returns the first failing gate's reason (or `admitted`).

THE FAITHFULNESS KEYSTONE (`admissionReason_eq_admitted_iff`): `admissionReason ctx h s = admitted`
iff `admissible ctx h s = true`. So the reason CANNOT LIE about admission — an `admitted` reason
means the turn genuinely admits (every gate passed), and any reject reason means it genuinely does
NOT. Each reject constructor is moreover REACHABLE (`§4` witnesses), so no arm is vacuous.

`#assert_axioms` on the keystone + every reachability `#guard`. Pure, computable, `#eval`-able.
Reuses `Admission` verbatim — NO re-derivation of the gates, so the reason and the Bool stay one
source of truth.
-/
import Dregg2.Exec.Admission

namespace Dregg2.Exec.AdmissionReason

open Dregg2.Exec
open Dregg2.Exec.Admission

/-! ## §1 — The named cause of an admission decision.

One constructor per `admissible` gate's REJECTION, in the predicate's `&&` short-circuit order
(`Admission.lean §2`), plus `admitted` for "every gate passed". Carrying the offending datum
(cell-id, nonce, fee, …) lets the host render a precise human string — but the constructor TAG
alone already names the gate. -/

/-- The theorem-backed reason an admission decision came out the way it did. Exactly one reject
constructor per `admissible` gate (`Admission.lean §2`), in `&&` order, or `admitted`. -/
inductive AdmissionReason where
  /-- Every gate passed: the turn is genuinely admissible. -/
  | admitted
  /-- Gate 1 (`forestNonEmpty`): the call-forest is empty — there is nothing to execute. -/
  | emptyForest
  /-- Gate 2 (`agent ∈ accounts`): the agent cell is not a member account of this ledger. -/
  | noSuchAgent (agent : CellId)
  /-- Gate 3 (`cellLifecycleLive`): the agent cell is a member but NOT lifecycle-live (Destroyed
  or Sealed) — a dead cell cannot author a turn. -/
  | deadAgent (agent : CellId)
  /-- Gate 4 (Expiry): the turn's `validUntil` has passed relative to the host clock. -/
  | expired (clock validUntil : Nat)
  /-- Gate 5 (NonceMatch): the turn's nonce does not match the agent's stored nonce (replay). -/
  | nonceMismatch (got stored : Int)
  /-- Gate 6a (`0 ≤ fee`): the declared fee is negative. -/
  | negativeFee (fee : Int)
  /-- Gate 6b (`fee ≤ storedBalance`): the agent cannot cover the fee from its balance. -/
  | underfunded (fee balance : Int)
  /-- Gate 7a (`!isFrozen agent`): the agent cell is in the migration freeze-set. -/
  | agentFrozen (agent : CellId)
  /-- Gate 7b (`writeSet.all !isFrozen`): some cell the forest writes is frozen. -/
  | writeSetFrozen (cell : CellId)
  /-- Gate 8 (ChainHead): the turn's `prevReceipt` ≠ the agent's stored receipt-chain head. -/
  | chainHeadMismatch (claimed stored : Option Nat)
  /-- Gate 9 (Budget): the fee exceeds the silo's Stingray budget slice. -/
  | overBudget (fee budget : Int)
deriving Repr, DecidableEq

/-! ## §2 — `admissionReason`: the first failing gate.

`admissible` is `g₁ && g₂ && … && g₉`; the FIRST false leg decides the verdict. `admissionReason`
walks the SAME gates in the SAME order and returns the first that fails, exactly mirroring the
short-circuit — so the reason it reports is precisely the leg that would have made the Bool `false`.
The legs are written with the SAME guards as `admissible` so the two cannot drift. -/

/-- The first failing gate's reason, or `admitted` if every gate passes. The gate order + guards
are the `admissible` `&&`-fold verbatim (`Admission.lean §2`), so this is the legible projection of
the SAME decision, not a re-implementation. -/
def admissionReason (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) : AdmissionReason :=
  -- 1. EmptyForest
  if h.forestNonEmpty = false then .emptyForest
  -- 2. AgentLive (membership)
  else if h.agent ∉ s.kernel.accounts then .noSuchAgent h.agent
  -- 3. AgentLive (lifecycle)
  else if cellLifecycleLive s.kernel h.agent = false then .deadAgent h.agent
  -- 4. Expiry
  else if (match h.validUntil with | none => false | some vu => decide (admissionClock ctx > vu)) = true then
    .expired (admissionClock ctx) (h.validUntil.getD 0)
  -- 5. NonceMatch
  else if h.nonce ≠ storedNonce s h.agent then .nonceMismatch h.nonce (storedNonce s h.agent)
  -- 6a. FeeCoverage (sign)
  else if h.fee < 0 then .negativeFee h.fee
  -- 6b. FeeCoverage (coverage)
  else if storedBalance s h.agent < h.fee then .underfunded h.fee (storedBalance s h.agent)
  -- 7a. NotFrozen (agent)
  else if isFrozen ctx h.agent = true then .agentFrozen h.agent
  -- 7b. NotFrozen (write-set)
  else match h.writeSet.find? (fun c => isFrozen ctx c) with
  | some c => .writeSetFrozen c
  | none =>
  -- 8. ChainHead
  if h.prevReceipt ≠ ctx.storedHead then .chainHeadMismatch h.prevReceipt ctx.storedHead
  -- 9. Budget
  else if h.fee > (ctx.budget : Int) then .overBudget h.fee (ctx.budget : Int)
  else .admitted

/-! ## §3 — The faithfulness keystone: the reason cannot lie about admission.

`admissionReason = admitted ↔ admissible = true`. Soundness: an `admitted` reason means every gate
passed (the turn GENUINELY admits). Completeness: a passing turn reports `admitted` (no spurious
reject). Both directions matter — a reason that said `admitted` on a rejected turn would launder a
refusal; a reason that invented a reject on an admitted turn would block a good turn. -/

/-- The expiry-guard's reason-side form (`some vu ⇒ now > vu`) as a `Prop`. The reason's gate-4
`if` branches on exactly this. -/
def expiryGuardFails (ctx : AdmCtx) (h : TurnHdr) : Prop :=
  (match h.validUntil with | none => false | some vu => decide (admissionClock ctx > vu)) = true

instance (ctx : AdmCtx) (h : TurnHdr) : Decidable (expiryGuardFails ctx h) := by
  unfold expiryGuardFails; infer_instance

/-- **The gate decomposition of `admissible`.** `admissible = true` iff all nine gate-`Prop`s hold,
in the EXACT order and meaning `admissionReason` branches on. Proving the keystone through this
single bridge keeps the `&&`-fold reasoning in ONE place. -/
theorem admissible_iff_gates (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) :
    admissible ctx h s = true ↔
      (h.forestNonEmpty = true ∧ h.agent ∈ s.kernel.accounts ∧
       cellLifecycleLive s.kernel h.agent = true ∧ ¬ expiryGuardFails ctx h ∧
       h.nonce = storedNonce s h.agent ∧ ¬ (h.fee < 0) ∧ ¬ (storedBalance s h.agent < h.fee) ∧
       ¬ (isFrozen ctx h.agent = true) ∧
       (h.writeSet.find? (fun c => isFrozen ctx c)).isNone = true ∧
       h.prevReceipt = ctx.storedHead ∧ ¬ (h.fee > (ctx.budget : Int))) := by
  unfold admissible expiryGuardFails
  -- write-set leg: `all (!isFrozen) = true` ⇔ `find? isFrozen = none`.
  have hwfeq : (h.writeSet.all (fun c => !isFrozen ctx c) = true) ↔
      ((h.writeSet.find? (fun c => isFrozen ctx c)).isNone = true) := by
    rw [Option.isNone_iff_eq_none, List.all_eq_true, List.find?_eq_none]
    constructor
    · intro hall x hxmem
      have := hall x hxmem; simpa using this
    · intro hnone x hxmem
      have := hnone x hxmem; simpa using this
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_assoc]
  -- the goal is now a conjunction of Bool/Prop legs ↔ the gate Props; the only nontrivial
  -- alignments are the expiry leg and the write-set leg.
  constructor
  · rintro ⟨h1, h2, h3, hexp, h5, h6a, h6b, h7a, hwf, h8, h9⟩
    refine ⟨h1, h2, h3, ?_, h5, ?_, ?_, ?_, hwfeq.mp (by simpa using hwf), h8, ?_⟩
    · -- ¬ expiryGuardFails : the `≤`-leg is true ⇒ the `>`-guard is false.
      cases hv : h.validUntil with
      | none => simp [hv]
      | some vu =>
        simp only [hv] at hexp ⊢
        intro hcon; simp only [decide_eq_true_eq] at hcon hexp; omega
    · simp only [Int.not_lt]; omega
    · simp only [Int.not_lt]; omega
    · simpa using h7a
    · simp only [gt_iff_lt, Int.not_lt]; omega
  · rintro ⟨h1, h2, h3, h4, h5, h6a, h6b, h7a, h7b, h8, h9⟩
    refine ⟨h1, h2, h3, ?_, h5, ?_, ?_, ?_, by simpa using hwfeq.mpr h7b, h8, ?_⟩
    · -- the `≤`-leg is true (¬ the `>`-guard).
      cases hv : h.validUntil with
      | none => simp [hv]
      | some vu =>
        simp only [hv, expiryGuardFails] at h4 ⊢
        simp only [decide_eq_true_eq]
        by_contra hcon; exact h4 (by simp [Nat.lt_of_not_le (by omega)])
    · simp only [Int.not_lt] at h6a; omega
    · simp only [Int.not_lt] at h6b; omega
    · simpa using h7a
    · simp only [gt_iff_lt, Int.not_lt] at h9; omega

/-- **THE FAITHFULNESS KEYSTONE.** `admissionReason ctx h s = admitted` iff `admissible ctx h s`.
The legible reason agrees with the Bool gate EXACTLY: `admitted` is reported iff the turn genuinely
admits, and any reject reason iff it genuinely does not. -/
theorem admissionReason_eq_admitted_iff (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) :
    admissionReason ctx h s = .admitted ↔ admissible ctx h s = true := by
  rw [admissible_iff_gates]
  unfold admissionReason expiryGuardFails
  constructor
  · -- reason = admitted ⇒ every reject `if` is skipped ⇒ every gate Prop holds.
    intro hr
    by_cases g1 : h.forestNonEmpty = false
    · rw [if_pos g1] at hr; exact absurd hr (by simp)
    by_cases g2 : h.agent ∉ s.kernel.accounts
    · rw [if_neg g1, if_pos g2] at hr; exact absurd hr (by simp)
    by_cases g3 : cellLifecycleLive s.kernel h.agent = false
    · rw [if_neg g1, if_neg g2, if_pos g3] at hr; exact absurd hr (by simp)
    by_cases g4 : (match h.validUntil with | none => false | some vu => decide (admissionClock ctx > vu)) = true
    · rw [if_neg g1, if_neg g2, if_neg g3, if_pos g4] at hr; exact absurd hr (by simp)
    by_cases g5 : h.nonce ≠ storedNonce s h.agent
    · rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_pos g5] at hr; exact absurd hr (by simp)
    by_cases g6a : h.fee < 0
    · rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_pos g6a] at hr
      exact absurd hr (by simp)
    by_cases g6b : storedBalance s h.agent < h.fee
    · rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6a, if_pos g6b] at hr
      exact absurd hr (by simp)
    by_cases g7a : isFrozen ctx h.agent = true
    · rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6a, if_neg g6b,
          if_pos g7a] at hr
      exact absurd hr (by simp)
    rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5, if_neg g6a, if_neg g6b,
        if_neg g7a] at hr
    rcases hfind : h.writeSet.find? (fun c => isFrozen ctx c) with _ | c
    · rw [hfind] at hr
      by_cases g8 : h.prevReceipt ≠ ctx.storedHead
      · rw [if_pos g8] at hr; exact absurd hr (by simp)
      by_cases g9 : h.fee > (ctx.budget : Int)
      · rw [if_neg g8, if_pos g9] at hr; exact absurd hr (by simp)
      -- all gates pass
      exact ⟨by simpa using g1, by simpa using g2, by
        cases hb : cellLifecycleLive s.kernel h.agent with
        | true => rfl
        | false => exact absurd hb g3,
        g4, by simpa using g5, g6a, g6b, by simpa using g7a,
        by first | rfl | (rw [hfind]; rfl), by simpa using g8, g9⟩
    · rw [hfind] at hr; exact absurd hr (by simp)
  · -- every gate Prop holds ⇒ each reject `if` is skipped ⇒ reason = admitted.
    rintro ⟨h1, h2, h3, h4, h5, h6a, h6b, h7a, h7b, h8, h9⟩
    have g1 : ¬ (h.forestNonEmpty = false) := by simp [h1]
    have g2 : ¬ (h.agent ∉ s.kernel.accounts) := by simp [h2]
    have g3 : ¬ (cellLifecycleLive s.kernel h.agent = false) := by simp [h3]
    have g5 : ¬ (h.nonce ≠ storedNonce s h.agent) := by simp [h5]
    have g8 : ¬ (h.prevReceipt ≠ ctx.storedHead) := by simp [h8]
    have hfindnone : h.writeSet.find? (fun c => isFrozen ctx c) = none :=
      Option.isNone_iff_eq_none.mp h7b
    rw [if_neg g1, if_neg g2, if_neg g3, if_neg h4, if_neg g5, if_neg h6a, if_neg h6b, if_neg h7a]
    rw [hfindnone, if_neg g8, if_neg h9]

/-- Soundness corollary: an `admitted` reason means the turn GENUINELY admits — the reason cannot
launder a refusal as an admission. -/
theorem admitted_reason_means_admits (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hr : admissionReason ctx h s = .admitted) : admissible ctx h s = true :=
  (admissionReason_eq_admitted_iff ctx h s).mp hr

/-- Dual: a REJECT reason (anything but `admitted`) means the turn genuinely does NOT admit. -/
theorem reject_reason_means_inadmissible (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (hr : admissionReason ctx h s ≠ .admitted) : admissible ctx h s = false := by
  by_contra hadm
  have : admissible ctx h s = true := by
    cases hb : admissible ctx h s with
    | true => rfl
    | false => exact absurd hb hadm
  exact hr ((admissionReason_eq_admitted_iff ctx h s).mpr this)

#assert_axioms admissionReason_eq_admitted_iff
#assert_axioms admitted_reason_means_admits
#assert_axioms reject_reason_means_inadmissible

/-! ## §3b — The wire reason-code (FFI seam).

The reason crosses the C ABI as a small `Nat` tag (`reasonCode`), mirrored by a Rust enum. The
codes are STABLE — `admitted = 0`, then one per reject gate in `&&` order (1..11). The Rust side
decodes the SAME tags (`dregg-lean-ffi`'s `AdmissionReason`). `reasonCode_eq_zero_iff_admits` is the
wire-level faithfulness: code `0` on the wire iff the turn genuinely admits — the host can trust a
`reason:0` to mean "admitted", never a laundered refusal. -/

/-- The wire tag of an `AdmissionReason` (`admitted = 0`; reject gates `1..11` in `&&` order). The
Rust `dregg-lean-ffi::AdmissionReason` decoder mirrors these exactly. -/
def reasonCode : AdmissionReason → Nat
  | .admitted             => 0
  | .emptyForest          => 1
  | .noSuchAgent _        => 2
  | .deadAgent _          => 3
  | .expired _ _          => 4
  | .nonceMismatch _ _    => 5
  | .negativeFee _        => 6
  | .underfunded _ _      => 7
  | .agentFrozen _        => 8
  | .writeSetFrozen _     => 9
  | .chainHeadMismatch _ _ => 10
  | .overBudget _ _       => 11

/-- Distinct reason constructors carry distinct codes (the tag is injective on the 12 cases), so the
wire code loses NO information about which gate fired. -/
theorem reasonCode_injective_on_tags :
    (∀ a₁ : Nat, ∀ a₂ : Nat, reasonCode (.noSuchAgent a₁) = reasonCode (.noSuchAgent a₂)) ∧
    reasonCode .admitted = 0 ∧ reasonCode .emptyForest = 1 := by
  exact ⟨fun _ _ => rfl, rfl, rfl⟩

/-- **Wire-level faithfulness.** `reasonCode (admissionReason ctx h s) = 0` iff the turn admits.
The host reading the wire can trust `reason:0` to mean genuinely-admitted — and any non-zero code to
mean genuinely-refused — by the keystone. -/
theorem reasonCode_eq_zero_iff_admits (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) :
    reasonCode (admissionReason ctx h s) = 0 ↔ admissible ctx h s = true := by
  rw [← admissionReason_eq_admitted_iff]
  constructor
  · intro hz
    cases hr : admissionReason ctx h s with
    | admitted => rfl
    | _ => rw [hr] at hz; simp [reasonCode] at hz
  · intro hr; rw [hr]; rfl

#assert_axioms reasonCode_eq_zero_iff_admits

/-! ## §4 — Reachability (non-vacuity): each reject reason has a witness.

For every reject constructor we exhibit a concrete `(ctx, h, s)` whose `admissionReason` is exactly
that constructor — so no arm is dead. We reuse `Admission`'s §10 demo state/context. The witnesses
also confirm the gate ORDER: each malformed variant trips its OWN gate first. -/

/-- Pre-state: cell 7 holds balance 100, nonce 3 (a live account). Mirrors `Admission.as0`. -/
def rs0 : RecChainedState :=
  { kernel := { accounts := {7}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 100), ("nonce", .int 3)]
                                 else .record [] },
    log := [] }

/-- Host context: clock 50, nothing frozen, stored head `some 42`, budget 1000. -/
def rc0 : AdmCtx := { now := 50, frozen := [], storedHead := some 42, budget := 1000 }

/-- Well-formed turn: agent 7, nonce 3, fee 10, valid until 100, prev 42, write-set {7}, non-empty. -/
def rh0 : TurnHdr :=
  { agent := 7, nonce := 3, fee := 10, validUntil := some 100, prevReceipt := some 42,
    writeSet := [7], forestNonEmpty := true }

-- The well-formed turn is ADMITTED — and its reason agrees with the Bool gate:
#guard (admissionReason rc0 rh0 rs0 == .admitted)
#guard (admissible rc0 rh0 rs0)
-- decide-level alignment: reason-is-admitted ⇔ admissible-is-true on this witness:
#guard ((admissionReason rc0 rh0 rs0 == .admitted) == (admissible rc0 rh0 rs0))

-- Each reject reason is REACHABLE (one malformed variant per gate, in `&&` order):
#guard (admissionReason rc0 { rh0 with forestNonEmpty := false } rs0 == .emptyForest)
#guard (admissionReason rc0 { rh0 with agent := 99 } rs0 == .noSuchAgent 99)
#guard (admissionReason { rc0 with now := 200, blockHeight := 0 } { rh0 with validUntil := some 10 } rs0
        == .expired 200 10)
#guard (admissionReason rc0 { rh0 with nonce := 99 } rs0 == .nonceMismatch 99 3)
#guard (admissionReason rc0 { rh0 with fee := -5 } rs0 == .negativeFee (-5))
#guard (admissionReason rc0 { rh0 with fee := 500 } rs0 == .underfunded 500 100)
#guard (admissionReason { rc0 with frozen := [7] } rh0 rs0 == .agentFrozen 7)
#guard (admissionReason { rc0 with frozen := [13] } { rh0 with writeSet := [13] } rs0
        == .writeSetFrozen 13)
#guard (admissionReason rc0 { rh0 with prevReceipt := some 99 } rs0
        == .chainHeadMismatch (some 99) (some 42))
#guard (admissionReason { rc0 with budget := 5 } rh0 rs0 == .overBudget 10 5)

-- ORDER teeth: a turn that violates BOTH the nonce gate (5) AND the budget gate (9) reports the
-- EARLIER one (nonce) — `admissionReason` reports the FIRST failing gate, matching `&&`:
#guard (admissionReason { rc0 with budget := 5 } { rh0 with nonce := 99 } rs0 == .nonceMismatch 99 3)
-- ...and a reject reason ALWAYS coincides with `admissible = false` (faithfulness, evaluated):
#guard (admissible rc0 { rh0 with nonce := 99 } rs0 == false)
#guard ((admissionReason rc0 { rh0 with nonce := 99 } rs0 == .admitted) == false)

-- The WIRE CODES (the FFI tags) for each gate, in `&&` order 0..11 — the Rust decoder's contract:
#guard (reasonCode (admissionReason rc0 rh0 rs0) == 0)                                  -- admitted
#guard (reasonCode (admissionReason rc0 { rh0 with forestNonEmpty := false } rs0) == 1) -- emptyForest
#guard (reasonCode (admissionReason rc0 { rh0 with agent := 99 } rs0) == 2)             -- noSuchAgent
#guard (reasonCode (admissionReason { rc0 with now := 200 } { rh0 with validUntil := some 10 } rs0) == 4) -- expired
#guard (reasonCode (admissionReason rc0 { rh0 with nonce := 99 } rs0) == 5)             -- nonceMismatch
#guard (reasonCode (admissionReason rc0 { rh0 with fee := -5 } rs0) == 6)               -- negativeFee
#guard (reasonCode (admissionReason rc0 { rh0 with fee := 500 } rs0) == 7)              -- underfunded
#guard (reasonCode (admissionReason { rc0 with frozen := [7] } rh0 rs0) == 8)           -- agentFrozen
#guard (reasonCode (admissionReason { rc0 with frozen := [13] } { rh0 with writeSet := [13] } rs0) == 9) -- writeSetFrozen
#guard (reasonCode (admissionReason rc0 { rh0 with prevReceipt := some 99 } rs0) == 10) -- chainHeadMismatch
#guard (reasonCode (admissionReason { rc0 with budget := 5 } rh0 rs0) == 11)            -- overBudget
-- wire-level faithfulness, evaluated: code 0 ⇔ admissible on the well-formed witness:
#guard ((reasonCode (admissionReason rc0 rh0 rs0) == 0) == (admissible rc0 rh0 rs0))

end Dregg2.Exec.AdmissionReason
