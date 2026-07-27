/-
ProxyTimeoutCorrect — correctness of the proxy phase-deadline decision by refinement.

A forwarding proxy imposes a wall-clock deadline on each phase of an outbound
request (connect, waiting for the first response byte, streaming the body, …).
When the time a phase has been running exceeds the budget allotted to it, the
proxy MUST stop waiting and surface a timeout to the client: it "did not
receive a timely response from an upstream server it needed to access in order
to complete the request", which is exactly the 504 (Gateway Timeout) condition
of RFC 9110 §15.6.5. Conversely, a phase that completes within its budget MUST
NOT be aborted — a proxy that timed out a within-deadline request would reject
work the upstream answered in time.

The decision reduces to one comparison: for a phase with budget `T` that has
been observed to run for `E`, the phase is aborted iff `E > T` (elapsed
strictly exceeds the timeout). At the exact boundary `E = T` the phase is still
within its deadline and is NOT aborted.

This module states that abort rule as an INDEPENDENT specification
(`deadlineAbort`, below) — written only from the paragraph above and RFC 9110
§15.6.5, defined WITHOUT reference to the state machine in `Proxy.Timeout` — and
proves that the DEPLOYED step function `Proxy.Timeout.step` (the function the
engine actually invokes) emits its timeout output exactly when, and only when,
the specification says the active phase is aborted.

Results:

  * `deadlineAbort` — the independent rule: aborted iff observed elapsed > budget;
  * `step_emits_timeout_iff_spec` — the DEPLOYED `step` emits `[timeout p]` iff
    the spec aborts the active phase `p` (the refinement);
  * `step_within_deadline_no_abort` — within deadline (`E ≤ T`) the deployed
    `step` emits nothing and does not go terminal;
  * `step_over_deadline_aborts` — over deadline (`E > T`) the deployed `step`
    emits one timeout and goes terminal;
  * `boundary_not_aborted` / `just_over_aborted` — the boundary is exclusive, so
    the rule is neither "never abort" nor "abort at the boundary" (non-vacuity).
-/

import Proxy.Timeout

namespace Proxy.TimeoutCorrect

open Proxy.Timeout

/-! ### The independent deadline specification

Defined from RFC 9110 §15.6.5 and the phase-deadline rule stated in the module
header, with no reference to `Proxy.Timeout.step`, `TState`, or any other
implementation construct: it is a bare comparison on two wall-clock durations. -/

/-- **Deadline abort rule.** A phase that has been observed to run for `elapsed`
time under a timeout `budget` is aborted iff its elapsed time *strictly exceeds*
the budget. The comparison is strict, so a phase that has run for exactly its
budget is within its deadline (not aborted). -/
def deadlineAbort (elapsed budget : Nat) : Prop := elapsed > budget

instance (elapsed budget : Nat) : Decidable (deadlineAbort elapsed budget) :=
  inferInstanceAs (Decidable (elapsed > budget))

/-! ### The observed elapsed time of the active phase

The wall-clock time the active phase has been observed to run at the moment
event `e` is processed: the monotone observed clock instant (`max s.clock e.now`,
never allowed to run backwards) minus the instant the phase began. This is a
plain reading of the machine's clock fields, not part of the abort decision. -/

/-- Observed elapsed time of the active phase when event `e` arrives. -/
def phaseElapsed (s : TState) (e : Ev) : Nat := max s.clock e.now - s.phaseStart

/-! ### Refinement: the deployed `step` matches the spec

`step_emits_timeout_iff_spec` binds `Proxy.Timeout.step` — the exact function
the request pipeline runs — with no intervening wrapper, and characterises its
timeout output by the independent `deadlineAbort` rule. -/

/-- **Refinement.** For a running request (`timedOut = false`) whose active
phase is `p`, the deployed `step` emits the timeout output `[timeout p]` if and
only if the independent specification aborts phase `p`, i.e. the observed
elapsed time strictly exceeds `p`'s budget. -/
theorem step_emits_timeout_iff_spec
    (b : Budgets) (s : TState) (e : Ev)
    (hrun : s.timedOut = false) (p : Phase) (rest : List Phase)
    (hrem : s.remaining = p :: rest) :
    (step b s e).2 = [Output.timeout p]
      ↔ deadlineAbort (phaseElapsed s e) (budgetOf b p) := by
  simp only [step, hrun, hrem, phaseElapsed, deadlineAbort]
  by_cases h : budgetOf b p < max s.clock e.now - s.phaseStart
  · rw [if_pos h]
    constructor
    · intro _; exact h
    · intro _; rfl
  · rw [if_neg h]
    constructor
    · intro hout; cases e <;> simp at hout
    · intro habort; exact absurd habort h

/-- **Within deadline ⇒ not aborted.** If the observed elapsed time does not
exceed the budget (`E ≤ T`), the deployed `step` emits no timeout and does not
enter the terminal timed-out state: a within-deadline request is not aborted. -/
theorem step_within_deadline_no_abort
    (b : Budgets) (s : TState) (e : Ev)
    (hrun : s.timedOut = false) (p : Phase) (rest : List Phase)
    (hrem : s.remaining = p :: rest)
    (hwithin : ¬ deadlineAbort (phaseElapsed s e) (budgetOf b p)) :
    (step b s e).2 = [] ∧ (step b s e).1.timedOut = false := by
  simp only [phaseElapsed, deadlineAbort, Nat.not_lt] at hwithin
  have hin : ¬ budgetOf b p < max s.clock e.now - s.phaseStart := by omega
  refine ⟨?_, ?_⟩
  · simp only [step, hrun, hrem]; rw [if_neg hin]; cases e <;> rfl
  · simp only [step, hrun, hrem]; rw [if_neg hin]; cases e <;> rfl

/-- **Over deadline ⇒ aborted.** If the observed elapsed time strictly exceeds
the budget (`E > T`), the deployed `step` emits exactly one timeout for the
active phase and transitions to the terminal timed-out state. -/
theorem step_over_deadline_aborts
    (b : Budgets) (s : TState) (e : Ev)
    (hrun : s.timedOut = false) (p : Phase) (rest : List Phase)
    (hrem : s.remaining = p :: rest)
    (hover : deadlineAbort (phaseElapsed s e) (budgetOf b p)) :
    (step b s e).2 = [Output.timeout p] ∧ (step b s e).1.timedOut = true := by
  have h : budgetOf b p < max s.clock e.now - s.phaseStart := hover
  simp only [step, hrun, hrem]; rw [if_pos h]; exact ⟨rfl, rfl⟩

/-! ### Non-vacuity

The specification is not the implementation renamed, and it is neither of the
two natural wrong rules. The boundary `E = T` is decisive:

  * a "never abort" implementation would disagree with `just_over_aborted`;
  * an "abort at the boundary" implementation (`E ≥ T`) would disagree with
    `boundary_not_aborted`.

Because `step_emits_timeout_iff_spec` pins the deployed `step` to `deadlineAbort`
exactly, either wrong implementation would refute the refinement at these
witnesses. -/

/-- At the exact boundary the phase is NOT aborted (the comparison is strict).
Rules out an `E ≥ T` implementation. -/
theorem boundary_not_aborted (t : Nat) : ¬ deadlineAbort t t := by
  simp [deadlineAbort]

/-- One tick past the budget the phase IS aborted. Rules out a "never abort"
implementation. -/
theorem just_over_aborted (t : Nat) : deadlineAbort (t + 1) t := by
  simp [deadlineAbort]

/-- Worked witness on the deployed machine: with the connect budget 20 and the
connect phase having run 35 (`clock` 45, `phaseStart` 10, over deadline), the
real `step` aborts; had it run exactly 20 (`clock` 30) it would not. -/
example :
    let b : Budgets := ⟨10, 20, 30, 5, 40, 100⟩
    let s : TState := ⟨[.connect, .tls, .body], 10, 10, 0, 10, false, 205⟩
    -- 35 > 20: the deployed step emits a connect timeout
    (step b s (.tick 45)).2 = [Output.timeout .connect]
      -- exactly 20 elapsed (boundary): no timeout
      ∧ (step b s (.tick 30)).2 = [] := by
  decide

end Proxy.TimeoutCorrect
