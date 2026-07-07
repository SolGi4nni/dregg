import Metrics.Basic

/-!
# MetricsCorrect: the deployed metrics accounting refines an independent spec

This file specifies **counter** and **histogram** accounting independently of
the implementation, from the OpenMetrics specification, and proves the deployed
`Metrics.Registry.inc` and `Metrics.Histogram.observe` refine that spec.

Standard reference — the OpenMetrics specification, revision 1.0.0
(<https://github.com/OpenObservability/OpenMetrics/blob/main/specification/OpenMetrics.md>):

* §"Counter" / "The MetricPoint of a Counter": a Counter's Total is a
  monotonically non-decreasing value; a valid increment adds a non-negative
  amount and never lowers the Total. Here the increment of a counter by `n`
  raises it by *exactly* `n` (exact-add ⇒ monotone).

* §"Histogram": a Histogram MetricPoint carries buckets identified by an upper
  bound label `le`. "The value of a bucket is the count of observations with a
  value less than or equal to the `le` threshold." Buckets are **cumulative**
  and their thresholds are unique and monotonically increasing, so the per-`le`
  cumulative counts are non-decreasing across thresholds. An observation of
  value `v` therefore belongs to the bucket whose exclusive lower threshold is
  `< v` and whose upper `le` threshold is `≥ v` (`gt lower, le upper`).

The spec below is written *only* in terms of `bounds`, `v`, counts, and the
`le`/cumulative rules from that standard. The implementation is then shown to
satisfy it. The bound-function `bucketIndex`, count-bump `bumpAt`, and the
`Registry.inc` / `Histogram.observe` transitions proved against are the exact
definitions the engine invokes (from `Metrics/Basic.lean`), not proof-file
copies.
-/

namespace MetricsCorrect

open Metrics

/-! ## Counter specification (OpenMetrics §"Counter") -/

/-- SPEC. A counter transition from `before` to `after` under an increment of
`delta` is *correct* iff the new value is exactly `before + delta`. This is the
exact-add law; monotonicity is a consequence (see `counterSpec_monotone`). It
mentions only the two counter values and the increment amount — no reference to
the `Registry` representation. -/
def CounterSpec (before after delta : Nat) : Prop := after = before + delta

/-- SPEC consequence: a spec-correct increment never lowers the counter
(OpenMetrics: a Counter Total is monotonically non-decreasing). -/
theorem counterSpec_monotone {before after delta : Nat}
    (h : CounterSpec before after delta) : before ≤ after := by
  simp only [CounterSpec] at h; omega

/-- REFINEMENT. The deployed `Metrics.Registry.inc` satisfies the counter spec
on the counter it targets: incrementing `name` by `delta` moves its value by
exactly `delta`. Binds the deployed `Registry.inc`. -/
theorem inc_refines_spec (r : Registry) (name : String) (delta : Nat) :
    CounterSpec (r.counters name) ((r.inc name delta).counters name) delta := by
  simp [CounterSpec, Registry.inc]

/-- REFINEMENT. The deployed increment leaves every *other* counter exactly
fixed — a spec-correct transition with `delta = 0` for those names. Binds the
deployed `Registry.inc`. -/
theorem inc_refines_others (r : Registry) (name n : String) (delta : Nat)
    (h : n ≠ name) :
    CounterSpec (r.counters n) ((r.inc name delta).counters n) 0 := by
  simp [CounterSpec, Registry.inc, h]

/-! ## Histogram bucket specification (OpenMetrics §"Histogram", `le` semantics)

`bounds` is the ascending list of `le` thresholds; there is one more bucket than
thresholds (the final `+∞` overflow bucket). Bucket `i` spans the half-open
interval `(lowerₚ, upperₚ]` where `upperₚ = bounds[i]` (`+∞` past the last
threshold) and `lowerₚ = bounds[i-1]` (`−∞` for the first bucket). -/

/-- SPEC. Value `v` belongs to bucket `i` of `bounds` iff `v ≤ upper` (the `le`
threshold, vacuously true for the `+∞` overflow bucket) **and** `v > lower` (the
predecessor threshold, vacuously true for the first bucket). This is exactly the
OpenMetrics `le` membership rule; it names only `bounds`, `v`, and `i`. -/
def Contains (bounds : List Nat) (v : Nat) (i : Nat) : Prop :=
  (match bounds[i]? with | some u => v ≤ u | none => True) ∧
  (match i with
   | 0 => True
   | j + 1 => match bounds[j]? with | some l => l < v | none => True)

/-- REFINEMENT. The deployed `Metrics.bucketIndex` always returns a bucket that
*contains* the observed value — `le upper ∧ gt lower` — for any bound list.
Binds the deployed `bucketIndex`. -/
theorem bucketIndex_contains (bounds : List Nat) (v : Nat) :
    Contains bounds v (bucketIndex bounds v) := by
  induction bounds with
  | nil => exact ⟨trivial, trivial⟩
  | cons b bs ih =>
    by_cases hb : b < v
    · -- `b` is taken; the target bucket is `(bucketIndex bs v) + 1`.
      have hidx : bucketIndex (b :: bs) v = bucketIndex bs v + 1 := by
        simp [bucketIndex, List.takeWhile_cons, hb]
      rw [hidx]
      refine ⟨?_, ?_⟩
      · -- upper: index `j+1` into `b::bs` is index `j` into `bs` (the IH's upper).
        simpa [List.getElem?_cons_succ] using ih.1
      · -- lower: predecessor threshold is `< v`.
        cases hj : bucketIndex bs v with
        | zero => simpa [List.getElem?_cons_zero] using hb
        | succ k =>
          have := ih.2
          rw [hj] at this
          simpa [List.getElem?_cons_succ] using this
    · -- `v ≤ b`; the value lands in bucket `0`.
      have hidx : bucketIndex (b :: bs) v = 0 := by
        simp [bucketIndex, List.takeWhile_cons, hb]
      rw [hidx]
      exact ⟨by simpa [List.getElem?_cons_zero] using Nat.le_of_not_lt hb, trivial⟩

/-! ## The count-bump refines "increment exactly the containing bucket" -/

/-- `bumpAt` raises exactly the target index by one. -/
theorem bumpAt_get_self (cs : List Nat) (i : Nat) :
    (bumpAt cs i)[i]? = (cs[i]?).map (· + 1) := by
  induction cs generalizing i with
  | nil => simp [bumpAt]
  | cons c cs ih =>
    cases i with
    | zero => simp [bumpAt]
    | succ i => simp [bumpAt, ih i]

/-- `bumpAt` leaves every non-target index untouched. -/
theorem bumpAt_get_other (cs : List Nat) (i k : Nat) (h : k ≠ i) :
    (bumpAt cs k)[i]? = cs[i]? := by
  induction cs generalizing i k with
  | nil => simp [bumpAt]
  | cons c cs ih =>
    cases k with
    | zero =>
      cases i with
      | zero => exact absurd rfl h
      | succ i => simp [bumpAt]
    | succ k =>
      cases i with
      | zero => simp [bumpAt]
      | succ i =>
        simp only [bumpAt, List.getElem?_cons_succ]
        exact ih i k (fun e => h (congrArg Nat.succ e))

/-- REFINEMENT. A single `observe v` bumps exactly the bucket that *contains*
`v` (by `bucketIndex_contains`) by exactly one, and leaves the rest fixed.
Binds the deployed `Histogram.observe`. -/
theorem observe_bumps_containing (h : Histogram) (v : Nat) :
    (h.observe v).counts[bucketIndex h.bounds v]?
      = (h.counts[bucketIndex h.bounds v]?).map (· + 1) := by
  simp only [Histogram.observe]
  exact bumpAt_get_self h.counts (bucketIndex h.bounds v)

/-- REFINEMENT. `observe v` leaves every bucket other than the containing one
exactly as it was. Binds the deployed `Histogram.observe`. -/
theorem observe_others_fixed (h : Histogram) (v : Nat) (k : Nat)
    (hk : k ≠ bucketIndex h.bounds v) :
    (h.observe v).counts[k]? = h.counts[k]? := by
  simp only [Histogram.observe]
  exact bumpAt_get_other h.counts k (bucketIndex h.bounds v) (fun e => hk e.symm)

/-! ## Cumulative bucket counts are non-decreasing (OpenMetrics `le` cumulation)

The exposed `le` value at threshold `j` is the count of observations in buckets
`0..j` — the cumulative sum of per-bucket counts. The standard requires these
`le` values to be non-decreasing across ascending thresholds. -/

/-- The cumulative `le` count at threshold index `j`: observations that fell in
some bucket `≤ j`. -/
def cumulative (counts : List Nat) (j : Nat) : Nat := (counts.take (j + 1)).sum

/-- REFINEMENT. The cumulative `le` counts are non-decreasing across ascending
thresholds — the OpenMetrics cumulation invariant. -/
theorem cumulative_mono (counts : List Nat) (j : Nat) :
    cumulative counts j ≤ cumulative counts (j + 1) := by
  have hsplit : counts.take (j + 2) = counts.take (j + 1) ++ (counts.drop (j + 1)).take 1 := by
    have : j + 2 = (j + 1) + 1 := rfl
    rw [this, List.take_add]
  simp only [cumulative]
  have : counts.take (j + 1 + 1) = counts.take (j + 2) := rfl
  rw [this, hsplit, Metrics.sum_append]
  exact Nat.le_add_right _ _

end MetricsCorrect

/-! ## Non-vacuity: buggy accountings are rejected by the spec

Concrete witnesses proving the spec has teeth: a lost increment and a
mis-binning both provably *fail* the specification, so the refinement theorems
above are not vacuously satisfiable. -/

namespace MetricsCorrect

open Metrics

/-- A buggy counter that drops the increment. -/
def lostInc (before : Nat) : Nat := before

/-- NON-VACUITY (counter). A counter that lost an increment fails the spec:
`CounterSpec 0 0 1` is `0 = 0 + 1`, which is false. -/
theorem lostIncrement_fails : ¬ CounterSpec 0 (lostInc 0) 1 := by
  simp [CounterSpec, lostInc]

/-- NON-VACUITY (counter). The deployed increment is genuinely *not* the lossy
one: it produces `1` where the lossy counter stays `0`. -/
theorem deployed_inc_is_not_lossy :
    (Registry.empty.inc "x" 1).counters "x" = 1 ∧ lostInc 0 = 0 := by
  refine ⟨?_, rfl⟩
  simp [Registry.inc, Registry.empty]

/-- NON-VACUITY (histogram). With thresholds `[10, 20]`, the value `15` lies in
`(10, 20]`, so its containing bucket is `1`, and the deployed `bucketIndex`
computes exactly that. -/
theorem bucketIndex_concrete : bucketIndex [10, 20] 15 = 1 := rfl

/-- NON-VACUITY (histogram). Bucket `1` genuinely contains `15`. -/
theorem contains_concrete : Contains [10, 20] 15 1 := by
  refine ⟨?_, ?_⟩
  · show (15 : Nat) ≤ 20; decide
  · show (10 : Nat) < 15; decide

/-- NON-VACUITY (histogram). A mis-binning **low** (bucket `0`, `le = 10`) does
NOT contain `15` — `15 ≤ 10` is false — so the spec rejects it. -/
theorem misbin_low_fails : ¬ Contains [10, 20] 15 0 := by
  intro hc
  exact absurd (show (15 : Nat) ≤ 10 from hc.1) (by decide)

/-- NON-VACUITY (histogram). A mis-binning **high** (bucket `2`, lower `= 20`)
does NOT contain `15` — `20 < 15` is false — so the spec rejects it. -/
theorem misbin_high_fails : ¬ Contains [10, 20] 15 2 := by
  intro hc
  exact absurd (show (20 : Nat) < 15 from hc.2) (by decide)

end MetricsCorrect
