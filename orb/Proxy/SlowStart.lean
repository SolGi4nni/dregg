/-
SlowStart — weight ramp for freshly recovered backends.

A backend that just came back Up (probe recovery, deploy restart) has cold
caches, empty connection pools, an un-warmed JIT. A reference proxy ramps its
share of traffic linearly over a configured window instead of hitting it with
its full configured weight at once. This module is that ramp, as a pure weight
transform composed with the proven weighted policies.

`rampWeight w elapsed window` is the effective weight `elapsed` time units
after recovery: the linear scale `w * elapsed / window`, floored at 1 so the
backend is never starved out of the rotation entirely, and equal to the full
configured `w` from `elapsed = window` on. A backend that has been up longer
than the window (or was never down) has `elapsed ≥ window` and is untouched.

Theorems:

  * `rampWeight_le`    — the ramp never EXCEEDS the configured weight: slow
    start only defers traffic, it cannot amplify a backend's share;
  * `rampWeight_pos`   — the ramp never hits zero (for positive configured
    weight): a recovering backend keeps receiving a trickle, so it can
    actually warm up — and WRR totality is preserved through the ramp;
  * `rampWeight_mono`  — the ramp is monotone in elapsed time: a backend's
    share never decreases as it warms;
  * `rampWeight_full`  — at the end of the window the ramp IS the configured
    weight: slow start terminates exactly, it does not asymptote;
  * `rampPool_*`       — the pool transform changes ONLY weights: ids,
    eligibility, tiers, connection counts are untouched, so the tier pool
    commutes with the ramp and `idsNodup` is preserved;
  * `wrr_ramp_window_weight` — **fairness through the ramp**: over a full
    cycle of the ramped pool, each backend is selected exactly its RAMPED
    weight's worth of times — the warming backend gets exactly its reduced
    share, everyone else exactly their full share.
-/

import Proxy.Balance

namespace Proxy

/-- Effective weight of a backend `elapsed` time units after recovery, under a
slow-start window of `window` units: linear ramp from a floor of 1 up to the
configured weight `w`, reaching it exactly at `elapsed = window`. -/
def rampWeight (w elapsed window : Nat) : Nat :=
  if window ≤ elapsed then w else max 1 (w * elapsed / window)

/-- Slow start terminates exactly: from the end of the window on, the
effective weight is the configured weight. -/
theorem rampWeight_full {w elapsed window : Nat} (h : window ≤ elapsed) :
    rampWeight w elapsed window = w := by
  simp [rampWeight, h]

/-- Division by a fixed denominator is monotone in the numerator. -/
theorem div_le_div_num {m n k : Nat} (h : m ≤ n) : m / k ≤ n / k := by
  cases k with
  | zero => simp
  | succ k =>
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos k)).2
    exact Nat.le_trans (Nat.div_mul_le_self m (k + 1)) h

/-- The ramp never exceeds the configured weight: slow start only defers. -/
theorem rampWeight_le {w elapsed window : Nat} (hw : 0 < w) :
    rampWeight w elapsed window ≤ w := by
  unfold rampWeight
  split
  · exact Nat.le_refl w
  · rename_i hlt
    have helt : elapsed < window := by omega
    have hdiv : w * elapsed / window ≤ w := by
      have hmul : w * elapsed ≤ w * window := Nat.mul_le_mul_left w (by omega)
      have h1 : w * elapsed / window ≤ w * window / window := div_le_div_num hmul
      have h2 : w * window / window = w := Nat.mul_div_cancel w (by omega)
      omega
    omega

/-- The ramp never starves (for positive configured weight): a recovering
backend keeps a trickle of traffic, and weighted-round-robin totality
(`select_wrr_total`, which needs positive weights) survives the ramp. -/
theorem rampWeight_pos {w elapsed window : Nat} (hw : 0 < w) :
    0 < rampWeight w elapsed window := by
  unfold rampWeight
  split
  · exact hw
  · exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left ..)

/-- The ramp is monotone in elapsed time: warming never loses traffic. -/
theorem rampWeight_mono {w e e' window : Nat} (hw : 0 < w) (h : e ≤ e') :
    rampWeight w e window ≤ rampWeight w e' window := by
  unfold rampWeight
  by_cases h1 : window ≤ e
  · rw [if_pos h1, if_pos (by omega : window ≤ e')]
    exact Nat.le_refl w
  · rw [if_neg h1]
    by_cases h2 : window ≤ e'
    · rw [if_pos h2]
      have hle := rampWeight_le (w := w) (elapsed := e) (window := window) hw
      rw [rampWeight, if_neg h1] at hle
      exact hle
    · rw [if_neg h2]
      have hmul : w * e ≤ w * e' := Nat.mul_le_mul_left w h
      have hdiv : w * e / window ≤ w * e' / window := div_le_div_num hmul
      omega

/-- Per-backend slow-start clock: backend id ↦ time units since recovery. -/
abbrev WarmClock := Nat → Nat

/-- Apply the ramp across a pool: each backend's weight becomes its effective
slow-start weight; every other field is untouched. -/
def rampPool (clock : WarmClock) (window : Nat) (bs : List Backend) :
    List Backend :=
  bs.map (fun b => { b with weight := rampWeight b.weight (clock b.id) window })

/-- The ramp changes only weights: ids are preserved pointwise. -/
theorem rampPool_ids (clock : WarmClock) (window : Nat) (bs : List Backend) :
    (rampPool clock window bs).map Backend.id = bs.map Backend.id := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [rampPool] at ih ⊢

/-- Distinct ids survive the ramp. -/
theorem rampPool_idsNodup {clock : WarmClock} {window : Nat}
    {bs : List Backend} (h : idsNodup bs) :
    idsNodup (rampPool clock window bs) := by
  unfold idsNodup
  rw [rampPool_ids]
  exact h

/-- Membership transport: every ramped backend is the ramp of an original
member, sharing id, conns, tier, health and status. -/
theorem mem_rampPool {clock : WarmClock} {window : Nat} {bs : List Backend}
    {b : Backend} (h : b ∈ rampPool clock window bs) :
    ∃ o ∈ bs, b = { o with weight := rampWeight o.weight (clock o.id) window } := by
  obtain ⟨o, ho, heq⟩ := List.mem_map.mp h
  exact ⟨o, ho, heq.symm⟩

/-- Ramped pools have positive weights whenever the configured pool does —
the hypothesis every weighted-policy totality/minimality theorem asks for. -/
theorem rampPool_pos {clock : WarmClock} {window : Nat} {bs : List Backend}
    (hw : ∀ b ∈ bs, 0 < b.weight) :
    ∀ b ∈ rampPool clock window bs, 0 < b.weight := by
  intro b hb
  obtain ⟨o, ho, heq⟩ := mem_rampPool hb
  rw [heq]
  exact rampWeight_pos (hw o ho)

/-- **Exact fairness through the ramp.** Over any window of
`totalWeight (rampPool …)` consecutive rounds, a ramped-pool member is
selected by WRR exactly its RAMPED weight's worth of times: the warming
backend receives exactly its reduced share, and (by `rampWeight_full`) a
fully warmed backend exactly its configured share. -/
theorem wrr_ramp_window_weight {clock : WarmClock} {window : Nat}
    {bs : List Backend} {b : Backend} (hnd : idsNodup bs)
    (hb : b ∈ rampPool clock window bs) (start : Nat) :
    cnt (fun j => decide (wrr (rampPool clock window bs) (start + j) = some b))
        (totalWeight (rampPool clock window bs))
      = b.weight :=
  wrr_window_weight (rampPool_idsNodup hnd) hb start

end Proxy
