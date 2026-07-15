/-
EwmaLatency — the exponentially-weighted-moving-average latency policy.

A latency-aware load-balancer class: each backend carries a live EWMA of its
observed request latency, and selection dials the eligible backend whose EWMA
is lowest. Two independent pieces, each proven:

  * the EWMA *recurrence* (`ewmaStep`) — the fixed-point smoothing the host runs
    per observed sample, with smoothing factor `α = 1/2^k`:

        ewma' = (sample + (2^k − 1)·ewma) / 2^k

    a convex combination of the old average and the new sample. Proven:
    `ewmaStep_fixed` (a steady stream at value `v` holds the average at `v`),
    `ewmaStep_le` / `ewmaStep_ge` (the average never leaves the `[L,B]` envelope
    of its inputs — no runaway, no undershoot), and `ewmaFold_le` (the whole
    per-backend history stays bounded by the worst sample);

  * the *selection* (`leastLat`) — pick the minimal-EWMA backend, earlier list
    position winning ties, with the SAME shape as `Proxy.leastConn`. Proven:
    `leastLat_mem` (a chosen backend is a real candidate), `leastLat_total`
    (a nonempty pool always yields a pick), and `leastLat_min` (the chosen
    backend's EWMA is minimal over the whole candidate list).

`selectLatency` runs `leastLat` over the tiered eligible pool (`Proxy.tierPool`),
so every fabric guarantee of the balancer algebra is inherited by construction:
`selectLatency_eligible` (a chosen backend is healthy ∧ active — the load-bearing
health/breaker ejection), `selectLatency_best_tier` (never a backup while a
primary is up), `selectLatency_total`, and `selectLatency_min` (minimality
through the tiered selector). The per-backend EWMA value is a host-supplied live
input `lat : Nat → Nat` keyed by backend id — exactly as `Proxy.leastConn` reads
the live in-flight count — so latency-aware selection needs no change to the
`Backend` snapshot.
-/

import Proxy.Balance

namespace Proxy

/-! ### The EWMA recurrence: `ewma' = (sample + (2^k − 1)·ewma) / 2^k` -/

/-- One EWMA update with smoothing factor `α = 1/2^k`: a convex combination
weighting the new `sample` by `1/2^k` and the running `old` average by
`(2^k−1)/2^k`. Larger `k` ⇒ smoother (slower to react); `k = 0` ⇒ track the
raw sample. Integer (truncating) division keeps it exact and host-runnable. -/
def ewmaStep (k old sample : Nat) : Nat := (sample + (2 ^ k - 1) * old) / 2 ^ k

/-- The convex-combination numerator collapses on a constant: at `sample = old`
the weights sum back to the whole. -/
private theorem convex_num (p x : Nat) (hp1 : 1 ≤ p) : x + (p - 1) * x = p * x := by
  have h : ((p - 1) + 1) * x = (p - 1) * x + x := by rw [Nat.add_mul, Nat.one_mul]
  have hp : (p - 1) + 1 = p := by omega
  rw [hp] at h
  omega

/-- **Steady state.** A stream that keeps reporting the same latency `v` holds
the EWMA at exactly `v` — the fixed point of the recurrence. -/
theorem ewmaStep_fixed (k v : Nat) : ewmaStep k v v = v := by
  unfold ewmaStep
  rw [convex_num _ v Nat.one_le_two_pow, Nat.mul_div_cancel_left v Nat.one_le_two_pow]

/-- **No runaway (upper envelope).** If both the running average and the new
sample are at most `B`, the updated average is at most `B`: the EWMA never
climbs above the worst input it has seen. -/
theorem ewmaStep_le {k old sample B : Nat} (ho : old ≤ B) (hs : sample ≤ B) :
    ewmaStep k old sample ≤ B := by
  unfold ewmaStep
  apply Nat.div_le_of_le_mul
  have hmul : (2 ^ k - 1) * old ≤ (2 ^ k - 1) * B := Nat.mul_le_mul_left _ ho
  have hnum : sample + (2 ^ k - 1) * old ≤ B + (2 ^ k - 1) * B := by omega
  rwa [convex_num _ B Nat.one_le_two_pow] at hnum

/-- **No undershoot (lower envelope).** Dually, if both the running average and
the new sample are at least `L`, the updated average is at least `L`. Together
with `ewmaStep_le` this pins the EWMA inside the `[L,B]` range of its inputs. -/
theorem ewmaStep_ge {k old sample L : Nat} (ho : L ≤ old) (hs : L ≤ sample) :
    L ≤ ewmaStep k old sample := by
  unfold ewmaStep
  rw [Nat.le_div_iff_mul_le Nat.one_le_two_pow]
  have hmul : (2 ^ k - 1) * L ≤ (2 ^ k - 1) * old := Nat.mul_le_mul_left _ ho
  have hge : L + (2 ^ k - 1) * L ≤ sample + (2 ^ k - 1) * old := by omega
  rw [convex_num _ L Nat.one_le_two_pow] at hge
  rw [Nat.mul_comm L]
  exact hge

/-- Fold the EWMA over a backend's whole observed-latency history from an
initial estimate. This is how the host maintains `lat id` between requests. -/
def ewmaFold (k init : Nat) (samples : List Nat) : Nat :=
  samples.foldl (ewmaStep k) init

/-- **Bounded history.** If the seed and every observed sample are at most `B`,
the folded EWMA is at most `B` — the whole maintained value stays inside the
input envelope, no accumulation drift. -/
theorem ewmaFold_le {k B : Nat} (init : Nat) (samples : List Nat)
    (hinit : init ≤ B) (hs : ∀ x ∈ samples, x ≤ B) :
    ewmaFold k init samples ≤ B := by
  unfold ewmaFold
  induction samples generalizing init with
  | nil => simpa using hinit
  | cons a rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact ewmaStep_le hinit (hs a (List.mem_cons_self _ _))
    · intro x hx; exact hs x (List.mem_cons_of_mem _ hx)

/-! ### Least-latency selection -/

/-- Pick the backend with the lowest EWMA latency (`lat` keyed by backend id);
ties go to the earlier list position — the SAME shape as `Proxy.leastConn`,
reading a host-supplied per-backend value instead of the in-flight count. -/
def leastLat (lat : Nat → Nat) : List Backend → Option Backend
  | [] => none
  | b :: bs =>
    match leastLat lat bs with
    | none => some b
    | some c => if lat b.id ≤ lat c.id then some b else some c

theorem leastLat_total {lat : Nat → Nat} {bs : List Backend} (h : bs ≠ []) :
    (leastLat lat bs).isSome := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b rest =>
    cases hr : leastLat lat rest with
    | none => simp [leastLat, hr]
    | some c => by_cases hb : lat b.id ≤ lat c.id <;> simp [leastLat, hr, hb]

theorem leastLat_mem {lat : Nat → Nat} {bs : List Backend} {b : Backend}
    (h : leastLat lat bs = some b) : b ∈ bs := by
  induction bs generalizing b with
  | nil => cases h
  | cons c rest ih =>
    cases hr : leastLat lat rest with
    | none =>
      simp only [leastLat, hr] at h
      cases h
      exact List.mem_cons_self c rest
    | some w =>
      simp only [leastLat, hr] at h
      split at h
      · cases h; exact List.mem_cons_self c rest
      · cases h; exact List.mem_cons_of_mem _ (ih hr)

/-- **Minimality.** The chosen backend's EWMA latency is minimal over the whole
candidate list — no eligible backend was faster at selection time. -/
theorem leastLat_min {lat : Nat → Nat} {bs : List Backend} {b : Backend}
    (h : leastLat lat bs = some b) : ∀ c ∈ bs, lat b.id ≤ lat c.id := by
  induction bs generalizing b with
  | nil => cases h
  | cons a rest ih =>
    intro c hc
    cases hr : leastLat lat rest with
    | none =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons x xs =>
          have := leastLat_total (lat := lat) (bs := x :: xs) (by intro hx; cases hx)
          rw [hr] at this
          cases this
      simp only [leastLat, hr] at h
      cases h
      rcases List.mem_cons.mp hc with hc' | hc'
      · rw [hc']; exact Nat.le_refl _
      · rw [hrest] at hc'; cases hc'
    | some w =>
      simp only [leastLat, hr] at h
      split at h
      · rename_i hle
        cases h
        rcases List.mem_cons.mp hc with hc' | hc'
        · rw [hc']; exact Nat.le_refl _
        · exact Nat.le_trans hle (ih hr c hc')
      · rename_i hgt
        cases h
        rcases List.mem_cons.mp hc with hc' | hc'
        · rw [hc']; omega
        · exact ih hr c hc'

/-! ### The tiered least-latency selector -/

/-- Least-latency over the tiered eligible pool: the same `tierPool` every
`Proxy.select` policy runs on, so eligibility / tiering guarantees carry over. -/
def selectLatency (lat : Nat → Nat) (bs : List Backend) : Option Backend :=
  leastLat lat (tierPool bs)

/-- **Chosen ⇒ eligible.** A least-latency pick is a healthy, active member of
the fleet — the load-bearing health/breaker ejection for this policy class. -/
theorem selectLatency_eligible {lat : Nat → Nat} {bs : List Backend} {b : Backend}
    (h : selectLatency lat bs = some b) : b ∈ bs ∧ b.eligible = true :=
  let spec := tierPool_spec (leastLat_mem h)
  ⟨spec.1, spec.2.1⟩

/-- **Best tier.** A least-latency pick sits in the healthiest nonempty tier —
backups engage only when no primary is eligible. -/
theorem selectLatency_best_tier {lat : Nat → Nat} {bs : List Backend} {b : Backend}
    (h : selectLatency lat bs = some b) : bestTier bs = some b.tier :=
  (tierPool_spec (leastLat_mem h)).2.2

/-- **Totality.** If any eligible backend exists, a least-latency pick is made. -/
theorem selectLatency_total {lat : Nat → Nat} {bs : List Backend} {w : Backend}
    (hmem : w ∈ bs) (helig : w.eligible = true) :
    (selectLatency lat bs).isSome :=
  leastLat_total (tierPool_ne_nil hmem helig)

/-- **Minimality through the tiered selector.** The chosen backend's EWMA is
minimal over the whole tier pool: no eligible same-tier backend was faster. -/
theorem selectLatency_min {lat : Nat → Nat} {bs : List Backend} {b : Backend}
    (h : selectLatency lat bs = some b) :
    ∀ c ∈ tierPool bs, lat b.id ≤ lat c.id :=
  leastLat_min h

/-! ### Runnable checks -/

-- Steady stream holds the average; a spike is damped, not tracked wholesale.
example : ewmaStep 3 40 40 = 40 := by decide
example : ewmaStep 3 40 120 = 50 := by decide   -- (120 + 7·40)/8 = 50, not 120
example : ewmaStep 0 40 120 = 120 := by decide   -- k=0 tracks the raw sample

#print axioms ewmaStep_le
#print axioms ewmaStep_ge
#print axioms selectLatency_min

end Proxy
