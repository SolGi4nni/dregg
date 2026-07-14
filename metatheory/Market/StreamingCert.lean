/-
# Market.StreamingCert — streaming certificate accumulation: `ε_{1:T} = Σ_t ε_t`.

**The optimization analogue of a recursive turn receipt.** `Cert-F` (`Market.CertF`) proves ONE batch's
certificate sound: a linear primal-dual check ⇒ `ε`-optimality, independent of how the triple was found.
This module runs that keystone in a STREAM. A finite sequence of batches `t : Fin T` each carries its own
LP `lp t` and its own certified triple `(f t, π t, s t)`. The per-batch certificates COMPOSE into a
single cumulative certificate whose accuracy telescopes:

    ε_{1:T}  =  Σ_t ε_t,

i.e. the cumulative objective at ANY family of feasible challengers is bounded by the cumulative certified
value plus the SUMMED per-batch `ε`. Each batch's certificate is read exactly ONCE — the cumulative bound
is a `Finset.sum` of the immutable per-batch `certifies_epsilon_optimal` receipts and NEVER reopens a past
batch (`StreamCertified` is a pointwise conjunction; appending a batch only ADDS its receipt,
`streaming_cert_extends`). This is the streaming/receipt structure of dregg's turn calculus transported to
convex clearing: a running cumulative certificate assembled from past receipts that stay fixed.

## What is proved (honest scope)

  * **`streaming_cert_telescopes` — the streaming telescoping.** Given `StreamCertified` (each batch's
    triple is `Certified`) and ANY family of primal-feasible challengers `f'`:
    `Σ_t (lp t).w ⬝ᵥ (f' t) ≤ (Σ_t (lp t).w ⬝ᵥ (f t)) + Σ_t (lp t).ε`. The proof is the sum of the
    per-batch `certifies_epsilon_optimal` bounds (`Finset.sum_le_sum`) followed by `Finset.sum_add_distrib`
    — the REAL summed bound, cumulative `(Σε_t)`-optimality. No cross-batch recomputation appears.
  * **`StreamCertified` + `streaming_cert_extends` — never reopens.** The cumulative certificate is exactly
    the pointwise conjunction of the per-batch receipts; the telescoped bound is its consequence. Extending
    a length-`T` stream to `T+1` leaves every prior receipt in place and merely appends the new one
    (`Fin.sum_univ_castSucc`) — past receipts are immutable.
  * **Non-vacuity — a worked 2-batch instance (`twoBatch_streaming`).** Reuse the `Cert-F` triangle
    (`ringLP`, value `3`, `ε = 0`) for BOTH batches. `StreamCertified` holds by `ringCert_valid`; the
    cumulative certified value is `3 + 3 = 6`, the cumulative `ε` is `0`, and the telescoping bounds EVERY
    cumulative challenger by `6`. `#guard`ed concrete: cumulative value `= 6`, cumulative `ε = 0`.

Pure. Builds on the committed `Market.CertF` keystone; edits nothing there.
-/
import Market.CertF
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Market

open Matrix
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-! ## 1. A certified batch stream — the immutable per-batch receipts. -/

/-- **`StreamCertified` — the cumulative certificate is the pointwise conjunction of per-batch receipts.**
A length-`T` stream in which EVERY batch `t` carries a valid `Cert-F` certificate `(f t, π t, s t)` for its
own LP `lp t`. This IS the cumulative certificate: nothing cross-batch, just the immutable list of per-batch
`Certified` receipts. The telescoped bound (`streaming_cert_telescopes`) is a consequence of exactly this
data — a past batch's receipt is never recomputed. -/
def StreamCertified {T : ℕ} (lp : Fin T → FlowLP V E R)
    (f : Fin T → E → R) (π : Fin T → V → R) (s : Fin T → E → R) : Prop :=
  ∀ t, Certified (lp t) (f t) (π t) (s t)

/-! ## 2. THE STREAMING TELESCOPING — `ε_{1:T} = Σ_t ε_t`. -/

/-- **`streaming_cert_telescopes` — cumulative `(Σε_t)`-optimality.** Given a `StreamCertified` stream and
ANY family of primal-feasible challengers `f'` (one per batch), the CUMULATIVE objective is bounded by the
cumulative certified value plus the SUMMED per-batch accuracy:

    Σ_t (lp t).w ⬝ᵥ (f' t)  ≤  (Σ_t (lp t).w ⬝ᵥ (f t))  +  Σ_t (lp t).ε.

The proof reads each batch's certificate ONCE: `certifies_epsilon_optimal` gives the per-batch bound
`(lp t).w ⬝ᵥ (f' t) ≤ (lp t).w ⬝ᵥ (f t) + (lp t).ε`; `Finset.sum_le_sum` sums them and
`Finset.sum_add_distrib` splits the accumulated right-hand side into the cumulative certified value plus
`ε_{1:T} = Σ_t ε_t`. No batch is reopened — this is the streaming certificate accumulation. -/
theorem streaming_cert_telescopes {T : ℕ} (lp : Fin T → FlowLP V E R)
    {f : Fin T → E → R} {π : Fin T → V → R} {s : Fin T → E → R}
    (hstream : StreamCertified lp f π s)
    {f' : Fin T → E → R} (hf' : ∀ t, PrimalFeasible (lp t) (f' t)) :
    ∑ t, (lp t).w ⬝ᵥ (f' t) ≤ (∑ t, (lp t).w ⬝ᵥ (f t)) + ∑ t, (lp t).ε := by
  calc ∑ t, (lp t).w ⬝ᵥ (f' t)
      ≤ ∑ t, ((lp t).w ⬝ᵥ (f t) + (lp t).ε) :=
        Finset.sum_le_sum (fun t _ => certifies_epsilon_optimal (lp t) (hstream t) (hf' t))
    _ = (∑ t, (lp t).w ⬝ᵥ (f t)) + ∑ t, (lp t).ε := Finset.sum_add_distrib

omit [Fintype V] [PartialOrder R] [IsOrderedRing R] in
/-- **`streaming_cert_extends` — appending a batch never reopens the past.** The cumulative certified value
over `T+1` batches is the cumulative value over the first `T` (each batch's receipt UNCHANGED) plus the new
batch's receipt alone. `Fin.sum_univ_castSucc` — the streaming accumulator only ever adds the newest
receipt; prior receipts are immutable. -/
theorem streaming_cert_extends {T : ℕ} (lp : Fin (T + 1) → FlowLP V E R) (flow : Fin (T + 1) → E → R) :
    (∑ t, (lp t).w ⬝ᵥ (flow t))
      = (∑ t : Fin T, (lp t.castSucc).w ⬝ᵥ (flow t.castSucc))
        + (lp (Fin.last T)).w ⬝ᵥ (flow (Fin.last T)) :=
  Fin.sum_univ_castSucc (fun t => (lp t).w ⬝ᵥ (flow t))

/-! ## 3. NON-VACUITY — a worked 2-batch stream (both batches = the `Cert-F` triangle). -/

/-- **`twoBatch_streaming` — the cumulative certificate over two triangle batches bounds EVERY challenger by
`6`.** Reuse `ringLP` (unit-triangle, certified value `3`, `ε = 0`) for both batches of a `T = 2` stream.
`StreamCertified` holds by `ringCert_valid` at each batch; the cumulative certified value is `3 + 3 = 6` and
the cumulative accuracy is `0 + 0 = 0`, so `streaming_cert_telescopes` says: for any family of feasible
challengers `f' : Fin 2 → Fin 3 → ℤ`, `Σ_t ringLP.w ⬝ᵥ (f' t) ≤ 6`. A concrete, non-vacuous streaming
certificate. -/
theorem twoBatch_streaming {f' : Fin 2 → Fin 3 → ℤ}
    (hf' : ∀ t, PrimalFeasible ringLP (f' t)) :
    ∑ t, ringLP.w ⬝ᵥ (f' t) ≤ 6 := by
  have h := streaming_cert_telescopes (fun _ : Fin 2 => ringLP)
    (f := fun _ => ringF) (π := fun _ => ringπ) (s := fun _ => ringS)
    (fun _ => ringCert_valid) hf'
  simpa [ringLP, ringF, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] using h

/-! ### `#guard` smoke — the cumulative certificate arithmetic is COMPUTED, not asserted. -/

-- the cumulative certified value over the two triangle batches is 3 + 3 = 6:
#guard (∑ _t : Fin 2, ringLP.w ⬝ᵥ ringF) == 6
-- the cumulative accuracy telescopes to ε_{1:2} = Σ_t ε_t = 0 + 0 = 0 (both batches exact):
#guard (∑ _t : Fin 2, ringLP.ε) == 0
-- a length-2 stream has exactly two immutable per-batch receipts:
#guard (Finset.univ : Finset (Fin 2)).card == 2

/-! ### Axiom hygiene — the streaming keystones pinned kernel-clean. -/

#assert_all_clean [Market.streaming_cert_telescopes, Market.streaming_cert_extends,
  Market.twoBatch_streaming]

end Market
