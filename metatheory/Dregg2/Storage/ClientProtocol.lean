/-
# `Dregg2.Storage.ClientProtocol` — the end-to-end guarantee, one theorem.

Everything the storage-in-Lean layer proved, composed into the promise a client actually cares about:
store an erasure-coded blob across `n` providers, and

1. **the data survives** as long as `k` providers pass their audit (they hold genuine shards, so RS
   reconstruction recovers the original — `Availability.verifiable_erasure_recovers`);
2. **honest providers keep their bond** (a passing PoR audit ⟹ `auditedPass`, from which slash is
   impossible — `MarketAudit.honest_provider_not_slashed`, made meaningful by
   `Retrievability.por_sound_or_collides`);
3. **withholding providers are slashed** (a failing audit ⟹ `auditedFail`, from which slash succeeds —
   `MarketAudit.withholding_is_slashable`; and `por_substitution_forces_collision` means faking a pass
   would FORCE a genuine sponge collision).

The proof is one term: the three guarantees are exactly the composition of the pieces. That is the
whole point of building the protocol in Lean — the end-to-end promise is *derived*, not asserted.
-/
import Dregg2.Storage.Availability
import Dregg2.Storage.MarketAudit

namespace Dregg2.Storage.ClientProtocol

open Polynomial
open Dregg2.Storage
open Dregg2.Storage.DealLifecycle
open Dregg2.Storage.MarketAudit

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The client's end-to-end guarantee.** For an erasure-coded blob `p` (degree `< k`) spread over
`n` distinct code points, with `honest` a set of `≥ k` providers whose shards match `p`'s, and one
honest deal (audit passed) and one withholding deal (audit failed):

* the decoder recovers the TRUE blob (`candidate = p`),
* the honest provider CANNOT be slashed,
* the withholding provider IS slashed.

Composes `verifiable_erasure_recovers` + `honest_provider_not_slashed` + `withholding_is_slashable`. -/
theorem data_survives_and_cheaters_pay (k n : ℕ) (p candidate : F[X])
    (hp : p.natDegree < k) (hc : candidate.natDegree < k)
    (pts : Fin n → F) (hinj : Function.Injective pts)
    (honest : Finset (Fin n)) (hk : k ≤ honest.card)
    (haudit : ∀ i ∈ honest, encodeShard candidate (pts i) = encodeShard p (pts i))
    (dh dh' : Deal) (hah : dh.state = .active) (hrunh : runAudit dh true = some dh')
    (dw dw' : Deal) (haw : dw.state = .active) (hrunw : runAudit dw false = some dw') (pen : Nat) :
    candidate = p
      ∧ (∀ q, slash dh' q = none)
      ∧ slash dw' pen = some { state := .slashed, bond := dw'.bond - pen } :=
  ⟨verifiable_erasure_recovers k n p candidate hp hc pts hinj honest hk haudit,
   fun q => honest_provider_not_slashed dh dh' hah hrunh q,
   withholding_is_slashable dw dw' haw hrunw pen⟩

#assert_axioms data_survives_and_cheaters_pay

end Dregg2.Storage.ClientProtocol
