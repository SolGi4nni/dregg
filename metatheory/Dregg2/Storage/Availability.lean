/-
# `Dregg2.Storage.Availability` — the end-to-end verifiable-erasure-coded storage theorem, IN LEAN.

Composes the storage-in-lean cluster: a light client holding ONLY the content root can reconstruct
the true blob from any `k` genuine shards, with no trust in any provider.

The chain:
- `BucketCommitment.read_sound_or_collides` / `Retrievability.por_sound_or_collides`: a served shard
  that opens against the committed root IS the genuine committed shard, OR the provider exhibited a
  specific sponge collision. (⚑ 2026-07-25 cutover: the old `read_sound` / `por_sound` were gated on the
  REFUTED `Poseidon2SpongeCR` and vacuous at the deployed hash; the successors are UNCONDITIONAL.)
- `Erasure.rs_decode_correct`: any `k` genuine shards (evals of the degree-`< k` message polynomial
  at `k` distinct code points) determine the UNIQUE message.

So: audit `k` shards genuine (por), then decode — the client recovers the true blob and cannot be
fed a wrong one. The genuine-shard link is `por_sound_or_collides` (the audit); the reconstruction is
`rs_decode_correct` (the code). Both are real theorems; the audit leg now assumes NO hash floor at all
— it delivers "genuine, or here is the collision" — and the algebra carries the standard axioms.
-/
import Dregg2.Storage.Erasure
import Dregg2.Storage.Retrievability

namespace Dregg2.Storage

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Verifiable erasure-coded recovery.** The true blob is the message polynomial `p` (degree
`< k`), RS-encoded at `n` distinct code points. A client audits a set `S` of `≥ k` shard positions
genuine (each equals `p`'s eval there — established by `por_sound_or_collides`/`read_sound_or_collides`
against the committed root) and runs any degree-`< k` decoder; the decoder output `candidate` IS `p`. The client recovers
the TRUE blob and cannot be tricked into a wrong reconstruction — holding only the root. -/
theorem verifiable_erasure_recovers (k n : ℕ) (p candidate : F[X])
    (hp : p.natDegree < k) (hc : candidate.natDegree < k)
    (pts : Fin n → F) (hinj : Function.Injective pts)
    (S : Finset (Fin n)) (hk : k ≤ S.card)
    (haudit : ∀ i ∈ S, encodeShard candidate (pts i) = encodeShard p (pts i)) :
    candidate = p := by
  apply rs_decode_correct k p candidate hp hc (S.image pts)
  · rwa [Finset.card_image_of_injective S hinj]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact haudit i hi

#assert_axioms verifiable_erasure_recovers

end Dregg2.Storage
