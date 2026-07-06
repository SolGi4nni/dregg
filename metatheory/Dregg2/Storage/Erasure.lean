/-
# `Dregg2.Storage.Erasure` — Reed–Solomon erasure coding correctness, IN LEAN.

The Rust `storage::erasure` encodes a blob into `n = k · expansion` shards where ANY `k` suffice to
reconstruct (true k-of-n / MDS). This is that codec's correctness as the source-of-truth theorem.

RS is polynomial evaluation: a message is a polynomial `p` of degree `< k` over a field; the shards
are `p` evaluated at `n` DISTINCT points; a decoder reads any `k` shards and interpolates. The
load-bearing fact — the whole reason the code is k-of-n — is that a degree-`< k` polynomial is
UNIQUELY pinned by its values at any `k` distinct points. So a decoder that finds ANY degree-`< k`
polynomial matching `k` received shards recovers the UNIQUE original: no wrong reconstruction exists.

This is REAL algebra (no crypto carrier): it reduces to `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`
over a field. The concrete GF(2⁸) systematic-matrix impl in Rust is the SAME code (a Vandermonde
generator = evaluation at points); binding that fast impl to this spec is a diff-test, not a carrier.
-/
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Tactics

namespace Dregg2.Storage

open Polynomial

variable {F : Type*} [Field F]

/-- A shard: the message polynomial evaluated at one code point. The encoder emits one per point. -/
def encodeShard (p : F[X]) (x : F) : F := p.eval x

/-- **RS is a code: the message is uniquely pinned by any `k` shards.** Two degree-`< k` messages
whose shards AGREE on a set of `≥ k` DISTINCT code points are EQUAL. -/
theorem message_unique_of_k_shards (k : ℕ) (p q : F[X])
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (pts : Finset F) (hcard : k ≤ pts.card)
    (hagree : ∀ x ∈ pts, encodeShard p x = encodeShard q x) : p = q := by
  apply eq_of_natDegree_lt_card_of_eval_eq' p q pts hagree
  exact lt_of_lt_of_le (max_lt hp hq) hcard

/-- **RS decode-correctness — true k-of-n reconstruction.** If the true message `p` (degree `< k`)
was encoded, and a decoder produces ANY degree-`< k` candidate `q` whose shards match `p`'s on `k`
distinct received points, then `q` IS `p`. The decoder recovers the original from any `k` of the `n`
shards — and cannot be tricked into a wrong reconstruction. -/
theorem rs_decode_correct (k : ℕ) (p candidate : F[X])
    (hp : p.natDegree < k) (hcand : candidate.natDegree < k)
    (received : Finset F) (hk : k ≤ received.card)
    (hmatch : ∀ x ∈ received, encodeShard candidate x = encodeShard p x) :
    candidate = p :=
  message_unique_of_k_shards k candidate p hcand hp received hk hmatch

/-- **No collision (the negative pole).** Two DISTINCT degree-`< k` messages cannot produce the same
shards on `k` distinct points — so no adversary can substitute a different blob under the same `k`
recovered shards. (Contrapositive of `message_unique_of_k_shards`.) -/
theorem no_wrong_reconstruction (k : ℕ) (p q : F[X])
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (pts : Finset F) (hcard : k ≤ pts.card) (hne : p ≠ q) :
    ∃ x ∈ pts, encodeShard p x ≠ encodeShard q x := by
  by_contra hcon
  apply hne
  apply message_unique_of_k_shards k p q hp hq pts hcard
  intro x hx
  by_contra hxne
  exact hcon ⟨x, hx, hxne⟩

#assert_axioms message_unique_of_k_shards
#assert_axioms rs_decode_correct
#assert_axioms no_wrong_reconstruction

end Dregg2.Storage
