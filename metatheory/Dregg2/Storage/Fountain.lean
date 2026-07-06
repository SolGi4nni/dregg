/-
# `Dregg2.Storage.Fountain` — fountain / rateless (LT) coding decode-uniqueness, IN LEAN.

Reed–Solomon (`Erasure.lean`) is FIXED-rate. Fountain codes are RATELESS: an encoder emits an
unbounded stream of droplets, each the field-sum (XOR over GF(2)) of a random subset of the message
symbols, and a decoder recovers the whole message from ANY set of droplets that happens to cover it.
This is the decode-CORRECTNESS core, IN LEAN: over a DECODABLE droplet set, the message is UNIQUELY
recovered — the decoder cannot be tricked, and a substituted message is refused.

A droplet is a linear functional of the message, so decodability is exactly a rank condition: the
droplets' incidence vectors must span the message space (the only vector they all sum to zero on is
zero). That IS the condition belief-propagation / peeling decode needs. It is the EXACT
characterization — not a carrier. The RATELESS guarantee (a soliton-distribution random droplet set
is decodable with high probability once ~k(1+ε) droplets arrive) is the probabilistic boundary,
documented here and NOT assumed into the uniqueness theorem.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Dregg2.Tactics

namespace Dregg2.Storage

variable {F : Type*} [Field F] {k : ℕ}

/-- An LT/fountain droplet over a message `msg : Fin k → F`: the field-sum (XOR over GF(2)) of the
message symbols the droplet covers. -/
def dropletValue (msg : Fin k → F) (S : Finset (Fin k)) : F := ∑ i ∈ S, msg i

/-- A droplet set `D` is **DECODABLE** iff its incidence spans the message space — the ONLY vector
all its droplets sum to zero on is the zero vector. This is exactly the rank condition the peeling /
belief-propagation decoder needs (and what a soliton-distribution random `D` achieves w.h.p. once
enough droplets arrive — the probabilistic boundary, outside this theorem). -/
def Decodable (D : Finset (Finset (Fin k))) : Prop :=
  ∀ d : Fin k → F, (∀ S ∈ D, ∑ i ∈ S, d i = 0) → d = 0

/-- **Fountain decode-uniqueness.** Over a decodable droplet set, two messages producing the SAME
droplet values are equal — the decoder recovers the unique original and cannot be tricked into a
wrong message. Reduces to linearity of the droplet functional + the decodability (rank) condition. -/
theorem fountain_decode_unique (D : Finset (Finset (Fin k))) (hD : @Decodable F _ k D)
    (p q : Fin k → F) (hagree : ∀ S ∈ D, dropletValue p S = dropletValue q S) : p = q := by
  have hd : p - q = 0 := by
    apply hD
    intro S hS
    have h := hagree S hS
    simp only [dropletValue] at h
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp hd

/-- **No wrong recovery (the negative pole).** Two DISTINCT messages cannot produce identical
droplet values on a decodable set — so no adversary can substitute a different message under the
same recovered droplets. (Contrapositive of `fountain_decode_unique`.) -/
theorem no_wrong_recovery (D : Finset (Finset (Fin k))) (hD : @Decodable F _ k D)
    (p q : Fin k → F) (hne : p ≠ q) :
    ∃ S ∈ D, dropletValue p S ≠ dropletValue q S := by
  by_contra hcon
  apply hne
  apply fountain_decode_unique D hD p q
  intro S hS
  by_contra hSne
  exact hcon ⟨S, hS, hSne⟩

#assert_axioms dropletValue
#assert_axioms fountain_decode_unique
#assert_axioms no_wrong_recovery

end Dregg2.Storage
