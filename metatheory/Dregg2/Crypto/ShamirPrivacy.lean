/-
# `Dregg2.Crypto.ShamirPrivacy` — the information-theoretic security foundation of threshold signatures.

`Frost.lean` (classical) and `HermineThreshold.lean` (post-quantum) proved that a `t`-of-`n` quorum
certificate CORRECTLY verifies under the group key, given the Lagrange/Vandermonde reconstruction
`secret = Σ λ_i · share_i`. But WHY is a threshold scheme secure — why does a corrupt MINORITY of
signers learn nothing about the group key? That is the load-bearing security lemma under BOTH schemes,
and unlike the full EUF-CMA unforgeability reduction (a random-oracle / forking-lemma affair we keep as
a named carrier), this half is UNCONDITIONAL and cleanly provable: **Shamir `t`-privacy.**

The group secret is a polynomial `p` of degree `< t` evaluated at 0; signer `i` holds the share `p(i)`.
The theorem: for ANY set of `t-1` observed shares and ANY candidate secret `s`, there is a degree-`<t`
polynomial consistent with both. So the `t-1` shares an adversary corrupts are consistent with EVERY
secret — they information-theoretically reveal nothing about the group key. A quorum of `t` is the
strict threshold at which the secret becomes determined; below it, perfect privacy.

Proved via Mathlib's Lagrange interpolation: `t-1` share points plus the point `(0, s)` are `t` nodes,
which a degree-`<t` polynomial interpolates exactly.
-/
import Dregg2.Tactics
import Mathlib.LinearAlgebra.Lagrange

namespace Dregg2.Crypto.ShamirPrivacy

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Shamir `t`-privacy.** Let `T` be the `t-1` distinct evaluation points a corrupt minority of
signers holds (none of them `0`, the secret's point), and `shares : F → F` the values they observe.
Then for ANY candidate group secret `secret`, there is a sharing polynomial `p` of degree `< t` that
is consistent with BOTH — it hits every observed share (`p(i) = shares i` on `T`) and evaluates to
`secret` at `0`. Since this holds for every `secret`, the `t-1` observed shares reveal NOTHING about
the group key: a corrupt minority cannot distinguish which secret was shared. (A quorum of `t` is the
strict threshold at which the secret becomes uniquely determined.) -/
theorem shamir_t_privacy (t : ℕ) (ht : 1 ≤ t) (T : Finset F) (hcard : T.card = t - 1)
    (h0 : (0 : F) ∉ T) (shares : F → F) (secret : F) :
    ∃ p : F[X], p.degree < (t : ℕ) ∧ p.eval 0 = secret ∧ ∀ i ∈ T, p.eval i = shares i := by
  classical
  -- Interpolate through the `t` nodes `T ∪ {0}`, locations = the points themselves, values below.
  let nodes : Finset F := insert 0 T
  let val : F → F := fun x => if x = 0 then secret else shares x
  have hinj : Set.InjOn (id : F → F) (nodes : Set F) := Set.injOn_id _
  refine ⟨Lagrange.interpolate nodes id val, ?_, ?_, ?_⟩
  · -- degree < #nodes = (t-1) + 1 = t
    have hdeg := Lagrange.degree_interpolate_lt (v := (id : F → F)) (r := val) hinj
    have hn : nodes.card = t := by
      show (insert 0 T).card = t
      rw [Finset.card_insert_of_notMem h0, hcard]
      omega
    rwa [hn] at hdeg
  · -- eval at 0 = secret
    have h0mem : (0 : F) ∈ nodes := Finset.mem_insert_self 0 T
    have := Lagrange.eval_interpolate_at_node val hinj h0mem
    simpa only [id_eq, val, if_pos rfl] using this
  · -- eval at each observed point i ∈ T = shares i
    intro i hi
    have himem : i ∈ nodes := Finset.mem_insert_of_mem hi
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
    have := Lagrange.eval_interpolate_at_node val hinj himem
    simpa only [id_eq, val, if_neg hi0] using this

/-- **Corollary — every secret is equally consistent.** Two different candidate secrets both admit a
degree-`<t` sharing matching the same `t-1` observed shares. Formalizes "the minority cannot tell the
secrets apart" as the existence of witnesses for both. -/
theorem shamir_secret_indistinguishable_below_threshold (t : ℕ) (ht : 1 ≤ t) (T : Finset F)
    (hcard : T.card = t - 1) (h0 : (0 : F) ∉ T) (shares : F → F) (s₀ s₁ : F) :
    (∃ p : F[X], p.degree < (t : ℕ) ∧ p.eval 0 = s₀ ∧ ∀ i ∈ T, p.eval i = shares i) ∧
    (∃ q : F[X], q.degree < (t : ℕ) ∧ q.eval 0 = s₁ ∧ ∀ i ∈ T, q.eval i = shares i) :=
  ⟨shamir_t_privacy t ht T hcard h0 shares s₀, shamir_t_privacy t ht T hcard h0 shares s₁⟩

#assert_axioms shamir_t_privacy
#assert_axioms shamir_secret_indistinguishable_below_threshold

end Dregg2.Crypto.ShamirPrivacy
