/-
# Dregg2.Crypto.Primitives — Layer A: cryptographic operations with algebraic laws + hardness carriers.

Separates algebraic laws (proved, used by the metatheory) from computational hardness obligations
(carried as `Prop`, discharged by the crypto layer, never proved in Lean):

- `commit_hom` (Pedersen additive homomorphism) — proved field, the metatheory's conservation tier.
- `collisionHard` (Poseidon2 CR), `binding` (DLog), `unlinkable` (anonymity) — `Prop` carriers.

`compress`/`compressN` are uninterpreted; their only law is the carried `collisionHard`, not an
equational idealization.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

namespace Dregg2.Crypto

universe u

/-- `CryptoPrimitives` — cryptographic operations with algebraic laws and hardness carriers.
`Digest` is the hash/commitment type (`AddCommGroup` because Pedersen commitments compose).
`commit_hom` is the one proved algebraic law; `collisionHard`/`binding`/`unlinkable` are `Prop`
carriers — genuine cryptographic assumptions, never proved, never `sorry`. -/
class CryptoPrimitives (Digest : Type u) [AddCommGroup Digest] where
  /-- Poseidon2 4-to-1 compression (`hash_2_to_1`, the Merkle node hash). Uninterpreted —
  collision-resistance is the carried `collisionHard`, not an equational law. -/
  compress : Digest → Digest → Digest
  /-- Poseidon2 sponge (`hash_many`): absorb a list of digests, squeeze one. Uninterpreted;
  CR is `collisionHard`. -/
  compressN : List Digest → Digest
  /-- CARRIER — Poseidon2 collision-resistance (`Prop`, never proved, never `sorry`). The correct
  assumption: CR, not idealized injectivity. -/
  collisionHard : Prop
  /-- **Pedersen commitment** `commit value blinding` over the curve. -/
  commit : Int → Int → Digest
  /-- Law (proved) — Pedersen additive homomorphism: the one algebraic law the metatheory relies
  on (conservation over hidden amounts). -/
  commit_hom : ∀ v w r s, commit (v + w) (r + s) = commit v r + commit w s
  /-- CARRIER — Pedersen/DLog binding (`Prop`, never a Lean law): a commitment cannot be opened
  to two distinct values. -/
  binding : Prop
  /-- Deterministic per-note nullifier (Zcash anti-double-spend tag). Function-ness is proved;
  only anonymity is carried. -/
  nullifier : Digest → Digest
  /-- CARRIER — nullifier/stealth unlinkability (anonymity advantage; `Prop`, never a Lean law). -/
  unlinkable : Prop

variable {Digest : Type u} [AddCommGroup Digest]

/-! ## Algebraic consequences proved from the homomorphism alone. -/

/-- `commit 0 0 = 0`, derived from `commit_hom` alone (cancellation in the `AddCommGroup`). -/
theorem commit_zero [CryptoPrimitives Digest] :
    (CryptoPrimitives.commit (0 : Int) (0 : Int) : Digest) = 0 := by
  have h := CryptoPrimitives.commit_hom (Digest := Digest) 0 0 0 0
  simp only [add_zero] at h
  have h2 : CryptoPrimitives.commit (0 : Int) (0 : Int) + (0 : Digest)
      = CryptoPrimitives.commit (0 : Int) (0 : Int)
        + CryptoPrimitives.commit (0 : Int) (0 : Int) := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- Nullifier determinism — function-ness, the only fact the anti-double-spend gate needs. -/
theorem nullifier_deterministic [CryptoPrimitives Digest] {d d' : Digest} (h : d = d') :
    CryptoPrimitives.nullifier d = CryptoPrimitives.nullifier d' := by rw [h]

/-! ## Reference instance — non-vacuity witness over `ℤ`.

A trivial lawful instance with hardness carriers `:= True`. Witnesses that `CryptoPrimitives` is
inhabitable and parametric theorems are non-vacuous. Not real crypto. -/
namespace Reference

instance instCryptoPrimitives : CryptoPrimitives Int where
  compress a b := a + b
  compressN l := l.sum
  collisionHard := True
  commit v r := v + r
  commit_hom := by intro v w r s; ring
  binding := True
  nullifier d := d
  unlinkable := True

example : (CryptoPrimitives.commit (0 : Int) (0 : Int) : Int) = 0 := commit_zero

end Reference

end Dregg2.Crypto
