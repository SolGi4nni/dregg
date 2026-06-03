/-
# Dregg2.Crypto.VerifierKernel — Layer B: `verify` as a dischargeable contract.

The Merkle verifier whose soundness is derived from a circuit bridge rather than assumed. The shape
mirrors `stark::verify(air, proof, public_inputs)`:

- `verify : Statement → Proof → Bool` — the §8 oracle;
- `extractable : Prop` — the one genuine cryptographic carrier: STARK soundness (FRI + Fiat-Shamir)
  gives "verify accepts ⇒ a satisfying trace exists". Never proved, never `sorry`;
- `merkle_verify_sound` — derived: accept ⇒ `MerkleMembers`, by composing `extractable` with
  `merkle_bridge` (satisfying circuit ⇔ membership, fully proved, no primitive seam).
-/
import Dregg2.Crypto.Merkle
import Dregg2.Tactics

namespace Dregg2.Crypto

open Dregg2.Crypto.Merkle

universe u

/-! ## The Merkle verifier kernel — `verify` + `extractable` carrier + derived `verify_sound`. -/

/-- The Merkle `VerifierKernel` (Layer B). `verify` is the §8 oracle; `extractable` is the
STARK-soundness carrier (FRI + Fiat-Shamir): if `verify` accepts, a satisfying AIR trace exists.
`verify_sound` is derived off `merkle_bridge` — "accept ⇒ membership" given `extractable`. -/
class MerkleVerifierKernel (Digest : Type u) (Proof : Type u) where
  /-- The abstract Poseidon2 node hash (the Layer-A `compress`; CR is `collisionHard`). -/
  compress : Digest → Digest → Digest
  /-- The §8 verify oracle: does `proof` discharge the statement `(root, leaf)`? Opaque `Bool`;
  soundness is the carried `extractable`. -/
  verify : Digest → Digest → Proof → Bool
  /-- CARRIER — STARK extractability/soundness (FRI proximity + Fiat-Shamir): `verify` accepts ⇒
  a satisfying trace exists. Single trust boundary; `Prop`, never proved, never `sorry`. -/
  extractable : Prop
  /-- `extractable` unpacked: an accepted proof witnesses a satisfying circuit. -/
  extract : extractable →
    ∀ (root leaf : Digest) (proof : Proof), verify root leaf proof = true →
      ∃ circuit : CircuitIR Digest, Satisfies compress circuit root leaf

variable {Digest Proof : Type u}

/-- `merkle_verify_sound` — given `extractable`, an accepted Merkle proof proves membership:
`verify root leaf proof = true → MerkleMembers compress root leaf`. Derived by composing
`extract` (accept ⇒ satisfying trace) with `merkle_bridge` (satisfying trace ⇔ membership,
fully proved). The only hypothesis is `extractable`. -/
theorem merkle_verify_sound [K : MerkleVerifierKernel Digest Proof]
    (hext : K.extractable) (root leaf : Digest) (proof : Proof)
    (haccept : K.verify root leaf proof = true) :
    MerkleMembers K.compress root leaf :=
  (merkle_bridge K.compress root leaf).mp (K.extract hext root leaf proof haccept)

/-! ## Reference verifier kernel — non-vacuity witness over `ℤ`.

`compress := (+)`, `verify` accepts iff the proof echoes a trivial self-hash trace,
`extractable := True`. Witnesses the interface is inhabitable. Not real crypto. -/
namespace Reference

/-- Reference: `verify root leaf proof` accepts iff `proof = root` and `root = leaf + leaf`
(single-level self-hash for the toy `ℤ` model with `compress := (+)`). -/
instance instMerkleVerifierKernel : MerkleVerifierKernel Int Int where
  compress a b := a + b
  -- accept iff the proof equals the claimed (single-level) root = leaf + leaf
  verify root leaf proof := decide (proof = root ∧ root = leaf + leaf)
  extractable := True
  extract := by
    intro _ root leaf proof haccept
    simp only [decide_eq_true_eq] at haccept
    obtain ⟨_, hroot⟩ := haccept
    -- a single self-hash level: current = leaf, sib = leaf, parent = leaf + leaf = root
    refine ⟨⟨[{ current := leaf, sib := leaf, position := 0, parent := leaf + leaf }]⟩, ?_⟩
    refine ⟨_, _, rfl, rfl, rfl, hroot.symm, ?_, ?_⟩
    · intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; rfl
    · trivial

/-- Non-vacuity: an accepted toy proof yields a genuine `MerkleMembers` witness. -/
example (leaf : Int) :
    MerkleMembers (Digest := Int) (· + ·) (leaf + leaf) leaf :=
  merkle_verify_sound (K := instMerkleVerifierKernel) trivial (leaf + leaf) leaf (leaf + leaf)
    (decide_eq_true ⟨rfl, rfl⟩)

end Reference

-- Tripwire: the derived verify law rests only on the `extractable` carrier (passed as a
-- hypothesis), never on a hidden `sorry`.
#assert_axioms merkle_verify_sound

end Dregg2.Crypto
