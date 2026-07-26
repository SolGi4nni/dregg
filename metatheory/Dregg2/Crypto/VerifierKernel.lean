/-
# Dregg2.Crypto.VerifierKernel — Layer B: `verify` as a dischargeable contract.

The Merkle verifier whose soundness is derived from a circuit bridge rather than assumed. The shape
mirrors `stark::verify(air, proof, public_inputs)`:

- `verify : Statement → Proof → Bool` — the §8 oracle;
- `extractable : Prop` — the one genuine cryptographic carrier: STARK soundness (FRI + Fiat-Shamir)
  gives "verify accepts ⇒ a satisfying trace exists". Never proved;
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
  a satisfying trace exists. Single trust boundary; `Prop`, never proved. -/
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

`compress := (+)`, `verify` accepts iff the proof echoes a trivial self-hash trace. Witnesses the
interface is inhabitable. Not real crypto.

⚑ **CARRIER REPAIR (2026-07-25).** `extractable` here was `True` — the `extract` field then carried
all the content and the carrier carried none, so the "non-vacuity witness" passed the carrier half of
`PremiseInhabitabilitySweep.CarrierLive` BY WRITING `True`. It is now the genuine
extractability-SHAPED `Prop` over THIS oracle (the `extract` obligation instantiated at the reference
`verify`/`compress`), `extract := fun h => h` in the PortalFloor style, and the carrier is:

  * separately PROVED — `instMerkleVerifierKernel_extractable`;
  * separately REFUTED at a broken sibling — `forgeMerkleKernel_not_extractable`, a kernel whose
    node hash collapses everything to `0` and whose oracle accepts every triple. A `True` carrier
    can never be refuted anywhere; that refutation is the evidence `True` cannot produce. -/
namespace Reference

/-- Reference: `verify root leaf proof` accepts iff `proof = root` and `root = leaf + leaf`
(single-level self-hash for the toy `ℤ` model with `compress := (+)`). `extractable` is the genuine
STARK-extractability-shaped `Prop` over this oracle (NOT `True`), proved just below. -/
instance instMerkleVerifierKernel : MerkleVerifierKernel Int Int where
  compress a b := a + b
  -- accept iff the proof equals the claimed (single-level) root = leaf + leaf
  verify root leaf proof := decide (proof = root ∧ root = leaf + leaf)
  extractable :=
    ∀ (root leaf proof : Int), decide (proof = root ∧ root = leaf + leaf) = true →
      ∃ circuit : CircuitIR Int, Satisfies (fun a b => a + b) circuit root leaf
  extract := fun h => h

/-- **THE REFERENCE CARRIER HOLDS** — the extraction obligation is a THEOREM at this oracle, not an
assumption: an accepting `(root, leaf, proof)` really does exhibit a satisfying single-level Merkle
trace. This is the proof the old `extractable := True` hid inside the `extract` field. -/
theorem instMerkleVerifierKernel_extractable : instMerkleVerifierKernel.extractable := by
  intro root leaf proof haccept
  simp only [decide_eq_true_eq] at haccept
  obtain ⟨_, hroot⟩ := haccept
  -- a single self-hash level: current = leaf, sib = leaf, parent = leaf + leaf = root
  refine ⟨⟨[{ current := leaf, sib := leaf, position := 0, parent := leaf + leaf }]⟩, ?_⟩
  refine ⟨_, _, rfl, rfl, rfl, hroot.symm, ?_, ?_⟩
  · intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; rfl
  · trivial

/-- Non-vacuity: an accepted toy proof yields a genuine `MerkleMembers` witness — now discharged
with the PROVED carrier rather than `trivial`. -/
example (leaf : Int) :
    MerkleMembers (Digest := Int) (· + ·) (leaf + leaf) leaf :=
  merkle_verify_sound (K := instMerkleVerifierKernel) instMerkleVerifierKernel_extractable
    (leaf + leaf) leaf (leaf + leaf) (decide_eq_true ⟨rfl, rfl⟩)

/-! ### The refutation half — the carrier is FALSE at a broken kernel.

`PortalFloor.Reference.instVerifierForge` is the template: same carrier SHAPE, broken oracle, carrier
provably FALSE. Here the break is in the node hash rather than the acceptance bit alone: `compress`
collapses every pair to `0`, so no non-empty path can recompose a non-zero root, while `verify`
accepts every triple. The extraction shape is then a claim about traces that do not exist. -/

/-- A collapsing node hash sends every non-empty path to `0`, whatever the leaf. -/
theorem recompose_collapse (path : List (Step Int)) :
    ∀ leaf : Int, path ≠ [] → recompose (fun _ _ => (0 : Int)) leaf path = 0 := by
  induction path with
  | nil => intro _ h; exact absurd rfl h
  | cons _ rest ih =>
    intro leaf _
    cases rest with
    | nil => rfl
    | cons t ts => exact ih 0 (by simp)

/-- **FORGE INSTANCE** (`def`, not an `instance` — it must never be resolved silently): the node hash
collapses to `0` and the oracle accepts EVERYTHING. The `extractable` field carries the SAME
extraction shape as the reference kernel, instantiated at this oracle. -/
@[reducible] def forgeMerkleKernel : MerkleVerifierKernel Int Int where
  compress _ _ := 0
  verify _ _ _ := true
  extractable :=
    ∀ (root leaf _proof : Int), (true : Bool) = true →
      ∃ circuit : CircuitIR Int, Satisfies (fun _ _ => (0 : Int)) circuit root leaf
  extract := fun h => h

/-- **THE CARRIER IS FALSE HERE.** At `root = 1`, `leaf = 0` the claimed satisfying trace would give
`MerkleMembers` through the fully-proved `merkle_bridge`, i.e. a non-empty path recomposing `1` from
`0` under a hash that collapses everything to `0`. So the reference carrier is not `True` in
disguise: stripping the oracle's soundness REFUTES it. This is the evidence a `True` carrier can
never produce, and the reason `extractable := True` was a hole rather than a stylistic choice. -/
theorem forgeMerkleKernel_not_extractable : ¬ forgeMerkleKernel.extractable := by
  intro h
  obtain ⟨circuit, hsat⟩ := h 1 0 0 rfl
  obtain ⟨path, hne, hrec⟩ := (merkle_bridge (fun _ _ => (0 : Int)) 1 0).mp ⟨circuit, hsat⟩
  rw [recompose_collapse path 0 hne] at hrec
  exact absurd hrec (by decide)

/-- The forge kernel is a LAWFUL instance of the class (it type-checks, `extract` is discharged) and
its verifier accepts every triple — so `#assert_axioms`, a `sorry` scan, and an acceptance-inhabited
check all pass on it. Only the carrier refutation sees the difference. -/
theorem forgeMerkleKernel_accepts_everything (root leaf proof : Int) :
    forgeMerkleKernel.verify root leaf proof = true := rfl

end Reference

-- Carrier non-vacuity pins (PortalFloor §9c discipline): the reference carrier HOLDS, the forge
-- carrier is FALSE.
#assert_axioms Reference.instMerkleVerifierKernel_extractable
#assert_axioms Reference.forgeMerkleKernel_not_extractable

-- The derived verify law rests only on the `extractable` carrier (passed as a hypothesis).
#assert_axioms merkle_verify_sound

end Dregg2.Crypto
