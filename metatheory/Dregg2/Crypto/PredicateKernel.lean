/-
# Dregg2.Crypto.PredicateKernel — Layer C: per-kind circuit obligations + dial wiring.

Lifts `Authority/Predicate.lean`'s registry so each `WitnessedKind` carries its statement algebra,
circuit, and `Dial` floor — and wires `EpistemicDial` to the per-kind verifier (the dial's `accepts`
is pinned to the kind's verify seam, not floating above it).

This module covers the first kind end-to-end: Merkle membership. `merkleKindObligation` records
the circuit relation, statement, and dial floor (`acceptanceOnly` — the verifier learns one bit:
"it is a member", nothing about which leaf). `merkle_dial_wired` instantiates `DiscloseAt` so its
`accepts` IS the kind's verify seam at that floor.
-/
import Dregg2.Crypto.VerifierKernel
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.PredicateKernel

open Dregg2.Crypto Dregg2.Crypto.Merkle Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-! ## The per-kind obligation record (statement algebra + relation + dial floor).

The registry/dial machinery lives at `Type` (universe 0); `MerkleVerifierKernel` is universe-polymorphic
and restricts cleanly. -/

/-- `KindObligation` — per-kind discharge data: the public-input `Statement` type, the `relation`
the AIR encodes (proved equivalent to circuit-satisfiability by the gadget bridge), and the
`dialFloor` — the epistemic boundary this kind discloses at. -/
structure KindObligation (Digest Proof : Type) where
  /-- The public-input algebra for this kind (e.g. `Digest × Digest` for Merkle `(root,leaf)`). -/
  Statement : Type
  /-- The relation the AIR encodes (membership, for Merkle), as a predicate on the statement. -/
  relation : Statement → Prop
  /-- The epistemic disclosure floor (`EpistemicDial.Dial`). -/
  dialFloor : Dial

/-! ## The Merkle kind — statement `(root, leaf)`, relation `MerkleMembers`, floor `acceptanceOnly`. -/

variable {Digest Proof : Type}

/-- The Merkle kind's obligation. Statement = `(root, leaf)`; relation = `MerkleMembers`;
dial floor = `acceptanceOnly` — the verifier learns one bit (membership), not which leaf. -/
def merkleKindObligation [K : MerkleVerifierKernel Digest Proof] :
    KindObligation Digest Proof where
  Statement := Digest × Digest
  relation := fun s => MerkleMembers K.compress s.1 s.2
  dialFloor := Dial.acceptanceOnly

@[simp] theorem merkleKindObligation_floor [MerkleVerifierKernel Digest Proof] :
    (merkleKindObligation (Digest := Digest) (Proof := Proof)).dialFloor = Dial.acceptanceOnly :=
  rfl

/-! ## The cascade — registry dispatch ∘ derived verify-soundness, per kind. -/

/-- The Merkle verifier plugin for the registry: the §8 `verify` oracle wrapped to the
`Verifier (Digest × Digest) Proof` shape (statement = `(root, leaf)`). -/
def merkleVerifier [K : MerkleVerifierKernel Digest Proof] :
    Verifier (Digest × Digest) Proof :=
  fun s proof => K.verify s.1 s.2 proof

/-- `merkle_registry_cascade` — an accepted Merkle proof both `Discharged`s the registry predicate
(`registry_sound`) and, given the STARK `extractable` carrier, proves `MerkleMembers`
(`merkle_verify_sound`). The single trust boundary is `extractable`; membership recomposition is
fully proved. -/
theorem merkle_registry_cascade [K : MerkleVerifierKernel Digest Proof]
    (hext : K.extractable)
    (base : Registry (Digest × Digest) Proof)
    (root leaf : Digest) (proof : Proof)
    (haccept : K.verify root leaf proof = true) :
    let reg : Registry (Digest × Digest) Proof :=
      fun j => if j = .merkleMembership then some merkleVerifier else base j
    (@Discharged (Digest × Digest) Proof (verifiableOfRegistry reg .merkleMembership)
        (root, leaf) proof)
      ∧ MerkleMembers K.compress root leaf := by
  intro reg
  refine ⟨?_, merkle_verify_sound hext root leaf proof haccept⟩
  apply registry_sound reg .merkleMembership (root, leaf) proof
  show registryVerify reg .merkleMembership (root, leaf) proof = true
  unfold registryVerify
  simp only [reg, if_pos rfl]
  exact haccept

/-- The Merkle-kind registry: the §8 `verify` oracle installed at `merkleMembership`. -/
def merkleReg [MerkleVerifierKernel Digest Proof]
    (base : Registry (Digest × Digest) Proof) : Registry (Digest × Digest) Proof :=
  fun j => if j = .merkleMembership then some merkleVerifier else base j

/-- The `Verifiable` seam this kind dispatches through. Explicit `def` (not auto-synthesized
`instance`) so `Discharged`/`DiscloseAt` share the same instance. -/
@[reducible] def merkleSeam [MerkleVerifierKernel Digest Proof]
    (base : Registry (Digest × Digest) Proof) : Verifiable (Digest × Digest) Proof :=
  verifiableOfRegistry (merkleReg base) .merkleMembership

/-! ## Dial wiring — `DiscloseAt` instantiated at the Merkle kind's floor.

The dial's `accepts` is pinned to `Discharged (root,leaf) proof` under the registry seam, so the
dial's acceptance bit IS the Merkle verifier's bit at the `acceptanceOnly` floor. -/

/-- `merkleDisclose` — a `DiscloseAt` over `Unit` whose `accepts d := Discharged (root,leaf) proof`
(position-independent). Realizes the dial at the `acceptanceOnly` (blinded membership) floor. -/
def merkleDisclose [MerkleVerifierKernel Digest Proof]
    (base : Registry (Digest × Digest) Proof) (root leaf : Digest) (proof : Proof) :
    @DiscloseAt Unit (Digest × Digest) Proof _ (merkleSeam base) :=
  letI : Verifiable (Digest × Digest) Proof := merkleSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := (root, leaf)
    wit := proof
    accepts := fun _ => Discharged (root, leaf) proof
    accepts_eq := fun _ => Iff.rfl }

/-- `merkle_dial_wired` — the Merkle kind's floor is `acceptanceOnly`; at that floor the dial's
acceptance bit is exactly the Merkle verifier's `Discharged` bit; and given STARK `extractable`,
that bit proves `MerkleMembers`. The dial is pinned to the per-kind verifier. -/
theorem merkle_dial_wired [K : MerkleVerifierKernel Digest Proof]
    (hext : K.extractable)
    (base : Registry (Digest × Digest) Proof) (root leaf : Digest) (proof : Proof) :
    -- (1) the floor is acceptanceOnly:
    (merkleKindObligation (Digest := Digest) (Proof := Proof)).dialFloor = Dial.acceptanceOnly ∧
    -- (2) the dial's bottom notch accepts IFF the Merkle verifier discharges:
    (@DiscloseAt.accepts Unit (Digest × Digest) Proof _ (merkleSeam base)
        (merkleDisclose base root leaf proof) (⊥ : Dial)
      ↔ @Discharged (Digest × Digest) Proof (merkleSeam base) (root, leaf) proof) ∧
    -- (3) and an accepting Merkle proof at the floor PROVES membership (the cascade):
    (K.verify root leaf proof = true → MerkleMembers K.compress root leaf) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Digest × Digest) Proof _ (merkleSeam base)
      (merkleDisclose base root leaf proof)
  · exact fun haccept => merkle_verify_sound hext root leaf proof haccept

/-! ## `Reference` — the whole cascade end-to-end at the toy kernel (non-vacuity witness). -/

namespace Reference

open Dregg2.Crypto.Reference

/-- The empty base registry over the toy `ℤ` statement/proof. -/
def base : Registry (Int × Int) Int := fun _ => none

/-- Non-vacuity: at the reference Merkle verifier kernel, an accepted toy proof drives the
FULL cascade — it `Discharged`s the registry predicate AND proves `MerkleMembers`. This
witnesses `merkle_registry_cascade` is not over an empty world. -/
example (leaf : Int) :
    (@Discharged (Int × Int) Int
        (verifiableOfRegistry (merkleReg base) .merkleMembership)
        (leaf + leaf, leaf) (leaf + leaf))
      ∧ MerkleMembers (Digest := Int) (· + ·) (leaf + leaf) leaf :=
  merkle_registry_cascade (K := instMerkleVerifierKernel) instMerkleVerifierKernel_extractable
    base (leaf + leaf) leaf (leaf + leaf) (decide_eq_true ⟨rfl, rfl⟩)

/-- Non-vacuity: the dial wiring holds at the reference kernel — the floor is `acceptanceOnly`,
the dial's bottom notch is the verifier's bit, and an accepting proof proves membership. -/
example (leaf : Int) :
    (merkleKindObligation (Digest := Int) (Proof := Int)).dialFloor = Dial.acceptanceOnly :=
  (merkle_dial_wired (K := instMerkleVerifierKernel) instMerkleVerifierKernel_extractable base
    (leaf + leaf) leaf (leaf + leaf)).1

end Reference

-- The cascade + dial wiring rest only on the `extractable` carrier (as a hypothesis).
#assert_axioms merkle_registry_cascade
#assert_axioms merkle_dial_wired

end Dregg2.Crypto.PredicateKernel
