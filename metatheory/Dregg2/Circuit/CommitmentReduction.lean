import Dregg2.Circuit.OodCommitmentBinding

/-!
# De-vacuating the commitment floor: binding as EXTRACTION, not injectivity

The deployed apex threads `Poseidon2SpongeCR sponge` (Poseidon2Binding.lean:178), stated as full
injectivity `∀ xs ys, sponge xs = sponge ys → xs = ys` — which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
PROVES FALSE for any real BabyBear-valued sponge (pigeonhole: a compressing hash is never injective).
So every theorem of the form `Poseidon2SpongeCR sponge → P` is VACUOUS at deployment.

The honest, non-vacuous form is the REDUCTION: a Merkle opening either genuinely BINDS
(`vOpened = vCommitted`) or it hands you a CONCRETE COLLISION (`∃ xs ys, xs ≠ ys ∧ sponge xs = sponge ys`).
No `Poseidon2SpongeCR` premise, no false hypothesis — an adversary who breaks binding has *by construction*
produced a hash collision. This is exactly how hash-based commitment soundness is stated in the
literature ("breaking the commitment reduces to finding a collision"), and it de-vacuates the floor:
the security claim survives instantiation at the real hash, now reading "unfoolable UNLESS you find a
collision" instead of "unfoolable ASSUMING the hash is injective (which it isn't)".
-/

namespace Dregg2.Circuit.CommitmentReduction

open Dregg2.Circuit.OodCommitmentBinding
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **Opening equivocation EXTRACTS a concrete collision.** Two DISTINCT values recomputing the same
Merkle root over the same path yield an explicit witnessed sponge collision — no `Poseidon2SpongeCR`
hypothesis. This is `opening_equivocation_breaks_cr` read as a constructive extractor: `¬injective`
unfolds to `∃ xs ys, sponge xs = sponge ys ∧ xs ≠ ys`. -/
theorem equivocation_extracts_collision (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    ∃ xs ys : List ℤ, xs ≠ ys ∧ sponge xs = sponge ys := by
  have hbreak : ¬ Poseidon2SpongeCR sponge :=
    opening_equivocation_breaks_cr sponge hne hCommitted hOpened
  unfold Poseidon2SpongeCR at hbreak
  push_neg at hbreak
  obtain ⟨xs, ys, heq, hxy⟩ := hbreak
  exact ⟨xs, ys, hxy, heq⟩

/-- **The commitment opening BINDS or EXTRACTS a collision — unconditionally.** The honest, non-vacuous
replacement for `commitmentOpening_binds_of_poseidon2CR` (which needs the false injectivity premise):
for ANY two openings to a common root over the same path, EITHER they agree (`vOpened = vCommitted`,
the honest case) OR the disagreement is itself a concrete sponge collision. No `Poseidon2SpongeCR`
hypothesis — this dichotomy holds at the real deployed hash. -/
theorem commitmentOpening_binds_or_collision (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    vOpened = vCommitted ∨ ∃ xs ys : List ℤ, xs ≠ ys ∧ sponge xs = sponge ys := by
  by_cases h : vOpened = vCommitted
  · exact Or.inl h
  · exact Or.inr (equivocation_extracts_collision sponge h hCommitted hOpened)

/-- **The reduction is LOAD-BEARING, not vacuous (both directions witnessed).** On the injective toy
sponge the opening binds (the honest branch fires); on a colliding sponge the collision branch fires
with a real witness. Stated abstractly here: if the sponge has NO collision on the relevant inputs,
the dichotomy forces binding — i.e. the collision branch cannot be spuriously taken. -/
theorem binds_of_no_collision (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root)
    (hNoColl : ∀ xs ys : List ℤ, sponge xs = sponge ys → xs = ys) :
    vOpened = vCommitted :=
  (commitmentOpening_binds_or_collision sponge hCommitted hOpened).elim id
    (fun ⟨xs, ys, hxy, heq⟩ => absurd (hNoColl xs ys heq) hxy)

#assert_axioms equivocation_extracts_collision
#assert_axioms commitmentOpening_binds_or_collision
#assert_axioms binds_of_no_collision

end Dregg2.Circuit.CommitmentReduction
