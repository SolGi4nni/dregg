/-
# Dregg2.Circuit.OodCommitmentBinding — STARK-FLOOR REDUCTION 3: `hood.b` reduced to `Poseidon2SpongeCR`.

**What this closes.** `FieldIntegerLift.OodInterpF.hood` (the per-constraint OOD identity
`(constraintPoly d t c).eval ζ = Zp.eval ζ · (qp c).eval ζ`) bundles THREE sub-obligations
(`docs/reference/STARK-FLOOR-REDUCTION.md §1`):

  * (a) RLC de-batching — Schwartz–Zippel, no assumption [handled by the RLC lane];
  * (b) **commitment-opening binding** — the value `verifyAlgo` OPENS at ζ (`TableOpening.constraintEval`)
        genuinely equals the COMMITTED constraint polynomial evaluated at ζ, i.e. the Merkle/FRI opening
        BINDS — a prover cannot open the commitment to a different value [THIS FILE];
  * (c) FRI low-degreeness — the genuine hard floor [later].

Sub-obligation (b) is NOT algebra: it is a hash-binding fact. This module REDUCES it to the ONE named
hash floor `Poseidon2SpongeCR` (`Dregg2/Circuit/Poseidon2Binding.lean`, a `Prop` HYPOTHESIS, never an
`axiom`) — the SAME floor `AggAirSound.combine_digest_binds` (the CR tooth) and `FriVerifier`'s
`merkleRecompute_binds` rest on. After this, `hood.b` is a legitimately-named crypto assumption (same
status as the PQ apex's hash/lattice floors), NOT a bare `hood` premise.

## The reduction (a break ⟹ a Poseidon2 collision)

`TableOpening.constraintEval` is delivered to the verifier by a Poseidon2 Merkle opening: the opened
leaf (the field value) is recomputed up its sibling path (`FriVerifier.merkleRecompute`, the
`MerkleTreeMmcs` opening — each node hashes two child digests, order fixed by the index bit) and
compared to the committed root. We model the node hash as the ordered two-felt Poseidon2 sponge
`sponge [l, r]` — the EXACT binary specialization whose collision-resistance is `Poseidon2SpongeCR`,
identical to `AggAirSound.Hsponge`.

  * **`merkleRecomputeZ_binds`** (mirrors `FriVerifier.merkleRecompute_binds`) — under
    `Poseidon2SpongeCR`, two leaves that recompute the SAME root at the SAME query index over the SAME
    sibling path are EQUAL. Proven by induction on the path; the ONLY crypto reliance is that each node
    hash `sponge [·, ·]` is injective, which is `Poseidon2SpongeCR` (`injection` splits `[a,b]=[a',b']`).
  * **`commitmentOpening_binds_of_poseidon2CR`** (THE `hood.b` REDUCTION) — under `Poseidon2SpongeCR`,
    an opened value `vOpened` and the honest committed value `vCommitted := (constraintPoly d t c).eval ζ`
    that BOTH recompute to the same committed root ARE EQUAL: the opened `constraintEval` is BOUND to the
    committed polynomial's evaluation. An adversary opening a DIFFERENT value forces two distinct leaves
    to the same root — a Poseidon2 collision (`opening_equivocation_breaks_cr`: a break ⟹ `¬
    Poseidon2SpongeCR`). This is the honest floor, not a re-assumed `hood.b`.

Anti-ghost, witnessed BOTH ways: on the injective toy sponge (`Poseidon2Binding.Reference.refSponge`,
CR-discharged) an honest opening BINDS (`honest_opening_binds`); on a NON-injective sponge
(constant-zero) an adversary equivocates two distinct values to the same root, and that equivocation
IS a witnessed collision (`constant_sponge_equivocates` — the CR floor is load-bearing, not vacuous).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `Poseidon2SpongeCR` is a Prop
hypothesis where used, never an `axiom`. New module; not wired into `Dregg2.lean` here.

## Remaining wire to `OodInterpF.hood`

The standalone binding is proven green. To land it INTO `OodInterpF.hood` for the deployed verifier one
supplies three deployment-plumbing facts (the same "unmodeled commitment/column layout" residual the doc
names, NOT new crypto): (i) the committed root of the constraint-poly commitment and that
`verifyAlgo`'s accepted opening (`OodQuotientConsistency.verifyAlgo_accept_forces_table_identity` ties
`topen.constraintEval` to `A.mul vanishingAtZeta quotientAtZeta`) recomputes to it via `merkleRecomputeZ`;
(ii) the honest committed leaf equals `(constraintPoly d t c).eval ζ` cast to the leaf felt; (iii) the
BabyBear→ℤ canonical-representative bridge (the same one `FieldIntegerLift` carries). Given those,
`commitmentOpening_binds_of_poseidon2CR` yields `topen.constraintEval = (constraintPoly d t c).eval ζ` —
`hood.b`, now DERIVED FROM `Poseidon2SpongeCR`.
-/
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.OodCommitmentBinding

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the ordered two-felt Merkle node hash (the `Poseidon2SpongeCR` binary specialization).

A Poseidon2 `MerkleTreeMmcs` node hashes two child digests into the parent; the index bit fixes the
order (even ⇒ `acc` on the left). We model the multi-lane digest as a single felt over the list-sponge
`sponge`, so a node hash is `sponge [l, r]` — the EXACT binary specialization of the sponge whose
collision-resistance is `Poseidon2SpongeCR` (identical to `AggAirSound.Hsponge`). -/

/-- Scalar-digest Merkle-path recompute: fold the opened `leaf` (a single felt) up through the
`siblings`, hashing two child digests per level with the ordered node hash `sponge [·, ·]`, branching on
the index bit exactly as `FriVerifier.merkleRecompute` does. Structural recursion on `siblings`. -/
def merkleRecomputeZ (sponge : List ℤ → ℤ) : Nat → ℤ → List ℤ → ℤ
  | _, acc, [] => acc
  | idx, acc, s :: rest =>
      merkleRecomputeZ sponge (idx / 2)
        (if idx % 2 = 0 then sponge [acc, s] else sponge [s, acc]) rest

/-! ## §2 — the Merkle binding tooth (mirrors `FriVerifier.merkleRecompute_binds`). -/

/-- **`merkleRecomputeZ_binds` (THE ANTI-FORGERY TOOTH).** Under `Poseidon2SpongeCR`, two leaves that
recompute the SAME root at the SAME query index over the SAME sibling path are EQUAL — an attacker
cannot open a Merkle query to a forged value. Proven by induction on the path; rests ONLY on the named
sponge CR (each node hash `sponge [·, ·]` is injective, `injection` splits `[a,b] = [a',b']`). This is
`FriVerifier.merkleRecompute_binds` over the scalar-digest sponge, grounded on the named floor. -/
theorem merkleRecomputeZ_binds (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ),
      merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings →
      l1 = l2 := by
  intro siblings
  induction siblings with
  | nil => intro idx l1 l2 h; simpa [merkleRecomputeZ] using h
  | cons s rest ih =>
      intro idx l1 l2 h
      unfold merkleRecomputeZ at h
      have hstep := ih (idx / 2) _ _ h
      by_cases hb : idx % 2 = 0
      · simp only [hb, if_true] at hstep
        -- `sponge [l1, s] = sponge [l2, s]` ⇒[CR] `[l1, s] = [l2, s]` ⇒ `l1 = l2` (the head).
        exact (List.cons.inj (hCR _ _ hstep)).1
      · simp only [hb, if_false] at hstep
        -- odd index: `sponge [s, l1] = sponge [s, l2]` ⇒[CR] `[s, l1] = [s, l2]` ⇒ `l1 = l2` (tail head).
        exact (List.cons.inj (List.cons.inj (hCR _ _ hstep)).2).1

/-! ## §3 — THE `hood.b` REDUCTION: the opened value is BOUND to the committed polynomial. -/

/-- **`commitmentOpening_binds_of_poseidon2CR` (THE `hood.b` REDUCTION).** Under `Poseidon2SpongeCR`,
the value `verifyAlgo` opens at ζ (`vOpened`, the `TableOpening.constraintEval`) and the honest
committed value `vCommitted` (intended `(constraintPoly d t c).eval ζ`) that BOTH recompute to the same
committed Merkle root `root` at the same query index over the same sibling path ARE EQUAL. So the opened
`constraintEval` is BOUND to the committed polynomial's evaluation at ζ — a prover cannot open the
commitment to a different value. The ONLY crypto reliance is the named `Poseidon2SpongeCR` floor; this
is `hood.b` DERIVED, not re-assumed. -/
theorem commitmentOpening_binds_of_poseidon2CR (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    vOpened = vCommitted :=
  merkleRecomputeZ_binds sponge hCR siblings idx vOpened vCommitted (hOpened.trans hCommitted.symm)

/-- **`opening_equivocation_breaks_cr` (A BREAK ⟹ A POSEIDON2 COLLISION).** If a prover opens the SAME
committed root at the SAME query to TWO DISTINCT values (`vOpened ≠ vCommitted`), it witnesses that the
sponge is NOT collision-resistant — `¬ Poseidon2SpongeCR`. This is the load-bearing role of the Merkle
commitment: equivocating the opened `constraintEval` after ζ is fixed is EXACTLY a Poseidon2 collision.
So `hood.b` bottoms out at the hash floor and nothing weaker. -/
theorem opening_equivocation_breaks_cr (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    ¬ Poseidon2SpongeCR sponge := fun hCR =>
  hne (commitmentOpening_binds_of_poseidon2CR sponge hCR hCommitted hOpened)

/-! ## §4 — NON-VACUITY: honest openings BIND, and the CR floor is LOAD-BEARING.

The reduction would be hollow if no opening ever bound, or if it bound even without CR. We exhibit BOTH:
on the injective toy sponge (`Poseidon2Binding.Reference.refSponge`, CR-discharged) an honest opening
binds; on a NON-injective sponge (constant-zero) an adversary equivocates two DISTINCT values to the
same root — a witnessed collision showing the `Poseidon2SpongeCR` hypothesis is genuinely required. -/

section Vacuity

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- **`honest_opening_binds` (POSITIVE non-vacuity).** On the injective toy sponge whose CR is proved
(`refSponge_CR`), any two openings to a common root over the same path bind — the reduction FIRES on a
concrete CR-satisfying instance, so `commitmentOpening_binds_of_poseidon2CR` is not vacuous. -/
theorem honest_opening_binds
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ refSponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ refSponge idx vOpened    siblings = root) :
    vOpened = vCommitted :=
  commitmentOpening_binds_of_poseidon2CR refSponge refSponge_CR hCommitted hOpened

/-- The constant-zero sponge — NOT collision-resistant: it maps every input to `0`. -/
def zSponge : List ℤ → ℤ := fun _ => 0

/-- **`constant_sponge_equivocates` (the CR floor is LOAD-BEARING).** Over the constant-zero sponge, two
DISTINCT leaves (`1 ≠ 2`) recompute the SAME root (`0`) over a one-level path — an equivocation. By
`opening_equivocation_breaks_cr` this is a witnessed failure of collision-resistance: `¬
Poseidon2SpongeCR zSponge`. Without the CR hypothesis the binding is FALSE, so the floor is real, not
vacuous — exactly the `OodQuotientConsistency.ood_exceptional_escape` role for `hnonexc`. -/
theorem constant_sponge_equivocates : ¬ Poseidon2SpongeCR zSponge :=
  opening_equivocation_breaks_cr zSponge (root := 0) (idx := 0) (siblings := [5])
    (vCommitted := 2) (vOpened := 1)
    (by decide) (by simp [merkleRecomputeZ, zSponge]) (by simp [merkleRecomputeZ, zSponge])

end Vacuity

/-! ## §5 — axiom hygiene: each result pins exactly the whitelist. -/

#assert_axioms merkleRecomputeZ_binds
#assert_axioms commitmentOpening_binds_of_poseidon2CR
#assert_axioms opening_equivocation_breaks_cr
#assert_axioms honest_opening_binds
#assert_axioms constant_sponge_equivocates

end Dregg2.Circuit.OodCommitmentBinding
