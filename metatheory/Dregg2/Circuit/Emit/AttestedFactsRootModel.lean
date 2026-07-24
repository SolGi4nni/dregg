/-
# FactsRootBindingModel — the soundness HEART of the predicate `facts_root` binding

This is the model-level theorem behind the AIR residual named in
`credentials/src/verification.rs` (the FAIL-CLOSED predicate accept) and
`metatheory/Dregg2/Circuit/Emit/AttestedFactMembershipEmit.lean` §"What is NOT closed here".

## The residual, precisely

`verify_predicate_proof_third_party(proof, facts_root, state_root)` is sound in its
`state_root` argument (a genuine, trusted presentation-STARK public input) but reads
`facts_root` off `attestation.facts_root` — PROVER-SUPPLIED. A forger fabricates a fact
under A's OWN trusted `state_root`, builds a one-leaf tree containing it, publishes THAT
root as `facts_root`, and the attestation's root-equality check (`verify_fact_attestation`)
compares the prover's root to the prover's root — vacuous. So `verify()` FAILS CLOSED.

The sound fix exposes `facts_root` as a TRUSTED public input of the presentation, equal to
the Merkle root over the credential's REAL committed attribute facts. This file proves the
security content that makes that fix work: **if the attestation authenticates a member
against a `facts_root` that equals the credential's committed root, the attested member IS
one of the committed leaves** — so a fabricated fact (not among the committed leaves) has NO
authenticating co-path and the forgery is refused BY THE BINDING, not by fail-close.

## Faithfulness

* `hash4` models the deployed arity-4 `hash_4_to_1` / Poseidon2 absorb used identically by
  `build_shared_tree` (`circuit/src/dsl/fold.rs:366`) and the attestation's Merkle levels
  (`AttestedFactMembershipEmit.level0Lookup`/`level1Lookup`).
* `committedRoot` is the depth-2 4-ary root over 16 committed leaves — the tree shape the
  attestation authenticates against (`attestedFactMembershipDesc`, depth 2, `hash_4_to_1`).
* `attestedRoot` is the LEFTMOST-child authentication the DEPLOYED attestation performs
  (`prove_fact_attestation` fixes `positions = vec![0u8; ...]`; the leftmost-child convention
  is stated in `AttestedFactMembershipEmit` §"What is NOT closed here"). The descriptor's
  position gates generalize this to arbitrary slots by the identical injectivity argument.

## Honest floor

`Hash4Injective` is a HYPOTHESIS — the collision-resistance / STARK-hash floor the whole
system already stands on (`project-fri-soundness-reality`), NOT proven here. Under it the
binding is a THEOREM. The remaining obligations to deploy it (the emitted-descriptor PI, the
credential-side attribute-facts tree, the weld to trusted derivation, and the Rust un-fail-
close) are engineering named in the accompanying report — NOT discharged here.

This file imports nothing (verified with bare `lean`); it is a self-contained model.
-/

namespace Dregg2.Circuit.Emit.AttestedFactsRootModel

set_option autoImplicit false

/-- Injectivity of the deployed arity-4 compression `hash_4_to_1`, stated elementarily so this
model needs no import. This is the honest collision-resistance floor as a HYPOTHESIS. -/
def Hash4Injective {F : Type} (hash4 : F → F → F → F → F) : Prop :=
  ∀ a b c d a' b' c' d' : F,
    hash4 a b c d = hash4 a' b' c' d' →
    a = a' ∧ b = b' ∧ c = c' ∧ d = d'

/-- The depth-2 4-ary Merkle root over 16 committed leaves (leftmost-group parents chained),
byte-shaped like `build_shared_tree(_, depth=2)` and `attestedFactMembershipDesc`'s two levels. -/
def committedRoot {F : Type} (hash4 : F → F → F → F → F)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : F) : F :=
  hash4 (hash4 l0 l1 l2 l3) (hash4 l4 l5 l6 l7) (hash4 l8 l9 l10 l11) (hash4 l12 l13 l14 l15)

/-- The attestation's LEFTMOST authentication of member `m`: level-0 co-path
`(s0a,s0b,s0c)` folds `m` to `parent0`, then level-1 co-path `(s1a,s1b,s1c)` folds `parent0`
to the authenticated root. This is exactly `attestedFactMembershipDesc`'s
`level0Lookup`→`level1Lookup` chain at positions `(0,0)`. -/
def attestedRoot {F : Type} (hash4 : F → F → F → F → F)
    (m s0a s0b s0c s1a s1b s1c : F) : F :=
  hash4 (hash4 m s0a s0b s0c) s1a s1b s1c

/-- **The binding lemma (soundness HEART).** If the attestation authenticates member `m`
(with any co-path) against a root that EQUALS the credential's committed facts root, then `m`
is the committed leftmost leaf `l0` AND the whole co-path equals the committed co-path.

This is what makes a TRUSTED `facts_root` (= `committedRoot`) sound: the attestation cannot
name a member unless it is genuinely one of the committed facts. -/
theorem attested_member_is_committed {F : Type} (hash4 : F → F → F → F → F)
    (hinj : Hash4Injective hash4)
    (m s0a s0b s0c s1a s1b s1c : F)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : F)
    (hroot :
      attestedRoot hash4 m s0a s0b s0c s1a s1b s1c
        = committedRoot hash4 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) :
    m = l0 ∧ s0a = l1 ∧ s0b = l2 ∧ s0c = l3
      ∧ s1a = hash4 l4 l5 l6 l7
      ∧ s1b = hash4 l8 l9 l10 l11
      ∧ s1c = hash4 l12 l13 l14 l15 := by
  -- Peel the top-level hash: parent0 = P0, and the level-1 siblings equal the committed parents.
  have htop := hinj (hash4 m s0a s0b s0c) s1a s1b s1c
      (hash4 l0 l1 l2 l3) (hash4 l4 l5 l6 l7) (hash4 l8 l9 l10 l11) (hash4 l12 l13 l14 l15) hroot
  obtain ⟨hp0, hs1a, hs1b, hs1c⟩ := htop
  -- Peel the level-0 hash: m = l0 and the level-0 siblings equal the committed leaves.
  have hbot := hinj m s0a s0b s0c l0 l1 l2 l3 hp0
  obtain ⟨hm, h0a, h0b, h0c⟩ := hbot
  exact ⟨hm, h0a, h0b, h0c, hs1a, hs1b, hs1c⟩

/-- **No-fabrication corollary.** A member `m` that is NOT the committed leftmost leaf `l0`
authenticates to a root DIFFERENT from the committed facts root, for EVERY co-path. Hence,
once `facts_root` is the trusted committed root, a fabricated fact is REFUSED by the binding
(the attestation's root cannot equal the trusted `facts_root`) — not by fail-close.

This is exactly the forgery `cross_credential_predicate_forgery_rejected` must refuse
soundly, and the WEAKER forgery (fact fabricated under A's own `state_root`, invented
`facts_root`) the current fail-closed accept leaves open. -/
theorem fabricated_member_refused {F : Type} (hash4 : F → F → F → F → F)
    (hinj : Hash4Injective hash4)
    (m s0a s0b s0c s1a s1b s1c : F)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : F)
    (hfab : m ≠ l0) :
    attestedRoot hash4 m s0a s0b s0c s1a s1b s1c
      ≠ committedRoot hash4 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 := by
  intro hroot
  exact hfab (attested_member_is_committed hash4 hinj
    m s0a s0b s0c s1a s1b s1c
    l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 hroot).1

/-- A genuinely injective 4-ary compression: the free `node` constructor over `Nat` leaves.
Constructor injectivity is definitional, so this is a concrete model of a collision-free
`hash_4_to_1` — the assumption is CONSISTENT, so the theorems above are not vacuous. -/
inductive FTree where
  | leaf : Nat → FTree
  | node : FTree → FTree → FTree → FTree → FTree
  deriving DecidableEq

/-- **Non-vacuity of the hypothesis.** `Hash4Injective` is satisfiable by a genuine injective
4-ary compression (`FTree.node`), so the theorems above are NOT vacuously true over an empty
hypothesis. This is a witness that the assumption is consistent, NOT a claim that the deployed
Poseidon2 is provably injective (that is the honest STARK/hash floor). -/
theorem hash4Injective_is_satisfiable :
    ∃ (F : Type) (hash4 : F → F → F → F → F), Hash4Injective hash4 := by
  refine ⟨FTree, FTree.node, ?_⟩
  intro a b c d a' b' c' d' heq
  injection heq with h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

-- Concrete non-vacuity: a fabricated member (`leaf 99`) does not equal the committed leftmost
-- leaf (`leaf 7`), so under the injective `FTree.node` its authenticated root DIFFERS from the
-- committed root — the no-fabrication corollary firing on data.
example :
    attestedRoot FTree.node (.leaf 99) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)
      ≠ committedRoot FTree.node (.leaf 7) (.leaf 1) (.leaf 2) (.leaf 3) (.leaf 4) (.leaf 5)
          (.leaf 6) (.leaf 7) (.leaf 8) (.leaf 9) (.leaf 10) (.leaf 11) (.leaf 12) (.leaf 13)
          (.leaf 14) (.leaf 15) := by
  decide

end Dregg2.Circuit.Emit.AttestedFactsRootModel
