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

## ⚑ The floor this file used to stand on is FALSE, and the binding now stands without it

`Hash4Injective` — global injectivity of a 4-to-1 compression — is REFUTED at every finite
carrier by `AttestedFactsRootRegrounded.hash4Injective_false_of_finite`, hence at the deployed
BabyBear field. It is pure pigeonhole: fixing two of the four arguments embeds `F × F` into `F`,
so the floor forces `|F|² ≤ |F|`. No Poseidon2 collision is exhibited and none is needed. The
old docstring called it "the honest collision-resistance floor"; it was neither honest nor a
floor, and both consumers here were vacuous at deployed parameters.

The consumers are now stated on `Coll4` — a PER-INSTANCE non-collision residual at the EXACT
two argument quadruples the two-level peel compares, and nowhere else. Both poles are proved
(`coll4_self_false` dischargeable, `coll4_of_constant` refutable), and
`coll4_breaks_hash4Injective` records that the deleted floor implied every residual, so the
port is visibly a WEAKENING of the hypothesis rather than a change of subject. What a caller
must now supply is a statement about the two preimage quadruples actually presented — the
shape a keyed-ROM advantage bound discharges (`Crypto.RomQueryFloor.birthday_bound`, PROVED),
which global injectivity never was.

The remaining obligations to deploy the binding (the emitted-descriptor PI, the credential-side
attribute-facts tree, the weld to trusted derivation, and the Rust un-fail-close) are
engineering named in the accompanying report — NOT discharged here.

This file imports nothing (verified with bare `lean`); it is a self-contained model. The tooth
needs a cardinality argument and therefore Mathlib, so it lives in the sibling
`AttestedFactsRootRegrounded` and this file keeps its bare-`lean` property.
-/

namespace Dregg2.Circuit.Emit.AttestedFactsRootModel

set_option autoImplicit false

/-- ⚠ **REFUTED AT EVERY FINITE CARRIER — see `AttestedFactsRootRegrounded.
hash4Injective_false_of_finite`, and NO LONGER ASSUMED ANYWHERE.** Global injectivity of the
deployed arity-4 compression `hash_4_to_1`: four field elements in, one out. Fixing two
arguments embeds `F × F` into `F`, so this forces `|F|² ≤ |F|` and is false for any `F` with
more than one element — the deployed BabyBear field included. KEPT for the record (the campaign
convention: the old carrier stays doc-marked beside its tooth); the honest per-instance
replacement is `Coll4`. -/
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

/-! ## The per-instance residual — the honest replacement for the refuted floor. -/

/-- **`Coll4 hash4 a b c d a' b' c' d'`** — a collision of the arity-4 compression at ONE named
pair of argument quadruples: the quadruples DIFFER, yet their images agree. This is what the
refuted `Hash4Injective` implied at every quadruple at once (`coll4_breaks_hash4Injective`), and
unlike that floor it is both dischargeable and refutable at deployed parameters — the two poles
immediately below. -/
def Coll4 {F : Type} (hash4 : F → F → F → F → F) (a b c d a' b' c' d' : F) : Prop :=
  ¬(a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧ hash4 a b c d = hash4 a' b' c' d'

/-- **THE RESIDUAL IS DISCHARGEABLE (positive pole).** At one quadruple against itself there is
nothing to collide, so `¬ Coll4` holds outright. A side condition that can never be discharged
is a broken keystone, not a repaired one. -/
theorem coll4_self_false {F : Type} (hash4 : F → F → F → F → F) (a b c d : F) :
    ¬ Coll4 hash4 a b c d a b c d :=
  fun h => h.1 ⟨rfl, rfl, rfl, rfl⟩

/-- **THE RESIDUAL IS REFUTABLE (negative pole).** At the constant compression any two distinct
quadruples DO collide, so `¬ Coll4` is not free — it is a real hypothesis about the deployed
hash at a named pair of preimages. -/
theorem coll4_of_constant {F : Type} (k : F) (a b c d a' b' c' d' : F)
    (hne : ¬(a = a' ∧ b = b' ∧ c = c' ∧ d = d')) :
    Coll4 (fun _ _ _ _ => k) a b c d a' b' c' d' :=
  ⟨hne, rfl⟩

/-- **THE PORT IS A WEAKENING, NOT A CHANGE OF SUBJECT.** A residual collision at any single
quadruple pair already REFUTES the global floor — so the deleted `Hash4Injective` implied every
`¬ Coll4` at once, and each consumer below is strictly stronger than its old form. Stated in
this direction (residual ⇒ `¬` floor) rather than as `floor ⇒ ¬ residual` deliberately: the
latter takes a refuted floor in HYPOTHESIS position and is a `#floor_ratchet` carrier, while
this one assumes no floor content and refutes some — the contrapositive is free either way. -/
theorem coll4_breaks_hash4Injective {F : Type} (hash4 : F → F → F → F → F)
    (a b c d a' b' c' d' : F) (hcoll : Coll4 hash4 a b c d a' b' c' d') :
    ¬ Hash4Injective hash4 :=
  fun hinj => hcoll.1 (hinj a b c d a' b' c' d' hcoll.2)

/-- **The binding lemma (soundness HEART).** If the attestation authenticates member `m`
(with any co-path) against a root that EQUALS the credential's committed facts root, then `m`
is the committed leftmost leaf `l0` AND the whole co-path equals the committed co-path.

This is what makes a TRUSTED `facts_root` (= `committedRoot`) sound: the attestation cannot
name a member unless it is genuinely one of the committed facts.

⚑ Stated on the PER-INSTANCE residual (was: the refuted `Hash4Injective`). The two-level peel
applies the compression exactly twice, so exactly two non-collision side conditions are owed —
`hTop` at the level-1 quadruple and `hBot` at the level-0 quadruple. Both are statements about
the preimages ACTUALLY PRESENTED, which is the shape an advantage bound discharges. -/
theorem attested_member_is_committed {F : Type} (hash4 : F → F → F → F → F)
    (m s0a s0b s0c s1a s1b s1c : F)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : F)
    (hTop : ¬ Coll4 hash4 (hash4 m s0a s0b s0c) s1a s1b s1c
        (hash4 l0 l1 l2 l3) (hash4 l4 l5 l6 l7) (hash4 l8 l9 l10 l11) (hash4 l12 l13 l14 l15))
    (hBot : ¬ Coll4 hash4 m s0a s0b s0c l0 l1 l2 l3)
    (hroot :
      attestedRoot hash4 m s0a s0b s0c s1a s1b s1c
        = committedRoot hash4 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) :
    m = l0 ∧ s0a = l1 ∧ s0b = l2 ∧ s0c = l3
      ∧ s1a = hash4 l4 l5 l6 l7
      ∧ s1b = hash4 l8 l9 l10 l11
      ∧ s1c = hash4 l12 l13 l14 l15 := by
  -- Peel the top-level hash: parent0 = P0, and the level-1 siblings equal the committed parents.
  -- `hroot` IS the image equality of the level-1 quadruples (both roots are that application by
  -- definition), so a difference at that quadruple would be exactly the excluded `Coll4`.
  have htop : (hash4 m s0a s0b s0c = hash4 l0 l1 l2 l3) ∧ s1a = hash4 l4 l5 l6 l7
      ∧ s1b = hash4 l8 l9 l10 l11 ∧ s1c = hash4 l12 l13 l14 l15 :=
    Classical.byContradiction fun hne => hTop ⟨hne, hroot⟩
  obtain ⟨hp0, hs1a, hs1b, hs1c⟩ := htop
  -- Peel the level-0 hash: m = l0 and the level-0 siblings equal the committed leaves.
  have hbot : m = l0 ∧ s0a = l1 ∧ s0b = l2 ∧ s0c = l3 :=
    Classical.byContradiction fun hne => hBot ⟨hne, hp0⟩
  obtain ⟨hm, h0a, h0b, h0c⟩ := hbot
  exact ⟨hm, h0a, h0b, h0c, hs1a, hs1b, hs1c⟩

/-- **No-fabrication corollary.** A member `m` that is NOT the committed leftmost leaf `l0`
authenticates to a root DIFFERENT from the committed facts root, for EVERY co-path. Hence,
once `facts_root` is the trusted committed root, a fabricated fact is REFUSED by the binding
(the attestation's root cannot equal the trusted `facts_root`) — not by fail-close.

This is exactly the forgery `cross_credential_predicate_forgery_rejected` must refuse
soundly, and the WEAKER forgery (fact fabricated under A's own `state_root`, invented
`facts_root`) the current fail-closed accept leaves open.

⚑ On the per-instance residual, like its parent. The forger who wants the root equality back
must now EXHIBIT a collision at one of the two named quadruples — which is the honest reading
of "the hash holds this up", and is what a `¬ Coll4` side condition prices. -/
theorem fabricated_member_refused {F : Type} (hash4 : F → F → F → F → F)
    (m s0a s0b s0c s1a s1b s1c : F)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : F)
    (hTop : ¬ Coll4 hash4 (hash4 m s0a s0b s0c) s1a s1b s1c
        (hash4 l0 l1 l2 l3) (hash4 l4 l5 l6 l7) (hash4 l8 l9 l10 l11) (hash4 l12 l13 l14 l15))
    (hBot : ¬ Coll4 hash4 m s0a s0b s0c l0 l1 l2 l3)
    (hfab : m ≠ l0) :
    attestedRoot hash4 m s0a s0b s0c s1a s1b s1c
      ≠ committedRoot hash4 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 := by
  intro hroot
  exact hfab (attested_member_is_committed hash4
    m s0a s0b s0c s1a s1b s1c
    l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 hTop hBot hroot).1

/-- **The binding, unconditionally: bind, or EXHIBIT a collision.** Floor-free and residual-free
— the root equality forces the committed opening UNLESS the deployed compression genuinely
collides at one of the two quadruples the peel compares. This is the honest form: it names the
exact price of the binding instead of assuming the price away. -/
theorem attested_member_is_committed_or_collides {F : Type} (hash4 : F → F → F → F → F)
    (m s0a s0b s0c s1a s1b s1c : F)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : F)
    (hroot :
      attestedRoot hash4 m s0a s0b s0c s1a s1b s1c
        = committedRoot hash4 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) :
    (m = l0 ∧ s0a = l1 ∧ s0b = l2 ∧ s0c = l3
      ∧ s1a = hash4 l4 l5 l6 l7
      ∧ s1b = hash4 l8 l9 l10 l11
      ∧ s1c = hash4 l12 l13 l14 l15)
    ∨ Coll4 hash4 (hash4 m s0a s0b s0c) s1a s1b s1c
        (hash4 l0 l1 l2 l3) (hash4 l4 l5 l6 l7) (hash4 l8 l9 l10 l11) (hash4 l12 l13 l14 l15)
    ∨ Coll4 hash4 m s0a s0b s0c l0 l1 l2 l3 := by
  by_cases hTop : Coll4 hash4 (hash4 m s0a s0b s0c) s1a s1b s1c
      (hash4 l0 l1 l2 l3) (hash4 l4 l5 l6 l7) (hash4 l8 l9 l10 l11) (hash4 l12 l13 l14 l15)
  · exact Or.inr (Or.inl hTop)
  · by_cases hBot : Coll4 hash4 m s0a s0b s0c l0 l1 l2 l3
    · exact Or.inr (Or.inr hBot)
    · exact Or.inl (attested_member_is_committed hash4
        m s0a s0b s0c s1a s1b s1c
        l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 hTop hBot hroot)

/-- A genuinely injective 4-ary compression: the free `node` constructor over `Nat` leaves.
Constructor injectivity is definitional, so this is a concrete model of a collision-free
`hash_4_to_1` — the assumption is CONSISTENT, so the theorems above are not vacuous. -/
inductive FTree where
  | leaf : Nat → FTree
  | node : FTree → FTree → FTree → FTree → FTree
  deriving DecidableEq

/-- **What made the floor look safe, said honestly.** `FTree.node` IS a genuinely injective
arity-4 compression — over an INFINITE carrier, where `F × F ↪ F` is unremarkable. That is the
whole reason global 4-ary injectivity reads as a plausible hash assumption, and it is exactly
what the tooth's finiteness hypothesis excludes: NO finite `F` with more than one element admits
one, the deployed field included.

⚑ This replaces `hash4Injective_is_satisfiable`, which asserted `∃ F hash4, Hash4Injective hash4`.
That statement was TRUE and read as reassurance for a floor that is false everywhere the system
actually runs — the object that made the wound survive. It also named a refuted floor in its
conclusion, which is a `#floor_ratchet` carrier for no benefit. Same content, no floor mention,
no false comfort. -/
theorem ftreeNode_injective (a b c d a' b' c' d' : FTree)
    (heq : FTree.node a b c d = FTree.node a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
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
