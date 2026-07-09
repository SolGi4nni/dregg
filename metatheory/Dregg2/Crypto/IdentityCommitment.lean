/-
# `Dregg2.Crypto.IdentityCommitment` — the HYBRID IDENTITY-COMMITMENT BINDING.

This is the soundness floor under the identity re-basing (`dregg-types` `7e3ea27ec`; the
`cell-crypto` / `captp` / `wire` id-commitment). The canonical hybrid identity is

  `Id = H("dregg-hybrid-id-v1", ed25519_pk ‖ len(ml_dsa_pk) ‖ ml_dsa_pk)`

(`types/src/lib.rs::hybrid_id_commitment`), and the enroll+pin gate is

  `verify_committed_ml_dsa(id, ed, ml) := hybrid_id_commitment(ed, ml) == id`.

A surface can therefore REPLACE out-of-band roster enrollment with the id itself: the id IS the
enrollment, because it cryptographically BINDS both keys. This file proves that binding reduces to
standard HASH COLLISION-RESISTANCE — the SAME named carrier (`HashCR`) the concurrent-signature
argument and the randomness beacon already ride (`Dregg2.Crypto.HermineHintMLWE`,
`Dregg2.Crypto.RandomnessBeacon`). No fresh `…Hard` carrier: the whole re-basing bottoms out at
hash collision-resistance, nothing more.

## The model
* `commit cr frame ed ml := cr.H () (frame ed ml)` — the domain-separated hash `H` (the imported
  `CommitReveal` carrier at index `Unit`) applied to the length-framed preimage `frame ed ml`
  (`= ed ‖ len(ml) ‖ ml`). `frame` is an INJECTIVE encoding: the fixed-width `ed` prefix plus the
  length-prefixed `ml` make distinct `(ed, ml)` pairs distinct pre-images (`Function.Injective2`).
* `verify_committed cr frame id ed ml := commit cr frame ed ml = id` — mirrors the Rust `==` gate.

## The floor (the two theorems the re-basing rests on)
* `id_commitment_binds` — under `HashCR`, an id determines its `(ed25519, ml_dsa)` pair UNIQUELY:
  two verifying pairs give `commit = id = commit`, hence (by `HashCR` + injective framing) the same
  pair. So a self-supplied pair that does not match the enrolled one cannot pass the gate.
* `attacker_key_not_committed` (THE TEETH) — an attacker who keeps the honest `ed25519` but swaps in
  their OWN `ml_dsa` is REJECTED (`¬ verify_committed`), unless they find a hash collision. This is
  exactly the guarantee `cell-crypto` / `captp` / `wire` rely on.

## The reduction
`distinct_verifying_pairs_break_hashcr` / `commit_collision_is_hash_collision`: two DISTINCT
key-pairs hashing to the SAME id is precisely a collision on `H` (the injective framing turns a
`commit`-collision into an `H`-collision), so it BREAKS `HashCR`. No named-carrier laundering: the
only irreducible object is `HashCR` (hash collision-resistance), reused verbatim from the tree.
-/
import Dregg2.Crypto.HermineHintMLWE

namespace Dregg2.Crypto.IdentityCommitment

open Dregg2.Crypto.HermineHintMLWE

/-! ## The commit model — a domain-separated hash over the length-framed key concatenation. -/

section Model

variable {Ed MlDsa Pre Id : Type*}

/-- **The hybrid-identity commitment.** The imported collision-resistant hash `H` (the `CommitReveal`
carrier at index `Unit`, the SAME carrier `HermineHintMLWE`/`RandomnessBeacon` use) applied to the
length-framed preimage `frame ed ml = ed ‖ len(ml) ‖ ml`. Models
`hybrid_id_commitment(ed, ml) = BLAKE3_derive_key("dregg-hybrid-id-v1", ed ‖ len(ml) ‖ ml)`. -/
def commit (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre) (ed : Ed) (ml : MlDsa) : Id :=
  cr.H () (frame ed ml)

/-- **The enroll+pin gate** `verify_committed_ml_dsa(id, ed, ml) := hybrid_id_commitment(ed, ml) == id`.
Recomputes the commitment from the two PRESENTED keys and accepts iff it equals the claimed id. -/
def verify_committed (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (id : Id) (ed : Ed) (ml : MlDsa) : Prop :=
  commit cr frame ed ml = id

/-- **BINDING — the id determines its key pair UNIQUELY (the floor).** Under `HashCR` (hash
collision-resistance) and an injective framing, if two key pairs `(ed, ml)` and `(ed', ml')` BOTH
verify against the same id, they are equal. Both verify ⇒ `commit(ed,ml) = id = commit(ed',ml')` ⇒ (by
`HashCR` on the combine, then injectivity of the length-framed encoding) `(ed, ml) = (ed', ml')`. So a
self-supplied pair that differs from the enrolled one CANNOT pass the gate without a hash collision. -/
theorem id_commitment_binds (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame) (hcr : HashCR cr)
    (id : Id) (ed ed' : Ed) (ml ml' : MlDsa)
    (h : verify_committed cr frame id ed ml) (h' : verify_committed cr frame id ed' ml') :
    (ed, ml) = (ed', ml') := by
  unfold verify_committed commit at h h'
  have hcol : cr.H () (frame ed ml) = cr.H () (frame ed' ml') := h.trans h'.symm
  obtain ⟨he, hm⟩ := hframe (hcr () (frame ed ml) (frame ed' ml') hcol)
  subst he; subst hm; rfl

/-- **THE TEETH — an attacker's own ML-DSA key is REJECTED.** Keeping the honest `ed25519` key but
swapping in a DIFFERENT ml_dsa key `(ed, ml) ≠ (ed, ml_attacker)` fails the gate: the attacker key is
NOT committed. Under `HashCR`, passing the gate with a non-enrolled pair would (by `id_commitment_binds`)
force it EQUAL to the enrolled pair — contradiction. This is the exact `cell-crypto`/`captp`/`wire`
guarantee: a self-carried PQ key cannot impersonate the enrolled one without a hash collision. -/
theorem attacker_key_not_committed (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame) (hcr : HashCR cr)
    (id : Id) (ed : Ed) (ml ml_attacker : MlDsa)
    (hne : (ed, ml) ≠ (ed, ml_attacker))
    (h : verify_committed cr frame id ed ml) :
    ¬ verify_committed cr frame id ed ml_attacker :=
  fun hatt => hne (id_commitment_binds cr frame hframe hcr id ed ed ml ml_attacker h hatt)

/-- **The reduction — distinct verifying pairs BREAK `HashCR`.** If two DISTINCT key pairs both verify
against one id, `HashCR` cannot hold: it is exactly a hash collision. The contrapositive of
`id_commitment_binds` — an attacker who forges a colliding enrollment has, definitionally, broken hash
collision-resistance. This is what grounds the whole id re-basing in the ONE standard carrier `HashCR`. -/
theorem distinct_verifying_pairs_break_hashcr (cr : CommitReveal Unit Pre Id)
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame)
    (id : Id) (ed ed' : Ed) (ml ml' : MlDsa) (hne : (ed, ml) ≠ (ed', ml'))
    (h : verify_committed cr frame id ed ml) (h' : verify_committed cr frame id ed' ml') :
    ¬ HashCR cr :=
  fun hcr => hne (id_commitment_binds cr frame hframe hcr id ed ed' ml ml' h h')

/-- **A `commit`-collision IS an `H`-collision (the length-framing is faithful).** Distinct key pairs
that hash to the SAME id yield two DISTINCT pre-images (`frame ed ml ≠ frame ed' ml'`, by injectivity of
the length-framed encoding) mapping to one hash output — a genuine collision on the underlying hash `H`.
So the domain-separation/length-framing reduces a commitment collision to a raw hash collision, exactly
as claimed: nothing beyond `HashCR` is at stake. -/
theorem commit_collision_is_hash_collision (cr : CommitReveal Unit Pre Id)
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame)
    (ed ed' : Ed) (ml ml' : MlDsa) (hne : (ed, ml) ≠ (ed', ml'))
    (h : commit cr frame ed ml = commit cr frame ed' ml') :
    ∃ p p' : Pre, p ≠ p' ∧ cr.H () p = cr.H () p' :=
  ⟨frame ed ml, frame ed' ml', fun hp => hne (by obtain ⟨he, hm⟩ := hframe hp; subst he; subst hm; rfl), h⟩

end Model

#assert_axioms id_commitment_binds
#assert_axioms attacker_key_not_committed
#assert_axioms distinct_verifying_pairs_break_hashcr
#assert_axioms commit_collision_is_hash_collision

/-! ## Teeth — the binding FIRES on concrete data, and its `HashCR` hypothesis is LOAD-BEARING.

(a) A HashCR-respecting instance: the honest pair verifies, and the attacker (honest ed, own ml_dsa,
    and also the ed-swap) is REJECTED — `attacker_key_not_committed` fires.
(b) A HashCR-VIOLATING toy instance: a constant hash makes TWO distinct pairs share one id, so binding
    FAILS — the `HashCR` hypothesis of `id_commitment_binds` is genuinely load-bearing (non-vacuous).
(c) The length-framing is faithful: naive concatenation `ed ++ ml` COLLIDES (ambiguous field
    boundary), whereas the length-prefixed framing is injective — so a `commit`-collision is a real
    `H`-collision. -/

section Teeth

/-! ### (a) HashCR-respecting instance — the honest pair passes, the attacker is rejected. -/

/-- The commitment hash `H((), p) = p`, injective on the committed domain (`HashCR`). Stands in for the
collision-resistant `BLAKE3_derive_key` over the length-framed preimage. -/
def exCR : CommitReveal Unit (List ℕ) (List ℕ) := ⟨fun _ p => p⟩

theorem exCR_hashcr : HashCR exCR := fun _ _ _ h => h

/-- The length-framed preimage `frame ed ml = ed ‖ len(ml) ‖ ml`: a fixed-width `ed` word, the length
of `ml`, then `ml`. Modeled over `ℕ × List ℕ` — the head is the fixed-width `ed`, `ml.length` is the
`len(ml)` prefix. -/
def exFrame : ℕ → List ℕ → List ℕ := fun ed ml => ed :: ml.length :: ml

/-- The framing is genuinely injective in BOTH keys: distinct `(ed, ml)` give distinct pre-images. -/
theorem exFrame_inj : Function.Injective2 exFrame := by
  intro ed ml ed' ml' h
  simp only [exFrame, List.cons.injEq] at h
  exact ⟨h.1, h.2.2⟩

/-- The honest enrolled id: `H("…", P_ed ‖ len(P_ml) ‖ P_ml)` for `P_ed = 1`, `P_ml = [2,3]`. -/
def exId : List ℕ := commit exCR exFrame 1 [2, 3]

/-- The honest `(P_ed, P_ml)` passes the enroll+pin gate. -/
theorem honest_verifies : verify_committed exCR exFrame exId 1 [2, 3] := rfl

/-- **THE TEETH FIRE.** The attacker keeps the honest `ed = 1` but swaps in their OWN ml_dsa `[9]`:
`attacker_key_not_committed` REJECTS it — `¬ verify_committed`. The self-carried PQ key cannot pass. -/
theorem attacker_ml_rejected : ¬ verify_committed exCR exFrame exId 1 [9] :=
  attacker_key_not_committed exCR exFrame exFrame_inj exCR_hashcr exId 1 [2, 3] [9]
    (by decide) honest_verifies

-- The honest commitment is the length-framed hash of both keys.
#guard exFrame 1 [2, 3] = [1, 2, 2, 3]
-- The attacker's own ml_dsa hashes to a DIFFERENT id — the gate rejects it.
#guard exFrame 1 [9] ≠ [1, 2, 2, 3]
-- An attacker who also swaps the ed25519 key is likewise rejected.
#guard exFrame 9 [2, 3] ≠ [1, 2, 2, 3]

/-! ### (b) HashCR-VIOLATING instance — binding's hypothesis is load-bearing (non-vacuous). -/

/-- A COLLIDING hash `H((), p) = []` for every preimage — every key pair hashes to the SAME id. This
VIOLATES `HashCR`. -/
def badCR : CommitReveal Unit (List ℕ) (List ℕ) := ⟨fun _ _ => []⟩

/-- `badCR` genuinely fails `HashCR`: the distinct preimages `[1] ≠ [2]` collide to `[]`. -/
theorem badCR_not_hashcr : ¬ HashCR badCR :=
  fun hcr => absurd (hcr () [1] [2] rfl) (by decide)

/-- **BINDING FAILS WITHOUT `HashCR` (load-bearing).** Under the colliding `badCR`, TWO distinct key
pairs `(1, [2,3]) ≠ (1, [9])` BOTH verify against the empty id `[]` — so the conclusion of
`id_commitment_binds` (uniqueness) is FALSE here. Its `HashCR` hypothesis is therefore genuinely
load-bearing: without collision-resistance the id no longer binds the key pair. -/
theorem binding_needs_hashcr :
    verify_committed badCR exFrame [] 1 [2, 3] ∧ verify_committed badCR exFrame [] 1 [9]
      ∧ ((1, [2, 3]) ≠ ((1, [9]) : ℕ × List ℕ)) :=
  ⟨rfl, rfl, by decide⟩

-- The collision is real: distinct key pairs, distinct FRAMED pre-images, ONE id — the hash collided,
-- not the framing. So it is exactly a hash collision (`commit_collision_is_hash_collision`).
#guard badCR.H () (exFrame 1 [2, 3]) = badCR.H () (exFrame 1 [9])
#guard exFrame 1 [2, 3] ≠ exFrame 1 [9]

/-! ### (c) The length-framing is faithful — naive concatenation collides; length-prefixing is injective. -/

/-- Naive `ed ++ ml`: no length prefix, so the field boundary is AMBIGUOUS. -/
def naiveFrame : List ℕ → List ℕ → List ℕ := fun ed ml => ed ++ ml

/-- Length-prefixed framing `len(ed) ‖ ed ‖ len(ml) ‖ ml`: self-describing, hence injective. -/
def lenFrame : List ℕ → List ℕ → List ℕ := fun ed ml => ed.length :: (ed ++ (ml.length :: ml))

-- WITHOUT length-framing the encoding COLLIDES: `([1], [2,3])` and `([1,2], [3])` both give `[1,2,3]`.
-- This is why the real `hybrid_id_commitment` prepends `len(ml)` (and `ed` is fixed-width).
#guard naiveFrame [1] [2, 3] = naiveFrame [1, 2] [3]
-- WITH length-framing the SAME distinct inputs give DISTINCT pre-images — injectivity restored.
#guard lenFrame [1] [2, 3] ≠ lenFrame [1, 2] [3]

/-- Length-prefixing both fields yields a genuinely injective encoding: distinct `(ed, ml)` (variable
width) map to distinct pre-images. This is the faithful reason `commit`-collisions reduce to
`H`-collisions — the framing never collides, only the hash can. -/
theorem lenFrame_inj : Function.Injective2 lenFrame := by
  intro ed ml ed' ml' h
  simp only [lenFrame, List.cons.injEq] at h
  obtain ⟨hlen, hcat⟩ := h
  obtain ⟨hed, hrest⟩ := List.append_inj hcat hlen
  simp only [List.cons.injEq] at hrest
  exact ⟨hed, hrest.2⟩

end Teeth

#assert_axioms exCR_hashcr
#assert_axioms exFrame_inj
#assert_axioms honest_verifies
#assert_axioms attacker_ml_rejected
#assert_axioms badCR_not_hashcr
#assert_axioms binding_needs_hashcr
#assert_axioms lenFrame_inj

end Dregg2.Crypto.IdentityCommitment
