/-
# Dregg2.Laws — the `Predicate ⊣ Witness` adjunction and the verify/find seam.

The central seam of the whole system: a *predicate* and a *witness* form a Galois
connection (an adjunction between thin categories / a residuated pair on a Heyting
algebra). The **verify** side is decidable and verifier-local (`Verify P w : Bool`);
the **find/search** side is an opaque, possibly-undecidable plugin (the prover /
matcher / solver). The metatheory commits ONLY to the verify side; the search side
is contracted to be *sound by verification* and nothing more (no completeness, no
termination — see `Authority/Positional.lean` and the README §matcher).

"Spec-first": the adjunction laws are discharged against `Order.GaloisConnection` (the
fully-provable `polarity_galois` once the `Predicate`/`Witness` orders are fixed). The
find/verify soundness *contract* is not provable in-module — it is the external plugin's
obligation — so it is carried as the `SoundSearchable.find_sound` typeclass FIELD (the
`CryptoKernel` Prop-portal idiom), NOT a `sorry`; `search_sound` recovers it as a lemma.
-/
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Heyting.Basic

open OrderDual Set

namespace Dregg2.Laws

/- The lattice of predicates over a fixed witness space `W`.
In the real system this is the Heyting algebra of admissibility conditions;
here it is abstract, required only to be a `HeytingAlgebra`. -/
variable {P : Type*} {W : Type*}

/-- The decidable, verifier-local check: does witness `w` satisfy predicate `p`?

This is *simultaneously* the proof target and a runnable function — a Lean
`def … : Bool` is both the spec and the executable golden oracle (backend #8 of
the differential harness). -/
class Verifiable (P : Type*) (W : Type*) where
  Verify : P → W → Bool

/-- `Discharged P w` ≜ the verifier accepts: the proof-relevant statement that a
witness discharges a predicate. This is the cross-vat admissibility object — a
freely copyable, verifier-checkable certificate, no off-island mediator. -/
def Discharged [Verifiable P W] (p : P) (w : W) : Prop :=
  Verifiable.Verify p w = true

instance [Verifiable P W] (p : P) (w : W) : Decidable (Discharged p w) := by
  unfold Discharged; exact inferInstanceAs (Decidable (_ = true))

/-- **The opaque search side (the prover plugin).** Given a predicate, *try* to
produce a discharging witness. Modelled as a partial function (`Option`) because
the search may be undecidable / nonterminating; the metatheory makes NO promise
about when it returns `some`. This class is the UNTRUSTED plugin: a `Searchable`
instance may return garbage — an adversarial `find` that returns a non-discharging
witness is a *legal* instance (see `Authority.Intent.evilMatcher`). Soundness is NOT a
field here precisely because that would forbid such adversarial plugins; consumers
re-`Verify` whatever `find` returns and never trust it. -/
class Searchable (P : Type*) (W : Type*) where
  find : P → Option W

/-- **The soundness-by-verification CONTRACT, as a typeclass field (the `CryptoKernel`
Prop-portal idiom).** A `SoundSearchable` is a search plugin that COMES WITH a soundness
guarantee `find_sound`: whatever it returns must verify. This is an *assumption*
about the (external, untrusted-by-default) plugin — there is no in-module relation between
an arbitrary `find` and `Verify` from which to derive it (that is exactly why the untrusted
`Searchable` above does NOT carry it, and why `Authority.Intent` re-`Verify`s instead of
appealing to the contract). Carried as a Prop field, the assumption is explicit and
auto-resolved at call sites that demand a CONTRACTED plugin. -/
class SoundSearchable (P : Type*) (W : Type*) [Verifiable P W] extends Searchable P W where
  /-- **Soundness-by-verification.** The ONLY guarantee a contracted plugin owes: whatever
  it returns must verify. (No completeness; no termination — `find` may still return `none`
  for a satisfiable predicate.) -/
  find_sound : ∀ (p : P) (w : W), find p = some w → Discharged p w

/-- **Soundness-by-verification — the contract, recovered as a lemma.** For any plugin
carrying the contract (`[SoundSearchable P W]`), whatever it returns verifies. Discharged by
the `SoundSearchable.find_sound` field. (For a bare untrusted `Searchable`, no such guarantee
exists by design; consumers re-`Verify`.) -/
theorem search_sound
    [Verifiable P W] [SoundSearchable P W] (p : P) (w : W)
    (h : Searchable.find p = some w) :
    Discharged p w :=
  SoundSearchable.find_sound p w h

/-- **The polarity Galois connection induced by an arbitrary relation.**

Every binary relation `R : α → β → Prop` induces an antitone Galois connection
between the powerset lattices `Set α` and `Set β` (a "polarity", aka the Birkhoff
dual / formal-concept adjunction). We realise the antitone pair as a *monotone*
`GaloisConnection` into the order dual `(Set β)ᵒᵈ`:

* `l A = {b | ∀ a ∈ A, R a b}` — the upper polar (all `b` related to every `a ∈ A`);
* `u B = {a | ∀ b ∈ B, R a b}` — the lower polar (all `a` related to every `b ∈ B`).

The adjunction `l A ≤ B ↔ A ≤ u B` holds because both sides unfold to the single
symmetric condition `∀ a ∈ A, ∀ b ∈ B, R a b`. This is the standard, fully-provable
construction; no hypotheses beyond the relation are needed. -/
theorem polarity_galois {α β : Type*} (R : α → β → Prop) :
    GaloisConnection
      (fun A : Set α => toDual {b : β | ∀ a ∈ A, R a b})
      (fun B : (Set β)ᵒᵈ => {a : α | ∀ b ∈ ofDual B, R a b}) := by
  intro A B
  -- `l A ≤ B` in `(Set β)ᵒᵈ` is, by defeq, `ofDual B ⊆ {b | ∀ a ∈ A, R a b}`.
  show (ofDual B) ⊆ {b : β | ∀ a ∈ A, R a b} ↔ A ⊆ {a : α | ∀ b ∈ ofDual B, R a b}
  constructor
  · intro h a ha b hb; exact h hb a ha
  · intro h b hb a ha; exact h ha b hb

/-- **Law: `Predicate ⊣ Witness` is a Galois connection** (the verify/find seam). Obtained
by instantiating `polarity_galois` at the `Discharged` relation. Predicates are ordered as
`Set P` under entailment/⊆; witness-sets as `(Set W)ᵒᵈ` (specificity order). The left
adjoint is `l A = {w | every predicate in A is discharged by w}`; the right adjoint is
`u B = {p | every witness in B discharges p}`. -/
theorem predicate_witness_galois [Verifiable P W] :
    GaloisConnection
      (fun A : Set P => toDual {w : W | ∀ p ∈ A, Discharged p w})
      (fun B : (Set W)ᵒᵈ => {p : P | ∀ w ∈ ofDual B, Discharged p w}) :=
  polarity_galois (fun (p : P) (w : W) => Discharged p w)

/-- **Law: the predicate algebra is Heyting.** Conjunction/implication of
admissibility conditions behaves intuitionistically (the residual of `⊓` is `⇨`),
which is exactly what justifies *attenuation* (a stricter predicate entails a
laxer one) in the authority module. -/
theorem predicate_heyting
    [HeytingAlgebra P] (a b c : P) :
    (a ⊓ b ≤ c) ↔ (a ≤ b ⇨ c) :=
  le_himp_iff.symm

end Dregg2.Laws
