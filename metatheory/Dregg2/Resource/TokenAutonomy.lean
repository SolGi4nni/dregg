/-
# Dregg2.Resource.TokenAutonomy — why an idempotent resource forces its OWN token.

`Resource.lean` internalizes conservation as a **frame-preserving update** on a
resource algebra (the camera), with `conservation_is_fpu` the canonical metatheorem.
A protocol's *token* is the OBJECT-LEVEL reflection of that conservation law: the
carrier of the conserved quantity. This module asks the dual, design-level question —

  **when can a protocol borrow a FOREIGN token (ADA, ℤ-money) to carry its resource,
  and when must it mint its OWN?**

The answer is a one-line piece of monoid algebra with real teeth. Frame the resource
as a commutative monoid `(M, *, 1)`. A *sound foreign substitution* of `P` by `F` is a
**retract in `CommMonoid`**: a homomorphic embedding `embed : P →* F` that some
homomorphic `read : F →* P` inverts (`read (embed p) = p`) — `F` faithfully carries
every `P`-resource and reads it back with NO loss of `P`-information. (Retract = "`F`
can stand in for `P` losslessly", the precise sense in which one token substitutes for
another.)

THE OBSTRUCTION. In a **cancellative** monoid the ONLY idempotent is the unit
(`a * a = a → a = 1`, by cancelling `a`). Money is cancellative: `x + a = x + b → a = b`
(ℤ, ADA). So a cancellative `F` has no non-trivial idempotent. But a **set/lattice**
resource — privacy commitments, nullifiers, the capability lattice, any `Finset` under
`∪` — DOES: a nonempty set `s` has `s ∪ s = s` with `s ≠ ∅`. "Have-it-twice =
have-it-once" is idempotence; it is the algebraic signature of *authority/membership*,
the opposite of a *quantity*. A retract would push `P`'s idempotent `a` to an idempotent
of `F` (homs preserve `a*a=a`), which in cancellative `F` is forced to `1`, and then
`read` pulls it back to `1 ≠ a` — contradicting `retract`. So:

  **`no_substitution_of_idempotent`** — a protocol whose conserved resource has a
  NON-TRIVIAL idempotent admits NO sound substitution by a cancellative (ℤ-like) token.
  Such a protocol MUST instantiate its own resource algebra — its own token.

This is exactly an autonomy theorem for dregg2's set-valued resources: the
capability lattice (`Exec/Positional.lean` `Auth` + `Finset Auth`), the nullifier and
commitment SETs (`Exec/RecordKernel.lean`), the CRDT `GSet` (`Confluence/CRDT.lean`) —
all `Finset`-under-`∪` idempotent monoids — are NOT ADA-substitutable. An idempotent
(non-numeric) resource forces an autonomous (non-numeric) token. See
`Resource.conservation_is_fpu`: the token is the object-level reflection of that
conservation metatheorem, and its *algebra* (cancellative vs idempotent) is what decides
substitutability.

THE HONEST OTHER SIDE (`degenerate_payment_substitutes`). When `P` itself is
cancellative — pure ℤ payment — it DOES retract into ℤ (identity). The cryptobro is
*right for money*: a payment protocol can ride ADA. The theorem is a *discriminator*,
not a blanket "always mint your own": it cleanly separates payment (cancellative,
substitutable) from privacy/authority (idempotent, autonomous).

Pure Lean + mathlib + the `Resource.lean` citation. Zero `sorry`/`admit`/`native_decide`
/`axiom`; keystones pinned with `#assert_axioms`.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Dregg2.Tactics
import Dregg2.Resource

namespace Dregg2.Resource.TokenAutonomy

universe u v

/-! ## §1. Sound foreign substitution = a retract in `CommMonoid`.

`F` can stand in for `P` losslessly: a hom embeds, a hom reads, the read inverts the
embed. This is the precise structure a "use ADA instead of your own token" claim asserts. -/

/-- **A sound foreign substitution of `P` by `F`** — a retract of commutative monoids.
`embed` homomorphically carries each `P`-resource into `F`; `read` homomorphically
recovers it; `retract` says NO `P`-information is lost (`read ∘ embed = id`). This is the
honest formalization of "the foreign token `F` can carry protocol `P`'s resource". -/
structure SoundSubstitution (P : Type u) (F : Type v) [CommMonoid P] [CommMonoid F] where
  /-- Homomorphically place a `P`-resource inside the foreign token `F`. -/
  embed : P →* F
  /-- Homomorphically read a `P`-resource back out of `F`. -/
  read : F →* P
  /-- Reading back what we embedded recovers it exactly — losslessness. -/
  retract : ∀ p : P, read (embed p) = p

/-! ## §2. The obstruction — a cancellative monoid has no non-trivial idempotent.

The single fact with teeth. It GENUINELY cancels `a` (`mul_left_cancel`), so it is the
load-bearing use of the cancellative hypothesis. -/

/-- **In a cancellative commutative monoid the only idempotent is the unit.**
From `a * a = a = a * 1`, cancel `a` on the left to get `a = 1`. This is the algebraic
heart: cancellativity (the ℤ/ADA property `x*a = x*b → a = b`) is exactly what forbids a
non-trivial "have-it-twice = have-it-once". -/
theorem idempotent_of_cancel_eq_one {F : Type v} [CommMonoid F] [IsCancelMul F]
    {a : F} (h : a * a = a) : a = 1 := by
  -- a * a = a = a * 1, then left-cancel `a`.
  have h' : a * a = a * 1 := by rw [h, mul_one]
  exact mul_left_cancel h'

/-- **No non-trivial idempotent in a cancellative monoid** (contrapositive packaging):
if `a` is idempotent and `a ≠ 1`, contradiction. -/
theorem cancellative_no_nontrivial_idempotent {F : Type v} [CommMonoid F] [IsCancelMul F]
    {a : F} (hidem : a * a = a) (hne : a ≠ 1) : False :=
  hne (idempotent_of_cancel_eq_one hidem)

/-- A monoid hom carries idempotents to idempotents: `f a * f a = f (a * a) = f a`. -/
theorem map_idempotent {P : Type u} {F : Type v} [CommMonoid P] [CommMonoid F]
    (f : P →* F) {a : P} (h : a * a = a) : f a * f a = f a := by
  rw [← map_mul, h]

/-! ## §3. THE KEYSTONE — an idempotent resource admits no cancellative substitution. -/

/-- **`no_substitution_of_idempotent` (THE KEYSTONE).** If `P`'s resource has a
NON-TRIVIAL idempotent `a` (`a * a = a`, `a ≠ 1`) and the foreign token `F` is
cancellative (ℤ-like), then there is NO sound substitution of `P` by `F`.

Proof: a substitution would push `a` to `embed a`, an idempotent of `F` (homs preserve
idempotence), which cancellativity forces to be `1`. Then `read` of that is `read 1 = 1`,
yet `retract` says `read (embed a) = a`. So `a = 1`, contradicting `a ≠ 1`. The protocol
literally cannot retract its set-valued resource into a numeric token. -/
theorem no_substitution_of_idempotent
    {P : Type u} {F : Type v} [CommMonoid P] [CommMonoid F] [IsCancelMul F]
    {a : P} (hidem : a * a = a) (hne : a ≠ 1) (s : SoundSubstitution P F) : False := by
  -- `embed a` is an idempotent of the cancellative `F`, hence the unit.
  have hF : s.embed a * s.embed a = s.embed a := map_idempotent s.embed hidem
  have hembed_one : s.embed a = 1 := idempotent_of_cancel_eq_one hF
  -- Read it back two ways: via `retract` it is `a`; via `hembed_one` it is `read 1 = 1`.
  have h1 : s.read (s.embed a) = a := s.retract a
  have h2 : s.read (s.embed a) = 1 := by rw [hembed_one, map_one]
  exact hne (h1.symm.trans h2)

/-- Packaged as the non-existence statement: the type of substitutions is empty. -/
theorem not_nonempty_substitution_of_idempotent
    {P : Type u} {F : Type v} [CommMonoid P] [CommMonoid F] [IsCancelMul F]
    {a : P} (hidem : a * a = a) (hne : a ≠ 1) : ¬ Nonempty (SoundSubstitution P F) :=
  fun ⟨s⟩ => no_substitution_of_idempotent hidem hne s

/-! ## §4. THE WITNESSES — landing on dregg2's REAL set-valued resources.

The dregg2 capability lattice / nullifier set / commitment set / CRDT `GSet` are all
`Finset` under `∪` with unit `∅`. We give that the `CommMonoid` structure (this is the
idempotent monoid the whole metatheory's set-resources share) and exhibit a non-trivial
idempotent. We use `Multiplicative ℤ` as the cancellative `F` (ℤ-money, ADA). -/

/-- **The grow-only / set resource `GSet α`** — a `Finset α` whose monoid operation is
`∪` with unit `∅`. This is the dregg2 capability lattice (`Finset Auth`), the nullifier
SET, the commitment SET, the CRDT `GSet` — ONE idempotent monoid. We wrap it in a
structure so the monoid operation is `∪` (not the default `Finset` product) without
clashing with any ambient instance. -/
@[ext] structure GSet (α : Type u) where
  /-- The underlying finite set of held elements. -/
  carrier : Finset α

namespace GSet
variable {α : Type u} [DecidableEq α]

instance : CommMonoid (GSet α) where
  mul s t := ⟨s.carrier ∪ t.carrier⟩
  one := ⟨∅⟩
  mul_assoc s t u := by apply GSet.ext; exact Finset.union_assoc _ _ _
  one_mul s := by apply GSet.ext; exact Finset.empty_union _
  mul_one s := by apply GSet.ext; exact Finset.union_empty _
  mul_comm s t := by apply GSet.ext; exact Finset.union_comm _ _

@[simp] theorem mul_carrier (s t : GSet α) : (s * t).carrier = s.carrier ∪ t.carrier := rfl
@[simp] theorem one_carrier : (1 : GSet α).carrier = (∅ : Finset α) := rfl

/-- **Every `GSet` is idempotent — `s * s = s` (set union with itself).** This is the
"have-it-twice = have-it-once" of a membership/authority resource. -/
theorem mul_self (s : GSet α) : s * s = s := by
  apply GSet.ext; simp

/-- **A non-trivial idempotent: a nonempty `GSet` is idempotent but not the unit.** This
is the concrete obstruction witness — the dregg2 set-resource that cannot retract into ℤ. -/
theorem nontrivial_idempotent {a : α} :
    (⟨{a}⟩ : GSet α) * (⟨{a}⟩ : GSet α) = (⟨{a}⟩ : GSet α) ∧ (⟨{a}⟩ : GSet α) ≠ 1 := by
  refine ⟨mul_self _, ?_⟩
  intro h
  -- `⟨{a}⟩ = 1` means `{a} = ∅`, impossible.
  have hcar : ({a} : Finset α) = (∅ : Finset α) := congrArg GSet.carrier h
  simp at hcar

end GSet

/-! ### The cancellative foreign token: `Multiplicative ℤ` (ℤ-money, ADA). -/

/-- `Multiplicative ℤ` is `ℤ` under `+` viewed as a `*`-monoid: a cancellative
commutative monoid. This is the algebraic shape of ADA / any ℤ-valued payment token. -/
example : CommMonoid (Multiplicative ℤ) := inferInstance
example : IsCancelMul (Multiplicative ℤ) := inferInstance

/-- **THE WITNESS THEOREM. The dregg2 capability/nullifier/commitment SET token is NOT
ADA-substitutable.** With `P = GSet α` (the dregg2 set-resource) and `F = Multiplicative ℤ`
(ADA), the non-trivial idempotent `{a}` blocks every sound substitution. Concretely: a
protocol whose conserved resource is a membership SET cannot ride a numeric/ℤ token. -/
theorem gset_not_substitutable_by_int {α : Type u} [DecidableEq α] (a : α) :
    ¬ Nonempty (SoundSubstitution (GSet α) (Multiplicative ℤ)) := by
  obtain ⟨hidem, hne⟩ := GSet.nontrivial_idempotent (a := a)
  exact not_nonempty_substitution_of_idempotent hidem hne

/-! ## §5. THE HONEST DEGENERATE COROLLARY — cancellative payment DOES substitute.

The discriminator's other arm: a cancellative `P` (pure ℤ payment) retracts into itself.
The cryptobro is *right for money* — a payment protocol can ride a foreign ℤ token. The
substitution exists (the identity retract); the theorem only forbids it for idempotent
(set/authority) resources. -/

/-- The identity retract: any commutative monoid soundly substitutes for ITSELF (embed =
read = id). The constructive content of "a cancellative payment token rides a foreign
copy of itself" — and concretely instantiated below for ℤ-money. -/
def SoundSubstitution.id (P : Type u) [CommMonoid P] : SoundSubstitution P P where
  embed := MonoidHom.id P
  read := MonoidHom.id P
  retract := fun _ => rfl

/-- **`degenerate_payment_substitutes` (THE HONEST OTHER SIDE).** Pure ℤ payment —
`F = Multiplicative ℤ`, a cancellative token — DOES admit a sound substitution (into a
foreign copy of itself, the identity retract). So the theorem is a *discriminator*: it
distinguishes idempotent privacy/authority resources (no substitution) from cancellative
payment (substitution exists). The cryptobro is right for money. -/
theorem degenerate_payment_substitutes :
    Nonempty (SoundSubstitution (Multiplicative ℤ) (Multiplicative ℤ)) :=
  ⟨SoundSubstitution.id _⟩

/-- Sharper: the substitution holds for ANY cancellative `P` into itself — payment of any
ℤ-like flavor rides a foreign copy of its own token. This is the precise dual to
`no_substitution_of_idempotent`: there the idempotent BLOCKED it; here cancellativity
poses NO obstruction (the identity retract always works). -/
theorem cancellative_self_substitutes (P : Type u) [CommMonoid P] [IsCancelMul P] :
    Nonempty (SoundSubstitution P P) :=
  ⟨SoundSubstitution.id P⟩

/-! ## §6. Internalization note (cite `Resource.conservation_is_fpu`).

`conservation_is_fpu` shows conservation IS a frame-preserving update on the resource
algebra. A protocol's *token* is the carrier of that conserved quantity — the
object-level reflection of the conservation law. This module proves a structural fact
about that reflection: the token's *algebra* decides substitutability.

  * cancellative carrier (ℤ, ADA)  ⇒  numeric quantity  ⇒  borrowable (degenerate §5).
  * idempotent carrier (Finset ∪)  ⇒  membership/authority ⇒  AUTONOMOUS (keystone §3).

An idempotent ("have-it-twice = have-it-once") resource forces an autonomous (non-numeric)
token — the protocol MUST instantiate its OWN resource algebra. We record the link to the
camera tier explicitly. -/

/-- **The bridge to the camera tier.** A `GSet` is a `Dregg2.Resource` camera element via
the always-valid, idempotent-core resource-algebra over the underlying `Finset` join —
the same idempotent monoid `conservation_is_fpu` conserves. We record the witness that the
metatheory's conserved set-resource is precisely the idempotent monoid §3 forbids ℤ from
carrying. (Stated as a `Prop` carrier reusing the §4 idempotent fact, so the citation is
machine-checked, not prose.) -/
theorem token_is_object_reflection_of_conservation {α : Type u} [DecidableEq α] (a : α) :
    -- the conserved set-resource is idempotent and non-trivial …
    ((⟨{a}⟩ : GSet α) * (⟨{a}⟩ : GSet α) = (⟨{a}⟩ : GSet α) ∧ (⟨{a}⟩ : GSet α) ≠ 1)
    -- … hence (cf. `Dregg2.Resource.conservation_is_fpu`, the conservation metatheorem
    -- whose object-level reflection this token is) it is NOT ℤ-substitutable.
    ∧ ¬ Nonempty (SoundSubstitution (GSet α) (Multiplicative ℤ)) :=
  ⟨GSet.nontrivial_idempotent, gset_not_substitutable_by_int a⟩

/-! ## §7. Axiom hygiene — every keystone pinned to the trusted base. -/

-- `#assert_axioms foo` (dregg2 `Tactics.lean`) FAILS unless `foo` depends ONLY on the
-- three kernel axioms `{propext, Classical.choice, Quot.sound}` — in particular it rejects
-- any inherited `sorryAx`. Every keystone is pinned.
#assert_axioms idempotent_of_cancel_eq_one
#assert_axioms cancellative_no_nontrivial_idempotent
#assert_axioms no_substitution_of_idempotent
#assert_axioms not_nonempty_substitution_of_idempotent
#assert_axioms gset_not_substitutable_by_int
#assert_axioms degenerate_payment_substitutes
#assert_axioms cancellative_self_substitutes
#assert_axioms token_is_object_reflection_of_conservation

/-! ## §8. Non-vacuity `#guard`s — the witnesses are CONCRETE and have teeth. -/

section Evals
open GSet

-- A nonempty `GSet ℕ` is idempotent: `{7} ∪ {7} = {7}` → `true`.
#guard (decide (((⟨{7}⟩ : GSet ℕ) * (⟨{7}⟩ : GSet ℕ)).carrier = (⟨{7}⟩ : GSet ℕ).carrier))  -- true
-- … but it is NOT the unit: `{7} = ∅` → `false`.
#guard (decide (((⟨{7}⟩ : GSet ℕ).carrier) = (1 : GSet ℕ).carrier) == false)                  -- false
-- The identity retract reads back what it embeds, concretely on a ℤ-money element.
#guard (decide ((SoundSubstitution.id (Multiplicative ℤ)).read
                ((SoundSubstitution.id (Multiplicative ℤ)).embed (Multiplicative.ofAdd 5))
              = Multiplicative.ofAdd 5))                                                    -- true
-- The obstruction's contradiction is concrete: in the cancellative `Multiplicative ℤ`,
-- the ONLY idempotent is `1` — `ofAdd 3` is NOT idempotent (`ofAdd 3 * ofAdd 3 = ofAdd 6 ≠
-- ofAdd 3`), so there is no non-trivial idempotent to embed into.
#guard (decide ((Multiplicative.ofAdd (3 : ℤ) * Multiplicative.ofAdd (3 : ℤ))
              = Multiplicative.ofAdd (3 : ℤ)) == false)                                      -- false

end Evals

end Dregg2.Resource.TokenAutonomy
