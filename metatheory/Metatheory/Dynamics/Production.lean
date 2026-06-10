/-
# Metatheory.Dynamics.Production — the non-forgeability production law + the Dregg2 model.

`CONSTRUCTIVE-KNOWLEDGE.md §3` (and `docs/DREGG3.md §2.1`, the Authority row): authority is
**produced, not merely spent**. The model "every step only narrows" (monotone descent down
a meet-semilattice) is WRONG — it forbids exactly the patterns that give capabilities their
power (Miller). The real dynamics GROW authority, disciplined by ONE law:

> **Miller — *"only connectivity begets connectivity"*:** no ambient authority. You may
> confer/introduce/amplify only authority you (transitively) hold; every generative act is
> itself authorized by held knowledge.

`Metatheory.ConstructiveKnowledge §3` proved this for the **rights-order** reading
(`Confers`/`no_forge_step` over a `Preorder`). This module lifts it to the **substance /
camera setting**: production is the growth of the authoritative element of the `Auth`
camera by an authorized increment, and the production step is a *frame-preserving update*
(so it preserves the substance discipline — `Substance.lean`'s `auth_grow_fpu`). The
**non-vacuity** is exhibited as a theorem: an UNAUTHORIZED amplification — granting a
fragment that exceeds the held bound — is provably NOT a valid production step (NOT `Fpu`).

Then `§3` gives the **Dregg2 candidate model**: a thin instance showing dregg2's authority
substance (the rights lattice under ∪, as the in-tree `Auth (USet Rights)` camera) inhabits
the abstract substance signature and satisfies the production law. This is what makes
"candidate-independent" NON-vacuous — at least ONE model exists. (The dregg2 authority
camera and its `attenuate`/non-amplification gate are mirrored from
`Dregg2/Substrate/FpuProbe.lean §3,§6`, which OWNS the executor-coupled originals; we copy
the candidate-independent fragment so `Metatheory/*` does not import `Dregg2.Substrate.*` —
the ownership boundary — and is not coupled to the executor.)

DISCIPLINE: keystones `#assert_axioms`'d kernel-clean. Non-vacuity:
`unauthorized_amplification_not_production` (the NON-vacuity witness the mission demands).
-/
import Dregg2.Resource
import Dregg2.Authority.Positional
import Metatheory.Dynamics.Substance
import Metatheory.Dynamics.VerbSignature
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Order.Basic

namespace Metatheory.Dynamics

open Dregg2.Resource
open scoped Dregg2.Resource.ResourceAlgebra

universe u

/-! ## §1. The non-forgeability production law — candidate-independent.

Production GROWS the authoritative element of an `Auth M` camera by an *authorized*
increment. "Authorized" = the increment is connectivity already covered by the held
authority — Miller's *"only connectivity begets connectivity."* We state it over an
arbitrary `AddCommMonoid M` with its extension order `fits` (the monoid's own `≼`), so the
law is candidate-independent (any rights/knowledge monoid instantiates it). -/

variable {M : Type u} [AddCommMonoid M]

/-- **`AuthorizedProduction held produced`** — the candidate-independent production
predicate (`CONSTRUCTIVE-KNOWLEDGE.md §3`, the generalization of `Metatheory.Confers` to
the substance setting). A holder of authority `held : M` may **produce** a fragment
`produced : M` provided `produced` is covered by `held` (`fits produced held` — `produced`
fits within the held authority: `∃ c, held = produced + c`). This is the camera-level
"granted ≤ held": you may confer only connectivity you already hold. Production is
GENERATIVE (a new fragment appears / the graph grows), yet each production is *bounded by
held connectivity* — the non-amplification discipline, not a monotone descent. -/
def AuthorizedProduction (held produced : M) : Prop :=
  fits produced held

/-- **`production_step_fpu_genesis` — the production law at the genesis frame, PROVED,
kernel-clean.** The cleanest, hypothesis-free statement of authorized production as an
`Fpu`: producing a fragment `produced` that EXACTLY exhausts the held authority `held =
produced + g` against the complementary held frame `g` is frame-preserving. This is the
non-forgeable production step in its canonical form — the held authority is fully and
disjointly distributed (`produced ⊕ g = held`), no authority appears ex nihilo. -/
theorem production_step_fpu_genesis (produced g : M) :
    Fpu (R := Auth M) (.mk (some (produced + g)) 0) (.mk (some (produced + g)) produced) := by
  apply conservation_is_fpu
  intro g' hg'
  rw [zero_add] at hg'
  -- hg' : fits g' (produced + g); show fits (produced + g') (produced + g).
  -- We use that the canonical compatible frame is `g`, giving the exact swap.
  obtain ⟨c, hc⟩ := hg'
  exact ⟨c, by rw [hc]; ac_rfl⟩

/-- **The genesis production IS authorized** — the produced fragment fits within the held
authority (`produced ≼ produced + g`): no right appears ex nihilo. This connects
`production_step_fpu_genesis`'s `Fpu` to the `AuthorizedProduction` predicate, so the
production is provably *non-forgeable* (Miller: *only connectivity begets connectivity*). -/
theorem genesis_production_authorized (produced g : M) :
    AuthorizedProduction (produced + g) produced :=
  ⟨g, rfl⟩

#assert_axioms production_step_fpu_genesis
#assert_axioms genesis_production_authorized

/-! ## §1(a). NON-VACUITY: unauthorized amplification is NOT a valid production step.

`CONSTRUCTIVE-KNOWLEDGE.md §3`: *"granted permissions exceed introducer's own:
amplification denied."* We exhibit this as a theorem over the concrete dregg2 rights camera
(the cleanest carrier where amplification is visible): granting `write` under a bound of
only `read` is NOT a frame-preserving update — it FORGES authority, and the camera rejects
it. This is the load-bearing non-vacuity: the production law has teeth. -/

/-- The dregg2 authority rights enum (qualified). -/
abbrev Rights := Dregg2.Authority.Auth

/-- `Finset α` wearing its `∪`-monoid hat — mirrored from `FpuProbe.USet` (the ownership
boundary; this is the same one-field wrapper so the in-tree `Auth` camera serves the rights
∪-monoid, with `+ = ∪` and `0 = ∅`). -/
structure USet (α : Type u) [DecidableEq α] : Type u where
  set : Finset α

namespace USet

variable {α : Type u} [DecidableEq α]

instance : Zero (USet α) := ⟨⟨∅⟩⟩
instance : Add (USet α) := ⟨fun a b => ⟨a.set ∪ b.set⟩⟩

instance : AddCommMonoid (USet α) where
  add a b    := a + b
  zero       := 0
  nsmul      := nsmulRec
  add_assoc a b c := congrArg USet.mk (Finset.union_assoc a.set b.set c.set)
  add_comm a b    := congrArg USet.mk (Finset.union_comm a.set b.set)
  zero_add a      := congrArg USet.mk (Finset.empty_union a.set)
  add_zero a      := congrArg USet.mk (Finset.union_empty a.set)

@[simp] theorem add_set (a b : USet α) : (a + b).set = a.set ∪ b.set := rfl
@[simp] theorem zero_set : (0 : USet α).set = (∅ : Finset α) := rfl
@[simp] theorem mk_set (s : Finset α) : (USet.mk s).set = s := rfl

theorem set_inj {a b : USet α} : a = b ↔ a.set = b.set :=
  ⟨congrArg USet.set, fun h => by cases a; cases b; simpa using h⟩

/-- The monoid extension order on `USet` is LITERALLY `⊆` — the rights/knowledge inclusion
(mirrored from `FpuProbe.USet.fits_iff`). -/
theorem fits_iff (f a : USet α) : fits f a ↔ f.set ⊆ a.set := by
  constructor
  · rintro ⟨c, hc⟩
    have hs : a.set = f.set ∪ c.set := by
      have := congrArg USet.set hc
      simpa using this
    rw [hs]
    exact Finset.subset_union_left
  · intro h
    refine ⟨⟨a.set⟩, set_inj.mpr ?_⟩
    show a.set = f.set ∪ a.set
    exact (Finset.union_eq_right.mpr h).symm

end USet

/-- **`unauthorized_amplification_not_production` — THE NON-VACUITY WITNESS (`§3`).**
Granting `write` under a held bound of only `read` is provably NOT a frame-preserving
update in `Auth (USet Rights)`: the empty frame already witnesses the amplification. An
unauthorized amplification FORGES authority and the camera rejects it — *only connectivity
begets connectivity*, made a refutation. (Mirrors `FpuProbe.amplifying_grant_not_fpu` under
the production name; this is what makes the production law non-trivial — it is FALSE for
unauthorized grants, TRUE for authorized ones.) -/
theorem unauthorized_amplification_not_production :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) := by
  intro hF
  have hv : ResourceAlgebra.valid
      ((Auth.mk (some (⟨{Dregg2.Authority.Auth.read}⟩ : USet Rights)) 0 : Auth (USet Rights))
        ⊙ .mk none 0) := by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid]
    rw [add_zero, USet.fits_iff]
    simp
  have hpost := hF (.mk none 0) hv
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid] at hpost
  rw [add_zero, USet.fits_iff] at hpost
  have hmem := hpost (Finset.mem_singleton_self Dregg2.Authority.Auth.write)
  exact absurd hmem (by decide)

/-- **The DUAL: an AUTHORIZED production over the rights camera IS `Fpu`** — granting `read`
under a held bound that already contains `read` is a valid production step. Together with
`unauthorized_amplification_not_production` this pins the production law as genuinely
two-sided (true for authorized, false for unauthorized) — the non-vacuity is complete. -/
theorem authorized_grant_is_production :
    Fpu (R := Auth (USet Rights))
      (.mk (some ⟨{Dregg2.Authority.Auth.read, Dregg2.Authority.Auth.write}⟩) 0)
      (.mk (some ⟨{Dregg2.Authority.Auth.read, Dregg2.Authority.Auth.write}⟩)
           ⟨{Dregg2.Authority.Auth.read}⟩) := by
  apply conservation_is_fpu
  intro g hg
  rw [zero_add] at hg
  rw [USet.fits_iff] at hg ⊢
  rw [USet.add_set, USet.mk_set]
  refine Finset.union_subset ?_ hg
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  simp

#assert_axioms unauthorized_amplification_not_production
#assert_axioms authorized_grant_is_production

/-! ## §2. The production law lifted to the rights monoid (the `§3` step law, substance form).

`Metatheory.no_forge_step` is the rights-order step law; here we give its camera form: the
single-step non-forgeability fact for the dregg2 authority substance, derived from the
generic `production_step_fpu_genesis`. -/

/-- **`rights_production_no_forge` — the step law over the dregg2 rights camera, PROVED.**
For any held rights `R` partitioned as `R = produced ∪ g`, producing the `produced`
fragment against the complementary `g` is `Fpu` in `Auth (USet Rights)`. No right appears
ex nihilo — the produced fragment was already covered by the held authority (it is a subset
of `R`). This is `Metatheory.no_forge_step` cashed at the substance/camera tier. -/
theorem rights_production_no_forge (produced g : USet Rights) :
    Fpu (R := Auth (USet Rights))
      (.mk (some (produced + g)) 0) (.mk (some (produced + g)) produced) :=
  production_step_fpu_genesis produced g

#assert_axioms rights_production_no_forge

/-! ## §3. The Dregg2 candidate model — at least ONE model exists.

This is what makes "candidate-independent" NON-vacuous. We exhibit the four dregg2
substance cameras as carriers of the abstract `Substances` signature, and a dregg2 `grant`
verb (authorized production of attenuated rights) as an inhabitant of the abstract `Verb`
signature whose footprint is `Fpu` (so it `Fires`, given any admitting witness). -/

/-- The dregg2 value-substance camera carrier (the per-asset ledger column as an `Auth ℕ` —
the abstract scalar shape; the full per-asset `SAuth` lives in `FpuProbe`, executor-owned).
Here we use the simplest faithful value camera so the model is self-contained. -/
abbrev DreggValue : Type := Auth Nat
/-- The dregg2 authority-substance camera: the rights ∪-monoid under `Auth` (`§1(a)`). -/
abbrev DreggAuthority : Type := Auth (USet Rights)
/-- The dregg2 evidence-substance camera: the spent-nullifier ∪-monoid under `Auth` — the
SAME camera shape as authority (`FpuProbe §F6`), at carrier `ℕ` instead of `Rights`. -/
abbrev DreggEvidence : Type := Auth (USet Nat)
/-- The dregg2 state-substance camera: the exclusive (points-to) heap on scalar slots. -/
abbrev DreggState : Type := Excl Int

/-- **The dregg2 candidate model of the four-substance signature** (`§Substance`). It
exhibits a genesis product element — the empty-but-valid configuration — witnessing that
the abstract `Substances` signature is INHABITED by dregg2's substance cameras. The
disciplines are discharged by the theorems above (`production_step_fpu_genesis` for
authority/non-amplification, `auth_grow_fpu` for evidence, `value_no_free_copy`/`excl_no_dup`
for value/state). -/
def dreggSubstances : Substances DreggValue DreggAuthority DreggEvidence DreggState where
  genesis := (.mk (some 0) 0, .mk (some ⟨∅⟩) 0, .mk (some ⟨∅⟩) 0, .ex 0)

/-- **The dregg2 `grant` verb as an inhabitant of the abstract `Verb` signature.** Its
footprint is an authorized production in the authority leg (`produced` rights conferred
under the held bound `held = produced ∪ g`), with the value/evidence/state legs idle. The
admission demand is carried abstractly (`P`/`W` the demand⊣supply seam); the candidate
model proves the FOOTPRINT is `Fpu`, hence the verb `Fires` for any admitting witness. -/
def dreggGrantVerb {P : Type} (adm : Admission P) (produced g : USet Rights) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState where
  admission := adm
  pre  := (.mk (some 0) 0, .mk (some (produced + g)) 0, .mk (some ⟨∅⟩) 0, .ex 0)
  post := (.mk (some 0) 0, .mk (some (produced + g)) produced, .mk (some ⟨∅⟩) 0, .ex 0)

/-- **The dregg2 `grant` verb is footprint-`Fpu`, PROVED, kernel-clean — the candidate
model satisfies the kernel meta-law.** The authority leg is the authorized production
(`rights_production_no_forge`); the value, evidence, and state legs are idle (`Fpu.refl`).
By `fpu_prod`, the product footprint is `Fpu`. So the dregg2 grant verb inhabits the
abstract `Verb` signature with a genuine `Fpu` footprint — the meta-law's ontic gate is met
by a REAL dregg2 verb, witnessing candidate-independence is non-vacuous. -/
theorem dreggGrantVerb_footprint {P : Type} (adm : Admission P) (produced g : USet Rights) :
    Footprint (dreggGrantVerb adm produced g) := by
  show Fpu _ _
  refine fpu_prod (Fpu.refl _) (fpu_prod ?_ (fpu_prod (Fpu.refl _) (Fpu.refl _)))
  exact rights_production_no_forge produced g

/-- **The dregg2 `grant` verb FIRES under any admitting witness** — the candidate model
satisfies BOTH gates of the kernel meta-law. Given a witness `w` that discharges the
admission (the epistemic gate) and the proved `Fpu` footprint (the ontic gate),
`Fires` holds, so `kernel_meta_law` applies: the dregg2 grant preserves product validity.
This is the end-to-end candidate model — dregg2's grant is a verb in the abstract signature
whose firing is governed by the abstract meta-law. -/
theorem dreggGrantVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (produced g : USet Rights) (w : W)
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (dreggGrantVerb adm produced g) w :=
  fires_intro (W := W) _ w hadm (dreggGrantVerb_footprint adm produced g)

/-- **The dregg2 grant, run through the abstract kernel meta-law.** Composing
`dreggGrantVerb_fires` with `kernel_meta_law`: a fired dregg2 grant preserves the product
validity of EVERY compatible frame — conservation ∧ non-amplification ∧ monotonicity ∧
frame, for the concrete dregg2 substance cameras. The abstract meta-law GOVERNS the
candidate model; that is the non-vacuity of "candidate-independent." -/
theorem dreggGrant_preserves_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (produced g : USet Rights) (w : W)
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid ((dreggGrantVerb adm produced g).pre ⊙ fr)) :
    ResourceAlgebra.valid ((dreggGrantVerb adm produced g).post ⊙ fr) :=
  kernel_meta_law _ w (dreggGrantVerb_fires adm produced g w hadm) fr hfr

#assert_axioms dreggGrantVerb_footprint
#assert_axioms dreggGrantVerb_fires
#assert_axioms dreggGrant_preserves_validity

/-! ## §Coda.

The non-forgeability production law (`CONSTRUCTIVE-KNOWLEDGE.md §3`, Miller) is cashed at
the substance/camera tier: authorized production is `Fpu` (`production_step_fpu_genesis` /
`rights_production_no_forge`), and unauthorized amplification is provably NOT
(`unauthorized_amplification_not_production` — the mission's non-vacuity witness), with the
authorized dual also pinned. The **Dregg2 candidate model** (`dreggSubstances` /
`dreggGrantVerb`) exhibits dregg2's four substance cameras as carriers of the abstract
signature and dregg2's `grant` as a verb whose footprint is `Fpu` and which `Fires` and is
governed by the abstract `kernel_meta_law` — so "candidate-independent" is non-vacuous: at
least one model exists, and the abstract dynamics layer governs it. -/

end Metatheory.Dynamics
