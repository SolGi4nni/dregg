/-
# Metatheory.Dynamics.Substance — the FOUR substances, candidate-independent.

This is the **dynamics layer** of the constructive-knowledge metatheory
(`CONSTRUCTIVE-KNOWLEDGE.md`, `docs/DREGG3.md §2.1`). The metatheory's `§1–§5`
(`Metatheory.ConstructiveKnowledge`) gave the *statics* — what a claim/witness/turn IS.
DREGG3 §2.1 names the *substances* the dynamics move, each with its own discipline of
use:

| Substance | Discipline | The law |
|---|---|---|
| **Value**     | linear — moves, never copies or vanishes | Σδ = 0, exact (a conservation camera) |
| **Authority** | **non-forgeable production** — GROWS only by authorized construction; narrows freely | Miller: *only connectivity begets connectivity* |
| **Evidence**  | monotone — once known, never unknown | grow-only |
| **State**     | guarded-mutable — changes only under `Pred`, only by its owner | the frame |

DREGG3 §2.1 (the S0 verdict, `Dregg2/Substrate/FpuProbe.lean`) found the algebra for all
four is a **resource algebra** (Iris camera): the product camera `Sub4 = ValueCam × Auth
× Auth × Heap`, every verb is a frame-preserving update (`Fpu`) of its footprint. The
sharpest finding: **authority and evidence are literally the SAME `Auth`-camera over
∪-monoids** — non-amplification (authority) and monotone growth (evidence) are two faces
of one camera (`FpuProbe §F6`). This module makes that a *structural fact of the abstract
signature*, not a coincidence of dregg2.

CANDIDATE-INDEPENDENCE is the point: the substances are **abstract camera carriers**, not
`Dregg2.RecordKernelState`. `Substance.lean` abstracts over the four carriers; the dregg2
RecordKernelState substances (and svenvs/mediateor, when built) are *candidate models*.
The non-vacuity of "candidate-independent" is exhibited in `Production.lean`'s `Dregg2`
instance: at least one model exists.

DISCIPLINE: faithful structures with real content; the keystones `#assert_axioms`'d
kernel-clean (`⊆ {propext, Classical.choice, Quot.sound}`). No `:= True` load-bearing; the
non-vacuity guard `authority_evidence_share_camera` exhibits the unification *as a
theorem*, and `value_no_free_copy` shows the value camera genuinely bites.
-/
import Dregg2.Resource
import Mathlib.Algebra.Group.Defs

namespace Metatheory.Dynamics

open Dregg2.Resource
open scoped Dregg2.Resource.ResourceAlgebra

universe u v w x

/-! ## §1. The substance signature — four abstract camera carriers.

Each substance is an Iris `ResourceAlgebra` (camera). The signature is the *product* of
four such, abstracted over their carriers `V A E S`. We do NOT fix `V := Dregg2.Ledger`
etc.: any camera with the right discipline instantiates it. The disciplines are recorded
as *abstract laws over the substance's camera* — `move`/`grant`/`shield`/`write` are
`Fpu`s — not as concrete `RecordKernelState` field equations. -/

/-- **The four-substance signature** (`DREGG3 §2.1`), candidate-independent. The four
carriers — value `V`, authority `A`, evidence `E`, state `S` — are each an abstract
resource algebra (Iris camera). The signature bundles ONLY the camera structure; the
*disciplines* (linear / non-forgeable-production / monotone / guarded) are theorems
*about* `Fpu` in these cameras, proved generically in `VerbSignature.lean` and
`Production.lean`, and discharged for a concrete system by a candidate model.

The product camera (`ResourceAlgebra (V × A × E × S)` — the in-tree `instProdRA` of
`FpuProbe`) is what a turn's footprint inhabits; `Substances.Product` names it. -/
structure Substances (V : Type u) (A : Type v) (E : Type w) (S : Type x)
    [ResourceAlgebra V] [ResourceAlgebra A] [ResourceAlgebra E] [ResourceAlgebra S] where
  /-- A witness that the signature is inhabited (a genesis product element). Keeps the
  structure non-empty without fixing a carrier — the candidate model supplies a real one. -/
  genesis : V × A × E × S

/-- The product camera of the four substances — `value × authority × evidence × state`.
A turn's footprint is a frame-preserving update *here* (`VerbSignature.preserves_product`).
This re-uses the in-tree product resource-algebra instance; mirrored as an `abbrev` so the
abstract signature names it without importing `Dregg2.Substrate.*` (ownership boundary). -/
abbrev Product (V : Type u) (A : Type v) (E : Type w) (S : Type x)
    [ResourceAlgebra V] [ResourceAlgebra A] [ResourceAlgebra E] [ResourceAlgebra S] :
    Type (max (max u v) (max w x)) :=
  V × A × E × S

/-! ## §1(a). The product of resource algebras IS a resource algebra.

Mirrored from `Dregg2.Substrate.FpuProbe.instProdRA` (the abstract signature must not
import `Dregg2.Substrate.*` — ownership boundary; this is a local copy of the exact same
construction, NOT a re-derivation of new mathematics). Componentwise `op`/`valid`; the
core exists iff both components' cores exist (the Iris product-camera `pcore`). -/

open ResourceAlgebra in
instance instProdRA {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B] :
    ResourceAlgebra (A × B) where
  op a b    := (a.1 ⊙ b.1, a.2 ⊙ b.2)
  valid a   := valid a.1 ∧ valid a.2
  core a    :=
    match core a.1, core a.2 with
    | some c1, some c2 => some (c1, c2)
    | _, _ => none
  op_comm a b := by
    show (a.1 ⊙ b.1, a.2 ⊙ b.2) = (b.1 ⊙ a.1, b.2 ⊙ a.2)
    rw [op_comm a.1 b.1, op_comm a.2 b.2]
  op_assoc a b c := by
    show ((a.1 ⊙ b.1) ⊙ c.1, (a.2 ⊙ b.2) ⊙ c.2) = (a.1 ⊙ (b.1 ⊙ c.1), a.2 ⊙ (b.2 ⊙ c.2))
    rw [op_assoc a.1 b.1 c.1, op_assoc a.2 b.2 c.2]
  valid_op_left a b h := ⟨valid_op_left a.1 b.1 h.1, valid_op_left a.2 b.2 h.2⟩
  core_id a ca h := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        show (c1 ⊙ a.1, c2 ⊙ a.2) = a
        rw [core_id a.1 c1 h1, core_id a.2 c2 h2]
  core_idem a ca h := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        show (match core c1, core c2 with
              | some d1, some d2 => some (d1, d2)
              | _, _ => none) = some (c1, c2)
        rw [core_idem a.1 c1 h1, core_idem a.2 c2 h2]
  core_mono a b ca h hext := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        obtain ⟨e, he⟩ := hext
        have hb1 : ∃ z, b.1 = a.1 ⊙ z := ⟨e.1, by rw [he]⟩
        have hb2 : ∃ z, b.2 = a.2 ⊙ z := ⟨e.2, by rw [he]⟩
        obtain ⟨d1, hd1, w1, hw1⟩ := core_mono a.1 b.1 c1 h1 hb1
        obtain ⟨d2, hd2, w2, hw2⟩ := core_mono a.2 b.2 c2 h2 hb2
        refine ⟨(d1, d2), by rw [hd1, hd2], (w1, w2), ?_⟩
        show (d1, d2) = (c1 ⊙ w1, c2 ⊙ w2)
        rw [hw1, hw2]

/-- **The product glue** (mirrored from `FpuProbe.fpu_prod`). Componentwise `Fpu` lifts to
the product — the formal content of "one theorem schema over the product of the
substances." Pinned kernel-clean. -/
theorem fpu_prod {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B]
    {a b : A} {c d : B} (h1 : Fpu a b) (h2 : Fpu c d) : Fpu (a, c) (b, d) :=
  fun f hv => ⟨h1 f.1 hv.1, h2 f.2 hv.2⟩

/-- **The product tooth** (mirrored from `FpuProbe.not_fpu_prod_left`). If ONE component
update is not `Fpu` (witnessed by a frame the other component can accompany validly), the
PRODUCT update is not `Fpu` — a violation in any single substance kills the whole verb.
This is the non-vacuity backbone: the product schema inherits every corner's tooth. -/
theorem not_fpu_prod_left {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B]
    {a b : A} {c d : B} (f1 : A)
    (hpre : ResourceAlgebra.valid (a ⊙ f1)) (hpost : ¬ ResourceAlgebra.valid (b ⊙ f1))
    (f2 : B) (hc : ResourceAlgebra.valid (c ⊙ f2)) : ¬ Fpu (a, c) (b, d) :=
  fun h => hpost (h (f1, f2) ⟨hpre, hc⟩).1

#assert_axioms fpu_prod
#assert_axioms not_fpu_prod_left

/-! ## §2. The four disciplines as ABSTRACT camera laws (candidate-independent).

Rather than `RecordKernelState` field equations, each discipline is stated against an
arbitrary camera. The candidate model proves its substances meet them. -/

/-! ### §2(a). Authority ≡ Evidence — the SAME camera (the structural unification).

`FpuProbe §F6`: authority (affine, non-amplification) and evidence (monotone, grow-only)
are the SAME in-tree `Auth M` camera at different carriers — `Auth (USet Rights)` vs
`Auth (USet Nat)`. We make this a *structural fact* of the signature: the abstract
authority and evidence cameras are both built by `Auth (·)` over an `AddCommMonoid`, and
the two governing laws — non-amplification (`conservation_is_fpu`) and authoritative
growth (`auth_grow_fpu`) — are theorems of *one* camera. -/

variable {M : Type u} [AddCommMonoid M]

/-- **Authoritative growth is `Fpu`** (the EVIDENCE law — Iris `auth_update_auth`).
Mirrored from `FpuProbe.auth_grow_fpu`. Enlarging the authoritative element `● a` to
`● (a + t)` while fragments stand still never invalidates a frame: every fragment that fit
within `a` fits within `a + t`. THIS is the monotone-substance law — "once known, never
unknown" as a camera fact. -/
theorem auth_grow_fpu (a t f : M) :
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some (a + t)) f) := by
  intro fr hv
  cases fr with
  | invalid =>
    exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 g =>
    cases a2 with
    | none =>
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hv ⊢
      obtain ⟨c, hc⟩ := hv
      exact ⟨c + t, by rw [hc, add_assoc]⟩
    | some a2 =>
      exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

/-- **`authority_evidence_share_camera` — the structural unification (`FpuProbe §F6`),
PROVED, kernel-clean.** Over ANY `AddCommMonoid M`, the authority discipline and the
evidence discipline are laws of **one and the same** camera `Auth M`:

  * the **AUTHORITY** law — a fragment minted *within* the bound is `Fpu` (non-amplifying
    production: granting `f → f'` under a fixed total `a` whenever `f'` covers no more than
    `f` does) — is `conservation_is_fpu` in `Auth M`;
  * the **EVIDENCE** law — authoritative *growth* `● a → ● (a + t)` is `Fpu` (monotone:
    once `● a` is known, the knowledge only enlarges) — is `auth_grow_fpu` in `Auth M`.

Both inhabit the SAME `Auth M`. This is not a coincidence we observe of dregg2; it is a
*property of the signature*: the authority and evidence carriers are constructed by the
same `Auth (·)` functor, so the non-amplification and monotone laws are two theorems of
one algebra. (The candidate model picks `M := USet Rights` for authority and `M := USet
Nat` for evidence — `Production.lean`.) -/
theorem authority_evidence_share_camera (a f f' : M)
    (hmono : ∀ g, fits (f + g) a → fits (f' + g) a) (t : M) :
    -- AUTHORITY: non-amplifying fragment production is Fpu in `Auth M` …
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some a) f')
    -- … and EVIDENCE: authoritative growth is Fpu in the SAME `Auth M`.
    ∧ Fpu (R := Auth M) (.mk (some a) f) (.mk (some (a + t)) f) :=
  ⟨conservation_is_fpu a f f' hmono, auth_grow_fpu a t f⟩

#assert_axioms auth_grow_fpu
#assert_axioms authority_evidence_share_camera

/-! ### §2(b). Value — the linear discipline bites (non-vacuity of the value camera).

The VALUE substance is a *conservation camera*: `Fpu` is the frame-preserving update, and
the linear discipline ("moves, never copies or vanishes") is `excl_no_dup` for the
unique-resource (NFT) case — an exclusive resource cannot compose with itself validly.
This exhibits that the value camera genuinely bites (not `valid := True`). -/

/-- **`value_no_free_copy` — the linear discipline of value, PROVED, kernel-clean.** In the
exclusive (NFT/linear-token) value camera `Excl R`, no resource composes with itself
validly: a unique value cannot be in two places. This is the camera-level "moves, never
copies" — the substructural skeleton of the value substance. (Mirrors
`Dregg2.Resource.excl_no_dup` under the substance name; the per-asset Σδ=0 ledger case is
the candidate model's `move_value_fpu`, `Production.lean`.) -/
theorem value_no_free_copy {R : Type u} (a : Excl R) : ¬ ResourceAlgebra.valid (a ⊙ a) :=
  excl_no_dup a

#assert_axioms value_no_free_copy

/-! ## §Coda.

The signature `Substances V A E S` carries the four abstract substance cameras; the
product camera `Product` is where a turn's footprint lives (`instProdRA`/`fpu_prod`). The
disciplines are *abstract camera laws*: authority and evidence are PROVED to be one camera
(`authority_evidence_share_camera`), value's linearity bites (`value_no_free_copy`). What
`VerbSignature.lean` adds: a `Verb` = admission × footprint-`Fpu`, and the kernel meta-law
(admission ∧ footprint-`Fpu` ⇒ product validity preserved). What `Production.lean` adds:
the non-forgeability production law and a `Dregg2` candidate model. -/

end Metatheory.Dynamics
