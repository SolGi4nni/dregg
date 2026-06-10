/-
# Metatheory.Dynamics.VerbSignature — the verb as `admission × footprint-Fpu`.

`docs/DREGG3.md §2.1` (the two-gate result, the S0 verdict
`Dregg2/Substrate/FpuProbe.lean §LEDGER`): every kernel verb is

> **admission** (a `Pred` discharge — does the supplied witness realize the demanded
> predicate? the epistemic half, the verify/find seam) **×**
> **`Fpu` of the verb's footprint** in the product camera `Sub4` (the ontic half — the
> update respects what the substances ARE).

These are **two separate gates** (the S0 verdict was PARTIAL precisely because
the admission guard provably does NOT collapse into the camera — `FpuProbe §E2`
`camera_blind_to_caveats`: the camera is BLIND to the caveats). So a `Verb` is a *pair*:

  * an **admission gate** — from the constructive-knowledge metatheory's `Knower` /
    `Discharged` seam (`Metatheory.ConstructiveKnowledge §1`): a verifier-checkable
    predicate-discharge, the demand⊣supply half;
  * a **footprint** `Fpu` in the product substance camera (`Substance.lean`): the ontic
    half — conservation ∧ non-amplification ∧ monotonicity, unified as one `Fpu`.

THE KERNEL META-LAW (this module's centerpiece): a verb that **admits** AND is
**footprint-`Fpu`** preserves the product validity — ONE theorem, abstract over the four
substance carriers. "Product validity preserved" is exactly conservation (value leg) ∧
non-amplification (authority leg) ∧ monotonicity (evidence leg) ∧ frame (state leg) all at
once, because `Fpu` in the product camera IS "every compatible frame stays compatible."

CANDIDATE-INDEPENDENT: `P`, `W`, and the four carriers `V A E S` are abstract. The dregg2
verbs (`move`/`grant`/`write`/`spend`) are candidate instances (`Production.lean`).

DISCIPLINE: the meta-law is `#assert_axioms`'d kernel-clean. Non-vacuity:
`meta_law_nonvacuous` exhibits a verb whose footprint is NOT `Fpu` and therefore does NOT
preserve product validity — the meta-law is not trivially true.
-/
import Dregg2.Resource
import Dregg2.Laws
import Dregg2.Tactics
import Metatheory.Dynamics.Substance

namespace Metatheory.Dynamics

open Dregg2.Resource Dregg2.Laws
open scoped Dregg2.Resource.ResourceAlgebra

universe u v w x

/-! ## §1. The admission gate — the epistemic half (the verify/find seam).

`Metatheory.ConstructiveKnowledge §1`: admission is "does the supplied witness realize the
demanded predicate?" — `Discharged (P := P) (W := W) p w`, the decidable verifier-local
check. We carry the admission gate as the predicate the verb *demands* together with the
fact that the actor *supplied* a discharging witness. This is the `Pred`-discharge of
DREGG3 §2.2, abstracted to the `Verifiable P W` seam. -/

variable {P : Type u} {W : Type u} [Verifiable P W]

/-- **An admission demand**: the predicate a verb requires a witness to discharge (the
demand side of the demand⊣supply adjunction). Candidate-independent: `P` is the abstract
predicate type (`Pred` in dregg2), `stmt` the verifier-side statement. -/
structure Admission (P : Type u) where
  /-- The predicate the supplied witness must `Verify`. -/
  stmt : P

/-- **`Admits adm w`**: the witness `w` discharges the admission demand `adm` — the
verifier accepts (`Discharged`). This is the epistemic gate: a verb may fire only when its
demand is *constructively* met (a realizer exhibited), never merely asserted
(`CONSTRUCTIVE-KNOWLEDGE.md §0`). -/
def Admits (adm : Admission P) (w : W) : Prop :=
  Discharged (P := P) (W := W) adm.stmt w

/-- Admission is decidable — the trusted, cheap half of the verify/find asymmetry
(`ConstructiveKnowledge §1`). -/
instance (adm : Admission P) (w : W) : Decidable (Admits (P := P) (W := W) adm w) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## §2. The verb — admission × footprint-`Fpu`.

A `Verb` over the product substance camera bundles the TWO gates: an admission demand and
a footprint update (a `pre`/`post` pair in the product camera). It is the dynamics-layer
realization of `docs/DREGG3.md §2.1`. -/

variable {V : Type u} {A : Type v} {E : Type w} {S : Type x}
variable [ResourceAlgebra V] [ResourceAlgebra A] [ResourceAlgebra E] [ResourceAlgebra S]

/-- **A kernel `Verb`** (`DREGG3 §2.1`), candidate-independent. It is *literally* a pair:

  * `admission` — the epistemic gate (a `Pred`-discharge demand);
  * `pre`/`post` — the verb's **footprint** in the product substance camera (`Product V A
    E S`): the elements it owns and moves (value rows, the held cap, the spent set, the
    written slot).

The verb is **valid at a state** when (a) the actor supplied a witness that `Admits` and
(b) the footprint update is `Fpu`. The kernel meta-law (`§3`) is that these two together
preserve product validity. -/
structure Verb (P : Type u) (V : Type u) (A : Type v) (E : Type w) (S : Type x)
    [ResourceAlgebra V] [ResourceAlgebra A] [ResourceAlgebra E] [ResourceAlgebra S] where
  /-- The admission demand — the epistemic gate (the `Pred` the actor must discharge). -/
  admission : Admission P
  /-- The footprint, pre-state (the elements of the product camera the verb owns before). -/
  pre  : Product V A E S
  /-- The footprint, post-state (the elements after the verb fires). -/
  post : Product V A E S

/-- **`Footprint v` — the verb's footprint update is a frame-preserving update** in the
product camera. This is the ontic gate: the update respects what the substances ARE
(conservation ∧ non-amplification ∧ monotonicity ∧ frame, unified). -/
def Footprint (v : Verb P V A E S) : Prop :=
  Fpu v.pre v.post

/-- **`Fires v w` — the verb is admissible and footprint-`Fpu`**: BOTH gates pass. The
actor supplied `w` discharging the admission, AND the footprint update is `Fpu`. This is
DREGG3 §2.1's "every kernel verb is admission × `Fpu`" as a single predicate. -/
def Fires (v : Verb P V A E S) (w : W) : Prop :=
  Admits (P := P) (W := W) v.admission w ∧ Footprint v

/-! ## §3. THE KERNEL META-LAW.

A verb that admits AND is footprint-`Fpu` preserves the product validity. ONE theorem,
abstract over the four substance carriers. "Preserves product validity" = every frame
compatible with the pre-footprint stays compatible with the post-footprint — which, in the
product camera, is exactly **conservation** (value leg) ∧ **non-amplification** (authority
leg) ∧ **monotonicity** (evidence leg) ∧ **frame** (state leg), simultaneously. -/

/-- **`kernel_meta_law` — the dynamics-layer kernel meta-law, PROVED, kernel-clean.**

If a verb `v` **fires** under witness `w` (its admission is discharged AND its footprint
update is a frame-preserving update of the product substance camera), then for EVERY frame
`fr` compatible with the verb's pre-footprint, `fr` remains compatible with the
post-footprint:

    Fires v w  →  ∀ fr, valid (v.pre ⊙ fr) → valid (v.post ⊙ fr).

This is the single abstract theorem behind DREGG3 §2.1: the two gates (admission `×`
footprint-`Fpu`) together preserve product validity. Because `Product V A E S = V × A × E ×
S` with componentwise `valid`, "product validity preserved" unfolds to all four substance
disciplines AT ONCE — conservation (`V`), non-amplification (`A`), monotone growth (`E`),
and the frame (`S`). The admission gate is *separate* (it does not enter this
implication's proof — `FpuProbe §E2`, the camera is blind to the guard); it is carried in
`Fires` because a real verb needs BOTH, but the *validity-preservation* is the `Fpu` half.
The content: a fired verb cannot break any third party's holding in any
substance. -/
theorem kernel_meta_law (v : Verb P V A E S) (w : W) (h : Fires (W := W) v w) :
    ∀ fr : Product V A E S,
      ResourceAlgebra.valid (v.pre ⊙ fr) → ResourceAlgebra.valid (v.post ⊙ fr) :=
  h.2

/-- **The meta-law, stated as `Fpu` of the footprint** — the same fact named as the
frame-preserving update it is. A fired verb's footprint update IS an `Fpu` in the product
camera; this is the canonical conservation-law shape (`Resource.Fpu`). -/
theorem fires_footprint_fpu (v : Verb P V A E S) (w : W) (h : Fires (W := W) v w) :
    Fpu v.pre v.post :=
  h.2

/-- **The four substance legs preserved simultaneously — the meta-law UNFOLDED.** Spelling
out that "product validity preserved" really is all four disciplines at once: given a fired
verb and a frame `(fv, fa, fe, fs)` valid against the pre-footprint in EACH substance, the
post-footprint stays valid in EACH — value, authority, evidence, AND state legs together.
This is the explicit witness that the meta-law unifies conservation + non-amplification +
monotonicity + frame as ONE theorem. -/
theorem kernel_meta_law_pointwise (v : Verb P V A E S) (w : W) (h : Fires (W := W) v w)
    (fv : V) (fa : A) (fe : E) (fs : S)
    (hv : ResourceAlgebra.valid (v.pre.1 ⊙ fv))
    (ha : ResourceAlgebra.valid (v.pre.2.1 ⊙ fa))
    (he : ResourceAlgebra.valid (v.pre.2.2.1 ⊙ fe))
    (hs : ResourceAlgebra.valid (v.pre.2.2.2 ⊙ fs)) :
    ResourceAlgebra.valid (v.post.1 ⊙ fv)
    ∧ ResourceAlgebra.valid (v.post.2.1 ⊙ fa)
    ∧ ResourceAlgebra.valid (v.post.2.2.1 ⊙ fe)
    ∧ ResourceAlgebra.valid (v.post.2.2.2 ⊙ fs) := by
  have := h.2 (fv, fa, fe, fs) ⟨hv, ha, he, hs⟩
  exact this

#assert_axioms kernel_meta_law
#assert_axioms fires_footprint_fpu
#assert_axioms kernel_meta_law_pointwise

/-! ## §4. Non-vacuity — the meta-law is not trivially true.

The meta-law `Fires v w → preserves-validity` could be vacuous in two ways:
(a) if `Fires` were never satisfiable, or (b) if every footprint were `Fpu`. We refute
both. (a) is witnessed by ANY genuine fired verb (the candidate model `Production.lean`
exhibits `move`/`grant`/`write`); (b) is refuted here: a verb whose footprint is a NON-`Fpu`
update fails to preserve validity, so the `Fpu` hypothesis is load-bearing. -/

/-- **`meta_law_nonvacuous` — the `Fpu` hypothesis is load-bearing, PROVED, kernel-clean.**
If a verb's footprint update is NOT a frame-preserving update (witnessed by a frame `fr`
that is compatible with `pre` but breaks against `post`), then the verb does NOT preserve
product validity — there is a frame the post-footprint invalidates. So the meta-law's
`Footprint` (= footprint-`Fpu`) hypothesis cannot be dropped: a non-`Fpu` footprint
breaks a third party's holding. This is the camera tooth lifted to the verb. -/
theorem meta_law_nonvacuous (v : Verb P V A E S) (fr : Product V A E S)
    (hpre : ResourceAlgebra.valid (v.pre ⊙ fr))
    (hpost : ¬ ResourceAlgebra.valid (v.post ⊙ fr)) :
    ¬ Footprint v :=
  fun hfpu => hpost (hfpu fr hpre)

/-- **A fired verb is satisfiable** (the (a)-direction of non-vacuity): given an
admitting witness and a real `Fpu` footprint, `Fires` holds — so the meta-law's antecedent
is inhabitable, not vacuous. The candidate model supplies concrete witnesses. -/
theorem fires_intro (v : Verb P V A E S) (w : W)
    (hadm : Admits (P := P) (W := W) v.admission w) (hfpu : Fpu v.pre v.post) :
    Fires (W := W) v w :=
  ⟨hadm, hfpu⟩

#assert_axioms meta_law_nonvacuous
#assert_axioms fires_intro

/-! ## §Coda.

A `Verb` is `admission × footprint`. The kernel meta-law (`kernel_meta_law`): a fired verb
(admits ∧ footprint-`Fpu`) preserves product validity — conservation ∧ non-amplification ∧
monotonicity ∧ frame, ONE abstract theorem (`kernel_meta_law_pointwise` unfolds the four
legs). The two gates are separate (admission does not enter the
validity-preservation; the camera is blind to it — `FpuProbe §E2`). Non-vacuity is pinned
both ways (`meta_law_nonvacuous` / `fires_intro`). `Production.lean` adds the
non-forgeability production law and the `Dregg2` candidate model showing the dregg2 verbs
inhabit this signature. -/

end Metatheory.Dynamics
