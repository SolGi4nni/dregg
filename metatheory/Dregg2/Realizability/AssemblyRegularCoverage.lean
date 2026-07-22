/-
# Dregg2.Realizability.AssemblyRegularCoverage — the regular-coverage frontier.

`Assemblies.lean` constructs the assembly category, its finite products and equalizers, and the
PER carried by a modest assembly.  This file advances the categorical construction one genuine
step toward the realizability topos: it constructs explicit pullbacks, a computationally
meaningful class of covers stable under pullback, and the kernel-pair coequalizer/image
factorization of every assembly morphism.

The cover notion is deliberately evidence-relevant.  `EffectiveCover q` supplies one PCA program
which, from any realizer of a target point, computes a realizer of a source point above it.  This
is stronger than mere surjectivity and is exactly what makes the pullback-stability theorem
constructive: the pullback realizer is produced by a chosen PCA fork.  The quotient map onto the
image of any assembly morphism is such a cover and is the coequalizer of its kernel pair.  Its
inclusion is monic.  These are the regular-image ingredients used by an exact completion; this
module does not claim that all internal equivalence relations are effective, construct the exact
completion, or prove the elementary-topos axioms.

The last section pins the proof-compilation boundary.  A `ProgramCertificate` gives an executable
PCA code, hence a morphism and the regular-image factorization proved here.  A concrete
always-accept attestation is nevertheless complete and range-unsound for a certified constant
program.  Thus transcript commitment binding and sampled-query soundness remain external
proof-system obligations: neither follows from the categorical cover/descent construction.
-/
import Dregg2.Realizability.Assemblies

namespace Dregg2.Realizability

open CategoryTheory

universe u v w

namespace Assembly

variable {P : PCA.{u}}

/-! ## Explicit pullbacks -/

/-- The assembly pullback of two tracked maps.  A point is a semantic pullback pair and a realizer
is the chosen PCA pair of realizers of its two components. -/
def pullback (C : ChosenPairing P) {X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) : Assembly.{u, v} P where
  Carrier := {xy : X.Carrier × Y.Carrier // f.toFun xy.1 = g.toFun xy.2}
  Realizes := fun r xy =>
    ∃ a, X.Realizes a xy.1.1 ∧
      ∃ b, Y.Realizes b xy.1.2 ∧ r = C.pairVal a b
  realized := by
    intro xy
    rcases X.realized xy.1.1 with ⟨a, ha⟩
    rcases Y.realized xy.1.2 with ⟨b, hb⟩
    exact ⟨C.pairVal a b, a, ha, b, hb, rfl⟩

/-- First pullback projection. -/
def pullbackFst (C : ChosenPairing P) {X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) : pullback C f g ⟶ X where
  toFun := fun xy => xy.1.1
  tracked := by
    refine ⟨C.fst, ?_⟩
    rintro xy r ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, C.app_fst a b, ha⟩

/-- Second pullback projection. -/
def pullbackSnd (C : ChosenPairing P) {X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) : pullback C f g ⟶ Y where
  toFun := fun xy => xy.1.2
  tracked := by
    refine ⟨C.snd, ?_⟩
    rintro xy r ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, C.app_snd a b, hb⟩

@[simp]
theorem pullback_condition (C : ChosenPairing P) {X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackFst C f g ≫ f = pullbackSnd C f g ≫ g := by
  apply hom_eq_of_pointwise
  intro xy
  exact xy.2

/-- The mediating arrow into the explicit pullback. -/
def pullbackLift (C : ChosenPairing P) {W X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (square : h ≫ f = k ≫ g) : W ⟶ pullback C f g where
  toFun := fun x => ⟨(h.toFun x, k.toFun x),
    congrArg (fun q : W ⟶ Z => q.toFun x) square⟩
  tracked := by
    rcases h.tracked with ⟨e, he⟩
    rcases k.tracked with ⟨d, hd⟩
    refine ⟨C.fork e d, ?_⟩
    intro x r hr
    rcases he x r hr with ⟨a, hea, ha⟩
    rcases hd x r hr with ⟨b, hdb, hb⟩
    exact ⟨C.pairVal a b, C.app_fork hea hdb, a, ha, b, hb, rfl⟩

@[simp]
theorem pullbackLift_fst (C : ChosenPairing P) {W X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (square : h ≫ f = k ≫ g) :
    pullbackLift C f g h k square ≫ pullbackFst C f g = h := by
  apply hom_eq_of_pointwise
  intro x
  rfl

@[simp]
theorem pullbackLift_snd (C : ChosenPairing P) {W X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (square : h ≫ f = k ≫ g) :
    pullbackLift C f g h k square ≫ pullbackSnd C f g = k := by
  apply hom_eq_of_pointwise
  intro x
  rfl

/-- Exact pullback uniqueness in the assembly category. -/
theorem pullbackLift_unique (C : ChosenPairing P) {W X Y Z : Assembly.{u, v} P}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (square : h ≫ f = k ≫ g) (m : W ⟶ pullback C f g)
    (hmf : m ≫ pullbackFst C f g = h)
    (hms : m ≫ pullbackSnd C f g = k) :
    m = pullbackLift C f g h k square := by
  apply hom_eq_of_pointwise
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : W ⟶ X => q.toFun x) hmf
  · exact congrArg (fun q : W ⟶ Y => q.toFun x) hms

/-! ## Effective covers and pullback stability -/

/-- `liftCode` uniformly computes a source realizer above every realized target point. -/
def TracksCover {X Y : Assembly.{u, v} P} (q : X ⟶ Y) (liftCode : P.Carrier) : Prop :=
  ∀ y r, Y.Realizes r y →
    ∃ x s, q.toFun x = y ∧ P.App liftCode r s ∧ X.Realizes s x

/-- A computational cover.  Unlike bare surjectivity, it carries one uniform realizer-lifting
program, which is the data needed for realizability descent. -/
def EffectiveCover {X Y : Assembly.{u, v} P} (q : X ⟶ Y) : Prop :=
  ∃ liftCode, TracksCover q liftCode

/-- An effective cover is surjective on semantic points. -/
theorem effectiveCover_surjective {X Y : Assembly.{u, v} P} {q : X ⟶ Y}
    (hq : EffectiveCover q) : Function.Surjective q.toFun := by
  rcases hq with ⟨liftCode, hlift⟩
  intro y
  rcases Y.realized y with ⟨r, hr⟩
  rcases hlift y r hr with ⟨x, s, hxy, hrs, hs⟩
  exact ⟨x, hxy⟩

/-- Identity is an effective cover, tracked and lifted by the PCA identity program. -/
theorem effectiveCover_id (X : Assembly.{u, v} P) :
    EffectiveCover (𝟙 X) := by
  refine ⟨P.ident, ?_⟩
  intro x r hr
  exact ⟨x, r, rfl, P.app_ident r, hr⟩

/-- Effective covers compose.  The composite lifting program runs the outer lift and then the
inner lift, mirroring semantic preimage composition. -/
theorem effectiveCover_comp {X Y Z : Assembly.{u, v} P}
    {q : X ⟶ Y} {r : Y ⟶ Z}
    (hq : EffectiveCover q) (hr : EffectiveCover r) :
    EffectiveCover (q ≫ r) := by
  rcases hq with ⟨qCode, hq⟩
  rcases hr with ⟨rCode, hr⟩
  refine ⟨P.compose qCode rCode, ?_⟩
  intro z a ha
  rcases hr z a ha with ⟨y, b, hry, hab, hb⟩
  rcases hq y b hb with ⟨x, c, hqx, hbc, hc⟩
  refine ⟨x, c, ?_, P.app_compose hab hbc, hc⟩
  change r.toFun (q.toFun x) = z
  rw [hqx]
  exact hry

/-- Effective covers are stable under pullback.  The new lifting program first runs the tracker
of the base-change map, then the old cover lift, and forks that result with the original target
realizer to construct the pullback pair. -/
theorem effectiveCover_pullback (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} {q : X ⟶ Z} (g : Y ⟶ Z)
    (hq : EffectiveCover q) : EffectiveCover (pullbackSnd C q g) := by
  rcases hq with ⟨liftCode, hlift⟩
  rcases g.tracked with ⟨gCode, hg⟩
  refine ⟨C.fork (P.compose liftCode gCode) P.ident, ?_⟩
  intro y r hr
  rcases hg y r hr with ⟨t, hgrt, ht⟩
  rcases hlift (g.toFun y) t ht with ⟨x, s, hqx, hlts, hs⟩
  let xy : (pullback C q g).Carrier := ⟨(x, y), hqx⟩
  refine ⟨xy, C.pairVal s r, rfl, ?_, ?_⟩
  · exact C.app_fork (P.app_compose hgrt hlts) (P.app_ident r)
  · exact ⟨s, hs, r, hr, rfl⟩

/-! ## Kernel pairs -/

/-- The explicit kernel pair of an assembly morphism. -/
def kernelPair (C : ChosenPairing P) {X Y : Assembly.{u, v} P}
    (f : X ⟶ Y) : Assembly.{u, v} P := pullback C f f

def kernelPairFst (C : ChosenPairing P) {X Y : Assembly.{u, v} P}
    (f : X ⟶ Y) : kernelPair C f ⟶ X := pullbackFst C f f

def kernelPairSnd (C : ChosenPairing P) {X Y : Assembly.{u, v} P}
    (f : X ⟶ Y) : kernelPair C f ⟶ X := pullbackSnd C f f

@[simp]
theorem kernelPair_condition (C : ChosenPairing P) {X Y : Assembly.{u, v} P}
    (f : X ⟶ Y) : kernelPairFst C f ≫ f = kernelPairSnd C f ≫ f :=
  pullback_condition C f f

/-- Coequalizing the explicit kernel pair is exactly constancy on semantic fibers. -/
theorem coequalizes_kernelPair_iff (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (f : X ⟶ Y) (h : X ⟶ Z) :
    kernelPairFst C f ≫ h = kernelPairSnd C f ≫ h ↔
      ∀ x x', f.toFun x = f.toFun x' → h.toFun x = h.toFun x' := by
  constructor
  · intro heq x x' hfx
    let p : (kernelPair C f).Carrier := ⟨(x, x'), hfx⟩
    exact congrArg (fun q : kernelPair C f ⟶ Z => q.toFun p) heq
  · intro hfiber
    apply hom_eq_of_pointwise
    intro p
    exact hfiber p.1.1 p.1.2 p.2

/-! ## Effective-cover descent -/

/-- A chosen semantic lift along an effective cover.  Choice is used only to define the
extensional semantic function; the tracker below uses the cover's explicit PCA lifting program. -/
noncomputable def coverRepresentative {X Y : Assembly.{u, v} P} (q : X ⟶ Y)
    (hq : EffectiveCover q) (y : Y.Carrier) : X.Carrier :=
  Classical.choose (effectiveCover_surjective hq y)

theorem coverRepresentative_spec {X Y : Assembly.{u, v} P} (q : X ⟶ Y)
    (hq : EffectiveCover q) (y : Y.Carrier) :
    q.toFun (coverRepresentative q hq y) = y :=
  Classical.choose_spec (effectiveCover_surjective hq y)

/-- Descent along an effective cover.  The semantic map chooses a lift; the executable tracker
does not: it runs the cover's uniform lift program and then the tracker for `h`. -/
noncomputable def coverDesc (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (q : X ⟶ Y) (hq : EffectiveCover q)
    (h : X ⟶ Z)
    (heq : kernelPairFst C q ≫ h = kernelPairSnd C q ≫ h) : Y ⟶ Z where
  toFun := fun y => h.toFun (coverRepresentative q hq y)
  tracked := by
    have hfiber := (coequalizes_kernelPair_iff C q h).1 heq
    rcases hq with ⟨liftCode, hlift⟩
    rcases h.tracked with ⟨hCode, hh⟩
    refine ⟨P.compose hCode liftCode, ?_⟩
    intro y r hr
    rcases hlift y r hr with ⟨x, s, hqx, hrs, hs⟩
    rcases hh x s hs with ⟨t, hst, ht⟩
    have hout : h.toFun x = h.toFun (coverRepresentative q ⟨liftCode, hlift⟩ y) := by
      apply hfiber
      exact hqx.trans (coverRepresentative_spec q ⟨liftCode, hlift⟩ y).symm
    exact ⟨t, P.app_compose hrs hst, by simpa [hout] using ht⟩

@[simp]
theorem coverDesc_fac (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (q : X ⟶ Y) (hq : EffectiveCover q)
    (h : X ⟶ Z)
    (heq : kernelPairFst C q ≫ h = kernelPairSnd C q ≫ h) :
    q ≫ coverDesc C q hq h heq = h := by
  have hfiber := (coequalizes_kernelPair_iff C q h).1 heq
  apply hom_eq_of_pointwise
  intro x
  apply hfiber
  exact coverRepresentative_spec q hq (q.toFun x)

/-- Effective-cover descent is unique. -/
theorem coverDesc_unique (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (q : X ⟶ Y) (hq : EffectiveCover q)
    (h : X ⟶ Z)
    (heq : kernelPairFst C q ≫ h = kernelPairSnd C q ≫ h)
    (k : Y ⟶ Z) (hk : q ≫ k = h) :
    k = coverDesc C q hq h heq := by
  apply hom_eq_of_pointwise
  intro y
  let x := coverRepresentative q hq y
  have hkx := congrArg (fun m : X ⟶ Z => m.toFun x) hk
  have hqx : q.toFun x = y := coverRepresentative_spec q hq y
  change k.toFun y = h.toFun x
  rw [← hqx]
  exact hkx

/-- Every effective cover is the coequalizer of its kernel pair.  Combined with
`effectiveCover_pullback`, this gives a pullback-stable class of regular epimorphisms rather than
mere set-surjections. -/
theorem effectiveCover_isKernelPairCoequalizer (C : ChosenPairing P)
    {X Y : Assembly.{u, v} P} (q : X ⟶ Y) (hq : EffectiveCover q) :
    kernelPairFst C q ≫ q = kernelPairSnd C q ≫ q ∧
    ∀ (Z : Assembly.{u, v} P) (h : X ⟶ Z),
      kernelPairFst C q ≫ h = kernelPairSnd C q ≫ h →
      ∃! k : Y ⟶ Z, q ≫ k = h := by
  constructor
  · exact kernelPair_condition C q
  · intro Z h heq
    refine ⟨coverDesc C q hq h heq, coverDesc_fac C q hq h heq, ?_⟩
    intro k hk
    exact coverDesc_unique C q hq h heq k hk

/-! ## Regular image factorization -/

/-- The image assembly retains a source realizer, not merely a target realizer.  This choice is
what makes the quotient map an effective cover and makes its coequalizer descent executable. -/
def image {X Y : Assembly.{u, v} P} (f : X ⟶ Y) : Assembly.{u, v} P where
  Carrier := {y : Y.Carrier // ∃ x, f.toFun x = y}
  Realizes := fun r y => ∃ x, X.Realizes r x ∧ f.toFun x = y.1
  realized := by
    intro y
    rcases y.2 with ⟨x, hxy⟩
    rcases X.realized x with ⟨r, hr⟩
    exact ⟨r, x, hr, hxy⟩

/-- Quotient onto the regular image, tracked by identity. -/
def imageQuot {X Y : Assembly.{u, v} P} (f : X ⟶ Y) : X ⟶ image f where
  toFun := fun x => ⟨f.toFun x, x, rfl⟩
  tracked := by
    refine ⟨P.ident, ?_⟩
    intro x r hr
    exact ⟨r, P.app_ident r, x, hr, rfl⟩

/-- Inclusion of the regular image, tracked by the original program. -/
def imageIncl {X Y : Assembly.{u, v} P} (f : X ⟶ Y) : image f ⟶ Y where
  toFun := Subtype.val
  tracked := by
    rcases f.tracked with ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro y r hr
    rcases hr with ⟨x, hx, hfx⟩
    rcases he x r hx with ⟨s, hers, hs⟩
    exact ⟨s, hers, by simpa [hfx] using hs⟩

@[simp]
theorem image_factorization {X Y : Assembly.{u, v} P} (f : X ⟶ Y) :
    imageQuot f ≫ imageIncl f = f := by
  apply hom_eq_of_pointwise
  intro x
  rfl

theorem imageQuot_surjective {X Y : Assembly.{u, v} P} (f : X ⟶ Y) :
    Function.Surjective (imageQuot f).toFun := by
  intro y
  rcases y.2 with ⟨x, hxy⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The image quotient is an effective cover, with identity as its realizer-lifting program. -/
theorem imageQuot_effectiveCover {X Y : Assembly.{u, v} P} (f : X ⟶ Y) :
    EffectiveCover (imageQuot f) := by
  refine ⟨P.ident, ?_⟩
  intro y r hr
  rcases hr with ⟨x, hx, hfx⟩
  refine ⟨x, r, ?_, P.app_ident r, hx⟩
  apply Subtype.ext
  exact hfx

/-- The image inclusion is monic, stated as the exact cancellation law. -/
theorem imageIncl_monic {X Y Z : Assembly.{u, v} P} (f : X ⟶ Y)
    (g h : Z ⟶ image f) (eqn : g ≫ imageIncl f = h ≫ imageIncl f) : g = h := by
  apply hom_eq_of_pointwise
  intro z
  apply Subtype.ext
  exact congrArg (fun q : Z ⟶ Y => q.toFun z) eqn

/-- The regular-image quotient has exactly the same semantic kernel as the original map. -/
theorem imageQuot_eq_iff {X Y : Assembly.{u, v} P} (f : X ⟶ Y)
    (x x' : X.Carrier) :
    (imageQuot f).toFun x = (imageQuot f).toFun x' ↔
      f.toFun x = f.toFun x' := by
  constructor
  · exact fun h => congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

noncomputable def imageRepresentative {X Y : Assembly.{u, v} P} (f : X ⟶ Y)
    (y : (image f).Carrier) : X.Carrier := Classical.choose y.2

theorem imageRepresentative_spec {X Y : Assembly.{u, v} P} (f : X ⟶ Y)
    (y : (image f).Carrier) :
    f.toFun (imageRepresentative f y) = y.1 := Classical.choose_spec y.2

/-- Descent through the image quotient.  Tracking is inherited from `h`; the kernel-pair equation
proves that choosing a representative does not change the semantic output. -/
noncomputable def imageDesc (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (f : X ⟶ Y) (h : X ⟶ Z)
    (heq : kernelPairFst C (imageQuot f) ≫ h =
      kernelPairSnd C (imageQuot f) ≫ h) : image f ⟶ Z where
  toFun := fun y => h.toFun (imageRepresentative f y)
  tracked := by
    have hfiber := (coequalizes_kernelPair_iff C (imageQuot f) h).1 heq
    rcases h.tracked with ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro y r hr
    rcases hr with ⟨x, hx, hfx⟩
    rcases he x r hx with ⟨s, hers, hs⟩
    have hq : (imageQuot f).toFun x =
        (imageQuot f).toFun (imageRepresentative f y) := by
      apply Subtype.ext
      exact hfx.trans (imageRepresentative_spec f y).symm
    have hh : h.toFun x = h.toFun (imageRepresentative f y) := hfiber x _ hq
    exact ⟨s, hers, by simpa [hh] using hs⟩

@[simp]
theorem imageDesc_fac (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (f : X ⟶ Y) (h : X ⟶ Z)
    (heq : kernelPairFst C (imageQuot f) ≫ h =
      kernelPairSnd C (imageQuot f) ≫ h) :
    imageQuot f ≫ imageDesc C f h heq = h := by
  have hfiber := (coequalizes_kernelPair_iff C (imageQuot f) h).1 heq
  apply hom_eq_of_pointwise
  intro x
  apply Eq.symm
  apply hfiber
  apply Subtype.ext
  exact (imageRepresentative_spec f ((imageQuot f).toFun x)).symm

/-- Uniqueness of descent through the image quotient. -/
theorem imageDesc_unique (C : ChosenPairing P)
    {X Y Z : Assembly.{u, v} P} (f : X ⟶ Y) (h : X ⟶ Z)
    (heq : kernelPairFst C (imageQuot f) ≫ h =
      kernelPairSnd C (imageQuot f) ≫ h)
    (k : image f ⟶ Z) (hk : imageQuot f ≫ k = h) :
    k = imageDesc C f h heq := by
  apply hom_eq_of_pointwise
  intro y
  let x := imageRepresentative f y
  have hkx := congrArg (fun q : X ⟶ Z => q.toFun x) hk
  have hqx : (imageQuot f).toFun x = y := by
    apply Subtype.ext
    exact imageRepresentative_spec f y
  change k.toFun y = h.toFun x
  rw [← hqx]
  exact hkx

/-- The image quotient is the coequalizer of its kernel pair.  This is the regular-epimorphism
fragment needed by exact completion, stated without importing a separate categorical colimit
API. -/
theorem imageQuot_isKernelPairCoequalizer (C : ChosenPairing P)
    {X Y : Assembly.{u, v} P} (f : X ⟶ Y) :
    kernelPairFst C (imageQuot f) ≫ imageQuot f =
      kernelPairSnd C (imageQuot f) ≫ imageQuot f ∧
    ∀ (Z : Assembly.{u, v} P) (h : X ⟶ Z),
      kernelPairFst C (imageQuot f) ≫ h =
        kernelPairSnd C (imageQuot f) ≫ h →
      ∃! k : image f ⟶ Z, imageQuot f ≫ k = h := by
  constructor
  · exact kernelPair_condition C (imageQuot f)
  · intro Z h heq
    refine ⟨imageDesc C f h heq, imageDesc_fac C f h heq, ?_⟩
    intro k hk
    exact imageDesc_unique C f h heq k hk

/-! ## Certified programs obtain the categorical factorization -/

/-- A compiled program's assembly morphism factors through an effective regular-image cover and
a monic inclusion.  All three arrows are executable in the relational PCA sense. -/
theorem ProgramCertificate.has_regular_image_factorization
    {A : Representation P α} {B : Representation P β} {f : α → β}
    (cert : ProgramCertificate A B f) :
    EffectiveCover (imageQuot cert.hom) ∧
      (∀ (Z : Assembly P) (g h : Z ⟶ image cert.hom),
        g ≫ imageIncl cert.hom = h ≫ imageIncl cert.hom → g = h) ∧
      imageQuot cert.hom ≫ imageIncl cert.hom = cert.hom := by
  exact ⟨imageQuot_effectiveCover cert.hom,
    fun Z g h eqn => imageIncl_monic cert.hom g h eqn,
    image_factorization cert.hom⟩

/-! ## Commitment/query soundness is not produced by the category -/

/-- An external proof-system view of an output claim.  A concrete STARK/IOP instantiation puts
its transcript commitment and sampled-query verification inside `verify`. -/
structure OutputAttestation (B : Type v) where
  Proof : Type w
  verify : B → Proof → Bool

namespace OutputAttestation

/-- Honest outputs have an accepted proof. -/
def CompleteFor (V : OutputAttestation.{v, w} β) (f : α → β) : Prop :=
  ∀ x, ∃ proof, V.verify (f x) proof = true

/-- Every accepted output is in the compiled program's semantic range.  For a query protocol,
this is the conclusion supplied only after commitment binding and query-soundness reductions. -/
def RangeSoundFor (V : OutputAttestation.{v, w} β) (f : α → β) : Prop :=
  ∀ y proof, V.verify y proof = true → ∃ x, f x = y

end OutputAttestation

/-- A certified constant-false program over the concrete one-point PCA. -/
def unitBoolRepresentation : Representation PCA.unitPCA Bool where
  encode := fun _ => ()

def unitInputRepresentation : Representation PCA.unitPCA Unit where
  encode := fun _ => ()

def constantFalse : Unit → Bool := fun _ => false

def constantFalseCertificate : ProgramCertificate unitInputRepresentation
    unitBoolRepresentation constantFalse where
  code := ()
  runs := by
    intro x
    trivial

/-- The compiled map itself is not a cover: its semantic range contains only `false`.  The
regular-image quotient is the cover, so the epi/mono factorization has a genuine two-valued
polarity even over the one-point PCA. -/
theorem constantFalseCertificate_hom_not_effectiveCover :
    ¬ EffectiveCover constantFalseCertificate.hom := by
  intro hcover
  rcases effectiveCover_surjective hcover true with ⟨x, hx⟩
  cases x
  cases hx

/-- The always-accept verifier is complete for the certified program. -/
def alwaysAcceptBool : OutputAttestation Bool where
  Proof := Unit
  verify := fun _ _ => true

/-- For the always-accept backend, range soundness collapses exactly to semantic surjectivity.
No commitment or query argument is hiding in the verifier. -/
theorem alwaysAcceptBool_rangeSound_iff_surjective (f : α → Bool) :
    alwaysAcceptBool.RangeSoundFor f ↔ Function.Surjective f := by
  constructor
  · intro h y
    exact h y () rfl
  · intro h y proof haccept
    exact h y

theorem alwaysAcceptBool_complete :
    alwaysAcceptBool.CompleteFor constantFalse := by
  intro x
  exact ⟨(), rfl⟩

/-- But it accepts an output outside the program image.  Therefore a compiled PCA program, its
effective cover, and its kernel-pair descent theorem do not imply transcript-binding/query
soundness. -/
theorem alwaysAcceptBool_not_rangeSound :
    ¬ alwaysAcceptBool.RangeSoundFor constantFalse := by
  intro hsound
  rcases hsound true () rfl with ⟨x, hx⟩
  cases x
  cases hx

/-- Concrete boundary theorem: the program certificate and regular-image factorization coexist
with a complete but range-unsound attestation backend. -/
theorem compiled_regular_image_does_not_supply_query_soundness :
    (∃ cert : ProgramCertificate unitInputRepresentation unitBoolRepresentation constantFalse,
      EffectiveCover (imageQuot cert.hom)) ∧
    alwaysAcceptBool.CompleteFor constantFalse ∧
    ¬ alwaysAcceptBool.RangeSoundFor constantFalse := by
  exact ⟨⟨constantFalseCertificate,
      imageQuot_effectiveCover constantFalseCertificate.hom⟩,
    alwaysAcceptBool_complete, alwaysAcceptBool_not_rangeSound⟩

#assert_all_clean [pullback_condition, pullbackLift_fst, pullbackLift_snd,
  pullbackLift_unique, effectiveCover_surjective, effectiveCover_id,
  effectiveCover_comp, effectiveCover_pullback,
  kernelPair_condition, coequalizes_kernelPair_iff, coverRepresentative_spec,
  coverDesc_fac, coverDesc_unique, effectiveCover_isKernelPairCoequalizer,
  image_factorization,
  imageQuot_surjective, imageQuot_effectiveCover, imageIncl_monic,
  imageQuot_eq_iff, imageRepresentative_spec, imageDesc_fac, imageDesc_unique,
  imageQuot_isKernelPairCoequalizer,
  ProgramCertificate.has_regular_image_factorization,
  constantFalseCertificate_hom_not_effectiveCover,
  alwaysAcceptBool_rangeSound_iff_surjective, alwaysAcceptBool_complete,
  alwaysAcceptBool_not_rangeSound,
  compiled_regular_image_does_not_supply_query_soundness]

end Assembly
end Dregg2.Realizability
