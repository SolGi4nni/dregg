/-
# Dregg2.Realizability.UFamTripos — uniform families and the Set-tripos law package.

For an evidenced frame `F`, `UFam F I` is the family `I → F.Proposition`; an entailment is
witnessed by one evidence element that works at every index.  The first half of this file proves
the indexed-preorder, strict substitution, finite-meet, implication, and exact-generic-predicate
laws directly from the evidenced-frame interface.

The second half specializes to the PCA evidenced frame.  There, the existing concrete sum and
quantifier constructions supply joins and both arbitrary-map adjoints.  The resulting bundle has
the customary Set-indexed tripos laws: Heyting preorders, strict reindexing, existential and
universal adjoints, weak-pullback Beck--Chevalley, and a generic predicate.  We call this a
`UFamTriposLaws` witness, but make no tripos-to-topos construction and no claim that such a topos
has been formalized here.
-/
import Dregg2.Realizability.EvidencedFrame
import Dregg2.Realizability.TriposFragment

namespace Dregg2.Realizability

universe u v w x y

namespace UFam

/-- Uniform families of propositions of an evidenced frame. -/
abbrev Predicate (F : EvidencedFrame.{u, v}) (I : Type w) := I → F.Proposition

/-- Evidence `e` works pointwise and uniformly across the entire family. -/
def Tracks (F : EvidencedFrame.{u, v}) {I : Type w} (e : F.Evidence)
    (a b : Predicate F I) : Prop :=
  ∀ i, F.Leads (a i) e (b i)

/-- The preorder relation forgets which uniform evidence witnesses the transformation. -/
def Entails (F : EvidencedFrame.{u, v}) {I : Type w}
    (a b : Predicate F I) : Prop :=
  ∃ e, Tracks F e a b

/-- Contravariant substitution is precomposition. -/
def reindex (F : EvidencedFrame.{u, v}) {I : Type w} {J : Type x}
    (f : J → I) (a : Predicate F I) : Predicate F J :=
  fun j => a (f j)

theorem tracks_ident (F : EvidencedFrame.{u, v}) {I : Type w}
    (a : Predicate F I) : Tracks F F.identEvidence a a := by
  intro i
  exact F.leads_ident (a i)

theorem entails_refl (F : EvidencedFrame.{u, v}) {I : Type w}
    (a : Predicate F I) : Entails F a a :=
  ⟨F.identEvidence, tracks_ident F a⟩

theorem tracks_compose (F : EvidencedFrame.{u, v}) {I : Type w}
    {a b c : Predicate F I} {e d : F.Evidence}
    (he : Tracks F e a b) (hd : Tracks F d b c) :
    Tracks F (F.composeEvidence e d) a c := by
  intro i
  exact F.leads_compose (he i) (hd i)

theorem entails_trans (F : EvidencedFrame.{u, v}) {I : Type w}
    {a b c : Predicate F I} (hab : Entails F a b) (hbc : Entails F b c) :
    Entails F a c := by
  rcases hab with ⟨e, he⟩
  rcases hbc with ⟨d, hd⟩
  exact ⟨F.composeEvidence e d, tracks_compose F he hd⟩

@[simp] theorem reindex_id (F : EvidencedFrame.{u, v}) {I : Type w}
    (a : Predicate F I) : reindex F id a = a := rfl

@[simp] theorem reindex_comp (F : EvidencedFrame.{u, v})
    {I : Type w} {J : Type x} {K : Type y} (f : J → I) (g : K → J)
    (a : Predicate F I) :
    reindex F g (reindex F f a) = reindex F (f ∘ g) a := rfl

theorem entails_reindex (F : EvidencedFrame.{u, v})
    {I : Type w} {J : Type x} (f : J → I) {a b : Predicate F I}
    (h : Entails F a b) : Entails F (reindex F f a) (reindex F f b) := by
  rcases h with ⟨e, he⟩
  exact ⟨e, fun j => he (f j)⟩

/-! ## Pointwise evidenced-frame logic -/

def truth (F : EvidencedFrame.{u, v}) {I : Type w} : Predicate F I :=
  fun _ => F.top

def meet (F : EvidencedFrame.{u, v}) {I : Type w}
    (a b : Predicate F I) : Predicate F I :=
  fun i => F.meet (a i) (b i)

def implication (F : EvidencedFrame.{u, v}) {I : Type w}
    (a b : Predicate F I) : Predicate F I :=
  fun i => F.implication (a i) (b i)

theorem entails_truth (F : EvidencedFrame.{u, v}) {I : Type w}
    (a : Predicate F I) : Entails F a (truth F) :=
  ⟨F.topEvidence, fun i => F.leads_top (a i)⟩

theorem entails_meet_iff (F : EvidencedFrame.{u, v}) {I : Type w}
    {a b c : Predicate F I} :
    Entails F a (meet F b c) ↔ Entails F a b ∧ Entails F a c := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨⟨F.composeEvidence e F.fstEvidence, ?_⟩,
      ⟨F.composeEvidence e F.sndEvidence, ?_⟩⟩
    · intro i
      exact F.leads_compose (he i) (F.leads_fst (b i) (c i))
    · intro i
      exact F.leads_compose (he i) (F.leads_snd (b i) (c i))
  · rintro ⟨⟨e, he⟩, ⟨d, hd⟩⟩
    exact ⟨F.pairEvidence e d, fun i => F.leads_meet (he i) (hd i)⟩

/-- The evidenced-frame universal implication gives the fiberwise Heyting adjunction. -/
theorem entails_implication_iff (F : EvidencedFrame.{u, v}) {I : Type w}
    {a b c : Predicate F I} :
    Entails F (meet F a b) c ↔ Entails F a (implication F b c) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨F.curryEvidence e, ?_⟩
    intro i
    apply F.leads_universalImp
    intro target htarget
    rcases Set.mem_singleton_iff.mp htarget with rfl
    exact he i
  · rintro ⟨e, he⟩
    let leftToImp : F.Evidence := F.composeEvidence F.fstEvidence e
    let packed : F.Evidence := F.pairEvidence leftToImp F.sndEvidence
    refine ⟨F.composeEvidence packed F.evalEvidence, ?_⟩
    intro i
    have himp : F.Leads (F.meet (a i) (b i)) leftToImp
        (F.implication (b i) (c i)) :=
      F.leads_compose (F.leads_fst (a i) (b i)) (he i)
    have harg : F.Leads (F.meet (a i) (b i)) F.sndEvidence (b i) :=
      F.leads_snd (a i) (b i)
    have hpacked : F.Leads (F.meet (a i) (b i)) packed
        (F.meet (F.implication (b i) (c i)) (b i)) :=
      F.leads_meet himp harg
    exact F.leads_compose hpacked
      (F.leads_eval (a := b i) (targets := {c i}) (Set.mem_singleton (c i)))

@[simp] theorem reindex_truth (F : EvidencedFrame.{u, v})
    {I : Type w} {J : Type x} (f : J → I) :
    reindex F f (truth F) = truth F := rfl

@[simp] theorem reindex_meet (F : EvidencedFrame.{u, v})
    {I : Type w} {J : Type x} (f : J → I) (a b : Predicate F I) :
    reindex F f (meet F a b) = meet F (reindex F f a) (reindex F f b) := rfl

@[simp] theorem reindex_implication (F : EvidencedFrame.{u, v})
    {I : Type w} {J : Type x} (f : J → I) (a b : Predicate F I) :
    reindex F f (implication F a b) =
      implication F (reindex F f a) (reindex F f b) := rfl

/-! ## The exact UFam generic predicate -/

/-- The generic UFam predicate is the identity family of frame propositions. -/
def generic (F : EvidencedFrame.{u, v}) : Predicate F F.Proposition := id

/-- A family itself is its classifying map into the proposition object. -/
def classify (F : EvidencedFrame.{u, v}) {I : Type w}
    (a : Predicate F I) : I → F.Proposition := a

theorem reindex_generic (F : EvidencedFrame.{u, v}) {I : Type w}
    (a : Predicate F I) :
    reindex F (classify F a) (generic F) = a := rfl

#assert_all_clean [tracks_ident, entails_refl, tracks_compose, entails_trans,
  reindex_id, reindex_comp, entails_reindex, entails_truth, entails_meet_iff,
  entails_implication_iff, reindex_truth, reindex_meet, reindex_implication,
  reindex_generic]

end UFam

/-! ## Exact bridge to the already-formalized PCA doctrine -/

/-- Uniform-family tracking over the PCA evidenced frame is definitionally the existing
`Tracks` relation. -/
theorem pcaUFam_tracks_iff (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) {I : Type w} {e : P.Carrier} {a b : Pred P I} :
    UFam.Tracks (pcaEvidencedFrame P C Q) e a b ↔ Tracks P e a b := Iff.rfl

/-- UFam entailment over the PCA frame does not change the semantics. -/
theorem pcaUFam_entails_iff (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) {I : Type w} {a b : Pred P I} :
    UFam.Entails (pcaEvidencedFrame P C Q) a b ↔ Entails P a b := Iff.rfl

/-- The existing existential is the UFam left adjoint along every set map. -/
theorem pcaUFam_exists_adjunction (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) {J : Type w} {I : Type x}
    (f : J → I) (a : Pred P J) (b : Pred P I) :
    UFam.Entails (pcaEvidencedFrame P C Q) (existsReal P f a) b ↔
      UFam.Entails (pcaEvidencedFrame P C Q) a (UFam.reindex (pcaEvidencedFrame P C Q) f b) :=
  existsReal_adjunction P f a b

/-- The thunked universal is the UFam right adjoint along every set map, including maps with
empty fibers. -/
theorem pcaUFam_forall_adjunction (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) {J : Type w} {I : Type x}
    (f : J → I) (a : Pred P J) (b : Pred P I) :
    UFam.Entails (pcaEvidencedFrame P C Q)
        (UFam.reindex (pcaEvidencedFrame P C Q) f b) a ↔
      UFam.Entails (pcaEvidencedFrame P C Q) b (forallReal P C f a) :=
  forallReal_adjunction P C f a b

/-- Existential Beck--Chevalley is literal equality in UFam. -/
theorem pcaUFam_exists_beckChevalley (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C)
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : WeakPullbackSquare g q f h) (a : Pred P J) :
    UFam.reindex (pcaEvidencedFrame P C Q) h (existsReal P f a) =
      existsReal P q (UFam.reindex (pcaEvidencedFrame P C Q) g a) :=
  existsReal_beckChevalley P W a

/-- Universal Beck--Chevalley is literal equality in UFam. -/
theorem pcaUFam_forall_beckChevalley (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C)
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : WeakPullbackSquare g q f h) (a : Pred P J) :
    UFam.reindex (pcaEvidencedFrame P C Q) h (forallReal P C f a) =
      forallReal P C q (UFam.reindex (pcaEvidencedFrame P C Q) g a) :=
  forallReal_beckChevalley P C W a

/-- Generic classification is exact equality, not merely mutual entailment. -/
theorem pcaUFam_generic_classification (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) {I : Type w} (a : Pred P I) :
    UFam.reindex (pcaEvidencedFrame P C Q)
      (UFam.classify (pcaEvidencedFrame P C Q) a)
      (UFam.generic (pcaEvidencedFrame P C Q)) = a := rfl

/-- The indexed PCA doctrine is consistent in the direct preorder sense: uniform truth cannot
entail falsity, already over the singleton index. -/
theorem pcaUFam_truth_not_entails_falsity (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) :
    ¬ UFam.Entails (pcaEvidencedFrame P C Q)
      (truth P : Pred P Unit) (falsity P) := by
  rintro ⟨e, he⟩
  rcases he () P.k trivial with ⟨y, hey, hy⟩
  exact hy

/-- A named package witnessing that the PCA `UFam` construction has the standard Set-indexed
tripos laws already proved in `TriposFragment`, plus exact evidence-level identification and a
non-collapse theorem.  This package does not construct the associated topos. -/
structure UFamTriposLaws (P : PCA.{u}) (C : ChosenPairing P)
    (S : ChosenSums P) (Q : ChosenCurrying P C) : Prop where
  logical_and_quantifier_laws : TriposFragmentLaws.{u, w} P C S Q
  evidence_relation_exact : ∀ {I : Type w} {e : P.Carrier} {a b : Pred P I},
    UFam.Tracks (pcaEvidencedFrame P C Q) e a b ↔ Tracks P e a b
  arbitrary_exists_adjunction : ∀ {J I : Type w} (f : J → I)
      (a : Pred P J) (b : Pred P I),
    UFam.Entails (pcaEvidencedFrame P C Q) (existsReal P f a) b ↔
      UFam.Entails (pcaEvidencedFrame P C Q) a
        (UFam.reindex (pcaEvidencedFrame P C Q) f b)
  arbitrary_forall_adjunction : ∀ {J I : Type w} (f : J → I)
      (a : Pred P J) (b : Pred P I),
    UFam.Entails (pcaEvidencedFrame P C Q)
        (UFam.reindex (pcaEvidencedFrame P C Q) f b) a ↔
      UFam.Entails (pcaEvidencedFrame P C Q) b (forallReal P C f a)
  generic_classification : ∀ {I : Type w} (a : Pred P I),
    UFam.reindex (pcaEvidencedFrame P C Q)
      (UFam.classify (pcaEvidencedFrame P C Q) a)
      (UFam.generic (pcaEvidencedFrame P C Q)) = a
  noncollapse : ¬ UFam.Entails (pcaEvidencedFrame P C Q)
    (truth P : Pred P Unit) (falsity P)

/-- The relational PCA construction satisfies the packaged UFam tripos laws. -/
def pcaUFamTriposLaws (P : PCA.{u}) (C : ChosenPairing P)
    (S : ChosenSums P) (Q : ChosenCurrying P C) :
    UFamTriposLaws.{u, w} P C S Q where
  logical_and_quantifier_laws := realizabilityTriposFragmentLaws P C S Q
  evidence_relation_exact := pcaUFam_tracks_iff P C Q
  arbitrary_exists_adjunction := pcaUFam_exists_adjunction P C Q
  arbitrary_forall_adjunction := pcaUFam_forall_adjunction P C Q
  generic_classification := pcaUFam_generic_classification P C Q
  noncollapse := pcaUFam_truth_not_entails_falsity P C Q

#assert_all_clean [pcaUFam_tracks_iff, pcaUFam_entails_iff,
  pcaUFam_exists_adjunction, pcaUFam_forall_adjunction,
  pcaUFam_exists_beckChevalley, pcaUFam_forall_beckChevalley,
  pcaUFam_generic_classification, pcaUFam_truth_not_entails_falsity,
  pcaUFamTriposLaws]

end Dregg2.Realizability
