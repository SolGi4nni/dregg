/-
# Dregg2.Realizability.EvidencedFrame — the PCA semantics as an evidenced frame.

An evidenced frame remembers *which* uniform transformer witnesses an entailment instead of
immediately truncating that transformer behind an existential.  This file gives the abstract
interface used by the `UFam` construction and then proves that the relational-PCA development
already supplies it.

The universal implication operation follows the evidenced-frame literature: `a ⇒ S` is one
proposition whose realizers uniformly map `a` into every proposition in `S`.  Its introduction
and evaluation laws are evidence-sensitive.  The PCA instance reuses `ChosenPairing` and
`ChosenCurrying`; it does not introduce a second realizability semantics.

This is an evidenced frame, not a topos.  The final theorems also expose a useful consistency
boundary: its derived bottom is literally the empty set, hence is not evidenceable, even for the
degenerate one-element PCA.
-/
import Dregg2.Realizability.LogicalStructure

namespace Dregg2.Realizability

universe u v

/-- An evidence-relevant presentation of a complete-Heyting-prealgebra core.

`Leads a e b` reads: evidence `e` transforms realizers of proposition `a` into realizers of
proposition `b`.  Universal implication takes an arbitrary set of consequents; this is the
operation from which the usual evidenced-frame `big meet`, bottom, and impredicative joins can
be defined.  Only the primitive laws needed by the uniform-family construction are recorded.
-/
structure EvidencedFrame where
  Proposition : Type u
  Evidence : Type v
  Leads : Proposition → Evidence → Proposition → Prop

  identEvidence : Evidence
  composeEvidence : Evidence → Evidence → Evidence
  leads_ident : ∀ a, Leads a identEvidence a
  leads_compose : ∀ {a b c e d},
    Leads a e b → Leads b d c → Leads a (composeEvidence e d) c

  top : Proposition
  topEvidence : Evidence
  leads_top : ∀ a, Leads a topEvidence top

  meet : Proposition → Proposition → Proposition
  pairEvidence : Evidence → Evidence → Evidence
  fstEvidence : Evidence
  sndEvidence : Evidence
  leads_meet : ∀ {a b c e d},
    Leads a e b → Leads a d c → Leads a (pairEvidence e d) (meet b c)
  leads_fst : ∀ a b, Leads (meet a b) fstEvidence a
  leads_snd : ∀ a b, Leads (meet a b) sndEvidence b

  universalImp : Proposition → Set Proposition → Proposition
  curryEvidence : Evidence → Evidence
  evalEvidence : Evidence
  leads_universalImp : ∀ {a b : Proposition} {targets : Set Proposition} {e : Evidence},
    (∀ c, c ∈ targets → Leads (meet a b) e c) →
      Leads a (curryEvidence e) (universalImp b targets)
  leads_eval : ∀ {a : Proposition} {targets : Set Proposition} {c : Proposition},
    c ∈ targets → Leads (meet (universalImp a targets) a) evalEvidence c

namespace EvidencedFrame

/-- Binary implication is universal implication into a singleton family. -/
def implication (F : EvidencedFrame.{u, v}) (a b : F.Proposition) : F.Proposition :=
  F.universalImp a {b}

/-- Arbitrary meet in the evidenced-frame presentation. -/
def infimum (F : EvidencedFrame.{u, v}) (targets : Set F.Proposition) : F.Proposition :=
  F.universalImp F.top targets

/-- Bottom is the meet of all propositions. -/
def bottom (F : EvidencedFrame.{u, v}) : F.Proposition :=
  F.infimum Set.univ

/-- A proposition is evidenceable when some evidence transforms top into it. -/
def Evidenceable (F : EvidencedFrame.{u, v}) (a : F.Proposition) : Prop :=
  ∃ e, F.Leads F.top e a

end EvidencedFrame

/-! ## The frame carried by a relational PCA -/

/-- Evidence-sensitive entailment between two unindexed PCA propositions.  It is exactly the
one-index specialization of `Tracks`, written without the inessential `Unit` argument. -/
def pcaLeads (P : PCA.{u}) (a : Set P.Carrier) (e : P.Carrier)
    (b : Set P.Carrier) : Prop :=
  ∀ x, x ∈ a → ∃ y, P.App e x y ∧ y ∈ b

/-- PCA meet, reusing the chosen-pair semantics from `Conjunction`. -/
def pcaMeet (P : PCA.{u}) (C : ChosenPairing P)
    (a b : Set P.Carrier) : Set P.Carrier :=
  (conj P C (fun _ : Unit => a) (fun _ : Unit => b)) ()

/-- PCA universal implication into a set of target propositions. -/
def pcaUniversalImp (P : PCA.{u}) (a : Set P.Carrier)
    (targets : Set (Set P.Carrier)) : Set P.Carrier :=
  {e | ∀ b, b ∈ targets → ∀ x, x ∈ a → ∃ y, P.App e x y ∧ y ∈ b}

/-- Every relational PCA with explicit pairing and currying code induces an evidenced frame.

The evidence operations are the already-derived PCA programs: identity, composition, fork,
projections, currying, and evaluation. -/
def pcaEvidencedFrame (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) : EvidencedFrame.{u, u} where
  Proposition := Set P.Carrier
  Evidence := P.Carrier
  Leads := pcaLeads P
  identEvidence := P.ident
  composeEvidence := fun e d => P.compose d e
  leads_ident := by
    intro a x hx
    exact ⟨x, P.app_ident x, hx⟩
  leads_compose := by
    intro a b c e d he hd x hx
    rcases he x hx with ⟨y, hey, hy⟩
    rcases hd y hy with ⟨z, hdz, hz⟩
    exact ⟨z, P.app_compose hey hdz, hz⟩
  top := Set.univ
  topEvidence := P.ident
  leads_top := by
    intro a x hx
    exact ⟨x, P.app_ident x, Set.mem_univ x⟩
  meet := pcaMeet P C
  pairEvidence := C.fork
  fstEvidence := C.fst
  sndEvidence := C.snd
  leads_meet := by
    intro a b c e d he hd x hx
    rcases he x hx with ⟨y, hey, hy⟩
    rcases hd x hx with ⟨z, hdz, hz⟩
    exact ⟨C.pairVal y z, C.app_fork hey hdz, ⟨y, hy, z, hz, rfl⟩⟩
  leads_fst := by
    intro a b r hr
    rcases hr with ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, C.app_fst x y, hx⟩
  leads_snd := by
    intro a b r hr
    rcases hr with ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, C.app_snd x y, hy⟩
  universalImp := pcaUniversalImp P
  curryEvidence := Q.curryArg
  evalEvidence := C.eval
  leads_universalImp := by
    intro a b targets e he t ht
    refine ⟨Q.curryVal e t, Q.app_curryArg e t, ?_⟩
    intro c hc x hx
    rcases he c hc (C.pairVal t x) ⟨t, ht, x, hx, rfl⟩ with ⟨y, hey, hy⟩
    exact ⟨y, Q.app_curryVal_iff.mpr hey, hy⟩
  leads_eval := by
    intro a targets c hc r hr
    rcases hr with ⟨e, he, x, hx, rfl⟩
    rcases he c hc x hx with ⟨y, hey, hy⟩
    exact ⟨y, C.app_eval hey, hy⟩

/-- The PCA frame relation is exactly uniform tracking on any constant family. -/
theorem pcaLeads_iff_tracks_const (P : PCA.{u}) {a b : Set P.Carrier} {e : P.Carrier} :
    pcaLeads P a e b ↔ Tracks P e (fun _ : Unit => a) (fun _ : Unit => b) := by
  constructor
  · intro h i
    exact h
  · intro h
    exact h ()

/-- The derived bottom of the PCA evidenced frame is literally the empty realizer set. -/
theorem pcaEvidencedFrame_bottom_eq_empty (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) :
    (pcaEvidencedFrame P C Q).bottom = (∅ : Set P.Carrier) := by
  change pcaUniversalImp P Set.univ Set.univ = (∅ : Set P.Carrier)
  apply Set.ext
  intro e
  constructor
  · intro he
    change ∀ b : Set P.Carrier, b ∈ (Set.univ : Set (Set P.Carrier)) →
      ∀ x, x ∈ (Set.univ : Set P.Carrier) →
        ∃ y, P.App e x y ∧ y ∈ b at he
    rcases he ∅ (Set.mem_univ ∅) P.k (Set.mem_univ P.k) with ⟨y, hey, hy⟩
    simp at hy
  · intro he
    simp at he

/-- The PCA evidenced frame is non-collapsed: bottom has no evidence from top. -/
theorem pcaEvidencedFrame_bottom_not_evidenceable (P : PCA.{u}) (C : ChosenPairing P)
    (Q : ChosenCurrying P C) :
    ¬ (pcaEvidencedFrame P C Q).Evidenceable (pcaEvidencedFrame P C Q).bottom := by
  rw [pcaEvidencedFrame_bottom_eq_empty P C Q]
  rintro ⟨e, he⟩
  rcases he P.k (Set.mem_univ P.k) with ⟨y, hey, hy⟩
  exact hy

/-- The unit PCA supplies a concrete evidenced frame, but does not make bottom evidenceable. -/
theorem unitPCAEvidencedFrame_consistent :
    ¬ (pcaEvidencedFrame PCA.unitPCA ChosenPairing.unitPairing
      ChosenCurrying.unitCurrying).Evidenceable
        (pcaEvidencedFrame PCA.unitPCA ChosenPairing.unitPairing
          ChosenCurrying.unitCurrying).bottom :=
  pcaEvidencedFrame_bottom_not_evidenceable PCA.unitPCA
    ChosenPairing.unitPairing ChosenCurrying.unitCurrying

#assert_all_clean [pcaLeads_iff_tracks_const, pcaEvidencedFrame_bottom_eq_empty,
  pcaEvidencedFrame_bottom_not_evidenceable, unitPCAEvidencedFrame_consistent]

end Dregg2.Realizability
