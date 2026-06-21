/-
# Metatheory.PolisAuthGame — the polis GROUNDED in dregg's authority/knowledge nouns & verbs.

Course-correction (ember): the polis is not a generic shield over a toy world — it is a theory of
KNOWLEDGE/AUTHORITY COORDINATION over dregg's *concrete* nouns and verbs, and its legitimacy floor IS
the substance discipline we already proved deployed. This file grounds it on the real objects:

  * **World** = `Dregg2.Authority.Caps` (`Label → List Cap`) — what authority each cell HOLDS (its
    knowledge-bearing, attenuable, proof-carrying capability tokens).
  * **Floor / legitimacy** = `Dregg2.Authority.PasRefined pol` — every conferred authority is bounded
    by the policy (authority never exceeds what was granted). The governor is NOT an external cop: it
    is this invariant, and `Dregg2.Authority.confinement_preserved` is the proof that an
    ATTENUATION-only turn preserves it (authority can only shrink across a boundary).
  * **Knowledge coordination** = `Dregg2.Authority.{Integrity, boundary_law}`: a cross-vat exercise is
    admissible iff a witness `Discharged` the predicate — you must *derive/prove the knowledge* to act
    across a boundary. Equivocation can't forge a discharge; laundering (growing authority) breaks
    `PasRefined`; both are refused by the substance discipline itself.

So the polis instantiates `SafetyGame` on `Caps` with `PasRefined` as the floor; the viability/
coordination layer of the rest of the polis rides on THIS, not on dist-to-home toys.
-/
import Metatheory.SafetyGame
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthGame

open Dregg2.Authority Metatheory.SafetyGame

variable (pol : Policy)

/-- **The authority game**: the polis over the real cap/knowledge state. A turn proposes a next
cap-state (`Caps`); the floor is the substance discipline `PasRefined pol` (authority ⊆ policy). -/
def authGame : Game where
  World := Caps
  Move := Caps
  Resp := Unit
  step := fun _ caps' _ => caps'
  legal := fun _ _ _ => True
  floor := PasRefined pol

@[simp] theorem authGame_floor (caps : Caps) :
    (authGame pol).floor caps = PasRefined pol caps := rfl

/-- **The legitimacy floor IS the substance discipline, and attenuation preserves it.** This is the
deployed `confinement_preserved`, read as "the polis floor is held by any authority-non-increasing
turn" — the governor is the substance discipline, not a bolt-on. -/
theorem authFloor_preserved_by_attenuation (caps caps' : Caps)
    (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s) :
    (authGame pol).floor caps' :=
  confinement_preserved pol caps caps' h noGrow

/-! ## The governor over the authority state is the substance discipline. -/

open Classical in
/-- The polis governor on the authority state: admit the proposed cap-state iff it stays within the
policy (`PasRefined`), else shield (keep the old caps). Decidability is classical (the floor is a
`∀` over labels/caps); the *content* is that this is exactly `genGovStep` over `PasRefined`. -/
noncomputable def authGov (caps caps' : Caps) : Caps :=
  if PasRefined pol caps' then caps' else caps

/-- **Laundering is refused by the floor itself.** A turn whose proposed cap-state would confer
authority outside the policy (`¬ PasRefined`) is shielded — the old caps stand. No external cop:
the substance discipline *is* the refusal. -/
theorem authGov_refuses_amplification (caps caps' : Caps)
    (hbad : ¬ PasRefined pol caps') : authGov pol caps caps' = caps := by
  unfold authGov; rw [if_neg hbad]

/-- **Honest attenuation is admitted.** A turn that only drops/narrows caps (never grows authority)
from a legitimate state lands within policy (by `confinement_preserved`), so it passes unchanged. -/
theorem authGov_admits_attenuation (caps caps' : Caps)
    (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s) :
    authGov pol caps caps' = caps' := by
  have hgood : PasRefined pol caps' := confinement_preserved pol caps caps' h noGrow
  unfold authGov; rw [if_pos hgood]

/-- The governor keeps the floor for EVERY proposed turn (admit-or-shield), from any legitimate
state — the `genGov_safe` shape over the real substance discipline. -/
theorem authGov_preserves (caps caps' : Caps) (h : PasRefined pol caps) :
    PasRefined pol (authGov pol caps caps') := by
  unfold authGov
  by_cases hb : PasRefined pol caps'
  · rwa [if_pos hb]
  · rwa [if_neg hb]

/-! ## Knowledge coordination: cross-vat exercise needs a DISCHARGED witness (derived knowledge). -/

/-- **Cross-vat coordination is gated by derivation**, re-exported as the polis's knowledge rule:
`Integrity` admits a change iff it is intra-vat (owner) OR a witness *discharges* the predicate
`p ko ko'` — you must DERIVE the knowledge to coordinate across a boundary. (`Dregg2.Authority.
boundary_law`.) Equivocation cannot manufacture the witness; the derivation is the legible move. -/
theorem coordination_needs_derivation
    {P KO W : Type*} [Dregg2.Laws.Verifiable P W]
    (owner : Label) (subjects : List Label) (pol' : Policy) (caps : Caps)
    (p : KO → KO → P) (ko ko' : KO)
    (refined : PasRefined pol' caps)
    (adm : owner ∈ subjects ∨ ∃ w : W, Dregg2.Laws.Discharged (p ko ko') w) :
    Integrity W owner subjects p ko ko' :=
  boundary_law owner subjects pol' caps p ko ko' refined adm

end Metatheory.PolisAuthGame
