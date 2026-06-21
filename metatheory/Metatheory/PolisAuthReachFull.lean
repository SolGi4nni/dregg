/-
# Metatheory.PolisAuthReachFull — viability across BOTH axes: authority caps OR derived knowledge.

The two grounded axes were separate: `PolisAuthReach` (reach a goal via held/derivable CAPS) and
`PolisAuthCoord` (cross-vat exercise needs a `Discharged` witness — derived KNOWLEDGE). This folds
them into ONE viability: an agent is viable for a goal iff it can reach it **by authority** (a cap it
holds/derives) OR **by knowledge** (discharging the predicate that guards the goal). Knowledge
coordination is now a *viability path*: a coalition that pools witnesses keeps an agent viable even
when its caps are revoked — and an equivocator (partial knowledge, no cap) is foreclosed, because it
cannot forge the discharge.

Grounded on the real `Dregg2.Laws.{Verifiable, Discharged}` (the `PolisAuthCoord` instance) and the
`Caps`/derivation reachability (`PolisAuthReach`). No `sorry`.
-/
import Metatheory.PolisAuthReach
import Metatheory.PolisAuthCoord

namespace Metatheory.PolisAuthReachFull

open Dregg2.Laws Metatheory.PolisAuthReach Metatheory.PolisAuthCoord

/-- The knowledge requirement guarding cross-vat exercise of an authority. In this model every goal
is guarded by `bothFacts` (you must derive both facts to exercise it across a boundary). -/
def guard (_ : Dregg2.Authority.Auth) : KnowReq := bothFacts

/-- **Viability across both axes.** `b` can reach `target` either by AUTHORITY — it holds/derives a
cap conferring `target` (`reachesB`, `PolisAuthReach`) — or by KNOWLEDGE — its witness `wit`
discharges the predicate `guard target` (`Discharged`, the cross-vat derivation). -/
def ReachesFull (target : Dregg2.Authority.Auth) (b : Dregg2.Authority.Label)
    (caps : Dregg2.Authority.Caps) (wit : FactSet) : Prop :=
  reachesB target b caps = true ∨ Discharged (guard target) wit

/-- **Authority path** — holding a deriving cap suffices, regardless of knowledge. -/
theorem reachesFull_via_caps : ReachesFull tgt B capsBoth witX :=
  Or.inl (by decide)

/-- **Knowledge path (coordination restores viability)** — with its caps fully revoked
(`capsDropAll`, no authority left), `b` is STILL viable because the coalition's pooled witness
`witCoalition` discharges the guard. Knowledge coordination is a viability path. -/
theorem reachesFull_via_knowledge : ReachesFull tgt B capsDropAll witCoalition :=
  Or.inr coalition_discharges_jointly

/-- **Equivocator foreclosed** — no cap AND only a partial witness (`witX`, which cannot discharge
`bothFacts`): `b` is NOT viable. You cannot forge the knowledge to stay reachable. -/
theorem equivocator_foreclosed : ¬ ReachesFull tgt B capsDropAll witX := by
  rintro (hc | hk)
  · exact absurd hc (by decide)
  · exact single_agent_cannot_X hk

/-- **The unification, in one line.** Viability is authority OR knowledge: the same agent in the same
caps-foreclosed state is viable WITH the coalition's pooled knowledge and foreclosed with only its
own partial knowledge. -/
theorem viability_is_authority_or_knowledge :
    ReachesFull tgt B capsDropAll witCoalition ∧ ¬ ReachesFull tgt B capsDropAll witX :=
  ⟨reachesFull_via_knowledge, equivocator_foreclosed⟩

end Metatheory.PolisAuthReachFull
