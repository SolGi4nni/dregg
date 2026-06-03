/-
# Dregg2.Apps.EpistemicSheaf — the constellation as a sheaf of verifiers.

The constellation is a sheaf of verifiers: each satellite / operator is a local verifier with
partial knowledge, mutually distrusting. Collision-avoidance agreement is a global section (H⁰
content — everyone consistent); a fork / disagreement is an obstruction (H¹ content). Consensus
is reached without a trusted central authority.

This module instantiates two things, following the honesty discipline of `SHEAF-OF-VERIFIERS.md`:

  1. **Consensus = a global section (H⁰ content, proved).** A `Verify`-discharged clearance fact
     is distributed knowledge of the honest operators — via `honest_distributed_knows_discharged`.
     No Byzantine subset can forge it; the honest group's distributed knowledge exceeds any single
     member's.

  2. **The fork = witnessed non-gluing (obstruction, proved).** A finite sheaf-gluing of
     per-operator screen verdicts over a shared overlap: the sections glue iff they agree on the
     boundary; a Byzantine operator whose verdict disagrees fails to glue — no global section.

## Honesty label

**REAL (proved, `#assert_axioms`-clean):** the H⁰ content (honest distributed knowledge, inherited
from `Metatheory.EpistemicConsensus`, instantiated at the orbital screen); the finite gluing; the
witnessed non-gluing (the fork as a real failed hypothesis).

**ESTABLISHED (in the lit, cited, not claimed as a dregg theorem):** "consensus = H⁰" and "fork =
a sound H¹ obstruction detector" (SHEAF-OF-VERIFIERS §3). We use the content and cite the framing.

**OUT OF SCOPE (honestly not built):** the cohomology objects themselves (a Čech complex, `δ⁰`, an
`H⁰`/`H¹` group, a `Presheaf` instance). We have the gluing and the non-gluing; we do NOT name
them `H⁰`/`H¹` as objects. Calling this "cohomology" would let vocabulary stand in for an absent
coboundary — exactly what SHEAF-OF-VERIFIERS refuses, and so do we.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Keystones `#assert_axioms`-pinned.

NOTE ON SOURCING. The epistemic frame (`Frame`, `DistKnows`, `verified`, and the keystones) is
ported from `Metatheory/EpistemicConsensus.lean` (which formalizes Goubault–Kniazev–Ledent–
Rajsbaum, arXiv:2311.01351). Ported rather than imported to keep this module buildable under any
order. The proofs are identical to the cited source. CITATION: `Metatheory.EpistemicConsensus`.
-/
import Dregg2.Laws
import Dregg2.Tactics
import Dregg2.Apps.OrbitalScreen

namespace Dregg2.Apps.EpistemicSheaf

open Dregg2.Laws
open Dregg2.Apps.OrbitalScreen

/-! ## 0. The epistemic frame — ported from `Metatheory.EpistemicConsensus`.

A minimal faithful copy of the distributed-knowledge frame: worlds `Ω`, operators `ι`, each
operator's partial-knowledge relation `Indist`, a Byzantine subset, and the distributed knowledge
modality. Keystones are identical one-line proofs from the source. -/

/-- A `Claim` carries a verifier-side statement (the realizability core of the cited source). -/
structure Claim (P : Type) where
  /-- the predicate a discharging witness must satisfy -/
  stmt : P

/-- A claim **holds** iff some witness discharges it (constructive demonstrability). -/
def Holds {P W : Type} [Verifiable P W] (X : Claim P) : Prop :=
  ∃ w : W, Discharged (P := P) (W := W) X.stmt w

/-- An **epistemic frame with faulty operators** (ported `EpistemicConsensus.Frame`). -/
structure Frame (Ω ι : Type) where
  /-- the true orbital world -/
  actual : Ω
  /-- operator `i`'s partial-knowledge indistinguishability relation `∼ᵢ` -/
  Indist : ι → Ω → Ω → Prop
  /-- the Byzantine / faulty subset -/
  Faulty : ι → Prop

namespace Frame

variable {Ω ι : Type} (F : Frame Ω ι)

/-- A proposition is a world-set. -/
abbrev Prop' (Ω : Type) := Ω → Prop

/-- An operator is **honest** when not Byzantine. -/
def Honest (i : ι) : Prop := ¬ F.Faulty i

/-- **Distributed knowledge** of group `B`: `φ` holds at every world every member of `B`
confuses with `w` (the `D_B` clause; the group pools its partial perspectives). -/
def DistKnows (B : ι → Prop) (φ : Prop' Ω) (w : Ω) : Prop :=
  ∀ w', (∀ i, B i → F.Indist i w' w) → φ w'

/-- The world-independent proposition "witness `w₀` discharges `X`" (a freely-copyable
verifier-checkable certificate; holds at every world or none). -/
def verified {P W : Type} [Verifiable P W] (X : Claim P) (w₀ : W) : Prop' Ω :=
  fun _ => Discharged (P := P) (W := W) X.stmt w₀

/-- **Honest distributed knowledge of a discharged claim (PORTED keystone).** -/
theorem honest_distributed_knows_discharged {P W : Type} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hd : Discharged (P := P) (W := W) X.stmt w₀) :
    F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual :=
  fun _ _ => hd

/-- **An unrealizable claim is never honestly distributed-known (PORTED keystone).** -/
theorem no_dist_knowledge_of_unrealizable {P W : Type} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hnh : ¬ Holds (W := W) X)
    (hrefl : ∀ i, F.Honest i → F.Indist i F.actual F.actual) :
    ¬ F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual := by
  intro hdk
  exact hnh ⟨w₀, hdk F.actual (fun i hi => hrefl i hi)⟩

/-- **Honest distributed knowledge composes (PORTED keystone).** -/
theorem honest_dist_knowledge_composes {P W : Type} [Verifiable P W]
    (X Y : Claim P) (wx wy : W)
    (hX : F.DistKnows F.Honest (verified (Ω := Ω) X wx) F.actual)
    (hY : F.DistKnows F.Honest (verified (Ω := Ω) Y wy) F.actual) :
    F.DistKnows F.Honest
      (fun w => verified (Ω := Ω) X wx w ∧ verified (Ω := Ω) Y wy w) F.actual :=
  fun w' hall => ⟨hX w' hall, hY w' hall⟩

end Frame

/-! ## 1. The orbital clearance fact as a `Verifiable` predicate.

The shared statement every operator screens: "pair `(d0, v)` is clear over step `[0,T]` at
squared threshold `thrSq`." The predicate is the screening problem; the witness is the
(conservative) screen's own clearance certificate. This reuses the REAL continuous-time-sound
screen of `Dregg2.Apps.OrbitalScreen`. -/

/-- A **clearance claim**: the orbital screening problem for one pair over one step. -/
structure ClearanceProblem where
  /-- relative position at step start -/
  d0    : Vec3
  /-- relative velocity over the step -/
  v     : Vec3
  /-- step length -/
  T     : ℚ
  /-- squared conjunction threshold -/
  thrSq : ℚ
deriving Repr

/-- The witness an operator offers: a unit token meaning "I ran the conservative screen and it
returned clear." (The content is in the `Verify` below — the screen is RE-RUN by every checker;
the token is never trusted, exactly the verify-not-find discipline.) -/
abbrev ClearanceWitness := Unit

/-- **VERIFY (in the TCB): re-run the conservative orbital screen.** A clearance claim is
discharged iff `OrbitalScreen.screen` returns clear — the continuous-time-sound check. This is
the only thing any operator trusts; an operator's *assertion* of clearance is never trusted. -/
instance instVerifiableClearance : Verifiable ClearanceProblem ClearanceWitness where
  Verify := fun p _ => screen p.d0 p.v p.T p.thrSq

/-- The `Claim` form of a clearance problem (for the epistemic frame). -/
def clearanceClaim (p : ClearanceProblem) : Claim ClearanceProblem := ⟨p⟩

/-- **`clearance_discharged_iff_screen` (PROVED) — a clearance claim is discharged iff the
conservative screen says clear.** Pins the epistemic `Discharged` to the REAL physics: the fact
the operators come to know is exactly "the continuous-time screen is clear." -/
theorem clearance_discharged_iff_screen (p : ClearanceProblem) (w : ClearanceWitness) :
    Discharged (P := ClearanceProblem) (W := ClearanceWitness) p w
      ↔ screen p.d0 p.v p.T p.thrSq = true := Iff.rfl

/-! ## 2. CONSENSUS = a global section (H⁰ CONTENT) — distributed knowledge of clearance.

We instantiate `Metatheory.EpistemicConsensus` at the constellation: operators are agents, each
with an indistinguishability relation (partial knowledge of the orbital picture); the actual
world is the true orbital state. A `screen`-clear clearance fact is **distributed knowledge of
the honest operators** — consensus without a central cop. -/

/-- A **constellation frame**: operators `ι` over orbital worlds `Ω`, with each operator's
partial-knowledge relation and the Byzantine subset, reusing `EpistemicConsensus.Frame`. -/
abbrev Constellation (Ω ι : Type) := Frame Ω ι

variable {Ω ι : Type}

/-- **`consensus_on_clearance` — consensus = a global section (H⁰ content).** If the conservative
screen certifies a pair clear, "the maneuver clears the conjunction" is distributed knowledge of the
honest operators at the actual world. No central authority decides it; each operator's own `Verify`
settles it. `honest_distributed_knows_discharged` instantiated at the orbital screen. -/
theorem consensus_on_clearance (F : Constellation Ω ι) (p : ClearanceProblem)
    (hclear : screen p.d0 p.v p.T p.thrSq = true) :
    F.DistKnows F.Honest
      (Frame.verified (Ω := Ω) (clearanceClaim p) (() : ClearanceWitness)) F.actual :=
  F.honest_distributed_knows_discharged (clearanceClaim p) () hclear

/-- **`no_consensus_on_unscreened` — a fork cannot be forged (PROVED).** If NO witness
discharges the clearance claim (the screen does NOT certify the pair clear — `¬ Holds`), then
the honest operators do NOT have distributed knowledge of clearance, no matter what any
(possibly Byzantine) operator asserts. Consensus on safety cannot be manufactured for an
un-screened maneuver — the contrapositive of unforgeability, via `no_dist_knowledge_of_unrealizable`. -/
theorem no_consensus_on_unscreened (F : Constellation Ω ι) (p : ClearanceProblem)
    (hno : ¬ Holds (P := ClearanceProblem) (W := ClearanceWitness) (clearanceClaim p))
    (hrefl : ∀ i, F.Honest i → F.Indist i F.actual F.actual) :
    ¬ F.DistKnows F.Honest
        (Frame.verified (Ω := Ω) (clearanceClaim p) (() : ClearanceWitness)) F.actual :=
  F.no_dist_knowledge_of_unrealizable (clearanceClaim p) () hno hrefl

/-- **`consensus_composes` — agreement on two clearances composes (PROVED).** If the honest
operators have distributed knowledge that pair-X clears AND that pair-Y clears, they have it of
the conjunction — a re-screen after a fix (the chain-reaction beat) pools cleanly. The
UC-flavoured static composition fragment, instantiated. -/
theorem consensus_composes (F : Constellation Ω ι) (pX pY : ClearanceProblem)
    (hX : F.DistKnows F.Honest
            (Frame.verified (Ω := Ω) (clearanceClaim pX) (() : ClearanceWitness)) F.actual)
    (hY : F.DistKnows F.Honest
            (Frame.verified (Ω := Ω) (clearanceClaim pY) (() : ClearanceWitness)) F.actual) :
    F.DistKnows F.Honest
      (fun w => Frame.verified (Ω := Ω) (clearanceClaim pX) () w
              ∧ Frame.verified (Ω := Ω) (clearanceClaim pY) () w) F.actual :=
  F.honest_dist_knowledge_composes (clearanceClaim pX) (clearanceClaim pY) () () hX hY

/-! ## 3. THE FORK = witnessed NON-GLUING (the OBSTRUCTION).

The finite sheaf-gluing: a 2-operator overlap. Each operator screens its own sub-window of the
maneuver and reports a boundary commitment (the separation it sees at the shared overlap time).
The sections GLUE iff the two operators agree on the overlap. A buggy / Byzantine operator whose
boundary value DISAGREES fails to glue — no global section. This is the structural twin of
`proofForest_sound` + the `¬ chainLinked [node0, badNode]` non-gluing
(`SHEAF-OF-VERIFIERS §1.4, §2.1`), specialised to the orbital screen. -/

/-- A **local section**: one operator's screen verdict on its sub-window, plus the boundary
separation it observed at the shared overlap time (its restriction to the overlap). -/
structure LocalSection where
  /-- the operator's own screen verdict on its window -/
  verdict  : Bool
  /-- the separation the operator reports AT THE SHARED OVERLAP (its restriction map value) -/
  boundary : ℚ
deriving Repr, DecidableEq

/-- **The gluing condition (the sheaf condition).** Two local sections GLUE iff (i) each is
locally valid (its operator's screen accepted) AND (ii) they AGREE on the overlap (report the
same boundary separation). This is the `proofForest_sound` split: per-node valid ∧ `Linked`. -/
def Glues (a b : LocalSection) : Prop :=
  a.verdict = true ∧ b.verdict = true ∧ a.boundary = b.boundary

/-- **`glued_global_section` — the GLUING (PROVED).** When two operators' sections glue, there
is a sound GLOBAL verdict: the whole maneuver is locally-accepted by both AND they are
consistent on the overlap — a global section over the 2-operator cover. The conclusion is the
conjunction "both accepted ∧ consistent on the overlap," exactly the H⁰ content (a unique glued
verified history). -/
theorem glued_global_section (a b : LocalSection) (h : Glues a b) :
    a.verdict = true ∧ b.verdict = true ∧ a.boundary = b.boundary := h

/-! ### The gluing BITES — a witnessed non-gluing (the fork as a real failed hypothesis). -/

/-- Operator A's section: screened clear, reports boundary separation `5` at the overlap. -/
def opA : LocalSection := { verdict := true, boundary := 5 }

/-- An HONEST operator B that AGREES on the overlap (boundary `5`): the sections glue. -/
def opB_honest : LocalSection := { verdict := true, boundary := 5 }

/-- A BYZANTINE / buggy operator B that locally "verifies" (`verdict = true`) but reports a
DIFFERENT boundary separation (`99`) — its restriction map disagrees on the overlap. -/
def opB_byzantine : LocalSection := { verdict := true, boundary := 99 }

/-- **`honest_sections_glue` (PROVED) — the consistent family has a global section.** Operator A
and the honest operator B glue: both accepted, and they agree on the overlap (`5 = 5`). The
2-operator constellation reaches a global verified verdict with no central cop. -/
theorem honest_sections_glue : Glues opA opB_honest := by
  refine ⟨rfl, rfl, ?_⟩; rfl

/-- **`byzantine_section_does_not_glue` — the obstruction, witnessed.** Operator A and the Byzantine
operator B do not glue: each is locally valid (`verdict = true`), yet they disagree on the overlap
(`5 ≠ 99`) — the compatible-family hypothesis fails, so there is no global section. This is the fork
as a real failed gluing hypothesis (the H¹ content, cited, not claimed as an H¹ object). -/
theorem byzantine_section_does_not_glue : ¬ Glues opA opB_byzantine := by
  rintro ⟨_, _, hbnd⟩
  -- `opA.boundary = 5`, `opB_byzantine.boundary = 99`; `5 = 99` is false.
  exact absurd hbnd (by decide)

/-- **`fork_is_genuine` (PROVED) — the obstruction is non-vacuous.** Both operators' sections
are individually valid, yet they do not glue — so the non-gluing is a real phenomenon, not an
artifact of one section being invalid. (Each `verdict = true`; the obstruction lives ENTIRELY in
the overlap disagreement, exactly as the sheaf-of-verifiers picture requires.) -/
theorem fork_is_genuine :
    opA.verdict = true ∧ opB_byzantine.verdict = true ∧ ¬ Glues opA opB_byzantine :=
  ⟨rfl, rfl, byzantine_section_does_not_glue⟩

/-! ## 4. `#eval` witnesses — consensus and the fork, runnable. -/

-- The honest family GLUES (consensus / global section): both clear, overlap agrees.
#eval (decide (opA.verdict = true ∧ opB_honest.verdict = true ∧ opA.boundary = opB_honest.boundary))
                                                            -- true  (H⁰: a global section)
-- The Byzantine family does NOT glue (the fork / obstruction): valid locally, disagree on overlap.
#eval (decide (opA.verdict = true ∧ opB_byzantine.verdict = true
               ∧ opA.boundary = opB_byzantine.boundary))    -- false (overlap disagreement ⇒ no glue)
-- Each operator is individually valid — the obstruction is PURELY the overlap disagreement:
#eval opA.verdict                                           -- true
#eval opB_byzantine.verdict                                 -- true  (locally fine …)
#eval (opA.boundary == opB_byzantine.boundary)              -- false (… but disagrees: the fork)
-- A clearance claim, discharged by the REAL conservative screen (clear pair):
#eval screen (⟨8,0,0⟩ : Vec3) (⟨0,3,0⟩ : Vec3) 10 25        -- true  (the H⁰ fact the operators know)

/-! ## 5. Axiom hygiene. -/

#assert_axioms clearance_discharged_iff_screen
#assert_axioms consensus_on_clearance
#assert_axioms no_consensus_on_unscreened
#assert_axioms consensus_composes
#assert_axioms glued_global_section
#assert_axioms honest_sections_glue
#assert_axioms byzantine_section_does_not_glue
#assert_axioms fork_is_genuine

end Dregg2.Apps.EpistemicSheaf
