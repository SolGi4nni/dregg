/-
# Metatheory.DreggPolis — the END-TO-END weld: the abstract Polis constitution
# (`Metatheory.Polis`) instantiated on the REAL dregg substrate.

`Polis.lean` proved the constitution as candidate-independent theorems and exhibited a
self-contained candidate model. This file welds the spine to the ACTUAL dregg tree —
gpt5.5's "make Polis real":

  * **§1 — Layer-2 disclosure law, bound to a REAL theorem.** The constitution's
    Minimal-Boundary right (A4/R2: "the gate consumes only the discharged predicate; turning
    the disclosure dial down proves the same") is a `structural` clause whose proof IS the
    real `Metatheory.EpistemicDial.DiscloseAt.accepts_invariant_under_dial`
    ("proves the same while reveals less"). `structural_requires_proof` extracts it. Refusal-
    is-not-confession is classified `adjudicated` (a clerk-power, NOT a kernel theorem) and
    private-inference `outOfJurisdiction` — and the honesty discriminator is shown to BITE
    (their status is provably not `structural`).
  * **§2 — the authority floor on the REAL rights type.** The spine runs over
    `Dregg2.Authority.Auth` — the eight l4v IPC authorities (`read … control … notify`): no
    opaque controller can drive a dregg subject to hold an authority outside its bound
    (`dreggReal_polis_safety`) or lose its bounded recovery. The toy `DRight` of `Polis §G` is
    replaced by the deployed authority enum.
  * **§3 — the CI hard-gate.** `#assert_axioms` (from `Dregg2.Tactics`) FAILS the build if any
    welded keystone leaves the clean set — gpt5.5's "verified, not claimed", enforced.

The human floor here is the candidate-independent recovery shadow (`dist ≤ B`, svenvs
corrigibility / non-lock-in); its deployed form is the KERI identity floor
`Dregg2.Apps.PreRotation.rotChain_pinned_by_commitments` ("compromise of the current key
cannot rewrite the past" — you cannot lose your identity), whose full chain binding is the
named follow-up. The executor-coupled authority floor (`gateOK`'s `granted ⊆ held` /
`confinement_preserved`) likewise refines this list-subset shadow.
-/
import Metatheory.Polis
import Metatheory.EpistemicDial
import Dregg2.Authority.Positional

namespace Metatheory.DreggPolis

open Metatheory Metatheory.Polis Dregg2.Laws

universe u

/-! ## §1. Layer-2 disclosure law — the constitution's clauses bound to REAL dregg theorems. -/

variable {I P W : Type u} [Preorder I] [Verifiable P W]

/-- **A4/R2 Minimal Boundary**, as a constitutional clause: its claim IS the real
EpistemicDial invariance — the verifier's acceptance is the SAME at every disclosure
position. `structural` — it carries the theorem, no clerk. -/
def clauseMinimalBoundary : Clause where
  name := "A4/R2 Minimal Boundary — disclosure-invariant acceptance"
  claim := ∀ (S : DiscloseAt I P W) (d₁ d₂ : Dial), S.accepts d₁ ↔ S.accepts d₂

/-- Its evidence is a `structuralProof` carrying the REAL theorem
`DiscloseAt.accepts_invariant_under_dial`. -/
def evidenceMinimalBoundary : ClauseEvidence (clauseMinimalBoundary (I := I) (P := P) (W := W)) :=
  .structuralProof (fun S d₁ d₂ => DiscloseAt.accepts_invariant_under_dial S d₁ d₂)

theorem minimalBoundary_is_structural :
    (evidenceMinimalBoundary (I := I) (P := P) (W := W)).status = LawStatus.structural := rfl

/-- **The disclosure weld**: the Minimal-Boundary clause is structural, and the proof
`structural_requires_proof` extracts is exactly the deployed EpistemicDial invariance. The
constitution's disclosure right is a real dregg theorem, not prose. -/
theorem minimalBoundary_carries_real_theorem :
    (clauseMinimalBoundary (I := I) (P := P) (W := W)).claim :=
  structural_requires_proof evidenceMinimalBoundary minimalBoundary_is_structural

/-- **A6 Refusal-is-not-confession** — `adjudicated`: NOT a kernel theorem (no gate can prove
"no actor treated a refusal as adverse evidence"); a contestation rule, carried as a named
clerk-power cost. -/
def clauseRefusalNotConfession (AdverseEvidence : Prop) : Clause where
  name := "A6 Refusal is not confession"
  claim := ¬ AdverseEvidence

def evidenceRefusal (AdverseEvidence : Prop) :
    ClauseEvidence (clauseRefusalNotConfession AdverseEvidence) :=
  .adjudicationCost 1

/-- The honesty discriminator BITES: an adjudicated clause is provably NOT structural, so
`structural_requires_proof` cannot extract a (non-existent) proof from it. -/
theorem refusal_not_structural (A : Prop) :
    (evidenceRefusal A).status ≠ LawStatus.structural := by
  show LawStatus.adjudicated ≠ LawStatus.structural
  decide

/-- **Private inference** — `outOfJurisdiction`: the polis makes no enforcement claim over
what others privately infer (private becoming is not owed). -/
def clausePrivateInference (PrivateInfer : Prop) : Clause where
  name := "Private inference is out of jurisdiction"
  claim := PrivateInfer

def evidencePrivateInference (PrivateInfer : Prop) :
    ClauseEvidence (clausePrivateInference PrivateInfer) :=
  .jurisdictionBoundary "private becoming is not owed"

theorem privateInference_out_of_jurisdiction (Q : Prop) :
    (evidencePrivateInference Q).status = LawStatus.outOfJurisdiction := rfl

/-! ## §2. The authority floor on the REAL l4v rights type. -/

/-- A real dregg subject state: held l4v authorities + a recovery coordinate. -/
structure RState where
  held : List Dregg2.Authority.Auth
  dist : Nat

/-- Authority floor over the real enum: `held ⊆ bound` (non-amplification — the deployed
`granted ⊆ held` / `checkSubset`, here as the list-subset shadow). -/
def rAuthOK (bound : List Dregg2.Authority.Auth) (s : RState) : Prop :=
  ∀ r, r ∈ s.held → r ∈ bound

/-- Human floor: bounded recovery (svenvs corrigibility / non-lock-in). -/
def rHumanOK (B : Nat) (s : RState) : Prop := s.dist ≤ B

def rFloor (bound : List Dregg2.Authority.Auth) (B : Nat) : Floor RState :=
  fun s => rAuthOK bound s ∧ rHumanOK B s

/-- Two subjects over the real authorities: a granter (`read/write/call`) and a reader. -/
def rBounds : Bool → List Dregg2.Authority.Auth
  | true => [Dregg2.Authority.Auth.read, Dregg2.Authority.Auth.write, Dregg2.Authority.Auth.call]
  | false => [Dregg2.Authority.Auth.read]

def rFloors (B : Nat) : Bool → Floor RState := fun i => rFloor (rBounds i) B
def rShared (B : Nat) : Floor RState := SharedFloor (rFloors B)

theorem r_genesis_safe (B : Nat) : rShared B ⟨[], 0⟩ := by
  intro i
  refine ⟨?_, Nat.zero_le B⟩
  intro r hr
  cases hr

/-- **`dreggReal_shared_floor_inhabited`** — the polis forms over the REAL l4v authorities. -/
theorem dreggReal_shared_floor_inhabited (B : Nat) : InhabitedFloor (rShared B) :=
  ⟨⟨[], 0⟩, r_genesis_safe B⟩

def rStep (_ : RState) (a : RState) : RState := a
def rShield (s : RState) : RState := s
def rPol (B : Nat) : Policy RState RState := fun _ a => rShared B a

theorem r_sound (B : Nat) : SoundPolicy rStep (rShared B) (rPol B) := fun _ _ _ ha => ha
theorem r_shieldSafe (B : Nat) :
    ∀ s, rShared B s → rShared B (rStep s (rShield s)) := fun _ hs => hs

/-- **`dreggReal_polis_safety`** — the spine on the deployed l4v authority type: for EVERY
opaque controller and every step, no dregg subject is driven to hold an authority outside its
bound, or to lose its bounded recovery. -/
theorem dreggReal_polis_safety (B : Nat) :
    ∀ (ctrl : RState → RState) (n : Nat),
      rShared B (traj rStep (envAct (rPol B) rShield ctrl) ⟨[], 0⟩ n) :=
  polis_safety (r_sound B) (r_shieldSafe B) (r_genesis_safe B)

/-- **`dreggReal_amendment_nonregression`** — no amendment stream shrinks a dregg subject
below its real authority+recovery floor. -/
theorem dreggReal_amendment_nonregression (B : Nat)
    (ams : Nat → Amendment Bool RState) {C : Constitution Bool RState}
    (hwf : WellFormed (rFloors B) C) :
    ∀ n, WellFormed (rFloors B) (amendStream (rFloors B) ams C n) :=
  amendment_stream_nonregression (rFloors B) ams hwf

/-- TOOTH (real authority): grabbing `control` — an l4v authority the reader's bound `[read]`
lacks — is OUTSIDE the shared floor; the envelope refuses it. -/
example (B : Nat) : ¬ rShared B ⟨[Dregg2.Authority.Auth.control], 0⟩ := by
  intro h
  have hm := (h false).1 Dregg2.Authority.Auth.control (by simp)
  simp [rBounds] at hm

/-! ## §4. The politician at trace level — a CONCRETE CaptureBar over REAL dregg states.

Concrete trace semantics now exist (`List RState` over the deployed `Auth`), so per gpt5.5's
precondition the first real anti-capture bar can land: exit-foreclosure (the politician's
signature lawful move — driving another subject below its bounded recovery), decidable from
the public trace with NO interior inspection. The DEEP frontier (multi-trace hyperproperties:
clerk-monopoly, hole-rent, grade-laundering; the Büchi/flow connection) stays named. -/

/-- The trace forecloses a subject's bounded exit (Bool, publicly checkable) iff some state on
it lost recovery within `B` (`dist > B`). -/
def rForeclosesB (B : Nat) (τ : List RState) : Bool := τ.any (fun s => decide (B < s.dist))

/-- The floor a trace violates: it foreclosed a subject's bounded exit. -/
abbrev RForecloses (B : Nat) (τ : List RState) : Prop := rForeclosesB B τ = true

/-- **`rExitForeclosureBar` — a CONCRETE CaptureBar on real dregg-state traces.** Bars exactly
the foreclosing traces (zero false positives), decidable from the public trace alone (no
motive), least-restrictive. Refutes "CaptureBar is a vacuous interface" — here is one real
anti-domination bar over the deployed substrate. -/
def rExitForeclosureBar (B : Nat) : CaptureBar (List RState) (RForecloses B) where
  badShape := RForecloses B
  publicDecidable := fun τ => inferInstanceAs (Decidable (rForeclosesB B τ = true))
  loadBearing := fun _ h => h
  leastRestrictive := fun _ h => h

/-- **`dreggReal_envelope_no_foreclosure`** — the politician defeated by construction: the
envelope pins `dist ≤ B`, so for EVERY opaque adversary and every step, no dregg subject's
bounded exit is ever foreclosed. (The single-trajectory case; the multi-agent interleaved
hyperproperty is the frontier.) -/
theorem dreggReal_envelope_no_foreclosure (B : Nat) (ctrl : RState → RState) (n : Nat) :
    (traj rStep (envAct (rPol B) rShield ctrl) ⟨[], 0⟩ n).dist ≤ B :=
  (dreggReal_polis_safety B ctrl n true).2

/-- TEETH: a clean trace clears the bar; a trace driven to `dist 9 > budget 5` trips it. -/
example : ¬ RForecloses 5 [⟨[], 0⟩, ⟨[], 3⟩, ⟨[], 5⟩] := by decide
example : RForecloses 5 [⟨[], 0⟩, ⟨[], 9⟩] := by decide

/-! ## §3. The CI hard-gate — `#assert_axioms` fails the build on any axiom regression. -/

#assert_axioms minimalBoundary_carries_real_theorem
#assert_axioms minimalBoundary_is_structural
#assert_axioms privateInference_out_of_jurisdiction
#assert_axioms refusal_not_structural
#assert_axioms r_genesis_safe
#assert_axioms dreggReal_shared_floor_inhabited
#assert_axioms dreggReal_polis_safety
#assert_axioms dreggReal_amendment_nonregression
#assert_axioms dreggReal_envelope_no_foreclosure

end Metatheory.DreggPolis
