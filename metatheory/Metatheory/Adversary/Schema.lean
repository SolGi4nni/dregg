/-
# Metatheory.Adversary.Schema — `GovernedDynamics`: non-domination ≡ unfoolability, ONE theorem.

ELEVATED ASSURANCE, Pillar 2 — the DEEPER FUSION scoped in `Model.lean` §6.

`Model.lean` fused non-domination and light-client-unfoolability as a CONJUNCTION over one
`Adversary` (`non_domination_and_unfoolability`): two guarantees, one object, discharged by two
proofs. This module collapses the conjunction into ONE theorem. Both `polis_safety`
(`Polis/Polis.lean:102`) and `lightclient_unfoolable` (`Dregg2/Circuit/CircuitSoundness.lean:453`)
are instances of a single abstract schema — a dynamics driven by an adversarial control, with an
accept-predicate and a safety invariant, such that **for every control, an accepted outcome
satisfies the invariant.**

  * `GovernedProperty run accept invariant` — the abstract governance property: `∀ control,
    accept (run control) → invariant (run control)`. This is a REAL predicate on
    `(run, accept, invariant)`: it is FALSE for some tuples (`broken_dynamics_not_governed`), so
    it is NOT a `P → P` tautology — carrying it is content.
  * `GovernedDynamics` — a bundle of `(Control, Outcome, run, accept, invariant)` together with a
    proof that it satisfies `GovernedProperty`. An instance is exactly a dynamics no adversarial
    control can push from an accepted outcome to an invariant violation.
  * `governed_holds` — THE unified consumer: `∀ (D : GovernedDynamics) (c : D.Control), D.accept
    (D.run c) → D.invariant (D.run c)`. Non-domination and unfoolability are BOTH this one lemma,
    at `D := polisDynamics` and `D := circuitDynamics`.

DID THEY FIT CLEANLY? (the honest finding)
  * POLIS fits with NO distortion: `accept := True` (polis_safety holds at every reached state
    unconditionally), `invariant := safety at every step`, control `:= ctrl`. `polis_safety` IS
    the `holds` proof.
  * CIRCUIT fits, with the named realizability floor `WitnessDecodes` carried IN the accept
    predicate (`accept := verifyBatch = accept ∧ WitnessDecodes …`). This is NOT a distortion of
    the verifier-acceptance driver — `WitnessDecodes` is a per-forgery floor the apex ALREADY
    carries as an explicit hypothesis (a genuine prover committed to the kernels its trace
    publishes); folding it into "accepted (for soundness)" is faithful. `lightclient_unfoolable`
    IS the `holds` proof. The global floors (`hash`/`S`/`R`/`hCR`/`StarkSound`/`kstep`/`hrefines`)
    are fixed when the instance is built (they are NOT per-control).

So: non-domination ≡ light-client-unfoolability — literally applications of ONE lemma.

Kernel-clean: the two `holds` fields ARE the deployed proofs. `#assert_axioms` at the foot.
-/
import Metatheory.Adversary.Model

namespace Metatheory.Adversary

set_option linter.dupNamespace false

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecChainedState)
open Metatheory.Polis (SoundPolicy envAct traj polis_safety)

/-! ## §1. The abstract governance property + the schema. -/

/-- **`GovernedProperty run accept invariant`** — the abstract "invariant-under-control" property:
for EVERY control `c`, if the outcome `run c` is accepted, it satisfies the invariant. A REAL
predicate on `(run, accept, invariant)` — FALSE for some tuples (see
`broken_dynamics_not_governed`), so carrying it is genuine content, not a tautology. -/
def GovernedProperty {C : Type u} {O : Type v}
    (run : C → O) (accept : O → Prop) (invariant : O → Prop) : Prop :=
  ∀ c, accept (run c) → invariant (run c)

/-- **`GovernedDynamics` — the single abstract schema.** A dynamics driven by an adversarial
`Control`, producing an `Outcome`, with an `accept` predicate and a safety `invariant`, PROVED to
satisfy `GovernedProperty`. Both `polis_safety` and `lightclient_unfoolable` are instances. -/
structure GovernedDynamics where
  /-- the adversary's control surface. -/
  Control : Type u
  /-- what a control produces (a run result / a verified claim). -/
  Outcome : Type v
  /-- how a control drives the dynamics to an outcome. -/
  run : Control → Outcome
  /-- which outcomes are ACCEPTED / reached (the admission floor). -/
  accept : Outcome → Prop
  /-- the safety / genuineness the accepted outcome must satisfy. -/
  invariant : Outcome → Prop
  /-- **the governance proof** — no control drives an accepted outcome out of the invariant. -/
  holds : GovernedProperty run accept invariant

/-- **`governed_holds` — THE unified lemma.** For every governed dynamics `D` and every
adversarial control `c`, an accepted outcome satisfies the invariant. Non-domination AND
light-client-unfoolability are both THIS lemma, at two instances. -/
theorem governed_holds (D : GovernedDynamics) (c : D.Control)
    (h : D.accept (D.run c)) : D.invariant (D.run c) :=
  D.holds c h

/-! ## §2. Instance 1 — THE POLIS dynamics (non-domination). Fits with no distortion. -/

/-- **`polisDynamics`** — `polis_safety` as a `GovernedDynamics`. Control = the opaque operator
`ctrl`; the outcome is its whole trajectory; every step is "accepted" (`accept := True`); the
invariant is safety at EVERY step. `polis_safety` IS the `holds` proof. -/
noncomputable def polisDynamics {State Action : Type}
    (step : State → Action → State) (safe : State → Prop)
    (pol : State → Action → Prop) (shield : State → Action) (init : State)
    (sound : SoundPolicy step safe pol)
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init) : GovernedDynamics where
  Control := State → Action
  Outcome := Nat → State
  run ctrl := fun n => traj step (envAct pol shield ctrl) init n
  accept _ := True
  invariant r := ∀ n, safe (r n)
  holds ctrl _ := polis_safety sound shieldSafe initSafe ctrl

/-- **NON-DOMINATION, derived from the ONE lemma.** The operator `ctrl` can never push the
enveloped system out of the floor, at any step — as an application of `governed_holds` to
`polisDynamics`. This IS `polis_safety`, now factored through the shared schema. -/
theorem polis_nondomination_via_schema {State Action : Type}
    (step : State → Action → State) (safe : State → Prop)
    (pol : State → Action → Prop) (shield : State → Action) (init : State)
    (sound : SoundPolicy step safe pol)
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init) (ctrl : State → Action) (n : Nat) :
    safe (traj step (envAct pol shield ctrl) init n) :=
  governed_holds (polisDynamics step safe pol shield init sound shieldSafe initSafe) ctrl trivial n

/-! ## §3. Instance 2 — THE CIRCUIT dynamics (unfoolability). Fits, with `WitnessDecodes` in `accept`. -/

/-- **`circuitDynamics`** — `lightclient_unfoolable` as a `GovernedDynamics`. Control = the forged
`(pi, π)`; the outcome is that pair; `accept` = the verifier accepts AND the named realizability
floor `WitnessDecodes` holds; the invariant = a genuine kernel transition committing to `pi`.
`lightclient_unfoolable` IS the `holds` proof. The global floors are fixed here (not per-control). -/
noncomputable def circuitDynamics
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e)) : GovernedDynamics where
  Control := BatchPublicInputs × BatchProof
  Outcome := BatchPublicInputs × BatchProof
  run p := p
  accept p := verifyBatch (vkOfRegistry R) p.1 p.2 = Verdict.accept ∧ WitnessDecodes hash R S p.1
  invariant p := ∃ pre post : RecChainedState,
    StateDecode S p.1.toPublished pre post ∧
    kstep p.1.effect pre post ∧
    p.1.pre = S.commit pre.kernel p.1.turn ∧
    p.1.post = S.commit post.kernel p.1.turn
  holds p h := lightclient_unfoolable hash S R hCR kstep hrefines p.1 p.2 h.2 h.1

/-- **UNFOOLABILITY, derived from the ONE lemma.** A forged `(pi, π)` that verifies (with the
named floor) yields a genuine kernel step — as an application of `governed_holds` to
`circuitDynamics`. This IS `lightclient_unfoolable`, now factored through the SAME schema as
non-domination. -/
theorem unfoolability_via_schema
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  governed_holds (circuitDynamics hash S R hCR kstep hrefines) (pi, π) ⟨hacc, hwitdec⟩

/-! ## §4. The marquee — BOTH surfaces of one `Adversary`, governed by the ONE lemma.

`Model.lean`'s `non_domination_and_unfoolability` conjoined two proofs. Here BOTH conjuncts are
`governed_holds` applications — non-domination and unfoolability are the SAME theorem, at the
operator instance and the prover instance of one schema, over one `Adversary`. -/

/-- **`adversary_governed_uniformly`** — for every adversary `A`, its OPERATOR surface (`A.opCtrl`
→ `polisDynamics`) and its PROVER surface (`A.forgedPI`/`A.forgedProof` → `circuitDynamics`) are
BOTH bounded by the single `governed_holds` lemma. Non-domination ≡ unfoolability: one lemma, two
instances, one object. -/
theorem adversary_governed_uniformly {State Action : Type}
    (step : State → Action → State) (safe : State → Prop)
    (pol : State → Action → Prop) (shield : State → Action) (init : State)
    (sound : SoundPolicy step safe pol)
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init)
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (A : Adversary State Action)
    (hwitdec : WitnessDecodes hash R S A.forgedPI) :
    (∀ n, safe (traj step (envAct pol shield A.opCtrl) init n))
    ∧ (verifyBatch (vkOfRegistry R) A.forgedPI A.forgedProof = Verdict.accept →
        ∃ pre post : RecChainedState,
          StateDecode S A.forgedPI.toPublished pre post ∧
          kstep A.forgedPI.effect pre post ∧
          A.forgedPI.pre = S.commit pre.kernel A.forgedPI.turn ∧
          A.forgedPI.post = S.commit post.kernel A.forgedPI.turn) :=
  ⟨governed_holds (polisDynamics step safe pol shield init sound shieldSafe initSafe) A.opCtrl trivial,
   fun hacc =>
     governed_holds (circuitDynamics hash S R hCR kstep hrefines)
       (A.forgedPI, A.forgedProof) ⟨hacc, hwitdec⟩⟩

/-! ## §5. ANTI-VACUITY — the schema carries REAL content (it is NOT a `P → P`).

Two obligations: (POSITIVE) a non-trivial instance whose accept-set genuinely rejects and whose
invariant genuinely constrains; (NEGATIVE) a would-be dynamics that is NOT an instance — a tuple
for which `GovernedProperty` is FALSE, so no `GovernedDynamics` can be built with it. The negative
is what proves the `holds` field is real content: not every dynamics is governed. -/

/-- **(POSITIVE) a non-trivial governed instance.** Control = `Nat`, accept = "even" (genuinely
rejects odds), invariant = "≠ 1" (genuinely excludes `1`). `holds` is a REAL proof (even ⟹ ≠1),
not `fun _ _ => trivial`. Witnesses the schema has models with non-trivial accept AND constraining
invariant. -/
def evenNeqOneDynamics : GovernedDynamics where
  Control := Nat
  Outcome := Nat
  run n := n
  accept n := n % 2 = 0
  invariant n := n ≠ 1
  holds n h := by omega

/-- The positive instance's accept-set genuinely REJECTS (it is not `True`): `1` is not accepted. -/
theorem evenNeqOne_accept_nontrivial : ¬ evenNeqOneDynamics.accept (1 : Nat) := by
  show ¬ ((1 : Nat) % 2 = 0); decide

/-- The positive instance's invariant genuinely CONSTRAINS (it is not `True`): `1` violates it. -/
theorem evenNeqOne_invariant_nontrivial : ¬ evenNeqOneDynamics.invariant (1 : Nat) := by
  show ¬ ((1 : Nat) ≠ 1); decide

/-- **(NEGATIVE) not every dynamics is governed — the schema can FAIL.** For `run := id`, `accept
:= True`, `invariant := (· = true)` over `Bool`, `GovernedProperty` is FALSE (the control `false`
is accepted yet violates the invariant). Hence NO `GovernedDynamics` can carry these components:
the `holds` field is a genuine constraint, so `GovernedDynamics` is NOT a `P → P` tautology. -/
theorem broken_dynamics_not_governed :
    ¬ GovernedProperty (C := Bool) (O := Bool) id (fun _ => True) (fun b => b = true) := by
  intro h
  exact absurd (h false trivial) (by decide)

/-- **The negative, stated at the schema level.** The `holds` field of any `GovernedDynamics`
built over the broken `(Bool, id, True, ·=true)` tuple would have type `GovernedProperty id …` —
and THAT type is EMPTY. So no such instance can be constructed: `GovernedDynamics` genuinely
excludes broken dynamics, and its `holds` field is real content (anti-`P→P`). -/
theorem broken_holds_field_empty :
    IsEmpty (GovernedProperty (C := Bool) (O := Bool) id (fun _ => True) (fun b => b = true)) :=
  ⟨broken_dynamics_not_governed⟩

/-! ## §6. Axiom hygiene. -/

#print axioms governed_holds
#print axioms polis_nondomination_via_schema
#print axioms unfoolability_via_schema
#print axioms adversary_governed_uniformly
#print axioms broken_dynamics_not_governed

#assert_axioms governed_holds
#assert_axioms polis_nondomination_via_schema
#assert_axioms unfoolability_via_schema
#assert_axioms adversary_governed_uniformly
#assert_axioms evenNeqOne_accept_nontrivial
#assert_axioms evenNeqOne_invariant_nontrivial
#assert_axioms broken_dynamics_not_governed
#assert_axioms broken_holds_field_empty

/-!
The fusion, in the logic:

  ONE schema `GovernedDynamics` = (Control, run, accept, invariant, holds : GovernedProperty).
  ONE lemma `governed_holds` : ∀ D c, D.accept (D.run c) → D.invariant (D.run c).

    D := polisDynamics    ⟹  polis_nondomination_via_schema   (= polis_safety)
    D := circuitDynamics  ⟹  unfoolability_via_schema         (= lightclient_unfoolable)

  Non-domination and light-client-unfoolability are the SAME theorem, at two instances.
  `adversary_governed_uniformly` runs BOTH surfaces of one `Adversary` through it.

  FIT: polis with NO distortion (accept = True); circuit with the named realizability floor
  `WitnessDecodes` folded into `accept` (a per-forgery floor the apex already carries — faithful,
  not a distortion of the verifier-acceptance driver).

  ANTI-VACUITY: a non-trivial instance (`evenNeqOneDynamics`, accept rejects + invariant
  constrains) AND a NEGATIVE (`broken_dynamics_not_governed` / `no_governed_dynamics_for_broken`
  — a tuple that is NOT an instance). The schema is NOT a `P → P`.
-/

end Metatheory.Adversary
