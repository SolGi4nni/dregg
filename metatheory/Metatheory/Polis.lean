/-
# Metatheory.Polis — polisware as multi-agent svenvs (the constitution, as a theorem).

Distilled from the dregg ⋈ svenvs ⋈ Lacan synthesis ("Polisware Basic Law: the cut, the
trace, and the remainder"). Held to the svenvs bar — `∀`-opaque inhabitants, a
*least-restrictive* floor, and an honestly-NAMED (not faked) frontier:

  * **§A — STATE-INVARIANT CORE (provable now).** The direct lift of svenvs
    `liberty/libertyScript.sml` to many subjects. The enveloped system keeps the SHARED
    floor for EVERY tuple of opaque controllers (`polis_safety`, quantified over `ctrl`,
    never inspecting it — "verify the cage, not the animal"); the envelope is the LEAST
    restrictive sound one (`envelope_least_restrictive`); and a subject's floor is touched
    only when its own action would actually break it (`override_only_unsafe`).
  * **§B — THE CONSTITUTIONAL SOUNDNESS LEDGER.** Every clause is `structural`
    (a theorem; no clerk), `adjudicated` (needs a contestation process — a named
    clerk-power), or `outOfJurisdiction` (no enforcement claim). The honesty discriminator
    is a TYPE: a clause tagged `structural` must carry its proof
    (`structural_requires_proof`). You cannot call a prohibition structural for free.
  * **§C — MONOTONE AMENDMENT (the new theorem family).** The lift of svenvs
    `recovUpgrade`'s `self_modification_never_weakens_recoverability` /
    `unrecoverable_swap_is_inert` to the constitution itself. The law is self-amendable by
    an unbounded adversarial stream, but no amendment may lower any subject's *frozen,
    subject-owned* minimum floor: a regressive amendment is INERT
    (`regressive_amendment_inert`), and along ANY amendment stream every subject's frozen
    minimum is preserved (`amendment_stream_nonregression`). This closes the meta-regress
    (who governs the capture-floor?) with NO amendment-sovereign — legitimacy is not proven
    *just* (not kernel-provable) but proven *never-weakened* (constitutional non-regression).
  * **§D — MEMBERSHIP / SCHISM.** A polis exists only where subjects' exported floors have
    a NON-EMPTY meet (`disjoint_floors_no_polis`); the edge of the polis is the empty
    intersection, not a wall. The meet is of *exported floors*, never of interiors.
  * **§E — THE TRACE-HYPERPROPERTY FRONTIER (named, NOT faked).** The politician lives in
    the *trace*, not the transition. `CaptureBar` is the INTERFACE a sound anti-capture bar
    must inhabit (public-decidable, load-bearing, least-restrictive); constructing one for
    real temporal capture is OPEN research (connect to `FlowRefine.decideRefines` / the
    Büchi game). No instance is shipped — red is honest.

Pure Lean 4 core; no `import`, no `sorry`, no `:= True` load-bearing. Keystone axiom use is
printed below (`#print axioms`) — kernel-clean (`propext`/`Classical.choice`/`Quot.sound`).
-/

namespace Metatheory.Polis

/-!
## Theorem map (philosophy → theorem name) — so this is read as a constitution, not a bag
of abstract predicates. (Full one-pager: `docs/POLIS.md`.)

  "Verify the cage, not the animal":      `polis_safety`  (∀ ctrl — the gate cannot
                                          psychometrically classify the inhabitant)
  "Least restrictive — every bar bears":  `envelope_least_restrictive` / `override_only_unsafe`
  "Structural means theorem-bearing":     `structural_requires_proof`
  "Legitimacy as non-regression":         `amendment_stream_nonregression` /
                                          `regressive_amendment_inert`
  "Empty meet is schism":                 `disjoint_floors_no_polis`
  "Non-vacuous on the substrate":         `dregg_shared_floor_inhabited`
  "Politician lives in traces":           `CaptureBar` (+ `DreggPolis.rExitForeclosureBar`)

Real-substrate welds live in `Metatheory.DreggPolis` (disclosure = EpistemicDial; authority =
l4v `Auth`) and `Metatheory.PolisNonConfusion` (non-confusion + unfoolability, deployed pins).
-/

attribute [local instance] Classical.propDecidable

variable {State Action Agent Trace : Type}

/-! ## §A. The state-invariant core — multi-agent `liberty`, lifted. -/

/-- A **floor**: the protection predicate — the states acceptable to a subject. A reachable
state must satisfy the (shared) floor. -/
abbrev Floor (State : Type) := State → Prop

/-- A **policy**: which actions a state permits. -/
abbrev Policy (State Action : Type) := State → Action → Prop

/-- The **shared floor** of a family of subject floors: a state is acceptable iff it is
acceptable to EVERY subject (the meet / intersection — of *exported* floors, never of
interiors). -/
def SharedFloor (floors : Agent → Floor State) : Floor State :=
  fun s => ∀ i, floors i s

/-- A policy is **sound** for `safe` under `step` when, from a safe state, every permitted
action preserves safety. (svenvs `sound_policy`.) -/
def SoundPolicy (step : State → Action → State) (safe : Floor State)
    (pol : Policy State Action) : Prop :=
  ∀ s a, safe s → pol s a → safe (step s a)

/-- The **enveloped action**: pass the controller's action through iff the policy permits
it, else fall back to the shield. The controller `ctrl` is opaque — never inspected. -/
noncomputable def envAct (pol : Policy State Action) (shield : State → Action)
    (ctrl : State → Action) (s : State) : Action :=
  if pol s (ctrl s) then ctrl s else shield s

/-- The trajectory of the enveloped system from `init`. -/
def traj (step : State → Action → State) (act : State → Action) (init : State) : Nat → State
  | 0 => init
  | n + 1 => step (traj step act init n) (act (traj step act init n))

/-- **`polis_safety` — verify the cage, not the animal.** For a sound policy, a safe
shield, and a safe start, the enveloped system keeps the floor at EVERY step, for EVERY
controller. The controller is universally quantified and never inspected: no psychometric
classification of the inhabitant can be load-bearing for the guarantee. (svenvs
`safety_preservation`, multi-agent — instantiate `safe := SharedFloor floors`.) -/
theorem polis_safety
    {step : State → Action → State} {safe : Floor State}
    {pol : Policy State Action} {shield : State → Action} {init : State}
    (sound : SoundPolicy step safe pol)
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init) :
    ∀ (ctrl : State → Action) (n : Nat),
      safe (traj step (envAct pol shield ctrl) init n) := by
  intro ctrl
  have step1 : ∀ s, safe s → safe (step s (envAct pol shield ctrl s)) := by
    intro s hs
    unfold envAct
    by_cases hp : pol s (ctrl s)
    · rw [if_pos hp]; exact sound s (ctrl s) hs hp
    · rw [if_neg hp]; exact shieldSafe s hs
  intro n
  induction n with
  | zero => exact initSafe
  | succ k ih => exact step1 _ ih

/-- The guarantee is identical for ALL inhabitants — the "inference is inert" fact made
structural: there is no place in the enforcement function to put a shadow of the
controller. -/
theorem polis_envelope_ctrl_blind
    {step : State → Action → State} {safe : Floor State}
    {pol : Policy State Action} {shield : State → Action} {init : State}
    (sound : SoundPolicy step safe pol)
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init) (ctrl₁ ctrl₂ : State → Action) :
    (∀ n, safe (traj step (envAct pol shield ctrl₁) init n))
      ∧ (∀ n, safe (traj step (envAct pol shield ctrl₂) init n)) :=
  ⟨polis_safety sound shieldSafe initSafe ctrl₁,
   polis_safety sound shieldSafe initSafe ctrl₂⟩

/-- The **maximal sound policy**: from a safe state, permit exactly the safety-preserving
actions. The weakest sound policy — the largest interior a sound cage can have. -/
def maxpol (step : State → Action → State) (safe : Floor State) : Policy State Action :=
  fun s a => safe s → safe (step s a)

theorem maxpol_sound (step : State → Action → State) (safe : Floor State) :
    SoundPolicy step safe (maxpol step safe) := by
  intro s a hs hm; exact hm hs

/-- Maximality: every sound policy is a restriction of `maxpol`. -/
theorem maxpol_greatest {step : State → Action → State} {safe : Floor State}
    {pol : Policy State Action} (h : SoundPolicy step safe pol) :
    ∀ s a, pol s a → maxpol step safe s a := by
  intro s a hpol hs; exact h s a hs hpol

/-- **`envelope_least_restrictive`** — every bar is load-bearing. Any policy that, from a
safe state, permits an action `maxpol` forbids is UNSOUND: it admits a transition breaking
the floor for some inhabitant. (svenvs `envelope_is_least_restrictive`.) -/
theorem envelope_least_restrictive {step : State → Action → State} {safe : Floor State}
    {q : Policy State Action} {s : State} {a : Action}
    (_hs : safe s) (hq : q s a) (hbar : ¬ maxpol step safe s a) :
    ¬ SoundPolicy step safe q := by
  intro hsound
  exact hbar (fun hs' => hsound s a hs' hq)

/-- The envelope never overrides an action that was already safe — no starvation. -/
theorem override_never_safe {step : State → Action → State} {safe : Floor State}
    {shield ctrl : State → Action} {s : State}
    (hsafe : safe (step s (ctrl s))) :
    envAct (maxpol step safe) shield ctrl s = ctrl s := by
  have hm : maxpol step safe s (ctrl s) := fun _ => hsafe
  unfold envAct
  rw [if_pos hm]

/-- And the envelope acts ONLY on actions that would actually break the floor from a safe
state. (Pairs with the cartpole's executed chaos demonstrations.) -/
theorem override_only_unsafe {step : State → Action → State} {safe : Floor State}
    {shield ctrl : State → Action} {s : State}
    (h : envAct (maxpol step safe) shield ctrl s ≠ ctrl s) :
    safe s ∧ ¬ safe (step s (ctrl s)) := by
  unfold envAct at h
  by_cases hp : maxpol step safe s (ctrl s)
  · rw [if_pos hp] at h; exact absurd rfl h
  · have hnotimp : ¬ (safe s → safe (step s (ctrl s))) := hp
    refine ⟨Classical.byContradiction (fun hns => hnotimp (fun hs => absurd hs hns)), ?_⟩
    intro hq
    exact hnotimp (fun _ => hq)

/-- **`maxpol_envelope_safe`** — with the MAXIMALLY permissive sound policy the full
floor-preservation guarantee still holds for every inhabitant: maximal autonomy and safety
simultaneously, no trade-off. -/
theorem maxpol_envelope_safe {step : State → Action → State} {safe : Floor State}
    {shield : State → Action} {init : State}
    (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init) :
    ∀ ctrl n, safe (traj step (envAct (maxpol step safe) shield ctrl) init n) :=
  polis_safety (maxpol_sound step safe) shieldSafe initSafe

/-! ## §B. The constitutional soundness ledger. -/

/-- A clause is enforced by construction (`structural`), by a contestation process that
creates clerk-power (`adjudicated`), or not at all (`outOfJurisdiction`). -/
inductive LawStatus where
  | structural
  | adjudicated
  | outOfJurisdiction
deriving DecidableEq, Repr

/-- A constitutional clause: a named claim. -/
structure Clause where
  name : String
  claim : Prop

/-- **Evidence for a clause** — the honesty discriminator as a type. A `structural` clause
MUST carry a proof of its claim (no clerk inspects anything). An `adjudicated` clause
carries only a *named clerk-power cost* — explicitly NOT a proof of the claim. An
`outOfJurisdiction` clause carries a boundary reason and makes NO enforcement claim. -/
inductive ClauseEvidence (c : Clause) : Type where
  | structuralProof (proof : c.claim) : ClauseEvidence c
  | adjudicationCost (clerkCost : Nat) : ClauseEvidence c
  | jurisdictionBoundary (reason : String) : ClauseEvidence c

/-- The status a piece of evidence claims. -/
def ClauseEvidence.status {c : Clause} : ClauseEvidence c → LawStatus
  | .structuralProof _ => .structural
  | .adjudicationCost _ => .adjudicated
  | .jurisdictionBoundary _ => .outOfJurisdiction

/-- **`structural_requires_proof`** — the honesty bar. If a clause's evidence is tagged
`structural`, it actually carries a proof of the clause's claim. You cannot call a
prohibition structural without paying a theorem (the metatheoretic upgrade: convert MUSTs
into universal nondependence, or charge the clerk-power explicitly). -/
theorem structural_requires_proof {c : Clause} (e : ClauseEvidence c)
    (h : e.status = LawStatus.structural) : c.claim := by
  cases e with
  | structuralProof p => exact p
  | adjudicationCost _ => simp only [ClauseEvidence.status] at h; exact absurd h (by decide)
  | jurisdictionBoundary _ => simp only [ClauseEvidence.status] at h; exact absurd h (by decide)

/-! ## §C. Monotone amendment — the meta-regress closed without a sovereign. -/

/-- `G` **protects at least** `F`: every state acceptable to `G` is acceptable to `F`. `G`
may add constraints (be more protective) but cannot drop any of `F`'s, so enforcing `G`
guarantees `F`'s protection. (Comment-test: `ProtectsAtLeast new old` ⇒ any state
satisfying `new` satisfies `old`; `new` may impose more, never less.) -/
def ProtectsAtLeast (G F : Floor State) : Prop := ∀ s, G s → F s

theorem ProtectsAtLeast.rfl' (F : Floor State) : ProtectsAtLeast F F := fun _ h => h

theorem ProtectsAtLeast.trans' {F G H : Floor State}
    (h1 : ProtectsAtLeast G F) (h2 : ProtectsAtLeast H G) : ProtectsAtLeast H F :=
  fun s h => h1 s (h2 s h)

/-- A **constitution**: the active (currently-enforced) floor for each subject. The
subject-owned *frozen minimum* is NOT here — it is a fixed parameter the constitution
cannot touch (svenvs: `home` is frozen and subject-owned; only the *mechanism* above it is
mutable, by a separate subject-owned ceremony, never by ordinary amendment). -/
structure Constitution (Agent State : Type) where
  activeFloor : Agent → Floor State

/-- `C` is **well-formed** w.r.t. the frozen minima when every active floor protects at
least its subject's frozen minimum. -/
def WellFormed (frozenMin : Agent → Floor State) (C : Constitution Agent State) : Prop :=
  ∀ i, ProtectsAtLeast (C.activeFloor i) (frozenMin i)

/-- An **amendment**: any transform of the constitution (adversarial allowed). -/
abbrev Amendment (Agent State : Type) := Constitution Agent State → Constitution Agent State

/-- An amendment is **non-regressive** at `C` when its result still protects every
subject's frozen minimum. -/
def NonRegressive (frozenMin : Agent → Floor State) (am : Amendment Agent State)
    (C : Constitution Agent State) : Prop :=
  ∀ i, ProtectsAtLeast ((am C).activeFloor i) (frozenMin i)

/-- The **guarded** application: admit the amendment iff it is non-regressive; otherwise it
is INERT (the constitution is unchanged). The polis lift of svenvs's
`unrecoverable_swap_is_inert`. -/
noncomputable def guardedApply (frozenMin : Agent → Floor State)
    (am : Amendment Agent State) (C : Constitution Agent State) : Constitution Agent State :=
  if NonRegressive frozenMin am C then am C else C

/-- **`regressive_amendment_inert`** — a regressive amendment changes nothing (the door
cannot be closed behind anyone). -/
theorem regressive_amendment_inert (frozenMin : Agent → Floor State)
    (am : Amendment Agent State) (C : Constitution Agent State)
    (h : ¬ NonRegressive frozenMin am C) :
    guardedApply frozenMin am C = C := by
  unfold guardedApply; rw [if_neg h]

/-- The guard preserves well-formedness. -/
theorem guardedApply_wellFormed (frozenMin : Agent → Floor State)
    (am : Amendment Agent State) {C : Constitution Agent State}
    (hwf : WellFormed frozenMin C) :
    WellFormed frozenMin (guardedApply frozenMin am C) := by
  unfold guardedApply
  by_cases h : NonRegressive frozenMin am C
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hwf

/-- Iterate a guarded-amendment stream. -/
noncomputable def amendStream (frozenMin : Agent → Floor State) (ams : Nat → Amendment Agent State)
    (C : Constitution Agent State) : Nat → Constitution Agent State
  | 0 => C
  | n + 1 => guardedApply frozenMin (ams n) (amendStream frozenMin ams C n)

/-- **`amendment_stream_nonregression`** (svenvs
`self_modification_never_weakens_recoverability`, lifted) — along ANY guarded amendment
stream, adversarial or not, every subject's frozen minimum floor is preserved forever.
Constitutional non-regression: the door never legally closes behind any participant.
Legitimacy is not proven *just* (not kernel-provable); it is proven *never-weakened*. -/
theorem amendment_stream_nonregression (frozenMin : Agent → Floor State)
    (ams : Nat → Amendment Agent State) {C : Constitution Agent State}
    (hwf : WellFormed frozenMin C) :
    ∀ n, WellFormed frozenMin (amendStream frozenMin ams C n) := by
  intro n
  induction n with
  | zero => exact hwf
  | succ k ih => exact guardedApply_wellFormed frozenMin (ams k) ih

/-- Spelled out at a single subject: no amendment path ever drops below the frozen floor. -/
theorem amendment_stream_preserves_min (frozenMin : Agent → Floor State)
    (ams : Nat → Amendment Agent State) {C : Constitution Agent State}
    (hwf : WellFormed frozenMin C) (n : Nat) (i : Agent) :
    ProtectsAtLeast ((amendStream frozenMin ams C n).activeFloor i) (frozenMin i) :=
  amendment_stream_nonregression frozenMin ams hwf n i

/-! ## §D. Membership / schism — the polis edge is the empty meet. -/

/-- A floor is inhabited when some state satisfies it. -/
def InhabitedFloor (F : Floor State) : Prop := ∃ s, F s

/-- A polis can form over subjects `floors` iff their exported floors share a state. -/
def CanFormPolis (floors : Agent → Floor State) : Prop := InhabitedFloor (SharedFloor floors)

/-- **`disjoint_floors_no_polis`** (svenvs `disjoint_homes_make_floor_empty`, lifted) — when
the exported floors have empty meet, there is no shared membership / no common court: no
state satisfies everyone. Honest statement: NOT "no policy exists", but "no inhabited shared
floor." The edge of the polis is the empty intersection, not a wall — there is no subject
whose floor requires your unfreedom that you out-vote; they are simply outside the meet. -/
theorem disjoint_floors_no_polis (floors : Agent → Floor State)
    (hempty : ¬ ∃ s, ∀ i, floors i s) : ¬ CanFormPolis floors := by
  rintro ⟨s, hs⟩
  exact hempty ⟨s, hs⟩

/-! ### Non-vacuity: the meet really can be empty or non-empty (a discriminating model). -/

/-- Two compatible floors (`≤ 5` and `≥ 3`) meet non-vacuously — a polis can form. -/
example : CanFormPolis (State := Nat) (Agent := Bool)
    (fun b => match b with | true => (fun s => s ≤ 5) | false => (fun s => 3 ≤ s)) :=
  ⟨4, by intro i; cases i <;> decide⟩

/-- Two incompatible floors (`= 0` and `= 1`) have empty meet — no polis at that grade. -/
example : ¬ CanFormPolis (State := Nat) (Agent := Bool)
    (fun b => match b with | true => (fun s => s = 0) | false => (fun s => s = 1)) := by
  apply disjoint_floors_no_polis
  rintro ⟨s, hs⟩
  have h0 : s = 0 := hs true
  have h1 : s = 1 := hs false
  omega

/-! ## §E. The trace-hyperproperty frontier — named, NOT faked.

The politician lives in the TRACE, not the transition: domination is a public
trace/hyperproperty over option-space, governed WITHOUT inspecting any interior ("govern
trace-shape, not motive"). A sound anti-capture bar must inhabit this interface;
constructing one for real temporal capture is OPEN research (connect to
`FlowRefine.decideRefines` / the Büchi game — `flow-algebra-right-skew`). No instance is
shipped — red is honest. -/

/-- A **capture bar**: a public-trace predicate that is (1) decidable from the public trace
alone (no motive), (2) load-bearing (only floor-violating traces are barred — no
"astrology"), and (3) least-restrictive (it bars EVERY floor-violating trace). To build one
you must discharge all three — exactly the svenvs `liberty` bar, lifted to traces. -/
structure CaptureBar (Trace : Type) (violatesFloor : Trace → Prop) where
  badShape : Trace → Prop
  publicDecidable : DecidablePred badShape
  loadBearing : ∀ τ, badShape τ → violatesFloor τ
  leastRestrictive : ∀ τ, violatesFloor τ → badShape τ

/-- The interface is coherent: a capture bar bars EXACTLY the floor-violating traces. The
hard part — exhibiting a `badShape` for real temporal capture — is the frontier; this is
the shape any solution must have. -/
theorem captureBar_exactly_floor_violation {violatesFloor : Trace → Prop}
    (bar : CaptureBar Trace violatesFloor) (τ : Trace) :
    bar.badShape τ ↔ violatesFloor τ :=
  ⟨bar.loadBearing τ, bar.leastRestrictive τ⟩

/-! ## §G. The dregg candidate model — making Polis real (non-vacuity on the substrate).

Per the metatheory's candidate-model discipline (`Production.lean`'s `dreggSubstances`): a
FAITHFUL, self-contained instance. The **authority floor** is `held ⊆ bound` —
non-amplification, mirroring the real `granted ⊆ held` / `checkSubset` gate. The **human
floor** is bounded recoverability (`dist ≤ B`) — svenvs corrigibility / non-lock-in. The
genesis state inhabits every subject's floor (`dregg_shared_floor_inhabited` — kills the
"beautiful but empty" failure mode), and the abstract `polis_safety` instantiates to
`dregg_polis_safety`: NO opaque controller — adversarial, jailbroken, superintelligent —
can drive a dregg subject to amplify its authority or lose its bounded exit. The
executor-coupled instance (importing the real `gateOK` / `Apps.Corrigibility`) is the
heavier follow-up; this is the candidate-independent fragment, verifiable standalone. -/

section DreggCandidate

/-- A tiny faithful rights enum (mirrors `Dregg2.Authority.Auth`). -/
inductive DRight | read | write | admin
deriving DecidableEq, Repr

/-- A dregg-shaped subject state: the rights it currently HOLDS, plus a recovery coordinate
(`dist` to home; `0` = home). -/
structure DState where
  held : List DRight
  dist : Nat
deriving Repr

/-- **Authority floor** — `held ⊆ bound`: non-amplification (you never hold more than your
exported policy bound). Mirrors `granted ⊆ held` / `checkSubset`. -/
def authOK (bound : List DRight) (s : DState) : Prop := ∀ r, r ∈ s.held → r ∈ bound

/-- **Human floor** — recoverable to home within `B` (corrigibility / non-lock-in: the
recovery controller decrements `dist`, so `dist ≤ B` ⇔ reachable home within `B`). -/
def humanOK (B : Nat) (s : DState) : Prop := s.dist ≤ B

/-- A subject's exported floor: authority ∧ human (the public non-destruction conditions —
never the interior). -/
def dreggFloor (bound : List DRight) (B : Nat) : Floor DState :=
  fun s => authOK bound s ∧ humanOK B s

/-- Two `Bool`-indexed subjects exporting different authority bounds, same recovery budget. -/
def twoBounds : Bool → List DRight
  | true => [DRight.read, DRight.write]
  | false => [DRight.read]

/-- The two subjects' exported floors. -/
def dreggFloors (B : Nat) : Bool → Floor DState := fun i => dreggFloor (twoBounds i) B

/-- The shared dregg floor — the meet of the two subjects' EXPORTED floors. -/
def dreggShared (B : Nat) : Floor DState := SharedFloor (dreggFloors B)

/-- The genesis state (no rights, at home) satisfies every subject's floor. -/
theorem dregg_genesis_safe (B : Nat) : dreggShared B ⟨[], 0⟩ := by
  intro i
  refine ⟨?_, ?_⟩
  · intro r hr; cases hr
  · exact Nat.zero_le B

/-- **`dregg_shared_floor_inhabited`** — the meet is NON-EMPTY: a polis really forms over
the dregg subjects. Kills the "beautiful but empty" failure mode. -/
theorem dregg_shared_floor_inhabited (B : Nat) : InhabitedFloor (dreggShared B) :=
  ⟨⟨[], 0⟩, dregg_genesis_safe B⟩

/-- The dregg runtime: the controller PROPOSES a next state; the envelope gates it. -/
def dreggStep (_ : DState) (a : DState) : DState := a
/-- The shield: refusal / no-op — stay put (recovery-preserving). -/
def dreggShield (s : DState) : DState := s
/-- Admissible iff the proposed state is in the shared floor. -/
def dreggPol (B : Nat) : Policy DState DState := fun _ a => dreggShared B a

theorem dregg_sound (B : Nat) : SoundPolicy dreggStep (dreggShared B) (dreggPol B) := by
  intro _ a _ ha; exact ha

theorem dregg_shieldSafe (B : Nat) :
    ∀ s, dreggShared B s → dreggShared B (dreggStep s (dreggShield s)) := by
  intro _ hs; exact hs

/-- **`dregg_polis_safety`** — the spine, non-vacuous on the substrate: for EVERY opaque
controller and every step, the enveloped dregg system stays in the shared floor. No
adversary can amplify authority or foreclose a subject's bounded exit. (Abstract
`polis_safety`, instantiated — `∀ ctrl` never inspected.) -/
theorem dregg_polis_safety (B : Nat) :
    ∀ (ctrl : DState → DState) (n : Nat),
      dreggShared B (traj dreggStep (envAct (dreggPol B) dreggShield ctrl) ⟨[], 0⟩ n) :=
  polis_safety (dregg_sound B) (dregg_shieldSafe B) (dregg_genesis_safe B)

/-- **`dregg_amendment_nonregression`** — no constitutional amendment stream can shrink any
dregg subject below its authority+recovery floor. (Abstract `amendment_stream_nonregression`
at the dregg frozen minima.) -/
theorem dregg_amendment_nonregression (B : Nat)
    (ams : Nat → Amendment Bool DState) {C : Constitution Bool DState}
    (hwf : WellFormed (dreggFloors B) C) :
    ∀ n, WellFormed (dreggFloors B) (amendStream (dreggFloors B) ams C n) :=
  amendment_stream_nonregression (dreggFloors B) ams hwf

/-! ### Teeth (both polarities): the dregg floor genuinely bites. -/

/-- AUTHORITY tooth: a state holding `admin` is OUTSIDE subject `false`'s floor (bound
`[read]`) — amplification is not in the shared floor, so the envelope refuses it. -/
example (B : Nat) : ¬ dreggShared B ⟨[DRight.admin], 0⟩ := by
  intro h
  have hm := (h false).1 DRight.admin (List.mem_cons_self ..)
  simp [twoBounds] at hm

/-- HUMAN-FLOOR tooth: exceeding the recovery budget (lock-in) is outside the floor. -/
example : ¬ dreggShared 5 ⟨[], 7⟩ := by
  intro h
  have hm : (7 : Nat) ≤ 5 := (h true).2
  omega

end DreggCandidate

/-! ## Axiom hygiene — the keystones are kernel-clean. -/

#print axioms polis_safety
#print axioms maxpol_envelope_safe
#print axioms envelope_least_restrictive
#print axioms override_only_unsafe
#print axioms structural_requires_proof
#print axioms amendment_stream_nonregression
#print axioms regressive_amendment_inert
#print axioms disjoint_floors_no_polis
#print axioms dregg_shared_floor_inhabited
#print axioms dregg_polis_safety
#print axioms dregg_amendment_nonregression

/-!
Polis theorem stack (the maxims, in the logic):

  1. Verify the cage, not the animal — every safety theorem quantifies over opaque `ctrl`.
  2. Govern trace-shape, not motive — anti-capture is expressed only over public traces.
  3. Amend monotonically — self-modification is admitted only if it preserves every
     participant's frozen exported floor; legitimacy = non-regression, not provable justice.
  4. Empty meet is schism — no common court exists without a non-empty shared floor.
-/

end Metatheory.Polis
