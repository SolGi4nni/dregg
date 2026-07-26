/-
# `Dregg2.Circuit.PremiseInhabitabilitySweep` — the INSTRUMENT, run across the soundness classes
`PremiseInhabitability` left UNSETTLED, plus the teeth that campaign's own repair still owes.

`PremiseInhabitability` (§5, §7) proved FIVE landed FRI-LDT bundles empty the deployed acceptance
predicate and tabulated the rest as NO CONTRADICTION FOUND / UNKNOWN. This module continues that
sweep. It adds nothing to the wound class's definition; it adds the missing TOOTH SHAPE and fires it
where the earlier pass could not reach.

## §A what was missing from the instrument, and is added here (§1)

`Empties` needs the premise's conclusion refuted on EVERY accepting run. That is the right tooth for
the OOD singleton (acceptance pins `oodPoint` on every run) and the wrong tooth for everything else:
most conjuncts are refutable only at a run one can EXHIBIT. `YieldsAt` + `not_of_yieldsAt_refutedAt`
is the point-refutation form — ONE exhibited accepting run on which the premise's conclusion fails
makes the premise FALSE, no `RejectsAll` required. It is strictly sharper than the `Empties` route
(`empties_of_yieldsAt` recovers the old form) and it is what the residual caveat needs.

## §B the caveat the repair owes, as a THEOREM (§2)

The corrected bundles of this campaign RETAIN `topen ∈ (view pi π).1.tableOpenings`, and acceptance
does NOT supply it. Two modules fire this, at different resolutions, and NEITHER subsumes the other
— stated here so this one is not read as the first:

  * `AlgoStarkSoundFanoutMemFree.memFreeFanout_premise_false_of_accepting_run_without_tableOpenings`
    (that lane's own, `:62` in its header) fires it at the `ℤ`-typed migrated premise of the 26
    fan-out instances, from a HYPOTHESIZED accepting run without table openings;
  * `tableOpeningMember_forcing_premise_is_false_at_a_real_pole` (§2 here) fires it at SCHEMA level
    on the EXHIBITED run, quantified over EVERY premise of the shape and over any field type, from
    `FriLdtExtractDeployed.deployed_accepting_pole_has_no_tableOpenings` (a `decide`-backed accepting
    run with `tableOpenings = []`).

What this module adds is therefore the generic tooth and the exhibited-pole discharge, not the
observation.

Read exactly: the landed and corrected bundles are `ℤ`-typed and the exhibited pole is `Nat`-typed,
so this REFUTES THE SCHEMA at the arguments where anything at all is exhibitable — it does not prove
the `ℤ` bundle false at the `opaque` deployed arguments. That is the same resolution as the rest of
this campaign, and it is the honest one: the corrected bundles STILL have no exhibited model, and the
one place a model could be exhibited refutes the conjunct they kept.

## §C the completeness class, settled (§3)

`CircuitCompleteness.StarkComplete` was tabulated `N/A — DUAL DIRECTION`. It is not N/A. Combined
with the landed FRI-LDT bundle — which forces `verifyBatch` to reject EVERY triple — it forces
something much worse than vacuity: NO trace whatsoever satisfies any registry descriptor while
publishing its own public inputs (`starkComplete_and_landedBundle_forbid_every_satisfying_trace`).
The emptied soundness premise does not merely make the soundness apex vacuous; carried alongside the
completeness carrier it empties the SATISFACTION relation, which is a statement about the prover
side and about descriptors nobody in this campaign was looking at.

## §D the abstract extraction floors (§4)

`AggAirSound.FriExtract`, `GroundedApex.BindingExtract` and the NINE `*LeafFriFloor` classes are one
shape: `Sat k → ∃ q, verify q = true ∧ …`. They are quantified over an ABSTRACT `verify` that is
never instantiated at the deployed verifier, so no acceptance predicate exists to test them against
and the §C recipe of `PremiseInhabitability` cannot be run. What CAN be settled, and is settled here
as theorems rather than as a shrug, is the pair that brackets them:

  * `deadVerifier_empties_leafFloor` — at any instantiation whose verifier rejects everything, the
    floor FORCES the in-circuit subcircuit to be UNSATISFIABLE. So these floors are not free: they
    are exactly as strong as the claim that the leaf verifier accepts something.
  * `leafFloor_inhabited_nondegenerately` — at `DescriptorIR2.demoEngine` the floor HOLDS with its
    antecedent SATISFIED. So they are not empty notions either, and the UNKNOWN verdict is about the
    DEPLOYED instantiation specifically, not about the shape.
  * `bindingExtract_is_free_when_the_binding_proof_fails` — `BindingExtract` is TRIVIALLY TRUE on any
    aggregate whose binding proof does not verify, so `GroundedApex.engineSound_grounded` says
    nothing at all about such aggregates.

## §E the carrier-gated kernel family, and a SECOND vacuity mode (§5)

Thirteen `Dregg2/Crypto/` classes gate their extraction on a self-chosen `extractable : Prop`
carrier. That gate admits a vacuity mode this campaign had not met: `extractable := False` makes
`extract` free, keeps the class inhabited, keeps the derived soundness theorem TRUE — and makes it
UNAPPLIABLE, even while the verifier accepts everything. It is independent of the empty-acceptance
mode (each is exhibited at a legal instance of the real in-tree `MerkleVerifierKernel`), so
checking one is not checking the other. `CarrierLive` is the conjunction that excludes both, and
`carrierLive_fires` is what it buys.

## §F the campaign's debt, MEASURED rather than caveated (§6)

`at_the_only_exhibited_pole_the_repair_is_half_realized`: on ONE run — the only accepting run of the
apex-facing predicate exhibited anywhere — the corrected OOD conjuncts HOLD at the deployed lane
width, the landed singleton is REFUTED, and the retained table-opening conjunct FAILS. The repair's
outstanding debt is therefore not diffuse: it is exactly the `tableOpenings` conjunct.

## §G the table is §7 — including one CORRECTION to the earlier pass

`PremiseInhabitability` §7's S7 read `ShieldedMerkleRootPin.AccumulatorSound` as an abstract class
and returned NO CONTRADICTION FOUND. Instantiated at the DEPLOYED on-ramp that verdict is wrong as a
deployment statement: the tree already PROVES the premise FALSE there
(`ShieldedOnRampPin.deployed_append_unsound`), and already flags its derived `IsCommittedNote` form
as holding at every root including a prover-written one. R18 records the correction. The lesson is
the instrument's own: a verdict about an abstract class is not a verdict about its instantiation.

## §H ⚑ WHAT IS AND IS NOT SETTLED (read before citing anything above)

SETTLED — machine-checked here: the point-refutation tooth (§1); that a premise demanding a table
opening on every accepting run is FALSE at the exhibited pole (§2); that the landed FRI-LDT bundle
carried alongside `StarkComplete` forbids EVERY satisfying trace (§3); the two brackets on the
abstract extraction floors (§4); the two independent vacuity modes of the carrier-gated kernel
family, each at a legal instance of a real in-tree class (§5); and that the campaign's repair is
HALF-realized at the only exhibited pole — OOD correction holds, table-opening conjunct fails (§6).

NOT SETTLED, and NOT to be read as settled:

  * NOTHING here proves any bundle SATISFIABLE at the deployed `cfg*` arguments. Those are
    `opaque`; no one can decide them. Every "UNKNOWN" in §7 is an UNSETTLED entry, not a pass.
  * §2 and §6 are at `Nat`-typed pole arguments; the landed and corrected bundles are `ℤ`-typed at
    `opaque` arguments. They refute the SCHEMA where anything is exhibitable. That gap is stated in
    §B and is not closed.
  * R5's nine `*LeafFriFloor` classes are machine-checked only at the `Custom` member; the other
    eight are reported as READ, not as separately proved.
  * The family-wide `extractable := True` finding (§5) was machine-checked at the Merkle kernel only;
    the other seven were READ at the cited `file:line`, not proved here. ⚑ REPAIRED 2026-07-25 — all
    eight now carry a PROVED, separately-REFUTED carrier (`Dregg2/Crypto/CarrierContent.lean`). The
    repair does not move the DEPLOYMENT verdict in R11 one inch: those are toy oracles.
  * R9–R16 were examined at reading resolution only, or not at all where the row says so.
  * The `#assert_axioms` lines below check what the proofs REST ON. They are structurally blind to
    the wound this module measures — that is the whole reason this module exists (`PremiseInhabitability`
    §B). Do not read a clean axiom audit here as an inhabitability result.
-/
import Dregg2.Circuit.PremiseInhabitability
import Dregg2.Circuit.CircuitCompleteness
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.GroundedApex
import Dregg2.Circuit.CustomBindingFromFold
import Dregg2.Crypto.VerifierKernel

namespace Dregg2.Circuit.PremiseInhabitabilitySweep

universe u v w

open Dregg2.Circuit.PremiseInhabitability
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 Satisfied2 ProofEngine demoEngine)
open Dregg2.Circuit.FriVerifier
  (BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith TableOpening)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof Verdict Registry vkOfRegistry verifyBatch tracePublishedCommit
   cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN cfgView)
open Dregg2.Circuit.ExtFieldChallenge (ExtFriCore ExtFriArith ExtVerifierView)
open Dregg2.Circuit.CircuitCompleteness (StarkComplete)
open Dregg2.Circuit.FriLdtExtractDeployed (deployed_accepting_pole_has_no_tableOpenings)

set_option autoImplicit false

/-! ## §1 — THE POINT-REFUTATION TOOTH (the instrument's missing shape).

`Empties P acc` demands the premise's conclusion be refuted on EVERY `acc`-accepting run. That is
available for the OOD singleton and for almost nothing else. `YieldsAt` names the weaker, universal
consequence a premise has on accepting runs, and `not_of_yieldsAt_refutedAt` refutes the premise from
ONE exhibited accepting run — which is what an exhibited pole actually gives you. -/

/-- **`YieldsAt P acc C`** — on every `acc`-accepting run, the premise `P` delivers `C`. Every
`Extracts`-shaped bundle is an instance with `C i := ∃ w, C' i w` (`yieldsAt_of_extracts`). -/
def YieldsAt {ι : Type u} (P : Prop) (acc : Acc ι) (C : ι → Prop) : Prop :=
  P → ∀ i, acc i → C i

/-- Every accepts-implies-exists bundle yields its own existential. -/
theorem yieldsAt_of_extracts {ι : Type u} {W : ι → Type v} (acc : Acc ι) (C : ∀ i, W i → Prop) :
    YieldsAt (Extracts acc C) acc (fun i => ∃ w : W i, C i w) :=
  fun h i hi => h i hi

/-- A `YieldsShape` premise yields the shape membership. -/
theorem yieldsAt_of_yieldsShape {ι : Type u} {A : Type v} {X : Type w}
    {P : Prop} {acc : Acc ι} {key : ι → X} {shape : A → X}
    (h : YieldsShape P acc key shape) :
    YieldsAt P acc (fun i => ∃ a : A, key i = shape a) := h

/-- **THE POINT-REFUTATION TOOTH.** ONE exhibited accepting run on which the premise's universal
consequence FAILS makes the premise FALSE. No `RejectsAll`, no `AcceptsSome`, no quantification over
all accepting runs — which is why this reaches conjuncts (table-opening membership, query shape,
segment content) that the `Empties` route cannot. -/
theorem not_of_yieldsAt_refutedAt {ι : Type u} {P : Prop} {acc : Acc ι} {C : ι → Prop}
    (h : YieldsAt P acc C) (i₀ : ι) (hacc : acc i₀) (href : ¬ C i₀) : ¬ P :=
  fun hP => href (h hP i₀ hacc)

/-- The old `Empties` verdict is the special case in which the refutation is available everywhere. -/
theorem empties_of_yieldsAt {ι : Type u} {P : Prop} {acc : Acc ι} {C : ι → Prop}
    (h : YieldsAt P acc C) (href : ∀ i, acc i → ¬ C i) : Empties P acc :=
  fun hP i hi => href i hi (h hP i hi)

/-- Point refutation is STRICTLY stronger than emptying wherever a pole exists: an emptied premise is
false there too, and the point form needs only the single run. -/
theorem not_of_empties_at_pole {ι : Type u} {P : Prop} {acc : Acc ι}
    (h : Empties P acc) (i₀ : ι) (hacc : acc i₀) : ¬ P :=
  fun hP => h hP i₀ hacc

/-- Point refutation transports along premise strength, like `empties_of_imp`. -/
theorem not_of_yieldsAt_refutedAt_imp {ι : Type u} {P Q : Prop} {acc : Acc ι} {C : ι → Prop}
    (hPQ : P → Q) (h : YieldsAt Q acc C) (i₀ : ι) (hacc : acc i₀) (href : ¬ C i₀) : ¬ P :=
  fun hP => href (h (hPQ hP) i₀ hacc)

/-! ## §2 — THE RESIDUAL CAVEAT, FIRED: table-opening membership is refuted at the exhibited pole.

Every corrected bundle in this campaign kept `topen ∈ (view pi π).1.tableOpenings`. The only
accepting run of the apex-facing predicate exhibited anywhere carries `tableOpenings = []`. -/

/-- **The generic form**, over any field type and any accepting run with no table openings: a premise
that demands a table opening on every accepting run is FALSE at those verifier arguments. -/
theorem not_of_tableOpeningYield_at_empty_pole {F : Type} [Inhabited F] [DecidableEq F]
    {P : Prop}
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat)
    (r₀ : BatchProofData F × WrapPublics F × ExtVerifierView F)
    (hacc : rawDeployedAcc perm RATE toNat params vk core A extCore extA W initState logN r₀)
    (hnil : r₀.1.tableOpenings = [])
    (h : YieldsAt P (rawDeployedAcc perm RATE toNat params vk core A extCore extA W initState logN)
      (fun r => ∃ topen : TableOpening F, topen ∈ r.1.tableOpenings)) :
    ¬ P := by
  refine not_of_yieldsAt_refutedAt h r₀ hacc ?_
  rintro ⟨topen, hmem⟩
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

/-- **THE CAVEAT, FIRED ON THE REAL POLE.** At verifier arguments where the deployed
extension-faithful predicate demonstrably ACCEPTS a run, EVERY premise that produces a table opening
on every accepting run is FALSE.

This is the counterpart of `PremiseInhabitability.singleton_forcing_premise_is_false_at_a_real_pole`,
and it points at the conjunct the REPAIR kept rather than the one it deleted. What it does NOT say:
that `FriLdtExtractV3Faithful` (which is `ℤ`-typed, at `opaque` deployed arguments) is false. What it
does say: the corrected bundles' surviving table-opening conjunct is not merely unwitnessed — at the
one instantiation where anything is exhibitable, it is REFUTED. The repair therefore still owes an
exhibited model, and this is the receipt for that debt. -/
theorem tableOpeningMember_forcing_premise_is_false_at_a_real_pole :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (W : Nat)
      (initState : List Nat) (logN : Nat),
      ∀ P : Prop,
        YieldsAt P (rawDeployedAcc perm RATE toNat params vk core A extCore extA W initState logN)
            (fun r => ∃ topen : TableOpening Nat, topen ∈ r.1.tableOpenings) →
          ¬ P := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, proof, pub,
    view, hacc, hnil⟩ := deployed_accepting_pole_has_no_tableOpenings
  refine ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, ?_⟩
  intro P h
  exact not_of_tableOpeningYield_at_empty_pole perm RATE toNat params vk core A extCore extA W
    initState logN (proof, pub, view) hacc hnil h

/-! ## §3 — `StarkComplete` IS reachable by the instrument, and the news is bad.

`PremiseInhabitability` §7 tabulated `CircuitCompleteness.StarkComplete` as `N/A — DUAL DIRECTION`,
on the ground that its premise is a `Satisfied2` witness rather than verifier acceptance. That is
true of the class in isolation and false of the class IN THE PRESENCE OF the landed FRI-LDT bundle,
because that bundle makes `verifyBatch` reject every triple and `StarkComplete` promises an accepting
triple. -/

/-- **THE COMPLETENESS-SIDE TOOTH.** Carrying the landed `AlgoStarkSoundGeneral.FriLdtExtract` at the
deployed `cfg*` arguments TOGETHER WITH the completeness carrier `StarkComplete hash R` forces: NO
trace satisfies the descriptor its public inputs name while publishing those public inputs — for
EVERY registry, EVERY descriptor, EVERY boundary, EVERY trace.

The soundness-side reading of the wound was "the apex quantifies over an empty accepting set". This
is the prover-side reading, and it is strictly worse: the emptied premise, standing next to the
completeness floor the same tree carries, denies the existence of any satisfying witness at all. A
premise with that consequence is not a conservative thing to leave a consumer riding.

⚑ THE UPGRADE THAT IS BLOCKED, CHECKED RATHER THAN LEFT OPEN. The natural sharpening is to REFUTE
the pair outright by exhibiting one satisfying trace that publishes its own inputs — the tree has the
first half (`CircuitCompletenessNonVacuityReal` inhabits `Satisfied2 hash transferV3 …` at a
non-empty real transfer row). The second half is unreachable: `tracePublishedCommit` is `opaque`
(`CircuitSoundness.lean:467`) and `BatchPublicInputs` (`:331`) has no field through which
`pi.toPublished` could be aimed at it, so `tracePublishedCommit t = pi.toPublished` is not provable
for ANY concrete pair, by anyone. The collapse therefore stops at "these two carriers jointly empty
the satisfaction relation" and does not reach "these two carriers are jointly false". -/
theorem starkComplete_and_landedBundle_forbid_every_satisfying_trace
    (hash : List ℤ → ℤ) (R : Registry) [hc : StarkComplete hash R]
    (sponge : List ℤ → ℤ)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (hfri : Dregg2.Circuit.AlgoStarkSoundGeneral.FriLdtExtract sponge cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN cfgView tr d)
    (pi : BatchPublicInputs) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (R pi.effect) minit mfin maddrs t) :
    tracePublishedCommit t ≠ pi.toPublished := by
  intro hpub
  obtain ⟨π, hacc⟩ := hc.build pi minit mfin maddrs t hsat hpub
  rw [friLdtExtract_makes_verifyBatch_reject_everything sponge tr d hfri (vkOfRegistry R) pi π]
    at hacc
  exact Verdict.noConfusion hacc

/-- The same collapse read as an emptiness verdict on the SATISFACTION side: under the two carriers,
the predicate "this trace satisfies the named descriptor and publishes the named inputs" — the
subject of every refinement rung in the tree — accepts nothing. -/
theorem starkComplete_and_landedBundle_empty_the_satisfaction_relation
    (hash : List ℤ → ℤ) (R : Registry) [StarkComplete hash R]
    (sponge : List ℤ → ℤ)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (hfri : Dregg2.Circuit.AlgoStarkSoundGeneral.FriLdtExtract sponge cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN cfgView tr d) :
    RejectsAll (fun q : BatchPublicInputs × (ℤ → ℤ) × (ℤ → ℤ × Nat) × List ℤ × VmTrace =>
      Satisfied2 hash (R q.1.effect) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
        ∧ tracePublishedCommit q.2.2.2.2 = q.1.toPublished) := by
  rintro q ⟨hsat, hpub⟩
  exact starkComplete_and_landedBundle_forbid_every_satisfying_trace hash R sponge tr d hfri
    q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 hsat hpub

/-! ## §4 — THE ABSTRACT EXTRACTION FLOORS, BRACKETED.

`AggAirSound.FriExtract` (`:157`), `GroundedApex.BindingExtract` (`:93`) and the nine `*LeafFriFloor`
classes are one shape. They are stated over an ABSTRACT `verify` which the tree never instantiates at
the deployed verifier, so the deployed-acceptance check has no argument to run on and the verdict at
deployment is genuinely UNKNOWN. Both brackets ARE settleable, and are settled here. -/

/-- A verifier that rejects everything — the degenerate instantiation these floors do not exclude. -/
def deadEngine : ProofEngine :=
  { Proof := Bool, verify := fun _ => false, piCommit := fun _ => 0, vkOf := fun _ => 0 }

/-- **The `*LeafFriFloor` family IS the `Extracts` shape**, so the whole instrument applies to it.
Stated at `CustomBindingFromFold.CustomLeafFriFloor`; the other eight (`Factory`, `Contract`,
`Membership`, `Sovereign`, `Dsl`, `Deco`, `NoteSpend`, `Blinded`) are the same body with the
projection renamed, and `AggAirSound.FriExtract` is the same body over `Seg`. -/
theorem customLeafFriFloor_iff_extracts (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor E Sat
      ↔ Extracts (fun p : ℤ × ℤ => Sat p.1 p.2)
          (fun p (q : E.Proof) => E.verify q = true ∧ E.piCommit q = p.2) := by
  constructor
  · intro h p hp; exact h p.1 p.2 hp
  · intro h a b hab; exact h (a, b) hab

/-- **THE LOWER BRACKET — these floors are NOT free.** At any instantiation whose leaf verifier
rejects everything, the floor EMPTIES the in-circuit satisfaction predicate: no satisfying
child-verifier subcircuit trace can exist. So `CustomLeafFriFloor` (and each of its eight siblings)
is exactly as strong as the claim that the leaf verifier accepts something — carrying it is carrying
that claim, and a consumer that never exhibits an accepting leaf proof has assumed the subcircuit
away rather than discharged it. -/
theorem deadVerifier_empties_leafFloor (E : ProofEngine) (Sat : ℤ → ℤ → Prop)
    (hdead : ∀ q : E.Proof, E.verify q = false) :
    Empties (Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor E Sat)
      (fun p : ℤ × ℤ => Sat p.1 p.2) := by
  intro h p hp
  obtain ⟨q, hq, _⟩ := h p.1 p.2 hp
  rw [hdead q] at hq
  exact Bool.noConfusion hq

/-- Fired at the concrete degenerate engine: nothing satisfies the subcircuit. -/
theorem deadEngine_leafFloor_forbids_satisfaction (Sat : ℤ → ℤ → Prop)
    (h : Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor deadEngine Sat) (a b : ℤ) :
    ¬ Sat a b :=
  fun hab => deadVerifier_empties_leafFloor deadEngine Sat (fun _ => rfl) h (a, b) hab

/-- **THE UPPER BRACKET — these floors are NOT empty notions.** At `DescriptorIR2.demoEngine` the
floor HOLDS with its antecedent SATISFIED — a non-degenerate model, not the cheap one obtained by
making the antecedent unsatisfiable (which `leafFloor_is_free_when_unsatisfiable` records
separately). So the UNKNOWN verdict for this family is about the DEPLOYED instantiation, which the
tree never writes down, and not about the shape. -/
theorem leafFloor_inhabited_nondegenerately :
    Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor demoEngine (fun _ c => c = 123)
      ∧ (∃ a b : ℤ, (fun (_ : ℤ) (c : ℤ) => c = 123) a b) := by
  constructor
  · intro a b hab
    exact ⟨true, rfl, hab.symm⟩
  · exact ⟨0, 123, rfl⟩

/-- The degenerate satisfaction: an unsatisfiable subcircuit predicate makes the floor free. Recorded
so `leafFloor_inhabited_nondegenerately` cannot be mistaken for this. -/
theorem leafFloor_is_free_when_unsatisfiable (E : ProofEngine) (Sat : ℤ → ℤ → Prop)
    (hno : ∀ a b, ¬ Sat a b) :
    Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor E Sat :=
  fun a b hab => absurd hab (hno a b)

/-- **`AggAirSound.FriExtract`, the same two brackets.** Lower: a dead child verifier empties the
child-verifier satisfaction predicate. -/
theorem deadVerifier_empties_aggFriExtract
    (Proof : Type) (verify : Proof → Bool) (vkCommit : Proof → ℤ)
    (exposedPI : Proof → Dregg2.Circuit.RecursiveAggregation.Seg)
    (ChildVerifierSat : ℤ → Dregg2.Circuit.RecursiveAggregation.Seg → Prop)
    (hdead : ∀ q : Proof, verify q = false) :
    Empties (Dregg2.Circuit.AggAirSound.FriExtract Proof verify vkCommit exposedPI ChildVerifierSat)
      (fun p : ℤ × Dregg2.Circuit.RecursiveAggregation.Seg => ChildVerifierSat p.1 p.2) := by
  intro h p hp
  obtain ⟨q, hq, _, _⟩ := h p.1 p.2 hp
  rw [hdead q] at hq
  exact Bool.noConfusion hq

/-- Upper bracket for `AggAirSound.FriExtract`: a non-degenerate model — the floor holds AND its
antecedent is satisfied. -/
theorem aggFriExtract_inhabited_nondegenerately :
    ∃ (Proof : Type) (verify : Proof → Bool) (vkCommit : Proof → ℤ)
      (exposedPI : Proof → Dregg2.Circuit.RecursiveAggregation.Seg)
      (ChildVerifierSat : ℤ → Dregg2.Circuit.RecursiveAggregation.Seg → Prop),
      Dregg2.Circuit.AggAirSound.FriExtract Proof verify vkCommit exposedPI ChildVerifierSat
        ∧ (∃ c s, ChildVerifierSat c s) := by
  refine ⟨ℤ × Dregg2.Circuit.RecursiveAggregation.Seg, fun _ => true, Prod.fst, Prod.snd,
    fun _ _ => True, ?_, ?_⟩
  · intro c s _
    exact ⟨(c, s), rfl, rfl, rfl⟩
  · exact ⟨0, ⟨0, 0, 0, 0⟩, trivial⟩

/-- **`GroundedApex.BindingExtract` is FREE — carries zero information — on any aggregate whose
binding proof does not verify.** So `GroundedApex.engineSound_grounded`, which consumes it, says
nothing whatsoever about such aggregates: its `binding_sound` leg is discharged by a premise that is
`True` there. This is the vacuity direction of the same wound, at a class the earlier sweep marked
UNKNOWN, and it is provable without any instantiation of the abstract verifier. -/
theorem bindingExtract_is_free_when_the_binding_proof_fails
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Dregg2.Circuit.RecursiveAggregation.Aggregate Proof)
    (steps : List Dregg2.Distributed.HistoryAggregation.ChainStep)
    (hrej : verify agg.bindingProof = false) :
    Dregg2.Circuit.GroundedApex.BindingExtract Proof verify hash CH RH cmb compress compressN agg
      steps := by
  intro hv
  rw [hrej] at hv
  exact Bool.noConfusion hv

/-! ## §5 — THE CARRIER-GATED KERNEL FAMILY: A SECOND, INDEPENDENT VACUITY MODE.

Thirteen classes in `Dregg2/Crypto/` (`VerifierKernel.lean:35`, `PortalFloor.lean:77`,
`Pedersen.lean:279`, `NonMembership.lean:249`, `Custom.lean:122`, `Deco.lean:285`,
`Temporal.lean:130`, `Dfa.lean:188`, `DfaAcceptanceAir.lean:512`, `Cfg.lean:110`,
`Bridge.lean:192`, `BlindedSet.lean:177`, `RangeProof.lean:183`) share ONE shape:

    verify     : Statement → Proof → Bool     -- an ABSTRACT acceptance predicate
    extractable : Prop                        -- a SELF-CHOSEN carrier, "never proved"
    extract     : extractable → ∀ stmt proof, verify stmt proof = true → ∃ w, Sat …

and each exports a derived theorem gated on the carrier (`merkle_verify_sound`,
`temporal_verify_sound`, `dfaAir_verify_sound`, …). This is the `Extracts` shape with an extra
gate, and the gate opens a vacuity mode the FRI sweep never had to consider:

  * **MODE 2 — empty acceptance.** `verify` rejects everything; the gated theorem quantifies over
    an empty set. This is the wound `PremiseInhabitability` was built for.
  * **MODE 1 — false carrier.** `extractable := False`; `extract` is then dischargeable for FREE,
    the class instance exists, the gated theorem is TRUE, and it can NEVER BE APPLIED — the
    verifier may accept every proof in sight and the theorem still reaches none of them.

The two are INDEPENDENT: neither implies the other, and an instance exhibiting each is built
below at the real in-tree class `Dregg2.Crypto.MerkleVerifierKernel`, whose real in-tree consumer
is `merkle_verify_sound`. Nothing in the family's definition, and no `#assert_axioms`, excludes
either mode. `CarrierLive` is the criterion that excludes both, and `carrierLive_fires` is what it
buys: the gated conclusion is reached on an actual run.

⚑ AND THE FAMILY'S OWN NON-VACUITY WITNESSES ALL PASS THE CARRIER HALF BY ASSUMPTION. Every
reference kernel in this family sets `extractable := True`: `VerifierKernel.lean:65`,
`NonMembership.lean:467`, `Pedersen.lean:486`, `Custom.lean:300`, `Deco.lean:498`,
`Temporal.lean:283`, `Bridge.lean:379`, `BlindedSet.lean:342` — eight for eight. Only the Merkle one
was machine-checked here; the other seven were reported as READ at those lines. So the mode-1 half of
the criterion was, family-wide, met by writing `True` — while `PortalFloor.lean`
(`instVerifierKernel_extractable` proved, `instVerifierForge_not_extractable` refuted) shows the same
tree knows how to give a carrier content. This was not a defect in any one instance; it was the
family's default.

⚑ **REPAIRED 2026-07-25.** All EIGHT now carry the genuine extractability-SHAPED `Prop` over their own
oracle (`extract := fun h => h`), each PROVED (`*_extractable`) and each REFUTED at a forge sibling
(`*forge*_not_extractable`) in the PortalFloor style. `referenceMerkleKernel_carrier_has_content`
below records it at the kernel this module measures; `Dregg2/Crypto/CarrierContent.lean` carries the
reusable criterion (`CarrierAudit`, whose `refuted` field a `True` carrier can never supply) and
fires it at all eight. The DEPLOYMENT verdict in row R11 is UNCHANGED: those carriers are proved at
TOY reference oracles, and no instantiation at any deployed verifier exists in-tree. -/

/-- **MODE 1, generically.** A conclusion gated on a FALSE carrier is arbitrary: the gated shape
holds for EVERY `Q`, so it carries no information — the carrier form of
`PremiseInhabitability.empties_proves_anything`. -/
theorem falseCarrier_proves_anything {ι : Type u} {carrier : Prop} {acc : Acc ι}
    (h : ¬ carrier) (Q : ι → Prop) : carrier → ∀ i, acc i → Q i :=
  fun hc => absurd hc h

/-- **MODE 2, generically.** A conclusion gated on a carrier that IS satisfiable is still arbitrary
when acceptance is empty. -/
theorem rejectsAll_proves_anything {ι : Type u} (carrier : Prop) {acc : Acc ι}
    (h : RejectsAll acc) (Q : ι → Prop) : carrier → ∀ i, acc i → Q i :=
  fun _ i hi => absurd hi (h i)

/-- **`CarrierLive carrier acc`** — the criterion that excludes BOTH modes: the carrier holds AND
acceptance is inhabited. This is what a carrier-gated kernel instance must exhibit for its derived
soundness theorem to say anything at all. -/
def CarrierLive {ι : Type u} (carrier : Prop) (acc : Acc ι) : Prop := carrier ∧ AcceptsSome acc

theorem carrierLive_excludes_falseCarrier {ι : Type u} {carrier : Prop} {acc : Acc ι}
    (h : CarrierLive carrier acc) : carrier := h.1

theorem carrierLive_excludes_rejectsAll {ι : Type u} {carrier : Prop} {acc : Acc ι}
    (h : CarrierLive carrier acc) : ¬ RejectsAll acc :=
  not_rejectsAll_of_acceptsSome h.2

/-- **WHAT THE CRITERION BUYS.** At a live instance the gated theorem DELIVERS: there is an actual
run on which its conclusion holds. Neither vacuity mode can produce this. -/
theorem carrierLive_fires {ι : Type u} {carrier : Prop} {acc : Acc ι} {Q : ι → Prop}
    (hlive : CarrierLive carrier acc) (hthm : carrier → ∀ i, acc i → Q i) : ∃ i, Q i := by
  obtain ⟨hc, i, hi⟩ := hlive
  exact ⟨i, hthm hc i hi⟩

/-- **`Discriminating acc`** — acceptance is neither empty nor total: some run is accepted and some
run is rejected. This is `Bridge/VerifiedLightClient.lean:141`'s `NonVacuous` carrier, stated in this
module's vocabulary; there it is a REQUIRED FIELD of `ForeignLightClient`, so no chain instance
exists until it is discharged. That is the discipline the STARK/FRI bundle family never had. -/
def Discriminating {ι : Type u} (acc : Acc ι) : Prop := AcceptsSome acc ∧ ∃ i, ¬ acc i

theorem discriminating_not_rejectsAll {ι : Type u} {acc : Acc ι}
    (h : Discriminating acc) : ¬ RejectsAll acc :=
  not_rejectsAll_of_acceptsSome h.1

/-- A discriminating acceptance predicate is also not TOTAL — the failure mode a verifier that
accepts everything has, which `AcceptsSome` alone does not exclude (`falseCarrierMerkleKernel` is
exactly that verifier). -/
theorem discriminating_not_total {ι : Type u} {acc : Acc ι}
    (h : Discriminating acc) : ¬ (∀ i, acc i) := by
  obtain ⟨_, i, hi⟩ := h
  exact fun htot => hi (htot i)

/-- A run of the Merkle kernel: `(root, leaf, proof)`. -/
abbrev MerkleRun : Type := Int × Int × Int

/-- A carrier-gated kernel's acceptance predicate, in the instrument's vocabulary. -/
def merkleAcc (K : Dregg2.Crypto.MerkleVerifierKernel Int Int) : Acc MerkleRun :=
  ofBool fun r => K.verify r.1 r.2.1 r.2.2

/-- **MODE-1 WITNESS.** A perfectly legal `MerkleVerifierKernel` that ACCEPTS EVERY TRIPLE and
discharges the `extract` obligation with a carrier that is `False`. -/
@[reducible] def falseCarrierMerkleKernel : Dregg2.Crypto.MerkleVerifierKernel Int Int where
  compress a b := a + b
  verify _ _ _ := true
  extractable := False
  extract := fun h => h.elim

theorem falseCarrierMerkleKernel_accepts_everything (r : MerkleRun) :
    merkleAcc falseCarrierMerkleKernel r := rfl

theorem falseCarrierMerkleKernel_acceptsSome : AcceptsSome (merkleAcc falseCarrierMerkleKernel) :=
  ⟨(0, 0, 0), falseCarrierMerkleKernel_accepts_everything (0, 0, 0)⟩

theorem falseCarrierMerkleKernel_carrier_false : ¬ falseCarrierMerkleKernel.extractable := id

/-- **THE MODE-1 VERDICT.** At this kernel the gated shape that `merkle_verify_sound` instantiates
holds for an ARBITRARY conclusion `Q` — including conclusions flatly contradicting membership —
while the verifier accepts every single triple. The soundness theorem is true, kernel-clean, and
unreachable. No axiom audit and no `sorry` scan sees this. -/
theorem falseCarrierMerkleKernel_soundness_never_fires (Q : MerkleRun → Prop) :
    falseCarrierMerkleKernel.extractable → ∀ r, merkleAcc falseCarrierMerkleKernel r → Q r :=
  falseCarrier_proves_anything falseCarrierMerkleKernel_carrier_false Q

/-- **MODE-2 WITNESS.** The dual degenerate kernel: the carrier is satisfiable (`True`) and the
verifier rejects everything. `extract` is again free — for the opposite reason. -/
@[reducible] def deadVerifierMerkleKernel : Dregg2.Crypto.MerkleVerifierKernel Int Int where
  compress a b := a + b
  verify _ _ _ := false
  extractable := True
  extract := by
    intro _ _ _ _ h
    exact Bool.noConfusion h

theorem deadVerifierMerkleKernel_carrier_holds : deadVerifierMerkleKernel.extractable := trivial

theorem deadVerifierMerkleKernel_rejectsAll : RejectsAll (merkleAcc deadVerifierMerkleKernel) := by
  intro r h
  exact Bool.noConfusion h

/-- **THE MODE-2 VERDICT** — the `PremiseInhabitability` wound, at a carrier-gated kernel. -/
theorem deadVerifierMerkleKernel_soundness_is_vacuous (Q : MerkleRun → Prop) :
    deadVerifierMerkleKernel.extractable → ∀ r, merkleAcc deadVerifierMerkleKernel r → Q r :=
  rejectsAll_proves_anything _ deadVerifierMerkleKernel_rejectsAll Q

/-- **THE TWO MODES ARE INDEPENDENT.** The mode-1 kernel has an inhabited accepting set and a false
carrier; the mode-2 kernel has a true carrier and an empty accepting set. So checking either one
alone is not a check: only the conjunction `CarrierLive` is. -/
theorem the_two_vacuity_modes_are_independent :
    (AcceptsSome (merkleAcc falseCarrierMerkleKernel)
        ∧ ¬ falseCarrierMerkleKernel.extractable)
      ∧ (deadVerifierMerkleKernel.extractable
        ∧ RejectsAll (merkleAcc deadVerifierMerkleKernel)) :=
  ⟨⟨falseCarrierMerkleKernel_acceptsSome, falseCarrierMerkleKernel_carrier_false⟩,
   ⟨deadVerifierMerkleKernel_carrier_holds, deadVerifierMerkleKernel_rejectsAll⟩⟩

/-- An accepting run of the reference kernel: `root = 2`, `leaf = 1`, `proof = 2`. -/
theorem referenceMerkleKernel_accepts_a_run :
    merkleAcc Dregg2.Crypto.Reference.instMerkleVerifierKernel (2, 1, 2) := rfl

/-- **THE ONE IN-TREE INSTANCE OF THIS CLASS PASSES THE CRITERION** — `Dregg2.Crypto.Reference`'s
kernel is `CarrierLive`, so `merkle_verify_sound` genuinely fires there. Read the next theorem
before reading this as reassurance.

⚑ **2026-07-25**: the carrier half is no longer `trivial`. It is
`instMerkleVerifierKernel_extractable`, a PROVED theorem over the reference oracle (see the repair
note on the next theorem). -/
theorem referenceMerkleKernel_carrierLive :
    CarrierLive Dregg2.Crypto.Reference.instMerkleVerifierKernel.extractable
      (merkleAcc Dregg2.Crypto.Reference.instMerkleVerifierKernel) :=
  ⟨Dregg2.Crypto.Reference.instMerkleVerifierKernel_extractable,
   ⟨(2, 1, 2), referenceMerkleKernel_accepts_a_run⟩⟩

/-- **…AND IT USED TO PASS WITH A CARRIER THAT HAD NO CONTENT — REPAIRED 2026-07-25.**

As measured by this sweep, `Reference`'s `extractable` was literally `True` — dischargeable by
`trivial` — so the mode-1 half of the criterion was met by assumption rather than by argument, at all
EIGHT reference kernels of the family. `Dregg2/Crypto/PortalFloor.lean` was the contrasting
discipline in the same tree: its `instVerifierKernel.extractable` is an extractability-SHAPED `Prop`
separately PROVED (`instVerifierKernel_extractable`) and separately REFUTED at a forgery instance
(`instVerifierForge_not_extractable`).

The eight have since been repaired to that pattern, and this theorem records the repair AT THE
KERNEL THIS MODULE MEASURED: the carrier is a theorem, and the SAME carrier shape is FALSE at
`forgeMerkleKernel` (a legal kernel whose node hash collapses to `0` while its verifier accepts every
triple). A `True` carrier can never have the second conjunct — that is the whole content of the
repair. `Dregg2/Crypto/CarrierContent.lean` carries the criterion (`CarrierAudit`,
`carrierAudit_shape_is_not_true`) and fires it at all eight. -/
theorem referenceMerkleKernel_carrier_has_content :
    Dregg2.Crypto.Reference.instMerkleVerifierKernel.extractable
      ∧ ¬ Dregg2.Crypto.Reference.forgeMerkleKernel.extractable :=
  ⟨Dregg2.Crypto.Reference.instMerkleVerifierKernel_extractable,
   Dregg2.Crypto.Reference.forgeMerkleKernel_not_extractable⟩

/-! ## §6 — THE REPAIR'S DEBT, LOCALIZED TO EXACTLY ONE CONJUNCT.

§2 refuted the retained `topen ∈ tableOpenings` conjunct at the exhibited pole. The natural next
question is whether the pole refutes the repair WHOLESALE — in which case the OOD correction would
have bought nothing. It does not, and the two halves can be read off THE SAME RUN, because
acceptance alone supplies the corrected OOD shape
(`FriLdtExtractDeployed.faithfulExt_accept_gives_cons_shape`). -/

/-- **THE CAMPAIGN'S DEBT, MEASURED.** At the only accepting run of the apex-facing predicate
exhibited anywhere in this tree, ON THAT ONE RUN: the corrected OOD conjuncts HOLD (cons shape, at
the deployed `params.extDeg` width), the LANDED singleton is REFUTED, and the retained
table-opening conjunct FAILS — there is no table opening at all.

So the repair is HALF-REALIZED at the pole, and the outstanding debt is not diffuse: it is exactly
the table-opening conjunct. The OOD lane correction is realized where anything is realizable; the
`tableOpenings` lane is refuted there. That is the sharpest honest statement available about the
state of this campaign, and it is a theorem rather than a caveat paragraph. -/
theorem at_the_only_exhibited_pole_the_repair_is_half_realized :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (W : Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (view : ExtVerifierView Nat) (ood : Nat) (oodRest : List Nat),
      Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core
          A extCore extA W initState logN proof pub view = true
        ∧ proof.oodPoint = ood :: oodRest
        ∧ (ood :: oodRest).length = params.extDeg
        ∧ (∀ o : Nat, proof.oodPoint ≠ [o])
        ∧ (∀ topen : TableOpening Nat, topen ∉ proof.tableOpenings) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, proof, pub,
    view, hacc, hnil⟩ := deployed_accepting_pole_has_no_tableOpenings
  obtain ⟨ood, oodRest, hcons, _, hlen⟩ :=
    Dregg2.Circuit.FriLdtExtractDeployed.faithfulExt_accept_gives_cons_shape perm RATE toNat params
      vk core A extCore extA W initState logN proof pub view hacc
  refine ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, proof, pub,
    view, ood, oodRest, hacc, hcons, hlen, ?_, ?_⟩
  · exact fun o =>
      Dregg2.Circuit.FriLdtExtractDeployed.faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat
        params vk core A extCore extA W initState logN proof pub view hacc o
  · intro topen hmem
    rw [hnil] at hmem
    exact List.not_mem_nil hmem

/-! ## §7 — THE SWEEP TABLE, CONTINUED.

Verdicts extend `PremiseInhabitability` §7. **PROVED UNINHABITABLE** = a machine-checked `Empties` or
point refutation here. **INHABITABLE** = a machine-checked model with the antecedent SATISFIED (never
the cheap model obtained by emptying the antecedent). **UNKNOWN** = the check cannot be run at the
deployed arguments and is recorded as unsettled, not as passing.

| # | class / bundle | file:line | verdict | evidence |
|---|---|---|---|---|
| R1 | the corrected bundles' RETAINED conjunct `topen ∈ tableOpenings` (`FriLdtExtractDeployed.FriLdtExtractV3Cons` `:318`, `FriLdtExtractV3Faithful` `:372`, `ApexOodLaneRepair.FriLdtExtractCons` `:234`, `FriFsDecodedOodRepair.ExtractBundleSansFSCons` `:226` / `DecodedLdtLinkCons` `:438`, `OodSingletonRepair.DecodedLdtLinkExtCons` `:426`) | see left | **PROVED UNINHABITABLE at the only exhibited pole** (schema); **UNKNOWN at `opaque` deployed args** | `deployed_accepting_pole_has_no_tableOpenings` (`FriLdtExtractDeployed.lean`, `decide`-backed accepting run with `tableOpenings = []`) + `tableOpeningMember_forcing_premise_is_false_at_a_real_pole`. The `ℤ`/`Nat` typing gap is stated in §B and NOT papered over: the schema is refuted where anything is exhibitable; the `ℤ` bundle at `opaque` args is not decided by anyone. |
| R2 | `CircuitCompleteness.StarkComplete` | `CircuitCompleteness.lean:147` | **PROVED TO COLLAPSE** when carried with the landed FRI-LDT bundle (upgrade from the earlier `N/A — DUAL DIRECTION`) | `starkComplete_and_landedBundle_forbid_every_satisfying_trace`; `starkComplete_and_landedBundle_empty_the_satisfaction_relation`. The pair forces `RejectsAll` on the satisfaction relation itself. |
| R3 | `AggAirSound.FriExtract` | `AggAirSound.lean:157` | **UNKNOWN at deployment** (never instantiated at the deployed verifier), **BRACKETED** | lower: `deadVerifier_empties_aggFriExtract`; upper: `aggFriExtract_inhabited_nondegenerately` |
| R4 | `GroundedApex.BindingExtract` | `GroundedApex.lean:93` | **UNKNOWN at deployment**, **PROVED FREE (zero information) on non-verifying aggregates** | `bindingExtract_is_free_when_the_binding_proof_fails` |
| R5 | the nine `*LeafFriFloor` classes — `CustomBindingFromFold.lean:83`, `FactoryBindingFromFold.lean:83`, `HatcheryBindingFromFold.lean:73`, `MembershipBindingFromFold.lean:83`, `SovereignBindingFromFold.lean:89`, `DslBindingFromFold.lean:93`, `DecoBindingFromFold.lean:81`, `BridgeBindingFromFold.lean:103`, `BlindedMembershipBindingFromFold.lean:82` | see left | **UNKNOWN at deployment**, **BRACKETED** | shape identity `customLeafFriFloor_iff_extracts`; lower `deadVerifier_empties_leafFloor` / `deadEngine_leafFloor_forbids_satisfaction`; upper `leafFloor_inhabited_nondegenerately`; degenerate-model warning `leafFloor_is_free_when_unsatisfiable`. Only the `Custom` member is instantiated as a theorem — the other eight are the SAME body with the projection renamed (verified by reading each `def`), and are therefore reported as reasoned, not as separately machine-checked. |
| R6 | `AlgoStarkSoundGeneral.BusModelFamily` `:202`, `MemoryLegs` `:219`, `MemMapFree` `:243` | `AlgoStarkSoundGeneral.lean` | NO CONTRADICTION FOUND | every conjunct is about the SKOLEM parameter `tr : BatchPublicInputs → BatchProof → VmTrace`, which the verifier never constrains: no `key`/`shape` pair exists to refute. Same reasoning as `PremiseInhabitability` §7's S1/S3. |
| R7 | `FriDecodedTraceWitness.DecodedBusLink` | `FriDecodedTraceWitness.lean:502` | NO CONTRADICTION FOUND | conclusion is `∃ mult, BusModelOk … (decodedTr …) l.table mult` — about the DECODED trace, not about any verifier-visible field of `(view pi π).1`. NB its sibling `DecodedLdtLink` (`:450`) IS emptied — entry E4. |
| R8 | `DeployedTraceExtract.TraceWitnessed` | `DeployedTraceExtract.lean:176` | NO CONTRADICTION FOUND | `MainAirAcceptF` + legs + `tracePublishedCommit t = pi.toPublished`, all about the existentially bound `t`; the only run-linked conjunct routes through `opaque tracePublishedCommit` (`CircuitSoundness.lean:467`), which acceptance does not constrain. Same verdict as `PremiseInhabitability` §7's S1/S3 and for the same reason. |
| R9 | `FriExtractNonCircular.TranscriptOfPolynomial` | `FriExtractNonCircular.lean:235` | UNKNOWN | its antecedent is `ChildSatColumns`-derived data over an abstract `friAccepts`, with no deployed instantiation; the module itself labels it "open in general". Not settled here. |
| R10 | `Emit/AccumulatorNonRevocationComplete.Accepts` `:381`, `NonMemberWitness` `:92` | see left | UNKNOWN | not examined at the resolution the other entries were; recorded so the sweep's coverage is not overstated. |
| R11 | the THIRTEEN carrier-gated kernels: `Crypto/VerifierKernel.lean:35`, `PortalFloor.lean:77`, `Pedersen.lean:279`, `NonMembership.lean:249`, `Custom.lean:122`, `Deco.lean:285`, `Temporal.lean:130`, `Dfa.lean:188`, `DfaAcceptanceAir.lean:512`, `Cfg.lean:110`, `Bridge.lean:192`, `BlindedSet.lean:177`, `RangeProof.lean:183` | see left | **UNKNOWN at deployment** (no instantiation at any deployed verifier exists in-tree), **PROVED to admit TWO INDEPENDENT VACUITY MODES** | §5. Mode 1 (`falseCarrierMerkleKernel_soundness_never_fires`): `extractable := False` keeps the class inhabited and the derived theorem true while making it unappliable — with the verifier accepting EVERY triple. Mode 2 (`deadVerifierMerkleKernel_soundness_is_vacuous`): the empty-acceptance wound. `the_two_vacuity_modes_are_independent` shows neither check subsumes the other; `CarrierLive` + `carrierLive_fires` is the criterion. AS MEASURED, the one in-tree instance of `MerkleVerifierKernel` passed (`referenceMerkleKernel_carrierLive`) with a carrier that was literally `True` — and so did the OTHER SEVEN reference kernels of the family: `extractable := True` at `VerifierKernel.lean:65`, `NonMembership.lean:467`, `Pedersen.lean:486`, `Custom.lean:300`, `Deco.lean:498`, `Temporal.lean:283`, `Bridge.lean:379`, `BlindedSet.lean:342` (eight for eight; only the Merkle one machine-checked here, the rest READ at those lines). `PortalFloor` is the contrasting in-tree discipline: carrier PROVED at a reference instance and REFUTED at a forge instance. ⚑ **REPAIRED 2026-07-25**: all eight now carry a proved, separately-REFUTED carrier in the PortalFloor style (`referenceMerkleKernel_carrier_has_content` here; `Dregg2/Crypto/CarrierContent.lean` for the criterion + all eight audits). Two MORE `extractable := True` reference instances were found while repairing and are NOT repaired: `RangeProof.lean:432` (whose `binding := True` sits beside it) and `DecoUnforgeable.lean:339`; `Pedersen`'s `binding := True` also remains. The DEPLOYMENT verdict is UNCHANGED — UNKNOWN, toy oracles only. |
| R12 | `Crypto/LightClientUC.ExtractsTo` `:146` (with `Foolable` `:97`) | see left | NOT RE-CHECKED HERE — **already self-checked in-module** | the `Extracts` shape over an abstract `verify`; the module carries its own non-vacuity apparatus — `badNotExtracts` `:244` REFUTES `ExtractsTo` at a concrete broken verifier, `refFoolingBreaksFloor` `:250` fires the contrapositive reduction on it, and `Reference.refResidual` `:371` inhabits the residual at a sound instance. No tooth added rather than duplicate one; recorded so the family is not silently counted as unexamined. |
| R13 | `Realizability/AssemblyRegularCoverage.RangeSoundFor` `:481` | see left | **NOT WOUNDED — companion-checked in-module** (reasoned from the definitions, not re-proved here) | it is paired with `CompleteFor` `:476` (`∀ x, ∃ proof, V.verify (f x) proof = true`), which ASSERTS the accepting set is inhabited — precisely the companion the FRI bundles lack — and the module exhibits a complete-but-range-unsound backend (`alwaysAcceptBool_not_rangeSound`), so the pair is discriminating rather than decorative. |
| R14 | `Circuit/AirSoundness.airChecks` `:232` | see left | UNKNOWN | acceptance is DEFINED by an existential requiring the opened trace tail to be `[]` (`openTr com = (⟨old, eff, new⟩, [])`) — the known "one side requires the list empty" shape — but `openTr`/`verifyLD` are abstract parameters with no deployed instantiation, so there is nothing to refute against. Flagged, not settled. |
| R15 | `AssuranceCaseGrounded.BroaderCryptoReductionSuite.bls_quorum` `:337` | see left | UNKNOWN | `cert.accepts → cert.SnarkContract → cert.BlsContract → ∃ S, …` is the shape, at the top-level assurance case; inhabitability of `accepts ∧ SnarkContract ∧ BlsContract` was not examined. Recorded as unexamined. |
| R16 | `Spec/VatBoundary.PhiFunctorial.preserves_id` `:359` | see left | UNKNOWN | `confers c c → ∃ w, Guard.admits (phiMor c) req w = true`: the shape with a CONFERRAL antecedent rather than verifier acceptance. Not examined. |
| R17 | the tree's OWN non-vacuity disciplines, recorded as the positive controls | `Bridge/VerifiedLightClient.lean:141`; `Circuit/RotatedKernelRefinementNotesFreshBridge.lean:191`; `Crypto/PortalFloor.lean:482` | **CLEAN — and these are what the FRI apex was missing** | `VerifiedLightClient.NonVacuous verify := ∃ ts u₁ u₂, verify ts u₁ = true ∧ verify ts u₂ = false` is a REQUIRED FIELD of `ForeignLightClient`, so no chain instance exists until acceptance is proved DISCRIMINATING (`discriminating_not_rejectsAll`, §5, is that condition in this module's vocabulary). `NoteFreshAccepts` is an existential acceptance predicate whose module proves the ⟸ direction CONSTRUCTIVELY (`gapOpen_complete`), which is an inhabitability proof by another name. `PortalFloor`'s forge instances refute each carrier. Three working precedents; the STARK/FRI bundle family had none of them. |
| R18 | `ShieldedMerkleRootPin.AccumulatorSound` `:252` — RE-EXAMINED (`PremiseInhabitability` §7's S7 read it as an abstract class and returned NO CONTRADICTION FOUND) | see left | **SETTLED IN-MODULE, and the deployment answer is NEGATIVE** — not UNKNOWN | at the DEPLOYED on-ramp shape the premise is already PROVED FALSE in-tree: `ShieldedOnRampPin.deployed_append_unsound` `:277` gives `¬ AccumulatorSound (Hair hash) (IsLedgerNote hash auth) (rootAfterAppend …)` for any non-ledger wire value, sharpened to today's population by `nothing_is_authorized_today` `:290` / `deployed_append_unsound_today` `:298`. Conditional inhabitation exists at the faithful realization (`ShieldedSpendPortResidual.accumulatorSound_of_hashFloor` `:383`, from a `FoldReachIsMember` floor). And the derived `IsCommittedNote` instance is SELF-FLAGGED vacuous: `noteAccumulatorCR_of_hashFloor` `:398` holds at EVERY root — including a prover-written one — under `ShieldedOnRampPin.C6Surjective` `:351` (`:381` says so in the module's own words). S7's verdict was right about the abstract class and would have been wrong as a deployment verdict; this row is the correction. |
| N/A | scanner false positives, recorded so the enumeration is auditable: the nine `Sat*Fold` structures (`CustomBindingFromFold.lean:126` and siblings — conjunctions of fold facts, no acceptance antecedent), `FriVerifierBridge.DeployedRefines:92` (accept → accept, no existential), `Lightclient/MMR.CommitBindsMMR:511` (an equation), `Exec/CustodyReceipt.receiptUnforgeable:301` (`sig = true → presenter = relay`, no existential), `Bridge/LightClientEth.EthValidAt:429` (a validity structure), `Crypto/HermineDkg.feldmanVerify:128`, and this module's own `PremiseInhabitability.consShape:664` | see left | N/A — NOT the accepts-implies-exists shape | read individually |

**Enumeration method, so coverage is auditable rather than asserted.** A mechanical scan of every
`Prop`-valued `class`/`structure`/`def`/`abbrev` under `metatheory/Dregg2/` for an acceptance-shaped
antecedent (`= true →`, `Accepts →`, `verify … →`) followed by an existential yielded **39** candidate
declarations. Every one is accounted for above by name or by family: 8 in the FRI/OOD bundle family
(E1–E5, R1), 4 apex soundness classes (S1, S2, S3, S8), 3 carrier-gated kernels found by the scan plus
10 more found by grepping `extractable : Prop` (R11), 2 in `LightClientUC` (R12), 9 `Sat*Fold` false
positives, and one each for R4, R13, R14, R15, R16 and the remaining N/A rows. The scan is a
STRUCTURAL filter: a bundle written in an unusual idiom could evade it, and no claim is made that 39
is the true total.

**Not claimed.** No entry asserts that any bundle IS satisfiable at the deployed configuration.
`cfgPerm`/`cfgParams`/`cfgView`/… are `opaque`. R1 is the sharpest NEGATIVE result available and it
is a result about the campaign's OWN repair, not about the landed wound: the repair's surviving
table-opening conjunct is refuted at the only run anyone can exhibit. -/

#assert_axioms yieldsAt_of_extracts
#assert_axioms yieldsAt_of_yieldsShape
#assert_axioms not_of_yieldsAt_refutedAt
#assert_axioms empties_of_yieldsAt
#assert_axioms not_of_empties_at_pole
#assert_axioms not_of_yieldsAt_refutedAt_imp
#assert_axioms not_of_tableOpeningYield_at_empty_pole
#assert_axioms tableOpeningMember_forcing_premise_is_false_at_a_real_pole
#assert_axioms starkComplete_and_landedBundle_forbid_every_satisfying_trace
#assert_axioms starkComplete_and_landedBundle_empty_the_satisfaction_relation
#assert_axioms customLeafFriFloor_iff_extracts
#assert_axioms deadVerifier_empties_leafFloor
#assert_axioms deadEngine_leafFloor_forbids_satisfaction
#assert_axioms leafFloor_inhabited_nondegenerately
#assert_axioms leafFloor_is_free_when_unsatisfiable
#assert_axioms deadVerifier_empties_aggFriExtract
#assert_axioms aggFriExtract_inhabited_nondegenerately
#assert_axioms bindingExtract_is_free_when_the_binding_proof_fails
#assert_axioms falseCarrier_proves_anything
#assert_axioms rejectsAll_proves_anything
#assert_axioms carrierLive_excludes_falseCarrier
#assert_axioms carrierLive_excludes_rejectsAll
#assert_axioms carrierLive_fires
#assert_axioms discriminating_not_rejectsAll
#assert_axioms discriminating_not_total
#assert_axioms falseCarrierMerkleKernel_accepts_everything
#assert_axioms falseCarrierMerkleKernel_acceptsSome
#assert_axioms falseCarrierMerkleKernel_carrier_false
#assert_axioms falseCarrierMerkleKernel_soundness_never_fires
#assert_axioms deadVerifierMerkleKernel_carrier_holds
#assert_axioms deadVerifierMerkleKernel_rejectsAll
#assert_axioms deadVerifierMerkleKernel_soundness_is_vacuous
#assert_axioms the_two_vacuity_modes_are_independent
#assert_axioms referenceMerkleKernel_accepts_a_run
#assert_axioms referenceMerkleKernel_carrierLive
#assert_axioms referenceMerkleKernel_carrier_has_content
#assert_axioms at_the_only_exhibited_pole_the_repair_is_half_realized

end Dregg2.Circuit.PremiseInhabitabilitySweep
