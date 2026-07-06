/-
# Metatheory.Adversary.Instances — the WHOLE deployed assurance case, as `GovernedDynamics`.

ELEVATED ASSURANCE, Pillar 2 — the FULL FLOWERING of `Schema.lean`'s `governed_holds`.

`Schema.lean` collapsed non-domination (`polisDynamics`) and light-client-unfoolability
(`circuitDynamics`) into instances of ONE schema `GovernedDynamics` = (Control, run, accept,
invariant, holds : GovernedProperty), consumed by ONE lemma `governed_holds`. This module carries
that unification to the END: EVERY remaining load-bearing deployed guarantee is re-stated as a
`GovernedDynamics` instance whose `holds` field IS the deployed theorem (reused, not re-proven), and
the guarantee-against-the-adversary is derived as a `governed_holds` application. The payoff
(`assurance_case_governed`) runs the WHOLE family through the single lemma against one `Adversary`.

THE INSTANCES (each: `run`, `accept`, `invariant`; `holds :=` the deployed theorem):

  1. `settlementDynamics`  — `Metatheory.SettlementSoundness.settlement_soundness`. Control = the
     settlement inputs (topology/log/held/tip/exercised-cap); accept = the turn SETTLES (`S …`);
     invariant = the exercised authority is LIVE at the settlement tip (`LiveAtTip`). Fits with NO
     distortion: `settlement_soundness hbind` IS the `holds` proof.

  2. `wholeHistoryDynamics` — `RecursiveAggregation.light_client_verifies_anchored_history`. Control
     = the presented aggregate (agg/g/steps); accept = the succinct root verifies AND the public
     genesis is the client's trusted anchor (with the named realizability floor `EngineSound` folded
     into accept — the same faithful move `circuitDynamics` made with `WitnessDecodes`); invariant =
     the whole history is genuine + complete-from-the-anchored-genesis (`AnchoredAttests`).

  3. the 8 CARRIER dynamics (`custom`/`factory`/`sovereign`/`membership`/`dsl`/`bridge`/`hatchery`/
     `deco`) — each `*_binding_from_fold`. Control = the per-turn fold face the prover presents;
     accept = the carrier's deployed fold leg is SATISFIED (`Sat*Fold`); invariant = the backing is
     GENUINE (∃ a verifying sub-proof exposing the published commitment) AND anti-ghost (the attested
     VK/nullifier/intent is determined). The in-AIR crypto floor (the FRI leaf floor `hfri`,
     Poseidon2-CR `hCR`, the engine factoring) is fixed when the instance is built.

  4. `assuranceApexDynamics` — `AssuranceCase.deployed_system_secure`, THE composed 5-guarantee apex.
     Control = the deployed turn's committed products (forest, noteSpend, aggregate); accept = the
     forest executed, the noteSpend committed, and the light client verified the aggregate root (with
     the named coverage/soundness/structure seams `hcov`/`EngineSound`/`KernelGenesisPin`/`SeamStruct`
     folded into accept); invariant = A∧B∧C∧D∧E (non-amp, conservation, integrity, freshness,
     unfoolability) hold AT ONCE over that one turn.

FIT / SEAMS (the honest finding, per instance):
  * settlement — fits cleanly, no folded seam (`BindsLiveAuthority` is the deployed predicate's own
    binding discipline, carried as the fixed hypothesis, exactly as the crypto floors are).
  * whole-history — one NAMED folded seam: `EngineSound` (the recursion/leaf/binding soundness) is
    per-presentation, so it rides IN `accept` (faithful — the prover committed to a sound engine for
    the aggregate it publishes; the exact analog of `WitnessDecodes` in `circuitDynamics`).
  * carriers — fit cleanly; the crypto floor is global (fixed at build), the connect rides `accept`
    via `Sat*Fold` (the satisfying aggregate's in-circuit trace).
  * apex — three NAMED folded seams in `accept`: the per-step coverage `hcov` (`EachStepMemProg`),
    the engine soundness `EngineSound`, and the genesis/structure `KernelGenesisPin`/`SeamStruct` —
    each already an explicit hypothesis of `deployed_system_secure`, folded faithfully.

ANTI-VACUITY (per instance — reusing the deployed teeth, never a `P → P`):
  * settlement — a revoked-at-the-tip cap is REJECTED by accept AND excluded by the invariant
    (`settlement_accept_bites` / the `deployedSettle_nonvacuous` witnesses).
  * whole-history — a non-verifying root is rejected by accept; a fabricated genesis is excluded by
    the invariant (`wholeHistory_accept_bites` / `wholeHistory_invariant_bites`).
  * carriers — a forged (unbacked) fold is rejected by accept (`*_binding`'s `forged_unsat`) AND
    excluded by the invariant; the shipped `forged_*_unsat_demo` are the concrete inhabitants.
  * apex — inherits every leg's teeth; the invariant is the load-bearing 5-conjunction (each leg
    proven non-vacuous in `AssuranceCase`).

Kernel-clean: every `holds` field is a deployed proof. `#assert_axioms` at the foot.
-/
import Metatheory.Adversary.Schema
import Dregg2.AssuranceCase
import Metatheory.SettlementSoundness
import Dregg2.Circuit.RecursiveAggregation
import Dregg2.Circuit.CustomBindingFromFold
import Dregg2.Circuit.FactoryBindingFromFold
import Dregg2.Circuit.SovereignBindingFromFold
import Dregg2.Circuit.MembershipBindingFromFold
import Dregg2.Circuit.DslBindingFromFold
import Dregg2.Circuit.BridgeBindingFromFold
import Dregg2.Circuit.HatcheryBindingFromFold
import Dregg2.Circuit.DecoBindingFromFold
import Dregg2.Crypto.DecoUnforgeable
import Dregg2.Crypto.DecoUC

namespace Metatheory.Adversary

set_option linter.dupNamespace false
set_option linter.unusedVariables false

open Dregg2.Exec (RecChainedState)
open Dregg2.Distributed.HistoryAggregation (ChainStep KernelGenesisPin SeamStruct)

/-! ## §1. Instance — SETTLEMENT SOUNDNESS. Fits cleanly (no folded seam). -/

open Metatheory.SettlementSoundness
open Metatheory.KeyLeak (Topo RevEvent CList reaches honors)

/-- The settlement control surface: the topology, the finalized revocation log, the held c-list, the
settlement tip, and the exercised authorized cap — the inputs `settlement_soundness` ranges over. -/
structure SettleControl where
  T : Topo
  log : List RevEvent
  held : CList
  tip : Tip
  ac : AuthCap

/-- **`settlementDynamics hbind`** — `settlement_soundness` as a `GovernedDynamics`. Control = the
settlement inputs; accept = the turn SETTLES under the predicate `S` (`S T log held tip ac`);
invariant = the exercised authority is LIVE at the settlement tip (`LiveAtTip` — held-as-attenuation
AND honored-at-the-tip). `settlement_soundness hbind` IS the `holds` proof. Fits with NO distortion:
`BindsLiveAuthority` is the deployed predicate's own binding discipline, fixed at build (like a
crypto floor), not a per-control hypothesis folded into accept. -/
def settlementDynamics {S : SettlePred} (hbind : BindsLiveAuthority S) : GovernedDynamics where
  Control := SettleControl
  Outcome := SettleControl
  run c := c
  accept c := S c.T c.log c.held c.tip c.ac
  invariant c := LiveAtTip c.T c.log c.held c.tip c.ac
  holds c h := settlement_soundness hbind c.T c.log c.held c.tip c.ac h

/-- **SETTLEMENT SOUNDNESS, via the ONE lemma.** A settled turn exercised authority live at the
settlement tip — as an application of `governed_holds` to `settlementDynamics`. This IS
`settlement_soundness`, factored through the shared schema. -/
theorem settlement_soundness_via_schema {S : SettlePred} (hbind : BindsLiveAuthority S)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : S T log held tip ac) :
    LiveAtTip T log held tip ac :=
  governed_holds (settlementDynamics hbind) ⟨T, log, held, tip, ac⟩ hsettled

/-- ANTI-VACUITY (settlement). On the DEPLOYED settlement, the accept predicate genuinely REJECTS a
control (a cap revoked-at-the-tip does NOT settle) AND the invariant genuinely CONSTRAINS (that same
cap is NOT live at the tip). Reuses the deployed `deployedSettle_nonvacuous` / gate teeth. -/
theorem settlement_accept_bites :
    ¬ (settlementDynamics deployedSettle_binds_live_authority).accept
        ⟨KeyLeak.demoTopo, demoLog', demoHeld, deadTip, demoAc⟩ := by
  show ¬ deployedSettle KeyLeak.demoTopo demoLog' demoHeld deadTip demoAc
  exact deployedSettle_nonvacuous.2

theorem settlement_invariant_bites :
    ¬ (settlementDynamics deployedSettle_binds_live_authority).invariant
        ⟨KeyLeak.demoTopo, demoLog', demoHeld, deadTip, demoAc⟩ := by
  -- invariant = LiveAtTip = liveSettlement (definitionally); reuse the deployed FALSE-side tooth.
  show ¬ LiveAtTip KeyLeak.demoTopo demoLog' demoHeld deadTip demoAc
  exact demo_unsettleable_when_revoked

/-- **(SATISFIABILITY — settlement, PROVEN concrete).** `accept c := deployedSettle c.T …` is INHABITED:
the same demo cap that `deployedSettle_nonvacuous` shows settles inside the stale window is a concrete
accepted control. So `∃ c, accept (run c)` — the settlement guarantee is not vacuously governed. Reuses
`deployedSettle_nonvacuous.1` (the deployed TRUE-side witness). -/
theorem settlement_accept_satisfiable :
    ∃ c, (settlementDynamics deployedSettle_binds_live_authority).accept
      ((settlementDynamics deployedSettle_binds_live_authority).run c) :=
  ⟨⟨KeyLeak.demoTopo, demoLog', demoHeld, liveTip, demoAc⟩, deployedSettle_nonvacuous.1⟩

/-! ## §2. Instance — WHOLE-HISTORY (light client verifies the whole history, anchored). -/

open Dregg2.Circuit.RecursiveAggregation

/-- The whole-history control surface: the aggregate the prover publishes, its genesis kernel state,
and the folded step list — the objects `light_client_verifies_anchored_history` ranges over. -/
structure WHControl (Proof : Type) where
  agg : Aggregate Proof
  g : RecChainedState
  steps : List ChainStep

/-- **`wholeHistoryDynamics …`** — `light_client_verifies_anchored_history` as a `GovernedDynamics`.
Control = the presented aggregate; accept = the succinct root verifies AND the public genesis is the
client's trusted anchor `expectedGenesis`, WITH the named realizability floor `EngineSound` folded in
(the recursion/leaf/binding soundness the prover commits to — the faithful analog of
`WitnessDecodes` in `circuitDynamics`); invariant = the whole history is genuine and
complete-from-the-anchored-genesis (`AnchoredAttests`). `light_client_verifies_anchored_history` IS
the `holds` proof. The commitment portal floors `(CH, RH, cmb, compress, compressN)` and the trusted
`expectedGenesis` are fixed at build (the verifier's config, like the VK). -/
def wholeHistoryDynamics (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (expectedGenesis : ℤ) : GovernedDynamics where
  Control := WHControl Proof
  Outcome := WHControl Proof
  run c := c
  accept c := EngineSound Proof verify CH RH cmb compress compressN c.agg c.g c.steps
    ∧ verify c.agg.root = true ∧ c.agg.genesisRoot = expectedGenesis
  invariant c := AnchoredAttests Proof CH RH cmb compress compressN c.agg c.g c.steps expectedGenesis
  holds c h := light_client_verifies_anchored_history Proof verify CH RH cmb compress compressN
    c.agg c.g c.steps expectedGenesis h.1 h.2.1 h.2.2

/-- **WHOLE-HISTORY UNFOOLABILITY, via the ONE lemma.** A light client that verifies the succinct
root and pins the trusted genesis obtains the anchored whole-history attestation — as an application
of `governed_holds` to `wholeHistoryDynamics`. This IS `light_client_verifies_anchored_history`,
factored through the shared schema. -/
theorem whole_history_via_schema (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (expectedGenesis : ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) (hanchor : agg.genesisRoot = expectedGenesis) :
    AnchoredAttests Proof CH RH cmb compress compressN agg g steps expectedGenesis :=
  governed_holds (wholeHistoryDynamics Proof verify CH RH cmb compress compressN expectedGenesis)
    ⟨agg, g, steps⟩ ⟨es, hroot, hanchor⟩

/-- ANTI-VACUITY (whole-history), accept. A control whose succinct root does NOT verify is REJECTED
by accept (accept requires `verify agg.root = true`). So accept is not `fun _ => True`: it genuinely
gates on the succinct verification. -/
theorem wholeHistory_accept_bites (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (expectedGenesis : ℤ)
    (c : WHControl Proof) (hbad : verify c.agg.root = false) :
    ¬ (wholeHistoryDynamics Proof verify CH RH cmb compress compressN expectedGenesis).accept c := by
  rintro ⟨_, hroot, _⟩
  rw [hbad] at hroot
  exact Bool.noConfusion hroot

/-- ANTI-VACUITY (whole-history), invariant. A control whose public genesis differs from the trusted
anchor is EXCLUDED by the invariant (`AnchoredAttests.genesis_anchored` would be contradictory). So
the invariant genuinely constrains — it is not satisfied by a fabricated-genesis history. Reuses the
deployed genesis anti-ghost tooth `anchored_attests_rejects_fabricated_genesis`. -/
theorem wholeHistory_invariant_bites (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (expectedGenesis : ℤ)
    (c : WHControl Proof) (hne : c.agg.genesisRoot ≠ expectedGenesis) :
    ¬ (wholeHistoryDynamics Proof verify CH RH cmb compress compressN expectedGenesis).invariant c :=
  fun hinv => anchored_attests_rejects_fabricated_genesis Proof CH RH cmb compress compressN
    c.agg c.g c.steps expectedGenesis hne hinv

/-- **(SATISFIABILITY — whole-history, NAMED FLOOR).** `accept c := EngineSound … ∧ verify root = true ∧
genesisRoot = expectedGenesis` folds the per-presentation realizability floor `EngineSound`. So
`∃ c, accept (run c)` RESTS ON that floor: given a presented aggregate that is engine-sound, verifies,
and anchors to the trusted genesis, accept is inhabited. Named `_of_floor` to make the vacuity risk
VISIBLE — the whole-history guarantee is non-vacuous exactly when an honest sound-engine aggregate for
the anchored genesis exists (the honest prover's own output). -/
theorem wholeHistory_accept_satisfiable_of_floor (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (expectedGenesis : ℤ)
    (c : WHControl Proof)
    (hes : EngineSound Proof verify CH RH cmb compress compressN c.agg c.g c.steps)
    (hroot : verify c.agg.root = true) (hanchor : c.agg.genesisRoot = expectedGenesis) :
    ∃ d, (wholeHistoryDynamics Proof verify CH RH cmb compress compressN expectedGenesis).accept
      ((wholeHistoryDynamics Proof verify CH RH cmb compress compressN expectedGenesis).run d) :=
  ⟨c, hes, hroot, hanchor⟩

/-! ## §3. Instances — THE 8 CARRIER BINDINGS (each `*_binding_from_fold`, from the FOLD).

Each carrier is one child folded into the per-turn aggregate. Control = the fold face the prover
presents; accept = the carrier's deployed fold leg is SATISFIED (`Sat*Fold` — what a verifying
aggregate's in-circuit trace IS, restricted to that face); invariant = the published commitment is
BACKED by a genuine verifying sub-proof AND the attested VK/nullifier/intent is DETERMINED (the
anti-ghost). The in-AIR crypto floor (the FRI leaf floor `hfri`, Poseidon2-CR `hCR`, the engine
factoring `hfactor`/`hvk`/`henc`) is FIXED at build — the standard-crypto carrier, not per-control.
`*_binding_from_fold` IS each `holds`. Anti-vacuity: a forged (unbacked) fold is rejected by accept
(`forged_unsat`) AND excluded by the invariant; the shipped `forged_*_unsat_demo` are the concrete
inhabitants. -/

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DescriptorIR2 (ProofEngine)
open Dregg2.Circuit.BridgeBackingAttack (NoteSpendEngine)
open Dregg2.Circuit.DecoBackingAttack (DecoEngine)
open Dregg2.Circuit.CustomBindingFromFold (CustomFold SatCustomFold CustomLeafFriFloor custom_binding_from_fold)
open Dregg2.Circuit.FactoryBindingFromFold (FactoryFold SatFactoryFold FactoryLeafFriFloor factory_binding_from_fold)
open Dregg2.Circuit.SovereignBindingFromFold (SovereignFold SatSovereignFold SovereignLeafFriFloor sovereign_binding_from_fold)
open Dregg2.Circuit.MembershipBindingFromFold (MembershipFold SatMembershipFold MembershipLeafFriFloor membership_binding_from_fold)
open Dregg2.Circuit.DslBindingFromFold (DslFold SatDslFold DslLeafFriFloor dsl_binding_from_fold)
open Dregg2.Circuit.BridgeBindingFromFold (BridgeFold SatBridgeFold NoteSpendLeafFriFloor bridge_binding_from_fold)
open Dregg2.Circuit.HatcheryBindingFromFold (HatcheryFold SatHatcheryFold ContractLeafFriFloor hatchery_binding_from_fold)
open Dregg2.Circuit.DecoBindingFromFold (DecoFold SatDecoFold DecoLeafFriFloor deco_binding_from_fold)

/-! ### §3.1 — CUSTOM. -/

/-- **`customCarrierDynamics`** — `custom_binding_from_fold` as a `GovernedDynamics`. -/
def customCarrierDynamics (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (CustomLeafSat : ℤ → ℤ → Prop) (hfri : CustomLeafFriFloor E CustomLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    GovernedDynamics where
  Control := CustomFold E
  Outcome := CustomFold E
  run f := f
  accept f := SatCustomFold E CustomLeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.c) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.c → E.piCommit q = f.c → E.vkOf p = E.vkOf q)
  holds f h := custom_binding_from_fold E hash enc CustomLeafSat hfri hCR hfactor hvk f h

/-- CUSTOM backing, via the ONE lemma. -/
theorem custom_backing_via_schema (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (CustomLeafSat : ℤ → ℤ → Prop) (hfri : CustomLeafFriFloor E CustomLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : CustomFold E) (hsat : SatCustomFold E CustomLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.c) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.c → E.piCommit q = f.c → E.vkOf p = E.vkOf q) :=
  governed_holds (customCarrierDynamics E hash enc CustomLeafSat hfri hCR hfactor hvk) f hsat

/-- ANTI-VACUITY (custom): a forged (unbacked) fold is rejected by accept AND excluded by invariant. -/
theorem customCarrier_bites (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (CustomLeafSat : ℤ → ℤ → Prop) (hfri : CustomLeafFriFloor E CustomLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : CustomFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.c) :
    ¬ (customCarrierDynamics E hash enc CustomLeafSat hfri hCR hfactor hvk).accept f ∧
    ¬ (customCarrierDynamics E hash enc CustomLeafSat hfri hCR hfactor hvk).invariant f :=
  ⟨Dregg2.Circuit.CustomBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.2 — FACTORY (child-VK). -/

def factoryCarrierDynamics (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (FactoryLeafSat : ℤ → ℤ → Prop) (hfri : FactoryLeafFriFloor E FactoryLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    GovernedDynamics where
  Control := FactoryFold E
  Outcome := FactoryFold E
  run f := f
  accept f := SatFactoryFold E FactoryLeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.cv) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.cv → E.piCommit q = f.cv → E.vkOf p = E.vkOf q)
  holds f h := factory_binding_from_fold E hash enc FactoryLeafSat hfri hCR hfactor hvk f h

theorem factory_backing_via_schema (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (FactoryLeafSat : ℤ → ℤ → Prop) (hfri : FactoryLeafFriFloor E FactoryLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : FactoryFold E) (hsat : SatFactoryFold E FactoryLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.cv) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.cv → E.piCommit q = f.cv → E.vkOf p = E.vkOf q) :=
  governed_holds (factoryCarrierDynamics E hash enc FactoryLeafSat hfri hCR hfactor hvk) f hsat

theorem factoryCarrier_bites (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (FactoryLeafSat : ℤ → ℤ → Prop) (hfri : FactoryLeafFriFloor E FactoryLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : FactoryFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.cv) :
    ¬ (factoryCarrierDynamics E hash enc FactoryLeafSat hfri hCR hfactor hvk).accept f ∧
    ¬ (factoryCarrierDynamics E hash enc FactoryLeafSat hfri hCR hfactor hvk).invariant f :=
  ⟨Dregg2.Circuit.FactoryBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.3 — SOVEREIGN (key-commit). -/

def sovereignCarrierDynamics (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (SovereignLeafSat : ℤ → ℤ → Prop) (hfri : SovereignLeafFriFloor E SovereignLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    GovernedDynamics where
  Control := SovereignFold E
  Outcome := SovereignFold E
  run f := f
  accept f := SatSovereignFold E SovereignLeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.kc) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.kc → E.piCommit q = f.kc → E.vkOf p = E.vkOf q)
  holds f h := sovereign_binding_from_fold E hash enc SovereignLeafSat hfri hCR hfactor hvk f h

theorem sovereign_backing_via_schema (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (SovereignLeafSat : ℤ → ℤ → Prop) (hfri : SovereignLeafFriFloor E SovereignLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : SovereignFold E) (hsat : SatSovereignFold E SovereignLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.kc) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.kc → E.piCommit q = f.kc → E.vkOf p = E.vkOf q) :=
  governed_holds (sovereignCarrierDynamics E hash enc SovereignLeafSat hfri hCR hfactor hvk) f hsat

theorem sovereignCarrier_bites (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (SovereignLeafSat : ℤ → ℤ → Prop) (hfri : SovereignLeafFriFloor E SovereignLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : SovereignFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.kc) :
    ¬ (sovereignCarrierDynamics E hash enc SovereignLeafSat hfri hCR hfactor hvk).accept f ∧
    ¬ (sovereignCarrierDynamics E hash enc SovereignLeafSat hfri hCR hfactor hvk).invariant f :=
  ⟨Dregg2.Circuit.SovereignBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.4 — MEMBERSHIP (tuple). -/

def membershipCarrierDynamics (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (MembershipLeafSat : ℤ → ℤ → Prop) (hfri : MembershipLeafFriFloor E MembershipLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    GovernedDynamics where
  Control := MembershipFold E
  Outcome := MembershipFold E
  run f := f
  accept f := SatMembershipFold E MembershipLeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.tup) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.tup → E.piCommit q = f.tup → E.vkOf p = E.vkOf q)
  holds f h := membership_binding_from_fold E hash enc MembershipLeafSat hfri hCR hfactor hvk f h

theorem membership_backing_via_schema (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (MembershipLeafSat : ℤ → ℤ → Prop) (hfri : MembershipLeafFriFloor E MembershipLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : MembershipFold E) (hsat : SatMembershipFold E MembershipLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.tup) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.tup → E.piCommit q = f.tup → E.vkOf p = E.vkOf q) :=
  governed_holds (membershipCarrierDynamics E hash enc MembershipLeafSat hfri hCR hfactor hvk) f hsat

theorem membershipCarrier_bites (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (MembershipLeafSat : ℤ → ℤ → Prop) (hfri : MembershipLeafFriFloor E MembershipLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : MembershipFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.tup) :
    ¬ (membershipCarrierDynamics E hash enc MembershipLeafSat hfri hCR hfactor hvk).accept f ∧
    ¬ (membershipCarrierDynamics E hash enc MembershipLeafSat hfri hCR hfactor hvk).invariant f :=
  ⟨Dregg2.Circuit.MembershipBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.5 — DSL (rc). -/

def dslCarrierDynamics (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (DslLeafSat : ℤ → ℤ → Prop) (hfri : DslLeafFriFloor E DslLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    GovernedDynamics where
  Control := DslFold E
  Outcome := DslFold E
  run f := f
  accept f := SatDslFold E DslLeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.rc) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.rc → E.piCommit q = f.rc → E.vkOf p = E.vkOf q)
  holds f h := dsl_binding_from_fold E hash enc DslLeafSat hfri hCR hfactor hvk f h

theorem dsl_backing_via_schema (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (DslLeafSat : ℤ → ℤ → Prop) (hfri : DslLeafFriFloor E DslLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : DslFold E) (hsat : SatDslFold E DslLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.rc) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.rc → E.piCommit q = f.rc → E.vkOf p = E.vkOf q) :=
  governed_holds (dslCarrierDynamics E hash enc DslLeafSat hfri hCR hfactor hvk) f hsat

theorem dslCarrier_bites (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (DslLeafSat : ℤ → ℤ → Prop) (hfri : DslLeafFriFloor E DslLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : DslFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.rc) :
    ¬ (dslCarrierDynamics E hash enc DslLeafSat hfri hCR hfactor hvk).accept f ∧
    ¬ (dslCarrierDynamics E hash enc DslLeafSat hfri hCR hfactor hvk).invariant f :=
  ⟨Dregg2.Circuit.DslBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.6 — HATCHERY (contract). -/

def hatcheryCarrierDynamics (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (ContractLeafSat : ℤ → ℤ → Prop) (hfri : ContractLeafFriFloor E ContractLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    GovernedDynamics where
  Control := HatcheryFold E
  Outcome := HatcheryFold E
  run f := f
  accept f := SatHatcheryFold E ContractLeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.ch) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.ch → E.piCommit q = f.ch → E.vkOf p = E.vkOf q)
  holds f h := hatchery_binding_from_fold E hash enc ContractLeafSat hfri hCR hfactor hvk f h

theorem hatchery_backing_via_schema (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (ContractLeafSat : ℤ → ℤ → Prop) (hfri : ContractLeafFriFloor E ContractLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : HatcheryFold E) (hsat : SatHatcheryFold E ContractLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.ch) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.piCommit p = f.ch → E.piCommit q = f.ch → E.vkOf p = E.vkOf q) :=
  governed_holds (hatcheryCarrierDynamics E hash enc ContractLeafSat hfri hCR hfactor hvk) f hsat

theorem hatcheryCarrier_bites (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (ContractLeafSat : ℤ → ℤ → Prop) (hfri : ContractLeafFriFloor E ContractLeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : HatcheryFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.ch) :
    ¬ (hatcheryCarrierDynamics E hash enc ContractLeafSat hfri hCR hfactor hvk).accept f ∧
    ¬ (hatcheryCarrierDynamics E hash enc ContractLeafSat hfri hCR hfactor hvk).invariant f :=
  ⟨Dregg2.Circuit.HatcheryBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.7 — BRIDGE (note-spend backing the mint). -/

def bridgeCarrierDynamics (E : NoteSpendEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop) (hfri : NoteSpendLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.spendDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.nullifier p = E.nullifier q) :
    GovernedDynamics where
  Control := BridgeFold E
  Outcome := BridgeFold E
  run f := f
  accept f := SatBridgeFold E LeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = f.mintHash) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.spendDigest p = f.mintHash → E.spendDigest q = f.mintHash → E.nullifier p = E.nullifier q)
  holds f h := bridge_binding_from_fold E hash enc LeafSat hfri hCR hfactor henc f h

theorem bridge_backing_via_schema (E : NoteSpendEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop) (hfri : NoteSpendLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.spendDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.nullifier p = E.nullifier q)
    (f : BridgeFold E) (hsat : SatBridgeFold E LeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = f.mintHash) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.spendDigest p = f.mintHash → E.spendDigest q = f.mintHash → E.nullifier p = E.nullifier q) :=
  governed_holds (bridgeCarrierDynamics E hash enc LeafSat hfri hCR hfactor henc) f hsat

theorem bridgeCarrier_bites (E : NoteSpendEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop) (hfri : NoteSpendLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.spendDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.nullifier p = E.nullifier q)
    (f : BridgeFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = f.mintHash) :
    ¬ (bridgeCarrierDynamics E hash enc LeafSat hfri hCR hfactor henc).accept f ∧
    ¬ (bridgeCarrierDynamics E hash enc LeafSat hfri hCR hfactor henc).invariant f :=
  ⟨Dregg2.Circuit.BridgeBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.8 — DECO (payment backing). -/

def decoCarrierDynamics (E : DecoEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop) (hfri : DecoLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.paymentDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.paymentIntent p = E.paymentIntent q) :
    GovernedDynamics where
  Control := DecoFold E
  Outcome := DecoFold E
  run f := f
  accept f := SatDecoFold E LeafSat f
  invariant f := (∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = f.paymentHash) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.paymentDigest p = f.paymentHash → E.paymentDigest q = f.paymentHash → E.paymentIntent p = E.paymentIntent q)
  holds f h := deco_binding_from_fold E hash enc LeafSat hfri hCR hfactor henc f h

theorem deco_backing_via_schema (E : DecoEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop) (hfri : DecoLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.paymentDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.paymentIntent p = E.paymentIntent q)
    (f : DecoFold E) (hsat : SatDecoFold E LeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = f.paymentHash) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
      E.paymentDigest p = f.paymentHash → E.paymentDigest q = f.paymentHash → E.paymentIntent p = E.paymentIntent q) :=
  governed_holds (decoCarrierDynamics E hash enc LeafSat hfri hCR hfactor henc) f hsat

theorem decoCarrier_bites (E : DecoEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop) (hfri : DecoLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash) (hfactor : ∀ p, E.verify p = true → E.paymentDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.paymentIntent p = E.paymentIntent q)
    (f : DecoFold E) (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.paymentDigest q = f.paymentHash) :
    ¬ (decoCarrierDynamics E hash enc LeafSat hfri hCR hfactor henc).accept f ∧
    ¬ (decoCarrierDynamics E hash enc LeafSat hfri hCR hfactor henc).invariant f :=
  ⟨Dregg2.Circuit.DecoBindingFromFold.forged_unsat hfri hforge, fun h => hforge h.1⟩

/-! ### §3.9 — DECO ATTESTATION UNFORGEABILITY (rung 4: the crypto floor BENEATH the payment carrier).

`decoCarrierDynamics` (§3.8) binds "the mint's published `payment_hash` is BACKED by a verifying DECO
sub-proof" (the fold-binding). This instance is the DISTINCT, COMPOSING leg beneath it: "a verifying
DECO sub-proof MEANS a genuine Stripe session" — the unforgeability of the attestation itself
(`Dregg2/Crypto/DecoUnforgeable.lean`). Composed: attestation-unforgeability ∘ carrier-backing = the
mint credited REAL money (the two legs `DecoBackingAttack.deployed_admits_unbacked_deco` shows are
BOTH needed). This supplies the second.

`accept` = the deployed DECO verifier accepts the presented `(stmt, proof)`; `invariant` =
`decoAuthenticated` (F_attestation would emit — a genuine Stripe-authenticated non-zero payment);
`holds` = `deco_attestation_realizes` (the §8 carriers are FIXED at instance build, exactly as
`circuitDynamics`'s crypto floors are — not per-control). -/

open Dregg2.Crypto.Deco (Statement DecoVerifierKernel)
open Dregg2.Crypto.PortalFloor (SignatureKernel MacKernelE)
open Dregg2.Crypto.DecoUnforgeable (decoAuthenticated deco_attestation_realizes)

/-- **`attestationDynamics`** — DECO attestation unforgeability as a `GovernedDynamics`. Control = the
`(stmt, proof)` the prover presents; `holds` IS `deco_attestation_realizes`. A NEW instance beside
`decoCarrierDynamics`, not a rewrite. -/
def attestationDynamics {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable) :
    GovernedDynamics where
  Control := Statement Dg × Proof
  Outcome := Statement Dg × Proof
  run c := c
  accept c := KD.verify c.1 c.2 = true
  invariant c := decoAuthenticated SK MK KD.compress KD.encode c.1
  holds c h := deco_attestation_realizes (KD := KD) SK MK hsigEq hmacEq hext hsig hmac c.1 c.2 h

/-- **DECO ATTESTATION UNFORGEABILITY, via the ONE lemma.** An accepting DECO proof means a genuine
Stripe session backs the statement — as an application of `governed_holds` to `attestationDynamics`.
This IS `deco_attestation_realizes`, factored through the shared schema. -/
theorem deco_attestation_via_schema {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (stmt : Statement Dg) (proof : Proof) (hacc : KD.verify stmt proof = true) :
    decoAuthenticated SK MK KD.compress KD.encode stmt :=
  governed_holds (attestationDynamics SK MK hsigEq hmacEq hext hsig hmac) (stmt, proof) hacc

/-- **The instance's `invariant` genuinely CONSTRAINS** (schema-level anti-vacuity, distinct from the
`decoCarrier_bites` fold tooth): at the forge kernel the ground truth is FALSE — `decoAuthenticated`
does NOT hold for the sample, so the invariant is not `True`. The forgery-side teeth
(`Forge.attestation_bites` / `Forge.attestation_bites_is_sig_forgery`) live in `DecoUnforgeable`; a
broken floor cannot even build `attestationDynamics` (its `holds` demands the carriers hold — the
`GovernedDynamics` anti-vacuity discipline). -/
theorem attestation_invariant_bites :
    ¬ decoAuthenticated Dregg2.Crypto.DecoUnforgeable.Forge.forgeSigKernel
        Dregg2.Crypto.Deco.Reference.refMacKernel
        Dregg2.Crypto.DecoUnforgeable.Forge.forgeDeco.compress
        Dregg2.Crypto.DecoUnforgeable.Forge.forgeDeco.encode
        Dregg2.Crypto.Deco.Reference.sampleStmt :=
  Dregg2.Crypto.DecoUnforgeable.Forge.forge_attestation_forgery.2

/-- **(SATISFIABILITY — attestation, PROVEN concrete).** `accept c := KD.verify c.1 c.2 = true` is
INHABITED at the reference DECO kernel: the disclosed sample statement with the simulator's witness-free
transcript is accepted (`DecoUC.decoSim_works.2`). So `∃ c, accept (run c)` — the attestation guarantee
(and the rung-5 wrapper `attestationUCDynamics`, whose accept is identical) is not vacuously governed.
The reference §8 carriers are the toy witnesses (`rfl`/`trivial`), exactly as in `DecoUC.ref_ucRealizes`. -/
theorem attestation_accept_satisfiable :
    ∃ c, (attestationDynamics (KD := Dregg2.Crypto.Deco.Reference.refKernel)
        Dregg2.Crypto.Deco.Reference.refSigKernel Dregg2.Crypto.Deco.Reference.refMacKernel
        rfl rfl trivial (fun _ _ _ h => of_decide_eq_true h) trivial).accept
      ((attestationDynamics (KD := Dregg2.Crypto.Deco.Reference.refKernel)
        Dregg2.Crypto.Deco.Reference.refSigKernel Dregg2.Crypto.Deco.Reference.refMacKernel
        rfl rfl trivial (fun _ _ _ h => of_decide_eq_true h) trivial).run c) :=
  ⟨(Dregg2.Crypto.Deco.Reference.sampleStmt, ()), Dregg2.Crypto.DecoUC.decoSim_works.2⟩

/-! ### §3.9b — DECO ATTESTATION: the rung-4 soundness leg re-exported (NOT a rung-5 summit).

⚑ RELABELED after the meta-review (`docs/audit/META-REVIEW-STATEMENTS.md` §1): what was presented here as
"rung 5, the UC-realization summit above rung 4" is, in Lean, rung-4 soundness re-exported under the UC
name. `DecoUC.UCRealizesFAtt` is now DEFINITIONALLY `AttRealizes` (its formerly-shipped `rfl`-vacuous
ZK conjunct was removed), and its computational carriers are `True`/`trivial` in every builder. So
`attestationUCDynamics` delivers the SAME invariant `decoAuthenticated` as the rung-4 `attestationDynamics`
(§3.9), routed through `DecoUC.decoUC_realization_of_discharge` — a WRAPPER, not a distinct guarantee. It
is kept (not deleted) so the manifest can name it truthfully as a wrapper-of-22 whose computational-UC
content is UNBUILT. The genuine computational summit needs the spmf / process-calculus framework named in
`DecoUC.lean`'s header. -/

open Dregg2.Crypto.DecoUC (decoUC_realization decoUC_realization_of_discharge
  DecoUCComputationalDischarge UCRealizesFAtt decoUC_realizes)

/-- **`attestationUCDynamics`** — the rung-4 soundness leg routed through the UC wrapper as a
`GovernedDynamics`. Control = the `(stmt, proof)` presented; invariant = `decoAuthenticated` (the ideal
emission); `holds` is the `soundness` leg of the assembled `DecoUCRealization`, the computational
discharge FIXED at build. ⚑ NOT above `attestationDynamics` (rung 4) in content: since `UCRealizesFAtt`
is definitionally `AttRealizes` and the computational carriers are `True`, this delivers the SAME
invariant via a wrapper — a truthfully-named re-export, not a distinct summit. -/
def attestationUCDynamics {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (d : DecoUCComputationalDischarge) :
    GovernedDynamics where
  Control := Statement Dg × Proof
  Outcome := Statement Dg × Proof
  run c := c
  accept c := KD.verify c.1 c.2 = true
  invariant c := decoAuthenticated SK MK KD.compress KD.encode c.1
  holds c h :=
    (decoUC_realization_of_discharge (KD := KD) SK MK hsigEq hmacEq hext hsig hmac d).soundness
      c.1 c.2 h

/-- **DECO ATTESTATION UC-REALIZATION, via the ONE lemma.** An accepting DECO proof means a genuine
Stripe session backs the statement — delivered AS the soundness leg of a UC realization, as an
application of `governed_holds` to `attestationUCDynamics` (rung 5). -/
theorem deco_attestation_uc_via_schema {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (d : DecoUCComputationalDischarge)
    (stmt : Statement Dg) (proof : Proof) (hacc : KD.verify stmt proof = true) :
    decoAuthenticated SK MK KD.compress KD.encode stmt :=
  governed_holds (attestationUCDynamics SK MK hsigEq hmacEq hext hsig hmac d) (stmt, proof) hacc

/-- **The re-exported soundness leg, factored:** given the §8 carriers, the deployed verifier satisfies
`UCRealizesFAtt`. ⚑ Since `UCRealizesFAtt` is now DEFINITIONALLY `AttRealizes` (the vacuous ZK conjunct
removed) and the computational carriers below are all `True`, this concludes EXACTLY the rung-4 soundness
`deco_attestation_via_schema` already gives — it is NOT a distinct summit. Kept under the historic name
so the audit trail is legible; see `docs/audit/NON-VACUITY-MANIFEST.md` row 23 (wrapper-of-22). -/
theorem deco_attestation_uc_realizes {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable) :
    UCRealizesFAtt KD.verify (decoAuthenticated SK MK KD.compress KD.encode) :=
  decoUC_realizes _ _ (decoUC_realization SK MK hsigEq hmacEq hext hsig hmac
    True True True True True trivial trivial trivial trivial trivial)

/-! ## §4. Instance — THE COMPOSED APEX (`AssuranceCase.deployed_system_secure`).

The marquee: the whole deployed 5-guarantee theorem (A non-amplification, B conservation, C
integrity, D freshness, E unfoolability) — over ONE committed turn — as a single `GovernedDynamics`.
Control = the deployed turn's committed products (the running-entry forest, the noteSpend, the
published aggregate); accept = the forest EXECUTED, the noteSpend committed, and the light client
VERIFIED the aggregate root, WITH three NAMED folded seams — the per-step coverage `hcov`
(`EachStepMemProg`), the engine soundness `EngineSound`, and the genesis/structure floors
(`KernelGenesisPin`/`SeamStruct`) — each already an explicit hypothesis of `deployed_system_secure`,
folded into accept faithfully; invariant = A∧B∧C∧D∧E hold AT ONCE over that one turn. The commitment
portal + injectivity floors (`UC`, `compressInjective`, `cellLeafInjective`, `RestHashIffFrame`) are
FIXED at build. `deployed_system_secure` IS the `holds` proof. -/

section Apex

open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.ForestMemoryProgram (EachStepMemProg MemProgTrans)
open Dregg2.Exec.UniversalBridge (UCodec)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Distributed.HistoryAggregation (lastStateOf)

variable {Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable [Dregg2.Laws.Verifiable Stmt Wit] [DecidableEq Tag]
variable [Dregg2.Authority.CaveatChain.MacKernel (Dregg2.Authority.CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]
variable {AProof : Type} (verify : AProof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- The deployed turn's committed products — the ONE subject the apex is a statement about. -/
structure DeployedControl where
  s : RecChainedState
  s' : RecChainedState
  f : @FullForestG Digest Proof Request Stmt Wit CellId Rights Ctx Gateway _ _ Bytes Tag
  b : Dregg2.Exec.AssetId
  nf : Nat
  k : Dregg2.Exec.RecordKernelState
  k' : Dregg2.Exec.RecordKernelState
  agg : Aggregate AProof
  g : RecChainedState
  steps : List ChainStep

/-- **`assuranceApexDynamics`** — `deployed_system_secure` as a `GovernedDynamics`. -/
def assuranceApexDynamics
    (UC : UCodec) (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) : GovernedDynamics where
  Control := @DeployedControl Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag
    _ _ AProof
  Outcome := @DeployedControl Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag
    _ _ AProof
  run c := c
  accept c :=
    execFullForestG c.s c.f = some c.s'
    ∧ EachStepMemProg UC (lowerForestG c.f)
    ∧ Dregg2.Circuit.Argus.interp (Dregg2.Circuit.Argus.noteSpendStmt c.nf) c.k = some c.k'
    ∧ EngineSound AProof verify CH RH cmb compress compressN c.agg c.g c.steps
    ∧ verify c.agg.root = true
    ∧ Dregg2.Distributed.HistoryAggregation.KernelGenesisPin c.g c.steps
    ∧ Dregg2.Distributed.HistoryAggregation.SeamStruct c.steps
  invariant c :=
    (∀ e ∈ forestEdgesG c.f,
        Dregg2.Authority.capAuthConferred (Dregg2.Exec.attenuate e.1 e.2) ⊆
          Dregg2.Authority.capAuthConferred e.2)
    ∧ Dregg2.Exec.recTotalAsset c.s'.kernel c.b = Dregg2.Exec.recTotalAsset c.s.kernel c.b
    ∧ (∀ p ∈ lowerForestG c.f, ∃ sa sa',
        execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa')
    ∧ MemProgTrans UC c.s c.s'
    ∧ (c.nf ∉ c.k.nullifiers ∧ c.nf ∈ c.k'.nullifiers ∧
        Dregg2.Circuit.Argus.interp (Dregg2.Circuit.Argus.noteSpendStmt c.nf) c.k' = none)
    ∧ AggregateAttests AProof CH RH cmb compress compressN c.agg c.g c.steps
    ∧ Dregg2.Exec.recTotal (lastStateOf c.g c.steps).kernel = Dregg2.Exec.recTotal c.g.kernel
  holds c h :=
    Dregg2.AssuranceCase.deployed_system_secure verify CH RH cmb compress compressN
      c.s c.s' c.f c.b h.1 UC h.2.1 h.2.2.1 c.agg c.g c.steps h.2.2.2.1 h.2.2.2.2.1
      hCmb hCompress hCompressN hLeaf hRest h.2.2.2.2.2.1 h.2.2.2.2.2.2

/-- **THE COMPOSED APEX, via the ONE lemma.** All five deployed guarantees hold at once over the
committed turn — as an application of `governed_holds` to `assuranceApexDynamics`. This IS
`deployed_system_secure`, factored through the shared schema. -/
theorem deployed_system_secure_via_schema
    (UC : UCodec) (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (c : @DeployedControl Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag
      _ _ AProof)
    (hacc : (assuranceApexDynamics verify CH RH cmb compress compressN UC hCmb hCompress hCompressN
      hLeaf hRest).accept c) :
    (assuranceApexDynamics verify CH RH cmb compress compressN UC hCmb hCompress hCompressN
      hLeaf hRest).invariant c :=
  governed_holds (assuranceApexDynamics verify CH RH cmb compress compressN UC hCmb hCompress
    hCompressN hLeaf hRest) c hacc

/-- **(SATISFIABILITY — apex, NAMED FLOOR).** The apex `accept` is a seven-fold conjunction folding the
per-turn realizability floors (`EachStepMemProg` coverage `hcov`, `EngineSound`, `KernelGenesisPin`,
`SeamStruct`). So `∃ c, accept (run c)` RESTS ON that floor: given any committed control that exhibits the
accept conjunction (an honest deployed turn that executes, commits the noteSpend, and whose light client
verifies the anchored aggregate), accept is inhabited. Named `_of_floor` to make the vacuity risk
VISIBLE — the composed five-guarantee apex is non-vacuous exactly when an honest deployed turn realizes
the whole accept floor. -/
theorem apex_accept_satisfiable_of_floor
    (UC : UCodec) (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (c : @DeployedControl Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag
      _ _ AProof)
    (hacc : (assuranceApexDynamics verify CH RH cmb compress compressN UC hCmb hCompress hCompressN
      hLeaf hRest).accept c) :
    ∃ d : @DeployedControl Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag
        _ _ AProof,
      (assuranceApexDynamics verify CH RH cmb compress compressN UC hCmb hCompress hCompressN
        hLeaf hRest).accept
      ((assuranceApexDynamics verify CH RH cmb compress compressN UC hCmb hCompress hCompressN
        hLeaf hRest).run d) :=
  ⟨c, hacc⟩

end Apex

/-! ## §5. THE PAYOFF — the WHOLE assurance case is `governed_holds`, N instances, ONE adversary.

`Schema.lean`'s `adversary_governed_uniformly` ran the polis (non-domination) and circuit
(unfoolability) surfaces of one `Adversary` through `governed_holds`. `assurance_case_governed`
extends that to the FULL family: for ONE adversary `A` and one floor set, non-domination,
light-client-unfoolability, settlement soundness, AND whole-history unfoolability are EACH literally
`governed_holds Dᵢ cᵢ hᵢ` — the entire top-level security of dregg is ONE lemma, applied across the
instance family, over ONE `Adversary` object. The 8 carrier bindings (`custom_backing_via_schema` …
`deco_backing_via_schema`) and the composed apex (`deployed_system_secure_via_schema`) are the SAME
shape — each a `governed_holds` application — completing the flowering. -/

open Dregg2.Circuit.CircuitSoundness
open Metatheory.Polis (SoundPolicy envAct traj)

/-- **`assurance_case_governed`** — the marquee. For EVERY adversary `A` and floor set, the four
top-level deployed guarantees are EACH a `governed_holds` application against the ONE schema:

  * **NON-DOMINATION** — `governed_holds polisDynamics A.opCtrl` (the operator can never push the
    enveloped system out of the floor);
  * **UNFOOLABILITY** — `governed_holds circuitDynamics (A.forgedPI, A.forgedProof)` (a forged
    accepting `(pi, π)` is a genuine kernel step);
  * **SETTLEMENT SOUNDNESS** — `governed_holds settlementDynamics` (a settled turn exercised
    live-at-tip authority);
  * **WHOLE-HISTORY** — `governed_holds wholeHistoryDynamics` (a verified anchored root attests the
    whole history from genesis).

One lemma (`governed_holds`), one adversary (`A`), N instances. -/
theorem assurance_case_governed {State Action : Type}
    -- non-domination floors:
    (step : State → Action → State) (safe : State → Prop)
    (pol : State → Action → Prop) (shield : State → Action) (init : State)
    (sound : SoundPolicy step safe pol) (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
    (initSafe : safe init)
    -- unfoolability floors:
    (hash : List ℤ → ℤ) (Sc : CommitSurface) (R : Registry)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines Sc hash (R e) (kstep e))
    -- settlement floors + control + accept:
    {Sset : SettlePred} (hbind : BindsLiveAuthority Sset) (sc : SettleControl)
    (hset : Sset sc.T sc.log sc.held sc.tip sc.ac)
    -- whole-history floors + control + accept:
    (WProof : Type) (wverify : WProof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (expectedGenesis : ℤ) (wc : WHControl WProof)
    (hwh : EngineSound WProof wverify CH RH cmb compress compressN wc.agg wc.g wc.steps
      ∧ wverify wc.agg.root = true ∧ wc.agg.genesisRoot = expectedGenesis)
    -- THE ONE adversary:
    (A : Adversary State Action) (hwitdec : WitnessDecodes hash R Sc A.forgedPI) :
    (∀ n, safe (traj step (envAct pol shield A.opCtrl) init n))
    ∧ (verifyBatch (vkOfRegistry R) A.forgedPI A.forgedProof = Verdict.accept →
        ∃ pre post : RecChainedState,
          StateDecode Sc A.forgedPI.toPublished pre post ∧
          kstep A.forgedPI.effect pre post ∧
          A.forgedPI.pre = Sc.commit pre.kernel A.forgedPI.turn ∧
          A.forgedPI.post = Sc.commit post.kernel A.forgedPI.turn)
    ∧ LiveAtTip sc.T sc.log sc.held sc.tip sc.ac
    ∧ AnchoredAttests WProof CH RH cmb compress compressN wc.agg wc.g wc.steps expectedGenesis :=
  ⟨governed_holds (polisDynamics step safe pol shield init sound shieldSafe initSafe) A.opCtrl trivial,
   fun hacc => governed_holds (circuitDynamics hash Sc R hCR kstep hrefines)
     (A.forgedPI, A.forgedProof) ⟨hacc, hwitdec⟩,
   governed_holds (settlementDynamics hbind) sc hset,
   governed_holds (wholeHistoryDynamics WProof wverify CH RH cmb compress compressN expectedGenesis)
     wc hwh⟩

/-! ## §6. Axiom hygiene — every via-schema theorem inherits the deployed proof's cleanliness. -/

#assert_axioms settlement_soundness_via_schema
#assert_axioms settlement_accept_bites
#assert_axioms settlement_invariant_bites
#assert_axioms settlement_accept_satisfiable
#assert_axioms whole_history_via_schema
#assert_axioms wholeHistory_accept_bites
#assert_axioms wholeHistory_invariant_bites
#assert_axioms wholeHistory_accept_satisfiable_of_floor
#assert_axioms custom_backing_via_schema
#assert_axioms customCarrier_bites
#assert_axioms factory_backing_via_schema
#assert_axioms factoryCarrier_bites
#assert_axioms sovereign_backing_via_schema
#assert_axioms sovereignCarrier_bites
#assert_axioms membership_backing_via_schema
#assert_axioms membershipCarrier_bites
#assert_axioms dsl_backing_via_schema
#assert_axioms dslCarrier_bites
#assert_axioms bridge_backing_via_schema
#assert_axioms bridgeCarrier_bites
#assert_axioms hatchery_backing_via_schema
#assert_axioms hatcheryCarrier_bites
#assert_axioms deco_backing_via_schema
#assert_axioms decoCarrier_bites
#assert_axioms deco_attestation_via_schema
#assert_axioms attestation_invariant_bites
#assert_axioms attestation_accept_satisfiable
#assert_axioms deco_attestation_uc_via_schema
#assert_axioms deco_attestation_uc_realizes
#assert_axioms deployed_system_secure_via_schema
#assert_axioms apex_accept_satisfiable_of_floor
#assert_axioms assurance_case_governed

end Metatheory.Adversary
