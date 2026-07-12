/-
# `Dregg2.Circuit.AlgoStarkSoundInstance` — DEBT-A COMPOSITION: a REAL `AlgoStarkSound`, no carrier.

## Honest scope (first sentence)

`AlgoStarkSound` IS assembled here as a genuine `instance`-producing theorem with **NO** `AlgoStarkSound`
/ `StarkSound` / `FriExtract` carrier and **NO** `verifyBatch`: `algoStarkSound_of_bricks_transferV3`
concludes the class from an EXPLICIT extraction hypothesis (the FRI-proximity-onto-the-deployed-descriptor
`MainAirAccept`, the LogUp/table `hbus` leg, the two aux-table-emptiness facts, and the `tracePublishedCommit`
link) — chaining the COMMITTED bricks `AirChecksSatisfied.airAccept_forces_satisfied2` /
`AirLegsDischarged.airAccept_forces_satisfied2_transferV3` (which do the real `MainAirAccept ⟹ rowConstraints`
lift). But it is NOT reachable "modulo only floor + DeployedMatchesModel": the FRI-side input `MainAirAccept`
CANNOT be discharged from the committed FRI bricks, because those (`FriProximityBridge.friProximity_bridge`,
`AirSoundness.circuit_sound_via_fri`) land on a DIFFERENT type — the TOY VM `Step`/`satisfiesTransition` /
`CircuitSound` — never on the deployed `VmTrace`/`EffectVmDescriptor2`/`MainAirAccept`. That type mismatch is
the precise unwired seam (documented in §0). So `MainAirAccept` enters as an honest DEPLOYED-MODELING
hypothesis, not laundered through a carrier.

## §0 — THE `CircuitSound ⟶ Satisfied2` SEAM VERDICT (the blocking finding)

The FRI/AIR-proximity chain and the `Satisfied2` chain are DISJOINT developments over DIFFERENT types:

  * **FRI-proximity chain** (`FriProximityBridge` → `AirSoundness.circuit_sound_via_fri`) concludes
        `CircuitSound applyEff (airChecks verifyLD openTr)` over the TOY VM
        `AirSoundness.Step State Effect`, whose payload is `satisfiesTransition applyEff s rest`
        (`allStep` step-gate + `carryChain`) and whose end product is the SINGLE-step
        `new = applyEff eff old`. It never mentions `EffectVmDescriptor2`, `VmTrace`, `MainAirAccept`,
        or `Satisfied2`.

  * **`Satisfied2` chain** (`AirChecksSatisfied.airAccept_forces_satisfied2` →
        `AirLegsDischarged.airAccept_forces_satisfied2_transferV3`) consumes
        `MainAirAccept hash (R pi.effect) t` — an EXISTENTIAL over an opened per-constraint quotient
        `quot` and a recomputed `zerofier` on a deployed `VmTrace t` — and produces the rich
        descriptor predicate `Satisfied2 hash (R pi.effect) minit mfin maddrs t`.

`circuit_sound_via_fri` yields the WEAKER `satisfiesTransition`/`CircuitSound`, NOT the `Satisfied2`
`AlgoStarkSound` needs; and its input `AirSoundness.FriProximity` is over `openTr : Commitment → Step …`,
NOT `MainAirAccept … VmTrace`. There is NO committed term of type
`verifyAlgo … = true → MainAirAccept hash (R pi.effect) t` (nor `… → satisfiesTransition …` at the
DEPLOYED trace). So the FRI legs `hplumb`/`hcode_sat` (which the DEBT-A brief hoped would feed this
composition) CANNOT: they discharge the toy-VM `AirSoundness.FriProximity`, a type that does not unify
with `MainAirAccept`. The composition is blocked at the type boundary; `MainAirAccept` is therefore
carried as an explicit hypothesis (the FRI-proximity-onto-the-deployed-descriptor obligation), which is
genuine DEPLOYED-MODELING work, not a floor and not a mere code-refinement.

## §Hypothesis tally (for `algoStarkSound_of_bricks_transferV3`, the deployed transfer slice)

  * `MainAirAccept hash transferV3 t`              — DEPLOYED-MODELING (FRI-proximity onto the deployed
        `VmTrace`; the committed FRI query-soundness `FriQuerySoundness.deployed_accept_prob_lt` +
        `FriProximityBridge` prove the geometric/toy side only; the wire to `MainAirAccept` is unwritten).
  * `hbus` (the `.lookup` arm)                     — FLOOR (LogUp permutation-argument soundness +
        chip/range table faithfulness; `AirLegsDischarged.hbus_is_lookup` pins every remaining obligation
        to a chip/range lookup membership, explicitly out of the Lean semantics per `Lookup.lean:17`).
  * `t.tf .memory = []`, `t.tf .mapOps = []`       — DEPLOYED-MODELING (aux-table-assembly emptiness for
        the mem/map-op-free `transferV3`; an irreducible structural fact about the committed trace).
  * `tracePublishedCommit t = pi.toPublished`      — DEPLOYED-MODELING (the abstract PI readout is
        `opaque`; the per-descriptor limb readout `rotV3_publishes` is the bridge).

The other SIX `Satisfied2` legs (`rowHashes`, `rowRanges`, `memAddrsNodup`, `memClosed`,
`memDisciplined`, `memBalanced`) are DISCHARGED-NOW by the committed `AirLegsDischarged` theorems, and
`rowConstraints` is FORCED-NOW from `MainAirAccept` by the committed `AirChecksSatisfied` arithmetic
bridge. No FLOOR of the `Poseidon2SpongeCR`/`HashCR`/`DL` kind is invoked directly at this slice (the
Merkle-binding floor is folded into `MainAirAccept`'s FRI-extraction obligation).

## Discipline

Sorry-free; no `def …Sound` carrier; no `verifyBatch`; no assumed `AlgoStarkSound`/`StarkSound`/`FriExtract`.
Teeth (§3) exhibit the load-bearing `MainAirAccept` premise firing (honest) and biting (a tampered gate
cannot supply it). NEW file; imports read-only; builds targeted (`lake build
Dregg2.Circuit.AlgoStarkSoundInstance`). Sibling `Exec/*` / `Crypto/MlDsa*` working-tree edits are OTHER
lanes' — FLAGGED, not owned here.
-/
import Dregg2.Circuit.FriVerifierBridge
import Dregg2.Circuit.AirChecksSatisfied
import Dregg2.Circuit.AirLegsDischarged

namespace Dregg2.Circuit.AlgoStarkSoundInstance

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks)
open Dregg2.Circuit.CircuitSoundness
  (Registry BatchPublicInputs BatchProof EffectIdx tracePublishedCommit)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace EffectVmDescriptor2 envAt memLog mapLog opRow VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAccept MainAirAcceptF isArith airAccept_forces_satisfied2)
open Dregg2.Circuit.AirLegsDischarged (airAccept_forces_satisfied2_transferV3)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Crypto

/-! ## §1 — THE DEPLOYED SLICE: a real `AlgoStarkSound` at the live `transferV3` descriptor.

The registry `fun _ => transferV3` is the transfer-effect deployment slice (`transferV3` is the live
graduated frozen-authority transfer descriptor, `RotatedKernelRefinement.transferV3` — NOT a `univ`/toy
descriptor). At this slice six `Satisfied2` legs are already DISCHARGED by the committed
`AirLegsDischarged` bricks and `rowConstraints` is FORCED from `MainAirAccept`, so the class reduces to
exactly the four hypotheses tallied in the header. -/

/-- **`algoStarkSound_of_bricks_transferV3` — `AlgoStarkSound` ASSEMBLED, no carrier.** From an explicit
extraction hypothesis `hextract` delivering, on every `verifyAlgo`-accept: an opened `VmTrace t` whose
AIR quotient check passes (`MainAirAccept`), the LogUp lookup arm (`hbus`), the two aux-table-emptiness
facts, and the published-commit link — the full `AlgoStarkSound` for the deployed `transferV3` registry
slice holds. The `MainAirAccept ⟹ Satisfied2.rowConstraints` lift and the six discharged legs are the
committed `airAccept_forces_satisfied2_transferV3`; the only thing this theorem ADDS is threading the
per-`(pi, π)` extraction through the class's `∀`. NO `AlgoStarkSound`/`StarkSound`/`FriExtract` carrier,
NO `verifyBatch`. -/
theorem algoStarkSound_of_bricks_transferV3
    (hash : List Int → Int)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (hextract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      ∃ (t : VmTrace),
        -- FRI-proximity onto the deployed descriptor's trace, as the CANONICAL field predicate
        -- (DEPLOYED-MODELING; `FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals` produces
        -- exactly this from `hood` + `hnonexc`):
        MainAirAcceptF transferV3 t ∧
        -- the `.lookup` arm — LogUp / chip-range table membership (FLOOR):
        (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        -- aux-table-assembly emptiness (DEPLOYED-MODELING):
        t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
        -- the published-commitment link (DEPLOYED-MODELING):
        tracePublishedCommit t = pi.toPublished) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk checks initState logN view where
  extract := by
    intro pi π hacc
    obtain ⟨t, hAir, hbus, hMem, hMap, hPub⟩ := hextract pi π hacc
    -- `transferV3` is mem-op-free, so its memory boundary is trivial: any image satisfies
    -- `MemCheck` over the empty log (`AirLegsDischarged.hBal_transferV3`); witness it concretely.
    exact ⟨fun _ => 0, fun _ => (0, 0), [], t,
      airAccept_forces_satisfied2_transferV3 hash (fun _ => 0) (fun _ => (0, 0)) t
        hAir hbus hMem hMap, hPub⟩

/-! ## §2 — THE GENERAL SLICE: a real `AlgoStarkSound` at an ARBITRARY registry `R`.

For a general descriptor `R pi.effect` the six legs are not structurally empty, so all EIGHT
`airAccept_forces_satisfied2` inputs are carried per-`(pi, π)` (each is either FLOOR — the LogUp/table
legs — or a structural fact about the committed trace). `rowConstraints` is STILL forced from
`MainAirAccept` by the committed arithmetic bridge — that is the genuine, non-tautological content: the
hypothesis supplies the AIR QUOTIENT acceptance (`MainAirAccept`, about opened `quot`/`zerofier`
values), NOT the semantic `Satisfied2.rowConstraints` denotation, which is PROVED. -/

/-- **`algoStarkSound_of_bricks` — general-registry `AlgoStarkSound`, no carrier.** Same shape as the
deployed slice, at an arbitrary `R : Registry`: the extraction hypothesis delivers, on accept, the
opened trace plus the eight `airAccept_forces_satisfied2` legs and the published-commit link; the class
follows. The `MainAirAccept ⟹ rowConstraints` lift is the committed `airAccept_forces_satisfied2`. -/
theorem algoStarkSound_of_bricks
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (hextract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace),
        -- FRI-proximity onto the deployed descriptor's trace, as the CANONICAL field predicate:
        MainAirAcceptF (R pi.effect) t ∧
        -- the `.lookup`/`.mapOp` arms — LogUp / map-ops table (FLOOR):
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        -- `rowHashes` / `rowRanges` (structural for graduated descriptors):
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        -- the six memory/map-table legs (FLOOR: LogUp balance / table-assembly faithfulness):
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        -- the published-commitment link (DEPLOYED-MODELING):
        tracePublishedCommit t = pi.toPublished) :
    AlgoStarkSound hash R perm RATE toNat params vk checks initState logN view where
  extract := by
    intro pi π hacc
    obtain ⟨minit, mfin, maddrs, t, hAir, hbus, hHashes, hRanges,
      hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩ := hextract pi π hacc
    exact ⟨minit, mfin, maddrs, t,
      airAccept_forces_satisfied2 hash (R pi.effect) minit mfin maddrs t
        hAir hbus hHashes hRanges hNodup hClosed hDisc hBal hMemTF hMapTF, hPub⟩

/-! ## §3 — TEETH: the load-bearing `MainAirAccept` premise (both polarities, committed witnesses).

The extraction hypothesis is a REAL obligation, not free by unfolding: its FRI-side conjunct
`MainAirAccept` both FIRES on honest data and BITES on a tampered gate. -/

/-- **RESPECTING** — the `MainAirAcceptF` premise is INHABITED on the honest toy descriptor/trace
(`AirChecksSatisfied.honest_mainAirAcceptF`): the extraction hypothesis is satisfiable, so the assembled
`AlgoStarkSound` is non-vacuous. -/
theorem mainAirAccept_respecting :
    MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
      Dregg2.Circuit.AirChecksSatisfied.tHonest :=
  Dregg2.Circuit.AirChecksSatisfied.honest_mainAirAcceptF

/-- **BITING** — the `MainAirAcceptF` premise is FALSIFIABLE: a trace with a tampered arithmetic gate
CANNOT supply it (`AirChecksSatisfied.tampered_gate_unacceptedF`; the tampered residual `5 ≢ 0` mod `p`).
So a prover cannot meet the extraction hypothesis with a lying trace — the premise carries genuine
soundness content, and the field migration did NOT make it vacuous. -/
theorem mainAirAccept_biting :
    ¬ MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unacceptedF

#assert_axioms algoStarkSound_of_bricks_transferV3
#assert_axioms algoStarkSound_of_bricks
#assert_axioms mainAirAccept_respecting
#assert_axioms mainAirAccept_biting

end Dregg2.Circuit.AlgoStarkSoundInstance
