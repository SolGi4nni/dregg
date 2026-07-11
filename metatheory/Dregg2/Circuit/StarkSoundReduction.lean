/-
# `Dregg2.Circuit.StarkSoundReduction` — `[StarkSound]` as a PROVEN reduction to ONE precise core.

## What this module does (the one-line honest claim)

The apex `CircuitSoundness.lightclient_unfoolable` consumes `[StarkSound hash R]` — the opaque
batch-STARK soundness carrier over `verifyBatch` (`CircuitSoundness.lean:382`). This module packages
the ALREADY-PROVEN reduction chain into a SINGLE named theorem `starkSound_of_core`:

    RSProximityCore hash R … → StarkSound hash R          (PROVED, `#assert_axioms`-clean)

so `[StarkSound]` is no longer an opaque assumption sitting under the apex — it is DERIVED from a
bundled core `RSProximityCore` that names EXACTLY the two irreducible residuals, and nothing else.

## Why a new module (the decomposition already exists but was SPLIT and never landed on `StarkSound`)

The chain to `StarkSound` was proven in TWO files whose composition was never taken:

  * `FriVerifierBridge.starkSound_of_verifyAlgo` : `[AlgoStarkSound …] → DeployedRefines → StarkSound`
    (lifts the opaque `verifyBatch` carrier to the SPECIFIED `verifyAlgo` algorithm — verifier
    ALGORITHM out of the TCB — plus one Rust-refines-spec residual `DeployedRefines`).
  * `AlgoStarkSoundInstance.algoStarkSound_of_bricks` : `DeployedTraceExtract → AlgoStarkSound`
    (the deployed-trace FRI extraction hypothesis `hextract` ⟹ the `AlgoStarkSound` class, via the
    committed `AirChecksSatisfied.airAccept_forces_satisfied2` bridge — `MainAirAccept ⟹ Satisfied2`).

`algoStarkSoundInstance` explicitly produces `AlgoStarkSound`, NEVER `StarkSound` (its header §0
documents the disjoint-types seam). This module TAKES the composition: `DeployedTraceExtract`
(feeding `algoStarkSound_of_bricks`) + `DeployedRefines` (feeding `starkSound_of_verifyAlgo`) ⟹
`StarkSound`. Bundled as `RSProximityCore`, that is the whole content of `[StarkSound]`.

## The precise irreducible core (what `RSProximityCore` names — and nothing more)

  1. **`DeployedTraceExtract`** — the FRI-proximity-ONTO-THE-DEPLOYED-TRACE extraction: for every
     `(pi, π)` the SPECIFIED `verifyAlgo` accepts, there is an opened deployed `VmTrace t` whose AIR
     quotient check passes (`MainAirAccept hash (R pi.effect) t`), the LogUp/table legs hold, and
     `tracePublishedCommit t = pi.toPublished`. This is the SINGLE research-grade residual. Its MATH
     content — FRI low-degree soundness at the deployed BabyBear field / rate-`1/8` / 8-to-1 fold /
     `38` queries — is ALREADY PROVED, axiom-clean, over abstract Reed–Solomon oracles:
       * geometric proximity + the KEY LEMMA `FriSoundness.fold_close_of_two_alpha` (2-to-1) and its
         arity generalization `FriFoldArity.fold_close_of_arity_challenges` (`n²·d`, deployed `n=8`);
       * query soundness `FriQuerySoundness.deployed_accept_prob_lt` : a `7/16`-far oracle passes the
         deployed `38`-query sampler with probability `< 2⁻³¹`.
     What is NOT proved is the WIRE from that abstract proximity to `MainAirAccept` on the deployed
     `VmTrace` — the "disjoint types" seam (`AlgoStarkSoundInstance` §0). That wire is the irreducible
     `DeployedTraceExtract`; see `RSProximityResearchLemma` below for its precise reduced statement.

  2. **`FriVerifierBridge.DeployedRefines`** — the deployed Rust `verify_batch` computes the SAME
     accept Boolean as the Lean `verifyAlgo` spec. A CODE-refinement obligation (a differential-testing
     target, the analogue of `FriVerifier.GnarkRefines`), NOT mathematics.

Everything BETWEEN these two and `StarkSound` (the `MainAirAccept ⟹ Satisfied2` arithmetic bridge, the
six discharged memory/hash legs, the `AlgoStarkSound ⟹ StarkSound` verifier-algorithm lift) is PROVED.

## Discipline

Sorry-free; no `def …Sound` carrier; no `axiom`; both residuals enter as an explicit hypothesis /
`Prop` field, never a smuggled `…Hard`. `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
New file; imports read-only; builds targeted (`lake build Dregg2.Circuit.StarkSoundReduction`).
-/
import Dregg2.Circuit.AlgoStarkSoundInstance

namespace Dregg2.Circuit.StarkSoundReduction

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView DeployedRefines starkSound_of_verifyAlgo)
open Dregg2.Circuit.FriVerifier (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks)
open Dregg2.Circuit.CircuitSoundness
  (Registry BatchPublicInputs BatchProof EffectIdx tracePublishedCommit StarkSound
   CommitSurface descriptorRefines StateDecode WitnessDecodes vkOfRegistry verifyBatch
   lightclient_unfoolable)
open Dregg2.Circuit.CircuitSoundness.Verdict (accept)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace EffectVmDescriptor2 envAt memLog mapLog opRow VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAccept isArith)
open Dregg2.Circuit.AlgoStarkSoundInstance (algoStarkSound_of_bricks)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecChainedState)
open Dregg2.Crypto

/-! ## §1 — `DeployedTraceExtract` : the FRI-proximity-onto-the-deployed-trace residual.

This is EXACTLY the `hextract` hypothesis of `AlgoStarkSoundInstance.algoStarkSound_of_bricks`, named
as a standalone `Prop`. It is the one research-grade obligation: an accepting `verifyAlgo` run yields
an opened deployed `VmTrace t` satisfying the deployed AIR quotient check (`MainAirAccept`), the
LogUp/table legs, the memory-checking legs, and the published-commit link. -/

/-- **`DeployedTraceExtract`** — for every batch the SPECIFIED algorithm accepts, an opened deployed
`VmTrace t` with: the AIR quotient acceptance `MainAirAccept` (FRI proximity onto the deployed
descriptor — the research residual), the non-arithmetic `.lookup`/`.mapOp` arms (LogUp/table FLOOR),
the `rowHashes`/`rowRanges` structural legs, the six memory-checking legs, and
`tracePublishedCommit t = pi.toPublished`. Verbatim the `algoStarkSound_of_bricks` premise. -/
def DeployedTraceExtract
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace),
      MainAirAccept hash (R pi.effect) t ∧
      (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
      (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
      maddrs.Nodup ∧
      (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
      MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
      MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
      t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
      t.tf .mapOps = mapLog (R pi.effect) t ∧
      tracePublishedCommit t = pi.toPublished

/-! ## §2 — `RSProximityCore` : the bundled irreducible core of `[StarkSound]`.

The WHOLE content of the opaque apex carrier `[StarkSound hash R]`, factored into exactly its two
irreducible residuals — the deployed-trace FRI extraction (research) and the Rust-refines-spec code
refinement — and nothing else. -/

/-- **`RSProximityCore`** — the two-field precise core `[StarkSound]` reduces to:
  * `extract` : `DeployedTraceExtract` (the FRI-proximity-onto-the-deployed-trace research residual);
  * `refines` : `DeployedRefines` (the Rust `verify_batch` ↔ Lean `verifyAlgo` code refinement).
No third obligation: everything else on the path to `StarkSound` is a PROVED theorem. -/
structure RSProximityCore
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Prop where
  extract : DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view
  refines : DeployedRefines R perm RATE toNat params vk checks initState logN view

/-! ## §3 — THE REDUCTION `starkSound_of_core` : `RSProximityCore → StarkSound`. -/

/-- **`starkSound_of_core` — the apex carrier `[StarkSound]` DERIVED from the precise core.**

From `RSProximityCore` the opaque `StarkSound hash R` holds. Proof: `algoStarkSound_of_bricks` turns
the `extract` field into the `AlgoStarkSound` class (the deployed-trace extraction ⟹ the specified
algorithm's extraction floor, via the committed `airAccept_forces_satisfied2` `MainAirAccept ⟹
Satisfied2` bridge); `starkSound_of_verifyAlgo` then lifts that plus the `refines` field to
`StarkSound`. The opaque whole-verifier carrier is GONE — replaced by two NAMED residuals, one
research (`DeployedTraceExtract`) and one code-refinement (`DeployedRefines`). -/
theorem starkSound_of_core
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (core : RSProximityCore hash R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  haveI : AlgoStarkSound hash R perm RATE toNat params vk checks initState logN view :=
    algoStarkSound_of_bricks hash R perm RATE toNat params vk checks initState logN view core.extract
  starkSound_of_verifyAlgo hash R perm RATE toNat params vk checks initState logN view core.refines

/-! ## §4 — the apex, on the precise core (opaque `[StarkSound]` fully eliminated).

`lightclient_unfoolable` (`CircuitSoundness.lean`) takes `[StarkSound hash R]` as an instance. Feeding
it `starkSound_of_core` re-states the whole single-transition unfoolability apex resting on the precise
core `RSProximityCore` (+ the SAME hash-CR / per-effect / witness-decode floors) instead of the opaque
carrier. This is the honest headline: a deployed-accepted batch yields a genuine kernel transition
committing to the public inputs, with the STARK carrier fully factored into its two named residuals. -/
theorem lightclient_unfoolable_of_core
    (hash : List Int → Int) (S : CommitSurface) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (core : RSProximityCore hash R perm RATE toNat params vk checks initState logN view)
    (hCR : Poseidon2SpongeCR hash)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  haveI : StarkSound hash R :=
    starkSound_of_core hash R perm RATE toNat params vk checks initState logN view core
  lightclient_unfoolable hash S R hCR kstep hrefines pi π hwitdec hacc

/-! ## §5 — the single research lemma, stated precisely (its proof the residual).

`RSProximityResearchLemma` is the reduced statement of the ONE thing left: the deployed-trace FRI
extraction. Everything else on the path to `StarkSound` is proved. Its geometric MATH content is
already discharged over abstract Reed–Solomon oracles (`FriSoundness` / `FriFoldArity` /
`FriQuerySoundness`, all `#assert_axioms`-clean at the deployed BabyBear field / rate-`1/8` / 8-to-1
fold / `38` queries in the unique-decoding regime). The residual is the WIRE from that abstract
proximity to `MainAirAccept` on the deployed `VmTrace` — the "disjoint types" seam. We state the
research lemma as EXACTLY `DeployedTraceExtract`, and record (below) that discharging it collapses the
apex to the code-refinement `DeployedRefines` alone. -/

/-- **`RSProximityResearchLemma` — the single irreducible research obligation, precisely.** The
deployed-trace FRI extraction is exactly `DeployedTraceExtract`. This `def` names it as THE research
lemma whose proof is the residual: FRI low-degree soundness at the deployed parameters, transported
from the proven abstract-oracle proximity onto the deployed `VmTrace`/`EffectVmDescriptor2` AIR so that
`verifyAlgo` acceptance forces `MainAirAccept`. (Not a new assumption — a rename that isolates the
target, so `RSProximityResearchLemma → RSProximityCore` needs ONLY the code-refinement.) -/
abbrev RSProximityResearchLemma
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Prop :=
  DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view

/-- **`core_of_research_and_refines` — the research lemma + code refinement ARE the core.** Once
`RSProximityResearchLemma` is discharged, the only thing standing between it and the apex carrier
`StarkSound` is the Rust-refines-spec `DeployedRefines` — a code obligation, not mathematics. This
makes the factoring exact: `[StarkSound]` = (one FRI research lemma) ∧ (one code refinement). -/
theorem core_of_research_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (hlemma : RSProximityResearchLemma hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    RSProximityCore hash R perm RATE toNat params vk checks initState logN view :=
  ⟨hlemma, href⟩

/-- **`starkSound_of_research_and_refines` — the end-to-end one-liner.** `StarkSound` from exactly the
FRI research lemma + the code refinement, with no other assumption. This IS "turn opaque `[StarkSound]`
into a proven reduction + one precisely-stated research lemma": the reduction is proved here; the
research lemma is `RSProximityResearchLemma`; the only other input is a code refinement. -/
theorem starkSound_of_research_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (hlemma : RSProximityResearchLemma hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  starkSound_of_core hash R perm RATE toNat params vk checks initState logN view
    (core_of_research_and_refines hash R perm RATE toNat params vk checks initState logN view hlemma href)

#assert_axioms starkSound_of_core
#assert_axioms lightclient_unfoolable_of_core
#assert_axioms core_of_research_and_refines
#assert_axioms starkSound_of_research_and_refines

/-! ## §6 — TEETH: the core is LOAD-BEARING (the extraction residual is a genuine obligation).

`DeployedTraceExtract`'s hard conjunct `MainAirAccept` is FALSIFIABLE — a trace with a tampered
arithmetic gate cannot supply it (`AirChecksSatisfied.tampered_gate_unaccepted`), while an honest trace
does (`AirChecksSatisfied.honest_mainAirAccept`). So `RSProximityCore` is not free by unfolding: a
prover cannot meet `extract` with a lying trace. (Reuses the committed witnesses; the point here is
that the BUNDLED core inherits their bite.) -/

/-- **BITING** — the core's extraction conjunct is a real obligation: a tampered-gate trace cannot
supply `MainAirAccept`, so it cannot witness `DeployedTraceExtract`'s existential. -/
theorem core_extract_biting :
    ¬ MainAirAccept (fun _ => 0) Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unaccepted

/-- **RESPECTING** — and the conjunct is inhabited on honest data, so the core is non-vacuous. -/
theorem core_extract_respecting :
    MainAirAccept (fun _ => 0) Dregg2.Circuit.AirChecksSatisfied.dArith
      Dregg2.Circuit.AirChecksSatisfied.tHonest :=
  Dregg2.Circuit.AirChecksSatisfied.honest_mainAirAccept

#assert_axioms core_extract_biting
#assert_axioms core_extract_respecting

end Dregg2.Circuit.StarkSoundReduction
