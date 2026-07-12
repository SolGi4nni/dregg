/-
# `Dregg2.Circuit.DeployedTraceExtract` — TRANSPORTING the proven abstract FRI proximity onto the
deployed `VmTrace`, factoring `DeployedTraceExtract` into (proven math) + TWO precise structure-maps.

## What this module does (the one-line honest claim)

`StarkSoundReduction.DeployedTraceExtract` is the single research-grade residual of `[StarkSound]`:
"an accepting deployed `verifyAlgo` run yields an opened `VmTrace t` with `MainAirAccept` + legs."
Its MATH content — FRI low-degree soundness at the deployed BabyBear field / rate-`1/8` / 8-to-1 fold
— is ALREADY PROVED, axiom-clean, over abstract Reed–Solomon oracles
(`FriFoldArity.fold_close_of_arity_challenges` → `FriBridgeDeployedArity.friProximityK8_discharge0`;
`FriQuerySoundness.deployed_accept_prob_lt`). What was NOT written is the WIRE from that abstract
proximity to `MainAirAccept` on the deployed `VmTrace`/`EffectVmDescriptor2` — the "disjoint types"
seam (`AlgoStarkSoundInstance` §0).

This file TRANSPORTS the proven proximity across that seam. It:

  1. Names the seam as EXACTLY TWO precise structure-maps (`DeployedFriEmbedding`):
       * `accept_folds` — the VERIFIER-DECODE: an accepting `verifyAlgo` run's committed BabyBear
         column oracle `oracle pi π`, folded by `8` distinct challenges `chal pi π`, lands in the
         deployed folded code `friSetupK8.C'` (the abstract arity-8 FRI transcript the deployed
         verifier's FRI sub-checks realize — the "FRI oracle ↔ EffectVmDescriptor2 commitment"
         identification, in the property→transcript direction of `FriExtractReal §4`);
       * `decode_trace` — the CODEWORD-DECODE: whenever the committed oracle IS a genuine low-degree
         codeword (`oracle pi π ∈ friSetupK8.C`), it decodes to a deployed `VmTrace t` with
         `MainAirAccept` + all the `DeployedTraceExtract` legs.
  2. WIRES the proven FRI keystone in the MIDDLE (`deployedTraceExtract_of_embedding`): the
     load-bearing `friProximityK8_discharge0` turns `accept_folds` into `oracle pi π ∈ friSetupK8.C`
     (0-closeness ⟺ codeword, unique decoding at rate-`1/8`), which is EXACTLY the extra hypothesis
     `decode_trace` gets to assume. So `decode_trace` is genuinely WEAKER than the raw
     `DeployedTraceExtract`: the FRI math has already discharged "is the committed oracle low-degree?"

So `DeployedTraceExtract` (hence the whole `[StarkSound]` math residual) reduces to the two named
maps, with the proven arity-8 proximity CONNECTED and load-bearing between them. The FRI-link BITES
(a far word cannot be the committed oracle of an accepting transcript, `embedding_rejects_far_oracle`)
and FIRES (the honest codeword folds in, `fri_fold_respecting`).

## The exact remaining type-bridge (what is NOT proved, stated precisely)

`DeployedFriEmbedding` is the residual — an explicit hypothesis structure, NOT a smuggled carrier.
Its two Prop fields are the precise remaining maps:

  * `accept_folds : ∀ pi π, verifyAlgo … = true → ∀ i, Fold friSetupK8.geom (chal pi π i)
        (oracle pi π) ∈ friSetupK8.C'` — the verifier-syntax decode + FRI knowledge-reflection;
  * `decode_trace : ∀ pi π, verifyAlgo … = true → oracle pi π ∈ friSetupK8.C →
        TraceWitnessed hash (R pi.effect) pi` — the low-degree-codeword ↔ `VmTrace`/AIR-quotient decode.

Everything between them — the arity-8 proximity, the unique-decoding collapse to a codeword — is a
PROVED theorem chained here. This is the honest verdict the brief asked for: the math is done, the
transport is engineered, and the seam is now two named structure-maps, not one opaque research Prop.

## Discipline

Sorry-free; no `def …Sound`/`…Hard` carrier; no `axiom`; the residual enters as an explicit
hypothesis structure. `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. New file; imports
read-only; builds targeted (`lake build Dregg2.Circuit.DeployedTraceExtract`). ADDITIVE — the shared
apex modules (`StarkSoundReduction`, `FriBridgeDeployedArity`, …) are imported, never edited.
-/
import Dregg2.Circuit.StarkSoundReduction
import Dregg2.Circuit.FriBridgeDeployedArity
import Dregg2.Circuit.FieldIntegerLift

namespace Dregg2.Circuit.DeployedTraceExtract

open Dregg2.Circuit.StarkSoundReduction
  (DeployedTraceExtract RSProximityCore RSProximityResearchLemma starkSound_of_core
   core_of_research_and_refines starkSound_of_research_and_refines)
open Dregg2.Circuit.FriVerifierBridge (ProofView DeployedRefines)
open Dregg2.Circuit.FriVerifier (verifyAlgo FriParams RecursionVk FriChecks)
open Dregg2.Circuit.CircuitSoundness
  (Registry BatchPublicInputs BatchProof EffectIdx tracePublishedCommit StarkSound)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace EffectVmDescriptor2 envAt memLog mapLog opRow VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAccept MainAirAcceptF isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem)
open Dregg2.Circuit.FriFoldArity
  (friSetupK8 Fold f0 f0_no_injective_good fHon8 fHon8_fold_complete chal8 chal8_inj)
open Dregg2.Circuit.FriBridgeDeployedArity (FriProximityK friProximityK8_discharge0)
open Dregg2.Crypto

/-! ## §1 — `TraceWitnessed` : the per-batch tail of `DeployedTraceExtract`, as a standalone `Prop`.

Verbatim the existential body of `StarkSoundReduction.DeployedTraceExtract`, abstracted over the
descriptor `D` (so `DeployedTraceExtract hash R … = ∀ pi π, verifyAlgo … → TraceWitnessed hash
(R pi.effect) pi` DEFINITIONALLY). This lets the codeword-decode map name exactly the deployed-trace
obligation without re-transcribing the ten-conjunct body at each use. -/

/-- **`TraceWitnessed hash D pi`** — an opened deployed `VmTrace t` for descriptor `D` and batch `pi`
carrying the AIR quotient acceptance `MainAirAccept`, the non-arithmetic (LogUp/table) arms, the
`rowHashes`/`rowRanges` structural legs, the six memory-checking legs, and the published-commit link.
The `D := R pi.effect` specialization is exactly one disjunct-per-`(pi,π)` of `DeployedTraceExtract`. -/
def TraceWitnessed (hash : List Int → Int) (D : EffectVmDescriptor2) (pi : BatchPublicInputs) : Prop :=
  ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace),
    MainAirAcceptF D t ∧
    (∀ i < t.rows.length, ∀ c ∈ D.constraints, ¬ isArith c →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
    (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) D.hashSites) ∧
    (∀ i < t.rows.length, ∀ r ∈ D.ranges, r.holds (envAt t i)) ∧
    maddrs.Nodup ∧
    (∀ op ∈ memLog D t, op.addr ∈ maddrs) ∧
    MemoryChecking.Disciplined (memLog D t) ∧
    MemoryChecking.MemCheck minit mfin maddrs (memLog D t) ∧
    t.tf .memory = (memLog D t).map opRow ∧
    t.tf .mapOps = mapLog D t ∧
    tracePublishedCommit t = pi.toPublished

/-- **`TraceWitnessed` IS the `DeployedTraceExtract` body**, per `(pi, π)`. This records the
definitional identity so the reduction below is transparent: `DeployedTraceExtract` is nothing but
"`verifyAlgo` accepts ⟹ `TraceWitnessed` at `R pi.effect`", for all `(pi, π)`. -/
theorem deployedTraceExtract_iff
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view
      ↔ ∀ (pi : BatchPublicInputs) (π : BatchProof),
          verifyAlgo perm RATE toNat params vk checks initState logN
              (view pi π).1 (view pi π).2 = true →
          TraceWitnessed hash (R pi.effect) pi :=
  Iff.rfl

/-! ## §2 — `DeployedFriEmbedding` : the TWO precise structure-maps that constitute the seam.

The whole content of the disjoint-developments seam, named. `oracle`/`chal` decode an accepting
`verifyAlgo` run into the abstract arity-8 FRI transcript (`accept_folds`); `decode_trace` decodes a
low-degree codeword into the deployed `VmTrace` (`MainAirAccept` + legs). Nothing else — the proximity
math CONNECTING them is a proved theorem (`§3`), not a field. -/

/-- **`DeployedFriEmbedding`** — the residual type-bridge for `DeployedTraceExtract`, as an explicit
hypothesis structure (NOT a smuggled carrier). Its data are the two decode functions and its Props the
two maps:
  * `oracle pi π : Fin 16 → BabyBear` — the committed BabyBear column oracle the deployed proof exposes;
  * `chal pi π : Fin 8 → BabyBear` — the `8` FRI fold challenges of the transcript (distinct, `chal_inj`);
  * `accept_folds` — VERIFIER-DECODE: on `verifyAlgo`-accept, every fold `Fold friSetupK8.geom
    (chal pi π i) (oracle pi π)` lands in the deployed folded code `friSetupK8.C'` (the deployed FRI
    sub-checks realize the abstract arity-8 transcript — the FRI-oracle↔commitment identification);
  * `decode_trace` — CODEWORD-DECODE: on accept AND the committed oracle being a genuine low-degree
    codeword, an opened deployed `VmTrace` witnesses `TraceWitnessed hash (R pi.effect) pi`.
`decode_trace` is genuinely WEAKER than raw extraction: the FRI math (`§3`) supplies its
`oracle pi π ∈ friSetupK8.C` hypothesis, so the decoder never faces an unresolved-degree oracle. -/
structure DeployedFriEmbedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Type where
  /-- The committed BabyBear column oracle the deployed proof exposes. -/
  oracle : BatchPublicInputs → BatchProof → (Fin 16 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` FRI fold challenges of the transcript. -/
  chal : BatchPublicInputs → BatchProof → (Fin 8 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` challenges are DISTINCT (so the arity-8 Vandermonde inverts — the keystone hypothesis). -/
  chal_inj : ∀ pi π, Function.Injective (chal pi π)
  /-- **VERIFIER-DECODE**: an accepting run's committed oracle folds into the deployed folded code
  under all `8` challenges — the abstract arity-8 FRI transcript the deployed FRI sub-checks realize. -/
  accept_folds : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ i, Fold friSetupK8.geom (chal pi π i) (oracle pi π) ∈ friSetupK8.C'
  /-- **CODEWORD-DECODE**: on accept AND the committed oracle being a genuine low-degree codeword, a
  deployed `VmTrace` witnesses the `DeployedTraceExtract` legs (`MainAirAccept` + …). -/
  decode_trace : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    oracle pi π ∈ friSetupK8.C →
    TraceWitnessed hash (R pi.effect) pi

/-! ## §3 — THE TRANSPORT : the proven arity-8 proximity, wired between the two maps. -/

/-- **`deployedTraceExtract_of_embedding` — `DeployedTraceExtract` DERIVED, FRI math load-bearing.**
From a `DeployedFriEmbedding` the opaque `DeployedTraceExtract` holds. Proof: `accept_folds` gives an
accepting arity-8 transcript; the PROVED keystone `friProximityK8_discharge0` (i.e.
`FriFoldArity.fold_close_of_arity_challenges` at `n = 8` over BabyBear) turns it into
`oracle pi π ∈ friSetupK8.C` (0-closeness ⟺ codeword — unique decoding at rate-`1/8`); that discharges
exactly the extra hypothesis `decode_trace` needs. The FRI proximity theorem is the LOAD-BEARING middle
link: remove it and `decode_trace`'s codeword hypothesis is unavailable. -/
theorem deployedTraceExtract_of_embedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view := by
  intro pi π hacc
  -- PROVEN FRI proximity: the accepting transcript's oracle is 0-close, i.e. a genuine codeword.
  have hlow : emb.oracle pi π ∈ friSetupK8.C :=
    closeN_zero_iff_mem.mp
      (friProximityK8_discharge0 (emb.chal_inj pi π) (emb.accept_folds pi π hacc))
  -- CODEWORD-DECODE: the low-degree codeword decodes to the deployed trace.
  exact emb.decode_trace pi π hacc hlow

/-! ## §4 — Composition to `RSProximityCore` and `StarkSound` (the opaque residual eliminated). -/

/-- **`rsProximityCore_of_embedding` — the precise core from the embedding + code refinement.** The
`StarkSoundReduction.RSProximityCore` (whose `extract` field IS `DeployedTraceExtract`) assembled from
the transported `DeployedFriEmbedding` and the Rust-refines-spec `DeployedRefines`. -/
theorem rsProximityCore_of_embedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    RSProximityCore hash R perm RATE toNat params vk checks initState logN view :=
  core_of_research_and_refines hash R perm RATE toNat params vk checks initState logN view
    (deployedTraceExtract_of_embedding hash R perm RATE toNat params vk checks initState logN view emb)
    href

/-- **`starkSound_of_embedding_and_refines` — `[StarkSound]` from the transport + code refinement.**
The apex carrier `StarkSound hash R` holds given (i) the transported `DeployedFriEmbedding` (the two
named type-bridge maps; the FRI math between them PROVED) and (ii) `DeployedRefines` (code refinement).
No opaque STARK carrier and no `DeployedTraceExtract` research Prop survives: the math residual is
transported down to the two structure-maps of `§2`. -/
theorem starkSound_of_embedding_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  starkSound_of_core hash R perm RATE toNat params vk checks initState logN view
    (rsProximityCore_of_embedding hash R perm RATE toNat params vk checks initState logN view emb href)

#assert_axioms deployedTraceExtract_of_embedding
#assert_axioms rsProximityCore_of_embedding
#assert_axioms starkSound_of_embedding_and_refines

/-! ## §5 — TEETH : the FRI link is LOAD-BEARING (the transport is not free by unfolding).

The transport's middle link — the proven arity-8 proximity — genuinely BITES on the verifier-decode
map and FIRES on the honest codeword. Plus the codeword-decode's `MainAirAccept` conjunct bites/fires
(reusing the committed `AirChecksSatisfied` witnesses). So `DeployedFriEmbedding` is a real obligation,
not a definitional pass-through. -/

/-- **FRI-LINK BITES** — a far word cannot be the committed oracle of an accepting transcript. If
`emb.oracle pi π` were the frequency-`8` far word `f0` (`f0 ∉ friSetupK8.C`), then `accept_folds` +
`chal_inj` would exhibit `8` distinct challenges all folding `f0` into `friSetupK8.C'`, contradicting
the PROVED `f0_no_injective_good`. So the verifier-decode map is genuinely constrained by the FRI
proximity content: an accepting deployed transcript's oracle is forced low-degree. -/
theorem embedding_rejects_far_oracle
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true) :
    emb.oracle pi π ≠ f0 := by
  intro hf
  apply f0_no_injective_good
  refine ⟨emb.chal pi π, emb.chal_inj pi π, fun i => ?_⟩
  have hi := emb.accept_folds pi π hacc i
  rwa [hf] at hi

/-- **FRI-LINK FIRES** — the honest degree-`< 8` codeword `fHon8` folds into `friSetupK8.C'` for the
`8` distinct challenges `chal8`, so an honest transcript satisfies `accept_folds` (the map is
non-vacuous — a genuine low-degree oracle passes). -/
theorem fri_fold_respecting :
    Function.Injective chal8 ∧ ∀ i, Fold friSetupK8.geom (chal8 i) fHon8 ∈ friSetupK8.C' :=
  ⟨chal8_inj, fun i => fHon8_fold_complete (chal8 i)⟩

/-- **CODEWORD-DECODE BITES** — the `MainAirAcceptF` conjunct `decode_trace` must supply is
FALSIFIABLE: a tampered-gate trace cannot meet it (`AirChecksSatisfied.tampered_gate_unacceptedF`). So
the codeword-decode map cannot be met with a lying trace — it carries genuine soundness content. -/
theorem decode_trace_biting :
    ¬ MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unacceptedF

/-- **CODEWORD-DECODE FIRES** — and its `MainAirAcceptF` conjunct is inhabited on honest data
(`AirChecksSatisfied.honest_mainAirAcceptF`), so the codeword-decode map is non-vacuous. -/
theorem decode_trace_respecting :
    MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
      Dregg2.Circuit.AirChecksSatisfied.tHonest :=
  Dregg2.Circuit.AirChecksSatisfied.honest_mainAirAcceptF

#assert_axioms embedding_rejects_far_oracle
#assert_axioms fri_fold_respecting
#assert_axioms decode_trace_biting
#assert_axioms decode_trace_respecting

/-! ## §6 — THE PAYOFF: the field-OOD landing feeds the extraction's AIR conjunct DIRECTLY.

Post-Phase-0 the extraction hypothesis's hardest conjunct is the CANONICAL field predicate
`MainAirAcceptF transferV3 t` (the first conjunct of `TraceWitnessed`, i.e. of `decode_trace`'s
deliverable and of `AlgoStarkSoundInstance`'s `hextract`). `FieldIntegerLift`'s committed field-OOD
bridge produces EXACTLY that — no ℤ lift is needed or attempted. The two demonstrators below WITNESS
the composition as a term:

  * from an `OodInterpF transferV3 t` (the field OOD bundle), directly;
  * from the two genuine crypto residuals `hood` (OOD/RLC quotient identity at ζ) + `hnonexc`
    (Fiat–Shamir non-exceptionality) with the domain-geometry vanisher `vanishingPoly` already
    discharged — so the residual set reaching the AIR conjunct is EXACTLY `{hood, hnonexc}`.

Before Phase-0 this conjunct was the ℤ `MainAirAccept`, which `FieldIntegerLift.mainAirAcceptF_does_not_
imply_MainAirAcceptZ` shows is UNREACHABLE for `transferV3`'s multiplicative gates — the field-OOD
lemma could not feed it. That gap is now dissolved. -/

/-- **PAYOFF (bundle form)** — the field OOD bundle for `transferV3` produces the extraction's AIR
conjunct `MainAirAcceptF transferV3 t` directly. -/
theorem extractionAirConjunct_of_oodInterpF
    (t : VmTrace)
    (I : Dregg2.Circuit.FieldIntegerLift.OodInterpF
          Dregg2.Circuit.RotatedKernelRefinement.transferV3 t) :
    MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t :=
  Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field _ t I

/-- **PAYOFF (two-crypto-residual form)** — with the domain vanisher discharged, the extraction's AIR
conjunct `MainAirAcceptF transferV3 t` follows from EXACTLY the two crypto residuals `hood` + `hnonexc`.
This is the exact term the ℤ target could not supply. -/
theorem extractionAirConjunct_of_residuals
    (t : VmTrace)
    (hcap : t.rows.length ≤ Dregg2.Circuit.TraceColumnInterp.domainSize)
    (ζ : Dregg2.Circuit.BabyBearFriField.BabyBear)
    (qp : VmConstraint2 → Polynomial Dregg2.Circuit.BabyBearFriField.BabyBear)
    (hood : ∀ c ∈ Dregg2.Circuit.RotatedKernelRefinement.transferV3.constraints, isArith c →
        (Dregg2.Circuit.TraceColumnInterp.constraintPoly
            Dregg2.Circuit.RotatedKernelRefinement.transferV3 t c).eval ζ =
          (Dregg2.Circuit.FieldIntegerLift.vanishingPoly t).eval ζ * (qp c).eval ζ)
    (hnonexc : ∀ c ∈ Dregg2.Circuit.RotatedKernelRefinement.transferV3.constraints, isArith c →
        ζ ∉ Dregg2.Circuit.OodQuotientConsistency.exceptionalSet
          (Dregg2.Circuit.TraceColumnInterp.constraintPoly
              Dregg2.Circuit.RotatedKernelRefinement.transferV3 t c
            - Dregg2.Circuit.FieldIntegerLift.vanishingPoly t * qp c)) :
    MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t :=
  Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals
    _ t hcap ζ qp hood hnonexc

#assert_axioms extractionAirConjunct_of_oodInterpF
#assert_axioms extractionAirConjunct_of_residuals

/-! ## §7 — DISCHARGING the two fields: proven math transported ONTO each, remaining maps named.

`§3` wired the proven arity-8 proximity BETWEEN the two fields. Here we go one step further and push
proven math INTO each field, shrinking both residuals to their irreducible cross-type cores:

  * **`decode_trace` is DISCHARGED down to an OOD/leg decode.** The single hardest conjunct of
    `decode_trace`'s deliverable `TraceWitnessed` is the AIR quotient acceptance `MainAirAcceptF
    (R pi.effect) t`. That conjunct is now PRODUCED, not assumed: `FieldIntegerLift.
    ood_forces_mainAirAccept_field` turns a committed field-OOD bundle `OodInterpF (R pi.effect) t`
    into exactly `MainAirAcceptF (R pi.effect) t`. So a codeword-decode that yields the OOD bundle
    (`DeployedTraceDecode.ood_decode`) is STRICTLY WEAKER than the raw `decode_trace`: the AIR
    conjunct is transported by a proved theorem. Per `FieldIntegerLift.
    ood_forces_mainAirAccept_field_of_residuals` the OOD bundle itself reduces further to EXACTLY the
    two crypto residuals `{hood, hnonexc}` (RLC/commitment-opening + Fiat–Shamir).

  * **`accept_folds` remains the FRI column-identification residual — proximity stays load-bearing.**
    We deliberately do NOT assume `oracle ∈ friSetupK8.C` at the fold level (that would launder the
    proximity math out — `fold_complete` would make `accept_folds` free by assuming its own
    conclusion). `accept_folds` stays the pure disjoint-types map: the deployed `verifyAlgo`'s FRI
    query check (over `Int`/`BatchProofData`) realizes the abstract arity-8 fold into `friSetupK8.C'`
    (over `BabyBear`/`Fin 16`). `FriColumnIdentification` names it precisely as a `Prop`. -/

/-- **`FriColumnIdentification`** — the EXACT irreducible map behind `accept_folds`, named. It is the
disjoint-developments seam that cannot close in-tree: the deployed `verifyAlgo` runs over a generic
field (deployed at `Int`, committing FRI columns inside `BatchProofData` as Merkle-opened lists),
while `friSetupK8 : FriSetupK BabyBear (Fin 16) (Fin 2) 8` lives over `BabyBear` with the `Fin 16`
Reed–Solomon domain. This `Prop` is the committed-column ↔ abstract-oracle identification in the
`property → transcript` direction: on `verifyAlgo`-accept the committed columns, read as the abstract
oracle, fold into `friSetupK8.C'` under all `8` challenges. It is `accept_folds` verbatim — a rename
that isolates the residual. (NOT assumed `oracle ∈ friSetupK8.C`: that is what proximity PROVES from
this, `friProximityK8_discharge0`; assuming it here would launder the FRI math out.) -/
def FriColumnIdentification
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → (Fin 16 → Dregg2.Circuit.BabyBearFriField.BabyBear))
    (chal : BatchPublicInputs → BatchProof → (Fin 8 → Dregg2.Circuit.BabyBearFriField.BabyBear)) :
    Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ i, Fold friSetupK8.geom (chal pi π i) (oracle pi π) ∈ friSetupK8.C'

/-- **`DeployedTraceDecode`** — the SHRUNK residual for `DeployedTraceExtract`: `accept_folds`
UNCHANGED (the FRI column-identification, proximity load-bearing) plus `ood_decode`, the codeword
decode delivering a field-OOD bundle `OodInterpF` and the non-AIR legs — NOT the raw `MainAirAcceptF`.
The AIR conjunct is discharged by proven math (`§7` theorem below), so `ood_decode` is strictly weaker
than `DeployedFriEmbedding.decode_trace`. -/
structure DeployedTraceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Type where
  /-- The committed BabyBear column oracle the deployed proof exposes. -/
  oracle : BatchPublicInputs → BatchProof → (Fin 16 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` FRI fold challenges of the transcript. -/
  chal : BatchPublicInputs → BatchProof → (Fin 8 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` challenges are DISTINCT (arity-8 Vandermonde inverts). -/
  chal_inj : ∀ pi π, Function.Injective (chal pi π)
  /-- **VERIFIER-DECODE (unchanged)** — the FRI column-identification residual (`FriColumnIdentification`);
  proximity remains load-bearing between this and the codeword hypothesis of `ood_decode`. -/
  accept_folds :
    FriColumnIdentification perm RATE toNat params vk checks initState logN view oracle chal
  /-- **OOD-DECODE (shrunk decode)** — on accept AND the committed oracle being a genuine low-degree
  codeword, an opened `VmTrace` with a field-OOD bundle `OodInterpF (R pi.effect) t` (⟹ `MainAirAcceptF`
  by proven math) plus all the non-AIR `TraceWitnessed` legs and the published-commit link. -/
  ood_decode : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    oracle pi π ∈ friSetupK8.C →
    ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
        (_ood : Dregg2.Circuit.FieldIntegerLift.OodInterpF (R pi.effect) t),
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

/-- **`deployedFriEmbedding_of_traceDecode` — `decode_trace` DISCHARGED via proven OOD→AIR math.**
Build the full `DeployedFriEmbedding` from the shrunk `DeployedTraceDecode`: `accept_folds` passes
through (same FRI column-identification residual, proximity untouched); `decode_trace` is CONSTRUCTED —
the OOD bundle from `ood_decode` is turned into the `MainAirAcceptF` conjunct by the PROVED
`FieldIntegerLift.ood_forces_mainAirAccept_field`, and the remaining legs pass through. So the raw
`decode_trace` obligation is replaced by the strictly weaker OOD/leg decode, with the AIR-acceptance
conjunct now supplied by a theorem rather than assumed. (A `def`: `DeployedFriEmbedding` is `Type`,
carrying the two decode functions as data.) -/
def deployedFriEmbedding_of_traceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view) :
    DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view where
  oracle := dec.oracle
  chal := dec.chal
  chal_inj := dec.chal_inj
  accept_folds := dec.accept_folds
  decode_trace := by
    intro pi π hacc hcw
    obtain ⟨minit, mfin, maddrs, t, hOod, hbus, hHashes, hRanges,
      hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩ := dec.ood_decode pi π hacc hcw
    exact ⟨minit, mfin, maddrs, t,
      Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field (R pi.effect) t hOod,
      hbus, hHashes, hRanges, hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩

/-- **`deployedTraceExtract_of_traceDecode`** — the opaque `DeployedTraceExtract` from the shrunk
residual, with BOTH proven links load-bearing: proximity (`§3`) between the two fields, and the
OOD→AIR bridge (`§7`) inside `decode_trace`. -/
theorem deployedTraceExtract_of_traceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view :=
  deployedTraceExtract_of_embedding hash R perm RATE toNat params vk checks initState logN view
    (deployedFriEmbedding_of_traceDecode hash R perm RATE toNat params vk checks initState logN view dec)

/-- **`starkSound_of_traceDecode_and_refines` — `[StarkSound]` from the shrunk residual + code
refinement.** The apex carrier from (i) the `DeployedTraceDecode` (the FRI column-identification map +
the OOD/leg decode; the arity-8 proximity AND the OOD→AIR bridge PROVED between/inside them) and (ii)
`DeployedRefines`. The math residual is now: one cross-type FRI column-identification (`accept_folds`)
and one codeword→OOD/leg decode, whose AIR conjunct further reduces to `{hood, hnonexc}`. -/
theorem starkSound_of_traceDecode_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  starkSound_of_embedding_and_refines hash R perm RATE toNat params vk checks initState logN view
    (deployedFriEmbedding_of_traceDecode hash R perm RATE toNat params vk checks initState logN view dec)
    href

#assert_axioms deployedFriEmbedding_of_traceDecode
#assert_axioms deployedTraceExtract_of_traceDecode
#assert_axioms starkSound_of_traceDecode_and_refines

/-! ### §7 TEETH — the OOD→AIR transport is genuine (load-bearing, both polarities).

The shrunk `ood_decode`'s AIR-acceptance conjunct is produced by proven math and is a real obligation:
the OOD bundle FIRES to `MainAirAcceptF` on honest data and the target conjunct BITES on a tampered
gate. Reuses the committed `FieldIntegerLift` / `AirChecksSatisfied` witnesses. -/

/-- **OOD→AIR FIRES** — a field-OOD bundle for `transferV3` yields the `MainAirAcceptF` conjunct that
`deployedFriEmbedding_of_traceDecode` needs, so the OOD-decode transport is non-vacuous. -/
theorem oodDecode_air_fires
    (t : VmTrace)
    (I : Dregg2.Circuit.FieldIntegerLift.OodInterpF
          Dregg2.Circuit.RotatedKernelRefinement.transferV3 t) :
    MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t :=
  Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field _ t I

/-- **OOD→AIR BITES** — the `MainAirAcceptF` the transport must produce is FALSIFIABLE: a tampered-gate
trace cannot meet it, so `ood_decode` cannot be satisfied by a lying trace even with the OOD softening. -/
theorem oodDecode_air_bites :
    ¬ MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unacceptedF

#assert_axioms oodDecode_air_fires
#assert_axioms oodDecode_air_bites

end Dregg2.Circuit.DeployedTraceExtract
