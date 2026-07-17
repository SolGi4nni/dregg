/-
# Dregg2.AssuranceCaseGrounded — the DEPLOYED capstone re-rested on the crypto floor.

`AssuranceCase.deployed_system_secure` (the composed A∧B∧C∧D∧E apex over ONE deployed turn)
discharges guarantee E — light-client unfoolability — by consuming an ASSUMED
`es : EngineSound …` (`AssuranceCase.lean:903`, fed to `light_client_verifies_whole_history`
at `:936` and `conserves_from_verification` at `:939`). `EngineSound` bundles THREE soundness
legs as a hypothesis: `recursive_sound` (FRI), `leaf_sound` (per-leaf executor binding), and
`binding_sound` (the chain-ordering tooth). Two of those three were SHRUNK to the crypto floor
this session in `Dregg2.Circuit.GroundedApex`:

  * `leaf_sound` → DERIVED by `engineSound_of_refinements` from a `Forall₂ LeafRefinement`
    family (the per-effect `descriptorRefines` realizer data the honest prover supplies);
  * `binding_sound` → DISCHARGED by `binding_air_discharges_binding_sound` from a satisfying
    represented `TurnChainBindingAir` trace (`BindingExtract`, the binding-AIR realizer data),
    with NO crypto at all;
  * `recursive_sound` → carried as the named FRI carrier `hrec` (the one honest residual; the
    per-node content is reduced by `AggAirSound`, the whole-tree fold is not yet composed).

This file performs the migration the grounded-apex agent named, ADDITIVELY: it states
`deployed_system_secure_grounded`, whose conclusion is the SAME A∧B∧C∧D∧E conjunction as
`deployed_system_secure`, but whose guarantee-E leg threads an `EngineSound` DERIVED on the
spot by `GroundedApex.engineSound_grounded` from the crypto floor + the honest prover's realizer
data — so the assumed `EngineSound` hypothesis is GONE from the capstone's premise list. Nothing
upstream is mutated: `deployed_system_secure` and its every citation are untouched; this theorem
CALLS it, supplying the derived engine for `es`. Guarantees A–D pass through byte-for-byte (they
are orthogonal to the four carriers — they read the committed forest / noteSpend, not the engine).

## What the deployed capstone now trusts (vs before)

  BEFORE: `{Poseidon2-CR (the §8 commitment carriers), FRI/STARK soundness}` + an ASSUMED
          `EngineSound` (which itself bundled the leaf-binding and chain-ordering soundness as
          opaque hypotheses).
  AFTER:  `{Poseidon2-CR (the same §8 carriers: hCmb/hCompress/hCompressN/hLeaf/hRest + the
          sponge `Poseidon2SpongeCR hCR`), FRI recursion soundness (`hrec`)}` + the honest
          prover's REALIZER DATA (`hleaves` = the per-effect `LeafRefinement`/`descriptorRefines`
          family, `hbindExtract` = the represented binding-AIR trace). NO assumed `EngineSound`.

The leaf-binding and chain-ordering legs are no longer trusted — they are DERIVED. The residual
is strictly `{crypto floor + honest-prover realizer data}`. `#assert_axioms`-clean
(⊆ {propext, Classical.choice, Quot.sound}; every carrier a Prop/struct hypothesis, no fresh
axiom, no `sorry`). Standalone: `lake build Dregg2.AssuranceCaseGrounded`.

The file also exports `GroundedAssuranceWithCrypto`: the exact A–E outcome bundled with the existing
real-dimension ML-KEM, weighted-BLS, DECO-payment, and Hermine CR+Module-SIS reductions. This closes the
proof-suite composition gap, not the deployed-consumer correspondence: showing one concrete run's
handshake/certificate/attestation/commit-reveal values instantiate those parameters remains named.
-/
import Dregg2.AssuranceCase
import Dregg2.Circuit.GroundedApex
import Dregg2.Crypto.MlKemFips203FullDim
import Dregg2.Crypto.BlsThreshold
import Dregg2.Crypto.Deco
import Dregg2.Crypto.HermineHashCRRegrounded

namespace Dregg2.AssuranceCaseGrounded

-- mirror the scope `AssuranceCase`'s Composed section + file-level opens establish, so the
-- A∧B∧C∧D∧E conclusion and the running-entry / aggregate argument types resolve identically.
open Dregg2.Exec
open Dregg2.Circuit
open Dregg2.Authority
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForest
open Dregg2.Exec.ForestMemoryProgram (MemProgTrans EachStepMemProg)
open Dregg2.Circuit.Argus (interp noteSpendStmt)
open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation
  (ChainStep KernelGenesisPin SeamStruct lastStateOf honestStep)
open Dregg2.Circuit.StateCommit
  (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)
-- the grounded-apex carriers + floor names:
open Dregg2.AssuranceCase (deployed_system_secure)
open Dregg2.Circuit.GroundedApex (engineSound_grounded engineSound_grounded_v2 BindingExtract)
open Dregg2.Circuit.RecursiveSoundFromNodes
  (PTree NodeCarrier rootP leavesP honestTree honest_node_carrier)
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.WitnessRealizing (LeafRefinement)
open Dregg2.Circuit.BindingAirSound
  (rowOf pubOf satisfies_one represents_one foldedFinalRoot_eq_lastNew)

-- the forest's descriptor phantom types + the gate typeclasses (exactly as `Composed`).
variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]
-- the aggregate's proof carrier + verifier + the §8 commitment portal (the unfoolability layer).
variable {AProof : Type} (verify : AProof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`deployed_system_secure_grounded` (THE GROUNDED COMPOSED APEX — A∧B∧C∧D∧E, on the floor).**
The SAME conjunction `deployed_system_secure` proves — over the SAME committed running-entry forest
`execFullForestG s f = some s'` (A∧B∧C), the SAME committed noteSpend (D), and the SAME published
recursion aggregate a light client checks with ONE `verify agg.root` (E) — but with guarantee E's
whole-history leg routed through `GroundedApex.engineSound_grounded`: the assumed `EngineSound`
hypothesis is REPLACED by the crypto floor (`hCR : Poseidon2SpongeCR hash`, the §8 commitment
injectivity carriers `hCmb`/`hCompress`/`hCompressN`/`hLeaf`/`hRest`) + the honest prover's REALIZER
DATA (`hleaves` = the per-effect `LeafRefinement`/`descriptorRefines` family that DERIVES `leaf_sound`,
`hbindExtract` = the represented binding-AIR trace that DISCHARGES `binding_sound`) + the ONE named FRI
residual `hrec` (= `recursive_sound`, the recursion floor — carried, not axiomatized).

Guarantees A–D are UNCHANGED: they read the committed forest / noteSpend, orthogonal to the four
carriers, so they pass through `deployed_system_secure` byte-for-byte. The capstone's premise list no
longer carries an assumed `EngineSound`; it carries strictly `{crypto floor + realizer data}`. -/
theorem deployed_system_secure_grounded
    -- A/B/C(c1+c2): the running-entry forest the node committed (UNCHANGED from the capstone).
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId)
    (hrun : execFullForestG s f = some s')
    (UC : Dregg2.Exec.UniversalBridge.UCodec)
    (hcov : EachStepMemProg UC (lowerForestG f))
    -- D: a committed noteSpend on the executable term IR (UNCHANGED).
    {nf : Nat} {k k' : RecordKernelState}
    (hspend : interp (noteSpendStmt nf) k = some k')
    -- E: the published recursion aggregate + the GROUNDED inputs in place of `es : EngineSound …`.
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep)
    (hleaves : List.Forall₂
      (fun (p : AProof) (st : ChainStep) => Nonempty (LeafRefinement AProof verify hash S p st))
      agg.leafProofs steps)
    (hbindExtract : BindingExtract AProof verify hash CH RH cmb compress compressN agg steps)
    (hrec : verify agg.root = true →
      (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true)
    (hroot : verify agg.root = true)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (hgen : KernelGenesisPin g steps) (hstruct : SeamStruct steps) :
    -- A:
    (∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2)
    -- B:
    ∧ recTotalAsset s'.kernel b = recTotalAsset s.kernel b
    -- C(c1): per-node attestation
    ∧ (∀ p ∈ lowerForestG f, ∃ sa sa',
        execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa')
    -- C(c2): the WHOLE TURN is a memory program
    ∧ MemProgTrans UC s s'
    -- D: freshness (no double-spend)
    ∧ (nf ∉ k.nullifiers ∧ nf ∈ k'.nullifiers ∧ interp (noteSpendStmt nf) k' = none)
    -- E: unfoolability — whole-history attestation + conservation FROM VERIFICATION
    ∧ AggregateAttests AProof CH RH cmb compress compressN agg g steps
    ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  -- A–D pass through `deployed_system_secure` untouched; guarantee E's `es` is DERIVED on the spot
  -- from the crypto floor + realizer data by `engineSound_grounded` (binding_sound + leaf_sound
  -- discharged; only `hrec` carried). The assumed `EngineSound` premise is GONE.
  deployed_system_secure
    (verify := verify) (CH := CH) (RH := RH) (cmb := cmb) (compress := compress)
    (compressN := compressN)
    (s := s) (s' := s') (f := f) (b := b) (hrun := hrun)
    (UC := UC) (hcov := hcov) (hspend := hspend)
    (agg := agg) (g := g) (steps := steps)
    (es := engineSound_grounded AProof verify hash S hCR CH RH cmb compress compressN
            agg g steps hleaves hbindExtract hrec)
    (hroot := hroot)
    (hCmb := hCmb) (hCompress := hCompress) (hCompressN := hCompressN)
    (hLeaf := hLeaf) (hRest := hRest) (hgen := hgen) (hstruct := hstruct)

#assert_axioms deployed_system_secure_grounded

/-- **`deployed_system_secure_grounded_v2` (THE GROUNDED COMPOSED APEX — NO CARRIED FRI).** Same
conclusion as `deployed_system_secure_grounded`, but guarantee E's recursion leg no longer carries the
whole-tree FRI hypothesis `hrec`: in its place a proof-carrying aggregation tree `t` + the per-node
`NodeCarrier hc` (the localized `AggAirSound.FriExtract` floor over one node + its two children) + the
wrapping facts, from which `engineSound_grounded_v2` DERIVES `recursive_sound` by the whole-tree fold
(`RecursiveSoundFromNodes`). So the deployed capstone now trusts strictly
`{the per-node FriExtract floor `hc`, Poseidon CR (the sponge `hCR` + the §8 injectivity carriers), the
named `CommitSurface` set}` + the honest prover's realizer data (`hleaves`, `hbindExtract`) — with
`recursive_sound`, `leaf_sound`, and `binding_sound` ALL derived: NO assumed `EngineSound`, NO carried
whole-tree recursion hypothesis. Guarantees A–D pass through `deployed_system_secure` byte-for-byte. -/
theorem deployed_system_secure_grounded_v2
    -- A/B/C(c1+c2): the running-entry forest the node committed (UNCHANGED from the capstone).
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId)
    (hrun : execFullForestG s f = some s')
    (UC : Dregg2.Exec.UniversalBridge.UCodec)
    (hcov : EachStepMemProg UC (lowerForestG f))
    -- D: a committed noteSpend on the executable term IR (UNCHANGED).
    {nf : Nat} {k k' : RecordKernelState}
    (hspend : interp (noteSpendStmt nf) k = some k')
    -- E: the published recursion aggregate + the GROUNDED-v2 inputs (per-node carrier, NOT `hrec`).
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (H : ℤ → ℤ → ℤ)
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep)
    (hleaves : List.Forall₂
      (fun (p : AProof) (st : ChainStep) => Nonempty (LeafRefinement AProof verify hash S p st))
      agg.leafProofs steps)
    (hbindExtract : BindingExtract AProof verify hash CH RH cmb compress compressN agg steps)
    (t : PTree AProof)
    (hc : NodeCarrier verify H t)
    (htroot : rootP t = agg.root)
    (hwrap : ∀ p ∈ agg.leafProofs, p ∈ leavesP t)
    (hbindleaf : agg.bindingProof ∈ leavesP t)
    (hroot : verify agg.root = true)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (hgen : KernelGenesisPin g steps) (hstruct : SeamStruct steps) :
    -- A:
    (∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2)
    -- B:
    ∧ recTotalAsset s'.kernel b = recTotalAsset s.kernel b
    -- C(c1): per-node attestation
    ∧ (∀ p ∈ lowerForestG f, ∃ sa sa',
        execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa')
    -- C(c2): the WHOLE TURN is a memory program
    ∧ MemProgTrans UC s s'
    -- D: freshness (no double-spend)
    ∧ (nf ∉ k.nullifiers ∧ nf ∈ k'.nullifiers ∧ interp (noteSpendStmt nf) k' = none)
    -- E: unfoolability — whole-history attestation + conservation FROM VERIFICATION
    ∧ AggregateAttests AProof CH RH cmb compress compressN agg g steps
    ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  -- A–D pass through `deployed_system_secure` untouched; guarantee E's `es` is DERIVED on the spot with
  -- ALL THREE EngineSound legs grounded — `recursive_sound` now off the per-node carrier fold, not `hrec`.
  deployed_system_secure
    (verify := verify) (CH := CH) (RH := RH) (cmb := cmb) (compress := compress)
    (compressN := compressN)
    (s := s) (s' := s') (f := f) (b := b) (hrun := hrun)
    (UC := UC) (hcov := hcov) (hspend := hspend)
    (agg := agg) (g := g) (steps := steps)
    (es := engineSound_grounded_v2 AProof verify hash S hCR CH RH cmb compress compressN H
            agg g steps hleaves hbindExtract t hc htroot hwrap hbindleaf)
    (hroot := hroot)
    (hCmb := hCmb) (hCompress := hCompress) (hCompressN := hCompressN)
    (hLeaf := hLeaf) (hRest := hRest) (hgen := hgen) (hstruct := hstruct)

#assert_axioms deployed_system_secure_grounded_v2

/-! ## Non-vacuity — the E-grounded engine FIRES on a real honest chain.

The migration's only delta is guarantee E: where the original capstone took an assumed
`es : EngineSound`, the grounded capstone DERIVES it via `engineSound_grounded`. Guarantees A–D
read the committed forest / noteSpend verbatim, so their inputs are exactly the original capstone's.
We therefore exhibit non-vacuity of the DELTA — the derived engine — on the honest teeth-genesis
chain (`teethGenesis ⟶ honestStep.post`), reusing the grounded apex's concrete realizer pieces: the
binding-AIR extraction is discharged CONCRETELY (`satisfies_one`/`represents_one` — so the keystone
`binding_air_discharges_binding_sound` is genuinely load-bearing), the recursion leg is the honest
accepting verifier, and the ONLY non-concrete input is the per-leaf `Forall₂ LeafRefinement` under the
accepting verifier — the SAME audited `Satisfied2`/STARK floor every grounded module carries (named
`hleaves`, not a hole). So the engine the grounded capstone threads into E is inhabited on a real
executor run, and concludes a TRUE executor fact. -/
theorem grounded_capstone_engine_fires
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (hleaves : List.Forall₂
      (fun (p : RealProof) (st : ChainStep) => Nonempty (LeafRefinement RealProof acceptAll hash S p st))
      realAggregate.leafProofs realSteps) :
    AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN realAggregate teethGenesis realSteps := by
  -- the binding-AIR extraction, discharged concretely on the honest step (as in `GroundedApex`).
  have hbe : BindingExtract RealProof acceptAll hash zCH zRH zcmb zcompress zcompressN
      realAggregate realSteps := by
    intro _
    refine ⟨[rowOf zCH zRH zcmb zcompress zcompressN honestStep],
            pubOf zCH zRH zcmb zcompress zcompressN hash honestStep,
            satisfies_one zCH zRH zcmb zcompress zcompressN hash honestStep,
            represents_one zCH zRH zcmb zcompress zcompressN honestStep, rfl, ?_⟩
    show realAggregate.finalRoot = (pubOf zCH zRH zcmb zcompress zcompressN hash honestStep).final
    simp only [realAggregate, pubOf, realSteps]
    exact foldedFinalRoot_eq_lastNew zCH zRH zcmb zcompress zcompressN teethGenesis [honestStep]
      honestStep (by simp)
  have hrec : acceptAll realAggregate.root = true →
      (∀ p ∈ realAggregate.leafProofs, acceptAll p = true)
        ∧ acceptAll realAggregate.bindingProof = true :=
    fun _ => ⟨fun _ _ => rfl, rfl⟩
  -- the engine the grounded capstone threads into E, on the honest chain — then the whole-history apex.
  exact light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps
    (engineSound_grounded RealProof acceptAll hash S hCR zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps hleaves hbe hrec)
    rfl

#assert_axioms grounded_capstone_engine_fires

/-- **`grounded_capstone_engine_fires_v2` (THE NO-CARRIED-FRI E-ENGINE FIRES).** As
`grounded_capstone_engine_fires`, but the engine threaded into guarantee E is `engineSound_grounded_v2`:
the carried `hrec` is replaced by the concrete honest proof-carrying tree `honestTree` and its per-node
carrier `honest_node_carrier`. So the whole-tree recursion fold is genuinely LOAD-BEARING in the firing —
`recursive_sound` is DERIVED — and the grounded capstone's E-leg still concludes the real whole-history
`AggregateAttests`. The only non-concrete input remains the per-leaf `Forall₂ LeafRefinement` (the audited
STARK floor). -/
theorem grounded_capstone_engine_fires_v2
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (hleaves : List.Forall₂
      (fun (p : RealProof) (st : ChainStep) => Nonempty (LeafRefinement RealProof acceptAll hash S p st))
      realAggregate.leafProofs realSteps) :
    AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN realAggregate teethGenesis realSteps := by
  have hbe : BindingExtract RealProof acceptAll hash zCH zRH zcmb zcompress zcompressN
      realAggregate realSteps := by
    intro _
    refine ⟨[rowOf zCH zRH zcmb zcompress zcompressN honestStep],
            pubOf zCH zRH zcmb zcompress zcompressN hash honestStep,
            satisfies_one zCH zRH zcmb zcompress zcompressN hash honestStep,
            represents_one zCH zRH zcmb zcompress zcompressN honestStep, rfl, ?_⟩
    show realAggregate.finalRoot = (pubOf zCH zRH zcmb zcompress zcompressN hash honestStep).final
    simp only [realAggregate, pubOf, realSteps]
    exact foldedFinalRoot_eq_lastNew zCH zRH zcmb zcompress zcompressN teethGenesis [honestStep]
      honestStep (by simp)
  -- the carried `hrec` is GONE: the recursion leg comes from the concrete honest tree + per-node carrier.
  exact light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps
    (engineSound_grounded_v2 RealProof acceptAll hash S hCR zCH zRH zcmb zcompress zcompressN
      Dregg2.Circuit.RecursiveSoundFromNodes.zH
      realAggregate teethGenesis realSteps hleaves hbe
      honestTree honest_node_carrier rfl
      (by intro p _; cases p; simp [leavesP, honestTree])
      (by simp [leavesP, honestTree, realAggregate]))
    rfl

#assert_axioms grounded_capstone_engine_fires_v2

/-! ## The broader crypto reduction suite, composed without laundering deployment use.

The historical capstone imported none of the ML-KEM/BLS/DECO/Hermine results, so even their proved
reductions were invisible at the assurance apex.  `BroaderCryptoReductionSuite` collects their exact
strongest reusable conclusions: real-dimension FIPS-203 correctness, weighted-quorum extraction,
authenticated-payment extraction, and the Hermine concurrent-forgery advantage bound — the last now at
its REPAIRED strength (a genuine union-bound reduction onto the MSIS and commit-collision games at
EXPLICIT `Eff` classes, not the pre-`4fe326cce` free-ensemble `MSISHardQuantShape` P→P; see the field's
own note).
It does not claim that every deployed turn invokes all four mechanisms.  The remaining protocol-use
binding — identifying the concrete handshake/certificate/DECO/commit-reveal values consumed on one run
with these theorem parameters — stays named separately in the horizon ledger. -/

/-- A single axiom-clean package of the four already-proved crypto reductions.  Each field retains the
real hypotheses and conclusion of its source theorem; no field is weakened to a Boolean label. -/
structure BroaderCryptoReductionSuite : Prop where
  mlkem768 : ∀ (m : List UInt8), m.length = 32 →
    Dregg2.Crypto.DreggKemRefinement.Fips203Correct
      (Dregg2.Crypto.MlKemFips203FullDim.fullKemApi m)
  bls_quorum : ∀ {PK : Type} {C : Dregg2.Crypto.BlsThreshold.Committee PK} {msg : Nat}
    (cert : Dregg2.Crypto.BlsThreshold.ThresholdCert C msg),
    cert.accepts → cert.SnarkContract → cert.BlsContract →
    ∃ S : Finset Nat,
      S ⊆ C.members ∧
      C.selectedWeight S ≥ cert.threshold ∧
      C.selectedWeight S ≤ C.totalWeight ∧
      (∀ i ∈ S, C.SignedBy i msg)
  deco_payment : ∀ {Dg Proof : Type}
    [KD : Dregg2.Crypto.Deco.DecoVerifierKernel Dg Proof]
    [SK : Dregg2.Crypto.PortalFloor.SignatureKernel Dg Dg Dg]
    [MK : Dregg2.Crypto.PortalFloor.MacKernelE Dg Dg Dg],
    KD.sigVerify = SK.sigVerify → KD.macVerify = MK.verifyTag →
    KD.extractable → SK.unforgeable → MK.unforgeable →
    ∀ (stmt : Dregg2.Crypto.Deco.Statement Dg) (proof : Proof),
      KD.verify stmt proof = true →
      ∃ w : Dregg2.Crypto.Deco.CircuitIR Dg,
        SK.Signed stmt.serverKey w.sessionKey ∧
        MK.Tagged w.sessionKey w.transcriptCommit w.tag ∧
        w.transcriptCommit = KD.compress (KD.encode stmt.facts) w.salt ∧
        1 ≤ stmt.facts.amountCents
  /-- ⚑ RE-STATED 07-17 to mirror `hermine_concurrent_forgery_advantage_bound`'s REPAIRED signature
  (`4fe326cce`), which this field had silently fallen behind — the suite still declared the PRE-repair
  shape (`MSISHardQuantShape adv` on a FREE ensemble, discharged by `hmsis solver`: the content-free
  `P → P` that `VACUITY-SWEEP.md` FINDING 1 documented at this exact site), so the capstone was
  advertising the laundered bound the repair had already deleted. The signature change made this a type
  error; nothing here weakens, and the field now carries the REAL reduction: the forger is a first-class
  game, its advantage is union-bounded by the advantages of the MSIS solver and commit-collision finder
  EXTRACTED from it, and both floors bite at those extracted adversaries under an EXPLICIT `Eff` class
  (undischarged — the tree has no cost model, `FloorGames` §8). -/
  hermine_rushing : ∀ (F : Dregg2.Crypto.HermineHashCRRegrounded.ConcurrentForgeryFamily)
    (Eff : Dregg2.Crypto.FloorGames.Adversary
      (Dregg2.Crypto.FloorGames.msisGame
        (Dregg2.Crypto.HermineHashCRRegrounded.cfMsisFamily F)) → Prop)
    (EffH : Dregg2.Crypto.FloorGames.Adversary
      (Dregg2.Crypto.HermineHashCRRegrounded.cfEquivGame F) → Prop)
    (A : Dregg2.Crypto.FloorGames.Adversary
      (Dregg2.Crypto.HermineHashCRRegrounded.concurrentForgeryGame F)),
    Eff (Dregg2.Crypto.HermineHashCRRegrounded.forgeryToMsisSolver F A) →
    EffH (Dregg2.Crypto.HermineHashCRRegrounded.forgeryToEquivFinder F A) →
    Dregg2.Crypto.FloorGames.MSISHardQuant
      (Dregg2.Crypto.HermineHashCRRegrounded.cfMsisFamily F) Eff →
    Dregg2.Crypto.FloorGames.Hard (Dregg2.Crypto.HermineHashCRRegrounded.cfEquivGame F) EffH →
    Dregg2.Crypto.ConcreteSecurity.Negl
      (Dregg2.Crypto.FloorGames.gameAdv
        (Dregg2.Crypto.HermineHashCRRegrounded.concurrentForgeryGame F) A)

/-- The wider suite is genuinely assembled from the four reduction theorems, rather than merely
co-imported. -/
theorem broader_crypto_reduction_suite : BroaderCryptoReductionSuite where
  mlkem768 := Dregg2.Crypto.MlKemFips203FullDim.fullKemApi_fips203
  bls_quorum := Dregg2.Crypto.BlsThreshold.accepting_cert_has_quorum
  deco_payment := by
    intro Dg Proof KD SK MK hsig hmac hext hsigFloor hmacFloor stmt proof hacc
    exact Dregg2.Crypto.Deco.deco_authenticates_payment
      hsig hmac hext hsigFloor hmacFloor stmt proof hacc
  hermine_rushing := Dregg2.Crypto.HermineHashCRRegrounded.hermine_concurrent_forgery_advantage_bound

#assert_axioms broader_crypto_reduction_suite

/-- The exact A–E conclusion of the grounded capstone, factored as a named proposition so the wider
crypto suite can attach to the real system guarantee rather than an arbitrary `Core : Prop`. -/
def GroundedCoreOutcome
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId) (UC : Dregg2.Exec.UniversalBridge.UCodec)
    (nf : Nat) (k k' : RecordKernelState)
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep) : Prop :=
  (∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2)
  ∧ recTotalAsset s'.kernel b = recTotalAsset s.kernel b
  ∧ (∀ p ∈ lowerForestG f, ∃ sa sa',
      execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa')
  ∧ MemProgTrans UC s s'
  ∧ (nf ∉ k.nullifiers ∧ nf ∈ k'.nullifiers ∧ interp (noteSpendStmt nf) k' = none)
  ∧ AggregateAttests AProof CH RH cmb compress compressN agg g steps
  ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel

/-- The actual grounded A–E assurance outcome together with the four broader crypto reductions.  This
closes the proof-suite composition gap while deliberately leaving the concrete consumer/value binding
as a separate deployment residual. -/
def GroundedAssuranceWithCrypto
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId) (UC : Dregg2.Exec.UniversalBridge.UCodec)
    (nf : Nat) (k k' : RecordKernelState)
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep) : Prop :=
  GroundedCoreOutcome (CH := CH) (RH := RH) (cmb := cmb) (compress := compress)
    (compressN := compressN) s s' f b UC nf k k' agg g steps ∧
  BroaderCryptoReductionSuite

/-- **Top-level suite fusion.**  Any concrete result of `deployed_system_secure_grounded{,_v2}` can be
re-read definitionally as `GroundedCoreOutcome`; this theorem attaches all four proved crypto
reductions without adding a premise or axiom. -/
theorem grounded_assurance_with_crypto_of_core
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId) (UC : Dregg2.Exec.UniversalBridge.UCodec)
    (nf : Nat) (k k' : RecordKernelState)
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep)
    (hcore : GroundedCoreOutcome (CH := CH) (RH := RH) (cmb := cmb) (compress := compress)
      (compressN := compressN) s s' f b UC nf k k' agg g steps) :
    GroundedAssuranceWithCrypto (CH := CH) (RH := RH) (cmb := cmb) (compress := compress)
      (compressN := compressN) s s' f b UC nf k k' agg g steps :=
  ⟨hcore, broader_crypto_reduction_suite⟩

#assert_axioms grounded_assurance_with_crypto_of_core

end Dregg2.AssuranceCaseGrounded
