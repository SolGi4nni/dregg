/-
# Path of Angels fhEgg / DrEX privacy topology

This module is the deliberately unglamorous map of who sees what in the
currently exercised Dark Bazaar path.  It does not turn an operator-visible
opening check into "house blindness", and it does not turn authenticated
PartyMPC transport into malicious-secure computation.

The topology matches the exercised pipeline:

* the source verifier receives each plaintext order and its encryption opening;
* four BFV custodians run a 3-of-4 opening, with one allowed to be offline;
* three live MPC parties receive additive curve shares and private preprocessing;
* the transport router sees routes, ciphertexts, masked openings, and the result;
* the ordinary PoA audience receives the crossing and atomic custody receipt.

The executable counterparts are
`dreggnet-market/tests/poa_dark_bazaar_protocol.rs` (PoA receipt-bound
opening-aware clearing), `dreggnet-market/tests/descent_fhegg_settlement.rs`
(3-of-4 fhEgg + PartyMPC + atomic custody), and
`dreggnet-market/src/fhegg_atomic_asset.rs` (the custody transaction).

The finite `OperatorView` table is a deployment contract, not a cryptographic
theorem.  The cryptographic/algebraic claims below are wrappers around the
actual market theorems: additive shares hide from a coalition missing one MPC
party, full collusion does not; the deterministic MPC view factors through the
crossing; the deployed smudging bound hides the modelled book-dependent noise
channel; and authenticated transport still does not prove honest arithmetic.

Honest residuals remain named.  RLWE security, ciphertext indistinguishability,
signature/AEAD unforgeability, DKG shortness, transcript-wide smudging
composition, malicious-secure MPC, and the PoA judged-salvage mint are not
proved here.
-/

import Market.DarkBazaarCollectiveOpening
import Market.MpcClearingSecurity
import Market.PartyMpcTransportBoundary
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.FheggPrivacyTopology

set_option autoImplicit false

/-! ## Exact deployed roles and views -/

inductive Operator where
  | sourceVerifier
  | bfvCustodian
  | mpcParty
  | mpcCoordinator
  | transportRouter
  | audience
deriving DecidableEq, Repr

/-- Every field is a positive statement about material delivered to that role.
`false` means the protocol does not intentionally place that material in the
role's view; it is not an indistinguishability proof about correlated bytes. -/
structure OperatorView where
  plaintextOrders : Bool
  encryptionOpenings : Bool
  signedCiphertexts : Bool
  ownBfvKeyShare : Bool
  ownMaskedCurveShare : Bool
  ownArithmeticShare : Bool
  ownBeaverPreprocessing : Bool
  routeMetadata : Bool
  encryptedPeerFrames : Bool
  maskedPublicOpenings : Bool
  crossing : Bool
  atomicCustodyReceipt : Bool
deriving DecidableEq, Repr

def view : Operator → OperatorView
  | .sourceVerifier =>
      { plaintextOrders := true
        encryptionOpenings := true
        signedCiphertexts := true
        ownBfvKeyShare := false
        ownMaskedCurveShare := false
        ownArithmeticShare := false
        ownBeaverPreprocessing := false
        routeMetadata := false
        encryptedPeerFrames := false
        maskedPublicOpenings := false
        crossing := true
        atomicCustodyReceipt := true }
  | .bfvCustodian =>
      { plaintextOrders := false
        encryptionOpenings := false
        signedCiphertexts := true
        ownBfvKeyShare := true
        ownMaskedCurveShare := true
        ownArithmeticShare := false
        ownBeaverPreprocessing := false
        routeMetadata := false
        encryptedPeerFrames := false
        maskedPublicOpenings := true
        crossing := true
        atomicCustodyReceipt := true }
  | .mpcParty =>
      { plaintextOrders := false
        encryptionOpenings := false
        signedCiphertexts := true
        ownBfvKeyShare := false
        ownMaskedCurveShare := false
        ownArithmeticShare := true
        ownBeaverPreprocessing := true
        routeMetadata := true
        encryptedPeerFrames := true
        maskedPublicOpenings := true
        crossing := true
        atomicCustodyReceipt := true }
  | .mpcCoordinator =>
      { plaintextOrders := false
        encryptionOpenings := false
        signedCiphertexts := true
        ownBfvKeyShare := false
        ownMaskedCurveShare := false
        ownArithmeticShare := false
        ownBeaverPreprocessing := false
        routeMetadata := true
        encryptedPeerFrames := true
        maskedPublicOpenings := true
        crossing := true
        atomicCustodyReceipt := true }
  | .transportRouter =>
      { plaintextOrders := false
        encryptionOpenings := false
        signedCiphertexts := false
        ownBfvKeyShare := false
        ownMaskedCurveShare := false
        ownArithmeticShare := false
        ownBeaverPreprocessing := false
        routeMetadata := true
        encryptedPeerFrames := true
        maskedPublicOpenings := true
        crossing := true
        atomicCustodyReceipt := false }
  | .audience =>
      { plaintextOrders := false
        encryptionOpenings := false
        signedCiphertexts := false
        ownBfvKeyShare := false
        ownMaskedCurveShare := false
        ownArithmeticShare := false
        ownBeaverPreprocessing := false
        routeMetadata := false
        encryptedPeerFrames := false
        maskedPublicOpenings := false
        crossing := true
        atomicCustodyReceipt := true }

theorem source_verifier_view_is_opening_aware :
    (view .sourceVerifier).plaintextOrders = true ∧
    (view .sourceVerifier).encryptionOpenings = true ∧
    (view .sourceVerifier).ownBfvKeyShare = false := by
  decide

theorem single_bfv_custodian_view_is_not_the_book :
    (view .bfvCustodian).plaintextOrders = false ∧
    (view .bfvCustodian).encryptionOpenings = false ∧
    (view .bfvCustodian).ownBfvKeyShare = true ∧
    (view .bfvCustodian).ownMaskedCurveShare = true := by
  decide

theorem single_mpc_party_view_names_its_private_inputs :
    (view .mpcParty).plaintextOrders = false ∧
    (view .mpcParty).ownArithmeticShare = true ∧
    (view .mpcParty).ownBeaverPreprocessing = true ∧
    (view .mpcParty).crossing = true := by
  decide

theorem coordinator_and_router_do_not_receive_raw_orders :
    (view .mpcCoordinator).plaintextOrders = false ∧
    (view .transportRouter).plaintextOrders = false ∧
    (view .mpcCoordinator).maskedPublicOpenings = true ∧
    (view .transportRouter).encryptedPeerFrames = true := by
  decide

theorem audience_receives_only_the_game_consequence_fields :
    (view .audience).plaintextOrders = false ∧
    (view .audience).encryptionOpenings = false ∧
    (view .audience).ownBfvKeyShare = false ∧
    (view .audience).ownArithmeticShare = false ∧
    (view .audience).maskedPublicOpenings = false ∧
    (view .audience).crossing = true ∧
    (view .audience).atomicCustodyReceipt = true := by
  decide

/-! ## Privacy labels that the topology can and cannot support -/

inductive PrivacyClaim where
  | audienceReceiptOmitsOrders
  | sourceOperatorHouseBlind
  | oneMpcShareHidesCurve
  | fullMpcCoalitionHidesCurve
  | authenticatedTransport
  | maliciousSecureArithmetic
  | endToEndPostQuantum
deriving DecidableEq, Repr

/-- Exact claim ledger for this path.  The negative entries are part of the
contract: callers must not upgrade them based on a successful happy-path run. -/
def supported : PrivacyClaim → Bool
  | .audienceReceiptOmitsOrders => true
  | .sourceOperatorHouseBlind => false
  | .oneMpcShareHidesCurve => true
  | .fullMpcCoalitionHidesCurve => false
  | .authenticatedTransport => true
  | .maliciousSecureArithmetic => false
  | .endToEndPostQuantum => false

theorem current_claim_ledger_is_exact :
    supported .audienceReceiptOmitsOrders = true ∧
    supported .sourceOperatorHouseBlind = false ∧
    supported .oneMpcShareHidesCurve = true ∧
    supported .fullMpcCoalitionHidesCurve = false ∧
    supported .authenticatedTransport = true ∧
    supported .maliciousSecureArithmetic = false ∧
    supported .endToEndPostQuantum = false := by
  decide

theorem source_opening_topology_refutes_house_blind_label :
    (view .sourceVerifier).plaintextOrders = true →
      supported .sourceOperatorHouseBlind = false := by
  intro _
  rfl

/-! ## Coalition measurements -/

structure DeploymentShape where
  bfvCustodians : Nat
  bfvOpeningThreshold : Nat
  liveMpcParties : Nat
  sourceOpeningVerifierCount : Nat
deriving DecidableEq, Repr

/-- Shape exercised by `descent_fhegg_settlement`: four DKG participants,
three live threshold openers, three PartyMPC workers, one opening-aware source
verifier. -/
def exercisedShape : DeploymentShape :=
  { bfvCustodians := 4
    bfvOpeningThreshold := 3
    liveMpcParties := 3
    sourceOpeningVerifierCount := 1 }

structure Coalition where
  includesSourceVerifier : Bool
  bfvCustodianCount : Nat
  mpcPartyCount : Nat
deriving DecidableEq, Repr

def Coalition.canReadIndividualOrders (coalition : Coalition) : Bool :=
  coalition.includesSourceVerifier

def Coalition.canOpenMaskedAggregate (coalition : Coalition) : Bool :=
  decide (exercisedShape.bfvOpeningThreshold ≤ coalition.bfvCustodianCount)

def Coalition.canReconstructAggregateCurves (coalition : Coalition) : Bool :=
  decide (exercisedShape.liveMpcParties ≤ coalition.mpcPartyCount)

def oneCustodian : Coalition := ⟨false, 1, 0⟩
def thresholdCustodians : Coalition := ⟨false, 3, 0⟩
def oneMpcParty : Coalition := ⟨false, 0, 1⟩
def allMpcParties : Coalition := ⟨false, 0, 3⟩
def sourceAlone : Coalition := ⟨true, 0, 0⟩

theorem exercised_shape_is_four_three_three_plus_source :
    exercisedShape = ⟨4, 3, 3, 1⟩ := by
  rfl

theorem exercised_shape_is_well_formed :
    0 < exercisedShape.bfvOpeningThreshold ∧
    exercisedShape.bfvOpeningThreshold ≤ exercisedShape.bfvCustodians ∧
    0 < exercisedShape.liveMpcParties ∧
    exercisedShape.sourceOpeningVerifierCount = 1 := by
  decide

theorem one_custodian_cannot_open_masked_aggregate :
    oneCustodian.canOpenMaskedAggregate = false := by
  decide

theorem threshold_custodians_open_only_the_masked_aggregate :
    thresholdCustodians.canOpenMaskedAggregate = true ∧
    thresholdCustodians.canReadIndividualOrders = false := by
  decide

theorem one_mpc_party_does_not_reconstruct_aggregate_curves :
    oneMpcParty.canReconstructAggregateCurves = false := by
  decide

theorem all_mpc_parties_can_reconstruct_aggregate_curves :
    allMpcParties.canReconstructAggregateCurves = true := by
  decide

theorem source_alone_reads_orders_without_any_threshold_or_mpc_collusion :
    sourceAlone.canReadIndividualOrders = true ∧
    sourceAlone.canOpenMaskedAggregate = false ∧
    sourceAlone.canReconstructAggregateCurves = false := by
  decide

/-! ## Connections to the actual market security models -/

open Market.MpcClearingSecurity

/-- A coalition missing one additive-share holder has a view-preserving
bijection between sharings of any two secrets. -/
theorem missing_one_mpc_party_is_perfectly_hiding
    {G : Type*} [AddCommGroup G]
    (n : Nat) (missing : Fin n) (coalition : Finset (Fin n))
    (notPresent : missing ∉ coalition) (left right : G) :
    ∃ φ : Sharing n left ≃ Sharing n right,
      ∀ (sharing : Sharing n left), ∀ party ∈ coalition,
        (φ sharing).val party = sharing.val party :=
  perfect_hiding n missing coalition notPresent left right

/-- Full MPC collusion reconstructs the additive secret, so the one-missing
party theorem has a real, proved boundary. -/
theorem full_mpc_collusion_is_not_hiding
    {G : Type*} [AddCommGroup G] {n : Nat} [NeZero n]
    {left right : G} (different : left ≠ right) :
    ¬ ∃ φ : Sharing n left → Sharing n right,
      ∀ (sharing : Sharing n left) (party : Fin n),
        (φ sharing).val party = sharing.val party :=
  full_collusion_breaks_hiding different

/-- The deterministic public computation view factors through `(p*, V*)` and
public shape; changing the private book without changing that leakage does not
change this modelled view. -/
theorem same_crossing_has_same_public_mpc_view
    (left right : MpcClearing)
    (sameBuckets : left.K = right.K)
    (sameMaskedLength : left.maskedLen = right.maskedLen)
    (same : left.leakage = right.leakage) :
    left.mpcView = right.mpcView :=
  MpcClearing.same_leakage_indistinguishable
    left right sameBuckets sameMaskedLength same

/-- The deployed smudging theorem covers the modelled book-dependent noise
channel at statistical distance at most `2^-48`.  It does not prove RLWE or a
transcript-wide hybrid. -/
theorem deployed_collective_noise_channel_bound :
    Market.DarkBazaarCollectiveOpening.CoalitionViewHides
      Bfv.Smudging.smudgeBound Bfv.Smudging.deployedCtNoise (1 / 2 ^ 48) :=
  Market.DarkBazaarCollectiveOpening.deployed_coalition_view_hides

/-- Replacing only party-local custody while keeping the public carrier fixed
does not alter the router projection.  This is structural, not cryptographic
indistinguishability of different ciphertexts. -/
theorem router_projection_omits_private_custody
    (run : Market.PartyMpcTransportBoundary.ProcessRun)
    (replacement : Market.PartyMpcTransportBoundary.PrivateCustody) :
    Market.PartyMpcTransportBoundary.release
        { run with privateCustody := replacement } =
      Market.PartyMpcTransportBoundary.release run :=
  Market.PartyMpcTransportBoundary.release_independent_of_private_custody run replacement

/-- Authentication and encryption of process transport do not establish
malicious-secure arithmetic.  The accepted dishonest execution is a theorem,
not merely a documentation warning. -/
theorem authenticated_transport_does_not_prove_honest_arithmetic :
    ∃ execution,
      Market.PartyMpcTransportBoundary.TransportAccepted execution ∧
      ¬ Market.PartyMpcTransportBoundary.ArithmeticHonest execution :=
  Market.PartyMpcTransportBoundary.transport_acceptance_does_not_imply_arithmetic_honesty

#assert_all_clean [
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.source_verifier_view_is_opening_aware,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.single_bfv_custodian_view_is_not_the_book,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.single_mpc_party_view_names_its_private_inputs,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.coordinator_and_router_do_not_receive_raw_orders,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.audience_receives_only_the_game_consequence_fields,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.current_claim_ledger_is_exact,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.source_opening_topology_refutes_house_blind_label,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.exercised_shape_is_four_three_three_plus_source,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.exercised_shape_is_well_formed,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.one_custodian_cannot_open_masked_aggregate,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.threshold_custodians_open_only_the_masked_aggregate,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.one_mpc_party_does_not_reconstruct_aggregate_curves,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.all_mpc_parties_can_reconstruct_aggregate_curves,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.source_alone_reads_orders_without_any_threshold_or_mpc_collusion,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.missing_one_mpc_party_is_perfectly_hiding,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.full_mpc_collusion_is_not_hiding,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.same_crossing_has_same_public_mpc_view,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.deployed_collective_noise_channel_bound,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.router_projection_omits_private_custody,
  Dregg2.Games.PathOfAngels.FheggPrivacyTopology.authenticated_transport_does_not_prove_honest_arithmetic]

end Dregg2.Games.PathOfAngels.FheggPrivacyTopology
