//! Dark Bazaar private-clearing apex: encrypted custody to a real game consequence.
//!
//! This integration deliberately uses one settlement authorization. Four canonical
//! side-hiding BFV rows are proved to open the same private book/root as the
//! Lean-authored HidingFRI clearing proof; a relying-party-selected native-PQ
//! quorum signs that complete claim with paired Ed25519 + ML-DSA-65 identities;
//! and the frontend-neutral fhEgg wire hands the receipt to the existing atomic
//! executor-backed Dark Bazaar settlement. The selected player buys the original
//! provenance-carrying Descent asset at the proved price in the same process-local
//! commit.
//!
//! The pre-settlement game survives a real `FileResumeStore` process boundary and
//! exposes the same binary-operation descriptor used by web/bot adapters. After
//! restart, trusted public deployment configuration reconstructs the complete
//! source-bound private verifier behind that frontend-neutral host operation and
//! accepts the composite wire. A fork of the same pre-operation durable log then
//! drives the atomic asset consequence through another instance of that exact
//! pinned registry, without retaining a witness, secret key, or decryption share.
//!
//! Honest boundary: this is centralized, operator-visible Tier 1. The live sealed
//! board now binds the exact canonical nine-slot `PrivateBookCiphertexts` later
//! consumed by the transferable Bulletproof and the packed homomorphic fold.
//! There is no second source-row encryption for quorum signatures to paper over.
//! The source verifier still sees each public one-unit game order and encryption
//! seed, so this test does not call the ingress house-blind or no-single-viewer.
//! The same exact BFV rows are homomorphically folded, masked, threshold-opened
//! only as a one-time-padded carrier, and converted locally into PartyMPC shares.
//! Authenticated party processes then reveal only `(p*, V*)`; the complete signed
//! gate/opening/output frame set must reconstruct the receipt transcript before
//! the same committee identities sign its full canonical claim. Peer transport is
//! strict native-PQ (ML-KEM-768 hybrid confidentiality and ML-DSA-65 dual
//! authentication), and neither the transport nor hosted verifier admits its
//! classical constructor. Beaver rows are globally relation-audited, signed by
//! a preprocessing authority, and bound into the transport/session domain. The
//! authority still learns and chooses every triple, and malicious private-input
//! share formation is not proved, so this is not dealer-free malicious MPC. Its
//! batch certificate is also still Ed25519-only; the native-PQ full-claim quorum
//! binds that certificate digest but does not retroactively make the dealer
//! certificate PQ. The transferable same-opening Bulletproof remains classical
//! even though its transport and quorum authority are native-PQ.

#![cfg(all(feature = "private-attested-clearing", feature = "fhegg-settlement"))]

use std::fs;
use std::path::PathBuf;
use std::thread;
use std::time::{Duration, Instant};

use dregg_circuit_prove::dark_bazaar_private::{self, PrivateBookWitness, PrivateOrder};
use dregg_sdk::{
    MlDsaKeygenCoreRealInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
    MlKemDecapsCoreInstall, MlKemEncapsCoreInstall, MlKemKeygenCoreInstall,
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core, install_verified_mlkem_decaps_core,
    install_verified_mlkem_encaps_core, install_verified_mlkem_keygen_core,
};
use dreggnet_catalog::{
    GameActionRef, GameAffordance, GameAudience, GameCommand, GameEpochLedger, GameHostIncarnation,
    GameResult, GameSessionRef, PrivateFheggGameConsequenceError, PrivateFheggGameConsequenceGate,
    PrivateFheggGameMechanic, PrivateFheggWinnerRoute, ShieldedDungeonPublicCard,
    ShieldedDungeonPublicationError, execute_bound_asserted_game_command,
    inspect_bound_game_session,
};
use dreggnet_market::fhegg_settlement::FheggSettlementError;
use dreggnet_market::fhegg_transport::{
    FHEGG_SETTLEMENT_MEDIA_TYPE, FHEGG_SETTLEMENT_OPERATION, FheggSettlementBundle,
    FheggSettlementOperation,
};
use dreggnet_market::fhegg_verifier_registry::PrivateBfvHostedVerifierConfig;
use dreggnet_market::private_attested_clearing::{
    PrivateAttestedClearingPolicy, private_order_root_commitment,
};
use dreggnet_market::private_bfv_attested_clearing::{
    PrivateBfvAttestedClearingVerifier, PrivateBfvAttestedVerifierConfigError,
    PrivateBfvQuorumSecurity,
};
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_LIST};
use dreggnet_offerings::dungeon::{DungeonOffering, PRIVATE_RAID_OPERATION};
use dreggnet_offerings::{
    Action, DreggIdentity, FileResumeStore, Offering, OfferingHost, Outcome, SessionConfig,
    SessionId, SessionResumeStore, TurnSigner,
};
use dreggnet_trade::{LegSpec, TradeWorld};
use dungeon_on_dregg::loot::{LootVault, roll_drop};
use dungeon_on_dregg::private_raid::{RaidRole, prove_private_assignment};
use dungeon_on_dregg::{KP_DESCEND, KP_PRESS_ON, KP_PRIVATE_RAID_MENDER_CHOICES, KP_TRADE_BLOWS};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, BfvPublicIdentity, ComputationIntegrityEvidence,
    ComputationIntegrityResidual, ComputationIntegrityVerifier, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest, NativePqAuthenticatedQuorumVerifier, NativePqPartyPublicKey,
};
use fhegg_fhe::boundary::{MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession};
use fhegg_fhe::mpc_party::transport::{
    CrossingCoordinatorMachine, CrossingPartyMachine, CrossingTransportRoster,
    NativePqCrossingEndpointSeal, NativePqTransportIdentity, TransportSecurityProfile,
    fresh_crossing_preprocessing_seed, is_native_post_quantum_crossing_control_frame,
    prepare_private_book_crossing_input, verify_native_post_quantum_public_crossing_transcript,
};
use fhegg_fhe::mpc_party::{
    DistributedRun, PartyMpcSession, TripleMaterial, certified_dealer_triples,
};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::private_book_bfv_zk::prove_private_book_bfv_zk;
use fhegg_fhe::private_book_relation::{
    FoldedPrivateBookCiphertext, PRIVATE_BOOK_LIVE_SLOTS, PrivateBookEncryptionOpening,
    encrypt_private_book, fold_private_book_ciphertexts,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, MIN_SMUDGE_BITS,
    ThresholdParty,
};
use fhegg_fhe::{Order, Side};
use procgen_dregg::CommittedSeed;
use rand::{
    SeedableRng,
    rngs::{OsRng, StdRng},
};
use starbridge_sealed_auction::Phase;

const MARKET_SEED: u64 = 0xD4_BA_A2_01;
const VALUE_BITS: usize = 16;
const SELLER: &str = "descent-player:alice";
const LOW_BIDDER: &str = "bazaar-bidder:bob";
const WINNER: &str = "bazaar-bidder:carol";
const SETTLEMENT_WORKER: &str = "bazaar-worker:receipt-verifier";

/// Secret-free, opt-in attribution for the full semantic apex. The ordinary
/// heavy gate stays silent and avoids clock reads; set
/// `DREGG_PRIVATE_BOOK_BFV_TIMING=1` to emit fixed phase labels and durations.
struct ApexPhaseTimings {
    started: Option<Instant>,
    current_started: Option<Instant>,
    current: &'static str,
    phases: Vec<(&'static str, Duration)>,
    emitted: bool,
}

impl ApexPhaseTimings {
    fn new(first_phase: &'static str) -> Self {
        let enabled = matches!(
            std::env::var("DREGG_PRIVATE_BOOK_BFV_TIMING").as_deref(),
            Ok("1" | "true" | "yes" | "on")
        );
        let now = enabled.then(Instant::now);
        Self {
            started: now,
            current_started: now,
            current: first_phase,
            phases: Vec::new(),
            emitted: false,
        }
    }

    fn next(&mut self, next_phase: &'static str) {
        let Some(previous) = self.current_started else {
            self.current = next_phase;
            return;
        };
        let now = Instant::now();
        self.phases
            .push((self.current, now.duration_since(previous)));
        self.current = next_phase;
        self.current_started = Some(now);
    }

    fn finish(&mut self) {
        self.emit("ok");
    }

    fn emit(&mut self, outcome: &'static str) {
        let (Some(started), Some(previous)) = (self.started, self.current_started) else {
            return;
        };
        let now = Instant::now();
        self.phases
            .push((self.current, now.duration_since(previous)));
        let phases = self
            .phases
            .iter()
            .map(|(name, duration)| format!("{name}={:.3}ms", duration.as_secs_f64() * 1e3))
            .collect::<Vec<_>>()
            .join(",");
        eprintln!(
            "private-clearing-apex-timing outcome={} total={:.3}ms phases=[{}]",
            outcome,
            now.duration_since(started).as_secs_f64() * 1e3,
            phases,
        );
        self.emitted = true;
    }
}

impl Drop for ApexPhaseTimings {
    fn drop(&mut self) {
        if !self.emitted {
            self.emit("panic-or-early-return");
        }
    }
}

/// Install the six real ML-DSA/ML-KEM cores before any identity is derived or
/// verified. This test is the shielded market apex, so a RustCrypto fallback is
/// not a semantic substitute: the test must either run with the archive-backed
/// keygen/sign/verify authority or fail before constructing the first game turn.
fn install_verified_turn_pq_runtime() {
    assert!(
        std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none(),
        "private-clearing apex must run with the unaudited-PQ escape hatch unset"
    );
    assert!(
        matches!(
            install_verified_mldsa_keygen_core_real(),
            MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
        ),
        "archive lacks dregg_mldsa_keygen_real; bootstrap/fetch a current verified-runtime seed"
    );
    assert!(
        matches!(
            install_verified_mldsa_sign_core_real(),
            MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
        ),
        "archive lacks dregg_fips204_sign_real; bootstrap/fetch a current verified-runtime seed"
    );
    assert!(
        matches!(
            install_verified_mldsa_verify_core(),
            MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
        ),
        "archive lacks dregg_fips204_verify_real; bootstrap/fetch a current verified-runtime seed"
    );
    assert!(
        matches!(
            install_verified_mlkem_keygen_core(),
            MlKemKeygenCoreInstall::Installed | MlKemKeygenCoreInstall::AlreadyInstalled
        ),
        "archive lacks the verified ML-KEM-768 keygen authority"
    );
    assert!(
        matches!(
            install_verified_mlkem_encaps_core(),
            MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled
        ),
        "archive lacks the verified ML-KEM-768 encapsulation authority"
    );
    assert!(
        matches!(
            install_verified_mlkem_decaps_core(),
            MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled
        ),
        "archive lacks the verified ML-KEM-768 decapsulation authority"
    );
}

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_owned())
}

fn inspect_raid_game(
    host: &OfferingHost,
    epochs: &GameEpochLedger,
    session: &GameSessionRef,
) -> dreggnet_catalog::GameSessionView {
    let generation = epochs
        .current_generation(session.offering(), session.session_id())
        .expect("private apex reads its independently held live generation");
    inspect_bound_game_session(
        host,
        epochs.host_incarnation(),
        generation,
        session.clone(),
        &GameAudience::Shared,
    )
    .expect("private apex inspects its bound dungeon session")
}

fn raid_game_action(
    view: &dreggnet_catalog::GameSessionView,
    choice: usize,
) -> (GameActionRef, Action) {
    view.affordances
        .iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Turn {
                reference, action, ..
            } if i64::try_from(choice).ok() == Some(action.arg) => {
                Some((reference.clone(), action.clone()))
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("private apex dungeon omitted choice {choice}"))
}

fn raid_assignment_command(
    view: &dreggnet_catalog::GameSessionView,
    payload: Vec<u8>,
) -> GameCommand {
    view.affordances
        .iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Operation { reference, .. }
                if reference.operation == PRIVATE_RAID_OPERATION =>
            {
                Some(GameCommand::Operation {
                    reference: reference.clone(),
                    payload: payload.clone(),
                })
            }
            _ => None,
        })
        .expect("private apex dungeon advertises the hiding raid operation")
}

fn collective_key(params: &BfvParams) -> (KeygenSession, Vec<ThresholdParty>, CollectivePublicKey) {
    let keygen = KeygenSession::from_seed(2, [0x21; 32]).expect("public DKG session");
    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    let mut parties = Vec::with_capacity(keygen.n_parties());
    for party in 0..keygen.n_parties() {
        let (secret_party, contribution) =
            ThresholdParty::join(&keygen, party, params).expect("party-local keygen");
        coordinator
            .accept(contribution)
            .expect("ordered public contribution");
        parties.push(secret_party);
    }
    (
        keygen,
        parties,
        coordinator.finish().expect("collective public key"),
    )
}

fn derive_packed_private_book_shares(
    nonce: [u8; 32],
    folded: &FoldedPrivateBookCiphertext,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
    threshold_parties: &[ThresholdParty],
) -> [[u64; PRIVATE_BOOK_LIVE_SLOTS]; 2] {
    let session = MaskedDecryptSession::from_public(
        nonce,
        threshold_parties.len(),
        PRIVATE_BOOK_LIVE_SLOTS,
        folded.ciphertext().clone(),
        params,
    )
    .expect("exact packed fold names the masked boundary");
    let mut coordinator = MaskedDecryptCoordinator::new(session.clone(), params.clone());
    let mut mask_parties = Vec::with_capacity(threshold_parties.len());
    for party in 0..threshold_parties.len() {
        let (state, contribution) =
            MaskedBoundaryParty::prepare(&session, party, params, public_key)
                .expect("party retains its exact-fold one-time pad");
        coordinator
            .accept(contribution)
            .expect("unique exact-session encrypted mask");
        mask_parties.push(state);
    }
    let masked = coordinator
        .finish()
        .expect("exact fold plus full encrypted-mask roster");
    let decrypt_wires = threshold_parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(masked.ciphertext(), MIN_SMUDGE_BITS)
                .expect("smudged share of the exact masked fold")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();
    let opening = masked
        .open_framed(&decrypt_wires, params)
        .expect("full threshold roster opens only the padded fold");
    let packed_shares: [[u64; PRIVATE_BOOK_LIVE_SLOTS]; 2] = mask_parties
        .iter()
        .map(|party| {
            party
                .derive_mod_t_share(&opening)
                .expect("party-local exact-fold mod-t share")
                .try_into()
                .expect("fixed nine-slot packed book")
        })
        .collect::<Vec<[u64; PRIVATE_BOOK_LIVE_SLOTS]>>()
        .try_into()
        .expect("fixed two-party crossing roster");
    packed_shares
}

fn run_authenticated_crossing(
    session: &PartyMpcSession,
    roster: &CrossingTransportRoster,
    party_identities: &[NativePqTransportIdentity; 2],
    coordinator_identity: &NativePqTransportIdentity,
    packed_shares: [[u64; PRIVATE_BOOK_LIVE_SLOTS]; 2],
    triples: Vec<TripleMaterial>,
) -> (
    DistributedRun,
    Vec<Vec<u8>>,
    Vec<NativePqCrossingEndpointSeal>,
) {
    session
        .require_certified_preprocessing()
        .expect("apex crossing refuses uncertified Beaver preprocessing");
    let mut input_rng = OsRng;
    let mut inputs = packed_shares
        .iter()
        .enumerate()
        .map(|(party, packed)| {
            prepare_private_book_crossing_input(session, party, packed, &mut input_rng)
                .expect("party-local packed crossing input")
        })
        .collect::<Vec<_>>();
    let mut triples = triples.into_iter();
    let mut parties = (0..session.n_parties())
        .map(|party| {
            CrossingPartyMachine::new_native_post_quantum_sealed(
                session.clone(),
                roster.clone(),
                party,
                party_identities[party].clone(),
                inputs.remove(0),
                triples.next().expect("one Beaver row per party"),
            )
            .expect("authenticated crossing party")
        })
        .collect::<Vec<_>>();
    let mut coordinator = CrossingCoordinatorMachine::new_native_post_quantum_sealed(
        session.clone(),
        roster.clone(),
        coordinator_identity.clone(),
    )
    .expect("reveal-only native-PQ authenticated coordinator");

    let mut public_frames = Vec::new();
    let mut party_done = vec![false; session.n_parties()];
    let mut result = None;
    // The falsifier baseline spent 1,202 seconds inside this loop because v4
    // performed 5,242 ML-DSA signs and 5,242 live verifies.  V5 retains the
    // exact 1,302-gate schedule while moving lattice authority to three
    // authenticated links and three terminal endpoint seals. Keep the same
    // ceiling: exceeding it is a regression, not grounds to relax the gate.
    let deadline = Instant::now() + Duration::from_secs(1_200);
    while result.is_none() || party_done.iter().any(|done| !done) {
        assert!(Instant::now() < deadline, "authenticated crossing stalled");
        let mut progressed = false;
        for sender in 0..parties.len() {
            loop {
                let Some(frame) = parties[sender]
                    .try_next_frame()
                    .expect("party emits authenticated frame")
                else {
                    break;
                };
                progressed = true;
                let recipient = frame.recipient();
                let bytes = frame.into_bytes();
                if recipient == roster.coordinator() {
                    if !is_native_post_quantum_crossing_control_frame(&bytes) {
                        public_frames.push(bytes.clone());
                    }
                    coordinator
                        .accept_frame(&bytes)
                        .expect("coordinator authenticates party frame");
                } else {
                    parties[recipient]
                        .accept_frame(&bytes)
                        .expect("peer authenticates encrypted ingress");
                }
            }
        }
        loop {
            let Some(frame) = coordinator
                .try_next_frame()
                .expect("coordinator emits authenticated opening")
            else {
                break;
            };
            progressed = true;
            let recipient = frame.recipient();
            let bytes = frame.into_bytes();
            if !is_native_post_quantum_crossing_control_frame(&bytes) {
                public_frames.push(bytes.clone());
            }
            parties[recipient]
                .accept_frame(&bytes)
                .expect("party authenticates coordinator opening");
        }
        for (party, machine) in parties.iter_mut().enumerate() {
            if !party_done[party]
                && machine
                    .try_result()
                    .expect("party completion report")
                    .is_some()
            {
                party_done[party] = true;
                progressed = true;
            }
        }
        if result.is_none() {
            if let Some(run) = coordinator
                .try_result()
                .expect("coordinator crossing result")
            {
                result = Some(run);
                progressed = true;
            }
        }
        if !progressed {
            thread::yield_now();
        }
    }
    let mut seals = parties
        .iter_mut()
        .map(|party| {
            party
                .try_terminal_seal()
                .expect("party terminal seal production")
                .expect("completed party seals its exact accepted and sent routes")
        })
        .collect::<Vec<_>>();
    seals.push(
        coordinator
            .try_terminal_seal()
            .expect("coordinator terminal seal production")
            .expect("completed coordinator seals its exact accepted and sent routes"),
    );
    (
        result.expect("full authenticated roster reconstructs crossing"),
        public_frames,
        seals,
    )
}

fn configured_offering(source_verifier: [u8; 32]) -> DarkBazaarOffering {
    DarkBazaarOffering::new()
        .with_fhegg_source_verifier(source_verifier)
        .expect("deployment-selected exact-opening verifier")
}

fn private_configured_offering(
    source_verifier: [u8; 32],
    config: &PrivateBfvHostedVerifierConfig,
) -> DarkBazaarOffering {
    DarkBazaarOffering::with_private_bfv_attested_registry(config.clone())
        .expect("deployment pin reconstructs the complete private verifier")
        .with_fhegg_source_verifier(source_verifier)
        .expect("deployment-selected exact-opening verifier")
}

fn open_listed(offering: &DarkBazaarOffering) -> DarkBazaarSession {
    let mut market = offering
        .open(SessionConfig::with_seed(MARKET_SEED))
        .expect("Dark Bazaar opens");
    let listed = offering.advance(
        &mut market,
        Action::new(TURN_LIST, TURN_LIST, 3, true),
        actor(SELLER),
    );
    assert!(matches!(listed, Outcome::Landed { .. }), "{listed:?}");
    market
}

fn live_orders() -> [(DreggIdentity, Order); 3] {
    [
        (
            actor(SELLER),
            Order {
                side: Side::Ask,
                limit: 3,
                qty: 1,
            },
        ),
        (
            actor(LOW_BIDDER),
            Order {
                side: Side::Bid,
                limit: 2,
                qty: 1,
            },
        ),
        (
            actor(WINNER),
            Order {
                side: Side::Bid,
                limit: 3,
                qty: 1,
            },
        ),
    ]
}

/// Build replayable operator-visible board bindings from the exact canonical
/// proof rows. No side-specific BFV ciphertext is manufactured on this path.
fn bind_live_board(
    offering: &DarkBazaarOffering,
    market: &mut DarkBazaarSession,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
    source_verifier: &SigningKey,
    asset: [u8; 32],
    private_orders: &[PrivateOrder; 3],
    private_seeds: &[[u8; 32]; 3],
    private_ciphertexts: &fhegg_fhe::private_book_relation::PrivateBookCiphertexts,
) -> (Vec<(Action, DreggIdentity)>, Vec<InputDigest>) {
    let ingress = OrderIngressSession::new(
        market
            .fhegg_order_ingress_nonce()
            .expect("listing-bound ingress nonce"),
        dark_bazaar_private::PRICE_COUNT,
        params,
        public_key,
    )
    .expect("source-row ingress");
    let orders = live_orders();
    let trader_keys = [
        SigningKey::from_bytes(&[0x41; 32]),
        SigningKey::from_bytes(&[0x42; 32]),
        SigningKey::from_bytes(&[0x43; 32]),
    ];
    let mut book = AuthenticatedOrderBook::new(
        ingress.clone(),
        trader_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .expect("authenticated trader roster");
    let mut actions = Vec::with_capacity(orders.len());

    for (trader, ((who, order), trader_key)) in orders.iter().zip(&trader_keys).enumerate() {
        let private_order = private_orders[trader];
        assert_eq!(private_order.limit as usize, order.limit);
        assert_eq!(u16::from(private_order.qty), order.qty);
        assert_eq!(
            matches!(private_order.side, dark_bazaar_private::Side::Bid),
            matches!(order.side, Side::Bid)
        );
        let submission = SignedOrderSubmission::encrypt_and_sign_private_book_row(
            &ingress,
            trader,
            0,
            private_order,
            private_seeds[trader],
            params,
            public_key,
            trader_key,
        )
        .expect("trader encrypts and signs the exact private proof row");
        assert_eq!(
            InputDigest::ciphertext(submission.ciphertext()),
            InputDigest::ciphertext(&private_ciphertexts.rows()[trader]),
            "live source ciphertext must byte-identify its proof row",
        );
        let binding = book
            .accept_private_book_opened(
                submission,
                private_order,
                private_seeds[trader],
                params,
                public_key,
            )
            .expect("operator-visible exact canonical-row reencryption check");
        let action = if matches!(order.side, Side::Ask) {
            let certificate =
                binding.certify_listing_for_market(who.0.as_bytes(), asset, source_verifier);
            DarkBazaarOffering::fhegg_listing_source_action(&certificate)
        } else {
            let certificate = binding.certify_for_market(who.0.as_bytes(), source_verifier);
            DarkBazaarOffering::fhegg_source_bound_bid_action(order.limit as i64, &certificate)
        };
        let landed = offering.advance(market, action.clone(), who.clone());
        assert!(matches!(landed, Outcome::Landed { .. }), "{landed:?}");
        actions.push((action, who.clone()));
    }

    let inputs = book
        .finish_private_book_source_inputs()
        .expect("private ingress returns bindings without legacy row retyping");
    market
        .verify_fhegg_bound_order_inputs(&inputs)
        .expect("all three source pairs are frozen into WriteOnce board seals");
    (actions, inputs)
}

fn replay_log(
    offering: &DarkBazaarOffering,
    log: &dreggnet_offerings::SessionMoveLog,
) -> DarkBazaarSession {
    let mut market = offering.open(log.cfg.clone()).expect("reopen from seed");
    for landed in &log.moves {
        let outcome = offering.advance(&mut market, landed.action.clone(), landed.actor.clone());
        assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
    }
    market
}

struct ScratchDir(PathBuf);

impl ScratchDir {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "dregg-private-clearing-apex-{}-{MARKET_SEED}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("create scratch directory");
        Self(path)
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// This is a minutes-class release-only test because it produces the fixed
/// n=4096 Bulletproof. Route the whole binary through nextest's `heavy` profile.
#[test]
fn private_bfv_receipt_survives_restart_and_authorizes_the_real_bazaar_consequence() {
    let mut timing = ApexPhaseTimings::new("verified-pq-runtime-install");
    install_verified_turn_pq_runtime();
    timing.next("fixture-world-and-collective-keygen");

    // The listed good is a genuine fair-drawn Descent note, not a market remint.
    let run_seed = CommittedSeed::from_bytes([0xD4; 32]);
    let draw = roll_drop(&run_seed, "boss:the Lantern Eater", 0);
    let mut vault = LootVault::new();
    let loot = vault.claim(SELLER, &draw).expect("fair Descent drop");
    let mut world = TradeWorld::with_assets(vault.into_assets());
    world.fund_dregg(SELLER, 0);
    world.fund_dregg(WINNER, 3);

    let source_verifier = SigningKey::from_bytes(&[0x31; 32]);
    let source_verifier_public = source_verifier.verifying_key().to_bytes();
    let committee_keys = [
        SigningKey::from_bytes(&[0x61; 32]),
        SigningKey::from_bytes(&[0x62; 32]),
    ];
    let committee_identities: [NativePqTransportIdentity; 2] = committee_keys
        .iter()
        .cloned()
        .map(NativePqTransportIdentity::generate)
        .collect::<Vec<_>>()
        .try_into()
        .expect("fixed two-party native-PQ committee");
    let committee_public_identities = committee_identities
        .iter()
        .map(NativePqTransportIdentity::public_identity)
        .collect::<Vec<_>>();
    let quorum = NativePqAuthenticatedQuorumVerifier::new(
        committee_public_identities
            .iter()
            .map(|identity| {
                NativePqPartyPublicKey::new(identity.ed25519(), identity.ml_dsa().to_vec())
            })
            .collect(),
        2,
    )
    .expect("strict native-PQ 2-of-2 computation roster");

    let params = BfvParams::fold_set();
    let (keygen, threshold_parties, public_key) = collective_key(&params);
    let bfv = BfvPublicIdentity::from_public(&params, &keygen, &public_key);
    let offering = configured_offering(source_verifier_public);
    let mut producer_market = open_listed(&offering);
    // Construct the canonical proof book before ingress. The live board will
    // sign and seal these exact first three ciphertexts; the fourth is only the
    // fixed relation's canonical zero-quantity pad.
    let private_orders = [
        PrivateOrder::ask(1, 3),
        PrivateOrder::bid(1, 2),
        PrivateOrder::bid(1, 3),
    ];
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &private_orders,
        core::array::from_fn(|lane| 17_000 + lane as u32),
    )
    .expect("fixed private book");
    let private_seed_rows = [[0x71; 32], [0x72; 32], [0x73; 32], [0x74; 32]];
    let private_opening = PrivateBookEncryptionOpening::from_seeds(private_seed_rows);
    timing.next("bfv-encrypt-four-source-rows");
    let private_ciphertexts =
        encrypt_private_book(&witness, &private_opening, &params, &public_key)
            .expect("canonical side-hiding BFV book");
    timing.next("source-ingress-and-turns");
    let live_seeds = [
        private_seed_rows[0],
        private_seed_rows[1],
        private_seed_rows[2],
    ];
    let (source_actions, live_inputs) = bind_live_board(
        &offering,
        &mut producer_market,
        &params,
        &public_key,
        &source_verifier,
        loot.asset_id.0,
        &private_orders,
        &live_seeds,
        &private_ciphertexts,
    );
    assert_eq!(producer_market.market().phase(), Some(Phase::Commit));

    timing.next("hiding-fri-prove");
    let proof_session = producer_market.private_proof_session();
    let (clearing_proof, statement) = dark_bazaar_private::prove_zk(proof_session, &witness)
        .expect("HidingFRI private clearing proof");
    assert_eq!((statement.p_star, statement.v_star), (3, 1));
    timing.next("bulletproof-same-opening-prove");
    let bfv_proof = prove_private_book_bfv_zk(
        statement,
        &witness,
        &private_ciphertexts,
        &private_opening,
        &params,
        &public_key,
    )
    .expect("transferable same-opening Bulletproof");
    timing.next("packed-fold-and-party-mpc-crossing");
    let packed_fold = fold_private_book_ciphertexts(&private_ciphertexts, &params)
        .expect("direct homomorphic fold of exact proof rows");

    // One claim covers the proved four-row/root prefix and the canonical live
    // source pairs/board suffix. Each live ciphertext digest is an exact repeat
    // of a distinct proof-row digest; the strict verifier pins that layout.
    let mut ordered_inputs = private_ciphertexts
        .rows()
        .iter()
        .map(InputDigest::ciphertext)
        .collect::<Vec<_>>();
    ordered_inputs.push(InputDigest::commitment(private_order_root_commitment(
        statement.order_root,
    )));
    ordered_inputs.extend(live_inputs.clone());
    ordered_inputs.push(InputDigest::ciphertext(packed_fold.ciphertext()));

    let claim_session_nonce = producer_market
        .fhegg_settlement_session_nonce()
        .expect("board-derived full replay nonce");
    let base_mpc_session = PartyMpcSession::new(
        claim_session_nonce,
        2,
        dark_bazaar_private::PRICE_COUNT,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(60),
    )
    .expect("canonical public clearing session");
    let packed_shares = derive_packed_private_book_shares(
        claim_session_nonce,
        &packed_fold,
        &params,
        &public_key,
        &threshold_parties,
    );
    let transport_coordinator_key = SigningKey::from_bytes(&[0x63; 32]);
    let transport_coordinator_identity =
        NativePqTransportIdentity::generate(transport_coordinator_key.clone());
    let transport_roster = CrossingTransportRoster::new_native_post_quantum_sealed_crossing(
        committee_public_identities.clone(),
        transport_coordinator_identity.public_identity(),
    )
    .expect("computation committee is the native-PQ authenticated crossing roster");
    let preprocessing_roster_digest = transport_roster.preprocessing_roster_digest();
    let packed_source_digest = InputDigest::ciphertext(packed_fold.ciphertext()).digest;
    let preprocessing_seed = fresh_crossing_preprocessing_seed(
        &base_mpc_session,
        packed_source_digest,
        &[0x83; 32],
        &mut OsRng,
    )
    .expect("source- and invocation-separated crossing preprocessing");
    let preprocessing_authority = SigningKey::from_bytes(&[0x84; 32]);
    let preprocessing_authority_identity =
        NativePqTransportIdentity::generate(preprocessing_authority.clone());
    let certified_batch = certified_dealer_triples(
        &base_mpc_session,
        preprocessing_roster_digest,
        &mut StdRng::from_seed(preprocessing_seed),
        &preprocessing_authority,
        preprocessing_authority_identity.ml_dsa_signing_key(),
    )
    .expect("preprocessing authority audits and signs every global Beaver relation");
    let (mpc_session, preprocessing_certificate, certified_triples) = certified_batch.into_parts();
    mpc_session
        .require_certified_preprocessing()
        .expect("certified batch returns a certified session domain");
    assert_eq!(
        preprocessing_certificate.authority_key(),
        preprocessing_authority.verifying_key().to_bytes()
    );
    assert_eq!(
        preprocessing_certificate.ml_dsa_authority_key(),
        preprocessing_authority_identity.public_identity().ml_dsa()
    );
    let required_preprocessing = mpc_session
        .preprocessing_binding()
        .expect("certified session exposes its exact hybrid authority and batch")
        .clone();
    let mut preprocessing_commitment =
        blake3::Hasher::new_derive_key("dreggnet-market/certified-party-mpc-preprocessing/v1");
    preprocessing_commitment.update(&mpc_session.preprocessing_binding_bytes());
    let required_tail_inputs = vec![
        InputDigest::commitment(*preprocessing_commitment.finalize().as_bytes()),
        producer_market
            .fhegg_source_input()
            .expect("live board commitment"),
    ];
    ordered_inputs.extend(required_tail_inputs.iter().copied());
    assert_eq!(
        transport_roster.security_profile(),
        TransportSecurityProfile::NativePostQuantumSealedCrossing
    );
    assert!(
        CrossingCoordinatorMachine::new(
            mpc_session.clone(),
            transport_roster.clone(),
            transport_coordinator_key.clone(),
        )
        .is_err(),
        "native-PQ transport roster must refuse the classical constructor"
    );
    let (distributed, authenticated_public_frames, endpoint_seals) = run_authenticated_crossing(
        &mpc_session,
        &transport_roster,
        &committee_identities,
        &transport_coordinator_identity,
        packed_shares,
        certified_triples,
    );
    assert_eq!(
        distributed.crossing.p_star,
        Some(statement.p_star as usize),
        "live PartyMPC price must equal the HidingFRI-proved price"
    );
    assert_eq!(
        distributed.crossing.v_star, statement.v_star as u64,
        "live PartyMPC volume must equal the HidingFRI-proved volume"
    );
    let crossing = distributed.crossing;
    let transcript = distributed.transcript;
    let expected = ExpectedClearingContext {
        session: &mpc_session,
        ordered_roster: quorum.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &ordered_inputs,
        transcript: &transcript,
        crossing: &crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical complete claim");
    let verified_crossing = verify_native_post_quantum_public_crossing_transcript(
        &mpc_session,
        &transport_roster,
        &authenticated_public_frames,
        &endpoint_seals,
        &crossing,
        &transcript,
        &receipt.claim,
    )
    .expect("complete signed transport reconstructs the exact public crossing");
    drop(authenticated_public_frames);
    drop(endpoint_seals);
    drop(transport_coordinator_identity);
    drop(transport_coordinator_key);
    drop(threshold_parties);
    timing.next("verifier-config-and-claim-assembly");
    let policy = PrivateAttestedClearingPolicy::new(VALUE_BITS as u32, bfv.clone())
        .expect("fixed private-clearing policy");

    // RED: quorum co-membership is not equality. A separately encrypted source
    // row (or one proof row reused for two actors) is refused before a verifier
    // id exists, even if every other public object is internally consistent.
    let mut detached_source = live_inputs.clone();
    detached_source[1] = InputDigest::ciphertext_bytes(b"detached-side-specific-source-row");
    assert!(matches!(
        PrivateBfvAttestedClearingVerifier::new_source_bound_native_post_quantum(
            quorum.clone(),
            policy.clone(),
            claim_session_nonce,
            statement,
            params.clone(),
            public_key.clone(),
            private_ciphertexts.clone(),
            detached_source,
            required_preprocessing.clone(),
            required_tail_inputs.clone(),
        ),
        Err(PrivateBfvAttestedVerifierConfigError::InvalidSourceInputs)
    ));
    let mut duplicated_source = live_inputs.clone();
    duplicated_source[3] = duplicated_source[1];
    assert!(matches!(
        PrivateBfvAttestedClearingVerifier::new_source_bound_native_post_quantum(
            quorum.clone(),
            policy.clone(),
            claim_session_nonce,
            statement,
            params.clone(),
            public_key.clone(),
            private_ciphertexts.clone(),
            duplicated_source,
            required_preprocessing.clone(),
            required_tail_inputs.clone(),
        ),
        Err(PrivateBfvAttestedVerifierConfigError::InvalidSourceInputs)
    ));
    let assembly_verifier =
        PrivateBfvAttestedClearingVerifier::new_source_bound_native_post_quantum(
            quorum.clone(),
            policy.clone(),
            claim_session_nonce,
            statement,
            params.clone(),
            public_key.clone(),
            private_ciphertexts.clone(),
            live_inputs.clone(),
            required_preprocessing.clone(),
            required_tail_inputs.clone(),
        )
        .expect("receipt-specific relying-party verifier");
    assert!(assembly_verifier.quorum().is_none());
    assert!(assembly_verifier.native_post_quantum_quorum().is_some());
    let mut substituted_tail = required_tail_inputs.clone();
    substituted_tail[0].digest[0] ^= 1;
    let substituted_preprocessing_verifier =
        PrivateBfvAttestedClearingVerifier::new_source_bound_native_post_quantum(
            quorum.clone(),
            policy.clone(),
            claim_session_nonce,
            statement,
            params.clone(),
            public_key.clone(),
            private_ciphertexts.clone(),
            live_inputs.clone(),
            required_preprocessing.clone(),
            substituted_tail,
        )
        .expect("well-shaped substituted preprocessing context");
    assert_ne!(
        assembly_verifier.verifier_id(),
        substituted_preprocessing_verifier.verifier_id(),
        "preprocessing tail substitution must change the hosted verifier identity"
    );
    let mut substituted_preprocessing_seed = preprocessing_seed;
    substituted_preprocessing_seed[0] ^= 1;
    let substituted_preprocessing_batch = certified_dealer_triples(
        &base_mpc_session,
        preprocessing_roster_digest,
        &mut StdRng::from_seed(substituted_preprocessing_seed),
        &preprocessing_authority,
        preprocessing_authority_identity.ml_dsa_signing_key(),
    )
    .expect("alternate valid batch for hostile verifier-pin test");
    let substituted_preprocessing = substituted_preprocessing_batch
        .session()
        .preprocessing_binding()
        .expect("alternate batch is certified")
        .clone();
    let substituted_batch_verifier =
        PrivateBfvAttestedClearingVerifier::new_source_bound_native_post_quantum(
            quorum.clone(),
            policy.clone(),
            claim_session_nonce,
            statement,
            params.clone(),
            public_key.clone(),
            private_ciphertexts.clone(),
            live_inputs.clone(),
            substituted_preprocessing,
            required_tail_inputs.clone(),
        )
        .expect("well-shaped alternate certified preprocessing batch");
    assert_ne!(
        assembly_verifier.verifier_id(),
        substituted_batch_verifier.verifier_id(),
        "an alternate valid batch must change the independently pinned verifier identity"
    );
    let hosted_config = PrivateBfvHostedVerifierConfig::new_native_post_quantum(
        assembly_verifier.verifier_id(),
        quorum.ordered_public_keys().to_vec(),
        2,
        VALUE_BITS as u32,
        bfv.clone(),
        claim_session_nonce,
        statement,
        params.clone(),
        public_key.clone(),
        private_ciphertexts.clone(),
        live_inputs.clone(),
        required_preprocessing.clone(),
        required_tail_inputs.clone(),
    );
    let signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| {
            quorum
                .sign_verified_crossing_claim(
                    &receipt.claim,
                    &expected,
                    &verified_crossing,
                    party,
                    key,
                    committee_identities[party].ml_dsa_signing_key(),
                )
                .expect("committee signs the exact complete claim")
        })
        .collect::<Vec<_>>();
    timing.next("receipt-assembly-hidingfri-and-bfv-verify");
    receipt.computation_integrity = assembly_verifier
        .assemble_native_post_quantum_evidence(
            &receipt.claim,
            &signatures,
            &clearing_proof,
            &bfv_proof,
        )
        .expect("native-PQ quorum + HidingFRI + BFV evidence compose");

    timing.next("public-wire-and-host-journal");
    let bundle = FheggSettlementBundle::new(&expected, &receipt).expect("public operation bundle");
    let wire = bundle.to_wire_bytes();
    assert_eq!(
        FheggSettlementBundle::from_wire_bytes(&wire)
            .expect("strict transport round trip")
            .to_wire_bytes(),
        wire
    );
    for secret_seed in [[0x71; 32], [0x72; 32], [0x73; 32], [0x74; 32]] {
        assert!(
            !wire
                .windows(secret_seed.len())
                .any(|window| window == secret_seed),
            "private BFV seed leaked into public restart material"
        );
    }

    // Persist the player-facing board with the real shared host before the
    // settlement worker arrives. Only landed public actions enter this log.
    let scratch = ScratchDir::new();
    let store = FileResumeStore::open(&scratch.0).expect("durable move store");
    let id = SessionId::new("private-clearing-apex");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DarkBazaarOffering::KEY,
        "The Dark Bazaar",
        private_configured_offering(source_verifier_public, &hosted_config),
    );
    host.open_session(
        DarkBazaarOffering::KEY,
        id.clone(),
        SessionConfig::with_seed(MARKET_SEED),
    )
    .expect("host opens shared table");
    assert!(matches!(
        host.advance(
            DarkBazaarOffering::KEY,
            &id,
            Action::new(TURN_LIST, TURN_LIST, 3, true),
            actor(SELLER),
        ),
        Some(Outcome::Landed { .. })
    ));
    for (action, who) in &source_actions {
        assert!(matches!(
            host.advance(DarkBazaarOffering::KEY, &id, action.clone(), who.clone(),),
            Some(Outcome::Landed { .. })
        ));
    }
    let commitment_before_restart = host
        .commitment(DarkBazaarOffering::KEY, &id)
        .expect("hosted table commitment");
    let descriptor = host
        .binary_operations(DarkBazaarOffering::KEY, &id)
        .expect("shared operation discovery")
        .into_iter()
        .find(|candidate| candidate.name == FHEGG_SETTLEMENT_OPERATION)
        .expect("web/bot-neutral fhEgg upload affordance");
    assert_eq!(descriptor.input_media_type, FHEGG_SETTLEMENT_MEDIA_TYPE);

    let wire_path = scratch.0.join("private-clearing.fhdb");
    fs::write(&wire_path, &wire).expect("persist canonical public settlement bundle");
    drop(host);
    drop(assembly_verifier);
    drop(receipt);
    drop(clearing_proof);
    drop(bfv_proof);
    drop(private_opening);
    drop(witness);
    drop(source_verifier);
    drop(committee_keys);
    drop(producer_market);

    // Fork the pre-operation durable input. One independent restarted host
    // proves the ordinary frontend-neutral operation accepts this verifier;
    // the original log remains an unconsumed relying-process input for the
    // atomic game-asset consequence below.
    let log = store
        .load(DarkBazaarOffering::KEY, &id)
        .expect("durable player move log");
    assert!(log.operations.is_empty());
    let probe_store =
        FileResumeStore::open(scratch.0.join("hosted-probe")).expect("durable probe store");
    probe_store.record_open(&log.key, &log.id, &log.cfg);
    for landed in &log.moves {
        probe_store.record_landed_attributed(
            &log.key,
            &log.id,
            &landed.action,
            &landed.actor,
            &landed.attribution,
        );
    }

    // A new shared host replays the exact executor-backed board after process
    // death, reinstalls the pinned public verifier, and applies the upload.
    let mut hosted_probe = OfferingHost::new().with_resume_store(Box::new(probe_store.clone()));
    hosted_probe.register(
        DarkBazaarOffering::KEY,
        "The Dark Bazaar",
        private_configured_offering(source_verifier_public, &hosted_config),
    );
    let resumed = hosted_probe.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "board restart failed: {resumed:?}");
    assert_eq!(
        hosted_probe
            .commitment(DarkBazaarOffering::KEY, &id)
            .expect("restarted commitment"),
        commitment_before_restart
    );
    assert!(hosted_probe.render(DarkBazaarOffering::KEY, &id).is_some());

    let public_wire = fs::read(&wire_path).expect("restart reads only public proof material");
    timing.next("hosted-operation-composite-verify");
    let hosted_receipt = hosted_probe
        .invoke_binary_operation(
            DarkBazaarOffering::KEY,
            &id,
            FHEGG_SETTLEMENT_OPERATION,
            &public_wire,
            actor(SETTLEMENT_WORKER),
        )
        .expect("pinned private verifier accepts the frontend-neutral operation");
    timing.next("restart-and-settlement-setup");
    assert_eq!(hosted_receipt.operation, FHEGG_SETTLEMENT_OPERATION);
    assert_eq!(
        hosted_receipt.public_fields,
        vec![
            ("price".to_string(), "3".to_string()),
            ("volume".to_string(), "1".to_string()),
            ("winner".to_string(), WINNER.to_string()),
        ]
    );
    assert_eq!(
        probe_store
            .load(DarkBazaarOffering::KEY, &id)
            .expect("hosted success journal")
            .operations
            .len(),
        1
    );
    assert!(
        store
            .load(DarkBazaarOffering::KEY, &id)
            .expect("unconsumed atomic branch")
            .operations
            .is_empty()
    );
    drop(hosted_probe);

    // Reconstruct the exact same public board from the original durable log and
    // reinstall the same pinned registry (no witness or key share) at the atomic
    // market + real-game-asset consequence.
    let relying_verifier = hosted_config
        .install()
        .expect("reinstall the pinned public verifier");
    let relying_offering =
        DarkBazaarOffering::with_fhegg_verifier_registry(relying_verifier.clone())
            .with_fhegg_source_verifier(source_verifier_public)
            .expect("deployment-selected exact-opening verifier");
    let mut restarted_market = replay_log(&relying_offering, &log);
    let public_bundle = FheggSettlementBundle::from_wire_bytes(&public_wire)
        .expect("shared operation bundle parses after restart");
    let public_expected = public_bundle.expected_context();
    let mut replay = InMemoryReplayGuard::default();
    let world_before = world.state_audit_digest();
    timing.next("atomic-settlement-composite-verify-and-turn");
    let authorized = relying_offering
        .settle_private_bfv_asset_atomic(
            &mut restarted_market,
            &mut world,
            loot.asset_id,
            public_bundle.receipt(),
            &public_expected,
            &relying_verifier,
            &mut replay,
        )
        .expect("private receipt atomically authorizes market clear and asset cross");
    timing.next("postconditions-and-replay-refusal");
    assert!(authorized.binding_verifies());
    assert_eq!(
        authorized.authority.verifier_id(),
        relying_verifier.verifier_id()
    );
    assert_eq!(
        authorized.authority.quorum_security(),
        PrivateBfvQuorumSecurity::NativePostQuantum
    );
    assert_ne!(authorized.authority.claim_digest(), [0; 32]);
    assert_ne!(authorized.authority.certificate_digest(), [0; 32]);
    assert_eq!(
        authorized.authority.claim_session_nonce(),
        claim_session_nonce
    );
    assert_eq!(authorized.authority.private_session(), statement.session);
    assert_eq!(authorized.authority.relation(), statement.rule);
    assert_eq!(authorized.authority.private_root(), statement.order_root);
    assert_eq!(
        authorized.authority.private_root_commitment(),
        private_order_root_commitment(statement.order_root)
    );
    assert_ne!(authorized.authority.roster_commitment(), [0; 32]);
    assert_eq!(authorized.authority.roster_len(), 2);
    assert_eq!(authorized.authority.price(), statement.p_star);
    assert_eq!(authorized.authority.volume(), statement.v_star);
    assert_ne!(authorized.authority.authority_digest(), [0; 32]);
    assert_ne!(authorized.consequence_digest, [0; 32]);
    assert_eq!(
        (
            authorized.settlement.fhegg.price,
            authorized.settlement.fhegg.volume,
        ),
        (3, 1)
    );
    assert_eq!(authorized.settlement.fhegg.winner, actor(WINNER));
    assert_ne!(
        authorized.settlement.fhegg.settlement_turn.turn_hash,
        [0; 32]
    );
    assert_eq!(authorized.settlement.world_before, world_before);
    assert_eq!(
        authorized.settlement.world_after,
        world.state_audit_digest()
    );
    assert_ne!(
        authorized.settlement.world_before,
        authorized.settlement.world_after
    );
    assert!(authorized.settlement.audit_digest_verifies());
    assert!(restarted_market.is_settled());
    assert!(restarted_market.clearing().expect("real clear").conserved());

    // The same verifier-minted private authority now drives an actual game
    // mechanic through the common, incarnation-bound game spine. A separate
    // HidingFri receipt privately selects the raid roles; its matrix stays with
    // that producer. The fhEgg adapter receives only the full public authority,
    // one public role-selected affordance, and the Bazaar winner's signed turn.
    timing.next("private-fhegg-signed-raid-consequence");
    let raid_store = FileResumeStore::open(scratch.0.join("private-fhegg-raid"))
        .expect("durable private fhEgg raid store");
    let raid_epoch_path = scratch.0.join("private-fhegg-raid-epochs");
    let raid_epochs =
        GameEpochLedger::open(&raid_epoch_path).expect("durable private fhEgg epoch custody");
    let raid_id = SessionId::new("private-fhegg-raid-mender");
    let raid_incarnation = raid_epochs.host_incarnation();
    let mut raid_host = OfferingHost::new().with_resume_store(Box::new(raid_store.clone()));
    raid_host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    raid_host
        .open_session("dungeon", raid_id.clone(), SessionConfig::with_seed(31_337))
        .expect("private fhEgg raid dungeon opens");
    let raid_generation = raid_epochs
        .bind_after_ensure("dungeon", &raid_id, true)
        .expect("fresh raid receives a durable generation");
    let raid_session = raid_epochs
        .bound_session("dungeon", &raid_id)
        .expect("epoch custody supplies the exact dungeon address");

    for choice in [KP_TRADE_BLOWS, KP_PRESS_ON, KP_DESCEND] {
        let view = inspect_raid_game(&raid_host, &raid_epochs, &raid_session);
        let (reference, action) = raid_game_action(&view, choice);
        let result = execute_bound_asserted_game_command(
            &mut raid_host,
            raid_incarnation,
            raid_generation,
            &raid_session,
            GameCommand::Turn { reference, action },
            actor("raid:pathfinder"),
        )
        .expect("ordinary route reaches the sanctum");
        assert!(matches!(result, GameResult::Landed(_)));
    }

    let raid_scores = [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]];
    let raid_assignment = prove_private_assignment(
        ((31_337u64 % 2_013_265_920) + 1) as u32,
        raid_scores,
        [[true; 4]; 4],
    )
    .expect("independent private raid role assignment proves");
    let mender_seat = raid_assignment
        .statement()
        .roles
        .iter()
        .position(|role| *role == RaidRole::Mender as u8)
        .expect("private role proof publishes one exact Mender");
    let mender_choice = KP_PRIVATE_RAID_MENDER_CHOICES[mender_seat];
    let view = inspect_raid_game(&raid_host, &raid_epochs, &raid_session);
    let raid_operation = raid_assignment_command(
        &view,
        raid_assignment
            .to_postcard()
            .expect("public hiding-proof carrier"),
    );
    let proof_applied = execute_bound_asserted_game_command(
        &mut raid_host,
        raid_incarnation,
        raid_generation,
        &raid_session,
        raid_operation,
        actor("raid:proof-uploader"),
    )
    .expect("common spine carries the independently verified assignment");
    assert!(matches!(proof_applied, GameResult::Landed(_)));

    let winner_signer = TurnSigner::from_seed([0x82; 32]);
    let winner_route = PrivateFheggWinnerRoute::new(actor(WINNER), winner_signer.pubkey_hex())
        .expect("deployment pins Bazaar winner to the game signing key");
    let view = inspect_raid_game(&raid_host, &raid_epochs, &raid_session);
    let (mender_reference, mender_action) = raid_game_action(&view, mender_choice);
    let mut game_gate = PrivateFheggGameConsequenceGate::new(
        &authorized,
        loot.asset_id.0,
        winner_route.clone(),
        PrivateFheggGameMechanic::DungeonRaidMender,
        &raid_epochs,
        mender_reference.clone(),
        mender_action.clone(),
    )
    .expect("full strict private authority targets the proof-assigned Mender");

    // Signer substitution is rejected before dispatch, so it neither changes
    // HP nor consumes the private authorization.
    let thief = TurnSigner::from_seed([0x83; 32]);
    let stolen = game_gate
        .execute_signed(
            &mut raid_host,
            thief.sign("dungeon", &raid_id, 0, mender_action.clone()),
        )
        .expect_err("a different game key cannot spend the Bazaar winner route");
    assert_eq!(stolen, PrivateFheggGameConsequenceError::WrongGameSigner);
    assert!(!game_gate.is_consumed());
    assert!(format!("{:?}", raid_host.render("dungeon", &raid_id).unwrap().0).contains("HP 30"));

    // The live epoch comes from independent durable custody. Rewrapping the
    // same action under a replacement-host identity cannot instantiate the gate.
    let wrong_incarnation = GameHostIncarnation::new([0x84; 32]).unwrap();
    let wrong_session = GameSessionRef::bound(
        "dungeon",
        raid_id.clone(),
        wrong_incarnation,
        raid_generation,
    )
    .unwrap();
    let wrong_reference = GameActionRef::new(
        wrong_session,
        &mender_action,
        mender_reference.expected_pre_head.clone(),
    );
    let wrong_epoch = PrivateFheggGameConsequenceGate::new(
        &authorized,
        loot.asset_id.0,
        winner_route.clone(),
        PrivateFheggGameMechanic::DungeonRaidMender,
        &raid_epochs,
        wrong_reference,
        mender_action.clone(),
    )
    .expect_err("cross-incarnation route substitution is refused");
    assert_eq!(
        wrong_epoch,
        PrivateFheggGameConsequenceError::AuthorityEpochMismatch
    );

    let (game_consequence, public_game_receipt) = game_gate
        .execute_signed_public(
            &mut raid_host,
            winner_signer.sign("dungeon", &raid_id, 0, mender_action.clone()),
        )
        .expect("the exact Bazaar winner spends the proof-assigned Mender once and publishes it");
    assert!(game_consequence.binding_verifies());
    public_game_receipt
        .validate()
        .expect("the viewer-blind game publication is self-authenticating");
    assert_eq!(game_consequence.market_winner, actor(WINNER));
    assert_eq!(game_consequence.market_asset_id, loot.asset_id.0);
    assert_eq!(
        game_consequence.private_root,
        authorized.authority.private_root()
    );
    assert_eq!(game_consequence.target_session, raid_session);
    assert_eq!(
        game_consequence.action_preimage_id,
        mender_reference.routing_preimage_id()
    );
    assert!(raid_host.verify("dungeon", &raid_id).unwrap().verified);
    assert!(format!("{:?}", raid_host.render("dungeon", &raid_id).unwrap().0).contains("HP 50"));

    // This is the object Discord, Telegram, web, and the cross-game activity
    // rail may share. It binds the one-shot FHTRI004/Bazaar authorization to
    // both the common-spine router receipt and the concrete executor receipt,
    // but its type has no winner, key, private root, certificate, asset, raw
    // session, action, payload, or state-head slot.
    let public_raid_card = ShieldedDungeonPublicCard::from_exact_receipts(
        &authorized,
        &game_consequence,
        &public_game_receipt,
    )
    .expect("the public card joins the exact private authority to its real Dungeon turn");
    assert_eq!(
        public_raid_card.authorization_id,
        game_consequence.authorization_id
    );
    assert_eq!(
        public_raid_card.consequence_id,
        game_consequence.consequence_digest
    );
    assert_eq!(
        public_raid_card.router_receipt_id,
        game_consequence.game_receipt_id
    );
    assert_eq!(
        public_raid_card.executor_receipt_id,
        game_consequence.inner_game_receipt_id
    );
    assert_eq!(
        public_raid_card.publication_id,
        public_game_receipt.publication_id
    );
    assert!(!public_raid_card.ended);
    public_raid_card
        .validate()
        .expect("the shipped public card is self-authenticating after transport");

    let public_render = public_raid_card
        .render_shared()
        .expect("the exact card is safe to render on a shared surface");
    assert!(public_render.starts_with("Dungeon · shielded consequence landed"));
    assert!(public_render.contains("router receipt "));
    assert!(public_render.contains("executor receipt "));
    assert!(!public_render.contains(WINNER));
    assert!(!public_render.contains(&raid_id.0));
    assert!(!public_render.contains(&game_consequence.game_signer_pubkey_hex));
    assert!(!public_render.contains("Mender"));

    let mut forged_stored_card = public_raid_card.clone();
    forged_stored_card.executor_receipt_id[0] ^= 1;
    assert_eq!(
        forged_stored_card
            .render_shared()
            .expect_err("a substituted stored public card cannot reach a shared surface"),
        ShieldedDungeonPublicationError::InvalidCardBinding
    );

    let mut forged_public_game_receipt = public_game_receipt.clone();
    forged_public_game_receipt.session_route_id[0] ^= 1;
    assert_eq!(
        ShieldedDungeonPublicCard::from_exact_receipts(
            &authorized,
            &game_consequence,
            &forged_public_game_receipt,
        )
        .expect_err("a substituted public route cannot be rendered"),
        ShieldedDungeonPublicationError::InvalidPublicationBinding
    );

    let game_replay_error = game_gate
        .execute_signed(
            &mut raid_host,
            winner_signer.sign("dungeon", &raid_id, 1, mender_action.clone()),
        )
        .expect_err("the exact private authorization is consumed before a second dispatch");
    assert_eq!(
        game_replay_error,
        PrivateFheggGameConsequenceError::AlreadyConsumed
    );

    // The public consequence itself is hostile-substitution detecting, and a
    // restarted gate can restore the exact authorization id before inspecting
    // or dispatching any stale command.
    let mut forged_game_consequence = game_consequence.clone();
    forged_game_consequence.private_root[0] ^= 1;
    assert!(!forged_game_consequence.binding_verifies());
    let mut restored_gate = PrivateFheggGameConsequenceGate::new(
        &authorized,
        loot.asset_id.0,
        winner_route,
        PrivateFheggGameMechanic::DungeonRaidMender,
        &raid_epochs,
        mender_reference,
        mender_action.clone(),
    )
    .expect("restart reconstructs the public-only consequence policy");
    restored_gate
        .restore_consumed(game_consequence.authorization_id)
        .expect("durable sidecar restores only the exact authorization id");
    assert_eq!(
        restored_gate
            .execute_signed(
                &mut raid_host,
                winner_signer.sign("dungeon", &raid_id, 1, mender_action),
            )
            .expect_err("restored authorization cannot dispatch"),
        PrivateFheggGameConsequenceError::AlreadyConsumed
    );

    let raid_log = raid_store
        .load("dungeon", &raid_id)
        .expect("game timeline is durably journaled");
    assert_eq!(raid_log.moves.len(), 4);
    assert_eq!(raid_log.operations.len(), 1);
    drop(raid_host);
    let mut restarted_raid = OfferingHost::new().with_resume_store(Box::new(raid_store.clone()));
    restarted_raid.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = restarted_raid.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(
        resumed[0].1.is_ok(),
        "private raid restart failed: {resumed:?}"
    );
    let restarted_epochs =
        GameEpochLedger::open(&raid_epoch_path).expect("epoch custody survives restart");
    assert_eq!(restarted_epochs.host_incarnation(), raid_incarnation);
    assert_eq!(
        restarted_epochs
            .bind_after_ensure("dungeon", &raid_id, false)
            .expect("resumed game retains its active generation"),
        raid_generation
    );
    assert_eq!(
        restarted_epochs
            .bound_session("dungeon", &raid_id)
            .expect("restarted epoch resolves the same address"),
        raid_session
    );
    assert!(restarted_raid.verify("dungeon", &raid_id).unwrap().verified);
    assert!(
        format!(
            "{:?}",
            restarted_raid.render("dungeon", &raid_id).unwrap().0
        )
        .contains("HP 50")
    );

    // The proof-selected game outcome has an owned-world consequence in that
    // same commit: the exact Descent note and winning payment crossed sealed escrow.
    let crossed = authorized.settlement.asset;
    assert_eq!(crossed.asset, loot.asset_id);
    assert_eq!(crossed.winner, actor(WINNER));
    assert_eq!(crossed.price, 3);
    assert_eq!(crossed.settlement.a_gave, LegSpec::Asset(loot.asset_id));
    assert_eq!(crossed.settlement.b_gave, LegSpec::Dregg(3));
    assert!(crossed.provenance.verified);
    assert_eq!(world.current_holder_label(loot.asset_id), Some(WINNER));
    assert_eq!(world.lineage_len(loot.asset_id), 3);
    assert_eq!(world.dregg_balance(WINNER), 0);
    assert_eq!(world.dregg_balance(SELLER), 3);

    // The same public artifact cannot authorize a second deterministic board in
    // the restarted relying process; verification reaches the restored gate and
    // burns no executor state on refusal.
    let mut replay_market = replay_log(&relying_offering, &log);
    let receipts_before = replay_market.market().receipts_len();
    let replay_error = FheggSettlementOperation::from_wire_bytes(&public_wire)
        .expect("same canonical operation")
        .execute(
            &relying_offering,
            &mut replay_market,
            &relying_verifier,
            &mut replay,
        )
        .expect_err("claim replay stays refused after one settlement");
    assert!(matches!(
        replay_error,
        FheggSettlementError::Attestation(AttestationError::ReplayDetected)
    ));
    assert_eq!(replay_market.market().receipts_len(), receipts_before);
    assert_eq!(replay_market.market().phase(), Some(Phase::Commit));
    assert!(!replay_market.is_settled());
    timing.finish();
}
