//! No-assembled-secret, one-bit Dark AMM acceptance composition.
//!
//! The acceptance path in this file is deliberately stronger than a scalar
//! differential oracle:
//!
//! 1. three opaque [`ThresholdParty`] values form a collective BFV public key;
//! 2. those same party-held shares run multiparty relinearization-key generation;
//! 3. encrypted reserves and encrypted `dx`/`dy` produce an encrypted invariant;
//! 4. parties encrypt one-time pads, threshold-decrypt only the padded invariant,
//!    and locally derive mod-`t` shares;
//! 5. those shares enter the peer-distributed equality circuit against public `k`;
//! 6. only one equality bit is quorum-attested and may authorize commit.
//!
//! This test imports neither `SecretKey` nor `threshold::combine`.  In
//! particular, it never reconstructs the raw invariant/product on either the
//! accepting or refusing path.  `MaskedOpening` is the public one-time-padded
//! value, not the invariant; only its mask-owning party can derive its local
//! MPC share.
//!
//! Honest boundary: keygen/relin/decrypt are n-of-n; mask and equality routing
//! are in-memory and semi-honest; Beaver triples use the shape-only trusted
//! preprocessing helper; Ed25519 quorum evidence authenticates roster agreement
//! on the bit, not malicious correctness of ciphertext/share formation.
//! Replay refusal is round-tripped through the canonical snapshot carrier;
//! rollback protection for that snapshot remains a host-storage obligation.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhe::bfv::{BfvParametersBuilder, Encoding, Plaintext, RelinearizationKey};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
    InMemoryReplayGuard, SnapshotReplayGuard,
};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::BoundedCiphertext;
use fhegg_fhe::boundary::{
    EncryptedMaskContribution, MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession,
    MaskedOpening,
};
use fhegg_fhe::dark_amm::{DarkAmmError, DarkPool, DarkPoolPublicHostMaterial, PrivateAppliedSwap};
use fhegg_fhe::dark_amm_attested::{
    commit_attested_private_decision, AttestedPrivateCommitError, AttestedPrivateDecisionPolicy,
    DarkAmmCommitPreflightError,
};
use fhegg_fhe::decision_attestation::{
    AttestedDecisionReceipt, DecisionAttestationError, ExpectedDecisionContext,
};
use fhegg_fhe::mpc_party::{
    local_channels, run_party_equality, trusted_dealer_triples, DistributedDecisionRun,
    PartyChannels, PartyEqualityInput, PartyMpcSession, TripleMaterial,
};
use fhegg_fhe::threshold::relin::{generate_relinearization_key, RelinKeySession};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    MIN_SMUDGE_BITS,
};
use rand::rngs::StdRng;
use rand::SeedableRng;
use sha2::{Digest, Sha256};

const N: usize = 3;
const VALUE_BITS: usize = 19;

struct CollectiveFixture {
    params: BfvParams,
    collective: CollectivePublicKey,
    parties: Vec<ThresholdParty>,
    relin: RelinearizationKey,
}

impl CollectiveFixture {
    fn new(entropy: u8) -> Self {
        let params = BfvParams::fold_set();
        let keygen = KeygenSession::from_seed(N, [entropy; 32]).expect("keygen session");
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        let mut parties = Vec::with_capacity(N);
        for party_index in 0..N {
            let (party, contribution) =
                ThresholdParty::join(&keygen, party_index, &params).expect("party keygen");
            coordinator
                .accept(contribution)
                .expect("public key contribution");
            parties.push(party);
        }
        let collective = coordinator.finish().expect("collective public key");
        let relin_session = RelinKeySession::from_public_entropy(
            &keygen,
            &collective,
            [entropy ^ 0xa5; 32],
            Duration::from_secs(30),
        )
        .expect("relin session");
        let relin = generate_relinearization_key(&relin_session, &params, &collective, &parties)
            .expect("party-owned multiparty relin key");
        Self {
            params,
            collective,
            parties,
            relin,
        }
    }

    fn pool(&self) -> DarkPool {
        let mut rng = rand_09::rng();
        let mut pool = DarkPool::init(
            self.params.arc(),
            &self.collective.pk,
            &self.relin,
            100,
            900,
            400,
            1_000,
            &mut rng,
        )
        .expect("collective-key Dark AMM pool");
        pool.strip_lp_view();
        pool
    }

    fn encrypted_amount(&self, value: u64) -> BoundedCiphertext {
        self.encrypted_amount_with_bound(value, value)
    }

    fn encrypted_amount_with_bound(&self, value: u64, public_bound: u64) -> BoundedCiphertext {
        let plaintext = Plaintext::try_encode(&[value], Encoding::simd(), self.params.arc())
            .expect("amount encoding");
        let ciphertext = self
            .collective
            .pk
            .try_encrypt(&plaintext, &mut rand_09::rng())
            .expect("collective amount encryption");
        BoundedCiphertext::new(ciphertext, public_bound)
    }
}

struct EqualityCommand {
    opening: MaskedOpening,
    session: PartyMpcSession,
    public_target_share: u64,
    triples: TripleMaterial,
    channels: PartyChannels,
    rng_seed: u64,
}

/// Compose party-owned masking, n-of-n smudged threshold opening of the padded
/// ciphertext, and direct-peer equality.  The coordinator receives public mask
/// ciphertexts, framed decrypt shares over the *masked* target, Beaver openings,
/// and the final bit. It has no endpoint for an invariant residue.
fn masked_invariant_decision(
    fixture: &CollectiveFixture,
    candidate: &PrivateAppliedSwap,
    public_k: u64,
    rng_seed: u64,
) -> (PartyMpcSession, DistributedDecisionRun) {
    let nonce = candidate.decision_session_nonce();
    let target = LeanCiphertext::from_fhe_bytes(
        &candidate.invariant.ct.to_bytes(),
        fixture.params.moduli(),
        fixture.params.degree(),
        candidate.invariant.plain_bound,
    )
    .expect("strict invariant ciphertext boundary");
    let mask_session = MaskedDecryptSession::from_public(nonce, N, 1, target, &fixture.params)
        .expect("candidate-bound masked-decrypt session");

    thread::scope(|scope| {
        let (mask_tx, mask_rx) = mpsc::channel::<EncryptedMaskContribution>();
        let (decrypt_tx, decrypt_rx) = mpsc::channel::<(usize, Vec<u8>)>();
        let mut decrypt_commands = Vec::with_capacity(N);
        let mut equality_commands = Vec::with_capacity(N);
        let mut workers = Vec::with_capacity(N);

        for threshold_party in &fixture.parties {
            let party_index = threshold_party.party();
            let (decrypt_command_tx, decrypt_command_rx) = mpsc::channel::<LeanCiphertext>();
            let (equality_command_tx, equality_command_rx) = mpsc::channel::<EqualityCommand>();
            decrypt_commands.push(decrypt_command_tx);
            equality_commands.push(equality_command_tx);
            let mask_tx = mask_tx.clone();
            let decrypt_tx = decrypt_tx.clone();
            let mask_session = &mask_session;
            let params = &fixture.params;
            let collective = &fixture.collective;
            workers.push(scope.spawn(move || {
                let (mask_state, contribution) =
                    MaskedBoundaryParty::prepare(mask_session, party_index, params, collective)
                        .expect("party retains its one-time pad");
                mask_tx
                    .send(contribution)
                    .expect("public encrypted-mask contribution");

                let masked_ciphertext = decrypt_command_rx
                    .recv()
                    .expect("masked ciphertext command");
                let decrypt_share = threshold_party
                    .partial_decrypt(&masked_ciphertext, MIN_SMUDGE_BITS)
                    .expect("smudged share over only the masked invariant");
                decrypt_tx
                    .send((party_index, decrypt_share.to_wire_bytes()))
                    .expect("public framed decrypt share");

                let command = equality_command_rx.recv().expect("equality command");
                let left_share = mask_state
                    .derive_mod_t_share(&command.opening)
                    .expect("party locally removes only its own pad")[0];
                let mut party_rng = StdRng::seed_from_u64(command.rng_seed ^ party_index as u64);
                let input = PartyEqualityInput::new(
                    &command.session,
                    party_index,
                    left_share,
                    command.public_target_share,
                    &mut party_rng,
                )
                .expect("party-owned equality ingress");
                run_party_equality(input, command.triples, command.channels)
                    .expect("party equality circuit");
            }));
        }
        drop(mask_tx);
        drop(decrypt_tx);

        let mut contributions = (0..N)
            .map(|_| mask_rx.recv().expect("mask contribution"))
            .collect::<Vec<_>>();
        contributions.sort_by_key(EncryptedMaskContribution::party);
        let mut mask_coordinator =
            MaskedDecryptCoordinator::new(mask_session.clone(), fixture.params.clone());
        for contribution in contributions {
            mask_coordinator
                .accept(contribution)
                .expect("exact unique mask contribution");
        }
        let masked = mask_coordinator
            .finish()
            .expect("target plus full encrypted mask quorum");
        for command in &decrypt_commands {
            command
                .send(masked.ciphertext().clone())
                .expect("masked threshold target");
        }
        let mut decrypt_shares = (0..N)
            .map(|_| decrypt_rx.recv().expect("masked decrypt share"))
            .collect::<Vec<_>>();
        decrypt_shares.sort_by_key(|(party, _)| *party);
        let framed = decrypt_shares
            .into_iter()
            .map(|(_, share)| share)
            .collect::<Vec<_>>();

        // This opens only invariant + Σ pads.  No caller in this test invokes
        // `values()` or reconstructs the invariant from it.
        let opening = masked
            .open_framed(&framed, &fixture.params)
            .expect("full quorum opens only the one-time-padded value");

        let equality_session = PartyMpcSession::equality(
            nonce,
            N,
            VALUE_BITS,
            fixture.params.plaintext_modulus(),
            Duration::from_secs(5),
        )
        .expect("candidate-bound equality session");
        let mut triple_rng = StdRng::seed_from_u64(rng_seed ^ 0x7472_6970_6c65);
        let triples = trusted_dealer_triples(&equality_session, &mut triple_rng)
            .expect("public-shape Beaver preprocessing");
        let (coordinator, endpoints) = local_channels(&equality_session);
        for (party, ((command, triples), channels)) in equality_commands
            .into_iter()
            .zip(triples)
            .zip(endpoints)
            .enumerate()
        {
            command
                .send(EqualityCommand {
                    opening: opening.clone(),
                    session: equality_session.clone(),
                    public_target_share: if party == 0 { public_k } else { 0 },
                    triples,
                    channels,
                    rng_seed: rng_seed ^ 0x6571_7561_6c,
                })
                .expect("party equality command");
        }
        let decision = coordinator
            .coordinate_equality(&equality_session)
            .expect("full party equality quorum");
        for worker in workers {
            worker.join().expect("custodian worker exits");
        }
        (equality_session, decision)
    })
}

fn decision_quorum() -> (Vec<SigningKey>, AuthenticatedQuorumVerifier) {
    let keys = vec![
        SigningKey::from_bytes(&[31; 32]),
        SigningKey::from_bytes(&[32; 32]),
        SigningKey::from_bytes(&[33; 32]),
    ];
    let verifier = AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("configured 2-of-3 decision roster");
    (keys, verifier)
}

fn attested_receipt(
    session: &PartyMpcSession,
    decision: &DistributedDecisionRun,
    keys: &[SigningKey],
    verifier: &AuthenticatedQuorumVerifier,
) -> AttestedDecisionReceipt {
    let context = ExpectedDecisionContext {
        session,
        roster_digest: verifier.roster_digest(),
        transcript: &decision.transcript,
        equal: decision.is_equal(),
    };
    let draft = AttestedDecisionReceipt::issue(
        &context,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical decision claim");
    let signatures = [0usize, 2]
        .into_iter()
        .map(|party| {
            verifier
                .sign_claim(&draft.claim_digest(), party, &keys[party])
                .expect("configured custodian signature")
        })
        .collect::<Vec<_>>();
    let evidence = verifier
        .assemble_evidence(&draft.claim_digest(), &signatures)
        .expect("2-of-3 evidence");
    let receipt = AttestedDecisionReceipt::issue(&context, evidence).expect("attested decision");
    AttestedDecisionReceipt::from_wire_bytes(
        &receipt.to_wire_bytes().expect("strict decision wire"),
    )
    .expect("strict decision wire roundtrip")
}

fn refresh_public_host_checksum(wire: &mut Vec<u8>) {
    const DOMAIN: &[u8] = b"fhegg/dark-amm/public-host-material/v2";
    wire.truncate(wire.len() - 32);
    let mut hash = Sha256::new();
    hash.update(DOMAIN);
    hash.update((wire.len() as u64).to_le_bytes());
    hash.update(&*wire);
    wire.extend_from_slice(&hash.finalize());
}

#[test]
fn no_assembled_secret_dark_amm_commits_only_after_attested_masked_equality_bit() {
    let fixture = CollectiveFixture::new(0x61);
    let mut pool = fixture.pool();
    let dx = fixture.encrypted_amount(50);
    let dy = fixture.encrypted_amount(300);
    let candidate = pool
        .try_private_swap_proposed(&dx, &dy)
        .expect("encrypted exact quote");
    let before_x = pool.reserve_cts().ct_x.ct.to_bytes();
    let before_y = pool.reserve_cts().ct_y.ct.to_bytes();

    let (session, decision) = masked_invariant_decision(&fixture, &candidate, pool.k, 0x6100_0001);
    assert!(decision.is_equal(), "only the equality bit is revealed");
    assert!(decision.transcript.is_reveal_only(&session));
    assert_eq!(pool.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_eq!(pool.reserve_cts().ct_y.ct.to_bytes(), before_y);

    let (keys, verifier) = decision_quorum();
    let receipt = attested_receipt(&session, &decision, &keys, &verifier);
    let context = ExpectedDecisionContext {
        session: &session,
        roster_digest: verifier.roster_digest(),
        transcript: &decision.transcript,
        equal: true,
    };
    let replay_context = candidate.decision_session_nonce();
    let mut replay = SnapshotReplayGuard::new(replay_context);
    receipt
        .verify_full(&context, &verifier, &mut replay)
        .expect("fresh 2-of-3 attested bit");
    let replay_wire = replay.to_wire_bytes();
    let mut restored_replay = SnapshotReplayGuard::from_wire_bytes(replay_context, &replay_wire)
        .expect("restart restores canonical replay state");
    assert_eq!(
        receipt.verify_full(&context, &verifier, &mut restored_replay),
        Err(DecisionAttestationError::ReplayDetected)
    );
    assert_eq!(
        receipt.claim.session_nonce,
        candidate.decision_session_nonce()
    );
    assert!(receipt.claim.equal);

    pool.commit_private_decision(candidate, decision)
        .expect("receipt-gated one-bit decision commits");
    assert_ne!(pool.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_ne!(pool.reserve_cts().ct_y.ct.to_bytes(), before_y);
}

#[test]
fn false_bit_and_cross_candidate_decision_hold_ciphertext_state_without_residue() {
    let fixture = CollectiveFixture::new(0x62);

    let mut bad_pool = fixture.pool();
    let bad_dx = fixture.encrypted_amount(50);
    let bad_dy = fixture.encrypted_amount(301);
    let bad_candidate = bad_pool
        .try_private_swap_proposed(&bad_dx, &bad_dy)
        .expect("well-shaped but off-invariant encrypted quote");
    let before_x = bad_pool.reserve_cts().ct_x.ct.to_bytes();
    let before_y = bad_pool.reserve_cts().ct_y.ct.to_bytes();
    let (bad_session, refused) =
        masked_invariant_decision(&fixture, &bad_candidate, bad_pool.k, 0x6200_0001);
    assert!(!refused.is_equal());
    assert!(refused.transcript.is_reveal_only(&bad_session));
    let error = bad_pool
        .commit_private_decision(bad_candidate, refused)
        .expect_err("false bit cannot mutate the pool");
    assert!(matches!(error, DarkAmmError::InvariantDecisionRefused));
    assert_eq!(
        error.to_string(),
        "private invariant decision refused; swap held"
    );
    assert_eq!(bad_pool.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_eq!(bad_pool.reserve_cts().ct_y.ct.to_bytes(), before_y);

    // A fully valid bit/receipt for candidate A cannot authorize candidate B.
    // Both candidates are encrypted and even identical plaintext transitions
    // receive distinct ciphertext-bound nonces.
    let pool_a = fixture.pool();
    let dx_a = fixture.encrypted_amount(50);
    let dy_a = fixture.encrypted_amount(300);
    let candidate_a = pool_a
        .try_private_swap_proposed(&dx_a, &dy_a)
        .expect("candidate A");
    let mut pool_b = fixture.pool();
    let dx_b = fixture.encrypted_amount(50);
    let dy_b = fixture.encrypted_amount(300);
    let candidate_b = pool_b
        .try_private_swap_proposed(&dx_b, &dy_b)
        .expect("candidate B");
    assert_ne!(
        candidate_a.decision_session_nonce(),
        candidate_b.decision_session_nonce()
    );
    let (session_a, decision_a) =
        masked_invariant_decision(&fixture, &candidate_a, pool_a.k, 0x6200_0002);
    assert!(decision_a.is_equal());
    let (keys, verifier) = decision_quorum();
    let receipt_a = attested_receipt(&session_a, &decision_a, &keys, &verifier);
    let context_a = ExpectedDecisionContext {
        session: &session_a,
        roster_digest: verifier.roster_digest(),
        transcript: &decision_a.transcript,
        equal: true,
    };
    receipt_a
        .verify_full(&context_a, &verifier, &mut InMemoryReplayGuard::default())
        .expect("candidate A receipt is fully valid in its own context");
    let wrong_session = PartyMpcSession::equality(
        candidate_b.decision_session_nonce(),
        N,
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("candidate B equality context");
    let wrong_context = ExpectedDecisionContext {
        session: &wrong_session,
        roster_digest: verifier.roster_digest(),
        transcript: &decision_a.transcript,
        equal: true,
    };
    assert_eq!(
        receipt_a.verify_binding(&wrong_context),
        Err(DecisionAttestationError::BindingMismatch)
    );
    let before_b_x = pool_b.reserve_cts().ct_x.ct.to_bytes();
    let before_b_y = pool_b.reserve_cts().ct_y.ct.to_bytes();
    assert!(matches!(
        pool_b.commit_private_decision(candidate_b, decision_a),
        Err(DarkAmmError::InvariantDecisionContextMismatch)
    ));
    assert_eq!(pool_b.reserve_cts().ct_x.ct.to_bytes(), before_b_x);
    assert_eq!(pool_b.reserve_cts().ct_y.ct.to_bytes(), before_b_y);
}

#[test]
fn public_only_host_material_is_strict_and_rejects_adversarial_dimensions() {
    let fixture = CollectiveFixture::new(0x63);
    let pool = fixture.pool();
    let material = pool.public_host_material().expect("public-only snapshot");
    let wire = material.to_wire_bytes();
    let decoded = DarkPoolPublicHostMaterial::from_wire_bytes(&wire, fixture.params.arc())
        .expect("strict public-only roundtrip");
    assert_eq!(decoded, material);
    assert_eq!(decoded.k(), 90_000);
    assert_eq!(decoded.cap_x(), 400);
    assert_eq!(decoded.cap_y(), 1_000);
    assert_ne!(decoded.material_digest(), [0; 32]);

    for end in [0usize, 1, 7, 8, 31, wire.len() - 33, wire.len() - 1] {
        assert!(
            DarkPoolPublicHostMaterial::from_wire_bytes(&wire[..end], fixture.params.arc())
                .is_err(),
            "truncation at {end} must fail"
        );
    }
    let mut trailing = wire.clone();
    trailing.push(0);
    assert!(DarkPoolPublicHostMaterial::from_wire_bytes(&trailing, fixture.params.arc()).is_err());
    let mut corrupt = wire.clone();
    corrupt[40] ^= 1;
    assert!(DarkPoolPublicHostMaterial::from_wire_bytes(&corrupt, fixture.params.arc()).is_err());

    // Recompute the public checksum after each semantic substitution: this
    // demonstrates validation beyond accidental-corruption detection.
    let mut wrong_magic = wire.clone();
    wrong_magic[0] ^= 1;
    refresh_public_host_checksum(&mut wrong_magic);
    assert!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&wrong_magic, fixture.params.arc()).is_err()
    );

    let mut retired_v1 = wire.clone();
    retired_v1[..8].copy_from_slice(b"FHDAP001");
    refresh_public_host_checksum(&mut retired_v1);
    assert!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&retired_v1, fixture.params.arc()).is_err(),
        "the incomplete v1 parameter identity must fail closed"
    );

    let mut wrong_t = wire.clone();
    wrong_t[24..32].copy_from_slice(&(fixture.params.plaintext_modulus() + 1).to_le_bytes());
    refresh_public_host_checksum(&mut wrong_t);
    assert!(matches!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&wrong_t, fixture.params.arc()),
        Err(DarkAmmError::PublicHostParameterMismatch)
    ));

    // Error variance is part of fhe.rs's parameter identity even though it
    // does not alter degree, ciphertext moduli, or plaintext modulus. A host
    // must not silently restart the carrier under a different encryption/noise
    // policy.
    let different_variance = BfvParametersBuilder::new()
        .set_degree(fixture.params.degree())
        .set_plaintext_modulus(fixture.params.plaintext_modulus())
        .set_moduli(fixture.params.moduli())
        .set_variance(1)
        .build_arc()
        .expect("same arithmetic parameters with different error variance");
    assert_eq!(different_variance.degree(), fixture.params.degree());
    assert_eq!(different_variance.moduli(), fixture.params.moduli());
    assert_eq!(
        different_variance.plaintext(),
        fixture.params.plaintext_modulus()
    );
    assert!(matches!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&wire, &different_variance),
        Err(DarkAmmError::PublicHostParameterMismatch)
    ));

    let mut zero_cap = wire.clone();
    zero_cap[72..80].copy_from_slice(&0u64.to_le_bytes());
    refresh_public_host_checksum(&mut zero_cap);
    assert!(DarkPoolPublicHostMaterial::from_wire_bytes(&zero_cap, fixture.params.arc()).is_err());

    let mut wrapping_caps = wire.clone();
    wrapping_caps[72..80].copy_from_slice(&1_016u64.to_le_bytes());
    wrapping_caps[80..88].copy_from_slice(&1_016u64.to_le_bytes());
    refresh_public_host_checksum(&mut wrapping_caps);
    assert!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&wrapping_caps, fixture.params.arc()).is_err()
    );

    let mut impossible_k = wire.clone();
    impossible_k[64..72].copy_from_slice(&400_001u64.to_le_bytes());
    refresh_public_host_checksum(&mut impossible_k);
    assert!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&impossible_k, fixture.params.arc()).is_err()
    );

    let mut oversized_pk = wire.clone();
    oversized_pk[88..96].copy_from_slice(&u64::MAX.to_le_bytes());
    refresh_public_host_checksum(&mut oversized_pk);
    assert!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&oversized_pk, fixture.params.arc()).is_err()
    );

    let mut malformed_pk = wire.clone();
    malformed_pk[96] = 0xff;
    refresh_public_host_checksum(&mut malformed_pk);
    assert!(
        DarkPoolPublicHostMaterial::from_wire_bytes(&malformed_pk, fixture.params.arc()).is_err()
    );
}

#[test]
fn secretless_public_host_restarts_chain_and_emits_collective_equality_inputs() {
    // This entire integration target imports no SecretKey and never calls
    // threshold::combine. Key generation/relin use only opaque party objects.
    let fixture = CollectiveFixture::new(0x64);
    let initial = fixture.pool();
    let initial_x = initial.reserve_cts().ct_x.ct.to_bytes();
    let initial_y = initial.reserve_cts().ct_y.ct.to_bytes();
    let initial_wire = initial
        .public_host_material()
        .expect("initial public host snapshot")
        .to_wire_bytes();
    drop(initial);

    let initial_material =
        DarkPoolPublicHostMaterial::from_wire_bytes(&initial_wire, fixture.params.arc())
            .expect("restart parses public state");
    let mut host = DarkPool::restore_public_host(fixture.params.arc(), &initial_material)
        .expect("host restores without secret key");
    assert_eq!(host.reserve_cts().ct_x.ct.to_bytes(), initial_x);
    assert_eq!(host.reserve_cts().ct_y.ct.to_bytes(), initial_y);

    let dx1 = fixture.encrypted_amount(50);
    let dy1 = fixture.encrypted_amount(300);
    let candidate1 = host
        .try_private_swap_proposed(&dx1, &dy1)
        .expect("restored host produces encrypted equality target");
    assert!(!candidate1.invariant.ct.to_bytes().is_empty());
    assert_ne!(candidate1.decision_session_nonce(), [0; 32]);
    let (session1, decision1) =
        masked_invariant_decision(&fixture, &candidate1, host.k, 0x6400_0001);
    assert!(decision1.is_equal());
    assert!(decision1.transcript.is_reveal_only(&session1));
    host.commit_private_decision(candidate1, decision1)
        .expect("collective bit commits first candidate");

    let after_first_x = host.reserve_cts().ct_x.ct.to_bytes();
    let after_first_y = host.reserve_cts().ct_y.ct.to_bytes();
    let first_wire = host
        .public_host_material()
        .expect("post-swap public host snapshot")
        .to_wire_bytes();
    drop(host);
    let first_material =
        DarkPoolPublicHostMaterial::from_wire_bytes(&first_wire, fixture.params.arc())
            .expect("second process parses exact ciphertext state");
    let mut restarted = DarkPool::restore_public_host(fixture.params.arc(), &first_material)
        .expect("second process restores without secret key");
    assert_eq!(restarted.reserve_cts().ct_x.ct.to_bytes(), after_first_x);
    assert_eq!(restarted.reserve_cts().ct_y.ct.to_bytes(), after_first_y);
    assert_ne!(after_first_x, initial_x);
    assert_ne!(after_first_y, initial_y);

    let dx2 = fixture.encrypted_amount(150);
    let dy2 = fixture.encrypted_amount(300);
    let candidate2 = restarted
        .try_private_swap_proposed(&dx2, &dy2)
        .expect("restarted host produces next equality target");
    let nonce2 = candidate2.decision_session_nonce();
    let (session2, decision2) =
        masked_invariant_decision(&fixture, &candidate2, restarted.k, 0x6400_0002);
    assert!(decision2.is_equal());
    assert!(decision2.transcript.is_reveal_only(&session2));
    restarted
        .commit_private_decision(candidate2, decision2)
        .expect("collective bit commits chained candidate");
    let final_material = restarted
        .public_host_material()
        .expect("final public-only snapshot");
    let final_wire = final_material.to_wire_bytes();
    let final_roundtrip =
        DarkPoolPublicHostMaterial::from_wire_bytes(&final_wire, fixture.params.arc())
            .expect("final state is restartable");
    assert_eq!(final_roundtrip, final_material);
    assert_ne!(nonce2, [0; 32]);
}

#[test]
fn restarted_host_commits_independent_attested_bit_without_runtime_decision_capability() {
    let fixture = CollectiveFixture::new(0x65);
    let initial = fixture.pool();
    let initial_material = initial
        .public_host_material()
        .expect("initial public host state");
    drop(initial);

    let mut host = DarkPool::restore_public_host(fixture.params.arc(), &initial_material)
        .expect("secretless host restart");
    let dx = fixture.encrypted_amount(50);
    let dy = fixture.encrypted_amount(300);
    let candidate = host
        .try_private_swap_proposed(&dx, &dy)
        .expect("encrypted candidate");
    let candidate_nonce = candidate.decision_session_nonce();
    let before_x = host.reserve_cts().ct_x.ct.to_bytes();
    let before_y = host.reserve_cts().ct_y.ct.to_bytes();

    let (session, runtime_decision) =
        masked_invariant_decision(&fixture, &candidate, host.k, 0x6500_0001);
    assert!(runtime_decision.is_equal());
    let transcript = runtime_decision.transcript.clone();
    let (keys, verifier) = decision_quorum();
    let receipt = attested_receipt(&session, &runtime_decision, &keys, &verifier);
    // The process-local authorization capability is deliberately unavailable
    // to the committing host. Only independently transported public artifacts
    // remain.
    drop(runtime_decision);
    drop(session);

    let policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
        verifier.clone(),
    )
    .expect("independent relying-party policy");
    assert_eq!(policy.n_parties(), N);
    assert_eq!(policy.value_bits(), VALUE_BITS);
    assert_eq!(policy.verifier().roster_digest(), verifier.roster_digest());

    // A true invariant can still carry a public worst-case bound wider than
    // the configured equality circuit. Even a genuine masked equality bit and
    // quorum receipt must not authorize a truncated-domain decision.
    let wide_dx = fixture.encrypted_amount_with_bound(50, 200);
    let wide_candidate = host
        .try_private_swap_proposed(&wide_dx, &dy)
        .expect("BFV modulus admits the wider public bound");
    assert!(wide_candidate.invariant.plain_bound >= (1 << VALUE_BITS));
    let (wide_session, wide_decision) =
        masked_invariant_decision(&fixture, &wide_candidate, host.k, 0x6500_0002);
    assert!(wide_decision.is_equal());
    let wide_receipt = attested_receipt(&wide_session, &wide_decision, &keys, policy.verifier());
    let mut wide_replay = SnapshotReplayGuard::new([0x64; 32]);
    assert!(matches!(
        commit_attested_private_decision(
            &mut host,
            &wide_candidate,
            &policy,
            &wide_decision.transcript,
            &wide_receipt,
            &mut wide_replay,
        ),
        Err(AttestedPrivateCommitError::CandidateRangeExceedsDecisionWidth {
            candidate_bound,
            range_end,
        }) if candidate_bound >= range_end && range_end == (1 << VALUE_BITS)
    ));
    assert!(wide_replay.is_empty());
    assert_eq!(host.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_eq!(host.reserve_cts().ct_y.ct.to_bytes(), before_y);

    // A well-formed but wrong host policy is rejected before replay storage is
    // touched; the exact same candidate/receipt can still pass under policy.
    let wrong_policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus() + 2,
        Duration::from_secs(5),
        verifier,
    )
    .expect("structurally valid but wrong BFV scalar domain");
    let mut replay = SnapshotReplayGuard::new([0x65; 32]);
    assert!(matches!(
        commit_attested_private_decision(
            &mut host,
            &candidate,
            &wrong_policy,
            &transcript,
            &receipt,
            &mut replay,
        ),
        Err(AttestedPrivateCommitError::PoolPlaintextModulusMismatch { .. })
    ));
    assert!(replay.is_empty());
    assert_eq!(host.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_eq!(host.reserve_cts().ct_y.ct.to_bytes(), before_y);

    commit_attested_private_decision(
        &mut host,
        &candidate,
        &policy,
        &transcript,
        &receipt,
        &mut replay,
    )
    .expect("fresh quorum-attested equality installs ciphertext state");
    assert_eq!(replay.len(), 1);
    assert_ne!(host.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_ne!(host.reserve_cts().ct_y.ct.to_bytes(), before_y);

    // Even with a fresh replay store, the old candidate cannot roll the now
    // advanced host backward. Candidate pre-state refusal itself consumes no
    // replay entry.
    let after_x = host.reserve_cts().ct_x.ct.to_bytes();
    let after_y = host.reserve_cts().ct_y.ct.to_bytes();
    let mut fresh_replay = SnapshotReplayGuard::new([0x66; 32]);
    assert_eq!(
        commit_attested_private_decision(
            &mut host,
            &candidate,
            &policy,
            &transcript,
            &receipt,
            &mut fresh_replay,
        ),
        Err(AttestedPrivateCommitError::Candidate(
            DarkAmmCommitPreflightError::CandidateContextMismatch
        ))
    );
    assert!(fresh_replay.is_empty());
    assert_eq!(host.reserve_cts().ct_x.ct.to_bytes(), after_x);
    assert_eq!(host.reserve_cts().ct_y.ct.to_bytes(), after_y);

    // A different restarted process deterministically reconstructs the same
    // candidate from the initial ciphertext state and encrypted amounts. The
    // durable replay snapshot still rejects the already accepted receipt.
    let replay_wire = replay.to_wire_bytes();
    let mut replay_after_restart = SnapshotReplayGuard::from_wire_bytes([0x65; 32], &replay_wire)
        .expect("durable replay state restarts");
    let mut duplicate_host = DarkPool::restore_public_host(fixture.params.arc(), &initial_material)
        .expect("independent initial-state restart");
    let duplicate_candidate = duplicate_host
        .try_private_swap_proposed(&dx, &dy)
        .expect("deterministic encrypted candidate reconstruction");
    assert_eq!(
        duplicate_candidate.decision_session_nonce(),
        candidate_nonce
    );
    assert!(matches!(
        commit_attested_private_decision(
            &mut duplicate_host,
            &duplicate_candidate,
            &policy,
            &transcript,
            &receipt,
            &mut replay_after_restart,
        ),
        Err(AttestedPrivateCommitError::Attestation(
            DecisionAttestationError::ReplayDetected
        ))
    ));
    assert_eq!(duplicate_host.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_eq!(duplicate_host.reserve_cts().ct_y.ct.to_bytes(), before_y);
}

#[test]
fn independently_attested_false_bit_holds_ciphertexts_and_replay() {
    let fixture = CollectiveFixture::new(0x66);
    let mut host = fixture.pool();
    let dx = fixture.encrypted_amount(50);
    let wrong_dy = fixture.encrypted_amount(301);
    let candidate = host
        .try_private_swap_proposed(&dx, &wrong_dy)
        .expect("well-shaped refusing candidate");
    let before_x = host.reserve_cts().ct_x.ct.to_bytes();
    let before_y = host.reserve_cts().ct_y.ct.to_bytes();
    let (session, runtime_decision) =
        masked_invariant_decision(&fixture, &candidate, host.k, 0x6600_0001);
    assert!(!runtime_decision.is_equal());
    let transcript = runtime_decision.transcript.clone();
    let (keys, verifier) = decision_quorum();
    let receipt = attested_receipt(&session, &runtime_decision, &keys, &verifier);
    drop(runtime_decision);
    drop(session);
    let policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
        verifier,
    )
    .expect("independent relying-party policy");
    let mut replay = SnapshotReplayGuard::new([0x67; 32]);
    assert_eq!(
        commit_attested_private_decision(
            &mut host,
            &candidate,
            &policy,
            &transcript,
            &receipt,
            &mut replay,
        ),
        Err(AttestedPrivateCommitError::DecisionRefused)
    );
    assert!(replay.is_empty());
    assert_eq!(host.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_eq!(host.reserve_cts().ct_y.ct.to_bytes(), before_y);
}
