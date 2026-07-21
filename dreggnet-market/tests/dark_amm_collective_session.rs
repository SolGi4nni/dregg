//! End-to-end game-service cutover: collective BFV public material, a real
//! HidingFri transition proof, collective Tier-1 same-opening, one staged
//! encrypted candidate, independent authenticated FHDAR decision, atomic
//! commit, and restart on both sides of the phase boundary.

#![cfg(feature = "dark-amm-game")]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use dregg_circuit_prove::dark_amm_private::{PrivateAmmWitness, prove_zk};
use dreggnet_market::dark_amm_collective::{
    CollectiveDarkAmmConfig, CollectiveDarkAmmError, CollectiveDarkAmmOffering,
    CollectiveDarkAmmSession, CollectiveDecisionBundle, DARK_AMM_COLLECTIVE_ABANDON_BYTES,
    DARK_AMM_COLLECTIVE_ABANDON_DISCLOSURE, DARK_AMM_COLLECTIVE_ABANDON_MEDIA_TYPE,
    DARK_AMM_COLLECTIVE_ABANDON_OPERATION, DARK_AMM_COLLECTIVE_COMMIT_OPERATION,
    DARK_AMM_COLLECTIVE_STAGE_OPERATION, DARK_AMM_COLLECTIVE_TASK_ARTIFACT,
    DARK_AMM_COLLECTIVE_TASK_MEDIA_TYPE,
};
use dreggnet_market::dark_amm_collective_worker::{
    CollectiveDecisionTask, CollectiveDecisionTaskContext,
};
use dreggnet_market::dark_amm_game::{
    DarkAmmPublicSession, SameOpeningProvedEncryptedSwapRequest,
    produce_proved_encrypted_swap_seeded,
};
use dreggnet_offerings::{BinaryArtifactVisibility, DreggIdentity, Offering, SessionConfig};
use ed25519_dalek::SigningKey;
use fhe::bfv::{PublicKey, RelinearizationKey};
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};
use fhegg_fhe::amm_same_opening::{
    AmmPrivacyTier, AmmSameOpeningContext, ExactBfvAmountOpening, Tier1SameOpeningAuthority,
};
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
};
use fhegg_fhe::dark_amm::{DarkPool, DarkPoolPublicHostMaterial};
use fhegg_fhe::dark_amm_attested::AttestedPrivateDecisionPolicy;
use fhegg_fhe::decision_attestation::{AttestedDecisionReceipt, ExpectedDecisionContext};
use fhegg_fhe::mpc_party::{DecisionTranscript, PartyMpcSession, simulate_decision_transcript};
use fhegg_fhe::threshold::relin::{RelinKeySession, generate_relinearization_key};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use rand::SeedableRng as SeedableRng08;
use rand::rngs::StdRng as StdRng08;

const N: usize = 3;
const VALUE_BITS: usize = 19;
const HOSTED_SESSION: [u8; 32] = [0x91; 32];
const WORKER_INPUT_CHECKSUM_DOMAIN: &str = "dregg-dark-amm-collective-worker-input-checksum-v1";

struct CollectiveFixture {
    params: BfvParams,
    keygen: KeygenSession,
    public_key_bytes: Vec<u8>,
    relin: RelinearizationKey,
    threshold_roots: Vec<[u8; 32]>,
}

impl CollectiveFixture {
    fn new() -> Self {
        let params = BfvParams::fold_set();
        let keygen = KeygenSession::from_seed(N, [0x92; 32]).unwrap();
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        let mut parties = Vec::new();
        let threshold_roots = (0..N)
            .map(|party| [0x31 + party as u8; 32])
            .collect::<Vec<_>>();
        for party in 0..N {
            let (holder, contribution) =
                ThresholdParty::join_seeded(&keygen, party, &params, &threshold_roots[party])
                    .unwrap();
            coordinator.accept(contribution).unwrap();
            parties.push(holder);
        }
        let collective = coordinator.finish().unwrap();
        let public_key_bytes = collective.pk.to_bytes();
        let relin_session = RelinKeySession::from_public_entropy(
            &keygen,
            &collective,
            [0x93; 32],
            Duration::from_secs(30),
        )
        .unwrap();
        let relin =
            generate_relinearization_key(&relin_session, &params, &collective, &parties).unwrap();
        Self {
            params,
            keygen,
            public_key_bytes,
            relin,
            threshold_roots,
        }
    }

    fn collective(&self) -> CollectivePublicKey {
        CollectivePublicKey {
            pk: PublicKey::from_bytes(&self.public_key_bytes, self.params.arc()).unwrap(),
        }
    }

    fn initial_material(&self) -> DarkPoolPublicHostMaterial {
        let collective = self.collective();
        let mut pool = DarkPool::init(
            self.params.arc(),
            &collective.pk,
            &self.relin,
            100,
            900,
            400,
            1_000,
            &mut rand_09::rng(),
        )
        .unwrap();
        pool.strip_lp_view();
        pool.public_host_material().unwrap()
    }
}

fn signing_keys(seed: u8) -> Vec<SigningKey> {
    (0..N)
        .map(|index| SigningKey::from_bytes(&[seed + index as u8; 32]))
        .collect()
}

fn verifier(keys: &[SigningKey]) -> AuthenticatedQuorumVerifier {
    AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap()
}

struct WorkerTestDir(PathBuf);

impl WorkerTestDir {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "dregg-dark-amm-worker-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for WorkerTestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn worker_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(WORKER_INPUT_CHECKSUM_DOMAIN);
    hash.update(&(content.len() as u64).to_le_bytes());
    hash.update(content);
    *hash.finalize().as_bytes()
}

fn finish_worker_wire(mut content: Vec<u8>) -> Vec<u8> {
    content.extend_from_slice(&worker_checksum(&content));
    content
}

fn worker_config_digest(config_wire: &[u8]) -> [u8; 32] {
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-dark-amm-collective-worker-configuration-v1");
    hash.update(&(config_wire.len() as u64).to_le_bytes());
    hash.update(config_wire);
    *hash.finalize().as_bytes()
}

fn worker_context_wire(context: CollectiveDecisionTaskContext) -> Vec<u8> {
    let mut wire = Vec::new();
    wire.extend_from_slice(b"DBCTX001");
    wire.extend_from_slice(&context.hosted_session);
    wire.extend_from_slice(&context.sequence.to_le_bytes());
    for lane in context.committed_root {
        wire.extend_from_slice(&lane.to_le_bytes());
    }
    wire.extend_from_slice(&context.same_opening_claim_digest);
    finish_worker_wire(wire)
}

fn worker_config_wire(fixture: &CollectiveFixture, decision_keys: &[SigningKey]) -> Vec<u8> {
    let mut wire = Vec::new();
    wire.extend_from_slice(b"DBWCv001");
    wire.extend_from_slice(&(N as u64).to_le_bytes());
    wire.extend_from_slice(&fixture.keygen.crp_seed());
    wire.extend_from_slice(&(VALUE_BITS as u64).to_le_bytes());
    wire.extend_from_slice(&5_000u64.to_le_bytes());
    wire.extend_from_slice(&2u64.to_le_bytes());
    wire.extend_from_slice(&(decision_keys.len() as u64).to_le_bytes());
    for key in decision_keys {
        wire.extend_from_slice(&key.verifying_key().to_bytes());
    }
    finish_worker_wire(wire)
}

fn party_custody_wire(
    config_wire: &[u8],
    party: usize,
    threshold_root: [u8; 32],
    decision_key: &SigningKey,
) -> Vec<u8> {
    let mut wire = Vec::new();
    wire.extend_from_slice(b"DBPCv001");
    wire.extend_from_slice(&worker_config_digest(config_wire));
    wire.extend_from_slice(&(party as u64).to_le_bytes());
    wire.extend_from_slice(&threshold_root);
    wire.extend_from_slice(&[0x81 + party as u8; 32]);
    wire.extend_from_slice(&decision_key.to_bytes());
    finish_worker_wire(wire)
}

fn write_worker_file(path: &Path, bytes: &[u8], secret: bool) {
    fs::write(path, bytes).unwrap();
    #[cfg(unix)]
    if secret {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o600)).unwrap();
    }
}

fn run_party_contribute(config: &Path, custody: &Path, output: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_dark-amm-tool"))
        .arg("collective-party-contribute")
        .arg(config)
        .arg(custody)
        .arg(output)
        .output()
        .unwrap()
}

fn run_split_collective_worker(
    task: &Path,
    material: &Path,
    context: &Path,
    config: &Path,
    output: &Path,
    parties: &[(PathBuf, PathBuf)],
) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_dark-amm-tool"));
    command
        .arg("collective-decide-split")
        .arg(task)
        .arg(material)
        .arg(context)
        .arg(config)
        .arg(output);
    for (custody, artifact) in parties {
        command.arg(custody).arg(artifact);
    }
    command.output().unwrap()
}

fn decode_hex_digest(value: &str) -> [u8; 32] {
    let bytes = (0..32)
        .map(|index| u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap())
        .collect::<Vec<_>>();
    <[u8; 32]>::try_from(bytes).unwrap()
}

fn config(
    fixture: &CollectiveFixture,
    hosted_session: [u8; 32],
    same_opening_verifier: AuthenticatedQuorumVerifier,
    decision_verifier: AuthenticatedQuorumVerifier,
) -> CollectiveDarkAmmConfig {
    let decision_policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
        decision_verifier,
    )
    .unwrap();
    CollectiveDarkAmmConfig::new(
        hosted_session,
        fixture.params.clone(),
        fixture.keygen.clone(),
        fixture.collective(),
        same_opening_verifier,
        decision_policy,
    )
    .unwrap()
}

fn decision_receipt(
    candidate_nonce: [u8; 32],
    equal: bool,
    keys: &[SigningKey],
    decision_verifier: &AuthenticatedQuorumVerifier,
) -> (DecisionTranscript, AttestedDecisionReceipt) {
    let session = PartyMpcSession::equality(
        candidate_nonce,
        N,
        VALUE_BITS,
        BfvParams::fold_set().plaintext_modulus(),
        Duration::from_secs(5),
    )
    .unwrap();
    let mut transcript_rng = StdRng08::seed_from_u64(if equal { 0x9401 } else { 0x9400 });
    let transcript = simulate_decision_transcript(equal, &session, &mut transcript_rng).unwrap();
    assert!(transcript.is_reveal_only(&session));
    let expected = ExpectedDecisionContext {
        session: &session,
        roster_digest: decision_verifier.roster_digest(),
        transcript: &transcript,
        equal,
    };
    let draft = AttestedDecisionReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    let signatures = [0usize, 2]
        .map(|index| {
            decision_verifier
                .sign_claim(&draft.claim_digest(), index, &keys[index])
                .unwrap()
        })
        .to_vec();
    let evidence = decision_verifier
        .assemble_evidence(&draft.claim_digest(), &signatures)
        .unwrap();
    AttestedDecisionReceipt::issue(&expected, evidence)
        .map(|receipt| (transcript, receipt))
        .unwrap()
}

#[test]
fn collective_two_phase_game_session_is_atomic_and_restartable_without_host_secret() {
    let fixture = CollectiveFixture::new();
    let same_opening_keys = signing_keys(0xa1);
    let decision_keys = signing_keys(0xb1);
    let same_opening_authority = Tier1SameOpeningAuthority::new(
        same_opening_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap();
    let decision_verifier = verifier(&decision_keys);

    let witness = PrivateAmmWitness::try_new(
        100,
        900,
        50,
        300,
        [1_000, 1_001, 1_002, 1_003, 1_004, 1_005, 1_006, 1_007],
        [2_000, 2_001, 2_002, 2_003, 2_004, 2_005, 2_006, 2_007],
    )
    .unwrap();
    let seed_public = DarkAmmPublicSession::try_from_collective(
        HOSTED_SESSION,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective(),
        90_000,
        400,
        1_000,
        0,
        [1; 8],
    )
    .unwrap();
    let (proof, statement) = prove_zk(seed_public.private_amm_receipt_session(), &witness).unwrap();
    let material = fixture.initial_material();
    let mut host = CollectiveDarkAmmSession::new(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        material.clone(),
        statement.old_root,
        0,
    )
    .unwrap();
    let public = host.public_session().unwrap();
    let public_wire = public.to_wire_bytes();
    assert_eq!(&public_wire[..8], b"DBAPv003");
    assert_eq!(
        DarkAmmPublicSession::from_wire_bytes(&public_wire).unwrap(),
        public
    );
    for retired_magic in [b"DBAPv001", b"DBAPv002"] {
        let mut retired = public_wire.clone();
        retired[..8].copy_from_slice(retired_magic);
        assert!(
            DarkAmmPublicSession::from_wire_bytes(&retired).is_err(),
            "retired public-session version must fail closed"
        );
    }
    let proved = produce_proved_encrypted_swap_seeded(
        &public,
        50,
        300,
        100,
        400,
        statement,
        proof.to_postcard().unwrap(),
        [0xc1; 32],
        [0xc2; 32],
    )
    .unwrap();
    let (dx, dy) = proved.bounded_ciphertexts(fixture.params.arc()).unwrap();
    let decoded_proof = proved.decoded_private_amm_proof().unwrap();
    let authority_collective = fixture.collective();
    let opening_context = AmmSameOpeningContext {
        privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
        hosted_session: HOSTED_SESSION,
        sequence: 0,
        dx_bound: proved.dx_bound(),
        dy_bound: proved.dy_bound(),
        params: &fixture.params,
        keygen: &fixture.keygen,
        collective: &authority_collective,
        dx_ciphertext: &dx.ct,
        dy_ciphertext: &dy.ct,
        proof: &decoded_proof,
        statement,
    };
    let dx_opening = ExactBfvAmountOpening::new(50, [0xc1; 32]);
    let dy_opening = ExactBfvAmountOpening::new(300, [0xc2; 32]);
    let endorsements = [0usize, 2]
        .map(|index| {
            same_opening_authority
                .endorse(
                    &opening_context,
                    &witness,
                    &dx_opening,
                    &dy_opening,
                    index,
                    &same_opening_keys[index],
                )
                .unwrap()
        })
        .to_vec();
    let same_opening_receipt = same_opening_authority
        .assemble_receipt(&endorsements)
        .unwrap();
    assert_eq!(same_opening_receipt.claim.bfv.n_parties, N as u64);
    let request = SameOpeningProvedEncryptedSwapRequest::new(proved, same_opening_receipt);
    let request_wire = request.to_wire_bytes();

    // Cross-session ingress is rejected before any replay or pending mutation.
    let mut other_session = CollectiveDarkAmmSession::new(
        config(
            &fixture,
            [0x99; 32],
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        material,
        statement.old_root,
        0,
    )
    .unwrap();
    let other_before = other_session.checkpoint_wire_bytes();
    assert!(matches!(
        other_session.stage_same_opening_request(&request_wire),
        Err(CollectiveDarkAmmError::Refused(_))
    ));
    assert_eq!(other_session.checkpoint_wire_bytes(), other_before);

    let committed_before = host.public_host_material().material_digest();
    let staged = host.stage_same_opening_request(&request_wire).unwrap();
    assert_eq!(staged.sequence, 0);
    assert_eq!(staged.new_root, statement.new_root);
    assert!(host.has_pending_candidate());
    assert_eq!(
        host.public_host_material().material_digest(),
        committed_before
    );
    assert_eq!(host.current_root(), statement.old_root);
    assert_eq!(host.next_sequence(), 0);
    assert_eq!(host.same_opening_replay_revision(), 0);
    assert_eq!(host.decision_replay_revision(), 0);
    assert_eq!(
        host.stage_same_opening_request(&request_wire),
        Err(CollectiveDarkAmmError::PendingCandidateExists)
    );

    // The public pending carrier survives restart only after full
    // proof/signature reconstruction and a consumed replay-slot check.
    let pending_checkpoint = host.checkpoint_wire_bytes();
    let mut host = CollectiveDarkAmmSession::restore_from_checkpoint(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        &pending_checkpoint,
    )
    .unwrap();
    assert!(host.has_pending_candidate());
    assert_eq!(host.checkpoint_wire_bytes(), pending_checkpoint);

    // A false decision, a cross-candidate decision, and residual-only evidence
    // each preserve every byte of authoritative state, including replay sets.
    let (false_transcript, false_receipt) = decision_receipt(
        staged.decision_task_digest,
        false,
        &decision_keys,
        &decision_verifier,
    );
    let before_false = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&false_transcript, &false_receipt)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_false);

    let (cross_transcript, cross_receipt) =
        decision_receipt([0xd1; 32], true, &decision_keys, &decision_verifier);
    let before_cross = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&cross_transcript, &cross_receipt)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_cross);

    // The old context-free candidate nonce is no longer a valid hosted
    // authority session: a correctly signed legacy receipt still refuses.
    let (legacy_transcript, legacy_receipt) = decision_receipt(
        staged.candidate_nonce,
        true,
        &decision_keys,
        &decision_verifier,
    );
    let before_legacy = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&legacy_transcript, &legacy_receipt)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_legacy);

    let (transcript, receipt) = decision_receipt(
        staged.decision_task_digest,
        true,
        &decision_keys,
        &decision_verifier,
    );
    let mut residual_only = receipt.clone();
    residual_only.computation_integrity = ComputationIntegrityEvidence::BindingOnly(
        ComputationIntegrityResidual::OutputOnlySelfAssertion,
    );
    let before_evidence = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&transcript, &residual_only)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_evidence);

    let committed = host
        .commit_attested_decision(&transcript, &receipt)
        .unwrap();
    assert_eq!(committed.committed_sequence, 0);
    assert_eq!(committed.next_sequence, 1);
    assert_eq!(committed.new_root, statement.new_root);
    assert_eq!(
        committed.same_opening_claim_digest,
        staged.same_opening_claim_digest
    );
    assert_eq!(committed.decision_claim_digest, receipt.claim_digest());
    assert!(!host.has_pending_candidate());
    assert_eq!(host.current_root(), statement.new_root);
    assert_eq!(host.next_sequence(), 1);
    assert_eq!(host.same_opening_replay_revision(), 1);
    assert_eq!(host.decision_replay_revision(), 1);
    assert_ne!(
        host.public_host_material().material_digest(),
        committed_before
    );

    let committed_checkpoint = host.checkpoint_wire_bytes();
    let mut restarted = CollectiveDarkAmmSession::restore_from_checkpoint(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        &committed_checkpoint,
    )
    .unwrap();
    assert_eq!(restarted.checkpoint_wire_bytes(), committed_checkpoint);
    let before_stale = restarted.checkpoint_wire_bytes();
    assert!(matches!(
        restarted.stage_same_opening_request(&request_wire),
        Err(CollectiveDarkAmmError::Refused(_))
    ));
    assert_eq!(restarted.checkpoint_wire_bytes(), before_stale);

    // Explicit cancellation clears only the public pending carrier. Phase one
    // did not burn the sequence slot, so the exact request (or a competing
    // verified same-sequence request) may be staged after restart.
    let mut cancelled = CollectiveDarkAmmSession::new(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier,
        ),
        fixture.initial_material(),
        statement.old_root,
        0,
    )
    .unwrap();
    let before_cancel_stage = cancelled.checkpoint_wire_bytes();
    let staged_for_cancel = cancelled.stage_same_opening_request(&request_wire).unwrap();
    assert_eq!(cancelled.same_opening_replay_revision(), 0);
    let committed_material = cancelled.public_host_material().material_digest();
    let abandoned = cancelled.abandon_pending().unwrap();
    assert_eq!(abandoned, staged_for_cancel);
    assert!(!cancelled.has_pending_candidate());
    assert_eq!(
        cancelled.public_host_material().material_digest(),
        committed_material
    );
    assert_eq!(cancelled.current_root(), statement.old_root);
    assert_eq!(cancelled.next_sequence(), 0);
    let abandoned_checkpoint = cancelled.checkpoint_wire_bytes();
    assert_eq!(abandoned_checkpoint, before_cancel_stage);
    let mut cancelled = CollectiveDarkAmmSession::restore_from_checkpoint(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            verifier(&decision_keys),
        ),
        &abandoned_checkpoint,
    )
    .unwrap();
    let restaged = cancelled.stage_same_opening_request(&request_wire).unwrap();
    assert_eq!(restaged, staged_for_cancel);
    assert!(cancelled.has_pending_candidate());
    assert_eq!(cancelled.same_opening_replay_revision(), 0);
}

#[test]
fn collective_service_is_a_replay_verified_two_phase_game_offering() {
    const SEED: u64 = 0xc011_ec71;
    const BASE_SESSION: [u8; 32] = [0x95; 32];

    let fixture = CollectiveFixture::new();
    let material = fixture.initial_material();
    let hosted_session =
        CollectiveDarkAmmOffering::derive_hosted_session(BASE_SESSION, SEED, &material).unwrap();
    let bootstrap = DarkAmmPublicSession::try_from_collective(
        hosted_session,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective(),
        90_000,
        400,
        1_000,
        0,
        [1; 8],
    )
    .unwrap();
    let witness = PrivateAmmWitness::try_new(
        100,
        900,
        50,
        300,
        [3_000, 3_001, 3_002, 3_003, 3_004, 3_005, 3_006, 3_007],
        [4_000, 4_001, 4_002, 4_003, 4_004, 4_005, 4_006, 4_007],
    )
    .unwrap();
    let (proof, statement) = prove_zk(bootstrap.private_amm_receipt_session(), &witness).unwrap();

    let same_opening_keys = signing_keys(0xc1);
    let decision_keys = signing_keys(0xd1);
    let same_opening_authority = Tier1SameOpeningAuthority::new(
        same_opening_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap();
    let decision_verifier = verifier(&decision_keys);
    let decision_policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
        decision_verifier.clone(),
    )
    .unwrap();
    let offering = CollectiveDarkAmmOffering::new(
        BASE_SESSION,
        SEED,
        fixture.params.clone(),
        fixture.keygen.clone(),
        fixture.collective(),
        material.clone(),
        statement.old_root,
        same_opening_authority.verifier().clone(),
        decision_policy,
    )
    .unwrap();
    let mut game = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    let public = game.public_session().unwrap();
    assert_eq!(public.session_id(), hosted_session);
    assert_eq!(
        public.proof_context().unwrap().current_root(),
        statement.old_root
    );
    assert_eq!(
        offering.binary_operations(&game)[0].name,
        DARK_AMM_COLLECTIVE_STAGE_OPERATION
    );
    assert!(offering.binary_artifacts(&game).is_empty());

    let proved = produce_proved_encrypted_swap_seeded(
        &public,
        50,
        300,
        100,
        400,
        statement,
        proof.to_postcard().unwrap(),
        [0xe1; 32],
        [0xe2; 32],
    )
    .unwrap();
    let (dx, dy) = proved.bounded_ciphertexts(fixture.params.arc()).unwrap();
    let decoded_proof = proved.decoded_private_amm_proof().unwrap();
    let authority_collective = fixture.collective();
    let opening_context = AmmSameOpeningContext {
        privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
        hosted_session,
        sequence: 0,
        dx_bound: proved.dx_bound(),
        dy_bound: proved.dy_bound(),
        params: &fixture.params,
        keygen: &fixture.keygen,
        collective: &authority_collective,
        dx_ciphertext: &dx.ct,
        dy_ciphertext: &dy.ct,
        proof: &decoded_proof,
        statement,
    };
    let dx_opening = ExactBfvAmountOpening::new(50, [0xe1; 32]);
    let dy_opening = ExactBfvAmountOpening::new(300, [0xe2; 32]);
    let endorsements = [0usize, 2]
        .map(|index| {
            same_opening_authority
                .endorse(
                    &opening_context,
                    &witness,
                    &dx_opening,
                    &dy_opening,
                    index,
                    &same_opening_keys[index],
                )
                .unwrap()
        })
        .to_vec();
    let request = SameOpeningProvedEncryptedSwapRequest::new(
        proved,
        same_opening_authority
            .assemble_receipt(&endorsements)
            .unwrap(),
    );
    let request_wire = request.to_wire_bytes();
    let actor = DreggIdentity("player:collective-swapper".to_string());

    // Journal preflight performs strict canonical decoding but no mutation.
    let replay = offering
        .binary_operation_replay_material(&game, DARK_AMM_COLLECTIVE_STAGE_OPERATION, &request_wire)
        .unwrap()
        .unwrap();
    assert_eq!(replay.bytes, request_wire);
    assert!(!game.has_pending_candidate());
    let staged_receipt = offering
        .invoke_binary_operation(
            &mut game,
            DARK_AMM_COLLECTIVE_STAGE_OPERATION,
            &request_wire,
            actor.clone(),
        )
        .unwrap();
    assert!(game.has_pending_candidate());
    assert_eq!(
        staged_receipt.operation,
        DARK_AMM_COLLECTIVE_STAGE_OPERATION
    );
    let pending_operations = offering.binary_operations(&game);
    assert_eq!(pending_operations.len(), 2);
    assert_eq!(
        pending_operations[0].name,
        DARK_AMM_COLLECTIVE_COMMIT_OPERATION
    );
    assert_eq!(
        pending_operations[1].name,
        DARK_AMM_COLLECTIVE_ABANDON_OPERATION
    );
    assert_eq!(
        pending_operations[1].input_media_type,
        DARK_AMM_COLLECTIVE_ABANDON_MEDIA_TYPE
    );
    assert_eq!(
        pending_operations[1].max_input_bytes,
        DARK_AMM_COLLECTIVE_ABANDON_BYTES
    );
    assert_eq!(
        pending_operations[1].disclosure,
        DARK_AMM_COLLECTIVE_ABANDON_DISCLOSURE
    );
    let artifacts = offering.binary_artifacts(&game);
    assert_eq!(artifacts.len(), 1);
    assert_eq!(artifacts[0].name, DARK_AMM_COLLECTIVE_TASK_ARTIFACT);
    assert_eq!(artifacts[0].media_type, DARK_AMM_COLLECTIVE_TASK_MEDIA_TYPE);
    assert_eq!(artifacts[0].visibility, BinaryArtifactVisibility::Public);

    let candidate_nonce = staged_receipt
        .public_fields
        .iter()
        .find(|(name, _)| name == "candidateNonce")
        .map(|(_, value)| decode_hex_digest(value))
        .unwrap();
    let task_digest = staged_receipt
        .public_fields
        .iter()
        .find(|(name, _)| name == "decisionTaskDigest")
        .map(|(_, value)| decode_hex_digest(value))
        .unwrap();

    // Journal preflight accepts only the exact current task identity and
    // returns that same fixed-width public digest as canonical replay
    // material. Preflight is read-only: neither owner nor encrypted state is
    // changed before the operation is actually invoked.
    let abandon_replay = offering
        .binary_operation_replay_material(
            &game,
            DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
            &task_digest,
        )
        .unwrap()
        .unwrap();
    assert_eq!(abandon_replay.bytes, task_digest);
    assert_eq!(
        abandon_replay.disclosure,
        DARK_AMM_COLLECTIVE_ABANDON_DISCLOSURE
    );
    assert!(game.has_pending_candidate());
    assert!(
        offering
            .binary_operation_replay_material(
                &game,
                DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
                &task_digest[..31],
            )
            .is_err()
    );
    assert!(game.has_pending_candidate());

    // The staging identity owns this exact pending slot at the shared-surface
    // layer. Another web/Telegram/Discord identity cannot cancel it, and a
    // stale task digest cannot cancel a replacement candidate at the same
    // sequence. Both refusals preserve the encrypted state and replay guards.
    let stranger = DreggIdentity("player:not-the-stager".to_string());
    assert!(
        offering
            .invoke_binary_operation(
                &mut game,
                DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
                &task_digest,
                stranger.clone(),
            )
            .is_err()
    );
    assert!(game.has_pending_candidate());
    let mut wrong_task_digest = task_digest;
    wrong_task_digest[0] ^= 1;
    assert!(
        offering
            .binary_operation_replay_material(
                &game,
                DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
                &wrong_task_digest,
            )
            .is_err()
    );
    assert!(
        offering
            .invoke_binary_operation(
                &mut game,
                DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
                &wrong_task_digest,
                actor.clone(),
            )
            .is_err()
    );
    assert!(game.has_pending_candidate());
    let abandon_receipt = offering
        .invoke_binary_operation(
            &mut game,
            DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
            &task_digest,
            actor.clone(),
        )
        .unwrap();
    assert_eq!(
        abandon_receipt.operation,
        DARK_AMM_COLLECTIVE_ABANDON_OPERATION
    );
    assert_eq!(
        abandon_receipt
            .public_fields
            .iter()
            .find(|(name, _)| name == "phase")
            .map(|(_, value)| value.as_str()),
        Some("abandoned")
    );
    assert_eq!(
        abandon_receipt
            .public_fields
            .iter()
            .find(|(name, _)| name == "decisionTaskDigest")
            .map(|(_, value)| decode_hex_digest(value)),
        Some(task_digest)
    );
    assert_eq!(
        abandon_receipt
            .public_fields
            .iter()
            .find(|(name, _)| name == "replaySlotsConsumed")
            .map(|(_, value)| value.as_str()),
        Some("0")
    );
    assert!(!game.has_pending_candidate());
    assert_eq!(
        offering.binary_operations(&game)[0].name,
        DARK_AMM_COLLECTIVE_STAGE_OPERATION
    );
    let report = offering.verify(&game);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 2);

    // Neither replay guard was consumed by stage/abandon, so the identical
    // proof-bearing request remains live and reconstructs the same task.
    let restaged_receipt = offering
        .invoke_binary_operation(
            &mut game,
            DARK_AMM_COLLECTIVE_STAGE_OPERATION,
            &request_wire,
            actor.clone(),
        )
        .unwrap();
    let restaged_task_digest = restaged_receipt
        .public_fields
        .iter()
        .find(|(name, _)| name == "decisionTaskDigest")
        .map(|(_, value)| decode_hex_digest(value))
        .unwrap();
    assert_eq!(restaged_task_digest, task_digest);
    let candidate = game.pending_decision_candidate().unwrap();
    assert_eq!(candidate.decision_session_nonce(), candidate_nonce);
    let task = game.pending_decision_task().unwrap();
    assert!(task.matches_candidate(&candidate));
    assert_eq!(task.attestation_nonce().unwrap(), task_digest);
    let task_wire = offering
        .export_binary_artifact(&game, DARK_AMM_COLLECTIVE_TASK_ARTIFACT)
        .unwrap();
    assert_eq!(task_wire, task.to_wire_bytes().unwrap());
    let authority_collective = fixture.collective();
    let task = CollectiveDecisionTask::from_wire_bytes(
        &task_wire,
        &material,
        &fixture.params,
        &fixture.keygen,
        &authority_collective,
        VALUE_BITS,
    )
    .unwrap();
    let expected_task_context = CollectiveDecisionTaskContext {
        hosted_session,
        sequence: 0,
        committed_root: statement.old_root,
        same_opening_claim_digest: request.same_opening_receipt().claim.digest(),
    };
    task.validate_context(expected_task_context).unwrap();
    let worker_dir = WorkerTestDir::new();
    let task_path = worker_dir.path("task.dbdt");
    let material_path = worker_dir.path("material.dbhm");
    let context_path = worker_dir.path("context.dbctx");
    let config_path = worker_dir.path("worker.dbwc");
    write_worker_file(&task_path, &task_wire, false);
    write_worker_file(&material_path, &material.to_wire_bytes(), false);
    write_worker_file(
        &context_path,
        &worker_context_wire(expected_task_context),
        false,
    );
    let config_wire = worker_config_wire(&fixture, &decision_keys);
    write_worker_file(&config_path, &config_wire, false);
    let mut party_files = Vec::new();
    for party in 0..N {
        let custody_path = worker_dir.path(&format!("party-{party}.dbpc"));
        let artifact_path = worker_dir.path(&format!("party-{party}.dbpa"));
        write_worker_file(
            &custody_path,
            &party_custody_wire(
                &config_wire,
                party,
                fixture.threshold_roots[party],
                &decision_keys[party],
            ),
            true,
        );
        let contributed = run_party_contribute(&config_path, &custody_path, &artifact_path);
        assert!(
            contributed.status.success(),
            "{}",
            String::from_utf8_lossy(&contributed.stderr)
        );
        let output = format!(
            "{}{}",
            String::from_utf8_lossy(&contributed.stdout),
            String::from_utf8_lossy(&contributed.stderr)
        );
        assert!(!output.contains(&format!("{:02x}", 0x31 + party as u8).repeat(32)));
        party_files.push((custody_path, artifact_path));
    }

    // Every independently pinned input is fail-closed before an output file is
    // created: hosted context, canonical task, committed ciphertext material,
    // and deterministic threshold custody.
    let wrong_context_path = worker_dir.path("wrong-context.dbctx");
    write_worker_file(
        &wrong_context_path,
        &worker_context_wire(CollectiveDecisionTaskContext {
            sequence: 1,
            ..expected_task_context
        }),
        false,
    );
    let refused = run_split_collective_worker(
        &task_path,
        &material_path,
        &wrong_context_path,
        &config_path,
        &worker_dir.path("wrong-context.bundle"),
        &party_files,
    );
    assert!(!refused.status.success());

    let truncated_task_path = worker_dir.path("truncated-task.dbdt");
    write_worker_file(
        &truncated_task_path,
        &task_wire[..task_wire.len() - 1],
        false,
    );
    let refused = run_split_collective_worker(
        &truncated_task_path,
        &material_path,
        &context_path,
        &config_path,
        &worker_dir.path("truncated-task.bundle"),
        &party_files,
    );
    assert!(!refused.status.success());

    let wrong_material_path = worker_dir.path("wrong-material.dbhm");
    let wrong_material = fixture.initial_material();
    assert_ne!(wrong_material.material_digest(), material.material_digest());
    write_worker_file(&wrong_material_path, &wrong_material.to_wire_bytes(), false);
    let refused = run_split_collective_worker(
        &task_path,
        &wrong_material_path,
        &context_path,
        &config_path,
        &worker_dir.path("wrong-material.bundle"),
        &party_files,
    );
    assert!(!refused.status.success());

    let wrong_custody_path = worker_dir.path("wrong-party-0.dbpc");
    let mut wrong_root = fixture.threshold_roots[0];
    wrong_root[0] ^= 1;
    write_worker_file(
        &wrong_custody_path,
        &party_custody_wire(&config_wire, 0, wrong_root, &decision_keys[0]),
        true,
    );
    let mut wrong_custody_files = party_files.clone();
    wrong_custody_files[0].0 = wrong_custody_path;
    let refused = run_split_collective_worker(
        &task_path,
        &material_path,
        &context_path,
        &config_path,
        &worker_dir.path("wrong-custody.bundle"),
        &wrong_custody_files,
    );
    assert!(!refused.status.success());

    let tampered_artifact_path = worker_dir.path("tampered-party-0.dbpa");
    let mut tampered_artifact = fs::read(&party_files[0].1).unwrap();
    tampered_artifact[48] ^= 1;
    write_worker_file(&tampered_artifact_path, &tampered_artifact, false);
    let mut tampered_files = party_files.clone();
    tampered_files[0].1 = tampered_artifact_path;
    let refused = run_split_collective_worker(
        &task_path,
        &material_path,
        &context_path,
        &config_path,
        &worker_dir.path("tampered-artifact.bundle"),
        &tampered_files,
    );
    assert!(!refused.status.success());

    let mut reordered_files = party_files.clone();
    reordered_files.swap(0, 1);
    let refused = run_split_collective_worker(
        &task_path,
        &material_path,
        &context_path,
        &config_path,
        &worker_dir.path("reordered-parties.bundle"),
        &reordered_files,
    );
    assert!(!refused.status.success());

    let bundle_path = worker_dir.path("decision.bundle");
    let produced = run_split_collective_worker(
        &task_path,
        &material_path,
        &context_path,
        &config_path,
        &bundle_path,
        &party_files,
    );
    assert!(
        produced.status.success(),
        "{}",
        String::from_utf8_lossy(&produced.stderr)
    );
    let process_output = format!(
        "{}{}",
        String::from_utf8_lossy(&produced.stdout),
        String::from_utf8_lossy(&produced.stderr)
    );
    assert!(!process_output.contains(&"ec".repeat(32)));
    assert!(!process_output.contains(&"31".repeat(32)));
    let signer_secret_hex = decision_keys[0]
        .to_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert!(!process_output.contains(&signer_secret_hex));
    let bundle_wire = fs::read(&bundle_path).unwrap();
    let bundle = CollectiveDecisionBundle::from_wire_bytes(&bundle_wire).unwrap();
    assert_eq!(&bundle_wire[..8], b"DBCDv001");
    assert!(bundle.receipt().claim.equal);
    assert_eq!(bundle.receipt().claim.session_nonce, task_digest);
    let mut trailing = bundle_wire.clone();
    trailing.push(0);
    assert!(CollectiveDecisionBundle::from_wire_bytes(&trailing).is_err());

    let committed_receipt = offering
        .invoke_binary_operation(
            &mut game,
            DARK_AMM_COLLECTIVE_COMMIT_OPERATION,
            &bundle_wire,
            stranger,
        )
        .expect_err("another frontend actor cannot finish the stager's candidate");
    assert!(committed_receipt.to_string().contains("staged"));
    assert!(game.has_pending_candidate());

    let committed_receipt = offering
        .invoke_binary_operation(
            &mut game,
            DARK_AMM_COLLECTIVE_COMMIT_OPERATION,
            &bundle_wire,
            actor,
        )
        .unwrap();
    assert_eq!(
        committed_receipt.operation,
        DARK_AMM_COLLECTIVE_COMMIT_OPERATION
    );
    assert_eq!(game.committed_swaps(), 1);
    assert!(!game.has_pending_candidate());
    assert!(offering.binary_artifacts(&game).is_empty());
    let report = offering.verify(&game);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 4);
}
