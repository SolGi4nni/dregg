#![cfg(feature = "dark-amm-game")]

#[path = "../src/dark_amm_collective_worker.rs"]
mod dark_amm_collective_worker;

use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhe::bfv::{Encoding, Plaintext, RelinearizationKey};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::attestation::{AuthenticatedQuorumVerifier, InMemoryReplayGuard};
use fhegg_fhe::bfv_mul::BoundedCiphertext;
use fhegg_fhe::dark_amm::{DarkPool, PrivateAppliedSwap};
use fhegg_fhe::dark_amm_attested::{
    AttestedPrivateCommitError, AttestedPrivateDecisionPolicy, commit_attested_private_decision,
    commit_attested_private_decision_in_context,
};
use fhegg_fhe::decision_attestation::{DecisionAttestationError, ExpectedDecisionContext};
use fhegg_fhe::mpc_party::trusted_dealer_triples;
use fhegg_fhe::threshold::relin::{RelinKeySession, generate_relinearization_key};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use rand::SeedableRng;
use rand::rngs::StdRng;

use dark_amm_collective_worker::{
    CollectiveDecisionTask, CollectiveDecisionTaskContext, CollectiveDecisionTaskError,
    CollectiveDecisionWorkerError, MaskedCollectiveDecisionWorker,
};

const N: usize = 3;
const VALUE_BITS: usize = 19;

struct Fixture {
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    parties: Vec<ThresholdParty>,
    relin: RelinearizationKey,
}

impl Fixture {
    fn new() -> Self {
        let params = BfvParams::fold_set();
        let keygen = KeygenSession::from_seed(N, [0x91; 32]).expect("keygen session");
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
            [0x92; 32],
            Duration::from_secs(30),
        )
        .expect("relinearization session");
        let relin = generate_relinearization_key(&relin_session, &params, &collective, &parties)
            .expect("party-owned relinearization key");
        Self {
            params,
            keygen,
            collective,
            parties,
            relin,
        }
    }

    fn pool(&self) -> DarkPool {
        let mut pool = DarkPool::init(
            self.params.arc(),
            &self.collective.pk,
            &self.relin,
            100,
            900,
            400,
            1_000,
            &mut rand_09::rng(),
        )
        .expect("collective-key pool");
        pool.strip_lp_view();
        pool
    }

    fn encrypted_amount(&self, value: u64) -> BoundedCiphertext {
        let plaintext = Plaintext::try_encode(&[value], Encoding::simd(), self.params.arc())
            .expect("amount encoding");
        let ciphertext = self
            .collective
            .pk
            .try_encrypt(&plaintext, &mut rand_09::rng())
            .expect("collective amount encryption");
        BoundedCiphertext::new(ciphertext, value)
    }

    fn candidate(&self, pool: &DarkPool, dy: u64) -> PrivateAppliedSwap {
        pool.try_private_swap_proposed(&self.encrypted_amount(50), &self.encrypted_amount(dy))
            .expect("encrypted private candidate")
    }
}

fn decision_authority() -> (Vec<SigningKey>, AuthenticatedQuorumVerifier) {
    let keys = vec![
        SigningKey::from_bytes(&[0xa1; 32]),
        SigningKey::from_bytes(&[0xa2; 32]),
        SigningKey::from_bytes(&[0xa3; 32]),
    ];
    let verifier = AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("2-of-3 authority");
    (keys, verifier)
}

#[test]
fn worker_refuses_roster_range_and_preprocessing_drift_before_masking() {
    let mut fixture = Fixture::new();
    fixture.parties.swap(0, 1);
    assert!(matches!(
        MaskedCollectiveDecisionWorker::new(
            &fixture.params,
            &fixture.keygen,
            &fixture.collective,
            &fixture.parties,
            VALUE_BITS,
            Duration::from_secs(5),
        ),
        Err(CollectiveDecisionWorkerError::InvalidConfiguration(
            "custodians must be in exact key-generation party order"
        ))
    ));
    fixture.parties.swap(0, 1);

    let pool = fixture.pool();
    let candidate = fixture.candidate(&pool, 300);
    let worker = MaskedCollectiveDecisionWorker::new(
        &fixture.params,
        &fixture.keygen,
        &fixture.collective,
        &fixture.parties,
        VALUE_BITS,
        Duration::from_secs(5),
    )
    .expect("valid worker");
    assert_eq!(worker.n_parties(), N);
    assert!(matches!(
        worker.decide_with_triples(&candidate, 90_000, Vec::new()),
        Err(CollectiveDecisionWorkerError::PreprocessingShape { have: 0, need: N })
    ));
    assert!(matches!(
        worker.decide_with_triples(&candidate, 1 << VALUE_BITS, Vec::new()),
        Err(CollectiveDecisionWorkerError::PublicTargetOutOfRange)
    ));

    let off_invariant = fixture.candidate(&pool, 301);
    let off_session = worker
        .decision_session(&off_invariant)
        .expect("off-invariant preprocessing session");
    let mut test_dealer = StdRng::seed_from_u64(0x91_00_01);
    let off_triples = trusted_dealer_triples(&off_session, &mut test_dealer)
        .expect("shape-only test preprocessing");
    let refused = worker
        .decide_with_triples(&off_invariant, 90_000, off_triples)
        .expect("masked equality returns a refusal bit");
    assert!(!refused.is_equal());
    assert!(refused.transcript().is_reveal_only(refused.session()));
    let (_, verifier) = decision_authority();
    assert!(
        !refused
            .draft_receipt(&verifier)
            .expect("canonical refusal claim")
            .claim
            .equal
    );
}

#[test]
fn masked_threshold_worker_emits_only_attested_bit_and_commits_real_candidate() {
    // Neither this integration target nor the reusable worker imports
    // `SecretKey` or calls `threshold::combine`. The only threshold opening is
    // performed by `ThresholdMaskedCiphertext::open_framed` over the padded
    // invariant, while pad removal stays inside each party thread.
    let fixture = Fixture::new();
    let mut pool = fixture.pool();
    let committed_material = pool
        .public_host_material()
        .expect("canonical committed material");
    let before_x = pool.reserve_cts().ct_x.ct.to_bytes();
    let before_y = pool.reserve_cts().ct_y.ct.to_bytes();
    let candidate = fixture.candidate(&pool, 300);
    let candidate_nonce = candidate.decision_session_nonce();
    let task_context = CollectiveDecisionTaskContext {
        hosted_session: [0xb1; 32],
        sequence: 7,
        committed_root: [17, 18, 19, 20, 21, 22, 23, 24],
        same_opening_claim_digest: [0xb2; 32],
    };
    let task = CollectiveDecisionTask::from_candidate(
        task_context,
        &committed_material,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective,
        VALUE_BITS,
        &candidate,
    )
    .expect("strict public decision task");
    assert_eq!(task.context(), task_context);
    assert_eq!(task.value_bits(), VALUE_BITS as u64);
    assert_eq!(task.candidate_nonce(), candidate_nonce);
    assert_eq!(task.candidate_carrier().candidate_nonce(), candidate_nonce);
    assert!(task.matches_candidate(&candidate));
    let task_nonce = task.attestation_nonce().expect("task digest");
    assert_ne!(task_nonce, candidate_nonce);

    let task_wire = task.to_wire_bytes().expect("strict task wire");
    let roundtrip = CollectiveDecisionTask::from_wire_bytes(
        &task_wire,
        &committed_material,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective,
        VALUE_BITS,
    )
    .expect("task wire roundtrip");
    assert_eq!(roundtrip, task);
    assert_eq!(roundtrip.attestation_nonce().unwrap(), task_nonce);
    for end in [0usize, 1, 7, task_wire.len() - 33, task_wire.len() - 1] {
        assert!(
            CollectiveDecisionTask::from_wire_bytes(
                &task_wire[..end],
                &committed_material,
                &fixture.params,
                &fixture.keygen,
                &fixture.collective,
                VALUE_BITS,
            )
            .is_err()
        );
    }
    let mut trailing = task_wire.clone();
    trailing.push(0);
    assert!(
        CollectiveDecisionTask::from_wire_bytes(
            &trailing,
            &committed_material,
            &fixture.params,
            &fixture.keygen,
            &fixture.collective,
            VALUE_BITS,
        )
        .is_err()
    );
    let mut corrupt = task_wire.clone();
    corrupt[48] ^= 1;
    assert!(matches!(
        CollectiveDecisionTask::from_wire_bytes(
            &corrupt,
            &committed_material,
            &fixture.params,
            &fixture.keygen,
            &fixture.collective,
            VALUE_BITS,
        ),
        Err(CollectiveDecisionTaskError::InvalidWire(
            "checksum mismatch"
        ))
    ));
    let wrong_keygen = KeygenSession::from_seed(N, [0xbf; 32]).expect("other DKG identity");
    assert!(matches!(
        CollectiveDecisionTask::from_wire_bytes(
            &task_wire,
            &committed_material,
            &fixture.params,
            &wrong_keygen,
            &fixture.collective,
            VALUE_BITS,
        ),
        Err(CollectiveDecisionTaskError::KeygenMismatch)
    ));
    let different_material = fixture
        .pool()
        .public_host_material()
        .expect("different committed ciphertext state");
    assert!(matches!(
        CollectiveDecisionTask::from_wire_bytes(
            &task_wire,
            &different_material,
            &fixture.params,
            &fixture.keygen,
            &fixture.collective,
            VALUE_BITS,
        ),
        Err(CollectiveDecisionTaskError::CommittedMaterialMismatch)
    ));

    let altered_contexts = [
        CollectiveDecisionTaskContext {
            hosted_session: [0xb3; 32],
            ..task_context
        },
        CollectiveDecisionTaskContext {
            sequence: 8,
            ..task_context
        },
        CollectiveDecisionTaskContext {
            committed_root: [31, 32, 33, 34, 35, 36, 37, 38],
            ..task_context
        },
        CollectiveDecisionTaskContext {
            same_opening_claim_digest: [0xb4; 32],
            ..task_context
        },
    ];
    for altered in &altered_contexts {
        let altered_task = CollectiveDecisionTask::from_candidate(
            *altered,
            &committed_material,
            &fixture.params,
            &fixture.keygen,
            &fixture.collective,
            VALUE_BITS,
            &candidate,
        )
        .expect("same candidate in an altered hosted context");
        assert_ne!(altered_task.attestation_nonce().unwrap(), task_nonce);
        assert!(altered_task.validate_context(task_context).is_err());
    }
    let rerandomized_candidate = fixture.candidate(&pool, 300);
    let rerandomized_task = CollectiveDecisionTask::from_candidate(
        task_context,
        &committed_material,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective,
        VALUE_BITS,
        &rerandomized_candidate,
    )
    .expect("same plaintext quote with a distinct encrypted carrier");
    assert_ne!(rerandomized_task.candidate_nonce(), candidate_nonce);
    assert_ne!(rerandomized_task.attestation_nonce().unwrap(), task_nonce);
    assert!(!task.matches_candidate(&rerandomized_candidate));
    let cross_context = altered_contexts[0];
    let cross_task = CollectiveDecisionTask::from_candidate(
        cross_context,
        &committed_material,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective,
        VALUE_BITS,
        &candidate,
    )
    .expect("same candidate in another table/round");
    assert_ne!(cross_task.attestation_nonce().unwrap(), task_nonce);
    assert!(task.validate_context(cross_context).is_err());

    let worker = MaskedCollectiveDecisionWorker::new(
        &fixture.params,
        &fixture.keygen,
        &fixture.collective,
        &fixture.parties,
        VALUE_BITS,
        Duration::from_secs(5),
    )
    .expect("valid worker");
    assert!(matches!(
        worker.decision_session_for_task(&cross_task, &committed_material, task_context),
        Err(CollectiveDecisionWorkerError::Task(
            CollectiveDecisionTaskError::InvalidContext(_)
        ))
    ));
    let public_session = worker
        .decision_session_for_task(&task, &committed_material, task_context)
        .expect("task-bound preprocessing session");
    assert_eq!(public_session.nonce(), task_nonce);
    let mut test_dealer = StdRng::seed_from_u64(0x91_92_93);
    let triples = trusted_dealer_triples(&public_session, &mut test_dealer)
        .expect("shape-only test preprocessing");
    let decision = worker
        .decide_task_with_triples(&task, &committed_material, task_context, triples)
        .expect("no-secret masked equality");
    assert!(decision.is_equal());
    assert_eq!(decision.session().nonce(), task_nonce);
    assert!(decision.transcript().is_reveal_only(decision.session()));

    let (keys, verifier) = decision_authority();
    let draft = decision
        .draft_receipt(&verifier)
        .expect("canonical unsigned decision claim");
    let signatures = [0usize, 2]
        .into_iter()
        .map(|party| {
            verifier
                .sign_claim(&draft.claim_digest(), party, &keys[party])
                .expect("independent custodian endorsement")
        })
        .collect::<Vec<_>>();
    let receipt = decision
        .assemble_attested_receipt(&verifier, &signatures)
        .expect("strict FHDAR receipt");
    assert_eq!(receipt.claim.session_nonce, task_nonce);
    assert!(receipt.claim.equal);
    let cross_session = worker
        .decision_session_for_task(&cross_task, &committed_material, cross_context)
        .expect("other hosted session task shape");
    assert_eq!(
        receipt.verify_binding(&ExpectedDecisionContext {
            session: &cross_session,
            roster_digest: verifier.roster_digest(),
            transcript: decision.transcript(),
            equal: true,
        }),
        Err(DecisionAttestationError::BindingMismatch)
    );

    let policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
        verifier,
    )
    .expect("host decision policy");
    assert!(matches!(
        commit_attested_private_decision(
            &mut pool,
            &candidate,
            &policy,
            decision.transcript(),
            &receipt,
            &mut InMemoryReplayGuard::default(),
        ),
        Err(AttestedPrivateCommitError::Attestation(
            DecisionAttestationError::BindingMismatch
        ))
    ));
    commit_attested_private_decision_in_context(
        &mut pool,
        &candidate,
        task_nonce,
        &policy,
        decision.transcript(),
        &receipt,
        &mut InMemoryReplayGuard::default(),
    )
    .expect("attested bit installs encrypted candidate");
    assert_ne!(pool.reserve_cts().ct_x.ct.to_bytes(), before_x);
    assert_ne!(pool.reserve_cts().ct_y.ct.to_bytes(), before_y);

    let short_verifier = AuthenticatedQuorumVerifier::new(
        keys[..2]
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("different 2-party roster");
    assert!(matches!(
        decision.draft_receipt(&short_verifier),
        Err(CollectiveDecisionWorkerError::RosterMismatch { have: 2, need: N })
    ));
}
