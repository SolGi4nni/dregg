//! fhIR exact-QP certificate -> executor-enforced raid allocation.
//!
//! This is the deliberately small, non-Automatafl mechanics weld for the optimizer stack:
//!
//! 1. a two-raider resource-allocation policy is authored as an fhIR `Portfolio` QP;
//! 2. an external worker returns only a canonical `FHQPB001` artifact;
//! 3. a custom witnessed-predicate verifier independently recompiles the policy and replays the
//!    artifact's exact SDD/PSD admission, complete `(P,q,A,l,u)` binding, and exact-zero KKT check;
//! 4. the cell commits one claim over the full QP, exact objective value, chosen coordinate, and
//!    ordered game roster; its program reads the *actual post-state* carrier slot and admits the
//!    ordinary `SetField` turn iff it names that claim's certificate-derived raider.
//!
//! No solver report or host-selected winner is authority.  The positive pole commits a meaningful
//! game outcome (raider B receives the one-copy relic-carrier assignment); a wrong assignment,
//! objective/roster substitution, corrupted certificate, and a valid certificate for the same `P`
//! but a different `q` all roll back through `TurnExecutor`.
//!
//! Honest boundary: `FHQPB001` is the native exact fixed-point checker/capability, not a STARK.
//! The fixture's coefficients are exact integers at the canonical scale, so no source-f64 rounding
//! error is exercised here.  The general source-f64 -> scale-9 refinement and the Rust checker ->
//! Lean `Market.QpCertificateBundle` correspondence remain named residuals; this test neither
//! hides nor discharges them.

use std::sync::Arc;

use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, InputRef, Ledger, Permissions, PredicateInput,
    ProvingSystemId, StateConstraint, VerifierFingerprint, VkComponents, WitnessedPredicate,
    WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    WitnessedPredicateVerifier, canonical_vk_v2, field_from_u64,
};
use dregg_turn::action::WitnessBlob;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnExecutor,
};
use fhegg_solver::qp_exact::CertQpExact;
use fhir::ast::{MatrixData, Product, ProductBody};
use fhir::compile::QP_CERT_EXACT_SCALE;
use fhir::{
    Compiled, ConvexProgram, ExactQpCertificateBundle, ExactQpObjectiveValue,
    VerifiedRosterAllocationClaim, compile, roster_allocation_claim_commitment,
    verify_zero_kkt_roster_allocation_claim,
};

const RELIC_CARRIER_SLOT: usize = 0;
const RAIDER_A: u64 = 1;
const RAIDER_B: u64 = 2;
const RAID_ROSTER: [u64; 2] = [RAIDER_A, RAIDER_B];

/// The independently authored public policy.  `x` distributes one indivisible-for-this-mechanic
/// carrier assignment over two candidates (`sum x = 1`, `0 <= x_i <= 1`).  Identity covariance is
/// a fatigue/concentration penalty and `mu` is the public readiness score.  With raider B rewarded,
/// the unique optimum is `x = [0,1]`; swapping `mu` leaves `P` unchanged but changes the authorized
/// program and winner, which supplies the program-substitution tooth below.
fn raid_policy(rewarded_raider: usize) -> Product {
    raid_policy_with_reward(rewarded_raider, 2.0)
}

/// The same game policy with an explicit public readiness reward.  Keeping this
/// authoring hook lets the hostile tests substitute an objective that selects
/// the SAME raider with a different score: output equality must not be mistaken
/// for source-program equality.
fn raid_policy_with_reward(rewarded_raider: usize, reward: f64) -> Product {
    let mu = match rewarded_raider {
        0 => vec![reward, 0.0],
        1 => vec![0.0, reward],
        other => panic!("the two-raider policy has no candidate {other}"),
    };
    Product::infer(
        format!("first-flame-relic-carrier-raider-{rewarded_raider}-reward-{reward}"),
        ProductBody::Portfolio {
            cov: MatrixData::public(2, 2, vec![1.0, 0.0, 0.0, 1.0]),
            mu,
            lambda: 1.0,
            w_max: 1.0,
        },
    )
}

/// Produce the worker artifact without running ADMM.  The worker is untrusted in the integration:
/// the relying-party verifier below decodes and rechecks this object from bytes.  Constructing the
/// exact known solution keeps the test fast and makes every numeric residual literally zero.
fn exact_worker_artifact(compiled: &Compiled, rewarded_raider: usize) -> Vec<u8> {
    let ConvexProgram::Qp(problem) = &compiled.program else {
        panic!("raid allocation policy must compile to QP")
    };
    let scale = 10_i128.pow(QP_CERT_EXACT_SCALE);
    let lift = |values: &[f64]| {
        values
            .iter()
            .map(|value| (value * scale as f64).round() as i128)
            .collect::<Vec<_>>()
    };

    let p = lift(&problem.p);
    let q = lift(&problem.q);
    let a = lift(&problem.a);
    let l = lift(&problem.l);
    let u = lift(&problem.u);

    let mut x = vec![0_i128; 2];
    x[rewarded_raider] = scale;
    // OSQP-form rows are [budget equality, box(A), box(B)]. The equality dual is free and fixed
    // to zero. At the selected upper bound, derive the exact box dual from the compiled P and q
    // instead of trusting the fixture's source-level reward constant.
    let mut y = vec![0_i128; 3];
    y[1 + rewarded_raider] = p[rewarded_raider * problem.n + rewarded_raider]
        .checked_add(q[rewarded_raider])
        .and_then(i128::checked_neg)
        .expect("fixture upper-bound dual is in exact range");

    let exact = CertQpExact {
        n: problem.n,
        mc: problem.mc,
        scale: QP_CERT_EXACT_SCALE,
        p,
        q,
        a,
        l,
        u,
        x,
        y,
        epsilon: 0,
    };
    let report = exact.check();
    assert_eq!(report.prim_res, Some(0), "fixture primal residual");
    assert_eq!(report.dual_res, Some(0), "fixture stationarity residual");
    assert_eq!(report.normal_res, Some(0), "fixture projection residual");

    let admission = compiled
        .exact_sdd_psd_certificate
        .clone()
        .expect("fhIR QP carries the exact SDD/PSD admission witness");
    ExactQpCertificateBundle::new(admission, exact)
        .expect("fixture has exact-zero KKT over the admitted matrix")
        .to_wire_bytes()
        .expect("FHQPB001 has a canonical bounded encoding")
}

struct RaidAllocationVerifier {
    vk_hash: [u8; 32],
    compiled: Compiled,
    program_digest: [u8; 32],
    roster: [u64; 2],
}

impl RaidAllocationVerifier {
    fn reject(&self, reason: impl Into<String>) -> WitnessedPredicateError {
        WitnessedPredicateError::Rejected {
            kind_name: "fhIR-exact-raid-allocation",
            reason: reason.into(),
        }
    }
}

impl WitnessedPredicateVerifier for RaidAllocationVerifier {
    fn name(&self) -> &'static str {
        "fhIR-exact-raid-allocation"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let claim =
            verify_zero_kkt_roster_allocation_claim(&self.compiled, proof_bytes, &self.roster)
                .map_err(|error| self.reject(format!("FHQPB001 refused: {error}")))?;
        if claim.program_digest() != self.program_digest {
            return Err(self.reject("certificate does not name this exact fhIR program"));
        }

        let PredicateInput::Slot(actual_carrier) = input else {
            return Err(WitnessedPredicateError::InputShapeMismatch {
                kind_name: "fhIR-exact-raid-allocation",
                expected: "post-state Slot",
                actual: "non-Slot",
            });
        };
        if claim.roster() != self.roster.as_slice()
            || claim.objective().scale_digits() != QP_CERT_EXACT_SCALE * 3
        {
            return Err(self.reject("derived allocation does not name this raid policy"));
        }
        if claim.commitment() != *commitment {
            return Err(self.reject(
                "cell claim does not bind this allocation, exact objective, and raid roster",
            ));
        }
        let winner = claim.winner();
        if actual_carrier.as_slice() != field_from_u64(winner).as_slice() {
            return Err(self.reject(format!(
                "post-state assigns relic carrier {:?}, certificate authorizes raider {winner}",
                actual_carrier
            )));
        }
        Ok(())
    }
}

#[derive(Clone)]
struct RaidFixture {
    compiled: Compiled,
    artifact: Vec<u8>,
    program_digest: [u8; 32],
    claim: VerifiedRosterAllocationClaim,
    claim_commitment: [u8; 32],
    roster: [u64; 2],
    vk_hash: [u8; 32],
}

fn fixture(rewarded_raider: usize) -> RaidFixture {
    let compiled =
        compile(&raid_policy(rewarded_raider)).expect("public raid QP is fhIR-admissible");
    fixture_from_compiled(compiled, rewarded_raider, RAID_ROSTER)
}

fn fixture_with_reward(rewarded_raider: usize, reward: f64) -> RaidFixture {
    let compiled = compile(&raid_policy_with_reward(rewarded_raider, reward))
        .expect("public raid QP is fhIR-admissible");
    fixture_from_compiled(compiled, rewarded_raider, RAID_ROSTER)
}

fn fixture_with_roster(rewarded_raider: usize, roster: [u64; 2]) -> RaidFixture {
    let compiled =
        compile(&raid_policy(rewarded_raider)).expect("public raid QP is fhIR-admissible");
    fixture_from_compiled(compiled, rewarded_raider, roster)
}

fn fixture_from_compiled(
    compiled: Compiled,
    rewarded_raider: usize,
    roster: [u64; 2],
) -> RaidFixture {
    assert!(roster[0] != 0 && roster[1] != 0 && roster[0] != roster[1]);
    let artifact = exact_worker_artifact(&compiled, rewarded_raider);
    let claim = verify_zero_kkt_roster_allocation_claim(&compiled, &artifact, &roster)
        .expect("fixture crosses the same hostile-byte boundary as the executor verifier");
    let program_digest = claim.program_digest();
    assert_eq!(claim.winner_index(), rewarded_raider);
    let claim_commitment = claim.commitment();

    // v2 identity binds the frozen policy, game roster, checker family, verifier implementation,
    // and proof system. WitnessedPredicateRegistry is the existing open custom-VK dispatch surface.
    let mut program_bytes = b"first-flame/relic-carrier/fhir-qp-v1".to_vec();
    program_bytes.extend_from_slice(&program_digest);
    program_bytes.extend_from_slice(&(roster.len() as u64).to_be_bytes());
    for raider in roster {
        program_bytes.extend_from_slice(&raider.to_be_bytes());
    }
    let air_fingerprint = *blake3::hash(b"FHQPB001/exact-SDD/exact-zero-KKT").as_bytes();
    let verifier_fingerprint = VerifierFingerprint::SourceHash(
        *blake3::hash(
            b"RaidAllocationVerifier/bind-one-hot-objective-roster-and-post-state-slot/v2",
        )
        .as_bytes(),
    );
    let proving_system_id = ProvingSystemId::Custom {
        id: "fhir-fhqp-bundle-native-v1",
    };
    let vk_hash = canonical_vk_v2(&VkComponents {
        program_bytes: &program_bytes,
        air_fingerprint,
        verifier_fingerprint,
        proving_system_id,
    });

    RaidFixture {
        compiled,
        artifact,
        program_digest,
        claim,
        claim_commitment,
        roster,
        vk_hash,
    }
}

/// A canonical, internally valid bounded-residual bundle carrying the SAME exact
/// optimum but a positive tolerance. It is legitimate approximate evidence and
/// therefore the strongest substitution for the game's exact-optimality boundary:
/// checksum corruption is not what makes this object refuse.
fn positive_tolerance_artifact(exact_wire: &[u8]) -> Vec<u8> {
    let exact = ExactQpCertificateBundle::from_wire_bytes(exact_wire)
        .expect("the exact worker artifact decodes");
    let mut approximate_kkt = exact.kkt().clone();
    approximate_kkt.epsilon = 1;
    ExactQpCertificateBundle::new(exact.admission().clone(), approximate_kkt)
        .expect("zero residuals remain valid under a positive tolerance")
        .to_wire_bytes()
        .expect("the approximate substitution has canonical FHQPB001 encoding")
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn allocation_cell(fixture: &RaidFixture, seed: u8) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    public_key[31] = seed.wrapping_mul(41);
    let mut cell = Cell::with_balance(public_key, [0u8; 32], 0);
    cell.permissions = open_permissions();
    cell.program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::custom(
            fixture.vk_hash,
            fixture.claim_commitment,
            InputRef::Slot {
                index: RELIC_CARRIER_SLOT as u8,
            },
            0,
        ),
    }]);
    cell
}

fn executor_for(fixture: RaidFixture) -> TurnExecutor {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        fixture.vk_hash,
        Arc::new(RaidAllocationVerifier {
            vk_hash: fixture.vk_hash,
            compiled: fixture.compiled,
            program_digest: fixture.program_digest,
            roster: fixture.roster,
        }),
    );
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_witnessed_registry(registry);
    executor
}

fn assignment_turn(cell: CellId, carrier: u64, artifact: Vec<u8>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: cell,
        method: *blake3::hash(b"assign-first-flame-relic-carrier").as_bytes(),
        args: vec![field_from_u64(carrier)],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell,
            index: RELIC_CARRIER_SLOT as u64,
            value: field_from_u64(carrier),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![WitnessBlob::proof(artifact)],
    });
    Turn {
        agent: cell,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

fn run(fixture: RaidFixture, carrier: u64, artifact: Vec<u8>) -> (bool, [u8; 32]) {
    let cell_fixture = fixture.clone();
    run_with_executor(&cell_fixture, fixture, carrier, artifact)
}

fn run_with_executor(
    cell_fixture: &RaidFixture,
    verifier_fixture: RaidFixture,
    carrier: u64,
    artifact: Vec<u8>,
) -> (bool, [u8; 32]) {
    let cell = allocation_cell(cell_fixture, carrier as u8 + 10);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger
        .insert_cell(cell)
        .expect("insert raid allocation cell");
    let turn = assignment_turn(cell_id, carrier, artifact);
    let committed = executor_for(verifier_fixture)
        .execute(&turn, &mut ledger)
        .is_committed();
    let post = ledger
        .get(&cell_id)
        .expect("a refused turn rolls back; neither pole destroys the cell")
        .state
        .fields[RELIC_CARRIER_SLOT];
    (committed, post)
}

#[test]
fn exact_fhir_certificate_commits_the_certificate_selected_raid_assignment() {
    let fixture = fixture(1);
    assert_eq!(fixture.claim.roster(), RAID_ROSTER.as_slice());
    assert_eq!(fixture.claim.winner_index(), 1);
    let objective = fixture.claim.objective();
    let objective_denominator = 10_i128.pow(objective.scale_digits());
    assert_eq!(
        objective.twice_numerator(),
        -3 * objective_denominator,
        "the bound exact objective is twice (-1.5), not a solver report"
    );
    let artifact = fixture.artifact.clone();
    let (committed, post) = run(fixture, RAIDER_B, artifact);
    assert!(committed, "the exact certified allocation must land");
    assert_eq!(
        post,
        field_from_u64(RAIDER_B),
        "the real cell now records raider B as the one-copy relic carrier"
    );
}

#[test]
fn host_cannot_spend_a_valid_certificate_on_a_different_raid_assignment() {
    let fixture = fixture(1);
    let artifact = fixture.artifact.clone();
    let (committed, post) = run(fixture, RAIDER_A, artifact);
    assert!(
        !committed,
        "the host-selected loser must not receive the relic"
    );
    assert_eq!(
        post,
        field_from_u64(0),
        "predicate refusal must roll the allocation slot back atomically"
    );
}

#[test]
fn corrupted_or_different_program_certificates_cannot_authorize_the_outcome() {
    let corrupt_fixture = fixture(1);

    let mut corrupted = corrupt_fixture.artifact.clone();
    let byte = corrupted
        .get_mut(32)
        .expect("FHQPB001 fixture is longer than its header");
    *byte ^= 1;
    let (corrupt_committed, corrupt_post) = run(corrupt_fixture, RAIDER_B, corrupted);
    assert!(!corrupt_committed, "checksum-validity failure must refuse");
    assert_eq!(corrupt_post, field_from_u64(0));

    // Same identity PSD matrix and feasible set, different linear objective: this artifact is
    // genuinely exact-zero-valid for the alternate policy, but full compiled-program binding must
    // prevent it from authorizing the original cell.
    let original = fixture(1);
    let alternate = fixture(0);
    let (substituted, substituted_post) = run(original, RAIDER_A, alternate.artifact);
    assert!(
        !substituted,
        "same-P/different-q optimizer evidence must not cross the source-program boundary"
    );
    assert_eq!(substituted_post, field_from_u64(0));
}

#[test]
fn same_winner_with_a_different_objective_cannot_reuse_the_cell_claim() {
    let original = fixture_with_reward(1, 2.0);
    let alternate_objective = fixture_with_reward(1, 3.0);
    assert_eq!(
        original.claim.winner_index(),
        alternate_objective.claim.winner_index()
    );
    assert_ne!(
        original.claim.objective(),
        alternate_objective.claim.objective(),
        "the hostile policy keeps the winner but changes its exact achieved objective"
    );

    let artifact = alternate_objective.artifact;
    let (committed, post) = run(original, RAIDER_B, artifact);
    assert!(
        !committed,
        "output equality cannot substitute a different objective/program"
    );
    assert_eq!(post, field_from_u64(0));
}

#[test]
fn objective_and_ordered_game_roster_are_part_of_the_cell_claim_and_vk() {
    let trusted = fixture(1);
    let artifact = trusted.artifact.clone();

    let mut wrong_objective_cell = trusted.clone();
    let objective = trusted.claim.objective();
    let forged_objective = ExactQpObjectiveValue::from_twice_scaled(
        objective
            .twice_numerator()
            .checked_add(1)
            .expect("fixture objective has room for a one-unit forgery"),
        objective.scale_digits(),
    );
    wrong_objective_cell.claim_commitment = roster_allocation_claim_commitment(
        trusted.claim.program_digest(),
        trusted.claim.roster(),
        trusted.claim.winner_index(),
        forged_objective,
    )
    .expect("the forged public objective image has valid claim shape");
    let (objective_committed, objective_post) = run_with_executor(
        &wrong_objective_cell,
        trusted.clone(),
        RAIDER_B,
        artifact.clone(),
    );
    assert!(
        !objective_committed,
        "a cell claim with the right winner but a forged objective must refuse"
    );
    assert_eq!(objective_post, field_from_u64(0));

    let mut wrong_roster_cell = trusted.clone();
    let reordered_roster = [RAIDER_B, RAIDER_A];
    wrong_roster_cell.claim_commitment = roster_allocation_claim_commitment(
        trusted.claim.program_digest(),
        &reordered_roster,
        trusted.claim.winner_index(),
        trusted.claim.objective(),
    )
    .expect("the reordered public roster image has valid claim shape");
    let (roster_claim_committed, roster_claim_post) = run_with_executor(
        &wrong_roster_cell,
        trusted.clone(),
        RAIDER_B,
        artifact.clone(),
    );
    assert!(
        !roster_claim_committed,
        "reordering the game roster under the same QP must refuse"
    );
    assert_eq!(roster_claim_post, field_from_u64(0));

    let alternate_roster = fixture_with_roster(1, [RAIDER_A, 99]);
    assert_ne!(
        trusted.vk_hash, alternate_roster.vk_hash,
        "the custom verifier identity itself must bind the deployment roster"
    );
    let (roster_vk_committed, roster_vk_post) =
        run_with_executor(&trusted, alternate_roster, RAIDER_B, artifact);
    assert!(
        !roster_vk_committed,
        "a verifier registered for another roster cannot serve this cell"
    );
    assert_eq!(roster_vk_post, field_from_u64(0));
}

#[test]
fn approximate_tolerance_cannot_authorize_the_exact_game_allocation() {
    let fixture = fixture(1);
    let approximate = positive_tolerance_artifact(&fixture.artifact);
    let (committed, post) = run(fixture, RAIDER_B, approximate);
    assert!(
        !committed,
        "positive-tolerance KKT evidence cannot cross the exact game boundary"
    );
    assert_eq!(post, field_from_u64(0));
}
