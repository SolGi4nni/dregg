//! Offline producer/operator utility for the hosted encrypted Dark Pool demo.
//!
//! `keygen` writes secret deployment custody; `public` derives a distributable
//! session context; `private-init` creates an owner-only hidden state opening;
//! and `private-swap` proves + encrypts one transition into an atomic upload
//! bundle without requiring caller-authored Rust. After acceptance,
//! `proved-cursor` advances the public context to the bundle's statement while
//! the bundle's next private state becomes the producer's new custody object.

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use dregg_circuit_prove::dark_amm_private::{
    PublicStatement as PrivateAmmPublicStatement, prove_zk, sample_commitment_blind,
};
use dreggnet_market::dark_amm_collective::CollectiveDecisionBundle;
use dreggnet_market::dark_amm_collective_worker::{
    CollectiveDecisionTask, CollectiveDecisionTaskContext, MAX_COLLECTIVE_DECISION_TASK_BYTES,
    MaskedCollectiveDecisionWorker,
};
use dreggnet_market::dark_amm_game::{
    DarkAmmGameOffering, DarkAmmHostKeyMaterial, DarkAmmPrivateState, DarkAmmPrivateSwapAuthority,
    DarkAmmPublicSession, ProvedEncryptedSwapRequest, private_amm_statement_from_wire,
    private_amm_statement_to_wire, produce_encrypted_swap, produce_proved_encrypted_swap,
    produce_proved_encrypted_swap_seeded,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::amm_same_opening::{
    MAX_AUTHORITY_PARTIES, SAME_OPENING_ENDORSEMENT_WIRE_LEN, Tier1SameOpeningAuthority,
    Tier1SameOpeningEndorsement,
};
use fhegg_fhe::attestation::{AuthenticatedQuorumVerifier, PartyClaimSignature};
use fhegg_fhe::dark_amm::{DarkPoolPublicHostMaterial, MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES};
use fhegg_fhe::mpc_party::trusted_dealer_triples;
use fhegg_fhe::threshold::{BfvParams, KeygenCoordinator, KeygenSession, ThresholdParty};
use rand::SeedableRng;
use rand::rngs::StdRng;
use rand_09::RngCore;

const COLLECTIVE_WORKER_CONFIG_MAGIC: &[u8; 8] = b"DBWCv001";
const COLLECTIVE_WORKER_CONTEXT_MAGIC: &[u8; 8] = b"DBCTX001";
const COLLECTIVE_WORKER_CUSTODY_MAGIC: &[u8; 8] = b"DBCKv001";
const COLLECTIVE_WORKER_CHECKSUM_DOMAIN: &str =
    "dregg-dark-amm-collective-worker-input-checksum-v1";
const MAX_COLLECTIVE_WORKER_PARTIES: usize = MAX_AUTHORITY_PARTIES;
const MAX_COLLECTIVE_WORKER_CONFIG_BYTES: u64 = 1024;
const MAX_COLLECTIVE_WORKER_CONTEXT_BYTES: u64 = 144;
const MAX_COLLECTIVE_WORKER_CUSTODY_BYTES: u64 = 2048;

fn main() {
    if let Err(error) = run() {
        eprintln!("dark-amm-tool: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match args.as_slice() {
        [command, output] if command == "keygen" => {
            let mut rng = rand_09::rng();
            let keys = DarkAmmHostKeyMaterial::generate(&mut rng).map_err(|e| e.to_string())?;
            let mut key_wire = keys.to_secret_wire_bytes();
            let result = write_new(Path::new(output), &key_wire, true);
            key_wire.fill(0);
            result?;
            println!("created protected Dark Pool deployment key: {output}");
            Ok(())
        }
        [command, key_file, session_seed, output] if command == "public" => {
            let keys = read_host_key(Path::new(key_file))?;
            let seed = parse_u64(session_seed)?;
            let public = DarkAmmGameOffering::demo(keys)
                .public_session_for_seed(seed)
                .map_err(|e| e.to_string())?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created public Dark Pool producer context: {output} (session {}, receipt session {}, sequence {})",
                hex32(&public.session_id()),
                public.private_amm_receipt_session(),
                public.next_sequence()
            );
            Ok(())
        }
        [command, key_file, session_seed, statement_file, output]
            if command == "public-proved" =>
        {
            let keys = read_host_key(Path::new(key_file))?;
            let statement = read_statement(Path::new(statement_file))?;
            let public = DarkAmmGameOffering::demo_proof_required(keys, statement.old_root)
                .map_err(|e| e.to_string())?
                .public_session_for_seed(parse_u64(session_seed)?)
                .map_err(|e| e.to_string())?;
            check_statement_context(&public, statement)?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created proof-required Dark Pool context: {output} (session {}, sequence {})",
                hex32(&public.session_id()),
                public.next_sequence()
            );
            Ok(())
        }
        [command, key_file, session_seed, private_state_file, output]
            if command == "public-private" =>
        {
            let keys = read_host_key(Path::new(key_file))?;
            let state = read_private_state(Path::new(private_state_file))?;
            let public = proof_public_for_seed(keys, parse_u64(session_seed)?, &state)?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created proof-required Dark Pool context from private state: {output} (session {}, root {}, sequence {})",
                hex32(&public.session_id()),
                hex_root(&state.root().map_err(|e| e.to_string())?),
                public.next_sequence()
            );
            Ok(())
        }
        [command, key_file, session_id, output] if command == "public-id" => {
            let keys = read_host_key(Path::new(key_file))?;
            // OfferingHost/web seed rule: BLAKE3(session id), low 8 bytes LE.
            let digest = blake3::hash(session_id.as_bytes());
            let seed = u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap());
            let public = DarkAmmGameOffering::demo(keys)
                .public_session_for_seed(seed)
                .map_err(|e| e.to_string())?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created public Dark Pool producer context: {output} (web session {session_id:?}, binding {}, receipt session {}, sequence {})",
                hex32(&public.session_id()),
                public.private_amm_receipt_session(),
                public.next_sequence()
            );
            Ok(())
        }
        [command, key_file, session_id, statement_file, output]
            if command == "public-id-proved" =>
        {
            let keys = read_host_key(Path::new(key_file))?;
            let statement = read_statement(Path::new(statement_file))?;
            let digest = blake3::hash(session_id.as_bytes());
            let seed = u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap());
            let public = DarkAmmGameOffering::demo_proof_required(keys, statement.old_root)
                .map_err(|e| e.to_string())?
                .public_session_for_seed(seed)
                .map_err(|e| e.to_string())?;
            check_statement_context(&public, statement)?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created proof-required Dark Pool context: {output} (web session {session_id:?}, binding {}, sequence {})",
                hex32(&public.session_id()),
                public.next_sequence()
            );
            Ok(())
        }
        [command, key_file, session_id, private_state_file, output]
            if command == "public-id-private" =>
        {
            let keys = read_host_key(Path::new(key_file))?;
            let state = read_private_state(Path::new(private_state_file))?;
            let public = proof_public_for_seed(keys, seed_for_session_id(session_id), &state)?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created proof-required Dark Pool context from private state: {output} (web session {session_id:?}, binding {}, root {}, sequence {})",
                hex32(&public.session_id()),
                hex_root(&state.root().map_err(|e| e.to_string())?),
                public.next_sequence()
            );
            Ok(())
        }
        [command, public_file, x, y, output] if command == "private-init" => {
            let public = read_public(Path::new(public_file))?;
            let blind = sample_commitment_blind()?;
            let state = DarkAmmPrivateState::try_new(
                &public,
                parse_u16(x)?,
                parse_u16(y)?,
                blind,
            )
            .map_err(|e| e.to_string())?;
            let mut wire = state.to_wire_bytes();
            let result = write_new_atomic(Path::new(output), &wire, true);
            wire.fill(0);
            result?;
            println!(
                "created owner-only Dark Pool private state: {output} (session {}, root {})",
                hex32(&state.session_id()),
                hex_root(&state.root().map_err(|e| e.to_string())?)
            );
            Ok(())
        }
        [command, public_file, dx, dy, dx_bound, dy_bound, output] if command == "swap" => {
            let public_bytes = fs::read(public_file)
                .map_err(|e| format!("cannot read public context {public_file:?}: {e}"))?;
            let public = DarkAmmPublicSession::from_wire_bytes(&public_bytes)
                .map_err(|e| e.to_string())?;
            let mut rng = rand_09::rng();
            let request = produce_encrypted_swap(
                &public,
                parse_u64(dx)?,
                parse_u64(dy)?,
                parse_u64(dx_bound)?,
                parse_u64(dy_bound)?,
                &mut rng,
            )
            .map_err(|e| e.to_string())?;
            write_new(Path::new(output), &request.to_wire_bytes(), false)?;
            println!(
                "created opaque encrypted swap: {output} (session {}, sequence {})",
                hex32(&public.session_id()),
                request.sequence()
            );
            Ok(())
        }
        [
            command,
            public_file,
            statement_file,
            proof_file,
            dx,
            dy,
            dx_bound,
            dy_bound,
            output,
        ] if command == "proved-swap" => {
            let public_bytes = fs::read(public_file)
                .map_err(|e| format!("cannot read public context {public_file:?}: {e}"))?;
            let public = DarkAmmPublicSession::from_wire_bytes(&public_bytes)
                .map_err(|e| e.to_string())?;
            let statement_bytes = fs::read(statement_file)
                .map_err(|e| format!("cannot read receipt statement {statement_file:?}: {e}"))?;
            let statement = private_amm_statement_from_wire(&statement_bytes)
                .map_err(|e| e.to_string())?;
            let proof_bytes = fs::read(proof_file)
                .map_err(|e| format!("cannot read hiding proof {proof_file:?}: {e}"))?;
            let mut rng = rand_09::rng();
            let request = produce_proved_encrypted_swap(
                &public,
                parse_u64(dx)?,
                parse_u64(dy)?,
                parse_u64(dx_bound)?,
                parse_u64(dy_bound)?,
                statement,
                proof_bytes,
                &mut rng,
            )
            .map_err(|e| e.to_string())?;
            write_new(Path::new(output), &request.to_wire_bytes(), false)?;
            println!(
                "created proof-required encrypted swap: {output} (session {}, sequence {})",
                hex32(&public.session_id()),
                request.sequence()
            );
            Ok(())
        }
        [
            command,
            public_file,
            private_state_file,
            dx,
            dy,
            dx_bound,
            dy_bound,
            output_dir,
        ] if command == "private-swap" => {
            let output_dir = Path::new(output_dir);
            ensure_new_bundle_target(output_dir)?;
            let public = read_public(Path::new(public_file))?;
            let state = read_private_state(Path::new(private_state_file))?;
            state
                .validate_for_proof_context(&public)
                .map_err(|e| e.to_string())?;
            let dx = parse_u16(dx)?;
            let dy = parse_u16(dy)?;
            let next_blind = sample_commitment_blind()?;
            let (witness, next_state) = state
                .transition(dx, dy, next_blind)
                .map_err(|e| e.to_string())?;
            let (proof, statement) = prove_zk(state.receipt_session(), &witness)?;
            let proof_bytes = proof.to_postcard()?;
            let mut rng = rand_09::rng();
            let mut dx_encryption_seed = [0u8; 32];
            let mut dy_encryption_seed = [0u8; 32];
            rng.fill_bytes(&mut dx_encryption_seed);
            rng.fill_bytes(&mut dy_encryption_seed);
            let request = produce_proved_encrypted_swap_seeded(
                &public,
                u64::from(dx),
                u64::from(dy),
                parse_u64(dx_bound)?,
                parse_u64(dy_bound)?,
                statement,
                proof_bytes,
                dx_encryption_seed,
                dy_encryption_seed,
            )
            .map_err(|e| e.to_string())?;
            let authority = DarkAmmPrivateSwapAuthority::try_new(
                &public,
                witness,
                dx_encryption_seed,
                dy_encryption_seed,
                &request,
            )
            .map_err(|e| e.to_string())?;
            let request_wire = request.to_wire_bytes();
            let statement_wire = private_amm_statement_to_wire(statement);
            let mut next_state_wire = next_state.to_wire_bytes();
            let mut authority_wire = authority.to_wire_bytes();
            let result = write_bundle_atomic(
                output_dir,
                &request_wire,
                &statement_wire,
                &next_state_wire,
                &authority_wire,
            );
            next_state_wire.fill(0);
            authority_wire.fill(0);
            result?;
            println!(
                "created atomic private-swap bundle: {} (sequence {}, old root {}, new root {})",
                output_dir.display(),
                request.sequence(),
                hex_root(&statement.old_root),
                hex_root(&statement.new_root)
            );
            Ok(())
        }
        [
            command,
            public_file,
            request_file,
            private_authority_file,
            roster_file,
            threshold,
            signer_index,
            signing_key_file,
            output,
        ] if command == "same-opening-endorse" => {
            ensure_absent(Path::new(output), "endorsement output")?;
            let public = read_public(Path::new(public_file))?;
            let request = read_proved_request(Path::new(request_file))?;
            let private_authority = read_private_authority(Path::new(private_authority_file))?;
            let authority = read_same_opening_policy(
                Path::new(roster_file),
                parse_usize(threshold, "threshold")?,
            )?;
            let signer_index = parse_usize(signer_index, "signer index")?;
            let signing_key = read_signing_key(Path::new(signing_key_file))?;
            let endorsement = private_authority
                .endorse_same_opening(
                    &public,
                    &request,
                    &authority,
                    signer_index,
                    &signing_key,
                )
                .map_err(|error| error.to_string())?;
            write_new_atomic(Path::new(output), &endorsement.to_wire_bytes(), false)?;
            println!(
                "created Tier-1 same-opening endorsement: {output} (signer {signer_index}, sequence {})",
                request.sequence()
            );
            Ok(())
        }
        [
            command,
            public_file,
            request_file,
            private_authority_file,
            roster_file,
            threshold,
            output,
            endorsement_files @ ..,
        ] if command == "same-opening-assemble" => {
            if endorsement_files.len() < 2 {
                return Err(
                    "same-opening-assemble requires at least two endorsement files".to_string(),
                );
            }
            ensure_absent(Path::new(output), "v3 request output")?;
            let public = read_public(Path::new(public_file))?;
            let request = read_proved_request(Path::new(request_file))?;
            let private_authority = read_private_authority(Path::new(private_authority_file))?;
            let authority = read_same_opening_policy(
                Path::new(roster_file),
                parse_usize(threshold, "threshold")?,
            )?;
            let endorsements = endorsement_files
                .iter()
                .map(|path| read_same_opening_endorsement(Path::new(path)))
                .collect::<Result<Vec<_>, _>>()?;
            let v3 = private_authority
                .assemble_same_opening_request(&public, request, &authority, &endorsements)
                .map_err(|error| error.to_string())?;
            write_new_atomic(Path::new(output), &v3.to_wire_bytes(), false)?;
            println!(
                "created strict v3 same-opening request: {output} ({} independent endorsements, sequence {})",
                endorsements.len(),
                v3.sequence()
            );
            Ok(())
        }
        [command, public_file, next_sequence, output] if command == "cursor" => {
            let public_bytes = fs::read(public_file)
                .map_err(|e| format!("cannot read public context {public_file:?}: {e}"))?;
            let public = DarkAmmPublicSession::from_wire_bytes(&public_bytes)
                .map_err(|e| e.to_string())?
                .at_sequence(parse_u64(next_sequence)?);
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created advanced public Dark Pool context: {output} (session {}, sequence {})",
                hex32(&public.session_id()),
                public.next_sequence()
            );
            Ok(())
        }
        [command, public_file, accepted_statement_file, next_sequence, output]
            if command == "proved-cursor" =>
        {
            let public_bytes = fs::read(public_file)
                .map_err(|e| format!("cannot read public context {public_file:?}: {e}"))?;
            let public = DarkAmmPublicSession::from_wire_bytes(&public_bytes)
                .map_err(|e| e.to_string())?;
            let statement = read_statement(Path::new(accepted_statement_file))?;
            check_statement_context(&public, statement)?;
            let public = public
                .at_proof_cursor(parse_u64(next_sequence)?, statement.new_root)
                .map_err(|e| e.to_string())?;
            write_new(Path::new(output), &public.to_wire_bytes(), false)?;
            println!(
                "created advanced proof-required Dark Pool context: {output} (session {}, sequence {})",
                hex32(&public.session_id()),
                public.next_sequence()
            );
            Ok(())
        }
        [
            command,
            task_file,
            material_file,
            expected_context_file,
            worker_config_file,
            worker_custody_file,
            output,
        ] if command == "collective-decide" => collective_decide(
            Path::new(task_file),
            Path::new(material_file),
            Path::new(expected_context_file),
            Path::new(worker_config_file),
            Path::new(worker_custody_file),
            Path::new(output),
        ),
        _ => Err(
            "usage:\n  dark-amm-tool keygen <new-secret-key-file>\n  dark-amm-tool public <secret-key-file> <session-seed> <new-public-context-file>\n  dark-amm-tool public-proved <secret-key-file> <session-seed> <initial-statement-file> <new-public-context-file>\n  dark-amm-tool public-private <secret-key-file> <session-seed> <private-state-file> <new-public-context-file>\n  dark-amm-tool public-id <secret-key-file> <web-session-id> <new-public-context-file>\n  dark-amm-tool public-id-proved <secret-key-file> <web-session-id> <initial-statement-file> <new-public-context-file>\n  dark-amm-tool public-id-private <secret-key-file> <web-session-id> <private-state-file> <new-public-context-file>\n  dark-amm-tool private-init <public-context-file> <x> <y> <new-private-state-file>\n  dark-amm-tool swap <public-context-file> <dx> <dy> <dx-bound> <dy-bound> <new-request-file>\n  dark-amm-tool proved-swap <public-context-file> <statement-file> <proof-postcard-file> <dx> <dy> <dx-bound> <dy-bound> <new-request-file>\n  dark-amm-tool private-swap <proof-public-context-file> <private-state-file> <dx> <dy> <dx-bound> <dy-bound> <new-bundle-directory>\n  dark-amm-tool same-opening-endorse <public-context-file> <request.dbam> <authority.dbaa> <ordered-roster-file> <threshold> <signer-index> <signing-key-file> <new-endorsement-file>\n  dark-amm-tool same-opening-assemble <public-context-file> <request.dbam> <authority.dbaa> <ordered-roster-file> <threshold> <new-v3-request-file> <endorsement-file> <endorsement-file> [...]\n  dark-amm-tool cursor <public-context-file> <next-sequence> <new-public-context-file>\n  dark-amm-tool proved-cursor <public-context-file> <accepted-statement-file> <next-sequence> <new-public-context-file>\n  dark-amm-tool collective-decide <task-file> <committed-public-material-file> <expected-context-file> <public-worker-config-file> <protected-worker-custody-file> <new-decision-bundle-file>"
                .to_string(),
        ),
    }
}

struct CollectiveWorkerConfig {
    keygen: KeygenSession,
    value_bits: usize,
    timeout: std::time::Duration,
    decision_verifier: AuthenticatedQuorumVerifier,
}

struct CollectiveWorkerCustody {
    threshold_roots: Vec<[u8; 32]>,
    preprocessing_seed: [u8; 32],
    decision_signers: Vec<(usize, SigningKey)>,
}

impl Drop for CollectiveWorkerCustody {
    fn drop(&mut self) {
        for root in &mut self.threshold_roots {
            root.fill(0);
        }
        self.preprocessing_seed.fill(0);
        // `ed25519_dalek::SigningKey` provides its own zeroize-on-drop path.
    }
}

fn collective_decide(
    task_path: &Path,
    material_path: &Path,
    expected_context_path: &Path,
    config_path: &Path,
    custody_path: &Path,
    output_path: &Path,
) -> Result<(), String> {
    let task_wire = read_bounded_regular(
        task_path,
        "collective decision task",
        MAX_COLLECTIVE_DECISION_TASK_BYTES as u64,
        false,
    )?;
    let material_wire = read_bounded_regular(
        material_path,
        "committed public host material",
        MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES as u64,
        false,
    )?;
    let context_wire = read_bounded_regular(
        expected_context_path,
        "expected collective task context",
        MAX_COLLECTIVE_WORKER_CONTEXT_BYTES,
        false,
    )?;
    let config_wire = read_bounded_regular(
        config_path,
        "public collective worker configuration",
        MAX_COLLECTIVE_WORKER_CONFIG_BYTES,
        false,
    )?;
    let mut custody_wire = read_bounded_regular(
        custody_path,
        "protected collective worker custody",
        MAX_COLLECTIVE_WORKER_CUSTODY_BYTES,
        true,
    )?;

    let result = (|| {
        let expected_context = parse_collective_worker_context(&context_wire)?;
        let config = parse_collective_worker_config(&config_wire)?;
        let custody = parse_collective_worker_custody(&custody_wire, &config)?;

        let params = BfvParams::fold_set();
        let material = DarkPoolPublicHostMaterial::from_wire_bytes(&material_wire, params.arc())
            .map_err(|error| format!("committed public host material refused: {error}"))?;
        let mut coordinator = KeygenCoordinator::new(config.keygen.clone(), params.clone());
        let mut parties = Vec::with_capacity(config.keygen.n_parties());
        for (party_index, root) in custody.threshold_roots.iter().enumerate() {
            let (party, contribution) =
                ThresholdParty::join_seeded(&config.keygen, party_index, &params, root)
                    .map_err(|error| format!("threshold custody refused: {error:?}"))?;
            coordinator
                .accept(contribution)
                .map_err(|error| format!("threshold contribution refused: {error:?}"))?;
            parties.push(party);
        }
        let collective = coordinator
            .finish()
            .map_err(|error| format!("collective key reconstruction refused: {error:?}"))?;
        let task = CollectiveDecisionTask::from_wire_bytes(
            &task_wire,
            &material,
            &params,
            &config.keygen,
            &collective,
            config.value_bits,
        )
        .map_err(|error| error.to_string())?;
        task.validate_context(expected_context)
            .map_err(|error| error.to_string())?;

        let worker = MaskedCollectiveDecisionWorker::new(
            &params,
            &config.keygen,
            &collective,
            &parties,
            config.value_bits,
            config.timeout,
        )
        .map_err(|error| error.to_string())?;
        let session = worker
            .decision_session_for_task(&task, &material, expected_context)
            .map_err(|error| error.to_string())?;
        // Trusted preprocessing is deliberately named by the protected seed.
        // It sees only the public circuit/session shape, never an operand.
        let mut preprocessing_rng = StdRng::from_seed(custody.preprocessing_seed);
        let triples = trusted_dealer_triples(&session, &mut preprocessing_rng)
            .map_err(|error| error.to_string())?;
        let decision = worker
            .decide_task_with_triples(&task, &material, expected_context, triples)
            .map_err(|error| error.to_string())?;
        let draft = decision
            .draft_receipt(&config.decision_verifier)
            .map_err(|error| error.to_string())?;
        let signatures = custody
            .decision_signers
            .iter()
            .map(|(index, key)| {
                config
                    .decision_verifier
                    .sign_claim(&draft.claim_digest(), *index, key)
                    .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<PartyClaimSignature>, String>>()?;
        let receipt = decision
            .assemble_attested_receipt(&config.decision_verifier, &signatures)
            .map_err(|error| error.to_string())?;
        let bundle = CollectiveDecisionBundle::new(decision.transcript().clone(), receipt);
        let bundle_wire = bundle.to_wire_bytes().map_err(|error| error.to_string())?;
        let bundle_digest = *blake3::hash(&bundle_wire).as_bytes();
        write_new_atomic(output_path, &bundle_wire, false)?;
        println!(
            "created public collective Dark Bazaar decision bundle: {} (task {}, bundle {})",
            output_path.display(),
            hex32(
                &task
                    .attestation_nonce()
                    .map_err(|error| error.to_string())?
            ),
            hex32(&bundle_digest)
        );
        Ok(())
    })();
    custody_wire.fill(0);
    result
}

fn parse_collective_worker_context(bytes: &[u8]) -> Result<CollectiveDecisionTaskContext, String> {
    let content = checked_collective_worker_wire(
        bytes,
        COLLECTIVE_WORKER_CONTEXT_MAGIC,
        "expected collective task context",
    )?;
    let mut input = CollectiveWorkerReader::new(content);
    input.expect_magic(COLLECTIVE_WORKER_CONTEXT_MAGIC)?;
    let hosted_session = input.array()?;
    let sequence = input.u64()?;
    let mut committed_root = [0u32; 8];
    for lane in &mut committed_root {
        *lane = input.u32()?;
    }
    let same_opening_claim_digest = input.array()?;
    input.finish()?;
    let context = CollectiveDecisionTaskContext {
        hosted_session,
        sequence,
        committed_root,
        same_opening_claim_digest,
    };
    if hosted_session == [0; 32] || same_opening_claim_digest == [0; 32] {
        return Err("expected collective task context contains a zero identity".to_string());
    }
    Ok(context)
}

fn parse_collective_worker_config(bytes: &[u8]) -> Result<CollectiveWorkerConfig, String> {
    let content = checked_collective_worker_wire(
        bytes,
        COLLECTIVE_WORKER_CONFIG_MAGIC,
        "public collective worker configuration",
    )?;
    let mut input = CollectiveWorkerReader::new(content);
    input.expect_magic(COLLECTIVE_WORKER_CONFIG_MAGIC)?;
    let n_parties = input.usize()?;
    let crp_seed = input.array()?;
    let value_bits = input.usize()?;
    let timeout_millis = input.u64()?;
    let threshold = input.usize()?;
    let roster_count = input.usize()?;
    if !(2..=MAX_COLLECTIVE_WORKER_PARTIES).contains(&n_parties) || roster_count != n_parties {
        return Err("public worker roster must name 2..=16 matching parties".to_string());
    }
    let mut ordered_public_keys = Vec::with_capacity(roster_count);
    for _ in 0..roster_count {
        ordered_public_keys.push(input.array()?);
    }
    input.finish()?;
    let keygen = KeygenSession::from_seed(n_parties, crp_seed)
        .map_err(|error| format!("public DKG identity refused: {error:?}"))?;
    if !(1..=63).contains(&value_bits) {
        return Err("worker value width must be between 1 and 63 bits".to_string());
    }
    let timeout = std::time::Duration::from_millis(timeout_millis);
    if timeout.is_zero()
        || timeout > dreggnet_market::dark_amm_collective_worker::MAX_COLLECTIVE_DECISION_TIMEOUT
    {
        return Err("worker timeout must be nonzero and at most five minutes".to_string());
    }
    let decision_verifier = AuthenticatedQuorumVerifier::new(ordered_public_keys, threshold)
        .map_err(|error| format!("decision authority policy refused: {error}"))?;
    Ok(CollectiveWorkerConfig {
        keygen,
        value_bits,
        timeout,
        decision_verifier,
    })
}

fn parse_collective_worker_custody(
    bytes: &[u8],
    config: &CollectiveWorkerConfig,
) -> Result<CollectiveWorkerCustody, String> {
    let content = checked_collective_worker_wire(
        bytes,
        COLLECTIVE_WORKER_CUSTODY_MAGIC,
        "protected collective worker custody",
    )?;
    let mut input = CollectiveWorkerReader::new(content);
    input.expect_magic(COLLECTIVE_WORKER_CUSTODY_MAGIC)?;
    let root_count = input.usize()?;
    if root_count != config.keygen.n_parties() {
        return Err("threshold custody root count differs from public DKG roster".to_string());
    }
    let mut threshold_roots = Vec::with_capacity(root_count);
    for _ in 0..root_count {
        let root = input.array()?;
        if root == [0; 32] || threshold_roots.contains(&root) {
            return Err("threshold custody roots must be nonzero and distinct".to_string());
        }
        threshold_roots.push(root);
    }
    let preprocessing_seed = input.array()?;
    if preprocessing_seed == [0; 32] {
        return Err("trusted preprocessing seed must be nonzero".to_string());
    }
    let signer_count = input.usize()?;
    if signer_count < config.decision_verifier.threshold()
        || signer_count > config.keygen.n_parties()
    {
        return Err("decision signer custody does not satisfy the public threshold".to_string());
    }
    let mut decision_signers = Vec::with_capacity(signer_count);
    let mut previous_index = None;
    for _ in 0..signer_count {
        let index = input.usize()?;
        if previous_index.is_some_and(|previous| index <= previous) {
            return Err("decision signer custody is not in strict roster order".to_string());
        }
        let mut key_bytes: [u8; 32] = input.array()?;
        let key = SigningKey::from_bytes(&key_bytes);
        key_bytes.fill(0);
        let expected = config
            .decision_verifier
            .ordered_public_keys()
            .get(index)
            .ok_or_else(|| "decision signer index is outside the public roster".to_string())?;
        if key.verifying_key().to_bytes() != *expected {
            return Err("decision signer key does not match its public roster slot".to_string());
        }
        previous_index = Some(index);
        decision_signers.push((index, key));
    }
    input.finish()?;
    Ok(CollectiveWorkerCustody {
        threshold_roots,
        preprocessing_seed,
        decision_signers,
    })
}

fn checked_collective_worker_wire<'a>(
    bytes: &'a [u8],
    magic: &[u8; 8],
    label: &str,
) -> Result<&'a [u8], String> {
    if bytes.len() < magic.len() + 32 || &bytes[..magic.len()] != magic {
        return Err(format!("{label} has a wrong or truncated version"));
    }
    let content_end = bytes.len() - 32;
    if bytes[content_end..] != collective_worker_checksum(&bytes[..content_end]) {
        return Err(format!("{label} checksum mismatch"));
    }
    Ok(&bytes[..content_end])
}

fn collective_worker_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(COLLECTIVE_WORKER_CHECKSUM_DOMAIN);
    hash.update(&(content.len() as u64).to_le_bytes());
    hash.update(content);
    *hash.finalize().as_bytes()
}

struct CollectiveWorkerReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CollectiveWorkerReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn expect_magic(&mut self, expected: &[u8; 8]) -> Result<(), String> {
        if self.array::<8>()? == *expected {
            Ok(())
        } else {
            Err("collective worker input version changed during parsing".to_string())
        }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], String> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| "collective worker input is truncated".to_string())?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| "collective worker fixed-width field is malformed".to_string())?;
        self.offset = end;
        Ok(value)
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn usize(&mut self) -> Result<usize, String> {
        usize::try_from(self.u64()?)
            .map_err(|_| "collective worker count does not fit this platform".to_string())
    }

    fn finish(self) -> Result<(), String> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err("collective worker input has trailing bytes".to_string())
        }
    }
}

fn parse_u64(value: &str) -> Result<u64, String> {
    if let Some(hex) = value
        .strip_prefix("0x")
        .or_else(|| value.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).map_err(|_| format!("invalid u64 value {value:?}"))
    } else {
        value
            .parse()
            .map_err(|_| format!("invalid u64 value {value:?}"))
    }
}

fn parse_u16(value: &str) -> Result<u16, String> {
    let parsed = parse_u64(value)?;
    u16::try_from(parsed).map_err(|_| format!("value {value:?} does not fit u16"))
}

fn parse_usize(value: &str, label: &str) -> Result<usize, String> {
    usize::try_from(parse_u64(value)?)
        .map_err(|_| format!("{label} value {value:?} does not fit this platform"))
}

fn read_bounded_regular(
    path: &Path,
    label: &str,
    max_bytes: u64,
    owner_only: bool,
) -> Result<Vec<u8>, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {label} {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "{label} {} must be a regular, non-symlinked file",
            path.display()
        ));
    }
    if metadata.len() > max_bytes {
        return Err(format!(
            "{label} {} is {} bytes; maximum is {max_bytes}",
            path.display(),
            metadata.len()
        ));
    }
    #[cfg(unix)]
    if owner_only {
        use std::os::unix::fs::MetadataExt;
        let mode = metadata.mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!(
                "{label} {} has mode {mode:03o}; remove all group/other permissions",
                path.display()
            ));
        }
    }
    fs::read(path).map_err(|error| format!("cannot read {label} {}: {error}", path.display()))
}

fn read_proved_request(path: &Path) -> Result<ProvedEncryptedSwapRequest, String> {
    let bytes = read_bounded_regular(path, "proved request", 8 * 1024 * 1024, false)?;
    ProvedEncryptedSwapRequest::from_wire_bytes(&bytes).map_err(|error| error.to_string())
}

fn read_private_authority(path: &Path) -> Result<DarkAmmPrivateSwapAuthority, String> {
    let mut bytes = read_bounded_regular(path, "private authority", 4096, true)?;
    let parsed =
        DarkAmmPrivateSwapAuthority::from_wire_bytes(&bytes).map_err(|error| error.to_string());
    bytes.fill(0);
    parsed
}

fn read_signing_key(path: &Path) -> Result<SigningKey, String> {
    let mut bytes = read_bounded_regular(path, "issuer signing key", 32, true)?;
    let parsed = (|| {
        let mut key_bytes: [u8; 32] = bytes.as_slice().try_into().map_err(|_| {
            format!(
                "issuer signing key {} must contain exactly 32 raw Ed25519 secret bytes",
                path.display()
            )
        })?;
        let key = SigningKey::from_bytes(&key_bytes);
        key_bytes.fill(0);
        Ok(key)
    })();
    bytes.fill(0);
    parsed
}

fn read_same_opening_policy(
    roster_path: &Path,
    threshold: usize,
) -> Result<Tier1SameOpeningAuthority, String> {
    let bytes = read_bounded_regular(
        roster_path,
        "ordered issuer roster",
        (MAX_AUTHORITY_PARTIES * 32) as u64,
        false,
    )?;
    if bytes.is_empty() || bytes.len() % 32 != 0 || bytes.len() / 32 > MAX_AUTHORITY_PARTIES {
        return Err(format!(
            "ordered issuer roster {} must be 1..={MAX_AUTHORITY_PARTIES} concatenated raw 32-byte Ed25519 public keys",
            roster_path.display()
        ));
    }
    let ordered_public_keys = bytes
        .chunks_exact(32)
        .map(|key| key.try_into().expect("chunks are exactly 32 bytes"))
        .collect();
    Tier1SameOpeningAuthority::new(ordered_public_keys, threshold)
        .map_err(|error| format!("invalid ordered issuer policy: {error}"))
}

fn read_same_opening_endorsement(path: &Path) -> Result<Tier1SameOpeningEndorsement, String> {
    let bytes = read_bounded_regular(
        path,
        "same-opening endorsement",
        SAME_OPENING_ENDORSEMENT_WIRE_LEN as u64,
        false,
    )?;
    Tier1SameOpeningEndorsement::from_wire_bytes(&bytes).map_err(|error| {
        format!(
            "invalid same-opening endorsement {}: {error}",
            path.display()
        )
    })
}

fn seed_for_session_id(session_id: &str) -> u64 {
    let digest = blake3::hash(session_id.as_bytes());
    u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap())
}

fn read_public(path: &Path) -> Result<DarkAmmPublicSession, String> {
    const MAX_PUBLIC_BYTES: u64 = 8 * 1024 * 1024;
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect public context {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "public context {} must be a regular, non-symlinked file",
            path.display()
        ));
    }
    if metadata.len() > MAX_PUBLIC_BYTES {
        return Err(format!(
            "public context {} is {} bytes; maximum is {MAX_PUBLIC_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot read public context {}: {error}", path.display()))?;
    DarkAmmPublicSession::from_wire_bytes(&bytes).map_err(|error| error.to_string())
}

fn proof_public_for_seed(
    keys: DarkAmmHostKeyMaterial,
    seed: u64,
    state: &DarkAmmPrivateState,
) -> Result<DarkAmmPublicSession, String> {
    let root = state.root().map_err(|error| error.to_string())?;
    let public = DarkAmmGameOffering::demo_proof_required(keys, root)
        .map_err(|error| error.to_string())?
        .public_session_for_seed(seed)
        .map_err(|error| error.to_string())?;
    state
        .validate_for_proof_context(&public)
        .map_err(|error| error.to_string())?;
    Ok(public)
}

fn read_private_state(path: &Path) -> Result<DarkAmmPrivateState, String> {
    const MAX_PRIVATE_STATE_BYTES: u64 = 4096;
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect private state {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "private state {} must be a regular, non-symlinked file",
            path.display()
        ));
    }
    if metadata.len() > MAX_PRIVATE_STATE_BYTES {
        return Err(format!(
            "private state {} is {} bytes; maximum is {MAX_PRIVATE_STATE_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let mode = metadata.mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!(
                "private state {} has mode {mode:03o}; remove all group/other permissions",
                path.display()
            ));
        }
    }
    let mut bytes =
        fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let parsed = DarkAmmPrivateState::from_wire_bytes(&bytes).map_err(|error| error.to_string());
    bytes.fill(0);
    parsed
}

fn read_statement(path: &Path) -> Result<PrivateAmmPublicStatement, String> {
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot read receipt statement {}: {error}", path.display()))?;
    private_amm_statement_from_wire(&bytes).map_err(|error| error.to_string())
}

fn check_statement_context(
    public: &DarkAmmPublicSession,
    statement: PrivateAmmPublicStatement,
) -> Result<(), String> {
    let context = public
        .proof_context()
        .ok_or_else(|| "public context is not proof-required".to_string())?;
    if statement.session != context.receipt_session()
        || statement.rule != context.rule()
        || u64::from(statement.k) != public.k()
        || statement.old_root != context.current_root()
    {
        return Err(
            "receipt statement does not pin this context's session, rule, k, and current root"
                .to_string(),
        );
    }
    Ok(())
}

fn read_host_key(path: &Path) -> Result<DarkAmmHostKeyMaterial, String> {
    const MAX_KEY_BYTES: u64 = 128 * 1024 * 1024;
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot inspect protected key {}: {e}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "protected key {} must be a regular, non-symlinked file",
            path.display()
        ));
    }
    if metadata.len() > MAX_KEY_BYTES {
        return Err(format!(
            "protected key {} is {} bytes; maximum is {MAX_KEY_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let mode = metadata.mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!(
                "protected key {} has mode {mode:03o}; remove all group/other permissions",
                path.display()
            ));
        }
    }
    let mut bytes =
        fs::read(path).map_err(|e| format!("cannot read protected key {}: {e}", path.display()))?;
    let parsed = DarkAmmHostKeyMaterial::from_secret_wire_bytes(&bytes).map_err(|e| e.to_string());
    bytes.fill(0);
    parsed
}

fn write_new(path: &Path, bytes: &[u8], secret: bool) -> Result<(), String> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    if secret {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|e| format!("refusing to overwrite {}: {e}", path.display()))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| format!("cannot persist {}: {e}", path.display()))
}

fn output_parent(path: &Path) -> Result<&Path, String> {
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let parent = if parent.as_os_str().is_empty() {
        Path::new(".")
    } else {
        parent
    };
    let metadata = fs::symlink_metadata(parent)
        .map_err(|error| format!("cannot inspect output parent {}: {error}", parent.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
        return Err(format!(
            "output parent {} must be a real directory, not a symlink",
            parent.display()
        ));
    }
    Ok(parent)
}

fn unique_staging_path(path: &Path) -> Result<PathBuf, String> {
    let parent = output_parent(path)?;
    let name = path
        .file_name()
        .filter(|name| !name.is_empty())
        .ok_or_else(|| format!("output path {} has no file name", path.display()))?
        .to_string_lossy();
    let mut rng = rand_09::rng();
    for _ in 0..32 {
        let mut nonce = [0u8; 16];
        rng.fill_bytes(&mut nonce);
        let candidate = parent.join(format!(".{name}.tmp-{}", hex_bytes(&nonce)));
        match fs::symlink_metadata(&candidate) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(candidate),
            Ok(_) => continue,
            Err(error) => {
                return Err(format!(
                    "cannot inspect staging path {}: {error}",
                    candidate.display()
                ));
            }
        }
    }
    Err("could not allocate a collision-free staging path".to_string())
}

fn ensure_absent(path: &Path, label: &str) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Ok(_) => Err(format!(
            "refusing to overwrite existing {label} {}",
            path.display()
        )),
        Err(error) => Err(format!("cannot inspect {}: {error}", path.display())),
    }
}

fn write_new_atomic(path: &Path, bytes: &[u8], secret: bool) -> Result<(), String> {
    ensure_absent(path, "output")?;
    let staging = unique_staging_path(path)?;
    let result = (|| {
        write_new(&staging, bytes, secret)?;
        // `hard_link` is an atomic no-clobber publication: unlike rename on
        // Unix, it fails if a destination appeared after the initial check.
        fs::hard_link(&staging, path).map_err(|error| {
            format!(
                "cannot publish {} without clobbering: {error}",
                path.display()
            )
        })?;
        fs::remove_file(&staging).map_err(|error| {
            format!(
                "published {} but could not remove staging link {}: {error}",
                path.display(),
                staging.display()
            )
        })?;
        fs::File::open(output_parent(path)?)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("cannot sync output parent: {error}"))?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&staging);
    }
    result
}

fn ensure_new_bundle_target(path: &Path) -> Result<(), String> {
    output_parent(path)?;
    ensure_absent(path, "bundle directory")
}

fn write_bundle_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|error| format!("cannot create bundle member {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|error| format!("cannot persist bundle member {}: {error}", path.display()))
}

fn write_bundle_atomic(
    output: &Path,
    request: &[u8],
    statement: &[u8],
    next_state: &[u8],
    authority: &[u8],
) -> Result<(), String> {
    ensure_new_bundle_target(output)?;
    let staging = unique_staging_path(output)?;
    let result = (|| {
        let mut builder = fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            builder.mode(0o700);
        }
        builder.create(&staging).map_err(|error| {
            format!(
                "cannot create bundle staging directory {}: {error}",
                staging.display()
            )
        })?;
        write_bundle_file(&staging.join("request.dbam"), request)?;
        write_bundle_file(&staging.join("statement.dbas"), statement)?;
        write_bundle_file(&staging.join("next-state.dbao"), next_state)?;
        write_bundle_file(&staging.join("authority.dbaa"), authority)?;
        fs::File::open(&staging)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("cannot sync bundle staging directory: {error}"))?;
        // Rename publishes all four fully synced members as one directory
        // entry. Re-check immediately before publication to fail closed on
        // ordinary output collisions.
        ensure_absent(output, "bundle directory")?;
        fs::rename(&staging, output).map_err(|error| {
            format!(
                "cannot atomically publish bundle {}: {error}",
                output.display()
            )
        })?;
        fs::File::open(output_parent(output)?)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("cannot sync bundle parent directory: {error}"))?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_dir_all(&staging);
    }
    result
}

fn hex32(bytes: &[u8; 32]) -> String {
    hex_bytes(bytes)
}

fn hex_root(root: &[u32; 8]) -> String {
    root.iter()
        .map(|lane| format!("{lane:08x}"))
        .collect::<Vec<_>>()
        .join(":")
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
