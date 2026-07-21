//! Offline producer/operator utility for the hosted encrypted Dark Pool demo.
//!
//! `keygen` writes secret deployment custody; `public` derives a distributable
//! session context; `private-init` creates an owner-only hidden state opening;
//! and `private-swap` proves + encrypts one transition into an atomic upload
//! bundle without requiring caller-authored Rust. After acceptance,
//! `proved-cursor` advances the public context to the bundle's statement while
//! the bundle's next private state becomes the producer's new custody object.

use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};

use dregg_circuit_prove::dark_amm_private::{
    PublicStatement as PrivateAmmPublicStatement, prove_zk, sample_commitment_blind,
};
use dreggnet_market::dark_amm_collective::CollectiveDecisionBundle;
use dreggnet_market::dark_amm_collective_worker::{
    CollectiveDecisionTask, CollectiveDecisionTaskContext, MAX_COLLECTIVE_DECISION_TASK_BYTES,
    MaskedCollectiveDecision, MaskedCollectiveDecisionWorker,
};
use dreggnet_market::dark_amm_game::{
    DarkAmmGameOffering, DarkAmmHostKeyMaterial, DarkAmmPrivateState, DarkAmmPrivateSwapAuthority,
    DarkAmmPublicSession, ProvedEncryptedSwapRequest, private_amm_statement_from_wire,
    private_amm_statement_to_wire, produce_encrypted_swap, produce_proved_encrypted_swap,
    produce_proved_encrypted_swap_seeded,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use fhe_traits::Serialize as FheSerialize;
use fhegg_fhe::amm_same_opening::{
    MAX_AUTHORITY_PARTIES, SAME_OPENING_ENDORSEMENT_WIRE_LEN, Tier1SameOpeningAuthority,
    Tier1SameOpeningEndorsement,
};
use fhegg_fhe::attestation::{AuthenticatedQuorumVerifier, PartyClaimSignature};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::boundary::{
    EncryptedMaskContribution, MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession,
};
use fhegg_fhe::dark_amm::{DarkPoolPublicHostMaterial, MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES};
use fhegg_fhe::mpc_party::transport::{
    AuthenticatedEqualityFrame, EqualityCoordinatorMachine, EqualityPartyMachine,
    EqualityTransportRoster,
};
use fhegg_fhe::mpc_party::{
    DecisionTranscript, PartyEqualityInput, PartyMpcSession, TripleMaterial, trusted_dealer_triples,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, MIN_SMUDGE_BITS,
    PublicKeyContribution, ThresholdParty,
};
use rand::SeedableRng;
use rand::rngs::{OsRng, StdRng};
use rand_09::RngCore;

const COLLECTIVE_WORKER_CONFIG_MAGIC: &[u8; 8] = b"DBWCv001";
const COLLECTIVE_WORKER_CONTEXT_MAGIC: &[u8; 8] = b"DBCTX001";
const COLLECTIVE_WORKER_CUSTODY_MAGIC: &[u8; 8] = b"DBCKv001";
const COLLECTIVE_PARTY_CUSTODY_MAGIC: &[u8; 8] = b"DBPCv001";
const COLLECTIVE_PARTY_ARTIFACT_MAGIC: &[u8; 8] = b"DBPAv001";
const COLLECTIVE_PREPROCESSING_SHARE_MAGIC: &[u8; 8] = b"DBPSv001";
const COLLECTIVE_WORKER_CHECKSUM_DOMAIN: &str =
    "dregg-dark-amm-collective-worker-input-checksum-v1";
const COLLECTIVE_PARTY_ARTIFACT_SIGNATURE_DOMAIN: &str =
    "dregg-dark-amm-collective-party-artifact-signature-v1";
const MAX_COLLECTIVE_WORKER_PARTIES: usize = MAX_AUTHORITY_PARTIES;
const MAX_COLLECTIVE_WORKER_CONFIG_BYTES: u64 = 1024;
const MAX_COLLECTIVE_WORKER_CONTEXT_BYTES: u64 = 144;
const MAX_COLLECTIVE_WORKER_CUSTODY_BYTES: u64 = 2048;
const MAX_COLLECTIVE_PARTY_CUSTODY_BYTES: u64 = 256;
const MAX_COLLECTIVE_PARTY_ARTIFACT_BYTES: u64 = 64 * 1024 * 1024;
const MAX_COLLECTIVE_PREPROCESSING_SHARE_BYTES: u64 = 112;

fn main() {
    if let Err(error) = run() {
        eprintln!("dark-amm-tool: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args
        .first()
        .is_some_and(|command| command == "collective-process-preprocess-internal")
    {
        return collective_process_preprocess_internal(&args[1..]);
    }
    if args
        .first()
        .is_some_and(|command| command == "collective-process-preprocessing-share-internal")
    {
        return collective_process_preprocessing_share_internal(&args[1..]);
    }
    if args
        .first()
        .is_some_and(|command| command == "collective-process-party-internal")
    {
        return collective_process_party_internal(&args[1..]);
    }
    if args
        .first()
        .is_some_and(|command| command == "collective-process-coordinator-internal")
    {
        return collective_process_coordinator_internal(&args[1..]);
    }
    if args
        .first()
        .is_some_and(|command| command == "collective-decide-split")
    {
        return collective_decide_split(&args[1..]);
    }
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
        [command, config_file, party_custody_file, output]
            if command == "collective-party-contribute" =>
        {
            collective_party_contribute(
                Path::new(config_file),
                Path::new(party_custody_file),
                Path::new(output),
            )
        }
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

struct CollectivePartyCustody {
    party: usize,
    threshold_root: [u8; 32],
    preprocessing_seed_share: [u8; 32],
    decision_signer: SigningKey,
}

impl Drop for CollectivePartyCustody {
    fn drop(&mut self) {
        self.threshold_root.fill(0);
        self.preprocessing_seed_share.fill(0);
    }
}

struct CollectivePartyArtifact {
    party: usize,
    contribution: PublicKeyContribution,
    signature: [u8; 64],
}

impl CollectivePartyArtifact {
    fn to_wire_bytes(&self, config_wire: &[u8]) -> Vec<u8> {
        let contribution = self.contribution.to_wire_bytes();
        let mut out = Vec::with_capacity(128 + contribution.len());
        out.extend_from_slice(COLLECTIVE_PARTY_ARTIFACT_MAGIC);
        out.extend_from_slice(&(self.party as u64).to_le_bytes());
        out.extend_from_slice(&collective_worker_config_digest(config_wire));
        out.extend_from_slice(&(contribution.len() as u64).to_le_bytes());
        out.extend_from_slice(&contribution);
        out.extend_from_slice(&self.signature);
        out.extend_from_slice(&collective_worker_checksum(&out));
        out
    }

    fn from_wire_bytes(
        bytes: &[u8],
        config_wire: &[u8],
        config: &CollectiveWorkerConfig,
    ) -> Result<Self, String> {
        let content = checked_collective_worker_wire(
            bytes,
            COLLECTIVE_PARTY_ARTIFACT_MAGIC,
            "public collective party contribution",
        )?;
        let mut input = CollectiveWorkerReader::new(content);
        input.expect_magic(COLLECTIVE_PARTY_ARTIFACT_MAGIC)?;
        let party = input.usize()?;
        let config_digest = input.array()?;
        if config_digest != collective_worker_config_digest(config_wire) {
            return Err("party contribution names a different worker configuration".to_string());
        }
        let contribution_wire = input.bytes(MAX_COLLECTIVE_PARTY_ARTIFACT_BYTES as usize)?;
        let signature = input.array()?;
        input.finish()?;
        let contribution = PublicKeyContribution::from_wire_bytes(contribution_wire)
            .map_err(|error| format!("party public-key contribution refused: {error:?}"))?;
        if party >= config.keygen.n_parties()
            || contribution.party() != party
            || contribution.session() != &config.keygen
        {
            return Err("party contribution has a wrong DKG identity or index".to_string());
        }
        let public_key = config
            .decision_verifier
            .ordered_public_keys()
            .get(party)
            .ok_or_else(|| "party contribution signer is outside the public roster".to_string())?;
        let verifier = VerifyingKey::from_bytes(public_key)
            .map_err(|_| "party contribution signer key is malformed".to_string())?;
        verifier
            .verify_strict(
                &collective_party_artifact_message(party, &config_digest, contribution_wire),
                &Signature::from_bytes(&signature),
            )
            .map_err(|_| "party contribution signature is invalid".to_string())?;
        let artifact = Self {
            party,
            contribution,
            signature,
        };
        if artifact.to_wire_bytes(config_wire) != bytes {
            return Err("party contribution is not canonically encoded".to_string());
        }
        Ok(artifact)
    }
}

fn collective_party_contribute(
    config_path: &Path,
    custody_path: &Path,
    output_path: &Path,
) -> Result<(), String> {
    let config_wire = read_bounded_regular(
        config_path,
        "public collective worker configuration",
        MAX_COLLECTIVE_WORKER_CONFIG_BYTES,
        false,
    )?;
    let config = parse_collective_worker_config(&config_wire)?;
    let mut custody_wire = read_bounded_regular(
        custody_path,
        "protected single-party collective custody",
        MAX_COLLECTIVE_PARTY_CUSTODY_BYTES,
        true,
    )?;
    let result = (|| {
        let custody = parse_collective_party_custody(&custody_wire, &config_wire, &config)?;
        let params = BfvParams::fold_set();
        let (_party, contribution) = ThresholdParty::join_seeded(
            &config.keygen,
            custody.party,
            &params,
            &custody.threshold_root,
        )
        .map_err(|error| format!("threshold custody refused: {error:?}"))?;
        let contribution_wire = contribution.to_wire_bytes();
        let message = collective_party_artifact_message(
            custody.party,
            &collective_worker_config_digest(&config_wire),
            &contribution_wire,
        );
        let artifact = CollectivePartyArtifact {
            party: custody.party,
            contribution,
            signature: custody.decision_signer.sign(&message).to_bytes(),
        };
        let artifact_wire = artifact.to_wire_bytes(&config_wire);
        if artifact_wire.len() > MAX_COLLECTIVE_PARTY_ARTIFACT_BYTES as usize {
            return Err("party contribution artifact exceeds its allocation limit".to_string());
        }
        let digest = *blake3::hash(&artifact_wire).as_bytes();
        write_new_atomic(output_path, &artifact_wire, false)?;
        println!(
            "created public collective party contribution: {} (artifact {})",
            output_path.display(),
            hex32(&digest)
        );
        Ok(())
    })();
    custody_wire.fill(0);
    result
}

const MAX_COLLECTIVE_PROCESS_RECORD_BYTES: usize = 96 * 1024 * 1024;
const COLLECTIVE_PROCESS_PUMP: u8 = 0;
const COLLECTIVE_PROCESS_SIGN: u8 = 1;

struct CollectiveProcessPublic {
    config: CollectiveWorkerConfig,
    params: BfvParams,
    collective: CollectivePublicKey,
    task: CollectiveDecisionTask,
    session: PartyMpcSession,
    mask_session: MaskedDecryptSession,
}

fn load_collective_process_public(
    task_path: &Path,
    material_path: &Path,
    context_path: &Path,
    config_path: &Path,
    artifact_paths: &[PathBuf],
) -> Result<CollectiveProcessPublic, String> {
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
        context_path,
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
    let expected_context = parse_collective_worker_context(&context_wire)?;
    let config = parse_collective_worker_config(&config_wire)?;
    if artifact_paths.len() != config.keygen.n_parties() {
        return Err("process worker requires one public artifact per DKG party".to_string());
    }
    let params = BfvParams::fold_set();
    let material = DarkPoolPublicHostMaterial::from_wire_bytes(&material_wire, params.arc())
        .map_err(|error| format!("committed public host material refused: {error}"))?;
    let mut keygen_coordinator = KeygenCoordinator::new(config.keygen.clone(), params.clone());
    for (expected_party, path) in artifact_paths.iter().enumerate() {
        let artifact_wire = read_bounded_regular(
            path,
            "public collective party contribution",
            MAX_COLLECTIVE_PARTY_ARTIFACT_BYTES,
            false,
        )?;
        let artifact =
            CollectivePartyArtifact::from_wire_bytes(&artifact_wire, &config_wire, &config)?;
        if artifact.party != expected_party {
            return Err("process party artifacts must be supplied in exact DKG order".to_string());
        }
        keygen_coordinator
            .accept(artifact.contribution)
            .map_err(|error| format!("threshold contribution refused: {error:?}"))?;
    }
    let collective = keygen_coordinator
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
    // `MaskedCollectiveDecisionWorker` deliberately requires party objects, so
    // reconstruct the public equality session directly from the exact task.
    // Its nonce is the complete canonical task digest.
    let session = PartyMpcSession::equality(
        task.attestation_nonce()
            .map_err(|error| error.to_string())?,
        config.keygen.n_parties(),
        config.value_bits,
        params.plaintext_modulus(),
        config.timeout,
    )
    .map_err(|error| error.to_string())?;
    let range_end = 1u64
        .checked_shl(config.value_bits as u32)
        .ok_or_else(|| "collective equality value width is not shift-safe".to_string())?;
    if task.public_k() >= range_end || task.public_k() >= params.plaintext_modulus() {
        return Err("collective task public invariant is outside the equality range".to_string());
    }
    let invariant = task.invariant(&params).map_err(|error| error.to_string())?;
    let target = LeanCiphertext::from_fhe_bytes(
        &invariant.ct.to_bytes(),
        params.moduli(),
        params.degree(),
        invariant.plain_bound,
    )
    .map_err(|_| "collective task invariant ciphertext is malformed".to_string())?;
    let mask_session = MaskedDecryptSession::from_public(
        session.nonce(),
        config.keygen.n_parties(),
        1,
        target,
        &params,
    )
    .map_err(|error| format!("masked decrypt session refused: {error:?}"))?;
    Ok(CollectiveProcessPublic {
        config,
        params,
        collective,
        task,
        session,
        mask_session,
    })
}

fn collective_process_preprocessing_share_internal(args: &[String]) -> Result<(), String> {
    if args.len() != 4 {
        return Err("invalid internal preprocessing-share invocation".to_string());
    }
    let config_path = Path::new(&args[0]);
    let party = parse_usize(&args[1], "preprocessing party index")?;
    let config_wire = read_bounded_regular(
        config_path,
        "public collective worker configuration",
        MAX_COLLECTIVE_WORKER_CONFIG_BYTES,
        false,
    )?;
    let config = parse_collective_worker_config(&config_wire)?;
    let mut custody_wire = read_bounded_regular(
        Path::new(&args[2]),
        "protected single-party collective custody",
        MAX_COLLECTIVE_PARTY_CUSTODY_BYTES,
        true,
    )?;
    let parsed = parse_collective_party_custody(&custody_wire, &config_wire, &config);
    custody_wire.fill(0);
    let mut custody = parsed?;
    if custody.party != party {
        return Err("preprocessing-share custody names another party".to_string());
    }
    let mut output = Vec::with_capacity(MAX_COLLECTIVE_PREPROCESSING_SHARE_BYTES as usize);
    output.extend_from_slice(COLLECTIVE_PREPROCESSING_SHARE_MAGIC);
    output.extend_from_slice(&collective_worker_config_digest(&config_wire));
    output.extend_from_slice(&(party as u64).to_le_bytes());
    output.extend_from_slice(&custody.preprocessing_seed_share);
    output.extend_from_slice(&collective_worker_checksum(&output));
    custody.preprocessing_seed_share.fill(0);
    debug_assert_eq!(
        output.len(),
        MAX_COLLECTIVE_PREPROCESSING_SHARE_BYTES as usize
    );
    let result = write_new(Path::new(&args[3]), &output, true);
    output.fill(0);
    result
}

fn read_collective_preprocessing_share(
    path: &Path,
    config_wire: &[u8],
    expected_party: usize,
) -> Result<[u8; 32], String> {
    let mut wire = read_bounded_regular(
        path,
        "protected single-party preprocessing share",
        MAX_COLLECTIVE_PREPROCESSING_SHARE_BYTES,
        true,
    )?;
    let result = (|| {
        let content = checked_collective_worker_wire(
            &wire,
            COLLECTIVE_PREPROCESSING_SHARE_MAGIC,
            "protected single-party preprocessing share",
        )?;
        let mut input = CollectiveWorkerReader::new(content);
        input.expect_magic(COLLECTIVE_PREPROCESSING_SHARE_MAGIC)?;
        if input.array::<32>()? != collective_worker_config_digest(config_wire) {
            return Err("preprocessing share names another worker configuration".to_string());
        }
        if input.usize()? != expected_party {
            return Err("preprocessing shares are not in exact party order".to_string());
        }
        let share = input.array::<32>()?;
        input.finish()?;
        if share == [0; 32] {
            return Err("preprocessing seed share must be nonzero".to_string());
        }
        Ok(share)
    })();
    wire.fill(0);
    result
}

fn collective_process_preprocess_internal(args: &[String]) -> Result<(), String> {
    if args.len() < 9 || (args.len() - 5) % 2 != 0 {
        return Err("invalid internal collective preprocessing invocation".to_string());
    }
    let pairs = &args[5..];
    let artifact_paths = pairs
        .chunks_exact(2)
        .map(|pair| PathBuf::from(&pair[1]))
        .collect::<Vec<_>>();
    let public = load_collective_process_public(
        Path::new(&args[0]),
        Path::new(&args[1]),
        Path::new(&args[2]),
        Path::new(&args[3]),
        &artifact_paths,
    )?;
    if pairs.len() / 2 != public.config.keygen.n_parties() {
        return Err("internal preprocessing custody roster has the wrong size".to_string());
    }
    let config_wire = read_bounded_regular(
        Path::new(&args[3]),
        "public collective worker configuration",
        MAX_COLLECTIVE_WORKER_CONFIG_BYTES,
        false,
    )?;
    let mut preprocessing_seed = [0u8; 32];
    for (expected_party, pair) in pairs.chunks_exact(2).enumerate() {
        let mut party_share =
            read_collective_preprocessing_share(Path::new(&pair[0]), &config_wire, expected_party)?;
        for (combined, share) in preprocessing_seed.iter_mut().zip(party_share.iter()) {
            *combined ^= *share;
        }
        party_share.fill(0);
    }
    if preprocessing_seed == [0; 32] {
        return Err("combined split preprocessing seed must be nonzero".to_string());
    }
    let mut rng = StdRng::from_seed(preprocessing_seed);
    preprocessing_seed.fill(0);
    let triples =
        trusted_dealer_triples(&public.session, &mut rng).map_err(|error| error.to_string())?;
    let output_dir = Path::new(&args[4]);
    let metadata = fs::symlink_metadata(output_dir)
        .map_err(|error| format!("cannot inspect preprocessing directory: {error}"))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err("preprocessing target must be a real directory".to_string());
    }
    for (party, triple) in triples.into_iter().enumerate() {
        let mut wire = triple.to_wire_bytes().map_err(|error| error.to_string())?;
        let result = write_new(
            &output_dir.join(format!("party-{party}.triples")),
            &wire,
            true,
        );
        wire.fill(0);
        result?;
    }
    Ok(())
}

struct CollectiveProcessPeer {
    child: Child,
    input: ChildStdin,
    output: ChildStdout,
    label: String,
}

impl CollectiveProcessPeer {
    fn spawn(args: &[String], label: String) -> Result<Self, String> {
        let executable = std::env::current_exe()
            .map_err(|error| format!("cannot locate dark-amm-tool executable: {error}"))?;
        let mut child = Command::new(executable)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|error| format!("cannot spawn {label}: {error}"))?;
        let input = child
            .stdin
            .take()
            .ok_or_else(|| format!("{label} has no stdin pipe"))?;
        let output = child
            .stdout
            .take()
            .ok_or_else(|| format!("{label} has no stdout pipe"))?;
        Ok(Self {
            child,
            input,
            output,
            label,
        })
    }

    fn send(&mut self, bytes: &[u8]) -> Result<(), String> {
        write_collective_process_record(&mut self.input, bytes, &self.label)
    }

    fn receive(&mut self) -> Result<Vec<u8>, String> {
        read_collective_process_record(&mut self.output, &self.label)
    }

    fn wait(&mut self) -> Result<(), String> {
        let status = self
            .child
            .wait()
            .map_err(|error| format!("cannot wait for {}: {error}", self.label))?;
        if status.success() {
            Ok(())
        } else {
            Err(format!("{} exited with {status}", self.label))
        }
    }
}

impl Drop for CollectiveProcessPeer {
    fn drop(&mut self) {
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

fn write_collective_process_record<W: Write>(
    output: &mut W,
    bytes: &[u8],
    label: &str,
) -> Result<(), String> {
    if bytes.len() > MAX_COLLECTIVE_PROCESS_RECORD_BYTES {
        return Err(format!("{label} record exceeds its allocation limit"));
    }
    output
        .write_all(&(bytes.len() as u64).to_be_bytes())
        .and_then(|_| output.write_all(bytes))
        .and_then(|_| output.flush())
        .map_err(|error| format!("cannot write {label} record: {error}"))
}

fn read_collective_process_record<R: Read>(input: &mut R, label: &str) -> Result<Vec<u8>, String> {
    let mut length = [0u8; 8];
    input
        .read_exact(&mut length)
        .map_err(|error| format!("cannot read {label} record length: {error}"))?;
    let length = usize::try_from(u64::from_be_bytes(length))
        .map_err(|_| format!("{label} record length does not fit this platform"))?;
    if length > MAX_COLLECTIVE_PROCESS_RECORD_BYTES {
        return Err(format!("{label} record exceeds its allocation limit"));
    }
    let mut bytes = vec![0u8; length];
    input
        .read_exact(&mut bytes)
        .map_err(|error| format!("cannot read {label} record body: {error}"))?;
    Ok(bytes)
}

fn encode_process_vectors(vectors: &[Vec<u8>]) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(&(vectors.len() as u32).to_be_bytes());
    for vector in vectors {
        let len = u32::try_from(vector.len())
            .map_err(|_| "process vector length does not fit u32".to_string())?;
        out.extend_from_slice(&len.to_be_bytes());
        out.extend_from_slice(vector);
    }
    if out.len() > MAX_COLLECTIVE_PROCESS_RECORD_BYTES {
        return Err("process vector collection exceeds its allocation limit".to_string());
    }
    Ok(out)
}

fn decode_process_vectors(bytes: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    let mut input = CollectiveWorkerReader::new(bytes);
    let count = usize::try_from(u32::from_be_bytes(input.array()?))
        .map_err(|_| "process vector count does not fit this platform".to_string())?;
    if count > 4096 {
        return Err("process vector collection contains too many entries".to_string());
    }
    let mut vectors = Vec::with_capacity(count);
    for _ in 0..count {
        let len = usize::try_from(u32::from_be_bytes(input.array()?))
            .map_err(|_| "process vector length does not fit this platform".to_string())?;
        if len > MAX_COLLECTIVE_PROCESS_RECORD_BYTES {
            return Err("process vector exceeds its allocation limit".to_string());
        }
        let end = input
            .offset
            .checked_add(len)
            .filter(|end| *end <= input.bytes.len())
            .ok_or_else(|| "process vector is truncated".to_string())?;
        vectors.push(input.bytes[input.offset..end].to_vec());
        input.offset = end;
    }
    input.finish()?;
    Ok(vectors)
}

struct ProcessRoutedFrame {
    sender: usize,
    recipient: usize,
    sequence: u64,
    wire: Vec<u8>,
}

struct ProcessPumpResponse {
    complete: bool,
    transcript: Option<DecisionTranscript>,
    frames: Vec<ProcessRoutedFrame>,
}

fn encode_pump_request(frames: &[Vec<u8>]) -> Result<Vec<u8>, String> {
    let mut out = vec![COLLECTIVE_PROCESS_PUMP];
    out.extend_from_slice(&encode_process_vectors(frames)?);
    Ok(out)
}

fn decode_pump_request(bytes: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    if bytes.first() != Some(&COLLECTIVE_PROCESS_PUMP) {
        return Err("process expected a pump request".to_string());
    }
    decode_process_vectors(&bytes[1..])
}

fn encode_pump_response(
    complete: bool,
    transcript: Option<&DecisionTranscript>,
    frames: Vec<AuthenticatedEqualityFrame>,
) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.push(u8::from(complete));
    match transcript {
        Some(transcript) => {
            out.push(1);
            let wire = transcript
                .to_wire_bytes()
                .map_err(|error| error.to_string())?;
            out.extend_from_slice(&(wire.len() as u32).to_be_bytes());
            out.extend_from_slice(&wire);
        }
        None => out.push(0),
    }
    out.extend_from_slice(&(frames.len() as u32).to_be_bytes());
    for frame in frames {
        out.extend_from_slice(&(frame.sender() as u32).to_be_bytes());
        out.extend_from_slice(&(frame.recipient() as u32).to_be_bytes());
        out.extend_from_slice(&frame.sequence().to_be_bytes());
        let wire = frame.into_bytes();
        out.extend_from_slice(&(wire.len() as u32).to_be_bytes());
        out.extend_from_slice(&wire);
    }
    Ok(out)
}

fn decode_pump_response(bytes: &[u8]) -> Result<ProcessPumpResponse, String> {
    let mut input = CollectiveWorkerReader::new(bytes);
    let complete = match input.array::<1>()?[0] {
        0 => false,
        1 => true,
        _ => return Err("process response has invalid completion tag".to_string()),
    };
    let transcript = match input.array::<1>()?[0] {
        0 => None,
        1 => {
            let len = usize::try_from(u32::from_be_bytes(input.array()?))
                .map_err(|_| "process transcript length does not fit".to_string())?;
            let end = input
                .offset
                .checked_add(len)
                .filter(|end| *end <= input.bytes.len())
                .ok_or_else(|| "process transcript is truncated".to_string())?;
            let transcript = DecisionTranscript::from_wire_bytes(&input.bytes[input.offset..end])
                .map_err(|error| error.to_string())?;
            input.offset = end;
            Some(transcript)
        }
        _ => return Err("process response has invalid transcript tag".to_string()),
    };
    let count = usize::try_from(u32::from_be_bytes(input.array()?))
        .map_err(|_| "process response frame count does not fit".to_string())?;
    if count > 4096 {
        return Err("process response contains too many frames".to_string());
    }
    let mut frames = Vec::with_capacity(count);
    for _ in 0..count {
        let sender = usize::try_from(u32::from_be_bytes(input.array()?))
            .map_err(|_| "process sender does not fit".to_string())?;
        let recipient = usize::try_from(u32::from_be_bytes(input.array()?))
            .map_err(|_| "process recipient does not fit".to_string())?;
        let sequence = u64::from_be_bytes(input.array()?);
        let len = usize::try_from(u32::from_be_bytes(input.array()?))
            .map_err(|_| "process frame length does not fit".to_string())?;
        if len > 64 * 1024 {
            return Err("process equality frame exceeds its bound".to_string());
        }
        let end = input
            .offset
            .checked_add(len)
            .filter(|end| *end <= input.bytes.len())
            .ok_or_else(|| "process equality frame is truncated".to_string())?;
        let wire = input.bytes[input.offset..end].to_vec();
        input.offset = end;
        frames.push(ProcessRoutedFrame {
            sender,
            recipient,
            sequence,
            wire,
        });
    }
    input.finish()?;
    Ok(ProcessPumpResponse {
        complete,
        transcript,
        frames,
    })
}

fn decode_fixed_hex<const N: usize>(value: &str, label: &str) -> Result<[u8; N], String> {
    if value.len() != N * 2 || !value.is_ascii() {
        return Err(format!("{label} must contain exactly {} hex digits", N * 2));
    }
    let mut output = [0u8; N];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .map_err(|_| format!("{label} contains non-hexadecimal text"))?;
    }
    Ok(output)
}

fn transport_roster(
    config: &CollectiveWorkerConfig,
    coordinator_key: [u8; 32],
) -> Result<EqualityTransportRoster, String> {
    EqualityTransportRoster::new(
        config.decision_verifier.ordered_public_keys().to_vec(),
        coordinator_key,
    )
    .map_err(|error| error.to_string())
}

fn drain_party_machine(
    machine: &mut EqualityPartyMachine,
) -> Result<(Vec<AuthenticatedEqualityFrame>, bool), String> {
    let deadline = Instant::now() + Duration::from_millis(20);
    let mut quiet = 0usize;
    let mut frames = Vec::new();
    let mut complete = false;
    loop {
        let mut moved = false;
        while let Some(frame) = machine
            .try_next_frame()
            .map_err(|error| error.to_string())?
        {
            frames.push(frame);
            moved = true;
        }
        if !complete {
            let became_complete = machine
                .try_result()
                .map_err(|error| error.to_string())?
                .is_some();
            if became_complete {
                complete = true;
                // The runtime sends its final decision share immediately
                // before returning. Give the forwarding thread a full quiet
                // window so process exit cannot strand that last frame.
                quiet = 0;
            }
        }
        if moved {
            quiet = 0;
        } else {
            quiet += 1;
            let required_quiet = if complete { 50 } else { 3 };
            if quiet >= required_quiet || Instant::now() >= deadline {
                break;
            }
            std::thread::sleep(Duration::from_micros(100));
        }
    }
    Ok((frames, complete))
}

fn drain_coordinator_machine(
    machine: &mut EqualityCoordinatorMachine,
) -> Result<(Vec<AuthenticatedEqualityFrame>, Option<DecisionTranscript>), String> {
    let deadline = Instant::now() + Duration::from_millis(20);
    let mut quiet = 0usize;
    let mut frames = Vec::new();
    let mut transcript = None;
    loop {
        let mut moved = false;
        while let Some(frame) = machine
            .try_next_frame()
            .map_err(|error| error.to_string())?
        {
            frames.push(frame);
            moved = true;
        }
        if transcript.is_none() {
            transcript = machine
                .try_result()
                .map_err(|error| error.to_string())?
                .map(|result| result.transcript);
        }
        if moved {
            quiet = 0;
        } else {
            quiet += 1;
            if quiet >= 3 || Instant::now() >= deadline {
                break;
            }
            std::thread::sleep(Duration::from_micros(100));
        }
    }
    Ok((frames, transcript))
}

fn collective_process_party_internal(args: &[String]) -> Result<(), String> {
    if args.len() < 11 {
        return Err("invalid internal collective party invocation".to_string());
    }
    let party = parse_usize(&args[4], "party index")?;
    let artifact_paths = args[9..].iter().map(PathBuf::from).collect::<Vec<_>>();
    let public = load_collective_process_public(
        Path::new(&args[0]),
        Path::new(&args[1]),
        Path::new(&args[2]),
        Path::new(&args[3]),
        &artifact_paths,
    )?;
    if party >= public.config.keygen.n_parties()
        || artifact_paths.len() != public.config.keygen.n_parties()
    {
        return Err("internal party is outside the exact process roster".to_string());
    }
    let coordinator_key = decode_fixed_hex::<32>(&args[8], "coordinator transport key")?;
    let roster = transport_roster(&public.config, coordinator_key)?;
    let config_wire = read_bounded_regular(
        Path::new(&args[3]),
        "public collective worker configuration",
        MAX_COLLECTIVE_WORKER_CONFIG_BYTES,
        false,
    )?;
    let mut custody_wire = read_bounded_regular(
        Path::new(&args[5]),
        "protected single-party collective custody",
        MAX_COLLECTIVE_PARTY_CUSTODY_BYTES,
        true,
    )?;
    let custody_result =
        parse_collective_party_custody(&custody_wire, &config_wire, &public.config);
    custody_wire.fill(0);
    let custody = custody_result?;
    if custody.party != party {
        return Err("internal party custody names a different roster slot".to_string());
    }
    let artifact_wire = read_bounded_regular(
        Path::new(&args[6]),
        "public collective party contribution",
        MAX_COLLECTIVE_PARTY_ARTIFACT_BYTES,
        false,
    )?;
    let artifact =
        CollectivePartyArtifact::from_wire_bytes(&artifact_wire, &config_wire, &public.config)?;
    if artifact.party != party {
        return Err("internal party artifact names a different roster slot".to_string());
    }
    let (threshold_party, contribution) = ThresholdParty::join_seeded(
        &public.config.keygen,
        party,
        &public.params,
        &custody.threshold_root,
    )
    .map_err(|error| format!("threshold custody refused: {error:?}"))?;
    if contribution != artifact.contribution {
        return Err("internal party custody does not reproduce its public artifact".to_string());
    }
    let mut triple_wire = read_bounded_regular(
        Path::new(&args[7]),
        "protected equality preprocessing row",
        fhegg_fhe::mpc_party::MAX_TRIPLE_MATERIAL_BYTES as u64,
        true,
    )?;
    let triple_result = TripleMaterial::from_wire_bytes(&public.session, party, &triple_wire)
        .map_err(|error| error.to_string());
    triple_wire.fill(0);
    let triples = triple_result?;

    let (mask_state, contribution) = MaskedBoundaryParty::prepare(
        &public.mask_session,
        party,
        &public.params,
        &public.collective,
    )
    .map_err(|error| format!("party mask preparation refused: {error:?}"))?;
    let stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let mut output = stdout.lock();
    let mut input = stdin.lock();
    write_collective_process_record(
        &mut output,
        &contribution.to_wire_bytes(),
        "party mask contribution",
    )?;

    let masked_wire = read_collective_process_record(&mut input, "masked ciphertext")?;
    let masked_ciphertext = LeanCiphertext::from_fhe_bytes(
        &masked_wire,
        public.params.moduli(),
        public.params.degree(),
        public.params.plaintext_modulus() - 1,
    )
    .map_err(|_| "party received a malformed masked ciphertext".to_string())?;
    let decrypt_share = threshold_party
        .partial_decrypt(&masked_ciphertext, MIN_SMUDGE_BITS)
        .map_err(|error| format!("threshold decryption refused: {error:?}"))?;
    write_collective_process_record(
        &mut output,
        &decrypt_share.to_wire_bytes(),
        "party decrypt share",
    )?;

    let opening_packet = read_collective_process_record(&mut input, "masked opening material")?;
    let opening_vectors = decode_process_vectors(&opening_packet)?;
    let n = public.config.keygen.n_parties();
    if opening_vectors.len() != n * 2 {
        return Err("masked opening material has the wrong quorum shape".to_string());
    }
    let mut mask_coordinator =
        MaskedDecryptCoordinator::new(public.mask_session.clone(), public.params.clone());
    for (expected_party, wire) in opening_vectors[..n].iter().enumerate() {
        let contribution = EncryptedMaskContribution::from_wire_bytes(wire, &public.params)
            .map_err(|error| format!("mask contribution refused: {error:?}"))?;
        if contribution.party() != expected_party {
            return Err("masked opening contributions are not in exact party order".to_string());
        }
        mask_coordinator
            .accept(contribution)
            .map_err(|error| format!("mask contribution refused: {error:?}"))?;
    }
    let masked = mask_coordinator
        .finish()
        .map_err(|error| format!("masked ciphertext construction refused: {error:?}"))?;
    if masked.ciphertext() != &masked_ciphertext {
        return Err("masked opening material reconstructs a different ciphertext".to_string());
    }
    let opening = masked
        .open_framed(&opening_vectors[n..], &public.params)
        .map_err(|error| format!("masked opening refused: {error:?}"))?;
    let left_share = mask_state
        .derive_mod_t_share(&opening)
        .map_err(|error| format!("masked share derivation refused: {error:?}"))?[0];
    let mut ingress_rng = OsRng;
    let equality_input = PartyEqualityInput::new(
        &public.session,
        party,
        left_share,
        if party == 0 {
            public.task.public_k()
        } else {
            0
        },
        &mut ingress_rng,
    )
    .map_err(|error| error.to_string())?;
    let signing_key = custody.decision_signer.clone();
    let mut machine = EqualityPartyMachine::new(
        public.session.clone(),
        roster,
        party,
        signing_key.clone(),
        equality_input,
        triples,
    )
    .map_err(|error| error.to_string())?;
    loop {
        let request = read_collective_process_record(&mut input, "party equality request")?;
        let frames = decode_pump_request(&request)?;
        for frame in frames {
            machine
                .accept_frame(&frame)
                .map_err(|error| error.to_string())?;
        }
        let (frames, complete) = drain_party_machine(&mut machine)?;
        let response = encode_pump_response(complete, None, frames)?;
        write_collective_process_record(&mut output, &response, "party equality response")?;
        if complete {
            break;
        }
    }
    let sign_request = read_collective_process_record(&mut input, "party claim-sign request")?;
    if sign_request.len() != 33 || sign_request[0] != COLLECTIVE_PROCESS_SIGN {
        return Err("party received a malformed claim-sign request".to_string());
    }
    let claim_digest: [u8; 32] = sign_request[1..].try_into().unwrap();
    let signature = public
        .config
        .decision_verifier
        .sign_claim(&claim_digest, party, &signing_key)
        .map_err(|error| error.to_string())?;
    let mut signature_wire = Vec::with_capacity(68);
    signature_wire.extend_from_slice(&signature.signer_index.to_be_bytes());
    signature_wire.extend_from_slice(&signature.signature);
    write_collective_process_record(&mut output, &signature_wire, "party claim signature")
}

fn collective_process_coordinator_internal(args: &[String]) -> Result<(), String> {
    if args.len() < 8 {
        return Err("invalid internal collective coordinator invocation".to_string());
    }
    let artifact_paths = args[6..].iter().map(PathBuf::from).collect::<Vec<_>>();
    let public = load_collective_process_public(
        Path::new(&args[0]),
        Path::new(&args[1]),
        Path::new(&args[2]),
        Path::new(&args[3]),
        &artifact_paths,
    )?;
    let coordinator_key = decode_fixed_hex::<32>(&args[5], "coordinator transport key")?;
    let roster = transport_roster(&public.config, coordinator_key)?;
    let mut seed_wire = read_bounded_regular(
        Path::new(&args[4]),
        "protected coordinator transport seed",
        32,
        true,
    )?;
    let seed_result: Result<[u8; 32], String> = seed_wire
        .as_slice()
        .try_into()
        .map_err(|_| "coordinator transport seed must contain exactly 32 bytes".to_string());
    let mut seed = seed_result?;
    seed_wire.fill(0);
    let signing_key = SigningKey::from_bytes(&seed);
    seed.fill(0);
    if signing_key.verifying_key().to_bytes() != coordinator_key {
        return Err("coordinator transport seed does not match its public key".to_string());
    }
    let mut machine = EqualityCoordinatorMachine::new(public.session, roster, signing_key)
        .map_err(|error| error.to_string())?;
    let stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let mut output = stdout.lock();
    let mut input = stdin.lock();
    loop {
        let request = read_collective_process_record(&mut input, "coordinator equality request")?;
        let frames = decode_pump_request(&request)?;
        for frame in frames {
            machine
                .accept_frame(&frame)
                .map_err(|error| error.to_string())?;
        }
        let (frames, transcript) = drain_coordinator_machine(&mut machine)?;
        let complete = transcript.is_some();
        let response = encode_pump_response(complete, transcript.as_ref(), frames)?;
        write_collective_process_record(&mut output, &response, "coordinator equality response")?;
        if complete {
            return Ok(());
        }
    }
}

fn collective_decide_split(args: &[String]) -> Result<(), String> {
    if args.len() < 9 || (args.len() - 5) % 2 != 0 {
        return Err("usage: dark-amm-tool collective-decide-split <task-file> <committed-public-material-file> <expected-context-file> <public-worker-config-file> <new-decision-bundle-file> <party-custody-0> <party-artifact-0> [<party-custody-N> <party-artifact-N> ...]".to_string());
    }
    let task_path = Path::new(&args[0]);
    let material_path = Path::new(&args[1]);
    let expected_context_path = Path::new(&args[2]);
    let config_path = Path::new(&args[3]);
    let output_path = Path::new(&args[4]);
    let party_files = &args[5..];
    ensure_absent(output_path, "decision bundle")?;
    let artifact_paths = party_files
        .chunks_exact(2)
        .map(|pair| PathBuf::from(&pair[1]))
        .collect::<Vec<_>>();
    let public = load_collective_process_public(
        task_path,
        material_path,
        expected_context_path,
        config_path,
        &artifact_paths,
    )?;
    let n = public.config.keygen.n_parties();
    if party_files.len() / 2 != n {
        return Err(
            "split worker must receive exactly one custody/artifact pair per DKG party".to_string(),
        );
    }

    let process_dir = unique_staging_path(output_path)?;
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder
        .create(&process_dir)
        .map_err(|error| format!("cannot create collective process directory: {error}"))?;
    let process_result = (|| {
        let executable = std::env::current_exe()
            .map_err(|error| format!("cannot locate dark-amm-tool executable: {error}"))?;
        let mut preprocessing_share_paths = Vec::with_capacity(n);
        for (party, pair) in party_files.chunks_exact(2).enumerate() {
            let share_path = process_dir.join(format!("party-{party}.preprocessing-share"));
            let extraction = Command::new(&executable)
                .arg("collective-process-preprocessing-share-internal")
                .arg(config_path)
                .arg(party.to_string())
                .arg(&pair[0])
                .arg(&share_path)
                .output()
                .map_err(|error| {
                    format!("cannot spawn preprocessing-share party {party}: {error}")
                })?;
            if !extraction.status.success() {
                return Err(format!(
                    "preprocessing-share party {party} refused: {}",
                    String::from_utf8_lossy(&extraction.stderr)
                ));
            }
            preprocessing_share_paths.push(share_path);
        }
        let mut preprocessing_args = vec![
            "collective-process-preprocess-internal".to_string(),
            task_path.display().to_string(),
            material_path.display().to_string(),
            expected_context_path.display().to_string(),
            config_path.display().to_string(),
            process_dir.display().to_string(),
        ];
        for (party, share_path) in preprocessing_share_paths.iter().enumerate() {
            preprocessing_args.push(share_path.display().to_string());
            preprocessing_args.push(party_files[party * 2 + 1].clone());
        }
        let preprocessing = Command::new(&executable)
            .args(&preprocessing_args)
            .output()
            .map_err(|error| format!("cannot spawn trusted preprocessing process: {error}"))?;
        if !preprocessing.status.success() {
            return Err(format!(
                "trusted preprocessing process refused: {}",
                String::from_utf8_lossy(&preprocessing.stderr)
            ));
        }

        let mut coordinator_seed = [0u8; 32];
        rand::RngCore::fill_bytes(&mut OsRng, &mut coordinator_seed);
        let coordinator_signer = SigningKey::from_bytes(&coordinator_seed);
        let coordinator_public = coordinator_signer.verifying_key().to_bytes();
        drop(coordinator_signer);
        let coordinator_seed_path = process_dir.join("coordinator.transport-key");
        let seed_write = write_new(&coordinator_seed_path, &coordinator_seed, true);
        coordinator_seed.fill(0);
        seed_write?;
        let coordinator_public_hex = hex32(&coordinator_public);

        let mut coordinator_args = vec![
            "collective-process-coordinator-internal".to_string(),
            task_path.display().to_string(),
            material_path.display().to_string(),
            expected_context_path.display().to_string(),
            config_path.display().to_string(),
            coordinator_seed_path.display().to_string(),
            coordinator_public_hex.clone(),
        ];
        coordinator_args.extend(artifact_paths.iter().map(|path| path.display().to_string()));
        let mut coordinator = CollectiveProcessPeer::spawn(
            &coordinator_args,
            "collective equality coordinator".to_string(),
        )?;
        let mut parties = Vec::with_capacity(n);
        for (party, pair) in party_files.chunks_exact(2).enumerate() {
            let mut party_args = vec![
                "collective-process-party-internal".to_string(),
                task_path.display().to_string(),
                material_path.display().to_string(),
                expected_context_path.display().to_string(),
                config_path.display().to_string(),
                party.to_string(),
                pair[0].clone(),
                pair[1].clone(),
                process_dir
                    .join(format!("party-{party}.triples"))
                    .display()
                    .to_string(),
                coordinator_public_hex.clone(),
            ];
            party_args.extend(artifact_paths.iter().map(|path| path.display().to_string()));
            parties.push(CollectiveProcessPeer::spawn(
                &party_args,
                format!("collective equality party {party}"),
            )?);
        }

        let mut contribution_wires = Vec::with_capacity(n);
        let mut mask_coordinator =
            MaskedDecryptCoordinator::new(public.mask_session.clone(), public.params.clone());
        for (expected_party, party) in parties.iter_mut().enumerate() {
            let wire = party.receive()?;
            let contribution = EncryptedMaskContribution::from_wire_bytes(&wire, &public.params)
                .map_err(|error| format!("mask contribution refused: {error:?}"))?;
            if contribution.party() != expected_party {
                return Err(
                    "party process emitted a mask contribution for another slot".to_string()
                );
            }
            mask_coordinator
                .accept(contribution)
                .map_err(|error| format!("mask contribution refused: {error:?}"))?;
            contribution_wires.push(wire);
        }
        let masked = mask_coordinator
            .finish()
            .map_err(|error| format!("masked ciphertext construction refused: {error:?}"))?;
        let masked_wire = masked.ciphertext().to_fhe_bytes();
        for party in &mut parties {
            party.send(&masked_wire)?;
        }
        let mut decrypt_shares = Vec::with_capacity(n);
        for party in &mut parties {
            decrypt_shares.push(party.receive()?);
        }
        // Verify the complete threshold opening in the supervisor as well as
        // independently inside every party process. This value is one-time
        // padded; it is not an equality operand or a reserve opening.
        masked
            .open_framed(&decrypt_shares, &public.params)
            .map_err(|error| format!("masked opening refused: {error:?}"))?;
        let opening_packet = encode_process_vectors(
            &contribution_wires
                .iter()
                .chain(decrypt_shares.iter())
                .cloned()
                .collect::<Vec<_>>(),
        )?;
        for party in &mut parties {
            party.send(&opening_packet)?;
        }

        let mut party_queues = vec![Vec::<Vec<u8>>::new(); n];
        let mut coordinator_queue = Vec::<Vec<u8>>::new();
        let mut party_complete = vec![false; n];
        let mut coordinator_complete = false;
        let mut transcript = None;
        let deadline = Instant::now() + public.config.timeout;
        while !(coordinator_complete && party_complete.iter().all(|complete| *complete)) {
            if Instant::now() >= deadline {
                return Err("cross-process equality exceeded its configured timeout".to_string());
            }
            for party_index in 0..n {
                if party_complete[party_index] {
                    continue;
                }
                let request = encode_pump_request(&std::mem::take(&mut party_queues[party_index]))?;
                parties[party_index].send(&request)?;
                let response = decode_pump_response(&parties[party_index].receive()?)?;
                if response.transcript.is_some() {
                    return Err("party process attempted to emit a decision transcript".to_string());
                }
                party_complete[party_index] = response.complete;
                for frame in response.frames {
                    if frame.sender != party_index || frame.recipient > n {
                        return Err("party process emitted an invalid public route".to_string());
                    }
                    let _sequence = frame.sequence;
                    if frame.recipient == n {
                        coordinator_queue.push(frame.wire);
                    } else {
                        party_queues[frame.recipient].push(frame.wire);
                    }
                }
            }
            if !coordinator_complete {
                let request = encode_pump_request(&std::mem::take(&mut coordinator_queue))?;
                coordinator.send(&request)?;
                let response = decode_pump_response(&coordinator.receive()?)?;
                coordinator_complete = response.complete;
                if response.transcript.is_some() {
                    if transcript.is_some() || !coordinator_complete {
                        return Err(
                            "coordinator emitted a duplicate or premature transcript".to_string()
                        );
                    }
                    transcript = response.transcript;
                }
                for frame in response.frames {
                    if frame.sender != n || frame.recipient >= n {
                        return Err(
                            "coordinator process emitted an invalid public route".to_string()
                        );
                    }
                    let _sequence = frame.sequence;
                    party_queues[frame.recipient].push(frame.wire);
                }
            }
        }
        if party_queues.iter().any(|queue| !queue.is_empty()) || !coordinator_queue.is_empty() {
            return Err(
                "equality processes completed with undelivered authenticated frames".to_string(),
            );
        }
        let transcript = transcript
            .ok_or_else(|| "coordinator completed without a reveal-only transcript".to_string())?;
        let decision =
            MaskedCollectiveDecision::from_external_transcript(public.session.clone(), transcript)
                .map_err(|error| error.to_string())?;
        let draft = decision
            .draft_receipt(&public.config.decision_verifier)
            .map_err(|error| error.to_string())?;
        let mut sign_request = Vec::with_capacity(33);
        sign_request.push(COLLECTIVE_PROCESS_SIGN);
        sign_request.extend_from_slice(&draft.claim_digest());
        let mut signatures = Vec::with_capacity(n);
        for (party_index, party) in parties.iter_mut().enumerate() {
            party.send(&sign_request)?;
            let wire = party.receive()?;
            if wire.len() != 68 {
                return Err("party process emitted a malformed FHDAR signature".to_string());
            }
            let signer_index = u32::from_be_bytes(wire[..4].try_into().unwrap());
            if signer_index as usize != party_index {
                return Err("party process emitted an FHDAR signature for another slot".to_string());
            }
            signatures.push(PartyClaimSignature {
                signer_index,
                signature: wire[4..].try_into().unwrap(),
            });
        }
        for party in &mut parties {
            party.wait()?;
        }
        coordinator.wait()?;

        // Only after all operand-holding processes have exited do we assemble
        // the public FHDAR001 receipt and publish the commit bundle.
        let receipt = decision
            .assemble_attested_receipt(&public.config.decision_verifier, &signatures)
            .map_err(|error| error.to_string())?;
        let bundle = CollectiveDecisionBundle::new(decision.transcript().clone(), receipt);
        let bundle_wire = bundle.to_wire_bytes().map_err(|error| error.to_string())?;
        let bundle_digest = *blake3::hash(&bundle_wire).as_bytes();
        write_new_atomic(output_path, &bundle_wire, false)?;
        println!(
            "created public process-separated Dark Bazaar decision bundle: {} (task {}, bundle {}, {} parties + coordinator exited)",
            output_path.display(),
            hex32(
                &public
                    .task
                    .attestation_nonce()
                    .map_err(|error| error.to_string())?
            ),
            hex32(&bundle_digest),
            n,
        );
        Ok(())
    })();
    let cleanup = fs::remove_dir_all(&process_dir)
        .map_err(|error| format!("cannot remove collective process directory: {error}"));
    process_result?;
    cleanup
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

fn parse_collective_party_custody(
    bytes: &[u8],
    config_wire: &[u8],
    config: &CollectiveWorkerConfig,
) -> Result<CollectivePartyCustody, String> {
    let content = checked_collective_worker_wire(
        bytes,
        COLLECTIVE_PARTY_CUSTODY_MAGIC,
        "protected single-party collective custody",
    )?;
    let mut input = CollectiveWorkerReader::new(content);
    input.expect_magic(COLLECTIVE_PARTY_CUSTODY_MAGIC)?;
    if input.array::<32>()? != collective_worker_config_digest(config_wire) {
        return Err("single-party custody names a different worker configuration".to_string());
    }
    let party = input.usize()?;
    let threshold_root = input.array()?;
    let preprocessing_seed_share = input.array()?;
    let mut signer_bytes: [u8; 32] = input.array()?;
    input.finish()?;
    if party >= config.keygen.n_parties()
        || threshold_root == [0; 32]
        || preprocessing_seed_share == [0; 32]
    {
        signer_bytes.fill(0);
        return Err("single-party custody has an invalid index or zero secret".to_string());
    }
    let decision_signer = SigningKey::from_bytes(&signer_bytes);
    signer_bytes.fill(0);
    if decision_signer.verifying_key().to_bytes()
        != config.decision_verifier.ordered_public_keys()[party]
    {
        return Err("single-party signer key does not match its public roster slot".to_string());
    }
    Ok(CollectivePartyCustody {
        party,
        threshold_root,
        preprocessing_seed_share,
        decision_signer,
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

fn collective_worker_config_digest(config_wire: &[u8]) -> [u8; 32] {
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-dark-amm-collective-worker-configuration-v1");
    hash.update(&(config_wire.len() as u64).to_le_bytes());
    hash.update(config_wire);
    *hash.finalize().as_bytes()
}

fn collective_party_artifact_message(
    party: usize,
    config_digest: &[u8; 32],
    contribution_wire: &[u8],
) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(COLLECTIVE_PARTY_ARTIFACT_SIGNATURE_DOMAIN);
    hash.update(&(party as u64).to_le_bytes());
    hash.update(config_digest);
    hash.update(&(contribution_wire.len() as u64).to_le_bytes());
    hash.update(blake3::hash(contribution_wire).as_bytes());
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

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], String> {
        let len = self.usize()?;
        if len > max {
            return Err("collective worker length-delimited field exceeds its limit".to_string());
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| "collective worker length-delimited field is truncated".to_string())?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
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
