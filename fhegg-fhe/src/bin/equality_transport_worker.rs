//! Standalone authenticated fhEgg equality worker.
//!
//! Each invocation owns exactly one role: one party (local mod-t operands,
//! ingress randomness, signing key, and Beaver row) or the reveal-only
//! coordinator (signing key only). A supervisor moves bounded, authenticated
//! frames between long-running processes over length-prefixed JSON requests.
//! `preprocess` creates per-party trusted-dealer rows without inputs, while
//! `provision-party`/`provision-coordinator` bind protected custody to the exact
//! public config and roster role without placing secret operands on argv.
//! Peer-ingress frames contain plaintext Boolean shares and therefore require
//! confidential direct party channels in deployment; they must not be relayed
//! through an eavesdropping coordinator.
//!
//! The arithmetic remains semi-honest and uses trusted preprocessing. Ed25519
//! authenticates transport; it does not prove honest share or triple formation.

use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::transport::{
    AuthenticatedEqualityFrame, EqualityCoordinatorMachine, EqualityPartyMachine,
    EqualityTransportRoster,
};
use fhegg_fhe::mpc_party::{
    trusted_dealer_triples, PartyEqualityInput, PartyMpcSession, PartyReport, TripleMaterial,
    MAX_TRIPLE_MATERIAL_BYTES,
};
use rand::rngs::StdRng;
use rand::SeedableRng;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MAX_CONFIG_BYTES: u64 = 64 * 1024;
const MAX_RPC_BYTES: usize = 40 * 1024 * 1024;
const MAX_INPUT_FRAMES: usize = 256;
const MAX_OUTPUT_FRAMES: usize = 32;
const MAX_AUTHENTICATED_FRAME_BYTES: usize = 64 * 1024;
const MAX_WORKER_PARTIES: usize = 64;
const MAX_TIMEOUT_MS: u64 = 5 * 60 * 1000;
const PARTY_CUSTODY_MAGIC: &[u8; 8] = b"FHEQPC01";
const COORDINATOR_CUSTODY_MAGIC: &[u8; 8] = b"FHEQCC01";
const PREPROCESSING_CUSTODY_MAGIC: &[u8; 8] = b"FHEQTR01";
const PARTY_CUSTODY_BYTES: usize = 8 + 32 + 4 + 32 + 32 + 8 + 8 + 32;
const COORDINATOR_CUSTODY_BYTES: usize = 8 + 32 + 32 + 32;
const PREPROCESSING_CUSTODY_OVERHEAD: usize = 8 + 32 + 4 + 8 + 32;
const CUSTODY_CHECKSUM_DOMAIN: &[u8] = b"fhegg/equality-worker-custody-checksum/v1";

fn main() {
    if let Err(error) = run() {
        eprintln!("fhegg-equality-worker: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match args.as_slice() {
        [role, config, party, custody, triples] if role == "party" => {
            serve_party(
                Path::new(config),
                parse_usize(party, "party")?,
                Path::new(custody),
                Path::new(triples),
            )
        }
        [role, config, custody] if role == "coordinator" => {
            serve_coordinator(Path::new(config), Path::new(custody))
        }
        [command, config, dealer_seed, output_dir] if command == "preprocess" => {
            preprocess(
                Path::new(config),
                Path::new(dealer_seed),
                Path::new(output_dir),
            )
        }
        [command, config, party, signing_seed, ingress_seed, operands, output]
            if command == "provision-party" =>
        {
            provision_party(
                Path::new(config),
                parse_usize(party, "party")?,
                Path::new(signing_seed),
                Path::new(ingress_seed),
                Path::new(operands),
                Path::new(output),
            )
        }
        [command, config, signing_seed, output] if command == "provision-coordinator" => {
            provision_coordinator(
                Path::new(config),
                Path::new(signing_seed),
                Path::new(output),
            )
        }
        _ => Err("usage: fhegg-equality-worker party <public-config.json> <party-index> <protected-party-custody> <protected-triples> | coordinator <public-config.json> <protected-coordinator-custody> | preprocess <public-config.json> <protected-dealer-seed> <existing-output-directory> | provision-party <public-config.json> <party-index> <protected-signing-seed> <protected-ingress-seed> <protected-two-u64-be-operands> <new-custody> | provision-coordinator <public-config.json> <protected-signing-seed> <new-custody>".to_string()),
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PublicConfig {
    version: u32,
    nonce_hex: String,
    value_bits: usize,
    plaintext_modulus: u64,
    timeout_ms: u64,
    party_public_keys_hex: Vec<String>,
    coordinator_public_key_hex: String,
}

struct LoadedConfig {
    digest: [u8; 32],
    session: PartyMpcSession,
    roster: EqualityTransportRoster,
    party_public_keys: Vec<[u8; 32]>,
    coordinator_public_key: [u8; 32],
}

fn load_config(path: &Path) -> Result<LoadedConfig, String> {
    let bytes = read_bounded_regular(path, "public equality config", MAX_CONFIG_BYTES, false)?;
    let digest: [u8; 32] = Sha256::digest(&bytes).into();
    let config: PublicConfig = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid public equality config: {error}"))?;
    if config.version != 1 {
        return Err("unsupported public equality config version".to_string());
    }
    if config.party_public_keys_hex.len() < 2
        || config.party_public_keys_hex.len() > MAX_WORKER_PARTIES
    {
        return Err(format!(
            "public equality roster must contain 2..={MAX_WORKER_PARTIES} parties"
        ));
    }
    if config.timeout_ms == 0 || config.timeout_ms > MAX_TIMEOUT_MS {
        return Err(format!(
            "public equality timeout must be 1..={MAX_TIMEOUT_MS} milliseconds"
        ));
    }
    let nonce = decode_hex_array::<32>(&config.nonce_hex, "session nonce")?;
    let party_keys = config
        .party_public_keys_hex
        .iter()
        .map(|key| decode_hex_array::<32>(key, "party public key"))
        .collect::<Result<Vec<_>, _>>()?;
    let coordinator_key =
        decode_hex_array::<32>(&config.coordinator_public_key_hex, "coordinator public key")?;
    let session = PartyMpcSession::equality(
        nonce,
        party_keys.len(),
        config.value_bits,
        config.plaintext_modulus,
        Duration::from_millis(config.timeout_ms),
    )
    .map_err(|error| error.to_string())?;
    let roster = EqualityTransportRoster::new(party_keys.clone(), coordinator_key)
        .map_err(|error| error.to_string())?;
    Ok(LoadedConfig {
        digest,
        session,
        roster,
        party_public_keys: party_keys,
        coordinator_public_key: coordinator_key,
    })
}

struct PartyCustody {
    signing_seed: [u8; 32],
    ingress_seed: [u8; 32],
    left_mod_t_share: [u8; 8],
    right_mod_t_share: [u8; 8],
}

fn read_party_custody(
    path: &Path,
    config_digest: [u8; 32],
    expected_party: usize,
) -> Result<PartyCustody, String> {
    let mut bytes = read_bounded_regular(
        path,
        "protected equality party custody",
        PARTY_CUSTODY_BYTES as u64,
        true,
    )?;
    let result = (|| {
        if bytes.len() != PARTY_CUSTODY_BYTES || &bytes[..8] != PARTY_CUSTODY_MAGIC {
            return Err("malformed protected equality party custody".to_string());
        }
        verify_custody_checksum(&bytes)?;
        if bytes[8..40] != config_digest {
            return Err("party custody names a different public config".to_string());
        }
        let party = usize::try_from(u32::from_be_bytes(bytes[40..44].try_into().unwrap()))
            .map_err(|_| "party custody index does not fit this platform".to_string())?;
        if party != expected_party {
            return Err("party custody names a different role slot".to_string());
        }
        Ok(PartyCustody {
            signing_seed: bytes[44..76].try_into().unwrap(),
            ingress_seed: bytes[76..108].try_into().unwrap(),
            left_mod_t_share: bytes[108..116].try_into().unwrap(),
            right_mod_t_share: bytes[116..124].try_into().unwrap(),
        })
    })();
    bytes.fill(0);
    result
}

fn read_coordinator_custody(path: &Path, config_digest: [u8; 32]) -> Result<[u8; 32], String> {
    let mut bytes = read_bounded_regular(
        path,
        "protected equality coordinator custody",
        COORDINATOR_CUSTODY_BYTES as u64,
        true,
    )?;
    let result = (|| {
        if bytes.len() != COORDINATOR_CUSTODY_BYTES || &bytes[..8] != COORDINATOR_CUSTODY_MAGIC {
            return Err("malformed protected equality coordinator custody".to_string());
        }
        verify_custody_checksum(&bytes)?;
        if bytes[8..40] != config_digest {
            return Err("coordinator custody names a different public config".to_string());
        }
        Ok(bytes[40..72].try_into().unwrap())
    })();
    bytes.fill(0);
    result
}

fn read_preprocessing_custody(
    path: &Path,
    config_digest: [u8; 32],
    session: &PartyMpcSession,
    expected_party: usize,
) -> Result<TripleMaterial, String> {
    let mut bytes = read_bounded_regular(
        path,
        "protected equality preprocessing",
        (MAX_TRIPLE_MATERIAL_BYTES + PREPROCESSING_CUSTODY_OVERHEAD) as u64,
        true,
    )?;
    let result = (|| {
        if bytes.len() < PREPROCESSING_CUSTODY_OVERHEAD
            || &bytes[..8] != PREPROCESSING_CUSTODY_MAGIC
        {
            return Err("malformed protected equality preprocessing custody".to_string());
        }
        verify_custody_checksum(&bytes)?;
        if bytes[8..40] != config_digest {
            return Err("preprocessing custody names a different public config".to_string());
        }
        let party = usize::try_from(u32::from_be_bytes(bytes[40..44].try_into().unwrap()))
            .map_err(|_| "preprocessing custody party does not fit this platform".to_string())?;
        if party != expected_party {
            return Err("preprocessing custody names a different party slot".to_string());
        }
        let wire_len = usize::try_from(u64::from_be_bytes(bytes[44..52].try_into().unwrap()))
            .map_err(|_| "preprocessing custody length does not fit this platform".to_string())?;
        let wire_end = 52usize
            .checked_add(wire_len)
            .ok_or_else(|| "preprocessing custody length overflow".to_string())?;
        if wire_len > MAX_TRIPLE_MATERIAL_BYTES || wire_end + 32 != bytes.len() {
            return Err("preprocessing custody has an invalid bounded length".to_string());
        }
        TripleMaterial::from_wire_bytes(session, expected_party, &bytes[52..wire_end])
            .map_err(|error| error.to_string())
    })();
    bytes.fill(0);
    result
}

fn verify_custody_checksum(bytes: &[u8]) -> Result<(), String> {
    let checksum_start = bytes
        .len()
        .checked_sub(32)
        .ok_or_else(|| "equality custody is truncated".to_string())?;
    let mut hash = Sha256::new();
    hash.update((CUSTODY_CHECKSUM_DOMAIN.len() as u64).to_be_bytes());
    hash.update(CUSTODY_CHECKSUM_DOMAIN);
    hash.update((checksum_start as u64).to_be_bytes());
    hash.update(&bytes[..checksum_start]);
    if bytes[checksum_start..] != hash.finalize()[..] {
        return Err("equality custody checksum mismatch".to_string());
    }
    Ok(())
}

fn append_custody_checksum(bytes: &mut Vec<u8>) {
    let mut hash = Sha256::new();
    hash.update((CUSTODY_CHECKSUM_DOMAIN.len() as u64).to_be_bytes());
    hash.update(CUSTODY_CHECKSUM_DOMAIN);
    hash.update((bytes.len() as u64).to_be_bytes());
    hash.update(&*bytes);
    bytes.extend_from_slice(&hash.finalize());
}

fn provision_party(
    config_path: &Path,
    party: usize,
    signing_seed_path: &Path,
    ingress_seed_path: &Path,
    operands_path: &Path,
    output_path: &Path,
) -> Result<(), String> {
    let loaded = load_config(config_path)?;
    if party >= loaded.party_public_keys.len() {
        return Err("party role is outside the public roster".to_string());
    }
    let mut signing_wire = read_bounded_regular(
        signing_seed_path,
        "protected party transport signing seed",
        32,
        true,
    )?;
    let mut ingress_wire =
        read_bounded_regular(ingress_seed_path, "protected party ingress seed", 32, true)?;
    let mut operands_wire =
        read_bounded_regular(operands_path, "protected party operand shares", 16, true)?;
    let result = (|| {
        let mut signing_seed: [u8; 32] = signing_wire.as_slice().try_into().map_err(|_| {
            "party transport signing seed must contain exactly 32 bytes".to_string()
        })?;
        if SigningKey::from_bytes(&signing_seed)
            .verifying_key()
            .to_bytes()
            != loaded.party_public_keys[party]
        {
            return Err("party transport signing seed does not match its roster slot".to_string());
        }
        let mut ingress_seed: [u8; 32] = ingress_wire
            .as_slice()
            .try_into()
            .map_err(|_| "party ingress seed must contain exactly 32 bytes".to_string())?;
        let mut operands: [u8; 16] = operands_wire.as_slice().try_into().map_err(|_| {
            "party operand file must contain exactly two big-endian u64 shares".to_string()
        })?;
        let left = u64::from_be_bytes(operands[..8].try_into().unwrap());
        let right = u64::from_be_bytes(operands[8..].try_into().unwrap());
        if left >= loaded.session.plaintext_modulus() || right >= loaded.session.plaintext_modulus()
        {
            return Err("party operand share is outside the public plaintext modulus".to_string());
        }
        let mut custody = Vec::with_capacity(PARTY_CUSTODY_BYTES);
        custody.extend_from_slice(PARTY_CUSTODY_MAGIC);
        custody.extend_from_slice(&loaded.digest);
        custody.extend_from_slice(&(party as u32).to_be_bytes());
        custody.extend_from_slice(&signing_seed);
        custody.extend_from_slice(&ingress_seed);
        custody.extend_from_slice(&operands);
        append_custody_checksum(&mut custody);
        debug_assert_eq!(custody.len(), PARTY_CUSTODY_BYTES);
        let write = write_new_secret(output_path, &custody);
        signing_seed.fill(0);
        ingress_seed.fill(0);
        operands.fill(0);
        custody.fill(0);
        write
    })();
    signing_wire.fill(0);
    ingress_wire.fill(0);
    operands_wire.fill(0);
    result
}

fn provision_coordinator(
    config_path: &Path,
    signing_seed_path: &Path,
    output_path: &Path,
) -> Result<(), String> {
    let loaded = load_config(config_path)?;
    let mut signing_wire = read_bounded_regular(
        signing_seed_path,
        "protected coordinator transport signing seed",
        32,
        true,
    )?;
    let result = (|| {
        let mut signing_seed: [u8; 32] = signing_wire.as_slice().try_into().map_err(|_| {
            "coordinator transport signing seed must contain exactly 32 bytes".to_string()
        })?;
        if SigningKey::from_bytes(&signing_seed)
            .verifying_key()
            .to_bytes()
            != loaded.coordinator_public_key
        {
            return Err(
                "coordinator transport signing seed does not match the public roster".to_string(),
            );
        }
        let mut custody = Vec::with_capacity(COORDINATOR_CUSTODY_BYTES);
        custody.extend_from_slice(COORDINATOR_CUSTODY_MAGIC);
        custody.extend_from_slice(&loaded.digest);
        custody.extend_from_slice(&signing_seed);
        append_custody_checksum(&mut custody);
        debug_assert_eq!(custody.len(), COORDINATOR_CUSTODY_BYTES);
        let write = write_new_secret(output_path, &custody);
        signing_seed.fill(0);
        custody.fill(0);
        write
    })();
    signing_wire.fill(0);
    result
}

fn serve_party(
    config_path: &Path,
    party: usize,
    custody_path: &Path,
    triples_path: &Path,
) -> Result<(), String> {
    let loaded = load_config(config_path)?;
    if party >= loaded.roster.n_parties() {
        return Err("party role is outside the public roster".to_string());
    }
    let mut custody = read_party_custody(custody_path, loaded.digest, party)?;
    let triples = read_preprocessing_custody(triples_path, loaded.digest, &loaded.session, party)?;
    let construction = (|| {
        let mut ingress_rng = StdRng::from_seed(custody.ingress_seed);
        let input = PartyEqualityInput::new(
            &loaded.session,
            party,
            u64::from_be_bytes(custody.left_mod_t_share),
            u64::from_be_bytes(custody.right_mod_t_share),
            &mut ingress_rng,
        )
        .map_err(|error| error.to_string())?;
        EqualityPartyMachine::new(
            loaded.session,
            loaded.roster,
            party,
            SigningKey::from_bytes(&custody.signing_seed),
            input,
            triples,
        )
        .map_err(|error| error.to_string())
    })();
    custody.signing_seed.fill(0);
    custody.ingress_seed.fill(0);
    custody.left_mod_t_share.fill(0);
    custody.right_mod_t_share.fill(0);
    serve(Worker::Party {
        machine: construction?,
        completion_sent: false,
    })
}

fn serve_coordinator(config_path: &Path, custody_path: &Path) -> Result<(), String> {
    let loaded = load_config(config_path)?;
    let mut signing_seed = read_coordinator_custody(custody_path, loaded.digest)?;
    let construction = EqualityCoordinatorMachine::new(
        loaded.session,
        loaded.roster,
        SigningKey::from_bytes(&signing_seed),
    )
    .map_err(|error| error.to_string());
    signing_seed.fill(0);
    serve(Worker::Coordinator {
        machine: construction?,
        completion_sent: false,
    })
}

fn preprocess(
    config_path: &Path,
    dealer_seed_path: &Path,
    output_dir: &Path,
) -> Result<(), String> {
    let loaded = load_config(config_path)?;
    let mut seed_wire = read_bounded_regular(
        dealer_seed_path,
        "protected equality preprocessing seed",
        32,
        true,
    )?;
    let result = (|| {
        let mut seed: [u8; 32] = seed_wire
            .as_slice()
            .try_into()
            .map_err(|_| "preprocessing seed must contain exactly 32 bytes".to_string())?;
        let metadata = fs::symlink_metadata(output_dir).map_err(|error| {
            format!(
                "cannot inspect preprocessing output directory {}: {error}",
                output_dir.display()
            )
        })?;
        if !metadata.is_dir() || metadata.file_type().is_symlink() {
            return Err(
                "preprocessing output must be an existing non-symlink directory".to_string(),
            );
        }
        for party in 0..loaded.roster.n_parties() {
            let path = output_dir.join(format!("party-{party}.triples"));
            if fs::symlink_metadata(&path).is_ok() {
                return Err(format!(
                    "preprocessing output {} already exists; refusing a partial overwrite",
                    path.display()
                ));
            }
        }
        let mut rng = StdRng::from_seed(seed);
        seed.fill(0);
        let rows =
            trusted_dealer_triples(&loaded.session, &mut rng).map_err(|error| error.to_string())?;
        for (party, row) in rows.into_iter().enumerate() {
            let path = output_dir.join(format!("party-{party}.triples"));
            let mut wire = row.to_wire_bytes().map_err(|error| error.to_string())?;
            let mut custody = Vec::with_capacity(wire.len() + PREPROCESSING_CUSTODY_OVERHEAD);
            custody.extend_from_slice(PREPROCESSING_CUSTODY_MAGIC);
            custody.extend_from_slice(&loaded.digest);
            custody.extend_from_slice(&(party as u32).to_be_bytes());
            custody.extend_from_slice(&(wire.len() as u64).to_be_bytes());
            custody.extend_from_slice(&wire);
            append_custody_checksum(&mut custody);
            let write = write_new_secret(&path, &custody);
            wire.fill(0);
            custody.fill(0);
            write?;
        }
        Ok(())
    })();
    seed_wire.fill(0);
    result
}

enum Worker {
    Party {
        machine: EqualityPartyMachine,
        completion_sent: bool,
    },
    Coordinator {
        machine: EqualityCoordinatorMachine,
        completion_sent: bool,
    },
}

#[derive(Deserialize)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
enum Request {
    Pump { frames_hex: Vec<String> },
    Shutdown,
}

#[derive(Serialize)]
struct RoutedFrame {
    sender: usize,
    recipient: usize,
    sequence: u64,
    wire_hex: String,
}

#[derive(Serialize)]
#[serde(tag = "role", rename_all = "snake_case")]
enum Completion {
    Party {
        party: usize,
        and_gates: usize,
        peer_input_messages_sent: usize,
        peer_input_messages_received: usize,
    },
    Coordinator {
        equal: bool,
        session_nonce_hex: String,
        transcript_hex: String,
    },
}

impl From<PartyReport> for Completion {
    fn from(report: PartyReport) -> Self {
        Self::Party {
            party: report.party,
            and_gates: report.and_gates,
            peer_input_messages_sent: report.peer_input_messages_sent,
            peer_input_messages_received: report.peer_input_messages_received,
        }
    }
}

#[derive(Serialize)]
struct Response {
    frames: Vec<RoutedFrame>,
    #[serde(skip_serializing_if = "Option::is_none")]
    completion: Option<Completion>,
}

fn serve(mut worker: Worker) -> Result<(), String> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut input = stdin.lock();
    let mut output = stdout.lock();
    loop {
        let Some(request) = read_rpc::<_, Request>(&mut input)? else {
            return Ok(());
        };
        match request {
            Request::Pump { frames_hex } => {
                if frames_hex.len() > MAX_INPUT_FRAMES {
                    return Err("pump request contains too many frames".to_string());
                }
                for encoded in frames_hex {
                    if encoded.len() > MAX_AUTHENTICATED_FRAME_BYTES * 2 {
                        return Err("authenticated frame exceeds its worker bound".to_string());
                    }
                    let frame = decode_hex(&encoded, "authenticated frame")?;
                    if frame.len() > MAX_AUTHENTICATED_FRAME_BYTES {
                        return Err("authenticated frame exceeds its worker bound".to_string());
                    }
                    worker.accept(&frame)?;
                }
                let response = Response {
                    frames: worker.drain_frames()?,
                    completion: worker.take_completion()?,
                };
                write_rpc(&mut output, &response)?;
            }
            Request::Shutdown => return Ok(()),
        }
    }
}

impl Worker {
    fn accept(&mut self, frame: &[u8]) -> Result<(), String> {
        match self {
            Self::Party { machine, .. } => machine.accept_frame(frame),
            Self::Coordinator { machine, .. } => machine.accept_frame(frame),
        }
        .map_err(|error| error.to_string())
    }

    fn drain_frames(&mut self) -> Result<Vec<RoutedFrame>, String> {
        let mut frames = Vec::new();
        while frames.len() < MAX_OUTPUT_FRAMES {
            let next = match self {
                Self::Party { machine, .. } => machine.try_next_frame(),
                Self::Coordinator { machine, .. } => machine.try_next_frame(),
            }
            .map_err(|error| error.to_string())?;
            let Some(frame) = next else { break };
            frames.push(route_frame(frame));
        }
        Ok(frames)
    }

    fn take_completion(&mut self) -> Result<Option<Completion>, String> {
        match self {
            Self::Party {
                machine,
                completion_sent,
            } => {
                if *completion_sent {
                    return Ok(None);
                }
                let completion = machine.try_result().map_err(|error| error.to_string())?;
                if completion.is_some() {
                    *completion_sent = true;
                }
                Ok(completion.map(Into::into))
            }
            Self::Coordinator {
                machine,
                completion_sent,
            } => {
                if *completion_sent {
                    return Ok(None);
                }
                let Some(decision) = machine.try_result().map_err(|error| error.to_string())?
                else {
                    return Ok(None);
                };
                *completion_sent = true;
                let transcript = decision
                    .transcript
                    .to_wire_bytes()
                    .map_err(|error| error.to_string())?;
                Ok(Some(Completion::Coordinator {
                    equal: decision.is_equal(),
                    session_nonce_hex: encode_hex(&decision.session_nonce()),
                    transcript_hex: encode_hex(&transcript),
                }))
            }
        }
    }
}

fn route_frame(frame: AuthenticatedEqualityFrame) -> RoutedFrame {
    let sender = frame.sender();
    let recipient = frame.recipient();
    let sequence = frame.sequence();
    RoutedFrame {
        sender,
        recipient,
        sequence,
        wire_hex: encode_hex(&frame.into_bytes()),
    }
}

fn read_rpc<R: Read, T: for<'de> Deserialize<'de>>(reader: &mut R) -> Result<Option<T>, String> {
    let mut first = [0u8; 1];
    match reader.read(&mut first) {
        Ok(0) => return Ok(None),
        Ok(1) => {}
        Ok(_) => unreachable!(),
        Err(error) => return Err(format!("cannot read worker request length: {error}")),
    }
    let mut length = [0u8; 4];
    length[0] = first[0];
    reader
        .read_exact(&mut length[1..])
        .map_err(|error| format!("truncated worker request length: {error}"))?;
    let length = u32::from_le_bytes(length) as usize;
    if length == 0 || length > MAX_RPC_BYTES {
        return Err(format!(
            "worker request length {length} is outside its bound"
        ));
    }
    let mut bytes = vec![0u8; length];
    reader
        .read_exact(&mut bytes)
        .map_err(|error| format!("truncated worker request: {error}"))?;
    serde_json::from_slice(&bytes)
        .map(Some)
        .map_err(|error| format!("invalid worker request: {error}"))
}

fn write_rpc<W: Write, T: Serialize>(writer: &mut W, value: &T) -> Result<(), String> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| format!("cannot encode worker response: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_RPC_BYTES || bytes.len() > u32::MAX as usize {
        return Err("worker response exceeds its allocation limit".to_string());
    }
    writer
        .write_all(&(bytes.len() as u32).to_le_bytes())
        .and_then(|()| writer.write_all(&bytes))
        .and_then(|()| writer.flush())
        .map_err(|error| format!("cannot write worker response: {error}"))
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
            "{label} {} must be a regular non-symlink file",
            path.display()
        ));
    }
    if metadata.len() > max_bytes {
        return Err(format!(
            "{label} {} exceeds its {max_bytes}-byte bound",
            path.display()
        ));
    }
    #[cfg(unix)]
    if owner_only {
        use std::os::unix::fs::MetadataExt;
        let mode = metadata.mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!(
                "{label} {} has mode {mode:03o}; remove group/other permissions",
                path.display()
            ));
        }
    }
    fs::read(path).map_err(|error| format!("cannot read {label} {}: {error}", path.display()))
}

fn write_new_secret(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o600);
    let mut file = options
        .open(path)
        .map_err(|error| format!("cannot create protected file {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write protected file {}: {error}", path.display()))
}

fn parse_usize(value: &str, label: &str) -> Result<usize, String> {
    value
        .parse::<usize>()
        .map_err(|_| format!("invalid {label} index {value:?}"))
}

fn decode_hex_array<const N: usize>(value: &str, label: &str) -> Result<[u8; N], String> {
    decode_hex(value, label)?
        .try_into()
        .map_err(|_| format!("{label} must contain exactly {N} bytes"))
}

fn decode_hex(value: &str, label: &str) -> Result<Vec<u8>, String> {
    if value.len() % 2 != 0 {
        return Err(format!("{label} has odd-length hexadecimal encoding"));
    }
    let mut out = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let high = hex_nibble(pair[0]).ok_or_else(|| format!("{label} is not hexadecimal"))?;
        let low = hex_nibble(pair[1]).ok_or_else(|| format!("{label} is not hexadecimal"))?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn encode_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}
