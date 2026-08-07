//! ONE process of a distributed `t`-of-`n` threshold custody committee.
//!
//! Run `n` of these and you have a committee in which no process ever holds more
//! than one custody share. The parties talk to each other over real TCP with
//! [`fhegg_fhe::threshold::distributed`]'s sealed envelopes; a relying party
//! (a separate process again) asks each of them for a decryption share and
//! combines `t` of them.
//!
//! ```text
//!   threshold-committee-party serve <session-dir> <party-index> <n> <t>
//! ```
//!
//! # What lives in this process, and what does not
//!
//! IN: this party's enrolled native-PQ transport identity (Ed25519 seed +
//! ML-KEM-768 keypair, `0600` under `<session-dir>/secret/`), the `n` private VSS
//! rows addressed to THIS party, and their sum — one Shamir evaluation of the
//! collective secret.
//!
//! NOT IN: any other party's row, and the collective secret. There is no code
//! path here, or in the library, that reconstructs `s = sum_d s_d`. An opening
//! applies this party's Lagrange coefficient to its own row locally and publishes
//! a smudged masked value.
//!
//! # Rendezvous
//!
//! `<session-dir>` is a shared directory used ONLY as an enrollment/rendezvous
//! surface — the equivalent of DNS plus a public key directory. Public identities
//! and listen addresses go there; no protocol message ever does. Every actual
//! message is a sealed envelope over a TCP connection.
//!
//! # Post-quantum provenance
//!
//! This binary installs the Lean-verified ML-DSA cores before any protocol
//! begins. It never sets `DREGG_ALLOW_UNAUDITED_PQ`: if the verified cores are
//! absent, `dregg-pq` aborts the process rather than answering with the
//! unaudited crate, and that abort is the correct outcome.

use std::collections::BTreeSet;
use std::fs;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Sender};
use std::thread;
use std::time::{Duration, Instant};

use dregg_pq::hybrid_kem::{
    install_verified_mlkem_decaps_core, install_verified_mlkem_encaps_core,
    install_verified_mlkem_keygen_core, MlKemDecapsCoreInstall, MlKemEncapsCoreInstall,
    MlKemKeygenCoreInstall,
};
use dregg_pq::{
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core, ml_kem768_keygen, MlDsaKeygenCoreRealInstall,
    MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
};
use ed25519_dalek::SigningKey;
use fhe_traits::Serialize as FheSerialize;
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::mpc_party::transport::{
    EqualityTransportRoster, NativePqTransportIdentity, NativePqTransportPublicIdentity,
};
use fhegg_fhe::threshold::chunked::{ChunkReassembler, ChunkStream};
use fhegg_fhe::threshold::distributed::{
    decode_enrollment, decode_finalize_request, encode_commit_response, encode_enrollment,
    AcceptedDealing, DistributedDkg, DistributedPendingCustody, DistributedVerifiedCustody,
    SEQUENCE_COMMIT_RESPONSE, SEQUENCE_CROSS_EVALUATION, SEQUENCE_FINALIZE_REQUEST,
    SEQUENCE_FINALIZE_RESPONSE, SEQUENCE_OPEN_REQUEST, SEQUENCE_OPEN_RESPONSE,
    SEQUENCE_PUBLIC_KEY_RESPONSE,
};
use fhegg_fhe::threshold::quorum::{AuthenticatedQuorumRoster, QuorumOpeningSession};
use fhegg_fhe::threshold::relying_party::{
    commit_response_chunk_domain, decode_open_request, finalize_request_chunk_domain,
    FINALIZE_ACK_FINALIZED, FINALIZE_ACK_INCOMPLETE, KIND_COMMIT_REQUEST, KIND_CROSS, KIND_DEALING,
    KIND_FINALIZE_REQUEST, KIND_OPEN_REQUEST, KIND_PUBLIC_KEY_REQUEST, KIND_SHUTDOWN,
};
use fhegg_fhe::threshold::{BfvParams, MIN_SMUDGE_BITS};
use rand::rngs::OsRng;
use rand::RngCore;

const ML_KEM_768_EK_BYTES: usize = 1_184;
const ML_KEM_768_DK_BYTES: usize = 2_400;
const MAX_MESSAGE_BYTES: usize = 16 * 1024 * 1024;
const SETUP_DEADLINE: Duration = Duration::from_secs(1_800);
const IO_TIMEOUT: Duration = Duration::from_secs(300);

// Frame kinds are the ONE definition in `fhegg_fhe::threshold::relying_party`, so
// the party and its caller cannot drift. The header is public routing only — the
// sealed envelope inside re-binds route, sequence and roster, so a lying header
// byte makes the open fail rather than making a receiver process the wrong thing.

fn main() {
    if let Err(error) = run() {
        eprintln!("threshold-committee-party: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match args.as_slice() {
        [role, dir, party, n, t] if role == "serve" => serve(
            Path::new(dir),
            parse_index(party)?,
            parse_index(n)?,
            parse_index(t)?,
        ),
        _ => Err(
            "usage: threshold-committee-party serve <session-dir> <party-index> <n> <t>"
                .to_string(),
        ),
    }
}

fn parse_index(value: &str) -> Result<usize, String> {
    value
        .parse::<usize>()
        .map_err(|_| format!("not an index: {value}"))
}

// ─── enrollment ──────────────────────────────────────────────────────────────

fn secret_path(dir: &Path, party: usize) -> PathBuf {
    dir.join("secret").join(format!("{party}.key"))
}

fn public_path(dir: &Path, party: usize) -> PathBuf {
    dir.join("enroll").join(format!("{party}.pub"))
}

fn address_path(dir: &Path, party: usize) -> PathBuf {
    dir.join("addr").join(format!("{party}.addr"))
}

fn ready_path(dir: &Path, party: usize) -> PathBuf {
    dir.join("ready").join(format!("{party}.ready"))
}

/// Generate this party's enrolled identity if it has none, and publish only its
/// public half. The secret file is created `0600` and no other participant ever
/// reads it.
fn enroll(dir: &Path, party: usize) -> Result<(NativePqTransportIdentity, [u8; 32]), String> {
    let secret = secret_path(dir, party);
    if let Ok(bytes) = fs::read(&secret) {
        return identity_from_material(&bytes);
    }
    let mut seed = [0u8; 32];
    OsRng
        .try_fill_bytes(&mut seed)
        .map_err(|_| "OS entropy unavailable".to_string())?;
    let (encapsulation_key, decapsulation_key) = ml_kem768_keygen();
    let mut material = Vec::with_capacity(32 + encapsulation_key.len() + decapsulation_key.len());
    material.extend_from_slice(&seed);
    material.extend_from_slice(&encapsulation_key);
    material.extend_from_slice(&decapsulation_key);
    write_private(&secret, &material)?;

    let identity = NativePqTransportIdentity::from_material(
        SigningKey::from_bytes(&seed),
        encapsulation_key,
        decapsulation_key,
    )
    .map_err(|error| format!("identity material: {error}"))?;
    publish_identity(dir, party, &identity)?;
    Ok((identity, seed))
}

fn publish_identity(
    dir: &Path,
    party: usize,
    identity: &NativePqTransportIdentity,
) -> Result<(), String> {
    write_atomic(
        &public_path(dir, party),
        &encode_enrollment(&identity.public_identity()),
    )
}

fn identity_from_material(bytes: &[u8]) -> Result<(NativePqTransportIdentity, [u8; 32]), String> {
    if bytes.len() != 32 + ML_KEM_768_EK_BYTES + ML_KEM_768_DK_BYTES {
        return Err("persisted identity has an invalid length".to_string());
    }
    let seed: [u8; 32] = bytes[..32].try_into().expect("32 bytes");
    let identity = NativePqTransportIdentity::from_material(
        SigningKey::from_bytes(&seed),
        bytes[32..32 + ML_KEM_768_EK_BYTES].to_vec(),
        bytes[32 + ML_KEM_768_EK_BYTES..].to_vec(),
    )
    .map_err(|error| format!("persisted identity: {error}"))?;
    Ok((identity, seed))
}

fn read_public_identity(path: &Path) -> Result<NativePqTransportPublicIdentity, String> {
    let bytes = fs::read(path).map_err(|error| format!("enrollment {path:?}: {error}"))?;
    decode_enrollment(&bytes).map_err(|error| format!("enrollment {path:?}: {error}"))
}

fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("mkdir {parent:?}: {error}"))?;
    }
    let temporary = path.with_extension("tmp");
    fs::write(&temporary, bytes).map_err(|error| format!("write {temporary:?}: {error}"))?;
    fs::rename(&temporary, path).map_err(|error| format!("rename {path:?}: {error}"))
}

fn write_private(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("mkdir {parent:?}: {error}"))?;
    }
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|error| format!("create {path:?}: {error}"))?;
    file.write_all(bytes)
        .map_err(|error| format!("write {path:?}: {error}"))?;
    file.sync_all()
        .map_err(|error| format!("fsync {path:?}: {error}"))
}

fn wait_for(path: &Path, deadline: Instant) -> Result<(), String> {
    while Instant::now() < deadline {
        if path.exists() {
            return Ok(());
        }
        thread::sleep(Duration::from_millis(25));
    }
    Err(format!("timed out waiting for {path:?}"))
}

// ─── framing ─────────────────────────────────────────────────────────────────

fn write_frame(
    stream: &mut TcpStream,
    kind: u8,
    sender: u32,
    payload: &[u8],
) -> Result<(), String> {
    if payload.len() > MAX_MESSAGE_BYTES {
        return Err("outbound message exceeds its allocation limit".to_string());
    }
    let mut header = [0u8; 9];
    header[0] = kind;
    header[1..5].copy_from_slice(&sender.to_be_bytes());
    header[5..].copy_from_slice(&(payload.len() as u32).to_be_bytes());
    stream
        .write_all(&header)
        .and_then(|()| stream.write_all(payload))
        .and_then(|()| stream.flush())
        .map_err(|error| format!("write frame: {error}"))
}

fn read_frame(stream: &mut TcpStream) -> Result<(u8, u32, Vec<u8>), String> {
    let mut header = [0u8; 9];
    stream
        .read_exact(&mut header)
        .map_err(|error| format!("read header: {error}"))?;
    let sender = u32::from_be_bytes(header[1..5].try_into().expect("4 bytes"));
    let length = u32::from_be_bytes(header[5..].try_into().expect("4 bytes")) as usize;
    if length > MAX_MESSAGE_BYTES {
        return Err("inbound message exceeds its allocation limit".to_string());
    }
    let mut payload = vec![0u8; length];
    stream
        .read_exact(&mut payload)
        .map_err(|error| format!("read payload: {error}"))?;
    Ok((header[0], sender, payload))
}

/// Deliver one frame and return WITHOUT waiting for an application answer.
///
/// Waiting would deadlock the whole committee and it took reading the protocol
/// to see it: in phase 1 every party is inside its own send loop at the same
/// moment, so if A blocks until B's protocol thread answers — and B is blocked
/// waiting for A — neither ever reaches its receive loop. Delivery here means
/// "connected and wrote"; the protocol's progress condition is the arrival of
/// the peer's own next-phase message, not an ack.
fn send_oneway(address: SocketAddr, kind: u8, sender: usize, payload: &[u8]) -> Result<(), String> {
    let mut stream = TcpStream::connect_timeout(&address, IO_TIMEOUT)
        .map_err(|error| format!("connect {address}: {error}"))?;
    stream
        .set_write_timeout(Some(IO_TIMEOUT))
        .map_err(|error| format!("timeouts: {error}"))?;
    write_frame(&mut stream, kind, sender as u32, payload)
}

fn deliver(
    address: SocketAddr,
    kind: u8,
    sender: usize,
    payload: &[u8],
    deadline: Instant,
) -> Result<(), String> {
    let mut last = String::new();
    while Instant::now() < deadline {
        match send_oneway(address, kind, sender, payload) {
            Ok(()) => return Ok(()),
            Err(error) => {
                last = error;
                thread::sleep(Duration::from_millis(50));
            }
        }
    }
    Err(format!("could not deliver to {address}: {last}"))
}

struct Inbound {
    kind: u8,
    sender: usize,
    payload: Vec<u8>,
    reply: Sender<Vec<u8>>,
}

fn spawn_listener(listener: TcpListener, inbox: Sender<Inbound>) {
    thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let inbox = inbox.clone();
            thread::spawn(move || {
                let _ = stream.set_read_timeout(Some(IO_TIMEOUT));
                let _ = stream.set_write_timeout(Some(IO_TIMEOUT));
                let Ok((kind, sender, payload)) = read_frame(&mut stream) else {
                    return;
                };
                let (reply, answers) = mpsc::channel();
                if inbox
                    .send(Inbound {
                        kind,
                        sender: sender as usize,
                        payload,
                        reply,
                    })
                    .is_err()
                {
                    return;
                }
                if let Ok(answer) = answers.recv() {
                    let _ = write_frame(&mut stream, kind, sender, &answer);
                }
            });
        }
    });
}

// ─── the party process ───────────────────────────────────────────────────────

fn install_verified_pq_cores() -> Result<(), String> {
    // NEVER `DREGG_ALLOW_UNAUDITED_PQ`. If these do not install, dregg-pq aborts
    // this process at the first ML-DSA operation, which is the right answer: the
    // committee's authentication would otherwise be decided by unaudited code.
    if !matches!(
        install_verified_mldsa_keygen_core_real(
            dregg_lean_ffi::mldsa_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mldsa_keygen_real(wire).ok(),
        ),
        MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
    ) {
        return Err("the verified ML-DSA keygen core did not install".to_string());
    }
    if !matches!(
        install_verified_mldsa_sign_core_real(
            dregg_lean_ffi::fips204_sign_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_sign_real(wire).ok(),
        ),
        MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
    ) {
        return Err("the verified ML-DSA sign core did not install".to_string());
    }
    if !matches!(
        install_verified_mldsa_verify_core(
            dregg_lean_ffi::fips204_verify_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_verify_real(wire).ok(),
        ),
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
    ) {
        return Err("the verified ML-DSA verify core did not install".to_string());
    }
    // ALL SIX, not the three that sign: this committee's confidentiality is
    // ML-KEM-768, and a process that installed only the signature cores aborts at
    // the first sealed envelope. That abort is how this list got completed.
    if !matches!(
        install_verified_mlkem_keygen_core(
            dregg_lean_ffi::mlkem_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_keygen_real(wire).ok(),
        ),
        MlKemKeygenCoreInstall::Installed | MlKemKeygenCoreInstall::AlreadyInstalled
    ) {
        return Err("the verified ML-KEM keygen core did not install".to_string());
    }
    if !matches!(
        install_verified_mlkem_encaps_core(
            dregg_lean_ffi::mlkem_encaps_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_encaps_real(wire).ok(),
        ),
        MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled
    ) {
        return Err("the verified ML-KEM encaps core did not install".to_string());
    }
    if !matches!(
        install_verified_mlkem_decaps_core(
            dregg_lean_ffi::mlkem_decaps_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_decaps_real(wire).ok(),
        ),
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled
    ) {
        return Err("the verified ML-KEM decaps core did not install".to_string());
    }
    Ok(())
}

struct Custody {
    state: DistributedVerifiedCustody,
    roster: AuthenticatedQuorumRoster,
    signing_key: SigningKey,
}

fn serve(dir: &Path, party: usize, n_parties: usize, threshold: usize) -> Result<(), String> {
    install_verified_pq_cores()?;
    let deadline = Instant::now() + SETUP_DEADLINE;
    let (identity, seed) = enroll(dir, party)?;
    let signing_key = SigningKey::from_bytes(&seed);

    // Bind BEFORE waiting for peers: a peer that reads our address must find a
    // socket already accepting, or its first connect races the bind.
    let listener = TcpListener::bind(SocketAddrV4::new(Ipv4Addr::LOCALHOST, 0))
        .map_err(|error| format!("bind: {error}"))?;
    let local = listener
        .local_addr()
        .map_err(|error| format!("local_addr: {error}"))?;
    let (inbox, inbound) = mpsc::channel();
    spawn_listener(listener, inbox);
    write_atomic(&address_path(dir, party), local.to_string().as_bytes())?;
    println!(
        "party {party} pid {} listening on {local}",
        std::process::id()
    );

    // Every slot INCLUDING the relying party's must be enrolled before the roster
    // — and therefore the session and the CRP seed — can be derived at all.
    let mut identities = Vec::with_capacity(n_parties + 1);
    for slot in 0..=n_parties {
        wait_for(&public_path(dir, slot), deadline)?;
        identities.push(read_public_identity(&public_path(dir, slot))?);
    }
    let party_keys = identities
        .iter()
        .take(n_parties)
        .map(|identity| identity.ed25519())
        .collect::<Vec<_>>();
    let relying_party = identities.pop().expect("the relying party slot");
    let roster = EqualityTransportRoster::new_native_post_quantum(identities, relying_party)
        .map_err(|error| format!("roster: {error}"))?;
    let dkg = DistributedDkg::new(roster, threshold, BfvParams::fold_set())
        .map_err(|error| format!("dkg: {error}"))?;

    let mut peers = Vec::with_capacity(n_parties - 1);
    for peer in 0..n_parties {
        if peer == party {
            continue;
        }
        wait_for(&address_path(dir, peer), deadline)?;
        let text = fs::read_to_string(address_path(dir, peer))
            .map_err(|error| format!("peer address: {error}"))?;
        let address = text
            .trim()
            .parse::<SocketAddr>()
            .map_err(|error| format!("peer address: {error}"))?;
        peers.push((peer, address));
    }

    // ── PHASE 1: deal, self-verify the whole dealing, seal one row per peer.
    let started = Instant::now();
    let hostile_victim = hostile_tamper_victim();
    let dealing = match hostile_victim {
        #[cfg(debug_assertions)]
        Some(victim) => dkg.deal_with_hostile_row_corruption(&identity, party, victim),
        _ => dkg.deal(&identity, party),
    }
    .map_err(|error| format!("deal: {error}"))?;
    // `relin_secret` is this dealer's own short `s_d`. It stays in this process
    // for the whole run: the relinearization ceremony is the one step that
    // cannot use the Lagrange custody row, and it runs on `s = sum_d s_d`.
    // See `fhegg_fhe::threshold::distributed_relin` for why.
    let (own, sealed, relin_secret) = dealing.own();
    eprintln!("party {party}: dealt in {:?}", started.elapsed());

    let mut accepted: Vec<AcceptedDealing> = vec![own];
    for (recipient, message) in sealed.into_iter() {
        let address = peers
            .iter()
            .find(|(peer, _)| *peer == recipient)
            .map(|(_, address)| *address)
            .ok_or_else(|| format!("no address for peer {recipient}"))?;
        deliver(address, KIND_DEALING, party, &message, deadline)?;
    }

    let mut pending_cross: Vec<(usize, Vec<u8>)> = Vec::new();
    let mut checked_cross: BTreeSet<usize> = BTreeSet::new();
    let mut sent_cross = false;
    // After DKG we hold `pending`: aggregated custody plus this party's own
    // secret-share commitment, awaiting the whole committee's commitment vectors.
    // The finalize round consumes it into a certificate-capable `custody`. The
    // collective key and setup digest are captured independently so the collective-
    // key request is answerable across that transition.
    let mut setup_done = false;
    // Held so `s_d` outlives the DKG and is available to a relinearization
    // ceremony; it has no serializer or coefficient accessor and overwrites
    // itself on drop.
    let _relin_secret = relin_secret;
    let mut pending: Option<DistributedPendingCustody> = None;
    let mut custody: Option<Custody> = None;
    // Chunked-round state. The commit response is built once and served by
    // index; the finalize request is accumulated until its payload closes.
    let mut commit_stream: Option<ChunkStream> = None;
    let mut finalize_chunks = ChunkReassembler::new(finalize_request_chunk_domain());
    let mut collective_pk_bytes: Option<Vec<u8>> = None;
    let mut setup_digest: Option<[u8; 32]> = None;

    loop {
        if accepted.len() == n_parties && !sent_cross {
            accepted.sort_by_key(AcceptedDealing::dealer);
            for &(peer, address) in &peers {
                let message = dkg
                    .cross_evaluation_message(&accepted, peer)
                    .map_err(|error| format!("cross evaluation: {error}"))?;
                let sealed = dkg
                    .seal(&identity, party, peer, SEQUENCE_CROSS_EVALUATION, &message)
                    .map_err(|error| format!("seal cross: {error}"))?;
                deliver(address, KIND_CROSS, party, &sealed, deadline)?;
            }
            sent_cross = true;
        }
        if sent_cross && !setup_done && !pending_cross.is_empty() {
            for (peer, sealed) in std::mem::take(&mut pending_cross) {
                let message = dkg
                    .open(&identity, peer, party, SEQUENCE_CROSS_EVALUATION, &sealed)
                    .map_err(|error| format!("open cross from {peer}: {error}"))?;
                dkg.check_cross_evaluation_message(&accepted, peer, &message)
                    .map_err(|error| format!("cross evaluation from {peer} REFUSED: {error}"))?;
                checked_cross.insert(peer);
            }
        }
        if !setup_done && checked_cross.len() == n_parties - 1 && accepted.len() == n_parties {
            let ready = dkg
                .prepare_verified_custody(party, std::mem::take(&mut accepted))
                .map_err(|error| format!("prepare verified custody: {error}"))?;
            let digest = ready.setup_digest();
            collective_pk_bytes = Some(ready.collective().pk.to_bytes());
            setup_digest = Some(digest);
            eprintln!(
                "party {party}: custody ready in {:?}, setup digest {}",
                started.elapsed(),
                hex(&digest)
            );
            write_atomic(&ready_path(dir, party), &digest)?;
            pending = Some(ready);
            setup_done = true;
        }

        let Ok(message) = inbound.recv_timeout(Duration::from_millis(250)) else {
            if !setup_done && Instant::now() > deadline {
                return Err("setup deadline expired".to_string());
            }
            continue;
        };
        match message.kind {
            KIND_DEALING => {
                if accepted.iter().any(|d| d.dealer() == message.sender) {
                    return Err(format!("duplicate dealing from {}", message.sender));
                }
                // A VSS refusal here is FATAL and it is the tampered-row tooth.
                // A transport refusal is equally fatal: this party's peer said
                // the frame came from a slot whose enrolled identity did not
                // authenticate it.
                let dealing = dkg
                    .accept_dealing(&identity, party, message.sender, &message.payload)
                    .map_err(|error| format!("dealing from {} REFUSED: {error}", message.sender))?;
                accepted.push(dealing);
                let _ = message.reply.send(vec![1]);
            }
            KIND_CROSS => {
                if !setup_done && !checked_cross.contains(&message.sender) {
                    pending_cross.push((message.sender, message.payload));
                }
                let _ = message.reply.send(vec![1]);
            }
            KIND_PUBLIC_KEY_REQUEST => {
                // Sealed to the relying party like everything else: the
                // encryption key a market will use is exactly as forgeable as
                // the channel that delivers it.
                let answer = match (&setup_digest, &collective_pk_bytes) {
                    (Some(digest), Some(pk_bytes)) => {
                        let mut body = Vec::with_capacity(32 + pk_bytes.len());
                        body.extend_from_slice(digest);
                        body.extend_from_slice(pk_bytes);
                        dkg.seal(
                            &identity,
                            party,
                            dkg.relying_party(),
                            SEQUENCE_PUBLIC_KEY_RESPONSE,
                            &body,
                        )
                        .map_err(|error| format!("seal public key: {error}"))?
                    }
                    _ => Vec::new(),
                };
                let _ = message.reply.send(answer);
            }
            KIND_COMMIT_REQUEST => {
                // Publish this party's PUBLIC aggregate-row commitment vector, its
                // binding proof, and the full dealer commitments it accepted; the
                // blindings stay in `pending`.
                //
                // The body outgrows one sealed envelope, so it is chunked. The
                // stream is built ONCE and cached: every chunk of one response
                // must carry the same digest, and rebuilding per request would
                // also redo the whole encode for each round-trip.
                let answer = match pending.as_ref() {
                    Some(ready) => {
                        let stream = commit_stream.get_or_insert_with(|| {
                            let stream = ChunkStream::new(
                                commit_response_chunk_domain(),
                                encode_commit_response(
                                    ready.dealer_commitments(),
                                    ready.secret_share_commitments(),
                                    ready.binding_proof(),
                                ),
                            );
                            // Printed so a run's own log shows whether chunking
                            // is LOAD-BEARING here or a one-chunk no-op. A
                            // payload past the 8 MiB envelope ceiling could not
                            // have been sent at all before this.
                            eprintln!(
                                "party {party}: commit response {} bytes in {} chunk(s)",
                                stream.total_len(),
                                stream.count()
                            );
                            stream
                        });
                        // A malformed or out-of-range index is a refusal, not a
                        // panic and not a silent chunk 0.
                        match chunk_index(&message.payload).and_then(|i| stream.chunk(i)) {
                            Some(chunk) => dkg
                                .seal(
                                    &identity,
                                    party,
                                    dkg.relying_party(),
                                    SEQUENCE_COMMIT_RESPONSE,
                                    &chunk,
                                )
                                .map_err(|error| format!("seal commit response: {error}"))?,
                            None => Vec::new(),
                        }
                    }
                    None => Vec::new(),
                };
                let _ = message.reply.send(answer);
            }
            KIND_FINALIZE_REQUEST => {
                let answer = accept_finalize_chunk(
                    &dkg,
                    &identity,
                    party,
                    &party_keys,
                    &signing_key,
                    &mut pending,
                    &mut custody,
                    &mut finalize_chunks,
                    &message.payload,
                );
                let _ = message.reply.send(answer);
            }
            KIND_OPEN_REQUEST => {
                let Some(ready) = custody.as_mut() else {
                    // Never opens before the verified commitment round has bound a
                    // transcript: an opening here would be uncertified.
                    let _ = message.reply.send(Vec::new());
                    continue;
                };
                match answer_opening(&dkg, &identity, party, ready, &message.payload) {
                    Ok(answer) => {
                        let _ = message.reply.send(answer);
                    }
                    Err(error) => {
                        eprintln!("party {party}: opening REFUSED: {error}");
                        let _ = message.reply.send(Vec::new());
                    }
                }
            }
            KIND_SHUTDOWN => {
                let _ = message.reply.send(vec![1]);
                return Ok(());
            }
            _ => {
                let _ = message.reply.send(Vec::new());
            }
        }
    }
}

/// The requested chunk index, or `None` if the request body is not exactly one
/// little-endian `u64`. A malformed index is a refusal, never an implicit 0.
fn chunk_index(payload: &[u8]) -> Option<usize> {
    let raw: [u8; 8] = payload.try_into().ok()?;
    usize::try_from(u64::from_le_bytes(raw)).ok()
}

/// Accept one finalize-request chunk.
///
/// The finalize request no longer fits one sealed envelope, so it arrives as a
/// chunk stream. Each chunk is opened (route-bound, dually signed) and fed to the
/// reassembler; custody is finalized ONLY on the chunk that closes the payload,
/// and only if the reassembly hashes to the digest every chunk declared. An
/// incomplete stream gets a sealed "not yet" ack, so the caller can tell it
/// apart from a refusal, which stays the empty reply it always was.
///
/// A chunk that is refused leaves `pending` INTACT on purpose: the pre-chunking
/// code consumed `pending` before it could fail, so one transient finalize error
/// permanently bricked the party's verified path. Only a decode or finalize
/// failure on the COMPLETE payload is terminal now.
#[allow(clippy::too_many_arguments)]
fn accept_finalize_chunk(
    dkg: &DistributedDkg,
    identity: &NativePqTransportIdentity,
    party: usize,
    party_keys: &[[u8; 32]],
    signing_key: &SigningKey,
    pending: &mut Option<DistributedPendingCustody>,
    custody: &mut Option<Custody>,
    chunks: &mut ChunkReassembler,
    sealed: &[u8],
) -> Vec<u8> {
    if pending.is_none() {
        return Vec::new();
    }
    let chunk = match dkg.open(
        identity,
        dkg.relying_party(),
        party,
        SEQUENCE_FINALIZE_REQUEST,
        sealed,
    ) {
        Ok(chunk) => chunk,
        Err(error) => {
            eprintln!("party {party}: finalize open REFUSED: {error}");
            return Vec::new();
        }
    };
    let request = match chunks.accept(&chunk) {
        Ok(Some(payload)) => payload,
        Ok(None) => {
            // Accepted, payload still open. Sealed so the caller can tell this
            // apart from a refusal by the same route-bound proof as any answer.
            return match dkg.seal(
                identity,
                party,
                dkg.relying_party(),
                SEQUENCE_FINALIZE_RESPONSE,
                &[FINALIZE_ACK_INCOMPLETE],
            ) {
                Ok(sealed) => sealed,
                Err(error) => {
                    eprintln!("party {party}: seal finalize progress ack: {error}");
                    Vec::new()
                }
            };
        }
        Err(error) => {
            eprintln!("party {party}: finalize chunk REFUSED: {error}");
            return Vec::new();
        }
    };
    finalize_custody(
        dkg,
        identity,
        party,
        party_keys,
        signing_key,
        pending,
        custody,
        &request,
    )
}

/// Consume `pending` into certificate-capable verified custody, once the collector
/// has sent the whole committee's ordered commitment vectors. Returns the sealed
/// acknowledgement, or an empty answer if the finalize is refused (a corrupted or
/// mis-collected commitment set aborts the verified path for this party rather than
/// silently opening uncertified).
#[allow(clippy::too_many_arguments)]
fn finalize_custody(
    dkg: &DistributedDkg,
    identity: &NativePqTransportIdentity,
    party: usize,
    party_keys: &[[u8; 32]],
    signing_key: &SigningKey,
    pending: &mut Option<DistributedPendingCustody>,
    custody: &mut Option<Custody>,
    request: &[u8],
) -> Vec<u8> {
    let Some(ready) = pending.take() else {
        return Vec::new();
    };
    let (commitments, binding_proofs) =
        match decode_finalize_request(request, dkg.session(), dkg.params()) {
            Ok(decoded) => decoded,
            Err(error) => {
                eprintln!("party {party}: finalize decode REFUSED: {error}");
                return Vec::new();
            }
        };
    let verified = match ready.finalize(commitments, binding_proofs) {
        Ok(verified) => verified,
        Err(error) => {
            eprintln!("party {party}: finalize REFUSED: {error}");
            return Vec::new();
        }
    };
    let roster = match AuthenticatedQuorumRoster::new_verified(
        dkg.session().clone(),
        &verified.transcript,
        party_keys.to_vec(),
    ) {
        Ok(roster) => roster,
        Err(error) => {
            eprintln!("party {party}: verified custody roster REFUSED: {error:?}");
            return Vec::new();
        }
    };
    *custody = Some(Custody {
        state: verified,
        roster,
        signing_key: signing_key.clone(),
    });
    match dkg.seal(
        identity,
        party,
        dkg.relying_party(),
        SEQUENCE_FINALIZE_RESPONSE,
        &[FINALIZE_ACK_FINALIZED],
    ) {
        Ok(sealed) => sealed,
        Err(error) => {
            eprintln!("party {party}: seal finalize ack: {error}");
            Vec::new()
        }
    }
}

fn answer_opening(
    dkg: &DistributedDkg,
    identity: &NativePqTransportIdentity,
    party: usize,
    custody: &mut Custody,
    sealed: &[u8],
) -> Result<Vec<u8>, String> {
    let relying_party = dkg.relying_party();
    let request = dkg
        .open(
            identity,
            relying_party,
            party,
            SEQUENCE_OPEN_REQUEST,
            sealed,
        )
        .map_err(|error| format!("open request: {error}"))?;
    let (nonce, roster, plain_bound, ciphertext_bytes) = decode_open_request(&request)?;
    // The opening binds the exact accepted VSS setup, so this party's certificate-
    // carrying share and the relying party's verified combiner agree on the same
    // transcript digest.
    let opening = QuorumOpeningSession::new_verified(
        dkg.session().clone(),
        &custody.state.transcript,
        nonce,
        roster,
    )
    .map_err(|error| format!("opening session: {error:?}"))?;
    let ciphertext = LeanCiphertext::from_fhe_bytes(
        &ciphertext_bytes,
        dkg.params().moduli(),
        dkg.params().degree(),
        plain_bound,
    )
    .map_err(|error| format!("ciphertext: {error:?}"))?;
    let share = custody
        .state
        .party
        .partial_decrypt(&opening, &ciphertext, MIN_SMUDGE_BITS, dkg.params())
        .map_err(|error| format!("partial decrypt: {error:?}"))?;
    let signed = custody
        .roster
        .sign_share(share, &custody.signing_key)
        .map_err(|error| format!("sign share: {error:?}"))?;
    dkg.seal(
        identity,
        party,
        relying_party,
        SEQUENCE_OPEN_RESPONSE,
        &signed.to_wire_bytes(),
    )
    .map_err(|error| format!("seal response: {error}"))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// HOSTILE INJECTION, debug builds only.
///
/// `FHEGG_COMMITTEE_TAMPER_ROW=<recipient>` makes THIS party corrupt the private
/// row it deals to that recipient AFTER committing to it — a dealer that lies to
/// one recipient. It exists so the recipient's refusal can be observed firing in
/// a real deployment instead of asserted in prose, and the library entry point it
/// calls is itself `#[cfg(debug_assertions)]`, so a release build has no such
/// path to reach.
#[cfg(debug_assertions)]
fn hostile_tamper_victim() -> Option<usize> {
    std::env::var("FHEGG_COMMITTEE_TAMPER_ROW")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
}

#[cfg(not(debug_assertions))]
fn hostile_tamper_victim() -> Option<usize> {
    None
}
