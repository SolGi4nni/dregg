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
use fhegg_fhe::threshold::distributed::{
    decode_enrollment, encode_enrollment, AcceptedDealing, DistributedCustody, DistributedDkg,
    SEQUENCE_CROSS_EVALUATION, SEQUENCE_OPEN_REQUEST, SEQUENCE_OPEN_RESPONSE,
    SEQUENCE_PUBLIC_KEY_RESPONSE,
};
use fhegg_fhe::threshold::quorum::{AuthenticatedQuorumRoster, QuorumOpeningSession};
use fhegg_fhe::threshold::{BfvParams, MIN_SMUDGE_BITS};
use rand::rngs::OsRng;
use rand::RngCore;

const ML_KEM_768_EK_BYTES: usize = 1_184;
const ML_KEM_768_DK_BYTES: usize = 2_400;
const MAX_MESSAGE_BYTES: usize = 16 * 1024 * 1024;
const SETUP_DEADLINE: Duration = Duration::from_secs(1_800);
const IO_TIMEOUT: Duration = Duration::from_secs(300);

/// Frame kinds. The header is public routing only — the sealed envelope inside
/// re-binds the real route, sequence and roster, so a lying header byte makes the
/// open fail rather than making a receiver process the wrong thing.
const KIND_DEALING: u8 = 1;
const KIND_CROSS: u8 = 2;
const KIND_OPEN_REQUEST: u8 = 3;
const KIND_PUBLIC_KEY_REQUEST: u8 = 4;
const KIND_SHUTDOWN: u8 = 5;

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
    state: DistributedCustody,
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
    let (own, sealed) = dealing.own();
    eprintln!("party {party}: dealt in {:?}", started.elapsed());

    let mut accepted: Vec<AcceptedDealing> = vec![own];
    for (recipient, message) in sealed {
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
    let mut custody: Option<Custody> = None;

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
        if sent_cross && !pending_cross.is_empty() {
            for (peer, sealed) in std::mem::take(&mut pending_cross) {
                let message = dkg
                    .open(&identity, peer, party, SEQUENCE_CROSS_EVALUATION, &sealed)
                    .map_err(|error| format!("open cross from {peer}: {error}"))?;
                dkg.check_cross_evaluation_message(&accepted, peer, &message)
                    .map_err(|error| format!("cross evaluation from {peer} REFUSED: {error}"))?;
                checked_cross.insert(peer);
            }
        }
        if custody.is_none() && checked_cross.len() == n_parties - 1 && accepted.len() == n_parties
        {
            let ready = dkg
                .finish(party, std::mem::take(&mut accepted))
                .map_err(|error| format!("finish: {error}"))?;
            let quorum_roster =
                AuthenticatedQuorumRoster::new(dkg.session().clone(), party_keys.clone())
                    .map_err(|error| format!("custody roster: {error:?}"))?;
            eprintln!(
                "party {party}: custody ready in {:?}, setup digest {}",
                started.elapsed(),
                hex(&ready.setup_digest)
            );
            write_atomic(&ready_path(dir, party), &ready.setup_digest)?;
            custody = Some(Custody {
                state: ready,
                roster: quorum_roster,
                signing_key: signing_key.clone(),
            });
        }

        let Ok(message) = inbound.recv_timeout(Duration::from_millis(250)) else {
            if custody.is_none() && Instant::now() > deadline {
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
                if custody.is_none() && !checked_cross.contains(&message.sender) {
                    pending_cross.push((message.sender, message.payload));
                }
                let _ = message.reply.send(vec![1]);
            }
            KIND_PUBLIC_KEY_REQUEST => {
                // Sealed to the relying party like everything else: the
                // encryption key a market will use is exactly as forgeable as
                // the channel that delivers it.
                let answer = match custody.as_ref() {
                    Some(ready) => {
                        let mut body = Vec::new();
                        body.extend_from_slice(&ready.state.setup_digest);
                        body.extend_from_slice(&ready.state.collective.pk.to_bytes());
                        dkg.seal(
                            &identity,
                            party,
                            dkg.relying_party(),
                            SEQUENCE_PUBLIC_KEY_RESPONSE,
                            &body,
                        )
                        .map_err(|error| format!("seal public key: {error}"))?
                    }
                    None => Vec::new(),
                };
                let _ = message.reply.send(answer);
            }
            KIND_OPEN_REQUEST => {
                let Some(ready) = custody.as_mut() else {
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
    let opening = QuorumOpeningSession::new(dkg.session().clone(), nonce, roster)
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

fn decode_open_request(bytes: &[u8]) -> Result<([u8; 32], Vec<usize>, u64, Vec<u8>), String> {
    let mut position = 0usize;
    let mut take = |length: usize| -> Result<&[u8], String> {
        let end = position
            .checked_add(length)
            .filter(|&end| end <= bytes.len())
            .ok_or_else(|| "truncated opening request".to_string())?;
        let output = &bytes[position..end];
        position = end;
        Ok(output)
    };
    let nonce: [u8; 32] = take(32)?.try_into().map_err(|_| "nonce".to_string())?;
    let count = u64::from_le_bytes(take(8)?.try_into().map_err(|_| "count".to_string())?) as usize;
    if count > 1024 {
        return Err("opening roster arity".to_string());
    }
    let mut roster = Vec::with_capacity(count);
    for _ in 0..count {
        roster.push(
            u64::from_le_bytes(take(8)?.try_into().map_err(|_| "party".to_string())?) as usize,
        );
    }
    let plain_bound = u64::from_le_bytes(take(8)?.try_into().map_err(|_| "bound".to_string())?);
    let length =
        u64::from_le_bytes(take(8)?.try_into().map_err(|_| "length".to_string())?) as usize;
    let ciphertext = take(length)?.to_vec();
    Ok((nonce, roster, plain_bound, ciphertext))
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
