// The file only compiles when the audited Lean PQ cores are linked. It is NOT
// registered in Cargo.toml (that is codex's file), so Cargo auto-discovers it as
// a test target WITHOUT `required-features`; this gate is what keeps a bare
// `cargo test` (no feature, no archive) from trying to compile it. Run it with:
//
//   cargo test -p fhegg-fhe --features verified-pq-runtime-tests \
//       --test distributed_netting_processes -- --nocapture
//
#![cfg(all(
    feature = "verified-pq-runtime-tests",
    any(target_os = "linux", target_os = "macos")
))]

//! HOUSE-BLIND NETTING ACROSS REAL SEPARATE OS PROCESSES — the teeth.
//!
//! `examples/distributed_ceremony_demo.rs` runs the same ceremony as isolated
//! structs in ONE process and says so: the no-single-viewer property there is
//! enforced by Rust module privacy. This harness moves the committee out of the
//! address space entirely. Each custody party is a distinct `threshold-committee-party`
//! PROCESS (its own pid, its own TCP socket, its own `0600` secret file); the DKG
//! runs over real TCP with sealed native-PQ envelopes; and the clearing house
//! (this test process) holds NO share. The no-single-viewer property is now an OS
//! boundary — no party's process can name another party's custody row, because it
//! is not in the same address space to name.
//!
//! What this proves end-to-end, across processes:
//!   1. `N` party PROCESSES run the real `DistributedDkg` to a collective key,
//!      each deriving the same public setup digest in its own process.
//!   2. The clearing house encrypts `M` private member obligation books under the
//!      collective key and NETS them HOMOMORPHICALLY into one ciphertext (nobody
//!      sees an obligation; the additive fold needs no ct×ct, no relinearization).
//!   3. A `t`-subset of the party processes each partial-decrypts the net
//!      ciphertext from its own custody row and signs; the clearing house combines
//!      `t` signed shares and recovers ONLY the net vector. `Σ nets = 0` and it is
//!      byte-for-byte the cleartext reference.
//!   4. A dealer that lies to one recipient is refused BY that recipient, in its
//!      own process, with an attributed error — the committee never comes up.
//!
//! The netting logic (obligation books, `member_contribution`, `reference_nets`,
//! the `signed_add` fold, the `center` decode) is ported verbatim from the
//! in-process demonstrator; only the committee changes from in-process actors to
//! spawned processes. The process-spawning + TCP protocol machinery is the same
//! as `tests/distributed_threshold_committee.rs`.
//!
//! `dregg-pq` aborts a process that reaches its unaudited fallback, so this test
//! and the party binaries install the Lean-verified ML-DSA/ML-KEM cores.
//! `DREGG_ALLOW_UNAUDITED_PQ` is never set — it is explicitly REMOVED from the
//! children's environment, so an operator's ambient opt-in cannot silently turn
//! this into a test of unaudited crypto.

use std::collections::BTreeSet;
use std::fs;
use std::io::{BufRead, BufReader, Read};
use std::net::{SocketAddr, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

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
use fhe::bfv::{Encoding, Plaintext, PublicKey};
use fhe_traits::{DeserializeParametrized, FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::convex_step::{center, encode_signed, signed_add, SignedCt};
use fhegg_fhe::mpc_party::transport::{EqualityTransportRoster, NativePqTransportIdentity};
use fhegg_fhe::threshold::distributed::{
    decode_enrollment, encode_enrollment, DistributedDkg, SEQUENCE_OPEN_REQUEST,
    SEQUENCE_OPEN_RESPONSE, SEQUENCE_PUBLIC_KEY_RESPONSE,
};
use fhegg_fhe::threshold::quorum::{
    AuthenticatedQuorumCombiner, AuthenticatedQuorumRoster, QuorumOpeningSession,
};
use fhegg_fhe::threshold::BfvParams;
use rand::rngs::{OsRng, StdRng};
use rand::{Rng, RngCore, SeedableRng};

// ── committee shape (a real t-of-n across processes) ─────────────────────────
const N_PARTIES: usize = 4;
const THRESHOLD: usize = 3;

// ── the house-blind clearing round (ported from distributed_ceremony_demo) ───
/// Members of the multilateral clearing ring. Each is one SIMD slot of the net
/// ciphertext, so ONE decrypt reveals every member's net at once.
const N_MEMBERS: usize = 128;
/// How many other members each member owes (sparse, realistic).
const OBLIGATIONS_PER_MEMBER: usize = 8;
/// Max gross amount of one bilateral obligation.
const MAX_AMOUNT: i64 = 50;
/// Conservative signed-window cap for one member's obligation vector.
const MEMBER_GROSS_CAP: i64 = (OBLIGATIONS_PER_MEMBER as i64) * MAX_AMOUNT;

const SETUP_TIMEOUT: Duration = Duration::from_secs(600);
const IO_TIMEOUT: Duration = Duration::from_secs(300);

const KIND_OPEN_REQUEST: u8 = 3;
const KIND_PUBLIC_KEY_REQUEST: u8 = 4;
const KIND_SHUTDOWN: u8 = 5;

// ─────────────────────────────────────────────────────────────────────────────
//  Process-spawn + TCP machinery — the same shape as
//  tests/distributed_threshold_committee.rs. Each party is a distinct OS process.
// ─────────────────────────────────────────────────────────────────────────────

/// A party process plus the pid it reported for ITSELF.
struct PartyProcess {
    child: Child,
    reported_pid: u32,
    address: SocketAddr,
}

impl Drop for PartyProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn install_verified_pq_cores() {
    assert!(
        std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none(),
        "this test must not run under the unaudited-PQ opt-in"
    );
    assert!(matches!(
        install_verified_mldsa_keygen_core_real(
            dregg_lean_ffi::mldsa_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mldsa_keygen_real(wire).ok(),
        ),
        MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mldsa_sign_core_real(
            dregg_lean_ffi::fips204_sign_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_sign_real(wire).ok(),
        ),
        MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mldsa_verify_core(
            dregg_lean_ffi::fips204_verify_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_verify_real(wire).ok(),
        ),
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mlkem_keygen_core(
            dregg_lean_ffi::mlkem_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_keygen_real(wire).ok(),
        ),
        MlKemKeygenCoreInstall::Installed | MlKemKeygenCoreInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mlkem_encaps_core(
            dregg_lean_ffi::mlkem_encaps_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_encaps_real(wire).ok(),
        ),
        MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mlkem_decaps_core(
            dregg_lean_ffi::mlkem_decaps_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_decaps_real(wire).ok(),
        ),
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled
    ));
}

fn session_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "fhegg-distributed-netting-{name}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(path.join("enroll")).expect("session dir");
    path
}

/// Enroll THIS process as the relying party (the clearing house): roster slot `n`.
/// It publishes only its PUBLIC identity; it never holds a custody share.
fn enroll_relying_party(dir: &Path) -> NativePqTransportIdentity {
    let mut seed = [0u8; 32];
    OsRng.try_fill_bytes(&mut seed).expect("OS entropy");
    let (encapsulation_key, decapsulation_key) = ml_kem768_keygen();
    let identity = NativePqTransportIdentity::from_material(
        SigningKey::from_bytes(&seed),
        encapsulation_key,
        decapsulation_key,
    )
    .expect("relying-party identity");
    fs::write(
        dir.join("enroll").join(format!("{N_PARTIES}.pub")),
        encode_enrollment(&identity.public_identity()),
    )
    .expect("publish the relying party enrollment");
    identity
}

fn spawn_party(dir: &Path, party: usize, tamper_victim: Option<usize>) -> PartyProcess {
    spawn_party_inner(dir, party, tamper_victim, false)
}

/// Same, but capture this party's stderr so a REFUSAL can be read back and
/// asserted on (which check refused, not merely that it exited non-zero).
fn spawn_party_capturing_stderr(dir: &Path, party: usize) -> PartyProcess {
    spawn_party_inner(dir, party, None, true)
}

fn spawn_party_inner(
    dir: &Path,
    party: usize,
    tamper_victim: Option<usize>,
    capture_stderr: bool,
) -> PartyProcess {
    let mut command = Command::new(env!("CARGO_BIN_EXE_threshold-committee-party"));
    command
        .args([
            "serve",
            dir.to_str().expect("utf-8 session dir"),
            &party.to_string(),
            &N_PARTIES.to_string(),
            &THRESHOLD.to_string(),
        ])
        .env_remove("DREGG_ALLOW_UNAUDITED_PQ")
        .stdout(Stdio::piped())
        .stderr(if capture_stderr {
            Stdio::piped()
        } else {
            Stdio::inherit()
        });
    if let Some(victim) = tamper_victim {
        command.env("FHEGG_COMMITTEE_TAMPER_ROW", victim.to_string());
    }
    let mut child = command.spawn().expect("spawn a committee party process");

    // The first stdout line is the party's own getpid() and listen address.
    // Comparing it against the pid the OS gave the PARENT is the evidence that
    // these are separate processes, not threads with a story.
    let stdout = child.stdout.take().expect("piped stdout");
    let mut line = String::new();
    BufReader::new(stdout)
        .read_line(&mut line)
        .expect("party announcement");
    let fields = line.split_whitespace().collect::<Vec<_>>();
    assert_eq!(
        fields.first().copied(),
        Some("party"),
        "announcement: {line}"
    );
    let reported_pid = fields[3].parse::<u32>().expect("pid field");
    let address = fields
        .last()
        .expect("address field")
        .parse::<SocketAddr>()
        .expect("listen address");
    PartyProcess {
        child,
        reported_pid,
        address,
    }
}

/// One request/response round trip against a party process. The header's sender
/// field is the relying party's roster slot (`N_PARTIES`); the sealed envelope
/// inside re-binds the real route, so the header is public routing only.
fn request(address: SocketAddr, kind: u8, payload: &[u8]) -> Vec<u8> {
    let mut stream =
        TcpStream::connect_timeout(&address, IO_TIMEOUT).expect("connect to a committee party");
    stream.set_read_timeout(Some(IO_TIMEOUT)).expect("timeout");
    stream.set_write_timeout(Some(IO_TIMEOUT)).expect("timeout");
    let mut header = [0u8; 9];
    header[0] = kind;
    header[1..5].copy_from_slice(&(N_PARTIES as u32).to_be_bytes());
    header[5..].copy_from_slice(&(payload.len() as u32).to_be_bytes());
    use std::io::Write;
    stream.write_all(&header).expect("write header");
    stream.write_all(payload).expect("write payload");
    stream.flush().expect("flush");
    let mut reply_header = [0u8; 9];
    stream.read_exact(&mut reply_header).expect("reply header");
    let length = u32::from_be_bytes(reply_header[5..].try_into().unwrap()) as usize;
    let mut reply = vec![0u8; length];
    stream.read_exact(&mut reply).expect("reply payload");
    reply
}

/// Tell a party to stop, WITHOUT waiting for its answer (it replies then exits,
/// so its answer races its own teardown).
fn shutdown(address: SocketAddr) {
    let Ok(mut stream) = TcpStream::connect_timeout(&address, IO_TIMEOUT) else {
        return;
    };
    let mut header = [0u8; 9];
    header[0] = KIND_SHUTDOWN;
    header[1..5].copy_from_slice(&(N_PARTIES as u32).to_be_bytes());
    use std::io::Write;
    let _ = stream.write_all(&header);
    let _ = stream.flush();
}

/// Wait for every party to publish custody, and FAIL THE MOMENT A PARTY DIES.
fn wait_for_ready(parties: &mut [PartyProcess], paths: &[PathBuf], deadline: Instant) {
    while Instant::now() < deadline {
        if paths.iter().all(|path| path.exists()) {
            return;
        }
        for (index, party) in parties.iter_mut().enumerate() {
            if let Some(status) = party.child.try_wait().expect("wait on a party") {
                panic!("party {index} died during setup with {status}");
            }
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    panic!("the distributed DKG did not complete before the deadline");
}

/// Wire layout the party's `decode_open_request` expects.
fn encode_open_request(
    nonce: [u8; 32],
    roster: &[usize],
    plain_bound: u64,
    ciphertext: &[u8],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&(roster.len() as u64).to_le_bytes());
    for &party in roster {
        out.extend_from_slice(&(party as u64).to_le_bytes());
    }
    out.extend_from_slice(&plain_bound.to_le_bytes());
    out.extend_from_slice(&(ciphertext.len() as u64).to_le_bytes());
    out.extend_from_slice(ciphertext);
    out
}

// ─────────────────────────────────────────────────────────────────────────────
//  The house-blind clearing computation — ported verbatim from the in-process
//  demonstrator (examples/distributed_ceremony_demo.rs).
// ─────────────────────────────────────────────────────────────────────────────

/// A private bilateral obligation book: `g[i][j]` = gross amount member `i` owes
/// member `j` (diagonal 0). Deterministic, so the run is reproducible.
struct ObligationBook {
    g: Vec<Vec<i64>>,
    nonzero: usize,
    gross: i64,
}

fn build_obligation_book() -> ObligationBook {
    let mut rng = StdRng::seed_from_u64(0x0b11_6a70_c1ea_1234);
    let mut g = vec![vec![0i64; N_MEMBERS]; N_MEMBERS];
    let mut nonzero = 0usize;
    let mut gross = 0i64;
    for (i, row) in g.iter_mut().enumerate() {
        for _ in 0..OBLIGATIONS_PER_MEMBER {
            let j = rng.gen_range(0..N_MEMBERS);
            if j == i {
                continue;
            }
            let amount = rng.gen_range(1..=MAX_AMOUNT);
            if row[j] == 0 {
                nonzero += 1;
            }
            row[j] += amount;
            gross += amount;
        }
    }
    ObligationBook { g, nonzero, gross }
}

/// Member `i`'s contribution vector to the global net: `+g[i][j]` credited to
/// each creditor `j`, and `-Σ_j g[i][j]` debited to `i`. Sums to zero over slots.
fn member_contribution(book: &ObligationBook, i: usize) -> Vec<i64> {
    let mut v = vec![0i64; N_MEMBERS];
    let mut owing = 0i64;
    for j in 0..N_MEMBERS {
        v[j] += book.g[i][j];
        owing += book.g[i][j];
    }
    v[i] -= owing;
    v
}

/// Cleartext reference net vector (what the encrypted clearing must reproduce).
fn reference_nets(book: &ObligationBook) -> Vec<i64> {
    let mut nets = vec![0i64; N_MEMBERS];
    for i in 0..N_MEMBERS {
        for j in 0..N_MEMBERS {
            nets[j] += book.g[i][j]; // j is owed
            nets[i] -= book.g[i][j]; // i owes
        }
    }
    nets
}

/// Encrypt one member's contribution vector under the COLLECTIVE key (held by no
/// single party), wrapped as a signed ciphertext with a conservative window.
fn encrypt_contribution(pk: &PublicKey, params: &BfvParams, values: &[i64], t: u64) -> SignedCt {
    let mut slots = vec![0u64; params.degree()];
    for (slot, &v) in slots.iter_mut().zip(values) {
        *slot = encode_signed(v, t);
    }
    let pt = Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("simd encode");
    let ct = pk
        .try_encrypt(&pt, &mut rand_09::rng())
        .expect("collective-key encrypt");
    let lean =
        LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), params.moduli(), params.degree(), t - 1)
            .expect("lean ciphertext");
    SignedCt::new(lean, -MEMBER_GROSS_CAP, MEMBER_GROSS_CAP, t).expect("signed window")
}

// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn distributed_netting_across_real_processes() {
    println!("\n── HOUSE-BLIND NETTING ACROSS REAL SEPARATE OS PROCESSES ──\n");
    install_verified_pq_cores();
    println!("verified-PQ cores installed (ML-DSA-65 + ML-KEM-768, audited Lean cores)");

    let dir = session_dir("clear");
    let identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    // ── SPAWN: N party PROCESSES, plus DKG over TCP to the collective key. ─────
    let spawn_dkg_start = Instant::now();
    let mut parties = (0..N_PARTIES)
        .map(|party| spawn_party(&dir, party, None))
        .collect::<Vec<_>>();

    // THE PROCESSES ARE REALLY SEPARATE: each reported the pid the OS gave the
    // parent for it, none is this (clearing-house) process, and no two share one.
    let mut pids = BTreeSet::new();
    for (index, party) in parties.iter().enumerate() {
        assert_eq!(
            party.child.id(),
            party.reported_pid,
            "party {index} reported a pid that is not the one the OS gave the parent"
        );
        assert_ne!(
            party.reported_pid,
            std::process::id(),
            "party {index} is running inside the clearing house's process"
        );
        assert!(
            pids.insert(party.reported_pid),
            "two parties share one process"
        );
    }
    println!(
        "clearing house pid {} holds NO share; {} custody parties in {} DISTINCT OS processes {:?}",
        std::process::id(),
        N_PARTIES,
        pids.len(),
        pids
    );

    let ready = (0..N_PARTIES)
        .map(|party| dir.join("ready").join(format!("{party}.ready")))
        .collect::<Vec<_>>();
    wait_for_ready(&mut parties, &ready, deadline);

    // Every party independently derived the same public setup digest, in its own
    // process, from the messages it verified itself.
    let digests = ready
        .iter()
        .map(|path| fs::read(path).expect("setup digest"))
        .collect::<Vec<_>>();
    assert!(
        digests.windows(2).all(|pair| pair[0] == pair[1]),
        "the parties finished on DIFFERENT setups"
    );

    // Build the clearing house's public view of the ceremony (no secret): the
    // enrolled roster, the session, and the DKG used to seal/open envelopes.
    let params = BfvParams::fold_set();
    let mut identities = (0..N_PARTIES)
        .map(|party| {
            decode_enrollment(
                &fs::read(dir.join("enroll").join(format!("{party}.pub"))).expect("enrollment"),
            )
            .expect("enrollment")
        })
        .collect::<Vec<_>>();
    let party_keys = identities
        .iter()
        .map(|identity| identity.ed25519())
        .collect::<Vec<_>>();
    let roster = EqualityTransportRoster::new_native_post_quantum(
        std::mem::take(&mut identities),
        identity.public_identity(),
    )
    .expect("native-PQ roster");
    let dkg = DistributedDkg::new(roster, THRESHOLD, params.clone()).expect("dkg parameters");

    // THE COLLECTIVE KEY, accepted only on unanimous agreement across processes.
    let mut collective_bytes: Option<Vec<u8>> = None;
    for (party, process) in parties.iter().enumerate() {
        let sealed = request(process.address, KIND_PUBLIC_KEY_REQUEST, &[]);
        let answer = dkg
            .open(
                &identity,
                party,
                dkg.relying_party(),
                SEQUENCE_PUBLIC_KEY_RESPONSE,
                &sealed,
            )
            .expect("a signed collective-key answer");
        assert_eq!(&answer[..32], digests[party].as_slice());
        match &collective_bytes {
            None => collective_bytes = Some(answer[32..].to_vec()),
            Some(expected) => assert_eq!(
                expected,
                &answer[32..].to_vec(),
                "party {party} reported a DIFFERENT collective public key"
            ),
        }
    }
    let collective_bytes = collective_bytes.expect("a collective key");
    let collective =
        PublicKey::from_bytes(&collective_bytes, params.arc()).expect("collective public key");
    let spawn_dkg_ms = spawn_dkg_start.elapsed().as_secs_f64() * 1e3;

    let t = params.plaintext_modulus();
    let window_half = (t - 1) / 2;
    println!(
        "committee: t={THRESHOLD}-of-{N_PARTIES}; BFV degree {} ({} SIMD slots), plaintext modulus {t}, centered window +/-{window_half}",
        params.degree(),
        params.degree()
    );
    println!(
        "DKG over TCP done in {spawn_dkg_ms:.0} ms (process spawn + ceremony) — collective key agreed by all {N_PARTIES} parties, setup digest {}",
        hex8(&digests[0])
    );
    println!("  (the collective secret s = sum s_d was never assembled in any process)");

    // ── NETTING: encrypt M private member books, fold HOMOMORPHICALLY. ────────
    let book = build_obligation_book();
    let reference = reference_nets(&book);
    assert_eq!(
        reference.iter().sum::<i64>(),
        0,
        "cleartext netting must conserve"
    );
    let window_use: i64 = (N_MEMBERS as i64) * MEMBER_GROSS_CAP;
    assert!(
        window_use < window_half as i64,
        "batch would exceed the signed window ({window_use} >= {window_half})"
    );
    println!(
        "clearing ring: M={N_MEMBERS} members, {} private bilateral obligations ({} total gross), net packed into {N_MEMBERS} SIMD slots",
        book.nonzero, book.gross
    );

    let compute_start = Instant::now();
    let mut netted: Option<SignedCt> = None;
    for i in 0..N_MEMBERS {
        let contribution = member_contribution(&book, i);
        let ct = encrypt_contribution(&collective, &params, &contribution, t);
        netted = Some(match netted.take() {
            None => ct,
            Some(acc) => signed_add(&acc, &ct, t).expect("homomorphic net add"),
        });
    }
    let net_ct = netted.expect("at least one member");
    let compute_ms = compute_start.elapsed().as_secs_f64() * 1e3;
    println!(
        "encrypted {N_MEMBERS} member books under the collective key + netted homomorphically in {compute_ms:.0} ms (additive regime, no ct*ct, no relinearization)"
    );

    // ── DISTRIBUTED DECRYPT across the processes: the net ciphertext goes to the
    //    t party processes; each partial-decrypts its OWN custody row and signs;
    //    the clearing house combines t signed shares. The house holds no share.
    let net_fhe_bytes = net_ct.ciphertext().to_fhe_bytes();
    let plain_bound = t - 1;
    let quorum: Vec<usize> = (0..THRESHOLD).collect(); // canonical, increasing
    let mut nonce = [0u8; 32];
    OsRng.try_fill_bytes(&mut nonce).expect("OS entropy");
    let opening = QuorumOpeningSession::new(dkg.session().clone(), nonce, quorum.clone())
        .expect("t-party opening");
    let request_body = encode_open_request(nonce, &quorum, plain_bound, &net_fhe_bytes);

    let decrypt_start = Instant::now();
    let mut framed = Vec::with_capacity(quorum.len());
    for &party in &quorum {
        let sealed_request = dkg
            .seal(
                &identity,
                dkg.relying_party(),
                party,
                SEQUENCE_OPEN_REQUEST,
                &request_body,
            )
            .expect("seal the opening request");
        let sealed_answer = request(parties[party].address, KIND_OPEN_REQUEST, &sealed_request);
        assert!(
            !sealed_answer.is_empty(),
            "party {party} refused to answer the opening"
        );
        framed.push(
            dkg.open(
                &identity,
                party,
                dkg.relying_party(),
                SEQUENCE_OPEN_RESPONSE,
                &sealed_answer,
            )
            .expect("an authenticated share answer"),
        );
    }

    // Reconstruct the net lean from the SAME wire bytes + bound the parties saw,
    // so the combiner and the custody processes decrypt byte-identical inputs.
    let lean_net = LeanCiphertext::from_fhe_bytes(
        &net_fhe_bytes,
        params.moduli(),
        params.degree(),
        plain_bound,
    )
    .expect("net lean ciphertext");
    let quorum_roster =
        AuthenticatedQuorumRoster::new(dkg.session().clone(), party_keys).expect("custody roster");
    let opened = AuthenticatedQuorumCombiner::new(quorum_roster)
        .combine_framed(&opening, &lean_net, &framed, &params)
        .expect("t signed shares reveal the net vector");
    let decrypt_ms = decrypt_start.elapsed().as_secs_f64() * 1e3;

    // Center-decode and check against the cleartext reference + conservation.
    let revealed: Vec<i64> = (0..N_MEMBERS).map(|k| center(opened[k], t)).collect();
    assert_eq!(
        revealed, reference,
        "the process committee's house-blind clearing did not reproduce the cleartext nets"
    );
    assert_eq!(
        revealed.iter().sum::<i64>(),
        0,
        "revealed nets do not conserve"
    );
    println!(
        "threshold decrypt across {THRESHOLD} party processes + combine in {decrypt_ms:.0} ms — revealed ONLY the {N_MEMBERS}-slot net vector"
    );

    let (creditor, &max_net) = revealed.iter().enumerate().max_by_key(|(_, &v)| v).unwrap();
    let (debtor, &min_net) = revealed.iter().enumerate().min_by_key(|(_, &v)| v).unwrap();
    println!(
        "  sample nets: member {creditor} is owed net {max_net}; member {debtor} owes net {}; Sum nets = 0",
        -min_net
    );

    let total_ms = spawn_dkg_ms + compute_ms + decrypt_ms;
    println!(
        "\n* {N_PARTIES} parties in {N_PARTIES} separate OS processes {pids:?}, t={THRESHOLD} threshold; \
         {} orders across M={N_MEMBERS} members cleared HOUSE-BLIND in {total_ms:.0} ms \
         (spawn+DKG {spawn_dkg_ms:.0} + netting {compute_ms:.0} + decrypt {decrypt_ms:.0}). \
         No process ever saw another's custody share, and nobody saw an order.\n",
        book.nonzero
    );

    for process in &parties {
        shutdown(process.address);
    }
    let _ = fs::remove_dir_all(&dir);
}

// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_tampering_dealer_is_caught_and_attributed_across_processes() {
    println!("\n── TAMPER: a dealer that lies to one recipient (separate processes) ──\n");
    install_verified_pq_cores();
    let dir = session_dir("tamper");
    let _identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    // Party 0 deals honestly to everyone EXCEPT party 1, whose row it corrupts
    // after committing to the honest one. Party 1 must REFUSE and exit non-zero;
    // nothing may reach custody — a committee with a corrupted row must not come up.
    let mut parties = Vec::new();
    parties.push(spawn_party(&dir, 0, Some(1)));
    parties.push(spawn_party_capturing_stderr(&dir, 1));
    for party in 2..N_PARTIES {
        parties.push(spawn_party(&dir, party, None));
    }

    let victim = &mut parties[1];
    let mut status = None;
    while Instant::now() < deadline {
        match victim.child.try_wait().expect("wait on the victim") {
            Some(exit) => {
                status = Some(exit);
                break;
            }
            None => std::thread::sleep(Duration::from_millis(100)),
        }
    }
    let status = status.expect("party 1 never terminated on the corrupted row");
    assert!(
        !status.success(),
        "party 1 ACCEPTED a row that does not open its dealer's commitment"
    );
    assert_eq!(
        status.code(),
        Some(2),
        "party 1 exited with an unexpected status"
    );
    let mut refusal = String::new();
    victim
        .child
        .stderr
        .take()
        .expect("captured victim stderr")
        .read_to_string(&mut refusal)
        .expect("read the victim's refusal");
    assert!(
        refusal.contains("VssCommitmentMismatch { dealer: 0, recipient: 1 }"),
        "party 1 died, but NOT on the dealer-0 commitment opening it was supposed to \
         refuse — the exit code alone would have hidden that. stderr was:\n{refusal}"
    );
    assert!(
        !dir.join("ready").join("1.ready").exists(),
        "the victim reached custody anyway"
    );
    println!(
        "malice ATTRIBUTED: party 1's process refused with VssCommitmentMismatch {{ dealer: 0, recipient: 1 }} \
         and exited code 2 — the committee does not come up, and the liar is named.\n"
    );

    let _ = fs::remove_dir_all(&dir);
}

fn hex8(bytes: &[u8]) -> String {
    bytes.iter().take(8).map(|b| format!("{b:02x}")).collect()
}
