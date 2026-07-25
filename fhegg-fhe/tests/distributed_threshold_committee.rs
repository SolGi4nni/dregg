#![cfg(any(target_os = "linux", target_os = "macos"))]

//! THE COMMITTEE IS ACTUALLY DISTRIBUTED — the teeth, against real processes.
//!
//! Every previous threshold committee in this tree runs its parties as threads in
//! one process, and both of them say so in their own docs. This test stands up
//! three party PROCESSES (distinct OS pids, real TCP, sealed native-PQ envelopes)
//! plus a fourth process — this test — as the relying party, and then attacks it:
//!
//!   * `t` parties open a ciphertext encrypted to the collective key;
//!   * `t-1` shares are refused, and a `t-1` coalition that FORGES the missing
//!     share to defeat the arity check still does not recover the plaintext;
//!   * a dealer that lies to ONE recipient is refused BY that recipient, and the
//!     committee never comes up.
//!
//! The relying party holds no share and never learns one. It receives `t` signed
//! decryption shares and combines them.
//!
//! `dregg-pq` aborts a process that reaches its unaudited fallback, so both this
//! test and the party binaries install the Lean-verified ML-DSA cores.
//! `DREGG_ALLOW_UNAUDITED_PQ` is never set — it is explicitly REMOVED from the
//! children's environment, so an operator's ambient opt-in cannot silently make
//! this a test of unaudited crypto.

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
use fhegg_fhe::mpc_party::transport::{EqualityTransportRoster, NativePqTransportIdentity};
use fhegg_fhe::threshold::distributed::{
    decode_enrollment, encode_enrollment, DistributedDkg, SEQUENCE_OPEN_REQUEST,
    SEQUENCE_OPEN_RESPONSE, SEQUENCE_PUBLIC_KEY_RESPONSE,
};
use fhegg_fhe::threshold::quorum::{
    combine_quorum, AuthenticatedQuorumCombiner, AuthenticatedQuorumDecryptShare,
    AuthenticatedQuorumRoster, QuorumDecryptShare, QuorumError, QuorumOpeningSession,
};
use fhegg_fhe::threshold::BfvParams;
use rand::rngs::OsRng;
use rand::RngCore;

const N_PARTIES: usize = 3;
const THRESHOLD: usize = 2;
const SECRET_VALUE: u64 = 41_237;
const PLAIN_BOUND: u64 = 65_536;
const SETUP_TIMEOUT: Duration = Duration::from_secs(600);
const IO_TIMEOUT: Duration = Duration::from_secs(300);

const KIND_OPEN_REQUEST: u8 = 3;
const KIND_PUBLIC_KEY_REQUEST: u8 = 4;
const KIND_SHUTDOWN: u8 = 5;

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
        "fhegg-distributed-committee-{name}-{}-{}",
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

/// Enroll THIS process as the relying party: roster slot `n`.
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
/// asserted on. "The process exited non-zero" is not the claim being made — the
/// claim names which check refused, so the test has to read it.
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

    // The first stdout line is the party's own `getpid()` and listen address.
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

/// Wait for the committee to come up, and FAIL THE MOMENT A PARTY DIES.
///
/// Without the liveness check a dead child is indistinguishable from a slow one
/// until the deadline, which turns a two-second `abort()` into a ten-minute wait
/// and hides the reason in a child's stderr.
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

#[test]
fn three_party_processes_open_at_t_and_refuse_below_it() {
    install_verified_pq_cores();
    let dir = session_dir("open");
    let identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    let mut parties = (0..N_PARTIES)
        .map(|party| spawn_party(&dir, party, None))
        .collect::<Vec<_>>();

    // ── THE PROCESSES ARE REALLY SEPARATE.
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
            "party {index} is running inside the relying party's process"
        );
        assert!(
            pids.insert(party.reported_pid),
            "two parties share one process"
        );
    }
    eprintln!(
        "relying party pid {} ; committee pids {:?}",
        std::process::id(),
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
        "the three parties finished on DIFFERENT setups"
    );

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

    // ── THE COLLECTIVE KEY, accepted only on unanimous agreement.
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

    // ── ENCRYPT. No secret and no quorum is involved.
    let mut slots = vec![0u64; params.degree()];
    slots[0] = SECRET_VALUE;
    let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("encode");
    let ciphertext = collective
        .try_encrypt(&plaintext, &mut rand_09::rng())
        .expect("encrypt to the collective key");
    let ciphertext_bytes = ciphertext.to_bytes();
    let lean = LeanCiphertext::from_fhe_bytes(
        &ciphertext_bytes,
        params.moduli(),
        params.degree(),
        PLAIN_BOUND,
    )
    .expect("lean ciphertext");

    // ── OPEN AT t. Parties 0 and 1 each produce a share in their own process.
    let quorum: Vec<usize> = vec![0, 1];
    let mut nonce = [0u8; 32];
    OsRng.try_fill_bytes(&mut nonce).expect("OS entropy");
    let opening = QuorumOpeningSession::new(dkg.session().clone(), nonce, quorum.clone())
        .expect("t-party opening");
    let request_body = encode_open_request(nonce, &quorum, PLAIN_BOUND, &ciphertext_bytes);

    let mut framed = Vec::new();
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

    let quorum_roster =
        AuthenticatedQuorumRoster::new(dkg.session().clone(), party_keys).expect("custody roster");
    let opened = AuthenticatedQuorumCombiner::new(quorum_roster.clone())
        .combine_framed(&opening, &lean, &framed, &params)
        .expect("t signed shares open the ciphertext");
    assert_eq!(
        opened[0], SECRET_VALUE,
        "the distributed committee did not reproduce the plaintext"
    );

    // ── REFUSE AT t-1, STRUCTURAL. This is an arity check and nothing more; it
    // says nothing about what one custodian could compute, which is why the
    // cryptographic statement follows immediately.
    assert_eq!(
        AuthenticatedQuorumCombiner::new(quorum_roster.clone()).combine_framed(
            &opening,
            &lean,
            &framed[..1],
            &params,
        ),
        Err(QuorumError::QuorumTooSmall { have: 1, need: 2 })
    );

    // ── REFUSE AT t-1, CRYPTOGRAPHIC. A `t-1` coalition (here: party 0 alone,
    // which is `t-1` at t=2) FORGES the missing share by re-labelling its own, so
    // the combiner sees a full-arity set and the arity check cannot be what
    // refuses it.
    let mut forged_wire = AuthenticatedQuorumDecryptShare::from_wire_bytes(&framed[0], &params)
        .expect("party 0's signed share parses")
        .share()
        .to_wire_bytes();
    // Inner body layout: magic(8) n(8) t(8) crp(32) nonce(32) vss-tag(1)
    // roster-len(8) roster(8*t) then the party index.
    const PARTY_OFFSET: usize = 8 + 8 + 8 + 32 + 32 + 1 + 8 + 8 * THRESHOLD;
    assert_eq!(
        u64::from_le_bytes(
            forged_wire[PARTY_OFFSET..PARTY_OFFSET + 8]
                .try_into()
                .unwrap()
        ),
        0,
        "the party index is not where this test thinks it is"
    );
    forged_wire[PARTY_OFFSET..PARTY_OFFSET + 8].copy_from_slice(&1u64.to_le_bytes());
    let forged = QuorumDecryptShare::from_wire_bytes(&forged_wire, &params)
        .expect("a re-labelled share is structurally well-formed");
    assert_eq!(forged.party(), 1, "the forgery claims the missing seat");

    let honest_first = AuthenticatedQuorumDecryptShare::from_wire_bytes(&framed[0], &params)
        .expect("party 0's share")
        .share()
        .clone();
    let coalition = vec![honest_first, forged];
    // The combiner ACCEPTS this set — asserted, not tolerated. If it refused, the
    // refusal would be structural again and would prove nothing new.
    let recovered = combine_quorum(&coalition, &opening, &params)
        .expect("a full-arity forged coalition passes every structural check");
    assert_ne!(
        recovered[0], SECRET_VALUE,
        "a t-1 coalition forging the missing share RECOVERED the plaintext"
    );

    // And the SIGNED path refuses the same forgery outright, because the forged
    // seat is not signed by the enrolled key that owns it.
    let mut forged_framed = framed.clone();
    forged_framed[1] = {
        let mut signed = AuthenticatedQuorumDecryptShare::from_wire_bytes(&framed[0], &params)
            .expect("party 0's signed share")
            .to_wire_bytes();
        const OUTER_OFFSET: usize = 8 + 32 + 8 + PARTY_OFFSET;
        signed[OUTER_OFFSET..OUTER_OFFSET + 8].copy_from_slice(&1u64.to_le_bytes());
        signed
    };
    assert_eq!(
        AuthenticatedQuorumCombiner::new(quorum_roster).combine_framed(
            &opening,
            &lean,
            &forged_framed,
            &params,
        ),
        Err(QuorumError::InvalidSignature { party: 1 })
    );

    for process in &parties {
        let _ = request(process.address, KIND_SHUTDOWN, &[]);
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_dealer_that_lies_to_one_recipient_is_refused_by_that_recipient() {
    install_verified_pq_cores();
    let dir = session_dir("tamper");
    let _identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    // Party 0 deals honestly to party 2 and CORRUPTS the row it deals to party 1,
    // after committing to the honest one.
    let mut parties = Vec::new();
    parties.push(spawn_party(&dir, 0, Some(1)));
    parties.push(spawn_party_capturing_stderr(&dir, 1));
    parties.push(spawn_party(&dir, 2, None));

    // Party 1 must REFUSE and exit non-zero. Nothing else may reach custody: a
    // committee with a corrupted row must not come up at all.
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
    eprintln!("victim stderr:\n{refusal}");
    assert!(
        refusal.contains("VssCommitmentMismatch { dealer: 0, recipient: 1 }"),
        "party 1 died, but NOT on the dealer-0 commitment opening it was supposed to \
         refuse — the exit code alone would have hidden that. stderr was:\n{refusal}"
    );
    assert!(
        !dir.join("ready").join("1.ready").exists(),
        "the victim reached custody anyway"
    );

    let _ = fs::remove_dir_all(&dir);
}
