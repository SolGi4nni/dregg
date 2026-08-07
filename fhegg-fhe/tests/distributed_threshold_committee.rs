#![cfg(any(target_os = "linux", target_os = "macos"))]

//! THE COMMITTEE IS ACTUALLY DISTRIBUTED — the teeth, against real processes.
//!
//! Every previous threshold committee in this tree runs its parties as threads in
//! one process, and both of them say so in their own docs. This test stands up
//! three party PROCESSES (distinct OS pids, real TCP, sealed native-PQ envelopes)
//! and drives them with the PRODUCTION relying-party caller
//! ([`fhegg_fhe::threshold::relying_party::DistributedCommitteeClient`]) — the same
//! object a market would use — as a fourth process (this test).
//!
//! It exercises the verified path end to end:
//!
//!   * three separate pids reach VERIFIED custody: collective-key agreement, then
//!     the commit round where each party publishes its own aggregate-row
//!     commitment and finalizes a shared transcript ([`three_party_processes_reach_verified_custody`]);
//!   * `t` parties open a ciphertext, each carrying a zero-knowledge decrypt-share
//!     certificate, and a below-`t` roster is refused
//!     ([`three_party_processes_open_verified_at_t_and_refuse_below_it`], `#[ignore]` —
//!     the degree-4096 certificate is minutes of proving);
//!   * a dealer that lies to ONE recipient is refused BY that recipient, and the
//!     committee never comes up ([`a_dealer_that_lies_to_one_recipient_is_refused_by_that_recipient`]).
//!
//! The certificate-FORGERY refusal (a mutated proof rejected) is proven fast at the
//! library level in `threshold::quorum::vss_tests` rather than over the wire here.
//!
//! The relying party holds no share and never learns one. `dregg-pq` aborts a
//! process that reaches its unaudited fallback, so both this test and the party
//! binaries install the Lean-verified ML-DSA cores. `DREGG_ALLOW_UNAUDITED_PQ` is
//! never set — it is explicitly REMOVED from the children's environment.

use std::collections::BTreeSet;
use std::fs;
use std::io::{BufRead, BufReader, Read};
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use fhe_traits::Serialize as FheSerializeCt;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};

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
use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::mpc_party::transport::{EqualityTransportRoster, NativePqTransportIdentity};
use fhegg_fhe::threshold::distributed::{decode_enrollment, encode_enrollment, DistributedDkg};
use fhegg_fhe::threshold::relying_party::DistributedCommitteeClient;
use fhegg_fhe::threshold::BfvParams;
use rand::rngs::OsRng;
use rand::RngCore;

const N_PARTIES: usize = 3;
const THRESHOLD: usize = 2;
const SECRET_VALUE: u64 = 41_237;
const PLAIN_BOUND: u64 = 65_536;
const SETUP_TIMEOUT: Duration = Duration::from_secs(600);

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

/// Build the production relying-party caller from the enrolled roster on disk.
fn committee_client(
    dir: &Path,
    identity: NativePqTransportIdentity,
    addresses: Vec<SocketAddr>,
    params: &BfvParams,
) -> DistributedCommitteeClient {
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
    DistributedCommitteeClient::new(identity, dkg, addresses, party_keys).expect("committee client")
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

/// Assert the three processes are really separate, and return their sorted pids.
fn assert_separate_processes(parties: &[PartyProcess]) -> BTreeSet<u32> {
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
    pids
}

fn ready_paths(dir: &Path) -> Vec<PathBuf> {
    (0..N_PARTIES)
        .map(|party| dir.join("ready").join(format!("{party}.ready")))
        .collect()
}

#[test]
fn three_party_processes_reach_verified_custody() {
    install_verified_pq_cores();
    let dir = session_dir("custody");
    let identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    let mut parties = (0..N_PARTIES)
        .map(|party| spawn_party(&dir, party, None))
        .collect::<Vec<_>>();

    let pids = assert_separate_processes(&parties);
    eprintln!(
        "relying party pid {} ; committee pids {:?}",
        std::process::id(),
        pids
    );

    let ready = ready_paths(&dir);
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
    let addresses = parties
        .iter()
        .map(|party| party.address)
        .collect::<Vec<_>>();
    let client = committee_client(&dir, identity, addresses, &params);

    // The collective key is agreed only on unanimous report, across three pids.
    let collective = client
        .collective_public_key()
        .expect("collective key agreement across three processes");

    // The verified commit round: each party publishes its own aggregate-row
    // commitment and finalizes ONE shared transcript. This is the round that lets a
    // later opening carry a decrypt-share certificate.
    let transcript = client
        .verified_transcript(&collective)
        .expect("verified commit + finalize round across three processes");
    assert_ne!(
        transcript.digest(),
        [0u8; 32],
        "the verified transcript did not bind a setup"
    );

    for party in 0..N_PARTIES {
        client.shutdown(party);
    }
    let _ = fs::remove_dir_all(&dir);
}

/// The DISTRIBUTED relinearization ceremony, end to end across three PROCESSES.
///
/// This is the step that had no distributed counterpart at all: the committee
/// could open, but nothing could multiply, so no caller needing a `ct x ct`
/// could move onto it. The ceremony is `n`-of-`n` over DEALERS — relin runs on
/// `s = sum_d s_d` because the Lagrange custody rows provably cannot carry it —
/// and each party's short secret never leaves the process that sampled it.
///
/// The key returned has already passed its acceptance gate, which decrypts fresh
/// random products through this committee's REAL `t`-of-`n` certified opening.
/// So the single `expect` below is not "a key came back"; it is "a key came back
/// that relinearizes, checked by decrypting products across three processes".
#[test]
#[ignore = "degree-4096 relin ceremony plus its acceptance gate over three processes: minutes; run with --release --ignored"]
fn three_party_processes_run_the_relinearization_ceremony() {
    install_verified_pq_cores();
    let dir = session_dir("relin");
    let identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    let mut parties = (0..N_PARTIES)
        .map(|party| spawn_party(&dir, party, None))
        .collect::<Vec<_>>();
    assert_separate_processes(&parties);
    let ready = ready_paths(&dir);
    wait_for_ready(&mut parties, &ready, deadline);

    let params = BfvParams::fold_set();
    let addresses = parties
        .iter()
        .map(|party| party.address)
        .collect::<Vec<_>>();
    let client = committee_client(&dir, identity, addresses, &params);

    let collective = client.collective_public_key().expect("collective key");
    let transcript = client
        .verified_transcript(&collective)
        .expect("verified commit + finalize");

    let opening_roster: Vec<usize> = (0..THRESHOLD).collect();
    let key = client
        .relin_key(
            &collective,
            &transcript,
            [0x5c; 32],
            SETUP_TIMEOUT,
            2,
            &opening_roster,
        )
        .expect("the distributed relin ceremony must produce a key that passes its own gate");

    // Independently of the gate: a product built with this key opens correctly
    // through the same t-of-n committee.
    let engine = MulEngine::new(&key, params.arc()).expect("multiplicator");
    let (left, right) = (7u64, 9u64);
    let product = engine
        .multiply(
            &BoundedCiphertext::new(encrypt_value(&collective, &params, left), 32),
            &BoundedCiphertext::new(encrypt_value(&collective, &params, right), 32),
        )
        .expect("ct x ct multiply under the distributed relin key");
    let opened = client
        .open_verified(
            &transcript,
            &product.ct.to_bytes(),
            product.plain_bound,
            &opening_roster,
            [0x5d; 32],
        )
        .expect("certified opening of the relinearized product");
    assert_eq!(
        opened.first().copied(),
        Some(left * right),
        "the distributed relin key did not relinearize across three processes"
    );

    for party in 0..N_PARTIES {
        client.shutdown(party);
    }
    let _ = fs::remove_dir_all(&dir);
}

fn encrypt_value(
    collective: &fhegg_fhe::threshold::CollectivePublicKey,
    params: &BfvParams,
    value: u64,
) -> fhe::bfv::Ciphertext {
    use fhe::bfv::{Encoding, Plaintext};
    use fhe_traits::{FheEncoder, FheEncrypter};
    let mut slots = vec![0u64; params.degree()];
    slots[0] = value;
    let plaintext =
        Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("SIMD encode");
    collective
        .pk
        .try_encrypt(&plaintext, &mut rand_09::rng())
        .expect("collective encrypt")
}

#[test]
#[ignore = "degree-4096 decrypt-share certificate over three processes: minutes; run with --release --ignored"]
fn three_party_processes_open_verified_at_t_and_refuse_below_it() {
    install_verified_pq_cores();
    let dir = session_dir("open");
    let identity = enroll_relying_party(&dir);
    let deadline = Instant::now() + SETUP_TIMEOUT;

    let mut parties = (0..N_PARTIES)
        .map(|party| spawn_party(&dir, party, None))
        .collect::<Vec<_>>();
    assert_separate_processes(&parties);

    let ready = ready_paths(&dir);
    wait_for_ready(&mut parties, &ready, deadline);

    let params = BfvParams::fold_set();
    let addresses = parties
        .iter()
        .map(|party| party.address)
        .collect::<Vec<_>>();
    let client = committee_client(&dir, identity, addresses, &params);

    let collective = client
        .collective_public_key()
        .expect("collective key agreement");
    let transcript = client
        .verified_transcript(&collective)
        .expect("verified commit + finalize round");

    // ── ENCRYPT. No secret and no quorum is involved.
    let mut slots = vec![0u64; params.degree()];
    slots[0] = SECRET_VALUE;
    let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("encode");
    let ciphertext = collective
        .pk
        .try_encrypt(&plaintext, &mut rand_09::rng())
        .expect("encrypt to the collective key");
    let ciphertext_bytes = ciphertext.to_bytes();

    // ── OPEN AT t. Parties 0 and 1 each produce a CERTIFICATE-carrying share in
    // their own process, and the verified combiner refuses any share without one.
    let mut nonce = [0u8; 32];
    OsRng.try_fill_bytes(&mut nonce).expect("OS entropy");
    let opened = client
        .open_verified(&transcript, &ciphertext_bytes, PLAIN_BOUND, &[0, 1], nonce)
        .expect("t certificate-carrying shares open the ciphertext");
    assert_eq!(
        opened[0], SECRET_VALUE,
        "the distributed committee did not reproduce the plaintext"
    );

    // ── REFUSE BELOW t, STRUCTURAL. A single-party roster is refused by the
    // verified opening session's arity check, through the production caller.
    let mut nonce2 = [0u8; 32];
    OsRng.try_fill_bytes(&mut nonce2).expect("OS entropy");
    assert!(
        client
            .open_verified(&transcript, &ciphertext_bytes, PLAIN_BOUND, &[0], nonce2)
            .is_err(),
        "a below-threshold roster must be refused"
    );

    for party in 0..N_PARTIES {
        client.shutdown(party);
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
