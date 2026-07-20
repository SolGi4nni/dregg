use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::{DecisionTranscript, PartyMpcSession};
use serde::Deserialize;
use serde_json::json;

const N: usize = 3;
const VALUE_BITS: usize = 8;
const MODULUS: u64 = 65_537;

#[derive(Deserialize)]
struct Response {
    frames: Vec<RoutedFrame>,
    completion: Option<Completion>,
}

#[derive(Deserialize)]
struct RoutedFrame {
    sender: usize,
    recipient: usize,
    sequence: u64,
    wire_hex: String,
}

#[derive(Deserialize)]
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

struct WorkerProcess {
    child: Child,
    input: ChildStdin,
    output: ChildStdout,
}

impl WorkerProcess {
    fn spawn(args: &[String]) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_fhegg-equality-worker"))
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn standalone equality role");
        let input = child.stdin.take().unwrap();
        let output = child.stdout.take().unwrap();
        Self {
            child,
            input,
            output,
        }
    }

    fn pump(&mut self, frames_hex: Vec<String>) -> Response {
        let request = serde_json::to_vec(&json!({
            "type": "pump",
            "frames_hex": frames_hex,
        }))
        .unwrap();
        self.input
            .write_all(&(request.len() as u32).to_le_bytes())
            .and_then(|()| self.input.write_all(&request))
            .and_then(|()| self.input.flush())
            .expect("send bounded worker pump");
        let mut length = [0u8; 4];
        self.output
            .read_exact(&mut length)
            .expect("read worker response length");
        let length = u32::from_le_bytes(length) as usize;
        assert!(length > 0 && length <= 40 * 1024 * 1024);
        let mut response = vec![0u8; length];
        self.output
            .read_exact(&mut response)
            .expect("read complete worker response");
        serde_json::from_slice(&response).expect("decode worker response")
    }

    fn shutdown(mut self) {
        let request = serde_json::to_vec(&json!({ "type": "shutdown" })).unwrap();
        self.input
            .write_all(&(request.len() as u32).to_le_bytes())
            .and_then(|()| self.input.write_all(&request))
            .and_then(|()| self.input.flush())
            .unwrap();
        let status = self.child.wait().expect("wait for equality role");
        if !status.success() {
            let mut stderr = String::new();
            self.child
                .stderr
                .take()
                .unwrap()
                .read_to_string(&mut stderr)
                .unwrap();
            panic!("equality role failed during shutdown: {stderr}");
        }
    }
}

impl Drop for WorkerProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[test]
fn authenticated_equality_runs_both_polarities_across_four_standalone_processes() {
    run_process_case(0x81, 56, true);
    run_process_case(0x82, 57, false);
}

fn run_process_case(nonce_byte: u8, final_right_share: u64, expected_equal: bool) {
    let temp = TestDir::new();
    let worker = env!("CARGO_BIN_EXE_fhegg-equality-worker");
    let nonce = [nonce_byte; 32];
    let party_seeds = [[0x91; 32], [0x92; 32], [0x93; 32]];
    let coordinator_seed = [0xa1; 32];
    let party_public = party_seeds
        .iter()
        .map(|seed| encode_hex(&SigningKey::from_bytes(seed).verifying_key().to_bytes()))
        .collect::<Vec<_>>();
    let coordinator_public = encode_hex(
        &SigningKey::from_bytes(&coordinator_seed)
            .verifying_key()
            .to_bytes(),
    );
    let config = serde_json::to_vec(&json!({
        "version": 1,
        "nonce_hex": encode_hex(&nonce),
        "value_bits": VALUE_BITS,
        "plaintext_modulus": MODULUS,
        "timeout_ms": 10_000,
        "party_public_keys_hex": party_public,
        "coordinator_public_key_hex": coordinator_public,
    }))
    .unwrap();
    let config_path = temp.path.join("session.json");
    fs::write(&config_path, &config).unwrap();

    // Trusted preprocessing is its own process invocation. It receives only
    // public circuit shape and a dealer seed, never either secret operand.
    let dealer_seed_path = temp.path.join("dealer.seed");
    write_secret(&dealer_seed_path, &[0xb1; 32]);
    let status = Command::new(worker)
        .args([
            "preprocess",
            config_path.to_str().unwrap(),
            dealer_seed_path.to_str().unwrap(),
            temp.path.to_str().unwrap(),
        ])
        .status()
        .expect("launch trusted preprocessing role");
    assert!(status.success());

    // The second invocation changes only the final right additive share, so
    // the public result exercises both reveal polarities without disclosing
    // either reconstructed operand at the coordinator process.
    let left: [u64; N] = [20, 30, 27];
    let right: [u64; N] = [10, 11, final_right_share];
    let mut processes = Vec::new();
    for party in 0..N {
        let signing_seed_path = temp.path.join(format!("party-{party}.signing"));
        let ingress_seed_path = temp.path.join(format!("party-{party}.ingress"));
        let operands_path = temp.path.join(format!("party-{party}.operands"));
        let custody_path = temp.path.join(format!("party-{party}.custody"));
        write_secret(&signing_seed_path, &party_seeds[party]);
        write_secret(&ingress_seed_path, &[0xc1 + party as u8; 32]);
        let mut operands = Vec::with_capacity(16);
        operands.extend_from_slice(&left[party].to_be_bytes());
        operands.extend_from_slice(&right[party].to_be_bytes());
        write_secret(&operands_path, &operands);
        let party_string = party.to_string();
        let provisioned = Command::new(worker)
            .args([
                "provision-party",
                config_path.to_str().unwrap(),
                party_string.as_str(),
                signing_seed_path.to_str().unwrap(),
                ingress_seed_path.to_str().unwrap(),
                operands_path.to_str().unwrap(),
                custody_path.to_str().unwrap(),
            ])
            .status()
            .expect("provision protected party custody");
        assert!(provisioned.success());
        if party == 0 {
            let refusal = Command::new(worker)
                .args([
                    "party",
                    config_path.to_str().unwrap(),
                    "0",
                    custody_path.to_str().unwrap(),
                    temp.path.join("party-1.triples").to_str().unwrap(),
                ])
                .output()
                .expect("launch substituted preprocessing refusal");
            assert!(!refusal.status.success());
            assert!(String::from_utf8_lossy(&refusal.stderr)
                .contains("preprocessing custody names a different party slot"));
        }
        processes.push(WorkerProcess::spawn(&[
            "party".to_string(),
            config_path.display().to_string(),
            party.to_string(),
            custody_path.display().to_string(),
            temp.path
                .join(format!("party-{party}.triples"))
                .display()
                .to_string(),
        ]));
    }
    let coordinator_custody_path = temp.path.join("coordinator.custody");
    let coordinator_seed_path = temp.path.join("coordinator.signing");
    write_secret(&coordinator_seed_path, &coordinator_seed);
    let provisioned = Command::new(worker)
        .args([
            "provision-coordinator",
            config_path.to_str().unwrap(),
            coordinator_seed_path.to_str().unwrap(),
            coordinator_custody_path.to_str().unwrap(),
        ])
        .status()
        .expect("provision protected coordinator custody");
    assert!(provisioned.success());
    processes.push(WorkerProcess::spawn(&[
        "coordinator".to_string(),
        config_path.display().to_string(),
        coordinator_custody_path.display().to_string(),
    ]));

    let mut pending = vec![Vec::<String>::new(); N + 1];
    let mut party_done = [false; N];
    let mut public_result = None;
    let deadline = Instant::now() + Duration::from_secs(20);
    while public_result.is_none() || party_done.iter().any(|done| !done) {
        for role in 0..processes.len() {
            let response = processes[role].pump(std::mem::take(&mut pending[role]));
            for frame in response.frames {
                assert!(frame.sender <= N);
                assert!(frame.recipient <= N);
                // The supervisor routes opaque bytes using only public header
                // metadata. In deployment, party-to-party legs need a
                // confidential channel because their payload is a Boolean share.
                assert!(frame.sequence < u64::MAX);
                pending[frame.recipient].push(frame.wire_hex);
            }
            if let Some(completion) = response.completion {
                match completion {
                    Completion::Party {
                        party,
                        and_gates,
                        peer_input_messages_sent,
                        peer_input_messages_received,
                    } => {
                        assert_eq!(role, party);
                        assert!(and_gates > 0);
                        assert_eq!(peer_input_messages_sent, 2 * N);
                        assert_eq!(peer_input_messages_received, 2 * N);
                        party_done[party] = true;
                    }
                    Completion::Coordinator {
                        equal,
                        session_nonce_hex,
                        transcript_hex,
                    } => {
                        assert_eq!(role, N);
                        public_result = Some((equal, session_nonce_hex, transcript_hex));
                    }
                }
            }
        }
        assert!(
            Instant::now() < deadline,
            "standalone equality run timed out"
        );
        thread::sleep(Duration::from_millis(1));
    }

    assert!(pending.iter().all(Vec::is_empty));
    let (equal, session_nonce_hex, transcript_hex) = public_result.unwrap();
    assert_eq!(equal, expected_equal);
    assert_eq!(session_nonce_hex, encode_hex(&nonce));
    let transcript = DecisionTranscript::from_wire_bytes(&decode_hex(&transcript_hex)).unwrap();
    let session =
        PartyMpcSession::equality(nonce, N, VALUE_BITS, MODULUS, Duration::from_secs(10)).unwrap();
    assert!(transcript.is_reveal_only(&session));
    assert_eq!(transcript.revealed_equal, u8::from(expected_equal));

    for process in processes {
        process.shutdown();
    }
}

fn write_secret(path: &Path, bytes: &[u8]) {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o600);
    let mut file = options.open(path).unwrap();
    file.write_all(bytes).unwrap();
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hex(value: &str) -> Vec<u8> {
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new() -> Self {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "fhegg-equality-processes-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self { path }
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
