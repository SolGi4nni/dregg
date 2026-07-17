//! # deploy-gate — the deployer-gate CLI (the factory's gate wire)
//!
//! The pipeline arm that turns `tools/token-factory` + `tools/dregg-audit` +
//! this crate from three disconnected PoCs into ONE flow:
//!
//! ```text
//! spec ──emit──▶ token.sol ──audit──▶ report ──register-audit──▶ audit_registry
//!                                        │
//!                    VERIFIED-SAFE only  ▼
//!            issue (Audit arm, macaroon) ──▶ capability token
//!                                        │
//!                     authorize (deploy-time re-check) ──▶ AUTHORIZED / refused
//! ```
//!
//! ## Honest scope
//!
//! This is the OPERATOR-SIDE gate, file-backed: the state file holds the issuing
//! root key and the audit registry (hashes of reports that CLEARED the pipeline).
//! It is a PoC operator daemon's state, NOT a chain: the on-chain enforcement of
//! the same gate is the landed `DreggLaunchpad.registerLaunch` hook
//! (`chain/contracts/launchpad/DreggLaunchpad.sol`, `DeployerNotGated`). Nothing
//! here deploys anything — issuing/authorizing a capability is off-chain; the
//! actual `forge create`/`registerLaunch` remains a separate, deliberate act.
//!
//! The capability is a REAL `dregg-macaroon` (HMAC-chained, attenuation-only):
//! `issue` refuses (`NotGated`) unless the report hash is in the registry, and
//! `authorize` replays the full chain + re-checks every caveat (scope, expiry,
//! arm) against the live state — a report hash withdrawn after issuance fails
//! closed at authorize time.

use std::io::Read;
use std::process::ExitCode;

use dregg_deployer_gate::{
    launch_params_hash, DeployRequest, DeployerGate, DeployerId, GateArm, GateContext,
};
use dregg_macaroon::Macaroon;
use sha2::{Digest, Sha256};

const LOCATION: &str = "dregg-deployer-gate/cli/v1";

fn hex_encode(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn hex_decode32(s: &str) -> Result<[u8; 32], String> {
    let s = s.trim();
    if s.len() != 64 || !s.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(format!("expected 64 hex chars, got {:?}", s));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        out[i] = u8::from_str_radix(std::str::from_utf8(chunk).unwrap(), 16).unwrap();
    }
    Ok(out)
}

fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize().into()
}

fn deployer_id(handle: &str) -> DeployerId {
    // A stable per-deployer identifier — an opaque hash of the handle, not KYC.
    let mut h = Sha256::new();
    h.update(b"dregg-deployer-gate/deployer-id/v1");
    h.update(handle.as_bytes());
    h.finalize().into()
}

/// The operator state file: line-based, human-auditable.
///   root-key <64 hex>
///   audit <64 hex>      (one line per report hash that CLEARED the audit)
struct State {
    root_key: [u8; 32],
    audit_hashes: Vec<[u8; 32]>,
}

impl State {
    fn load(path: &str) -> Result<State, String> {
        let text = std::fs::read_to_string(path)
            .map_err(|e| format!("cannot read state file {path}: {e}"))?;
        let mut root_key = None;
        let mut audit_hashes = Vec::new();
        for (n, line) in text.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let (k, v) = line
                .split_once(' ')
                .ok_or_else(|| format!("{path}:{}: malformed line", n + 1))?;
            match k {
                "root-key" => {
                    root_key = Some(hex_decode32(v).map_err(|e| format!("{path}:{}: {e}", n + 1))?)
                }
                "audit" => audit_hashes
                    .push(hex_decode32(v).map_err(|e| format!("{path}:{}: {e}", n + 1))?),
                other => return Err(format!("{path}:{}: unknown key {other:?}", n + 1)),
            }
        }
        Ok(State {
            root_key: root_key
                .ok_or_else(|| format!("{path}: missing root-key (run `deploy-gate init`)"))?,
            audit_hashes,
        })
    }

    fn save(&self, path: &str) -> Result<(), String> {
        let mut out = String::from(
            "# dregg deploy-gate operator state (PoC, file-backed — see src/bin/deploy-gate.rs)\n",
        );
        out.push_str(&format!("root-key {}\n", hex_encode(&self.root_key)));
        for h in &self.audit_hashes {
            out.push_str(&format!("audit {}\n", hex_encode(h)));
        }
        std::fs::write(path, out).map_err(|e| format!("cannot write state file {path}: {e}"))
    }

    fn context(&self) -> GateContext {
        let mut ctx = GateContext::default();
        for h in &self.audit_hashes {
            ctx.audit_registry.insert(*h);
        }
        ctx
    }
}

fn now_unix() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock before epoch")
        .as_secs() as i64
}

fn random_key() -> Result<[u8; 32], String> {
    let mut f =
        std::fs::File::open("/dev/urandom").map_err(|e| format!("open /dev/urandom: {e}"))?;
    let mut k = [0u8; 32];
    f.read_exact(&mut k)
        .map_err(|e| format!("read /dev/urandom: {e}"))?;
    Ok(k)
}

fn arg_value(args: &[String], flag: &str) -> Option<String> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1).cloned())
}

fn usage() -> String {
    "usage:\n\
     deploy-gate init <state-file>\n\
     deploy-gate register-audit <state-file> <audit-report-file>\n\
     deploy-gate issue <state-file> --deployer HANDLE --launch-params FILE \\\n\
                       --report-hash HEX64 [--not-after UNIX] [--ttl SECS]\n\
     deploy-gate authorize <state-file> --deployer HANDLE --launch-params FILE \\\n\
                       --capability TOKEN [--now UNIX]\n"
        .into()
}

fn run() -> Result<(), (u8, String)> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().cloned().unwrap_or_default();
    match cmd.as_str() {
        "init" => {
            let path = args.get(1).ok_or((2, usage()))?;
            if std::path::Path::new(path).exists() {
                return Err((
                    2,
                    format!("refusing to overwrite existing state file {path}"),
                ));
            }
            let state = State {
                root_key: random_key().map_err(|e| (1, e))?,
                audit_hashes: Vec::new(),
            };
            state.save(path).map_err(|e| (1, e))?;
            println!("initialized {path}");
            Ok(())
        }
        "register-audit" => {
            let path = args.get(1).ok_or((2, usage()))?;
            let report = args.get(2).ok_or((2, usage()))?;
            let bytes =
                std::fs::read(report).map_err(|e| (1, format!("cannot read {report}: {e}")))?;
            let hash = sha256(&bytes);
            let mut state = State::load(path).map_err(|e| (1, e))?;
            if !state.audit_hashes.contains(&hash) {
                state.audit_hashes.push(hash);
                state.save(path).map_err(|e| (1, e))?;
            }
            println!("{}", hex_encode(&hash));
            Ok(())
        }
        "issue" => {
            let path = args.get(1).ok_or((2, usage()))?;
            let state = State::load(path).map_err(|e| (1, e))?;
            let deployer = arg_value(&args, "--deployer").ok_or((2, usage()))?;
            let params_file = arg_value(&args, "--launch-params").ok_or((2, usage()))?;
            let report_hash = hex_decode32(&arg_value(&args, "--report-hash").ok_or((2, usage()))?)
                .map_err(|e| (2, e))?;
            let not_after = match arg_value(&args, "--not-after") {
                Some(v) => v
                    .parse::<i64>()
                    .map_err(|e| (2, format!("--not-after: {e}")))?,
                None => {
                    let ttl = arg_value(&args, "--ttl")
                        .map(|v| v.parse::<i64>())
                        .transpose()
                        .map_err(|e| (2, format!("--ttl: {e}")))?
                        .unwrap_or(3600);
                    now_unix() + ttl
                }
            };
            let params = std::fs::read(&params_file)
                .map_err(|e| (1, format!("cannot read {params_file}: {e}")))?;
            let gate = DeployerGate::new(state.root_key, LOCATION);
            let mac = gate
                .issue(
                    deployer_id(&deployer),
                    GateArm::Audit { report_hash },
                    launch_params_hash(&params),
                    not_after,
                    &state.context(),
                )
                .map_err(|e| (3, format!("issuance refused: {e}")))?;
            let token = mac.encode().map_err(|e| (1, format!("encode: {e}")))?;
            println!("{token}");
            Ok(())
        }
        "authorize" => {
            let path = args.get(1).ok_or((2, usage()))?;
            let state = State::load(path).map_err(|e| (1, e))?;
            let deployer = arg_value(&args, "--deployer").ok_or((2, usage()))?;
            let params_file = arg_value(&args, "--launch-params").ok_or((2, usage()))?;
            let token = arg_value(&args, "--capability").ok_or((2, usage()))?;
            let now = arg_value(&args, "--now")
                .map(|v| v.parse::<i64>())
                .transpose()
                .map_err(|e| (2, format!("--now: {e}")))?
                .unwrap_or_else(now_unix);
            let params = std::fs::read(&params_file)
                .map_err(|e| (1, format!("cannot read {params_file}: {e}")))?;
            let mac = Macaroon::decode(&token).map_err(|e| (3, format!("bad capability: {e}")))?;
            let gate = DeployerGate::new(state.root_key, LOCATION);
            let req = DeployRequest::new(
                now,
                &deployer_id(&deployer),
                launch_params_hash(&params),
                &state.context(),
            );
            gate.authorize_deploy(&mac, &req)
                .map_err(|e| (3, format!("deploy refused: {e}")))?;
            println!("AUTHORIZED");
            Ok(())
        }
        _ => Err((2, usage())),
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err((code, msg)) => {
            eprintln!("deploy-gate: {msg}");
            ExitCode::from(code)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_roundtrip() {
        let h = sha256(b"report");
        assert_eq!(hex_decode32(&hex_encode(&h)).unwrap(), h);
        assert!(hex_decode32("zz").is_err());
    }

    #[test]
    fn state_roundtrip() {
        let dir = std::env::temp_dir().join(format!("deploy-gate-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("state").to_str().unwrap().to_string();
        let state = State {
            root_key: sha256(b"k"),
            audit_hashes: vec![sha256(b"a"), sha256(b"b")],
        };
        state.save(&path).unwrap();
        let loaded = State::load(&path).unwrap();
        assert_eq!(loaded.root_key, state.root_key);
        assert_eq!(loaded.audit_hashes, state.audit_hashes);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
