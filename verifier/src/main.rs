//! `dregg-verifier`: the standalone proof verifier.
//!
//! # Usage
//!
//! ```text
//! dregg-verifier rotated-replay-chain <request.json>
//! dregg-verifier verify-cross-fed-bundle --bundle <path> \
//!                                        --known-issuer <path> \
//!                                        --known-recipient <path>
//! dregg-verifier aggregated-bundle <bundle.json>
//! ```
//!
//! ## Exit codes
//! - 0 — verified
//! - 1 — rejected (cryptographically invalid, or a binding did not hold)
//! - 2 — error (bad inputs, unknown subcommand, deserialisation failure)
//!
//! # ⚑ FLAG DAY 2026-08-05 — four surfaces DELETED, not retired
//!
//! This binary used to advertise seven entry points. Five of them could not return
//! "verified" for any input, because each one bottomed out in `verify_effect_vm_proof`,
//! a stub that returned `exit_code::ERROR` unconditionally. A check that cannot pass is
//! not fail-closed caution, it is an advertisement for a check that does not exist, and
//! a reader trusts it. So:
//!
//! | deleted | why | what to use |
//! |---|---|---|
//! | the bare `--proof/--pi/--vk-hash` mode | always exit 2 | `rotated-replay-chain` |
//! | the JSON-on-stdin mode | always exit 2 | `rotated-replay-chain` |
//! | `replay-chain` | v1 hand-AIR; rejected every entry | `rotated-replay-chain` |
//! | `scope-recursive` | same, via the recursion tower | `rotated-replay-chain` |
//! | `bilateral-pair` / `bilateral-bundle` | verified NO proof: it printed `verified: true` over `WitnessedReceipt`s carrying `proof_bytes: []`, which is what this crate's own fabricator produces | nothing — the PI-agreement algebra survives as a library call (`check_bilateral_pi_agreement`), named for what it does |
//!
//! The `--vk-hash` flag's documented example value was
//! `8b80e1cf7b0a04e74e7d7bfb9c7a11e37c1d0bb1a5edae8e3b92c9e9b6d5f42a`, described as
//! `SHA-256(b"dregg-effect-vm-v1")`. That digest is actually
//! `0942b5f2a4ecb7d78aaff908fc605257cb2a31b55b722561f330a8f8ff3c87f3`. The constant was
//! invented and the derivation note was wrong; both are gone with the flag.
//!
//! The `cross-fed` and `aggregate-bilateral` aliases are also gone (zero callers; two
//! spellings that agree today are two spellings that disagree later).
//!
//! **Who this breaks:** `demo/two-ai-handoff/charlie.py` spawns `replay-chain`,
//! `bilateral-pair` and `scope-recursive`; `demo/cross-app-e2e/verify_real.py` spawns
//! `replay-chain`. All four invocations were already receiving a rejection on every
//! run. They now get usage + exit 2 and must be re-pointed at `rotated-replay-chain`.
//!
//! # Isolation guarantee
//! This binary carries no prover state, no ledger, no executor, and no program
//! registry. The only dependencies on shared context are the bytes it reads from disk.
//!
//! ⚠ It DOES still LINK a prover, and this note exists so nobody reads the sentence
//! above as saying otherwise. `dregg-turn-prover` is an unconditional dependency (the
//! `aggregated-bundle` subcommand's type + verifier live there) and it pulls
//! `dregg-circuit-prove` at depth 2 — measured 2026-08-05 with `cargo tree`. Deleting
//! this crate's own `prover` feature and direct `dregg-circuit-prove` edge removed a
//! knob, not the tower. No verify path calls into it; the linkage is real anyway.

use dregg_verifier::{
    CommitteeDescriptor, exit_code, verify_aggregated_bundle_json, verify_cross_fed_bundle,
};
use std::{env, io, process};

const USAGE: &str = "\
Usage:
  dregg-verifier rotated-replay-chain <request.json>
  dregg-verifier verify-cross-fed-bundle --bundle <path> --known-issuer <path> \
--known-recipient <path>
  dregg-verifier aggregated-bundle <bundle.json>

Exit codes: 0 = verified, 1 = rejected, 2 = error.";

fn main() {
    let args: Vec<String> = env::args().collect();

    match args.get(1).map(String::as_str) {
        Some("rotated-replay-chain") => run_rotated_replay_chain(&args[2..]),
        Some("verify-cross-fed-bundle") => run_verify_cross_fed_bundle(&args[2..]),
        Some("aggregated-bundle") => run_aggregated_bundle(&args[2..]),
        Some(other) => {
            eprintln!("unknown subcommand: {other}");
            eprintln!("{USAGE}");
            process::exit(exit_code::ERROR);
        }
        None => {
            eprintln!("{USAGE}");
            process::exit(exit_code::ERROR);
        }
    }
}

// ---------------------------------------------------------------------------
// rotated-replay-chain subcommand (the verify floor: no verify path here calls a prover)
// ---------------------------------------------------------------------------

/// On-disk request for the rotated replay-chain verify: the chained
/// `"effect-vm-rotated"` legs plus the caller's trusted pre/post commitments.
#[derive(serde::Deserialize)]
struct RotatedReplayRequest {
    /// The rotated legs in chain order (`s0 → s1 → … → sN`).
    legs: Vec<dregg_verifier::RotatedReplayLeg>,
    /// The turn's pre-state commitment as the 8-felt (~124-bit) anchor: eight canonical
    /// BabyBear `u32` lanes. The first leg's before-anchor must match.
    expected_old_commit: [u32; 8],
    /// The turn's post-state commitment as the 8-felt anchor. The last leg's
    /// after-anchor must match.
    expected_new_commit: [u32; 8],
}

/// `dregg-verifier rotated-replay-chain <path-to-request.json>`
///
/// Reads `{ "legs": [..], "expected_old_commit": [u32; 8], "expected_new_commit": [u32; 8] }`
/// and runs the ROTATED replay-chain verify. Each leg is an `"effect-vm-rotated"` IR-v2
/// batch proof verified SELECTOR-BOUND via the audited `verify_vm_descriptor2` against
/// the committed WIDE / welded-wide / bare-V3 registries; the chain's endpoints and
/// interior adjacency are then checked against the caller's commitments at each leg's
/// TRUE width, and each leg is bound to the `TurnReceipt` it attests.
///
/// ⚑ FLAG DAY (2026-07-27): each leg object REQUIRES a `"receipt"` field (a serialized
/// `dregg_turn::TurnReceipt`). A request written before that date has no `receipt` on
/// its legs and REFUSES TO LOAD — deliberately, and with a parse error rather than a
/// silent verify: the field's absence used to mean "this chain's proofs are bound to no
/// receipt at all".
///
/// ⚑ FLAG DAY (2026-08-05): `expected_old_commit` / `expected_new_commit` are now
/// 8-element arrays, not single integers. Reading a WIDE leg's ~124-bit anchor at its
/// ~31-bit slot-0 position is the defect the SDK's `vk_hash_is_wide` exists to prevent,
/// and this floor now accepts WIDE legs, so it must speak the wide anchor. A request in
/// the old single-integer shape REFUSES TO LOAD. Nothing persists these requests;
/// re-emit them from the producer. A genuinely narrow (1-felt) expectation is written
/// `[felt, 0, 0, 0, 0, 0, 0, 0]`, which is exactly how a narrow leg publishes it.
///
/// Exit code: 0 = chain verified, 1 = at least one rejection, 2 = read/parse error.
fn run_rotated_replay_chain(args: &[String]) -> ! {
    use dregg_circuit::field::BabyBear;
    use dregg_verifier::verify_rotated_replay_chain;

    let Some(path) = args.first() else {
        eprintln!("Usage: dregg-verifier rotated-replay-chain <path-to-request.json>");
        process::exit(exit_code::ERROR);
    };

    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            process::exit(exit_code::ERROR);
        }
    };

    let req: RotatedReplayRequest = match serde_json::from_str(&text) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cannot parse rotated-replay-chain request JSON: {}", e);
            eprintln!(
                "note: `expected_old_commit` / `expected_new_commit` are 8-element arrays of \
                 canonical u32 BabyBear lanes as of 2026-08-05; a single integer no longer parses."
            );
            process::exit(exit_code::ERROR);
        }
    };

    let lift = |lanes: [u32; 8]| lanes.map(BabyBear::new_canonical);
    let output = verify_rotated_replay_chain(
        &req.legs,
        lift(req.expected_old_commit),
        lift(req.expected_new_commit),
    );
    let json = serde_json::to_string_pretty(&output).unwrap_or_else(|_| {
        r#"{"overall_verified":false,"summary":"serialisation error"}"#.to_string()
    });
    println!("{}", json);

    let code = if output.overall_verified {
        exit_code::VERIFIED
    } else {
        exit_code::REJECTED
    };
    process::exit(code);
}

// ---------------------------------------------------------------------------
// verify-cross-fed-bundle subcommand
// ---------------------------------------------------------------------------

/// `dregg-verifier verify-cross-fed-bundle --bundle <path> --known-issuer <path> --known-recipient <path>`
///
/// Reads a JSON-encoded `dregg_federation::CrossFedReceiptBundle` and two committee
/// descriptors (issuing + receiving federation), runs the cross-federation
/// verification from `SILVER-VISION-E2E-VERIFICATION.md` §1 Step 6, and prints a
/// `CrossFedVerdict` JSON to stdout. Exit code matches the verdict (0 =
/// overall_verified, 1 = at least one check failed, 2 = parse / IO error).
fn run_verify_cross_fed_bundle(args: &[String]) -> ! {
    let mut bundle_path: Option<String> = None;
    let mut issuer_path: Option<String> = None;
    let mut recipient_path: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--bundle" => {
                i += 1;
                bundle_path = args.get(i).cloned();
            }
            "--known-issuer" | "--known-F1" => {
                i += 1;
                issuer_path = args.get(i).cloned();
            }
            "--known-recipient" | "--known-F2" => {
                i += 1;
                recipient_path = args.get(i).cloned();
            }
            other => {
                eprintln!("unknown flag: {other}");
                eprintln!(
                    "Usage: dregg-verifier verify-cross-fed-bundle --bundle <path> \
                     --known-issuer <path> --known-recipient <path>"
                );
                process::exit(exit_code::ERROR);
            }
        }
        i += 1;
    }
    let Some(bundle_path) = bundle_path else {
        eprintln!("--bundle is required");
        process::exit(exit_code::ERROR);
    };
    let Some(issuer_path) = issuer_path else {
        eprintln!("--known-issuer is required");
        process::exit(exit_code::ERROR);
    };
    let Some(recipient_path) = recipient_path else {
        eprintln!("--known-recipient is required");
        process::exit(exit_code::ERROR);
    };

    let bundle_text = match std::fs::read_to_string(&bundle_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read bundle file {bundle_path}: {e}");
            process::exit(exit_code::ERROR);
        }
    };
    let bundle: dregg_federation::CrossFedReceiptBundle = match serde_json::from_str(&bundle_text) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("cannot parse bundle JSON ({bundle_path}): {e}");
            process::exit(exit_code::ERROR);
        }
    };
    let issuer: CommitteeDescriptor = match std::fs::read_to_string(&issuer_path).and_then(|t| {
        serde_json::from_str(&t).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("cannot read issuer descriptor {issuer_path}: {e}");
            process::exit(exit_code::ERROR);
        }
    };
    let recipient: CommitteeDescriptor =
        match std::fs::read_to_string(&recipient_path).and_then(|t| {
            serde_json::from_str(&t).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
        }) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("cannot read recipient descriptor {recipient_path}: {e}");
                process::exit(exit_code::ERROR);
            }
        };

    let verdict = verify_cross_fed_bundle(&bundle, &issuer, &recipient);
    let json = serde_json::to_string_pretty(&verdict).unwrap_or_else(|_| {
        r#"{"overall_verified":false,"summary":"serialisation error"}"#.to_string()
    });
    println!("{}", json);
    let code = if verdict.overall_verified {
        exit_code::VERIFIED
    } else {
        exit_code::REJECTED
    };
    process::exit(code);
}

// ---------------------------------------------------------------------------
// aggregated-bundle subcommand (Stage 7-γ.2 Phase 2)
// ---------------------------------------------------------------------------

/// `dregg-verifier aggregated-bundle <bundle.json>`
///
/// Reads a JSON-encoded `dregg_turn_prover::AggregatedBundle` and runs the Phase-2
/// joint aggregation verifier (`STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`), whose step 4 is a
/// real `verify_vm_descriptor2` batch verify of the bundle's outer proof against the
/// Lean-emitted descriptor.
/// Exit code: 0 = verified, 1 = rejected, 2 = read / parse error.
fn run_aggregated_bundle(args: &[String]) -> ! {
    let Some(path) = args.first() else {
        eprintln!("Usage: dregg-verifier aggregated-bundle <bundle.json>");
        process::exit(exit_code::ERROR);
    };

    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            process::exit(exit_code::ERROR);
        }
    };

    let verdict = verify_aggregated_bundle_json(&text);
    let json = serde_json::to_string_pretty(&verdict)
        .unwrap_or_else(|_| r#"{"verified":false,"reason":"serialisation error"}"#.to_string());
    println!("{}", json);
    let code = if verdict.verified {
        exit_code::VERIFIED
    } else {
        exit_code::REJECTED
    };
    process::exit(code);
}
