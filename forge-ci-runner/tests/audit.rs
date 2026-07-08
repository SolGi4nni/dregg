//! THE TWO POLES — the confined runner produces a work-bound signed verdict that
//! (i) re-verifies HONEST and satisfies the L1 forge `CiRun` gate; (ii) a LYING
//! host's fabricated verdict is CONVICTED by re-execution.
//!
//! macOS-only: these drive the real Seatbelt jail. Run:
//!   cd forge-ci-runner && cargo test

#![cfg(target_os = "macos")]

use std::path::{Path, PathBuf};

use dregg_doc::check::CiRunWitness;
use dregg_doc::{planned_ci_run_hash, CheckRefusal, CheckWitness, CiVerdict, RequiredCheck};
use forge_ci_runner::{
    confinement_id, input_root_of_dir, reexecute_and_verify, run_check_confined, AuditVerdict,
};

// RFC 8032 §7.1 TEST 1 Ed25519 (seed, verifying-key) pair — the SAME real pair
// the dregg-doc CI-gate tests use; the executor derives KEY from SEED by standard
// key generation, so a verdict signed with SEED verifies against KEY.
const SEED: [u8; 32] = [
    0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c, 0xc4,
    0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae, 0x7f, 0x60,
];
const KEY: [u8; 32] = [
    0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07, 0x3a,
    0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07, 0x51, 0x1a,
];

// The CI-run region cell's identity (repo policy — the verifier rebuilds the
// identical genesis cell) and the required check's command id.
const CI_EDITOR: u8 = 7;
const CI_REGION: u8 = 8;
const COMMAND: [u8; 32] = [0x11; 32];

const CAT: &str = "/bin/cat";

// ─────────────────────── POLE (i): HONEST re-verifies + satisfies the gate ─────

#[test]
fn honest_run_reverifies_and_satisfies_the_forge_gate() {
    // A deterministic check: `/bin/cat {WORK}/input.txt` prints the seeded file's
    // exact bytes — stable across runs, so its output digest is reproducible.
    let input = seed_dir("fcr-honest", "the exact bytes CI ran against\n");
    let argv = vec!["{WORK}/input.txt".to_string()];

    // L2 — the confined runner produces a signed, work-bound verdict.
    let out = run_check_confined(
        &input,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("confined run + verdict commit");

    assert_eq!(
        out.verdict.exit_code, 0,
        "the deterministic check command succeeded confined"
    );
    assert!(
        out.receipt.executor_signature.is_some(),
        "the CI host signed the verdict receipt"
    );
    // input_root is the REAL substrate_commit of the working tree.
    assert_eq!(
        out.verdict.input_root,
        input_root_of_dir(&input).unwrap(),
        "the verdict binds the tree's real substrate commitment"
    );

    // THE L1 IN-TURN BINDING: the signed receipt's turn hash equals the
    // fresh-genesis re-derivation over the verdict (what the forge check runs).
    assert_eq!(
        planned_ci_run_hash(CI_EDITOR, CI_REGION, &out.verdict),
        Some(out.receipt.turn_hash),
        "the verdict is bound INSIDE the signed genesis turn"
    );

    // L3 — re-execution reproduces the verdict exactly → Honest.
    let audit = reexecute_and_verify(&out.verdict, &input, Path::new(CAT), &argv)
        .expect("re-execution audit runs");
    assert_eq!(audit, AuditVerdict::Honest, "an honest host re-verifies");

    // THE FORGE GATE (`RequiredCheck::ci_run.satisfied_by` — exactly what
    // `PullRequest::land` calls): bound to a PR whose input_root matches, the
    // work-bound, signed, exit-0 verdict SATISFIES.
    let check = RequiredCheck::ci_run("build", COMMAND, CI_EDITOR, CI_REGION, vec![KEY]);
    let witness = CheckWitness::CiRun(CiRunWitness::signed(
        out.receipt.clone(),
        out.verdict.clone(),
    ));
    check
        .satisfied_by(&witness, out.verdict.input_root)
        .expect("the L1 forge CiRun check accepts the work-bound signed verdict");

    // And it is genuinely BOUND to this PR's code: a mismatched input_root refuses.
    let mut other_root = out.verdict.input_root;
    other_root[0] ^= 0xff;
    match check.satisfied_by(&witness, other_root) {
        Err(CheckRefusal::InputRootMismatch { .. }) => {}
        other => panic!("expected InputRootMismatch for a different PR's code, got {other:?}"),
    }

    let _ = std::fs::remove_dir_all(&input);
}

// ─────────────────────── POLE (ii): a LYING host is CONVICTED ──────────────────

#[test]
fn lying_host_is_caught_by_reexecution() {
    let input = seed_dir("fcr-liar", "honest input bytes\n");
    let argv = vec!["{WORK}/input.txt".to_string()];

    // Honest baseline: what the command REALLY produces confined.
    let honest = run_check_confined(
        &input,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("honest confined run");
    assert_eq!(honest.verdict.exit_code, 0);

    // THE LIE: a well-formed verdict with the SAME (real) input_root, command,
    // confinement, and a passing exit code — but a FABRICATED output_digest. The
    // host could sign this (it is the executor); re-execution convicts it.
    let bogus_digest = [0xAB; 32];
    assert_ne!(
        bogus_digest, honest.verdict.output_digest,
        "the lie must differ from the truth"
    );
    let lie = CiVerdict {
        output_digest: bogus_digest,
        ..honest.verdict.clone()
    };

    let audit =
        reexecute_and_verify(&lie, &input, Path::new(CAT), &argv).expect("re-execution audit runs");
    match audit {
        AuditVerdict::HostLied {
            field,
            claimed,
            recomputed,
        } => {
            assert_eq!(field, "output_digest", "the divergent field is named");
            assert_eq!(claimed, hex(&bogus_digest));
            assert_eq!(recomputed, hex(&honest.verdict.output_digest));
        }
        AuditVerdict::Honest => panic!("a fabricated output_digest must be CONVICTED"),
    }

    let _ = std::fs::remove_dir_all(&input);
}

#[test]
fn lying_about_exit_code_is_caught() {
    // A command that really FAILS: cat a file that does NOT exist in the work
    // dir → nonzero exit. (Its stderr text embeds the ephemeral path, so its
    // OUTPUT is not reproducible — but the audit checks exit_code before
    // output_digest, and confinement_id is path-agnostic, so the exit-code lie
    // is caught cleanly.)
    let input = seed_dir("fcr-exitlie", "present\n");
    let argv = vec!["{WORK}/does-not-exist.txt".to_string()];

    let honest = run_check_confined(
        &input,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("confined run of a failing command");
    assert_ne!(
        honest.verdict.exit_code, 0,
        "cat of a missing file fails confined"
    );

    // THE LIE: claim success (exit 0) over a run that really failed, keeping the
    // real confinement id so the audit reaches the exit-code comparison.
    let lie = CiVerdict {
        exit_code: 0,
        ..honest.verdict.clone()
    };
    let audit =
        reexecute_and_verify(&lie, &input, Path::new(CAT), &argv).expect("re-execution audit runs");
    match audit {
        AuditVerdict::HostLied { field, claimed, .. } => {
            assert_eq!(field, "exit_code");
            assert_eq!(claimed, "0");
        }
        AuditVerdict::Honest => panic!("claiming success over a failing run must be CONVICTED"),
    }

    let _ = std::fs::remove_dir_all(&input);
}

#[test]
fn confinement_id_binds_the_command() {
    // A verdict whose confinement_id does not match the command being audited is
    // convicted on that field first (the audit binds WHICH sandbox/command ran).
    let input = seed_dir("fcr-cid", "x\n");
    let argv = vec!["{WORK}/input.txt".to_string()];
    let honest = run_check_confined(
        &input,
        Path::new(CAT),
        &argv,
        COMMAND,
        SEED,
        CI_EDITOR,
        CI_REGION,
    )
    .expect("honest run");

    // Claim it ran under a DIFFERENT command's confinement.
    let wrong_cid = confinement_id("/bin/echo", &argv, &brew());
    let lie = CiVerdict {
        confinement_id: wrong_cid,
        ..honest.verdict.clone()
    };
    match reexecute_and_verify(&lie, &input, Path::new(CAT), &argv).unwrap() {
        AuditVerdict::HostLied { field, .. } => assert_eq!(field, "confinement_id"),
        AuditVerdict::Honest => panic!("a mismatched confinement id must be caught"),
    }
    let _ = std::fs::remove_dir_all(&input);
}

// ─────────────────────────────── helpers ──────────────────────────────────────

fn seed_dir(tag: &str, contents: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let p = std::env::temp_dir().join(format!(
        "{tag}-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p).unwrap();
    std::fs::write(p.join("input.txt"), contents).unwrap();
    p
}

fn brew() -> String {
    std::env::var("HOMEBREW_PREFIX").unwrap_or_else(|_| "/opt/homebrew".to_string())
}

fn hex(b: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for &x in b {
        s.push(HEX[(x >> 4) as usize] as char);
        s.push(HEX[(x & 0x0f) as usize] as char);
    }
    s
}
