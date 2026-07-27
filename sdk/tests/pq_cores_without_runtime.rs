//! **An SDK consumer that never builds an `AgentRuntime` must be able to VERIFY.**
//!
//! # The hole this pins shut
//!
//! `dregg-pq` answers an ML-DSA verify only through a function pointer some host installed, and
//! with none installed it refuses — `process::abort()`, uncatchable by design. The SDK installed
//! the verified cores ASYMMETRICALLY: keygen and sign at the point of use
//! (`AgentCipherclerk::ml_dsa_key`), but VERIFY only from an `AgentRuntime` constructor. So whether
//! an SDK-hosted process could verify a signature was a fact about whether something had
//! constructed a runtime first — an ORDERING, not a property of the verifying code — and two
//! ordinary, advertised consumer shapes have no runtime at all:
//!
//!   * `dregg_sdk::embed::DreggEngine`, the documented no-I/O service-integration engine. It owns a
//!     `TurnExecutor`; every turn an SDK cipherclerk signs is a `HybridSignature` by default; the
//!     executor's admission fail-closes a present PQ half through `dregg_turn::pq::ml_dsa_verify`.
//!     First turn, abort.
//!   * `dregg_sdk::verify_finalized_history`, the light-client entry, whose entire premise is a
//!     verifier holding a trust anchor and nothing else. Each committee vote carries an ML-DSA
//!     half. First vote, abort.
//!
//! This is the same un-called-initializer class that killed `dregg-node genesis`/`mcp`/`relay`
//! (`1fc796e8d`) and `dregg-preflight`'s `main()` (`046c6aa67`), one layer up.
//!
//! # Why these are SUBPROCESS arms
//!
//! The refusal is `process::abort()`, so it cannot be observed from inside the process it kills —
//! and it takes the whole test binary, not one test. Each arm therefore re-executes this binary
//! with a role marker, and the parent asserts on how the child died (or lived). It is also the only
//! way to isolate WHICH construction armed the cores: a `Once` is process-global, so two arms in
//! one process would contaminate each other.
//!
//! ⚑ The banner is TEXTLESS under libtest's output capture — `process::abort()` never flushes, and
//! `dregg-pq` writes to raw fd 2 precisely so a subprocess like this one can still read it. The
//! children run with `--nocapture` for the same reason.
//!
//! # This binary deliberately does NOT call `dregg_pq_testkit::install_at_process_start!()`
//!
//! A process-start initializer here would arm the cores in every child before any arm ran, and the
//! whole file would pass no matter what the SDK did. That is exactly how the production hole stayed
//! invisible: the test-only mechanism is the right tool for a binary whose SUBJECT is something
//! else, and the wrong tool for one whose subject is the production install itself.

use std::process::Command;

/// Marker telling a re-executed child which arm to run.
const ROLE: &str = "DREGG_SDK_PQ_ARM";

/// A well-formed-length ML-DSA-65 `(pk, sig)` that is cryptographically garbage.
///
/// The LENGTHS are what matter: `ml_dsa_verify`'s malformed-input check short-circuits with `false`
/// AHEAD of the audit gate (deliberately — a truncated signature has no verdict on any backend, and
/// a gate ahead of it would hand any peer a remote kill). So a wrong-length probe would survive
/// every arm below and prove nothing. With correct lengths, the gate is the only thing that can
/// decide the call, and an unarmed process aborts.
fn well_formed_but_bogus() -> (Vec<u8>, Vec<u8>) {
    (
        vec![0u8; dregg_turn::pq::ML_DSA_PK_LEN],
        vec![0u8; dregg_turn::pq::ML_DSA_SIG_LEN],
    )
}

/// How many ML-DSA verifies the LEAN-VERIFIED core has answered in this process.
///
/// `dregg_pq::pq_provenance()` is the per-direction ledger of "which implementation answered a
/// given operation". Reading it is how an arm proves it REACHED the gate rather than merely
/// surviving — a distinction that matters, because "the process did not abort" is also true of a
/// process that never performed the operation at all.
fn verified_ml_dsa_verifies() -> u64 {
    dregg_pq::pq_provenance()
        .iter()
        .find(|(site, ..)| *site == dregg_pq::PqSite::MlDsaVerify)
        .map(|&(_, verified, ..)| verified)
        .expect("MlDsaVerify is one of the six sites")
}

/// The verify the deployed executor performs at `turn/src/executor/authorize.rs` for a
/// `HybridSignature` — the same entry, so an arm that survives this survives an admission.
fn drive_one_verify() -> bool {
    let (pk, sig) = well_formed_but_bogus();
    dregg_turn::pq::ml_dsa_verify(&pk, b"a message no key signed", &sig)
}

fn child_body(role: &str) -> ! {
    match role {
        // ── THE FIX, ARM 1: the embed engine ────────────────────────────────────────────────
        // `DreggEngine::new` is the whole SDK object this child constructs. No `AgentRuntime`, no
        // cipherclerk — so if it does not arm the verify core, nothing does.
        "engine_then_verify" => {
            let _engine =
                dregg_sdk::embed::DreggEngine::new(dregg_sdk::embed::EngineConfig::for_testing());
            let accepted = drive_one_verify();
            println!("ARM SURVIVED: verify -> {accepted}");
            assert!(!accepted, "a bogus signature must not verify");
        }

        // ── THE FIX, ARM 2: the identity, point of use ──────────────────────────────────────
        // `ml_dsa_public_bytes()` forces `AgentCipherclerk::ml_dsa_key`, the point-of-use install
        // that used to arm KEYGEN and SIGN only. The verify below is the half it did not cover:
        // this arm is the exact production defect, driven.
        "cipherclerk_then_verify" => {
            let clerk = dregg_sdk::AgentCipherclerk::new();
            let pq_pk = clerk.ml_dsa_public_bytes();
            assert_eq!(pq_pk.len(), dregg_turn::pq::ML_DSA_PK_LEN);
            let accepted = drive_one_verify();
            println!("ARM SURVIVED: verify -> {accepted}");
            assert!(!accepted, "a bogus signature must not verify");
        }

        // ── THE FIX, ARM 3: sign THEN verify, end to end, no runtime ────────────────────────
        // The shape `sdk/tests/hybrid_pq_turn.rs` has: a cipherclerk signs, and the same process
        // verifies what it signed. A GENUINE signature, so a broken-archive `VerifiedCoreFaulted`
        // (which rejects rather than aborts) cannot masquerade as success here.
        "sign_then_verify" => {
            let clerk = dregg_sdk::AgentCipherclerk::new();
            let target = clerk.cell_id("default");
            let turn = clerk.make_turn(empty_action(target, 1));
            let signed = clerk.sign_turn(&turn);
            let h = signed.turn.hash();
            let accepted =
                dregg_turn::pq::ml_dsa_verify(&signed.pq_signer, &h, &signed.pq_signature);
            println!("ARM SURVIVED: genuine verify -> {accepted}");
            assert!(
                accepted,
                "the process signed this itself; the verified core must accept it (a false here \
                 means an installed core FAULTED — a broken archive)"
            );
        }

        // ── THE FIX, ARM 4: the executor really admits a hybrid turn ────────────────────────
        // Not a bare primitive call: `DreggEngine::execute_turn` drives
        // `TurnExecutor::execute` → `verify_authorization` → the `HybridSignature` branch →
        // `crate::pq::ml_dsa_verify`. That is the exact call an SDK-hosted service makes on every
        // turn it admits, and the one that took the process down.
        //
        // ⚑ THE LEDGER IS LOAD-BEARING, NOT SETUP. `verify_authorization` reads the live TARGET
        // CELL to decide which key the PQ half is checked against, so on an EMPTY ledger the turn
        // is refused before the hybrid branch and this arm proves NOTHING — measured: with the
        // pre-fix code restored, an empty-ledger version of this arm PASSED while the other three
        // aborted. It seeds the agent cell exactly as `AgentRuntime::new` does.
        //
        // ⚑ AND THE PASS CONDITION IS THE PROVENANCE COUNTER, not "a Result came back".
        // `dregg_pq::pq_provenance()` counts, per direction, how many operations the VERIFIED core
        // answered. Asserting it moved is what makes this arm unable to go green by not reaching
        // the gate — the failure mode it was written with the first time.
        "engine_executes_hybrid_turn" => {
            let clerk = dregg_sdk::AgentCipherclerk::new();
            let target = clerk.cell_id("default");
            let fed = [0u8; 32];
            // ⚑ THE EFFECT IS LOAD-BEARING TOO. `verify_authorization` dispatches on what the
            // action REQUIRES: an effect-free action lands on `AuthRequired::None => Ok(())` and is
            // admitted without its `HybridSignature` ever being looked at — correct (there is
            // nothing to authorize) and useless here. A `SetField` on the agent's own cell demands
            // `AuthRequired::Signature`, which is the arm that reaches the hybrid branch.
            let mut unsigned = empty_action(target, 1);
            unsigned.effects = vec![dregg_sdk::Effect::SetField {
                cell: target,
                index: 0,
                value: [7u8; 32],
            }];
            let action = clerk.sign_action(unsigned, &fed);
            let mut turn = clerk.make_turn(action);
            // `make_turn` defaults `fee` to 0, and the fee IS the computron budget — so the
            // executor refuses with `BudgetExceeded { limit: 0, used: 100 }` before it authorizes
            // anything. (Found by the provenance assertion below, which is the whole reason it is
            // there.) `sign_action` signs the ACTION, not the turn envelope, so setting this does
            // not disturb the signature the hybrid branch is about to check.
            turn.fee = 100_000;

            let mut ledger = dregg_sdk::Ledger::new();
            ledger
                .insert_cell(dregg_cell::Cell::with_balance(
                    clerk.public_key().0,
                    *blake3::hash(b"default").as_bytes(),
                    1_000_000,
                ))
                .expect("fresh ledger, no conflict");

            let before = verified_ml_dsa_verifies();
            let mut engine = dregg_sdk::embed::DreggEngine::with_ledger(
                dregg_sdk::embed::EngineConfig::for_testing(),
                ledger,
            );
            let outcome = engine.execute_turn(&turn);
            let after = verified_ml_dsa_verifies();
            println!(
                "ARM SURVIVED: execute_turn -> ok={}, verified ml_dsa_verify answers {before} -> {after}",
                outcome.is_ok()
            );
            assert!(
                after > before,
                "the executor never reached `ml_dsa_verify` — this arm would have passed without \
                 exercising the gate it exists to exercise (execute_turn returned {outcome:?})"
            );
        }

        // ── THE ANTI-VACUITY ARM: nothing built, and the gate MUST still bite ────────────────
        // No SDK object of any kind. This is the boundary the fix deliberately does NOT move: the
        // SDK arms its cores from its own gateways, not from a process-start initializer, so a
        // consumer that reaches `dregg_turn::pq` directly having asked the SDK for nothing still
        // refuses. If this arm ever stops aborting, the four arms above have become vacuous — they
        // would pass on a process where the cores were armed by something other than the gateway
        // under test, which is precisely the ordering bug this file exists to rule out.
        "nothing_then_verify" => {
            let accepted = drive_one_verify();
            println!("ARM SURVIVED THE GATE: verify -> {accepted}");
        }

        other => {
            eprintln!("ARM: unknown role {other}");
            std::process::exit(3);
        }
    }
    std::process::exit(0)
}

fn empty_action(target: dregg_sdk::CellId, method: u8) -> dregg_turn::action::Action {
    dregg_turn::action::Action {
        target,
        method: [method; 32],
        args: vec![],
        authorization: dregg_turn::action::Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: dregg_turn::action::DelegationMode::None,
        commitment_mode: dregg_turn::action::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// Re-exec this binary as a child running exactly `role`.
///
/// `DREGG_ALLOW_UNAUDITED_PQ` is REMOVED from the child's environment, never set: routing a PQ
/// operation onto the unaudited `fips204` crate is the substitution the gate exists to prevent, and
/// setting it would make every arm below pass for the wrong reason. `DREGG_REQUIRE_LEAN` is removed
/// too, so an inherited demand cannot revoke an install the arm is supposed to be testing.
fn run_arm(role: &str) -> std::process::Output {
    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = Command::new(exe);
    cmd.arg("arm_dispatcher")
        .arg("--exact")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(ROLE, role)
        .env_remove("DREGG_ALLOW_UNAUDITED_PQ")
        .env_remove("DREGG_REQUIRE_LEAN");
    cmd.output().expect("spawn arm")
}

/// The re-exec landing pad. In a parent run the marker is unset and this is a no-op.
#[test]
fn arm_dispatcher() {
    if let Ok(role) = std::env::var(ROLE) {
        child_body(&role);
    }
}

/// Assert an arm ran to completion — no abort, no panic.
fn assert_survived(role: &str) {
    let out = run_arm(role);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_ne!(
            out.status.signal(),
            Some(6),
            "`{role}` died on SIGABRT — `dregg-pq` refused a PQ operation because this \
             construction path armed no verified core. That is the production hole, not a test \
             artifact: the same code in a service aborts the process.\nstdout:\n{stdout}\n\
             stderr:\n{stderr}"
        );
    }
    assert!(
        out.status.success(),
        "`{role}` did not complete.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("ARM SURVIVED"),
        "`{role}` exited 0 without reaching its assertion — the arm is not driving what it \
         claims.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// ★ A `DreggEngine` host — no `AgentRuntime` anywhere — can verify.
#[test]
fn embed_engine_alone_arms_the_verify_core() {
    assert_survived("engine_then_verify");
}

/// ★ A cipherclerk host — no `AgentRuntime` anywhere — can verify, not merely sign.
#[test]
fn cipherclerk_alone_arms_the_verify_core() {
    assert_survived("cipherclerk_then_verify");
}

/// ★ Sign and verify in one runtime-less process, on a GENUINE signature.
#[test]
fn sign_then_verify_without_a_runtime() {
    assert_survived("sign_then_verify");
}

/// ★ The executor's own `HybridSignature` admission runs under an embed engine.
#[test]
fn embed_engine_executes_a_hybrid_turn_without_a_runtime() {
    assert_survived("engine_executes_hybrid_turn");
}

/// ★ **THE ANTI-VACUITY TOOTH.** With no SDK object constructed, the gate must still abort.
///
/// This is what keeps the four arms above meaningful. They assert that a specific construction
/// ARMS the cores; that assertion is only worth something if a process which constructs nothing
/// still refuses. It also pins the design decision: `dregg-sdk` arms from its gateways, and
/// deliberately not from a `.init_array` initializer that would arm every process linking it.
#[test]
fn no_sdk_object_still_refuses_and_says_why() {
    let out = run_arm("nothing_then_verify");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);

    assert!(
        !out.status.success(),
        "ml_dsa_verify SURVIVED in a process that installed nothing — the gate is not \
         biting, so every other test in this file is vacuous.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("ARM SURVIVED THE GATE"),
        "the gate did not stop the call:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    // SIGABRT (6), not a catchable panic: a panic is swallowed at a task boundary in a deployed
    // server, which would restore the silent substitution.
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(
            out.status.signal(),
            Some(6),
            "expected SIGABRT (process::abort), got {:?}.\nstderr:\n{stderr}",
            out.status
        );
    }

    // The banner must name the operation and the install that fixes it — this is the text that
    // told us the SDK's hole was on VERIFY and not on keygen.
    for needle in [
        "refused to run UNAUDITED post-quantum crypto",
        "ML-DSA-65 verify",
        "fips204 0.4",
        "install_verified_mldsa_verify_core",
    ] {
        assert!(
            stderr.contains(needle),
            "refusal banner is missing {needle:?}.\nstderr:\n{stderr}"
        );
    }
}
