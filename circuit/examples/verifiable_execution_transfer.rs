//! # Verifiable-Execution Beachhead — `execute → prove → verify` for ONE effect (Transfer)
//!
//! This example runs the END-TO-END verifiable-execution path the Lean executor + circuit stack
//! supports for the `Transfer` effect, over the REAL record-cell executor state:
//!
//!   1. EXECUTE: the Lean executor `Dregg2.Exec.RecordKernel.recKExec kS0 goodTurnS` commits the
//!      transfer (actor 0 moves 30 from cell 0 to cell 1; cell 2 is an untouched bystander). The Lean
//!      witness generator `Dregg2.Circuit.TransferWitness.transferWitnessVec` lays the executor's
//!      post-state out as a satisfying full-state assignment, with every digest column filled by the
//!      concrete commitment surface (`compressNConcrete`/`cmbConcrete`/…). The vectors below are the
//!      EXACT bytes Lean's `#guard honestWitnessJson ==` / `forgedWitnessJson ==` goldens pin.
//!   2. PROVE: `prove_executor_derived_transfer` parses the Lean-emitted full-state circuit
//!      (`dregg-transfer-fullstate-v1`: the 9 transfer gates + 3 frame-forcing EQ gates, SOUND for the
//!      18-field `TransferSpec`, NOT the two-balance projection) and proves the witness with the real
//!      Plonky3 STARK prover.
//!   3. VERIFY → ACCEPT: the proof verifies. A FORGED witness (the real `forgedThirdCell` post-state:
//!      bystander cell 2 minted 50 → 999) is REJECTED by the frame-reuse digest gate — the anti-ghost
//!      tooth, end-to-end through the real prover, on a genuine forged state. The two MOVED balances
//!      still conserve, so the old projection circuit would have accepted the forgery; the full-state
//!      circuit does not.
//!
//! Run with: `cargo run -p dregg-circuit --example verifiable_execution_transfer`

use dregg_circuit::lean_descriptor_air::{
    STATE_DESCRIPTOR_JSON_FULLSTATE, parse_descriptor, prove_descriptor,
    prove_executor_derived_transfer, verify_descriptor,
};

/// Executor-derived HONEST witness (`transferWitnessVec kS0 goodTurnS`). Wires:
/// 0..4 = src/dst pre/post balances + amt; 5..10 = guard bits; 11/12 = full-state roots
/// (unconstrained, large); 13/14 = rest digests; 15/16 = untouched-cell frame digests;
/// 17/18/19 = moved-cell digests (pre / post / spec-expected).
const HONEST: [i64; 20] = [
    100,
    5,
    70,
    35,
    30,
    1,
    1,
    1,
    1,
    1,
    1,
    1000150000005000003,
    1000120000035000003,
    3,
    3,
    1000050,
    1000050,
    100000005,
    70000035,
    70000035,
];

/// Executor-derived FORGED witness — same pre/turn, but the REAL `forgedThirdCell` post-state
/// (cell 2 minted 50 → 999). Only the post-root (12) and the untouched-cell frame post digest
/// (16: 1000050 → 1000999) change: the minted bystander perturbs the frame sponge, so `15 != 16`.
const FORGED: [i64; 20] = [
    100,
    5,
    70,
    35,
    30,
    1,
    1,
    1,
    1,
    1,
    1,
    1000150000005000003,
    1001069000035000003,
    3,
    3,
    1000050,
    1000999,
    100000005,
    70000035,
    70000035,
];

fn main() {
    println!("== Verifiable-Execution Beachhead: execute → prove → verify (Transfer) ==\n");

    let desc = parse_descriptor(STATE_DESCRIPTOR_JSON_FULLSTATE).expect("parse full-state circuit");
    println!(
        "Circuit: {} — {} gates, {} wires (full-state; SOUND for the 18-field TransferSpec)",
        desc.name,
        desc.constraints.len(),
        desc.trace_width
    );

    // ---- 1+2+3: honest execute → prove → verify ----
    println!("\n[honest] executor witness = {:?}", HONEST);
    match prove_executor_derived_transfer(&HONEST) {
        Ok(_proof) => println!("[honest] PROVED + VERIFIED ✓  (executor transition accepted)"),
        Err(e) => {
            eprintln!("[honest] UNEXPECTED FAILURE: {e}");
            std::process::exit(1);
        }
    }

    // ---- anti-ghost: forged third-cell-mint must be rejected ----
    println!(
        "\n[forged] executor witness (cell 2 minted 50→999) = {:?}",
        FORGED
    );
    assert_eq!(
        FORGED[2] + FORGED[3],
        FORGED[0] + FORGED[1],
        "the forgery still conserves the two moved balances (the projection ghost)"
    );
    assert_ne!(
        FORGED[15], FORGED[16],
        "but the untouched-cell frame digest changed"
    );

    let rejected = std::panic::catch_unwind(|| {
        let p = prove_descriptor(&desc, &FORGED)?;
        verify_descriptor(&desc, &p)
    });
    match rejected {
        Err(_) => println!("[forged] REJECTED ✓  (prover UNSAT on the frame-reuse gate)"),
        Ok(Err(_)) => println!("[forged] REJECTED ✓  (verification rejected the forged proof)"),
        Ok(Ok(())) => {
            eprintln!("[forged] ANTI-GHOST FAILURE: a third-cell-mint forgery VERIFIED!");
            std::process::exit(1);
        }
    }

    println!(
        "\n== Beachhead complete: the executor-derived transfer transition is verifiable, \
              and a forged post-state is rejected end-to-end. =="
    );
}
