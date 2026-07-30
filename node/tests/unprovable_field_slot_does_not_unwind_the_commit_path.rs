//! # GitHub #62 — a wedged prover must not take the durable barrier down with it.
//!
//! ═══ WHAT WAS REPORTED ═══════════════════════════════════════════════════════════
//! A `dregg-cave-node` running for days on a disk data-dir was "accepting and receipting
//! turns normally (`ingress-immediate`, consensus_final on the API), but its redb file's
//! bytes did not change across 17 minutes of committed turns and a clean SIGTERM". A
//! restore-and-cold-boot lost that window. Correlated with #61's repeated prover panic
//! (`SetField field_idx out of bounds: 8`); reported as "prover starvation".
//!
//! ═══ WHAT IT ACTUALLY IS ═════════════════════════════════════════════════════════
//! Not starvation — an UNWIND ACROSS THE DURABLE BARRIER. In
//! `node::blocklace_sync::execute_finalized_turn` the full-turn proving leg runs INLINE
//! (its own comment: "the full-turn PROVING FFI below still runs inline under the (now
//! briefly re-acquired) write lock"), and the durable commit-log write —
//! `commit_finalized_turn_with_faithful_root_and_executor_state` — is LATER IN THE SAME
//! FUNCTION. `prove_and_verify_finalized_turn` reached
//! `assert!(field_idx < 8)` inside the trace generator and PANICKED, so the unwind left
//! the function before it ever reached the barrier. The RAM ledger and the receipt were
//! already published; redb was not. Every subsequent turn with a payload-slot write did
//! the same thing, so the store simply stopped advancing while the API kept saying yes.
//!
//! On the OTHER path (`node::prove_pool`, the async HTTP one) `spawn_blocking` catches the
//! panic, so there the same defect shows up as #61: `receipt stays committed-but-unattested`,
//! forever, for that whole traffic class.
//!
//! ═══ WHAT THIS TEST PINS ═════════════════════════════════════════════════════════
//! That the node's prover entry point RETURNS on a witness the AIR cannot carry. Not that
//! it succeeds — it must not, the write genuinely has no proof lane — but that the failure
//! is a VALUE the caller can carry to its next statement, which on the finalized path is
//! the durable commit.
//!
//! The bound itself is CORRECT and is not raised here; see
//! `circuit/tests/setfield_air_lane_bound_pin.rs` for the measurement (Lean `Fin 8`, the
//! emitted registries' eight per-slot members, and the deployed column layout all agree).

use dregg_circuit::effect_vm::state;
use dregg_node::turn_proving::{FullTurnProvingError, prove_and_verify_finalized_turn};
use dregg_types::CellId;

/// The first slot with no AIR lane — the exact index in #61's panic string.
const FIRST_UNPROVABLE_SLOT: u64 = state::NUM_FIELDS as u64;

fn set_field(cell: CellId, index: u64) -> dregg_turn::Effect {
    dregg_turn::Effect::SetField {
        cell,
        index,
        value: [0x5a; 32],
    }
}

/// **THE #62 REGRESSION.** The prover entry point the finalized-turn path calls inline must
/// RETURN — not unwind — for a `SetField` whose slot the deployed AIR has no lane for.
///
/// The `catch_unwind` is the whole assertion. `Err(_)` from the prover is FINE and expected;
/// a panic is the defect, because a panic is what skipped
/// `commit_finalized_turn_with_faithful_root_and_executor_state`.
///
/// ANTI-VACUITY: three separate things are checked, and no one of them alone would catch a
/// regression —
///   1. the call returned at all (the unwind check);
///   2. it returned a REFUSAL naming the offending slot and the lane count, not a generic
///      failure that an operator would read as a transient prover error and retry forever;
///   3. the SENTINEL below still runs — i.e. a caller's downstream durable step is reached.
///      A test that only asserted `is_err()` would pass equally well if the prover silently
///      succeeded on a fabricated trace, and one that only asserted "no panic" would pass if
///      the refusal were deleted.
#[test]
fn an_unprovable_field_slot_returns_a_refusal_instead_of_unwinding() {
    let agent = CellId([0x77; 32]);
    let effects = vec![set_field(agent, FIRST_UNPROVABLE_SLOT)];

    // The caller's "durable barrier": a statement AFTER the prove call. On the finalized path
    // this is the redb commit. If proving unwinds, this never runs — which is #62.
    let mut durable_barrier_reached = false;

    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let r = prove_and_verify_finalized_turn(&agent, 10_000, 0, &effects, [0x11; 32], None);
        durable_barrier_reached = true;
        r
    }));

    let result = outcome.expect(
        "prove_and_verify_finalized_turn UNWOUND on a SetField slot with no AIR lane. This is \
         GitHub #62: on the finalized path this call is inline and upstream of the durable \
         commit-log write in the same function, so an unwind here means the turn is committed \
         and receipted in RAM and NEVER written to redb — the node keeps saying yes while its \
         store stops advancing.",
    );
    assert!(
        durable_barrier_reached,
        "the statement after the prove call must be reached; that statement is the durable \
         commit on the finalized path"
    );

    let err = result.err().expect(
        "a write to a slot with no AIR lane has no proof to make — the prover must REFUSE it, \
         not mint an attestation over a fabricated trace",
    );
    let rendered = err.to_string();
    assert!(
        matches!(err, FullTurnProvingError::Prove(_)),
        "the refusal must be reported as a witness-domain failure, not a verify failure or a \
         capacity error: {rendered}"
    );
    assert!(
        rendered.contains(&FIRST_UNPROVABLE_SLOT.to_string())
            && rendered.contains(&state::NUM_FIELDS.to_string()),
        "the message an operator reads must name the offending slot AND the lane count, so the \
         fix (use slots 0..{}) is legible from the log line alone; got: {rendered}",
        state::NUM_FIELDS - 1
    );
}

/// The refusal must be a BOUND, not a wall: a `SetField` to the last slot the AIR does carry
/// must NOT produce this refusal. Without this, "returns an error instead of panicking" would
/// be satisfiable by refusing every field write, which would take the whole whisper/heartbeat
/// traffic class offline rather than the unprovable half of it.
#[test]
fn the_maximum_provable_slot_is_not_refused_by_the_projection() {
    let agent = CellId([0x78; 32]);
    let effects = vec![set_field(agent, state::NUM_FIELDS as u64 - 1)];

    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_and_verify_finalized_turn(&agent, 10_000, 0, &effects, [0x12; 32], None)
    }))
    .expect("proving the maximum provable slot must not unwind either");

    if let Err(e) = &outcome {
        let rendered = e.to_string();
        assert!(
            !rendered.contains("developer field lanes"),
            "slot {} HAS a state-block column and must never hit the lane refusal; got: {rendered}",
            state::NUM_FIELDS - 1
        );
    }
}

/// **THE PANIC DETECTOR IS LIVE.** `catch_unwind` returning `Ok` above is the load-bearing
/// assertion in this file, so it has to be shown capable of returning `Err`. A closure that
/// panics on purpose, through the same wrapper — if this ever stops catching (panic = abort,
/// a harness change), the two tests above would go green for the wrong reason.
#[test]
fn the_unwind_detector_can_go_red() {
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        panic!("SetField field_idx out of bounds: 8 (must be 0..7)")
    }));
    assert!(
        caught.is_err(),
        "catch_unwind must observe a panic; if it cannot, the unwind assertions in this file \
         are vacuous and #62 could regress silently"
    );
}
