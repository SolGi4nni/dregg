//! round_advance_probe — the TRANSPORT probe for the verified ES round-advance gate
//! (`@[export] dregg_round_advance`, `Dregg2.Distributed.RoundAdvanceGate`).
//!
//! The RULE's verdicts on these exact wires are Lean-PROVEN (`wire_advances_trace3` /
//! `wire_holds_noLeader` / `wire_timeout_advances_noLeader` / `wire_bad_timeout_bit_errs`,
//! all `#assert_compiled`). What this test adds is the C-ABI leg the theorems cannot see:
//! the archive exports the symbol, `dregg_ffi_init` runs the module initializer, the string
//! bridge round-trips, and the verdicts arrive intact in Rust. It also times the raw FFI call
//! (decode + memoized `advanceGateFast` + encode) — the pure-gate half of the producer's
//! good-case latency (the node-side `consult` adds the lace encoder on top).
//!
//! Self-skips without the export (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).

/// `trace3` (the Lean fixture): 3 creators, 3 fully cross-linked rounds, participants 1,2,3.
/// Wire grammar: `r=<round>;t=<0|1>;w=<W>;P=<..>;B=<id:creator:seq:preds|..>`.
const TRACE3_TAIL: &str = "w=3;P=1,2,3;B=10:1:0:|20:2:0:|30:3:0:|11:1:1:10.20.30|21:2:1:10.20.30|31:3:1:10.20.30|12:1:2:11.21.31|22:2:2:11.21.31|32:3:2:11.21.31";

/// `traceNoLeader` (the Lean fixture): n=4, round 1 filled by creators 2,3,4 — cordial
/// (supermajority(4)=3) with the wave-0 round-robin leader (participant 1) ABSENT.
const NOLEADER_TAIL: &str = "w=3;P=1,2,3,4;B=20:2:0:|30:3:0:|40:4:0:";

#[test]
fn round_advance_transport_and_latency() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::round_advance_available(),
        "the Lean round-advance export (round_advance_available()==false)",
    ) {
        return;
    }

    // ── PROMPT POLE on trace3 (Lean: `wire_advances_trace3`): mid-wave round 2, leader block
    //    prefix-ratified, NO timeout — the verdict must arrive as "1" through the real bridge.
    let advance = dregg_lean_ffi::shadow_round_advance(&format!("r=2;t=0;{TRACE3_TAIL}"))
        .expect("export present");
    assert_eq!(
        advance, "1",
        "trace3 r=2 must ADVANCE promptly (Lean wire_advances_trace3)"
    );

    // ── REFUSAL POLE (Lean: `wire_holds_noLeader`): cordial-but-leaderless holds at t=0 …
    let hold = dregg_lean_ffi::shadow_round_advance(&format!("r=1;t=0;{NOLEADER_TAIL}"))
        .expect("export present");
    assert_eq!(
        hold, "0",
        "a cordial creator-supermajority WITHOUT the leader must HOLD (the line-67 clause)"
    );
    // … and the timeout bit un-sticks the SAME wire (Lean: `wire_timeout_advances_noLeader`).
    let unstick = dregg_lean_ffi::shadow_round_advance(&format!("r=1;t=1;{NOLEADER_TAIL}"))
        .expect("export present");
    assert_eq!(
        unstick, "1",
        "the timeout must un-stick the leaderless round (Prop. 38)"
    );

    // ── FAIL-CLOSED (Lean: `wire_bad_timeout_bit_errs`): a malformed timeout bit is ERR.
    let err =
        dregg_lean_ffi::shadow_round_advance("r=1;t=2;w=3;P=1,2,3;B=").expect("export present");
    assert_eq!(
        err, "ERR",
        "a bad timeout bit must be the fail-closed sentinel"
    );

    // ── LATENCY of the raw gate call (decode + advanceGateFast + encode), median of 100 on the
    //    9-block trace3 wire. ⚠ Printed, not asserted: read it alongside the reported box load —
    //    a saturated box prices the fleet, not the code.
    let wire = format!("r=2;t=0;{TRACE3_TAIL}");
    let mut samples: Vec<u128> = (0..100)
        .map(|_| {
            let t0 = std::time::Instant::now();
            let v = dregg_lean_ffi::shadow_round_advance(&wire).expect("export present");
            assert_eq!(v, "1");
            t0.elapsed().as_micros()
        })
        .collect();
    samples.sort_unstable();
    eprintln!(
        "ES-GATE RAW FFI LATENCY (trace3, 9 blocks, n=3): median {} µs, p90 {} µs, max {} µs \
         over 100 calls",
        samples[50], samples[90], samples[99]
    );
}
