//! marshal_roundtrip.rs — THE GATE: the round-trip test for the T8/T9 marshaller
//! (`marshal.rs`) against the REAL Lean FFI `@[export] dregg_exec_full_forest_auth`.
//!
//! This is the non-negotiable correctness gate. It proves the Rust marshaller's wire
//! is BYTE-CORRECT against the live Lean parser by:
//!   * marshalling a `WireState` + `WireTurn` and feeding the string to the kernel via
//!     the existing C-ABI bridge `dregg_exec_full_forest_auth_str`;
//!   * asserting the output PARSES (`unmarshal_result`) and is SENSIBLE (commit bit +
//!     expected per-asset balance delta);
//!   * exercising the fail-closed contracts: a legitimate ROLLBACK (over-spend, forged
//!     credential) must echo the unchanged state with ok:0, while a byte-MUTATED wire
//!     must produce the empty-state MalformedWireSentinel — proving the marshaller never
//!     confuses "I sent garbage" (a bug) with "the turn was rejected" (legitimate).
//!
//! It is a BIN (not a #[test]) for the same reason every other harness here is: the Lean
//! runtime must be brought up exactly once (`dregg_ffi_init`) before any export is called.
//!
//! The seed cases mirror the Lean `#eval` fixtures in FFI.lean §WG so the bytes are
//! cross-checkable against the source of truth:
//!   * `wideDemoState`   (FFI.lean:2745) — 2 cells, caps, all 5 side-tables populated;
//!   * `gatedDemoTurn`   (FFI.lean:3044) — transfer 30 (cell0->cell1, asset0) under a
//!     genuine `.signature 7 7` + a monotone caveat, with a child escrow under `.token 3 3`.
//!     Both credentials pass the §1 portal ⇒ the gated tree COMMITS (ok:1).

// Force an rlib edge to the `dregg_lean_ffi` lib so this bin inherits the build script's
// PROPAGATED native-lib link directives (the shim + Lean closure via `links = "dregg_lean"`).
extern crate dregg_lean_ffi as _;

#[path = "marshal.rs"]
mod marshal;

use marshal::*;
use std::ffi::CString;
use std::os::raw::c_char;
use std::process::ExitCode;

// --- The C bridge over the Lean GATED complete-turn executor (src/lean_init.c). ---
extern "C" {
    fn dregg_ffi_init() -> i32;
    /// Boxes `in_utf8`, calls the verified `dregg_exec_full_forest_auth`, writes the result
    /// (NUL-terminated, truncated to `out_cap-1`) into `out`, returns the full byte length.
    fn dregg_exec_full_forest_auth_str(
        in_utf8: *const c_char,
        out: *mut c_char,
        out_cap: usize,
    ) -> usize;
}

/// Call the Lean gated executor with a wire string, returning the result wire string.
/// Grows the output buffer on truncation (the kernel echoes/extends the input).
fn lean_forest_auth(wire: &str) -> String {
    let c_in = CString::new(wire).expect("wire has interior NUL");
    let mut cap = wire.len() * 2 + 1024;
    loop {
        let mut buf = vec![0u8; cap];
        let full = unsafe {
            dregg_exec_full_forest_auth_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
        };
        if full == usize::MAX {
            panic!("dregg_exec_full_forest_auth_str: unusable output buffer");
        }
        if full < cap {
            let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
            return String::from_utf8(buf[..nul].to_vec()).expect("result not UTF-8");
        }
        cap = full + 1;
    }
}

// =============================================================================
// The seed fixtures — byte-mirrors of the Lean `#eval` fixtures.
// =============================================================================

/// `wideDemoState` (FFI.lean:2745): cell0 bal[asset0]=100, cell1 bal[asset0]=5, a cap
/// table (holder 9 has `node 0`), and ONE entry in EACH side-table.
fn wide_demo_state() -> WireState {
    WireState {
        cells: vec![
            (
                0,
                WireValue::Record(vec![
                    ("balance".into(), WireValue::Int(100)),
                    ("nonce".into(), WireValue::Int(7)),
                ]),
            ),
            (1, WireValue::Record(vec![("balance".into(), WireValue::Int(5))])),
        ],
        caps: vec![(9, vec![Cap::Node(0)])],
        bal: vec![(0, 0, 100), (1, 0, 5)],
        escrows: vec![WireEscrow {
            id: 1,
            creator: 0,
            recipient: 1,
            amount: 7,
            resolved: false,
            asset: 0,    // wideDemoState omits asset/bridge/queue* => they default to 0/false/none
            bridge: false,
            queue_dep: None,
            queue_msg: None,
        }],
        nullifiers: vec![111],
        commitments: vec![222],
        queues: vec![WireQueue { id: 1, owner: 0, capacity: 4, buffer: vec![333, 444] }],
        swiss: vec![WireSwiss {
            swiss: 5,
            exporter: 0,
            target: 1,
            rights: vec![Auth::Read, Auth::Write],
            refcount: 1,
            cert: Some(99),
        }],
        revoked: vec![], // wideDemoState omits `revoked` => defaults empty
    }
}

/// A transfer-only gated turn: the root transfers 30 of asset 0 (cell0->cell1) under a
/// genuine `.signature 7 7` AND a monotone caveat ⟨0,0,0,0⟩ ("cell 0 holds >= 0 of asset 0",
/// trivially true on the pre-state). The credential passes the §1 portal (proof echoes the
/// statement) and the caveat discharges ⇒ the gated tree COMMITS, conserving asset 0
/// (100+5 = 70+35). This is `gatedDemoTurn`'s credential shape minus the child escrow, so the
/// balance delta is the CLEAN conserved transfer (loglen:1) rather than the escrow-debited
/// 60/35 (loglen:2) the full `gatedDemoTurn` produces — keeping the conservation assertion
/// crisp. The expected wire is GOLDEN_INPUT below.
fn gated_demo_turn() -> WireTurn {
    WireTurn {
        agent: 0,
        nonce: 7,
        fee: 5,
        valid_until: 1000,
        block_height: 0,
        prev_hash: Digest::default(),
        root: WForest {
            auth: WireAuth::Signature { pubkey: Digest::from_u64(7), sig: 7 },
            caveats: vec![WireCaveat { tier: 0, cell: 0, asset: 0, min: 0 }],
            action: WireAction::Balance { actor: 0, src: 0, dst: 1, amt: 30, asset: 0 },
            children: vec![],
        },
    }
}

/// The EXACT golden input wire the Lean side emits for `wide_demo_state()` + `gated_demo_turn()`
/// (captured from `IO.println (encodeWState wideDemoState ++ encodeWTurn myTurn)` against
/// metatheory/Dregg2/Exec/FFI.lean). `marshal_turn` must reproduce this BYTE-FOR-BYTE — that
/// is the Layer-0 byte-equality gate, the strongest possible check short of the live parser.
const GOLDEN_INPUT: &str = "{\"host\":{\"now\":0,\"block_height\":0,\"frozen\":[],\"stored_head\":0,\"budget\":1000000000},\"state\":{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}],[\"nonce\",{\"int\":7}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[[9,[{\"node\":0}]]],\"bal\":[[0,0,100],[1,0,5]],\"escrows\":[[1,0,1,7,0,0,0,{\"none\":0},{\"none\":0}]],\"nullifiers\":[111],\"commitments\":[222],\"queues\":[[1,0,4,[333,444]]],\"swiss\":[[5,0,1,[0,1],1,{\"some\":99}]],\"revoked\":[]},\"turn\":{\"agent\":0,\"nonce\":7,\"fee\":5,\"valid_until\":1000,\"prev\":\"0000000000000000000000000000000000000000000000000000000000000000\",\"root\":{\"auth\":{\"sig\":[\"0000000000000000000000000000000000000000000000000000000000000007\",7]},\"caveats\":[[0,0,0,0]],\"action\":{\"bal\":[0,0,1,30,0]},\"children\":[]}}}";

/// A forged-credential turn (FFI.lean:3072 `forgedGatedTurn`): the SAME transfer under
/// `.signature 7 8` (proof does NOT echo the statement ⇒ the §1 portal REJECTS ⇒ rollback).
fn forged_turn() -> WireTurn {
    WireTurn {
        agent: 0,
        nonce: 0,
        fee: 0,
        valid_until: 0,
        block_height: 0,
        prev_hash: Digest::default(),
        root: WForest {
            auth: WireAuth::Signature { pubkey: Digest::from_u64(7), sig: 8 },
            caveats: vec![],
            action: WireAction::Balance { actor: 0, src: 0, dst: 1, amt: 30, asset: 0 },
            children: vec![],
        },
    }
}

/// Wrong nonce (stored 7, claimed 6) ⇒ `admissible = false` ⇒ `runGatedForestTurn = none`
/// with NO edit (unlike a body rollback, the prologue never runs).
fn bad_nonce_turn() -> WireTurn {
    let mut t = gated_demo_turn();
    t.nonce = 6;
    t
}

/// Fee exceeds agent balance (200 > 100) ⇒ admission leg 5 fails ⇒ inadmissible, no edit.
fn overfee_turn() -> WireTurn {
    let mut t = gated_demo_turn();
    t.fee = 200;
    t
}

/// An over-spend turn under `.unchecked` (transfer 1000 > cell0's 100) ⇒ the ledger
/// availability check fails ⇒ `execFullForestG = none` ⇒ rollback echoing the unchanged
/// state (the `wideRollbackTurn` shape, FFI.lean:2772, run through the GATED export).
fn overspend_turn() -> WireTurn {
    WireTurn {
        agent: 0,
        nonce: 0,
        fee: 0,
        valid_until: 0,
        block_height: 0,
        prev_hash: Digest::default(),
        root: WForest {
            auth: WireAuth::Unchecked,
            caveats: vec![],
            action: WireAction::Balance { actor: 0, src: 0, dst: 1, amt: 1000, asset: 0 },
            children: vec![],
        },
    }
}

/// Read `bal cell asset` out of a decoded post-state (0 if the slot is absent — matching
/// the Lean `balOfEntries` "listed slot, else 0" regime read at the input's bal keys).
fn bal_of(st: &WireState, cell: u64, asset: u64) -> i128 {
    st.bal
        .iter()
        .find(|(c, a, _)| *c == cell && *a == asset)
        .map(|(_, _, amt)| *amt)
        .unwrap_or(0)
}

fn main() -> ExitCode {
    let rc = unsafe { dregg_ffi_init() };
    if rc != 0 {
        eprintln!("FATAL: Lean module initialization failed (rc={rc})");
        return ExitCode::FAILURE;
    }

    println!("=== T8/T9 marshaller round-trip vs dregg_exec_full_forest_auth ===");
    let mut failures = 0u32;

    // ---------------------------------------------------------------------
    // CASE 1 — the gated demo COMMITS, with the conserved balance delta.
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let turn = gated_demo_turn();
        let wire = match marshal_turn(&state, &turn) {
            Ok(w) => w,
            Err(e) => {
                println!("  [case1] FAIL: marshal_turn errored: {e}");
                return ExitCode::FAILURE;
            }
        };
        println!("  [case1] marshalled wire ({} bytes):", wire.len());
        println!("          {wire}");

        // LAYER 0 — byte-equality against the Lean golden. If this fails, STOP: nothing
        // downstream is meaningful (this is where whitespace/key-order/hex-case/field-order
        // bugs surface unambiguously).
        if wire == GOLDEN_INPUT {
            println!("  [case1] PASS (layer-0): marshal_turn output is BYTE-IDENTICAL to the Lean golden input wire");
        } else {
            println!("  [case1] FAIL (layer-0): marshal_turn output != Lean golden. First diff:");
            let (a, b) = (wire.as_bytes(), GOLDEN_INPUT.as_bytes());
            let n = a.len().min(b.len());
            let mut at = n;
            for k in 0..n {
                if a[k] != b[k] {
                    at = k;
                    break;
                }
            }
            let lo = at.saturating_sub(20);
            println!(
                "          at byte {at}:\n            got: ...{}\n            want:...{}",
                &wire[lo..(at + 20).min(wire.len())],
                &GOLDEN_INPUT[lo..(at + 20).min(GOLDEN_INPUT.len())]
            );
            failures += 1;
        }

        let out = lean_forest_auth(&wire);
        println!("  [case1] kernel out:");
        println!("          {out}");

        match unmarshal_result(&out) {
            Ok(res) => {
                let pre0 = bal_of(&state, 0, 0);
                let pre1 = bal_of(&state, 1, 0);
                let post0 = bal_of(&res.state, 0, 0);
                let post1 = bal_of(&res.state, 1, 0);
                // Expect: ok:1; cell0 asset0 100->70, cell1 asset0 5->35; conserved (sum=105).
                let ok = res.committed
                    && post0 == 70
                    && post1 == 35
                    && (post0 + post1) == (pre0 + pre1);
                if ok {
                    println!(
                        "  [case1] PASS: COMMIT (ok:1), loglen={}, bal cell0 asset0 {pre0}->{post0}, cell1 asset0 {pre1}->{post1} (conserved sum {})",
                        res.loglen,
                        post0 + post1
                    );
                } else {
                    println!(
                        "  [case1] FAIL: committed={} post0={post0} (want 70) post1={post1} (want 35)",
                        res.committed
                    );
                    failures += 1;
                }
            }
            Err(e) => {
                println!("  [case1] FAIL: unmarshal_result errored: {e}");
                failures += 1;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CASE 2 — a FORGED credential ROLLS BACK (ok:0, state echoed unchanged).
    //          This is the gate having TEETH: the same ledger op, a bad proof.
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let wire = marshal_turn(&state, &forged_turn()).expect("marshal forged");
        let out = lean_forest_auth(&wire);
        match unmarshal_result(&out) {
            Ok(res) => {
                let unchanged = !res.committed
                    && bal_of(&res.state, 0, 0) == 100
                    && bal_of(&res.state, 1, 0) == 5
                    && res.loglen == 0;
                if unchanged {
                    println!("  [case2] PASS: forged credential ROLLED BACK (ok:0), bal unchanged (100/5), loglen=0");
                } else {
                    println!(
                        "  [case2] FAIL: expected rollback w/ unchanged state; got committed={} bal0={} bal1={} loglen={}",
                        res.committed,
                        bal_of(&res.state, 0, 0),
                        bal_of(&res.state, 1, 0),
                        res.loglen
                    );
                    failures += 1;
                }
            }
            Err(UnmarshalError::MalformedWireSentinel) => {
                println!("  [case2] FAIL: kernel returned the malformed-wire sentinel — our wire was MALFORMED (marshalling bug), not a rejection!");
                failures += 1;
            }
            Err(e) => {
                println!("  [case2] FAIL: unmarshal_result errored: {e}");
                failures += 1;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CASE 3 — an OVER-SPEND ROLLS BACK (ok:0, state echoed unchanged).
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let wire = marshal_turn(&state, &overspend_turn()).expect("marshal overspend");
        let out = lean_forest_auth(&wire);
        match unmarshal_result(&out) {
            Ok(res) => {
                let unchanged = !res.committed
                    && bal_of(&res.state, 0, 0) == 100
                    && bal_of(&res.state, 1, 0) == 5;
                if unchanged {
                    println!("  [case3] PASS: over-spend ROLLED BACK (ok:0), bal unchanged (100/5)");
                } else {
                    println!(
                        "  [case3] FAIL: expected rollback; got committed={} bal0={} bal1={}",
                        res.committed,
                        bal_of(&res.state, 0, 0),
                        bal_of(&res.state, 1, 0)
                    );
                    failures += 1;
                }
            }
            Err(e) => {
                println!("  [case3] FAIL: unmarshal_result errored: {e}");
                failures += 1;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CASE 4 — a BYTE-MUTATED wire ⇒ the kernel's parser fails ⇒ empty-state
    //          sentinel ⇒ unmarshal_result returns MalformedWireSentinel.
    //          We inject ONE space right after the opening `{` so the kernel's very
    //          first `lit "{\"state\":"` fails-closed. (Uppercasing a hex nibble would
    //          NOT work — parseHex32 accepts A-F on parse; we need a STRUCTURAL break.)
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let good = marshal_turn(&state, &gated_demo_turn()).expect("marshal good");
        // `{"host":...` -> `{ "host":...`  — a single injected space breaks the kernel's very
        // first `lit "{\"host\":"` (the host context is the new leading wire field, bug 1).
        let mutated = good.replacen("{\"host\"", "{ \"host\"", 1);
        assert_ne!(mutated, good, "mutation must change the wire");
        let out = lean_forest_auth(&mutated);
        match unmarshal_result(&out) {
            Err(UnmarshalError::MalformedWireSentinel) => {
                println!("  [case4] PASS: byte-mutated wire ⇒ empty-state sentinel ⇒ MalformedWireSentinel (a marshalling bug is NOT mistaken for a rollback)");
            }
            Ok(res) => {
                println!(
                    "  [case4] FAIL: expected MalformedWireSentinel; got committed={} (the mutated wire still parsed in the kernel?!)",
                    res.committed
                );
                failures += 1;
            }
            Err(e) => {
                println!("  [case4] FAIL: unmarshal_result errored unexpectedly: {e}");
                failures += 1;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CASE 6 — ADMISSION: nonce replay ⇒ inadmissible ⇒ ok:0, state unchanged.
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let wire = marshal_turn(&state, &bad_nonce_turn()).expect("marshal bad nonce");
        let out = lean_forest_auth(&wire);
        match unmarshal_result(&out) {
            Ok(res) => {
                let unchanged = !res.committed
                    && bal_of(&res.state, 0, 0) == 100
                    && bal_of(&res.state, 1, 0) == 5
                    && res.loglen == 0;
                if unchanged {
                    println!(
                        "  [case6] PASS: nonce replay INADMISSIBLE (ok:0), bal unchanged (100/5), loglen=0"
                    );
                } else {
                    println!(
                        "  [case6] FAIL: expected inadmissible no-edit; got committed={} bal0={} bal1={} loglen={}",
                        res.committed,
                        bal_of(&res.state, 0, 0),
                        bal_of(&res.state, 1, 0),
                        res.loglen
                    );
                    failures += 1;
                }
            }
            Err(e) => {
                println!("  [case6] FAIL: unmarshal_result errored: {e}");
                failures += 1;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CASE 7 — ADMISSION: fee > balance ⇒ inadmissible ⇒ ok:0, state unchanged.
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let wire = marshal_turn(&state, &overfee_turn()).expect("marshal overfee");
        let out = lean_forest_auth(&wire);
        match unmarshal_result(&out) {
            Ok(res) => {
                let unchanged = !res.committed
                    && bal_of(&res.state, 0, 0) == 100
                    && bal_of(&res.state, 1, 0) == 5
                    && res.loglen == 0;
                if unchanged {
                    println!(
                        "  [case7] PASS: insufficient fee INADMISSIBLE (ok:0), bal unchanged (100/5), loglen=0"
                    );
                } else {
                    println!(
                        "  [case7] FAIL: expected inadmissible no-edit; got committed={} bal0={} bal1={} loglen={}",
                        res.committed,
                        bal_of(&res.state, 0, 0),
                        bal_of(&res.state, 1, 0),
                        res.loglen
                    );
                    failures += 1;
                }
            }
            Err(e) => {
                println!("  [case7] FAIL: unmarshal_result errored: {e}");
                failures += 1;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CASE 5 — all 56 FullActionA arms PARSE through the live Lean kernel.
    //          For each arm: marshal a minimal turn rooted at that action against
    //          wide_demo_state, call lean_forest_auth, assert the output is NOT the
    //          MalformedWireSentinel (unmarshal_result succeeds — we don't need commit).
    // ---------------------------------------------------------------------
    {
        let state = wide_demo_state();
        let arms = all_action_arms_demo();
        assert_eq!(arms.len(), 56, "all_action_arms_demo must cover every Lean arm");
        let mut arm_failures = 0u32;
        for (i, action) in arms.iter().enumerate() {
            let turn = demo_turn_for_action(action.clone());
            let wire = match marshal_turn(&state, &turn) {
                Ok(w) => w,
                Err(e) => {
                    println!("  [case5] arm {i} FAIL: marshal_turn errored: {e}");
                    arm_failures += 1;
                    continue;
                }
            };
            let out = lean_forest_auth(&wire);
            match unmarshal_result(&out) {
                Ok(_res) => {
                    // Parsed successfully — commit/rollback both acceptable.
                }
                Err(UnmarshalError::MalformedWireSentinel) => {
                    println!(
                        "  [case5] arm {i} FAIL: Lean returned MalformedWireSentinel — action did not parse"
                    );
                    arm_failures += 1;
                }
                Err(e) => {
                    println!("  [case5] arm {i} FAIL: unmarshal_result errored: {e}");
                    arm_failures += 1;
                }
            }
        }
        if arm_failures == 0 {
            println!(
                "  [case5] PASS: all {} FullActionA arms marshal+parse through dregg_exec_full_forest_auth",
                arms.len()
            );
        } else {
            println!("  [case5] FAIL: {arm_failures}/{} arms did not parse", arms.len());
            failures += arm_failures;
        }
    }

    println!();
    if failures == 0 {
        println!(
            "ALL PASS — the T8/T9 marshaller's wire is BYTE-CORRECT against the live Lean parser \
             (dregg_exec_full_forest_auth): admission+gated commit conserved, \
             forged/overspend/admission rejections roll back or no-edit, malformed wire distinguished."
        );
        ExitCode::SUCCESS
    } else {
        eprintln!("{failures} round-trip assertion(s) FAILED — the marshaller is NOT byte-correct.");
        ExitCode::FAILURE
    }
}
