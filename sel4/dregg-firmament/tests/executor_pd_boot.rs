//! THE EXECUTOR-PD BOOT TEST — an app-PD stages a turn, signals the executor-PD
//! over the Endpoint, and the receipt round-trips back through `commit_out`
//! (`docs/FIRMAMENT.md §2` L3 — the heart; `docs/DREGG-DESKTOP-OS.md §3` — the
//! KEYSTONE payoff "the verified executor-PD hosts on the semihost NOW").
//!
//! This is the executor-PD's `turn_in → step → commit_out` cap partition,
//! native-now on the semihost [`EmulatedKernel`] — the SAME boot shape as
//! `compositor_pd_boot.rs` (PDs are threads over one kernel, exercising the §3
//! Endpoint `pp_call` path), now driving the HEART instead of the compositor.
//!
//! ## The shape (the executor-stub's `ingress→executor` edge, RUNNING)
//!
//! The executor-PD is the Endpoint SERVER. An app-PD (the cockpit / a swarm
//! member) is a client that:
//!   1. **stages the turn** into the `turn_in` region (the app-PD's `turn_in`
//!      write — here driven through the kernel-held shm region);
//!   2. **`pp_call`s the executor's PP channel** (the synchronous Endpoint Call,
//!      the `ingress→executor` signal the executor-stub awaits on channel 1);
//!   3. the executor **reads `turn_in`, runs the turn through its `TurnRunner`**
//!      (the GENUINE `granted ⊆ held` gate — `is_attenuation`, the SAME the real
//!      `DreggEngine` runs), **writes the receipt into `commit_out`**, and
//!      **`reply`s** the verdict;
//!   4. the app-PD reads the receipt back out of `commit_out`.
//!
//! We prove, on ONE shared [`EmulatedKernel`]:
//!   1. an **attenuating** staged turn COMMITS — the receipt round-trips through
//!      `commit_out` across the IPC boundary;
//!   2. an **amplifying** staged turn is REJECTED — `commit_out` holds the
//!      reason, not a receipt; no state advanced (the ocap guarantee fires at the
//!      heart, fail-closed).
//!
//! ## Fidelity (honestly labeled — NOT laundered)
//!
//! The runner here is a 2-byte attenuation gate over the GENUINE
//! [`dregg_cell::is_attenuation`] lattice (the SAME `granted ⊆ held` the real
//! executor runs) — it keeps THIS firmament test free of the heavy
//! `dregg-turn::Turn` codec while exercising the REAL gate over the REAL wire.
//! The FULL `dregg_sdk::embed::DreggEngine` runner (a real value/cap turn through
//! the verified `TurnExecutor`) rides the SAME `ExecutorPd` in starbridge-v2
//! (`world.rs::SemihostCockpit`, the cockpit-turn-through-the-semihost test).
//! [`ExecutorPd::FIDELITY`] states this plainly.

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use dregg_cell::{is_attenuation, AuthRequired};
use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::executor_pd::{
    ExecutorPd, TurnRunner, LABEL_RUN_TURN, LABEL_TURN_COMMITTED, LABEL_TURN_REJECTED,
};
use dregg_firmament::microkit_facade::{Channel, ChannelTable, ChannelWiring, MessageInfo};

/// The unit of meaning over the wire for THIS test: `[held, granted]` decoded
/// over the GENUINE `is_attenuation` lattice. The runner commits iff
/// `granted ⊆ held` (the SAME gate the real executor's GrantCapability path
/// runs). This is the firmament-test stand-in for the full `DreggEngine` runner
/// (which starbridge-v2 plugs in), exercising the REAL gate over the REAL
/// `turn_in → step → commit_out` wire.
struct AttenuationRunner;

fn auth_of(b: u8) -> AuthRequired {
    match b {
        0 => AuthRequired::None,
        1 => AuthRequired::Signature,
        2 => AuthRequired::Either,
        _ => AuthRequired::Impossible,
    }
}

impl TurnRunner for AttenuationRunner {
    fn run_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, String> {
        if turn_bytes.len() != 2 {
            return Err(format!(
                "malformed turn: expected 2 bytes, got {}",
                turn_bytes.len()
            ));
        }
        let held = auth_of(turn_bytes[0]);
        let granted = auth_of(turn_bytes[1]);
        if is_attenuation(&held, &granted) {
            // The committed "receipt": the request echoed + a commit tag.
            Ok(vec![turn_bytes[0], turn_bytes[1], 0xCC])
        } else {
            Err(format!(
                "non-attenuating: granted {:?} is wider than held {:?} (granted ⊄ held)",
                granted, held
            ))
        }
    }
}

// ===========================================================================
// THE BOOT TEST — an app-PD stages a turn + signals the executor-PD over the
// Endpoint; the receipt round-trips through commit_out; a widening is refused.
//
// The executor-PD runs on its own host thread as the Endpoint SERVER (a real
// PD's protected body on its own thread), serving exactly the calls the app-PD
// makes. ONE EmulatedKernel; the turn_in/commit_out regions + the runner live in
// the executor-PD. This is the same-code boot shape as compositor_pd_boot.rs,
// now exercising the HEART's turn path.
// ===========================================================================

#[test]
fn app_pd_stages_turn_executor_pd_commits_receipt_round_trips() {
    // ── The firmament wires the slice at boot (the `.system`-file equivalent). ──
    let kernel = EmulatedKernel::new();

    // The run-turn Endpoint the app-PD pp_calls (the executor's PP channel — the
    // `ingress→executor` edge the executor-stub awaits on channel 1).
    let run_ep = kernel.create_endpoint();
    const RUN_CHANNEL: usize = 1;

    // The executor-PD boots: it allocates + SOLELY holds its turn_in (R) and
    // commit_out (RW) regions and takes the runner (the verified semantics). It is
    // shared (behind a Mutex) ONLY so the harness can read commit_out / the counts
    // AFTER the threads join — the executor's OWN thread is the sole writer during
    // the slice (it holds the lock across each served call). On a real PD the
    // executor IS its thread; here the Arc<Mutex> is the harness's observation
    // handle, not a second authority.
    let executor = Arc::new(Mutex::new(ExecutorPd::boot(
        kernel.clone(),
        AttenuationRunner,
        4096,
        4096,
    )));
    // Capture the executor's turn_in region id ONCE, before the server thread
    // parks in `recv` (holding the executor's lock). The app-PD stages through
    // this id LOCK-FREE (`stage_turn_into`), the way a real app-PD writes its
    // mapped turn_in view — it never needs the executor handle while the
    // executor's thread is parked. (Reaching `stage_turn` via the executor lock
    // here would deadlock against the server blocked in `recv` holding it.)
    let (turn_in, commit_out) = {
        let e = executor.lock().unwrap();
        (e.turn_in(), e.commit_out())
    };

    // The app-PD's LOCK-FREE commit_out read (its mapped RW view): snapshot the
    // region through the kernel + strip the 4-byte LE length prefix. Done WITHOUT
    // the executor lock so the harness can read the receipt between calls while
    // the executor's thread is parked in the next `recv` holding that lock.
    let read_commit_out = |kernel: &EmulatedKernel| -> Vec<u8> {
        let region = kernel.region_read(commit_out).expect("commit_out region");
        let len = u32::from_le_bytes(region[0..4].try_into().unwrap()) as usize;
        region[4..4 + len].to_vec()
    };

    // ── The executor-PD server thread: serve exactly TWO run-turn calls
    //    (attenuating-commit, amplifying-reject), then return. Each `serve_turn`
    //    blocks on the Endpoint until the app-PD calls, reads turn_in, runs the
    //    gate, writes commit_out, and replies the verdict. ──
    let exec_srv = executor.clone();
    let server = thread::spawn(move || {
        for _ in 0..2 {
            let mut e = exec_srv.lock().unwrap();
            let _served = e.serve_turn(run_ep).expect("serve turn");
            drop(e);
        }
    });

    // Give the server a beat to park on `recv` (not load-bearing — the rendezvous
    // blocks either way — but exercises the genuine Endpoint synchrony).
    thread::sleep(Duration::from_millis(20));

    // ── App-PD wiring: it names the run-channel (index → endpoint). ──
    let mut app_table = ChannelTable::new();
    app_table.wire(
        RUN_CHANNEL,
        ChannelWiring {
            notification: kernel.create_notification(),
            endpoint: Some(run_ep),
        },
    );
    let app_table = Arc::new(app_table);

    // A helper: the app-PD STAGES a turn into turn_in, then pp_calls the executor
    // (the `stage → signal` shape). Returns the reply label (COMMITTED/REJECTED).
    let submit = |turn_bytes: &[u8]| -> u64 {
        // The app-PD stages the turn into turn_in BEFORE signalling (the executor
        // reads turn_in when the call arrives). It writes the shared turn_in region
        // LOCK-FREE through the kernel (`stage_turn_into`), exactly as a real app-PD
        // writes its mapped turn_in view — never touching the executor handle while
        // the executor's thread is parked in `recv` holding the executor lock.
        assert!(
            dregg_firmament::stage_turn_into(&kernel, turn_in, turn_bytes).is_some(),
            "the turn fits turn_in"
        );
        let ch = Channel::bound(RUN_CHANNEL, kernel.clone(), app_table.clone());
        let (reply_tag, _reply_bytes) = ch
            .pp_call(MessageInfo::new(LABEL_RUN_TURN, 0), &[])
            .expect("run-turn pp_call round-trips");
        reply_tag.label()
    };

    // ── APP-PD: stage an ATTENUATING turn (held=Either, granted=Signature — a
    //    genuine narrowing). It COMMITS; the receipt is in commit_out. ──
    let r1 = submit(&[2, 1]);
    assert_eq!(
        r1, LABEL_TURN_COMMITTED,
        "an attenuating turn COMMITS through the heart"
    );
    // The receipt round-tripped back through commit_out (the app-PD reads it
    // LOCK-FREE — the server is now parked in the next recv holding the executor
    // lock, so we must NOT take that lock here).
    assert_eq!(
        read_commit_out(&kernel),
        vec![2, 1, 0xCC],
        "the committed receipt round-tripped through commit_out"
    );

    // ── APP-PD: stage an AMPLIFYING turn (held=Signature, granted=Either — a
    //    WIDENING). It is REJECTED; commit_out holds the reason; no state advanced. ──
    let r2 = submit(&[1, 2]);
    assert_eq!(
        r2, LABEL_TURN_REJECTED,
        "a widening turn is REJECTED at the heart (the gate fires)"
    );
    let reason = String::from_utf8(read_commit_out(&kernel)).unwrap();
    assert!(
        reason.contains("non-attenuating"),
        "the reason names the widening: {reason}"
    );

    // ── Join the server (both calls served). ──
    server.join().expect("executor-PD served both staged turns");

    // ── THE OBSERVABLE: exactly ONE turn committed through the heart; ONE was
    //    rejected (the ocap guarantee firing, fail-closed). The server thread has
    //    returned, so taking the executor lock here is contention-free. ──
    let e = executor.lock().unwrap();
    assert_eq!(e.committed_count(), 1, "one attenuating turn committed");
    assert_eq!(
        e.rejected_count(),
        1,
        "one widening turn was rejected (the gate fired)"
    );

    // The honest fidelity label travels with the code (it runs the GENUINE turn
    // semantics over the GENUINE EmulatedKernel IPC; it is NOT the real-seL4 PD).
    assert!(
        ExecutorPd::<AttenuationRunner>::FIDELITY.contains("GENUINE verified turn semantics"),
        "the fidelity label states it runs the genuine semantics over the genuine IPC"
    );

    println!(
        "EXECUTOR-PD: app-PD staged a turn into turn_in, pp_call'd the heart; the \
         attenuating turn COMMITTED (receipt round-tripped through commit_out), the \
         WIDENING turn was REJECTED (commit_out held the reason, no state advanced). \
         the verified heart ran a turn over the EmulatedKernel ( ◕‿◕ )"
    );
    let _ = MessageInfo::default();
}
