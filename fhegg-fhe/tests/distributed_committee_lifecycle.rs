#![cfg(any(target_os = "linux", target_os = "macos"))]

//! **WHAT A DISTRIBUTED COMMITTEE COSTS, MEASURED — and the two poles of its lifecycle.**
//!
//! The committee's price has always been quoted from a round formula. A formula is a
//! derivation about the protocol; it is not a statement about a deployment, and nobody
//! had ever put a stopwatch on one. This file does, through
//! [`fhegg_fhe::threshold::supervisor`] — the object a production caller holds — so the
//! numbers are of the thing that would actually run, not of a bench harness beside it.
//!
//! Every number printed here is wall-clock on the machine that ran it, over real OS
//! processes and real TCP. Re-measure anywhere the answer matters.
//!
//! # The two poles
//!
//! * **A clearing completes.** [`a_dark_clearing_completes_across_the_distributed_committee`]
//!   runs the custody half of a dark clearing end to end over real processes: traders
//!   encrypt to a collective key whose secret exists nowhere as a whole, the ciphertexts
//!   are folded homomorphically with no secret involved, and only the aggregate is opened
//!   — by `t` parties, each carrying a zero-knowledge decrypt-share certificate produced
//!   in its own process. The per-order values are never opened by anything.
//! * **It fails cleanly and names the real cause.** [`a_roster_short_of_t_is_refused_before_a_byte_moves`]
//!   and [`a_lying_dealer_ends_the_committee_and_the_supervisor_names_the_refusal`]. The
//!   second is the one worth reading: before the supervisor, a party that refused a
//!   corrupted row died with its reason in a pipe nobody drained, and the caller saw a
//!   setup timeout minutes later. Now the caller gets
//!   `VssCommitmentMismatch { dealer: 0, recipient: 1 }`.
//!
//! # Honest scope
//!
//! What is measured is the COMMITTEE: DKG, key agreement, the verified commit round, the
//! certified `t`-of-`n` opening, and the distributed relinearization ceremony. A full node
//! clearing additionally runs a masked boundary and an MPC crossing, and those parties are
//! still co-located in the node — not measured here and not claimed.
//!
//! The parties are separate PROCESSES on ONE host. That is a weaker adversary model than
//! `n` independently-operated hosts and it is named rather than glossed: what survives is
//! everything the protocol enforces, what does not is an adversary who owns the host.

use std::time::{Duration, Instant};

use fhe_traits::Serialize as FheSerialize;
use fhegg_fhe::threshold::supervisor::{
    CommitteeSpec, CommitteeSupervisor, LiveCommittee, PartyLaunch, SupervisorError,
};
use fhegg_fhe::threshold::BfvParams;

/// A trader's order quantity. Small on purpose: the family this mirrors is 4-bit.
const ORDER_QUANTITIES: [u64; 4] = [3, 11, 6, 9];
const PLAIN_BOUND: u64 = 4_096;

fn launch() -> PartyLaunch {
    PartyLaunch::new(env!("CARGO_BIN_EXE_threshold-committee-party"))
}

/// Install the Lean-verified PQ cores. The supervisor REFUSES without them rather than
/// letting `dregg-pq` abort the process mid-ceremony, so this is also what makes that
/// refusal not fire.
fn install_cores() {
    assert!(
        std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none(),
        "this test must not run under the unaudited-PQ opt-in"
    );
    dregg_pq_testkit::install_or_panic();
}

fn spec(label: &str, n: usize, t: usize) -> CommitteeSpec {
    let mut spec = CommitteeSpec::ephemeral(label, n, t, BfvParams::fold_set());
    spec.setup_timeout = Duration::from_secs(900);
    spec
}

/// Print one committee's stand-up cost. This is the answer to "what does a distributed
/// committee cost", and it is printed rather than asserted because a wall-clock is a
/// measurement, not a contract — asserting it would be pinning one machine's load.
fn report_stand_up(label: &str, committee: &LiveCommittee) {
    let phases = committee.phases();
    let wire = committee.wire_cost();
    println!(
        "\n── {label}: {}-of-{} committee, degree {}, pids {:?}\n\
            enrol           {:>10.3?}\n\
            spawn           {:>10.3?}\n\
            DKG (n procs)   {:>10.3?}\n\
            key agreement   {:>10.3?}\n\
            commit round    {:>10.3?}\n\
            ── stand-up     {:>10.3?}   [{wire}]",
        committee.threshold(),
        committee.n_parties(),
        committee.params().degree(),
        committee.party_pids(),
        phases.enroll,
        phases.spawn,
        phases.dkg,
        phases.key_agreement,
        phases.commit_round,
        phases.total(),
    );
}

/// **POLE ONE: A DARK CLEARING COMPLETES ACROSS THE DISTRIBUTED COMMITTEE.**
///
/// Four traders encrypt their own quantities under the collective public key. The
/// ciphertexts are folded homomorphically — no secret, no quorum, nothing decrypted. Then
/// the AGGREGATE alone is opened by `t` party processes, each producing a certificate the
/// combiner verifies against the committee's transcript before it will combine at all.
///
/// The individual quantities are never opened by anything in this test, and no process in
/// the system holds more than one custody share.
///
/// This also carries the MEASUREMENT: stand-up phases, and the marginal cost of one
/// opening, priced in wall-clock and in round-trips and bytes that were counted on the
/// socket rather than derived from a formula.
#[test]
#[ignore = "three party processes at degree 4096 with a real ZK decrypt-share certificate: minutes. \
            Run with --release --ignored --nocapture (the numbers are the point)."]
fn a_dark_clearing_completes_across_the_distributed_committee() {
    install_cores();
    let committee = CommitteeSupervisor::spawn_local(spec("clearing", 3, 2), &launch())
        .expect("a 2-of-3 committee must stand up across three processes");
    report_stand_up("dark clearing", &committee);

    assert_eq!(
        committee.party_pids().len(),
        3,
        "three party processes must have been supervised"
    );
    assert!(
        !committee.party_pids().contains(&std::process::id()),
        "a party is running inside the relying party's own process"
    );

    // ── ENCRYPT. Each trader does this in its own right: no secret, no quorum.
    let started = Instant::now();
    let orders = ORDER_QUANTITIES
        .iter()
        .map(|&q| committee.encrypt(q).expect("encrypt to the collective key"))
        .collect::<Vec<_>>();
    let encrypt = started.elapsed();

    // ── FOLD. Homomorphic addition of the ciphertexts. Nothing is decrypted, and the
    // relying party holds no share, so this reveals nothing to anybody.
    let started = Instant::now();
    let mut folded = fhe::bfv::Ciphertext::zero(committee.params().arc());
    for order in &orders {
        folded += order;
    }
    let fold = started.elapsed();

    // ── OPEN THE AGGREGATE ONLY, at t, certificate-checked, across processes.
    let before = committee.wire_cost();
    let started = Instant::now();
    let total = committee
        .open(&folded, PLAIN_BOUND, [0x5c; 32])
        .expect("t certificate-carrying shares must open the folded aggregate");
    let open = started.elapsed();
    let open_wire = committee.wire_cost().since(before);

    let expected: u64 = ORDER_QUANTITIES.iter().sum();
    assert_eq!(
        total, expected,
        "the distributed committee did not reproduce the folded aggregate"
    );

    // A SECOND opening, so the marginal cost is a measurement rather than an
    // extrapolation from one sample that includes any first-call warmth.
    let before = committee.wire_cost();
    let started = Instant::now();
    let again = committee
        .open(&folded, PLAIN_BOUND, [0x5d; 32])
        .expect("a second opening under a fresh nonce");
    let open_again = started.elapsed();
    let open_again_wire = committee.wire_cost().since(before);
    assert_eq!(
        again, expected,
        "the second opening disagreed with the first"
    );

    println!(
        "   encrypt x{}    {:>10.3?}\n\
         \x20  fold x{}       {:>10.3?}\n\
         \x20  OPEN #1 (t={}) {:>10.3?}   [{open_wire}]\n\
         \x20  OPEN #2 (t={}) {:>10.3?}   [{open_again_wire}]\n\
         \x20  cleared total = {total} (expected {expected}); per-order values never opened",
        ORDER_QUANTITIES.len(),
        encrypt,
        // The fold starts from a zero ciphertext, so it is one add PER ORDER — not
        // `len() - 1`. A measurement labelled with the wrong operation count is a
        // wrong measurement, however small.
        ORDER_QUANTITIES.len(),
        fold,
        committee.threshold(),
        open,
        committee.threshold(),
        open_again,
    );

    committee.shutdown();
}

/// **THE RELINEARIZATION CEREMONY, PRICED.**
///
/// Separated from the clearing because it is a different liveness requirement (`n`-of-`n`
/// over the dealers, so nothing may be offline) and a different order of cost. Quoting it
/// inside a "clearing latency" would be quoting the wrong number for both.
///
/// **`trials` IS A FLOOR, NOT A REQUEST.** `relin_acceptance_gate` does
/// `let trials = trials.max(8)`, so every caller pays for **8** full certified `t`-of-`n`
/// openings whatever it asked for — the two other call sites in this tree pass `1` and `2`
/// and a reader would reasonably believe those are what run. `8` is passed here so the
/// argument in this test and the work it buys are the same number. That is where this
/// measurement's cost lives: eight ZK decrypt-share certificates at degree 4096, and the
/// ceremony itself is the smaller half.
const RELIN_GATE_TRIALS: usize = 8;

#[test]
#[ignore = "the n-of-n relin ceremony plus an acceptance gate that runs EIGHT certified \
            t-of-n openings: tens of minutes. Run with --release --ignored --nocapture."]
fn the_distributed_relinearization_ceremony_priced() {
    install_cores();
    let committee = CommitteeSupervisor::spawn_local(spec("relin", 3, 2), &launch())
        .expect("a 2-of-3 committee must stand up");
    report_stand_up("relin ceremony", &committee);

    let before = committee.wire_cost();
    let started = Instant::now();
    let _key = committee
        .relin_key([0x5c; 32], Duration::from_secs(1_800), RELIN_GATE_TRIALS)
        .expect("the distributed relin ceremony must produce a gated key");
    let ceremony = started.elapsed();
    let wire = committee.wire_cost().since(before);

    // Cached: a second call must not re-run a ceremony that is a pure function of the
    // committee and the public entropy.
    let started = Instant::now();
    let _cached = committee
        .relin_key([0x5c; 32], Duration::from_secs(1_800), RELIN_GATE_TRIALS)
        .expect("cached relin key");
    let cached = started.elapsed();

    println!(
        "   RELIN + {RELIN_GATE_TRIALS}-trial gate  {:>10.3?}   [{wire}]\n\
         \x20  cached                    {:>10.3?}",
        ceremony, cached
    );
    assert!(
        cached * 100 < ceremony,
        "a second relin_key() cost {cached:?} against a {ceremony:?} ceremony — it is being \
         regenerated per call"
    );

    committee.shutdown();
}

/// **HOW THE COST SCALES WITH THE ROSTER — and what the NODE's shape costs.**
///
/// The commit response grows as `O(n^2 * degree)` and is the round that forced chunking,
/// so `n` is where the cost lives, and one measurement at `n = 3` says nothing about
/// `n = 4`.
///
/// `(4, 3)` is not an arbitrary second point. It is EXACTLY the live production caller's
/// shape: `node/src/dark_clearing_service.rs` runs `OPENING_THRESHOLD = 3` of
/// `KEY_CUSTODIANS = 4`, in-process, and stands a fresh DKG up inside every
/// `open_session` — which is an HTTP request handler. What this row costs is therefore
/// the direct answer to "can that surface stand a distributed committee up per session",
/// and it should be read as such rather than as a benchmark.
#[test]
#[ignore = "two full committees (3 and 4 processes) at degree 4096: many minutes. \
            Run with --release --ignored --nocapture."]
fn the_stand_up_cost_measured_against_the_roster() {
    install_cores();
    for (n, t) in [(3usize, 2usize), (4, 3)] {
        let committee = CommitteeSupervisor::spawn_local(spec("scale", n, t), &launch())
            .unwrap_or_else(|error| panic!("a {t}-of-{n} committee must stand up: {error}"));
        report_stand_up(&format!("roster n={n} t={t}"), &committee);

        // One certified opening at this roster size, so the OPENING cost is measured
        // against `t` too and not only the stand-up.
        let ciphertext = committee.encrypt(1_234).expect("encrypt");
        let before = committee.wire_cost();
        let started = Instant::now();
        let opened = committee
            .open(&ciphertext, PLAIN_BOUND, [0x11; 32])
            .expect("certified opening");
        println!(
            "   OPEN (t={t})       {:>10.3?}   [{}]",
            started.elapsed(),
            committee.wire_cost().since(before)
        );
        assert_eq!(opened, 1_234);
        committee.shutdown();
    }
}

/// **POLE TWO (a): A ROSTER SHORT OF `t` IS REFUSED BEFORE A BYTE MOVES.**
///
/// The refusal names the shortfall and the threshold. That matters more than it looks: a
/// caller that learns "your committee is unavailable" from a combiner arity error three
/// round-trips later has already leaked the request to the parties it did reach, and has
/// no way to tell an unavailable committee from a malformed ciphertext.
///
/// Cheap — no ciphertext is ever sent — so it is NOT `#[ignore]`d. It stands a real
/// committee up, which is the only part that costs.
#[test]
#[ignore = "stands a real 2-of-3 committee up (a real DKG at degree 4096): minutes. \
            Run with --release --ignored."]
fn a_roster_short_of_t_is_refused_before_a_byte_moves() {
    install_cores();
    let committee = CommitteeSupervisor::spawn_local(spec("short", 3, 2), &launch())
        .expect("a 2-of-3 committee must stand up");

    let ciphertext = committee.encrypt(7).expect("encrypt");
    let bytes = ciphertext.to_bytes();

    // Nothing is sent, so the wire cost must not move. Asserting that is what
    // distinguishes "refused early" from "refused eventually".
    let before = committee.wire_cost();
    let one_party = committee.open_slots(&bytes, PLAIN_BOUND, &[0], [0x01; 32]);
    let after = committee.wire_cost();
    match one_party {
        Err(SupervisorError::Roster(why)) => {
            assert!(
                why.contains("below the 2-of-3 opening threshold"),
                "the refusal did not name the real cause: {why}"
            );
        }
        other => panic!("a 1-party roster must be refused by the roster check, got {other:?}"),
    }
    assert_eq!(
        after, before,
        "a below-threshold opening put bytes on the wire before refusing"
    );

    // An empty roster, a duplicated party, and an out-of-range party are each their own
    // misconfiguration and each says which.
    assert!(matches!(
        committee.open_slots(&bytes, PLAIN_BOUND, &[], [0x02; 32]),
        Err(SupervisorError::Roster(_))
    ));
    match committee.open_slots(&bytes, PLAIN_BOUND, &[0, 0], [0x03; 32]) {
        Err(SupervisorError::Roster(why)) => assert!(
            why.contains("twice"),
            "a duplicated party must be named as one: {why}"
        ),
        other => panic!("a duplicated roster must be refused, got {other:?}"),
    }
    match committee.open_slots(&bytes, PLAIN_BOUND, &[0, 9], [0x04; 32]) {
        Err(SupervisorError::Roster(why)) => assert!(
            why.contains("party 9"),
            "an out-of-range party must be named: {why}"
        ),
        other => panic!("an out-of-range roster must be refused, got {other:?}"),
    }
    // An out-of-order roster is a WRONG opening, not an invalid one — the Lagrange
    // coefficients follow the order — so it must be refused rather than silently
    // producing a garbage plaintext.
    match committee.open_slots(&bytes, PLAIN_BOUND, &[1, 0], [0x06; 32]) {
        Err(SupervisorError::Roster(why)) => assert!(
            why.contains("increasing order"),
            "an out-of-order roster must be named as one: {why}"
        ),
        other => panic!("an out-of-order roster must be refused, got {other:?}"),
    }

    // And the same committee still opens at exactly `t`, so the refusals above are the
    // roster check and not a broken committee.
    assert_eq!(
        committee
            .open_slots(&bytes, PLAIN_BOUND, &[0, 1], [0x05; 32])
            .expect("t parties open")
            .first()
            .copied(),
        Some(7)
    );

    committee.shutdown();
}

/// **POLE TWO (b): A LYING DEALER ENDS THE COMMITTEE, AND THE CALLER IS TOLD WHY.**
///
/// Party 0 commits to an honest row and deals a CORRUPTED one to party 1. Party 1 refuses
/// it and exits. What is under test here is not the refusal — that is
/// `distributed_threshold_committee.rs`'s — but what the CALLER learns.
///
/// Before the supervisor, the answer was: nothing useful. The dead party's reason went to
/// a stderr pipe nobody drained, and a caller waiting on custody saw a setup timeout up to
/// `setup_timeout` later with no cause attached. That is the failure this pole exists to
/// close: the supervisor must fail the moment the party dies, and must hand back the
/// refusal the party named.
///
/// **DEBUG BUILDS ONLY, and that is a property of the ADVERSARY.** The corrupting path is
/// `#[cfg(not(debug_assertions))] -> None` in the party binary — compiled out of release
/// on purpose. A release run would spawn an honest dealer, nothing would be refused, and
/// this test would fail for a reason that says nothing about the refusal it is named for.
/// Gating it to match its adversary is the honest shape; the alternative is a guaranteed
/// red that cannot distinguish a working supervisor from a broken one.
#[cfg(debug_assertions)]
#[test]
#[ignore = "spawns three party processes and runs a real DKG until one refuses: minutes. \
            Run with --ignored (DEBUG — the adversary is compiled out of release)."]
fn a_lying_dealer_ends_the_committee_and_the_supervisor_names_the_refusal() {
    install_cores();
    let launch = launch().with_party_env(0, "FHEGG_COMMITTEE_TAMPER_ROW", "1");

    let started = Instant::now();
    let outcome = CommitteeSupervisor::spawn_local(spec("lying-dealer", 3, 2), &launch);
    let elapsed = started.elapsed();

    let error = match outcome {
        Ok(_) => panic!(
            "the committee came up with a dealer that corrupted a row — the endorsement seam is \
             not holding"
        ),
        Err(error) => error,
    };

    // THE CLAIM IS THE CAUSE, NOT THE STATUS. An exit code alone would have passed a
    // party that died of anything at all.
    match &error {
        SupervisorError::PartyDied {
            party,
            refusal,
            stderr_tail,
            ..
        } => {
            assert_eq!(*party, 1, "the wrong party died");
            let refusal = refusal
                .as_deref()
                .unwrap_or_else(|| panic!("no refusal captured; stderr tail: {stderr_tail:?}"));
            assert!(
                refusal.contains("VssCommitmentMismatch { dealer: 0, recipient: 1 }"),
                "party 1 died, but the supervisor did not surface the dealer-0 commitment \
                 refusal it died of. Captured: {refusal:?}; tail: {stderr_tail:?}"
            );
        }
        other => panic!(
            "a lying dealer must surface as PartyDied with the refusal it named, got: {other}"
        ),
    }

    // FAST, and that is the point of the liveness check. Without it the caller waits the
    // full setup timeout (900s here) to learn nothing.
    assert!(
        elapsed < Duration::from_secs(600),
        "the supervisor waited {elapsed:?} on a party that had already died — it is not \
         failing on the death, it is failing on the deadline"
    );
    println!("\n── lying dealer: refused and surfaced in {elapsed:.3?}\n   {error}");
}

/// A spec that cannot carry the property is refused BEFORE a process is forked — no
/// committee, no ceremony, no cost. Cheap, so it always runs.
#[test]
fn an_unopenable_or_unilateral_spec_is_refused_without_spawning_anything() {
    let unilateral = CommitteeSupervisor::spawn_local(spec("unilateral", 3, 1), &launch());
    assert!(
        matches!(unilateral, Err(SupervisorError::Spec(_))),
        "a 1-of-3 committee lets one party open unilaterally and must be refused"
    );
    let unopenable = CommitteeSupervisor::spawn_local(spec("unopenable", 3, 4), &launch());
    assert!(matches!(unopenable, Err(SupervisorError::Spec(_))));
    let single = CommitteeSupervisor::spawn_local(spec("single", 1, 1), &launch());
    assert!(matches!(single, Err(SupervisorError::Spec(_))));
}
