//! lean_state_producer_sidetable.rs — DISSOLVED-VERB WIRE REFUSAL: the factory-dissolved
//! holding-store verbs (`cesc`/`cobl` — the old escrow/obligation kernel ops) are gone from the
//! verified kernel (F1b deleted `RecordKernelState.escrows`; their semantics live in factory-born
//! cells, `Dregg2/Apps/{EscrowFactory,ObligationFactory}`). The kernel no longer PARSES those wire
//! actions — so a STALE OR MALICIOUS PEER whose bytes still carry one must be refused LOUDLY at
//! the wire (`committed == false` or the strict-parser sentinel), NEVER silently skipped-and-committed
//! (a silent accept would install a post-state the sender never authorized — parse-confusion).
//!
//! SUBSTRATE: the decider here is the VERIFIED LEAN kernel — `Dregg2.Exec.FFI.execFullForestAuthStep`
//! (`@[export] dregg_exec_full_forest_auth`), reached through `shadow_exec_full_forest_auth`. This
//! file is Rust HARNESS only: it builds a wire, mutates one tag, and reads the verdict. No admission
//! or parse logic is authored here.
//!
//! # Mechanism, and the ONE non-vacuity obligation
//!
//! A refusal tooth is worthless against a baseline that was already refusing. So each refusal test
//! FIRST asserts, IN THE SAME PROCESS, that the honest wire is ADMITTED and COMMITS
//! (`status == BodyCommitted`, `reason == Admitted`), then swaps its `{"bal":[...]}` action tag for
//! a dissolved (`cesc`/`cobl`) or unknown (`zzzz`) tag and asserts the verified kernel refuses the
//! mutant — and refuses it for the RIGHT reason (the strict `parseWWire` fails ⇒ the empty-state
//! malformed-wire sentinel), not for some unrelated error that merely happens to be an `Err`.
//!
//! # ⚠ WHY THE FIXTURE IS BUILT HERE AND NOT SCAVENGED FROM THE CONFORMANCE CORPUS
//!
//! This tooth previously took its baseline from `dregg_lean_ffi::marshal::conformance_input_corpus()`
//! by scanning for a case that both carried a `bal` action and committed. **No such case has ever
//! existed.** That corpus is the MARSHALLING translation-validation corpus: its only obligation is
//! that `marshal_turn_hosted` reproduces the Lean-emitted golden BYTE-FOR-BYTE
//! (`dregg-lean-ffi/src/marshal_conformance.rs`, which additionally asserts the Rust and Lean case
//! NAMES are set-equal). It is deliberately full of shapes chosen to exercise the ENCODER — negative
//! amounts, absent agents, escaped field names — and its envelope builder `conf_turn_of` has carried
//! `prev = 0xDEADBEEF` against a `stored_head = 0` host since the corpus was born (`c6c3eb2e9`,
//! 2026-06-13), which is a `ChainHeadMismatch` at admission. Measured 2026-07-29: all 49 corpus cases
//! are REJECTED — 44 `NonceMismatch`, 3 `Underfunded`, 1 `ChainHeadMismatch`, 1 `NoSuchAgent`; not one
//! reaches a body. Adding a committing case to that corpus is also not the fix: it would break the
//! byte-for-byte golden join until `metatheory/EmitMarshalGolden.lean` is re-emitted, and it would
//! make an encoder corpus answer a semantics question. So the semantic fixture lives HERE, explicitly.
//!
//! HISTORY. `5fe426a0d` (2026-07-16) rewrote this file from a zero-test husk into the real tooth, and
//! its own commit message records `⚠ RUNTIME-VERIFICATION PENDING for this one file — the lane hit
//! disk ENOSPC then a build-lock queue and could not run it in-session`. The "find a committing corpus
//! case" premise was never executed, so all four tests have been RED since the day they were written,
//! and the panic message they carried ("the corpus lost its committing Balance case") was that lane's
//! own unverified guess — later inherited by two more lanes as if it were a diagnosis. The corpus lost
//! nothing.
//!
//! Requires the linked Lean archive; self-skips unarmed and PANICS under
//! `DREGG_TEST_REQUIRE_LEAN=1` (`demand_lean`) when the archive is absent.

use dregg_lean_ffi::marshal::{
    Digest, WForest, WireAction, WireAuth, WireCaveat, WireHostCtx, WireState, WireTurn, WireValue,
    marshal_turn_hosted,
};
use dregg_lean_ffi::{
    AdmissionReason, TurnStatus, decode_shadow_verdict, demand_lean, lean_available,
    shadow_exec_full_forest_auth,
};

fn skip_no_lean() -> bool {
    // Routed through the DREGG_TEST_REQUIRE_LEAN hard mode (dregg-lean-ffi::demand_lean):
    // unarmed, an archive-less build prints the honest SKIP and returns; ARMED, it PANICS —
    // so this suite can never report `ok` having asserted nothing on the hard-mode lane.
    !demand_lean(lean_available(), "Lean archive (lean_available)")
}

/// The HONEST baseline wire: a turn the verified kernel ADMITS and COMMITS, carrying exactly one
/// `{"bal":[...]}` action for the mutation to target.
///
/// Every field is chosen against a named admission gate (`Dregg2.Exec.Admission.admissible`), so a
/// future gate change fails LOUDLY here (via [`assert_baseline_commits`]) rather than turning the
/// refusal teeth vacuous in silence:
///   * agent `0` is present and Live            → `NoSuchAgent` / `DeadAgent` pass;
///   * turn nonce `7` == cell 0's `nonce` field  → `NonceMismatch` passes;
///   * fee `5` ≤ cell 0's `balance` 100          → `NegativeFee` / `Underfunded` pass;
///   * `valid_until` 1000 ≥ host `now` 0         → `Expired` passes;
///   * host `frozen` is empty                    → `AgentFrozen` / `WriteSetFrozen` pass;
///   * `prev = 0` == host `stored_head = 0`      → `ChainHeadMismatch` passes (`prevReceiptOf 0 = none`,
///                                                 `Dregg2/Exec/AdmissionWire.lean:98`);
///   * fee `5` ≤ host `budget`                   → `OverBudget` passes;
/// and the BODY commits: a signature credential over a src≠dst move of 30 out of cell 0's 100 in
/// asset 0, under a tier-0 (monotone) `min = 0` caveat that 70 still satisfies.
fn honest_committing_wire() -> String {
    let host = WireHostCtx::diag();
    let state = WireState {
        cells: vec![
            (
                0,
                WireValue::Record(vec![
                    ("balance".into(), WireValue::int(100)),
                    ("nonce".into(), WireValue::int(7)),
                ]),
            ),
            (
                1,
                WireValue::Record(vec![("balance".into(), WireValue::int(5))]),
            ),
        ],
        bal: vec![(0, 0, 100), (1, 0, 5)],
        ..Default::default()
    };
    let turn = WireTurn {
        agent: 0,
        nonce: 7,
        fee: 5,
        valid_until: 1000,
        block_height: 0,
        prev_hash: Digest::from_u64(0),
        root: WForest {
            auth: WireAuth::Signature {
                pubkey: Digest::from_u64(7),
                sig: 7,
            },
            caveats: vec![WireCaveat {
                tier: 0,
                cell: 0,
                asset: 0,
                min: 0,
            }],
            action: WireAction::Balance {
                actor: 0,
                src: 0,
                dst: 1,
                amt: 30,
                asset: 0,
            },
            children: vec![],
        },
    };
    let wire = marshal_turn_hosted(&host, &state, &turn).expect("the baseline fixture marshals");
    assert!(
        wire.contains("{\"bal\":["),
        "the baseline fixture must carry the `bal` tag the mutation targets — got {wire}"
    );
    wire
}

/// THE NON-VACUITY FLOOR, asserted inside every refusal test so it holds in the SAME process as the
/// refusal it licenses: the unmutated wire is ADMITTED (`reason == Admitted` — no gate refused it)
/// AND its BODY COMMITS (`status == BodyCommitted`, not the prologue-only anti-spam charge).
fn assert_baseline_commits(wire: &str) {
    let out = shadow_exec_full_forest_auth(wire).expect("the verified kernel runs the honest wire");
    let v = decode_shadow_verdict(&out).expect("the honest wire yields a decodable verdict");
    assert_eq!(
        v.reason,
        Some(AdmissionReason::Admitted),
        "the baseline fixture must pass EVERY admission gate — a refusal here makes the dissolved-verb \
         teeth vacuous (they would be refusing an already-refused turn). Fix the fixture."
    );
    assert_eq!(
        v.status,
        Some(TurnStatus::BodyCommitted),
        "the baseline fixture's BODY must commit — a prologue-only result is a REJECTED turn and \
         would make the dissolved-verb teeth vacuous. Fix the fixture."
    );
    assert!(v.committed, "BodyCommitted implies the commit bit");
}

/// The tooth: swapping the committing wire's `bal` tag for `verb` must flip the kernel from COMMIT
/// to a LOUD refusal — never a silent skip-and-commit.
///
/// The refusal is classified, because "an `Err` came back" is not evidence the check bit. Exactly two
/// outcomes are accepted:
///   * `Ok(verdict)` with `committed == false` — the kernel parsed the mutant and refused it;
///   * the strict-parser refusal — `parseWWire` has no arm for the tag, so `execFullForestAuthStep`
///     returns the empty-state malformed-wire sentinel, which `unmarshal_result` reports as
///     `MalformedWireSentinel`. This is the DESIGNED fail-closed path for an unknown tag.
/// Any other `Err` (FFI init failure, an output-envelope parse error, …) FAILS the test: it would
/// mean the process never reached the verb check and the tooth would be reading an unrelated fault
/// as if the refusal had bitten.
fn dissolved_verb_refuses(verb: &str) {
    if skip_no_lean() {
        return;
    }
    let wire = honest_committing_wire();
    // POLE 1 (same process): the honest turn is ADMITTED and COMMITS.
    assert_baseline_commits(&wire);

    // POLE 2: the ONE-TAG mutant must not.
    let mutant = wire.replacen("{\"bal\":[", &format!("{{\"{verb}\":["), 1);
    assert_ne!(wire, mutant, "mutation must change the wire");

    let out = match shadow_exec_full_forest_auth(&mutant) {
        Ok(out) => out,
        Err(e) => panic!(
            "the FFI itself failed on the `{verb}` mutant ({e}) — this tooth cannot tell a verb \
             refusal from a broken harness, so it refuses to call this a pass"
        ),
    };
    match decode_shadow_verdict(&out) {
        Ok(v) => assert!(
            !v.committed,
            "SILENT STATE INSTALL: the verified kernel COMMITTED a turn whose action carried the \
             dissolved/unknown wire verb `{verb}` — stale-peer bytes must refuse loudly, not be \
             skipped-and-committed (parse-confusion). status={:?} reason={:?}",
            v.status, v.reason
        ),
        Err(e) => assert!(
            e.contains("malformed-wire sentinel"),
            "the `{verb}` mutant was refused, but NOT by the strict wire parser — the refusal this \
             tooth licenses is the fail-closed unknown-tag path (the empty-state sentinel), and an \
             unrelated decode failure must not be read as the check biting. got: {e}"
        ),
    }
}

/// `cesc` — the dissolved CreateEscrow kernel verb (F1b): stale peer bytes must refuse.
#[test]
fn dissolved_escrow_wire_verb_refuses_loudly() {
    dissolved_verb_refuses("cesc");
}

/// `cobl` — the dissolved CreateObligation kernel verb (F1b): stale peer bytes must refuse.
#[test]
fn dissolved_obligation_wire_verb_refuses_loudly() {
    dissolved_verb_refuses("cobl");
}

/// The general pole: a verb the kernel NEVER knew must refuse the same way (pins unknown-tag
/// handling as fail-closed, so a future "skip unknown actions" convenience can't slip in).
#[test]
fn unknown_wire_verb_never_silently_commits() {
    dissolved_verb_refuses("zzzz");
}

/// The non-vacuity floor as its own named test, so a fixture that stops committing reports itself
/// directly instead of only as a confusing failure inside the three refusal teeth.
#[test]
fn baseline_bal_wire_commits() {
    if skip_no_lean() {
        return;
    }
    assert_baseline_commits(&honest_committing_wire());
}
