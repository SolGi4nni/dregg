//! Non-vacuous ledger tests — the load-bearing guarantees, each exercised so it can FAIL.
//!
//! Every test drives the REAL metered path ([`metered_converse`]) with an injected backend, so
//! the ordering (price → reserve → call → true-up) and the fail-closed corners are checked
//! against the actual code, not a mock of it. The two sharpest: an over-cap / unpriced call is
//! refused BEFORE the backend is ever touched (the backend PANICS if reached), and two
//! concurrent invocations serialize on the lock and never sum past the cap.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};

use dregg_narrator::{
    metered_converse, BudgetLedger, ConverseBackend, ConverseRequest, ConverseResponse,
    ModelRegistry, Narrator, NarratorError, PriceSource, CLAUDE_HAIKU_4_5, NOVA_2_LITE,
};

// ── test backends ──────────────────────────────────────────────────────────────────────────

/// A backend that returns canned token usage. Records how many times it was called.
struct FakeBackend {
    input_tokens: u32,
    output_tokens: u32,
    calls: Arc<AtomicUsize>,
    delay_ms: u64,
}

impl FakeBackend {
    fn new(input_tokens: u32, output_tokens: u32) -> (Arc<Self>, Arc<AtomicUsize>) {
        let calls = Arc::new(AtomicUsize::new(0));
        (
            Arc::new(FakeBackend {
                input_tokens,
                output_tokens,
                calls: calls.clone(),
                delay_ms: 0,
            }),
            calls,
        )
    }
    fn slow(input_tokens: u32, output_tokens: u32, delay_ms: u64) -> Arc<Self> {
        Arc::new(FakeBackend {
            input_tokens,
            output_tokens,
            calls: Arc::new(AtomicUsize::new(0)),
            delay_ms,
        })
    }
}

impl ConverseBackend for FakeBackend {
    fn converse(&self, _req: &ConverseRequest) -> Result<ConverseResponse, String> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        if self.delay_ms > 0 {
            std::thread::sleep(std::time::Duration::from_millis(self.delay_ms));
        }
        Ok(ConverseResponse {
            text: "a torch gutters against wet stone".to_string(),
            tool_calls: Vec::new(),
            stop_reason: "end_turn".to_string(),
            input_tokens: self.input_tokens,
            output_tokens: self.output_tokens,
            attestation: None,
        })
    }
}

/// A backend that PANICS if it is ever called — proves a refusal happened BEFORE the network.
struct PanicBackend;
impl ConverseBackend for PanicBackend {
    fn converse(&self, _req: &ConverseRequest) -> Result<ConverseResponse, String> {
        panic!("the backend was called — the pre-flight refusal did NOT short-circuit!");
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────────────────────

fn ledger_at(dir: &std::path::Path, cap: f64) -> BudgetLedger {
    BudgetLedger::new(dir.join("ledger.json"), cap)
}

fn req(model: &str, max_tokens: u32) -> ConverseRequest {
    ConverseRequest::plain(
        model,
        "you are a dungeon master",
        "narrate the ashen antechamber",
        max_tokens,
    )
}

const EPS: f64 = 1e-9;

// ── the tests ──────────────────────────────────────────────────────────────────────────────

#[test]
fn below_cap_call_allowed_and_trues_up_to_exact_usage() {
    let tmp = tempfile::tempdir().unwrap();
    let ledger = ledger_at(tmp.path(), 20.00);
    let registry = ModelRegistry::builtin();
    let (backend, calls) = FakeBackend::new(61, 43);

    let resp =
        metered_converse(&ledger, &registry, backend.as_ref(), &req(NOVA_2_LITE, 256)).unwrap();
    assert_eq!(resp.input_tokens, 61);
    assert_eq!(
        calls.load(Ordering::SeqCst),
        1,
        "the backend WAS called (a below-cap call)"
    );

    // Nova Lite (verified): 61/1000*0.00006 + 43/1000*0.00024 = 0.00001398.
    let expected = 61.0 / 1000.0 * 0.00006 + 43.0 / 1000.0 * 0.00024;
    let spent = ledger.spent_usd().unwrap();
    assert!(
        (spent - expected).abs() < EPS,
        "spent {spent} != exact usage cost {expected}"
    );

    let snap = ledger.snapshot().unwrap();
    assert_eq!(snap.calls, 1);
    let m = snap.per_model.get(NOVA_2_LITE).unwrap();
    assert_eq!(m.calls, 1);
    assert!(matches!(m.price_source, Some(PriceSource::Verified { .. })));
}

#[test]
fn over_cap_call_is_refused_before_the_network() {
    let tmp = tempfile::tempdir().unwrap();
    // A cap far below even one Haiku reservation (256 out * 0.010/1K = $0.00256) — the very first
    // call must be refused. The injected backend PANICS if the refusal fails to short-circuit.
    let ledger = ledger_at(tmp.path(), 0.0001);
    let registry = ModelRegistry::builtin();

    let err = metered_converse(
        &ledger,
        &registry,
        &PanicBackend,
        &req(CLAUDE_HAIKU_4_5, 256),
    )
    .expect_err("an over-cap call must be refused");
    assert!(
        matches!(err, NarratorError::BudgetExhausted { .. }),
        "expected BudgetExhausted, got {err:?}"
    );
    // No reservation was taken (the refusal preceded it).
    assert_eq!(
        ledger.spent_usd().unwrap(),
        0.0,
        "a refused call spends nothing"
    );
}

#[test]
fn unpriced_model_is_refused_before_the_network() {
    let tmp = tempfile::tempdir().unwrap();
    let ledger = ledger_at(tmp.path(), 20.00);
    let registry = ModelRegistry::builtin(); // does NOT know "mystery-model"

    let err = metered_converse(
        &ledger,
        &registry,
        &PanicBackend,
        &req("mystery-model", 256),
    )
    .expect_err("an unpriced model must be refused");
    assert!(
        matches!(err, NarratorError::UnpricedModel { .. }),
        "expected UnpricedModel, got {err:?}"
    );
    assert_eq!(ledger.spent_usd().unwrap(), 0.0);
}

#[test]
fn true_up_replaces_the_reservation_with_actual() {
    let tmp = tempfile::tempdir().unwrap();
    let ledger = ledger_at(tmp.path(), 20.00);
    let registry = ModelRegistry::builtin();

    // max_tokens=4096 makes the reservation LARGE; the real usage (5 in / 7 out) is tiny.
    let pricing = registry.pricing_for(NOVA_2_LITE).unwrap();
    let request = req(NOVA_2_LITE, 4096);
    let reservation_cost = pricing.reservation_cost(request.prompt_bytes(), 4096);

    let (backend, _calls) = FakeBackend::new(5, 7);
    metered_converse(&ledger, &registry, backend.as_ref(), &request).unwrap();

    let actual = pricing.actual_cost(5, 7);
    let spent = ledger.spent_usd().unwrap();
    assert!(
        reservation_cost > actual * 10.0,
        "the reservation should dwarf the actual"
    );
    assert!(
        (spent - actual).abs() < EPS,
        "after true-up the spend must be the ACTUAL {actual}, not the reservation {reservation_cost}; got {spent}"
    );
}

#[test]
fn concurrent_invocations_serialize_and_never_exceed_cap() {
    let tmp = tempfile::tempdir().unwrap();
    let registry = ModelRegistry::builtin();

    // One reservation (256 out at Haiku $0.010/1K ≈ $0.00256) fits; two do not.
    let probe = ledger_at(tmp.path(), f64::INFINITY);
    let one_res = registry
        .pricing_for(CLAUDE_HAIKU_4_5)
        .unwrap()
        .reservation_cost(req(CLAUDE_HAIKU_4_5, 256).prompt_bytes(), 256);
    let cap = one_res * 1.5; // room for exactly one in-flight reservation
    let _ = probe;

    let ledger = ledger_at(tmp.path(), cap);
    let barrier = Arc::new(Barrier::new(2));
    // A SLOW backend so the first call still holds its reservation when the second reserves.
    let backend = FakeBackend::slow(30, 20, 250);

    let handles: Vec<_> = (0..2)
        .map(|_| {
            let ledger = ledger.clone();
            let registry = registry.clone();
            let barrier = barrier.clone();
            let backend = backend.clone();
            std::thread::spawn(move || {
                barrier.wait();
                metered_converse(
                    &ledger,
                    &registry,
                    backend.as_ref(),
                    &req(CLAUDE_HAIKU_4_5, 256),
                )
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    let ok = results.iter().filter(|r| r.is_ok()).count();
    let exhausted = results
        .iter()
        .filter(|r| matches!(r, Err(NarratorError::BudgetExhausted { .. })))
        .count();
    assert_eq!(
        ok, 1,
        "exactly one concurrent call should land under this cap"
    );
    assert_eq!(exhausted, 1, "the other should be refused BudgetExhausted");

    let spent = ledger.spent_usd().unwrap();
    assert!(
        spent <= cap + EPS,
        "combined spend {spent} must never exceed the cap {cap}"
    );
}

#[test]
fn ledger_persists_and_reloads() {
    let tmp = tempfile::tempdir().unwrap();
    let registry = ModelRegistry::builtin();
    {
        let ledger = ledger_at(tmp.path(), 20.00);
        let (backend, _c) = FakeBackend::new(61, 43);
        metered_converse(&ledger, &registry, backend.as_ref(), &req(NOVA_2_LITE, 256)).unwrap();
    }
    // A FRESH ledger handle over the same file reads the persisted state.
    let reloaded = ledger_at(tmp.path(), 20.00);
    let snap = reloaded.snapshot().unwrap();
    assert_eq!(snap.calls, 1, "the persisted call survived the reload");
    assert!(snap.total_spent_usd > 0.0);
}

#[test]
fn corrupt_ledger_fails_closed_missing_starts_at_zero() {
    let tmp = tempfile::tempdir().unwrap();
    let registry = ModelRegistry::builtin();

    // MISSING → starts at zero and a call is allowed.
    let ledger = BudgetLedger::new(tmp.path().join("fresh.json"), 20.00);
    assert_eq!(
        ledger.spent_usd().unwrap(),
        0.0,
        "a missing ledger starts at $0.00"
    );
    let (backend, _c) = FakeBackend::new(10, 10);
    metered_converse(&ledger, &registry, backend.as_ref(), &req(NOVA_2_LITE, 128)).unwrap();

    // CORRUPT → refuse everything until reset.
    let corrupt_path = tmp.path().join("corrupt.json");
    std::fs::write(&corrupt_path, b"{ this is not valid json ][").unwrap();
    let corrupt = BudgetLedger::new(&corrupt_path, 20.00);
    assert!(matches!(
        corrupt.spent_usd(),
        Err(NarratorError::LedgerCorrupt { .. })
    ));
    let err = metered_converse(&corrupt, &registry, &PanicBackend, &req(NOVA_2_LITE, 128))
        .expect_err("a corrupt ledger refuses all calls");
    assert!(
        matches!(err, NarratorError::LedgerCorrupt { .. }),
        "got {err:?}"
    );

    // Only an EXPLICIT reset clears it (never a silent zero).
    corrupt.reset().unwrap();
    assert_eq!(corrupt.spent_usd().unwrap(), 0.0);
    let (backend, _c) = FakeBackend::new(10, 10);
    metered_converse(
        &corrupt,
        &registry,
        backend.as_ref(),
        &req(NOVA_2_LITE, 128),
    )
    .unwrap();
}

#[test]
fn conservative_upper_bound_source_round_trips_into_the_ledger() {
    let tmp = tempfile::tempdir().unwrap();
    let ledger = ledger_at(tmp.path(), 20.00);
    let registry = ModelRegistry::builtin();

    let (backend, _c) = FakeBackend::new(65, 108);
    metered_converse(
        &ledger,
        &registry,
        backend.as_ref(),
        &req(CLAUDE_HAIKU_4_5, 256),
    )
    .unwrap();

    // Reload from disk and confirm the price + provenance persisted.
    let reloaded = ledger_at(tmp.path(), 20.00);
    let snap = reloaded.snapshot().unwrap();
    let m = snap.per_model.get(CLAUDE_HAIKU_4_5).unwrap();
    assert_eq!(m.input_per_1k, Some(0.002));
    assert_eq!(m.output_per_1k, Some(0.010));
    match &m.price_source {
        Some(PriceSource::ConservativeUpperBound { rationale }) => {
            assert!(
                rationale.contains("upper bound"),
                "the rationale is recorded: {rationale}"
            );
        }
        other => panic!("expected a ConservativeUpperBound source, got {other:?}"),
    }
}

#[test]
fn haiku_pessimistic_rate_prices_a_known_turn() {
    let registry = ModelRegistry::builtin();
    let pricing = registry.pricing_for(CLAUDE_HAIKU_4_5).unwrap();
    // 65 in / 108 out at the pinned upper bound (0.002 / 0.010 per 1K).
    let cost = pricing.actual_cost(65, 108);
    let expected = 65.0 / 1000.0 * 0.002 + 108.0 / 1000.0 * 0.010; // 0.00013 + 0.00108 = 0.00121
    assert!((cost - expected).abs() < EPS);
    assert!(
        (cost - 0.00121).abs() < 1e-6,
        "the pessimistic Haiku turn is ~$0.00121, got {cost}"
    );
}

#[test]
fn kind_never_claims_a_model_that_did_not_run_budget_exhausted() {
    let tmp = tempfile::tempdir().unwrap();
    // A cap that refuses every hosted call → the chain must fall to Scripted, honestly labeled.
    let ledger = ledger_at(tmp.path(), 0.00001);
    let registry = ModelRegistry::builtin();

    // A Bedrock backend that PANICS if called (it must not be, since the budget refuses it first)
    // plus a Scripted tail.
    let panic_backend: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(PanicBackend);
    let narrator = Narrator::for_test(
        ledger,
        registry,
        vec![(panic_backend, CLAUDE_HAIKU_4_5.to_string())],
        None,
        true, // scripted tail
    );

    let narration = narrator
        .narrate("system", "the player peers into the dark", 256)
        .unwrap();
    assert_eq!(
        narration.kind, "scripted(budget-exhausted)",
        "the budget was exhausted, so the honest kind is scripted(budget-exhausted); a model that did not run is NEVER claimed"
    );
    assert!(!narration.text.trim().is_empty());
}

#[test]
fn kind_reports_the_model_that_actually_narrated() {
    let tmp = tempfile::tempdir().unwrap();
    let ledger = ledger_at(tmp.path(), 20.00);
    let registry = ModelRegistry::builtin();

    let (backend, calls) = FakeBackend::new(20, 30);
    let bedrock: Arc<dyn ConverseBackend + Send + Sync> = backend;
    let narrator = Narrator::for_test(
        ledger,
        registry,
        vec![(bedrock, NOVA_2_LITE.to_string())],
        None,
        true,
    );

    let narration = narrator.narrate("system", "narrate", 256).unwrap();
    assert_eq!(narration.kind, format!("model:{NOVA_2_LITE}"));
    assert_eq!(calls.load(Ordering::SeqCst), 1, "the model actually ran");
}
