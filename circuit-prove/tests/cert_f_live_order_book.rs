//! **THE INTEGRITY CERTIFICATE, REACHED FROM A LIVE ORDER BOOK.**
//!
//! The Cert-F STARK wrap existed, was sound, and could never fire for a live order. Three
//! things stood between a posted batch and a verifying proof:
//!
//!   1. `fhegg_clear` claimed its certificate against a hardcoded `epsilon = 0.5` — a
//!      number unrelated to any registered program's budget;
//!   2. `cert_f_prove` defaulted the fixed-point scale to `1` with no `epsilon` at all, so
//!      the bridged program was the `×1` image of the batch with `ε := achieved gap` —
//!      the preimage of no registered program. Every live batch was refused at
//!      `try_cert_f_descriptor` before the prover ever ran; and
//!   3. the deployed AIR REFUSED an honest solve. A real solve of this batch returns the
//!      dual `π = (1, −1, 0)`; its fixed-point image carries `−100`, which lifts to `p−100`
//!      in BabyBear and has no 28-bit decomposition, so the descriptor's potential range
//!      gadget rejected a Cert-F-valid certificate (`OodEvaluationMismatch`). Every Cert-F
//!      clause mentions `π` only through `π_head − π_tail`, so the bridge presents the
//!      canonical translate `π − min(π) ≥ 0` — the same certificate, in the representative
//!      the deployed gadget can accept.
//!
//! This gate drives the whole live path with none of those:
//!
//!   order book JSON  →  `fhegg_solver::book::map_book`  (the ONE mapping the CLI uses)
//!                    →  PDHG + exact-feasibility restore
//!                    →  `CertF` at a budget DERIVED from the resolved registration
//!                    →  `resolve_registered_scaling` (the batch finds its own registration)
//!                    →  `prove_cert_f`  →  `verify_cert_f`   ACCEPTS
//!
//! and then shows the teeth: a MUTATED clearing (an overstated fill, and an over-capacity
//! fill) is REFUSED, a forged public cleared-volume does not verify, and a batch whose shape
//! is not the preimage of a registered Lean-emitted program is refused with the exact
//! artifact it is missing.
//!
//! ## Substrate
//!
//! Nothing here authors a constraint. The AIR is `Market.CertFDescriptor.certFDescriptorOf`
//! in Lean, byte-pinned and committed under `circuit/descriptors/`; Rust parses that artifact
//! and proves against it. What this file adds is *resolution*: which Lean-emitted program a
//! live batch IS. A batch that is the preimage of none is refused — no shape is specialised
//! at runtime.

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::cert_f_air::{
    VALUE_BITS, from_solution_json, from_solution_json_registered, prove_cert_f,
    prove_cert_f_refused, resolve_registered_scaling, verify_cert_f,
};
use fhegg_solver::book::{AccuracyBudget, BookOrder, map_book};
use fhegg_solver::cert::CertF;
use fhegg_solver::pdhg::{restore_feasibility, solve_cpu};

fn order(trader: &str, offer: &str, amount: u64, want: &str, priority: u64) -> BookOrder {
    BookOrder {
        trader: trader.to_string(),
        offer_asset: offer.to_string(),
        offer_amount: amount,
        want_asset: want.to_string(),
        want_min: 1,
        priority,
    }
}

/// A LIVE-SHAPED batch: four posted orders over three assets — a 3-asset ring of trades plus
/// one bilateral leg at higher priority. This is a real order book, not a hand-written
/// program: every `(w, c)` entry comes out of `map_book` from the posted `priority` and
/// `offerAmount`.
fn live_batch() -> Vec<BookOrder> {
    vec![
        order("alice", "B", 5, "A", 1),
        order("bob", "C", 5, "B", 1),
        order("carol", "A", 5, "C", 1),
        order("dave", "A", 3, "B", 3),
    ]
}

/// Clear a posted batch exactly the way `fhegg_clear` does, at a budget the caller supplies.
fn clear(orders: &[BookOrder], budget: AccuracyBudget, iters: usize) -> (CertF, Vec<f64>) {
    let program = map_book(orders);
    let approx = solve_cpu(&program.lp, iters);
    let (f_exact, _box_viol) = restore_feasibility(&program.lp, approx.f.clone());
    let epsilon = budget.epsilon_for(&program.lp);
    let cert = CertF::from_solution(&program.lp, &f_exact, &approx.y, epsilon);
    (cert, f_exact)
}

/// The registration a live batch resolves to, as the budget the solver claims against.
fn resolved_budget(orders: &[BookOrder]) -> AccuracyBudget {
    // Resolution only reads the PUBLIC program `(n_nodes, edges, w, c)`, so a throwaway
    // zero-witness certificate over the mapped LP is enough to ask the registry which
    // program this batch is.
    let program = map_book(orders);
    let probe = CertF::from_solution(
        &program.lp,
        &vec![0.0; program.lp.m()],
        &vec![0.0; program.lp.n_nodes],
        0.0,
    );
    let scaling = resolve_registered_scaling(&probe.to_json())
        .expect("the live batch must resolve to a registered Lean-emitted program");
    AccuracyBudget::Registered {
        scale: scaling.scale,
        integer_epsilon: scaling.epsilon,
    }
}

/// **THE HEADLINE.** A live order book produces a Cert-F certificate that the REAL dregg
/// STARK proves and the verifier ACCEPTS — with no operator-supplied scale, no
/// operator-supplied epsilon, and no hand-written program anywhere on the path.
#[test]
fn live_order_book_produces_a_verifying_cert_f_stark_proof() {
    let batch = live_batch();

    // The batch tells us its own registration; the certificate is claimed against exactly
    // the budget that registration grants (2000 in the scaled grid = 0.2 in solver units).
    let budget = resolved_budget(&batch);
    assert_eq!(
        budget,
        AccuracyBudget::Registered {
            scale: 100,
            integer_epsilon: 2000
        },
        "the posted batch is the x100 preimage of the Lean-emitted market4 program"
    );

    let (cert, _f) = clear(&batch, budget, 8000);
    let report = cert.check_strict();
    assert!(
        report.valid,
        "the untrusted solve must produce a strictly-checkable f64 certificate at the \
         registration's own budget: {report:?}"
    );

    // Dynamic registration: scale AND epsilon are read off the resolved Lean-emitted
    // program. Nothing here is an environment variable.
    let (witness, scaling) = from_solution_json_registered(&cert.to_json())
        .expect("a live batch must bridge under its own registration");
    assert_eq!(scaling.scale, 100);
    assert_eq!(scaling.epsilon, 2000);
    assert_eq!(scaling.solver_epsilon, 0.2);

    let check = witness.check();
    assert!(
        check.valid,
        "the bridged live certificate must satisfy Market.Certified: {check:?}"
    );
    assert!(
        check.gap >= 0 && check.gap <= scaling.epsilon,
        "achieved integer gap {} must sit inside the granted budget {}",
        check.gap,
        scaling.epsilon
    );

    // THE REAL STARK.
    let (desc, proof, pis) =
        prove_cert_f(&witness).expect("the live batch's certificate must prove in the STARK");
    verify_cert_f(&desc, &proof, &pis).expect("the live batch's STARK proof must VERIFY");

    // The only witness-derived value the world sees is the cleared volume.
    assert_eq!(pis.len(), 1);
    assert_eq!(pis[0].as_u32() as i64, witness.objective());
    assert_eq!(
        witness.objective(),
        180_000,
        "the live batch clears wᵀf = 180000 in the scaled grid (18 in solver units)"
    );
}

/// **THE CANONICAL-POTENTIAL TOOTH.** The blocker this lane found: a real solve of the live
/// batch returns the dual `π = (1, −1, 0)`, whose fixed-point image carries `−100`. In
/// BabyBear that lifts to `p − 100`, which has no 28-bit decomposition, so the descriptor's
/// potential range gadget refuses an honest, Cert-F-valid certificate. The bridge must hand
/// the AIR the canonical translate — same certificate, presentable representative.
#[test]
fn a_real_solve_has_a_negative_dual_and_the_bridge_canonicalises_it() {
    let batch = live_batch();
    let program = map_book(&batch);
    let approx = solve_cpu(&program.lp, 8000);
    assert!(
        approx.y.iter().any(|&pi| pi < -1e-9),
        "the live solve's dual really is negative somewhere — if this stops holding the \
         canonicalisation below is no longer being exercised: {:?}",
        approx.y
    );

    let (f_exact, _) = restore_feasibility(&program.lp, approx.f.clone());
    let cert = CertF::from_solution(&program.lp, &f_exact, &approx.y, 0.2);
    let (witness, _) = from_solution_json_registered(&cert.to_json()).expect("live batch bridges");
    assert!(
        witness.pi.iter().all(|&pi| pi >= 0),
        "the bridged witness must present nonnegative potentials: {:?}",
        witness.pi
    );
    assert_eq!(
        witness.pi.iter().min(),
        Some(&0),
        "the canonical translate pins min(π) = 0: {:?}",
        witness.pi
    );
    // The certificate is the SAME one: the shift is invisible to every Cert-F clause.
    assert!(witness.check().valid);
    assert_eq!(witness.gap(), 0, "a common π shift cannot move the gap");
    assert_eq!(witness.s, vec![300, 0, 0, 100], "nor the dual slacks");
}

/// **MAKE THE NEW GUARD FIRE.** Canonicalising the potentials removes the *sign* problem, not
/// the *span* problem: a dual whose spread reaches `2^VALUE_BITS` still has no decomposition
/// under the deployed gadget, at any translate. The bridge must REFUSE by name there rather
/// than hand the prover a witness its own AIR rejects.
#[test]
fn a_potential_span_past_the_range_gadget_is_refused_not_shifted() {
    // A ring-3-shaped program whose dual spans the whole 28-bit window. `min` is already 0,
    // so the translate cannot help — this is the guard's own territory.
    let span = (1u64 << VALUE_BITS) as f64;
    let json = format!(
        r#"{{"n_nodes":3,"m_edges":3,"edges":[[0,1],[1,2],[2,0]],
             "w":[1.0,1.0,1.0],"c":[1.0,1.0,1.0],
             "f":[1.0,1.0,1.0],"pi":[0.0,{span},0.0],"s":[1.0,1.0,1.0],"epsilon":0.0}}"#
    );
    let err = from_solution_json(&json, 1)
        .expect_err("a potential span at 2^VALUE_BITS must be refused by the bridge");
    assert!(
        err.contains("canonical potential translate") && err.contains("range gadget"),
        "the refusal must name the deployed gadget it does not fit: {err}"
    );

    // One below the window, the same shape passes — the guard rejects the span, not the shape.
    let ok_span = span - 1.0;
    let json_ok = format!(
        r#"{{"n_nodes":3,"m_edges":3,"edges":[[0,1],[1,2],[2,0]],
             "w":[1.0,1.0,1.0],"c":[1.0,1.0,1.0],
             "f":[1.0,1.0,1.0],"pi":[0.0,{ok_span},0.0],"s":[1.0,1.0,1.0],"epsilon":0.0}}"#
    );
    assert!(from_solution_json(&json_ok, 1).is_ok());
}

/// **THE MUTATION TOOTH.** The same live batch, cleared honestly, then MUTATED: one trader's
/// fill is overstated. The mutated clearing cannot produce a verifying proof.
#[test]
fn a_mutated_clearing_of_the_live_batch_is_refused() {
    let batch = live_batch();
    let budget = resolved_budget(&batch);
    let (honest, _) = clear(&batch, budget, 8000);
    assert!(honest.check_strict().valid);

    // (a) OVERSTATED FILL: alice's cleared amount is inflated by one unit with no return
    //     leg. Per-asset conservation breaks — value appears from nowhere.
    let mut overstated = honest.clone();
    overstated.f[0] += 1.0;
    let (witness, _) = from_solution_json_registered(&overstated.to_json())
        .expect("the mutated batch still resolves to the same public program");
    let check = witness.check();
    assert!(
        !check.conserves,
        "an overstated fill must break Af = 0: {check:?}"
    );
    assert!(
        prove_cert_f_refused(&witness),
        "the STARK must REFUSE a clearing with an overstated fill"
    );

    // (b) OVER-CAPACITY FILL: push the ring past every posted offerAmount and stand the
    //     bilateral leg down, so the circulation still balances at every asset. Conservation
    //     holds, so only the box gate can catch it.
    let mut over_capacity = honest.clone();
    for e in 0..3 {
        over_capacity.f[e] = over_capacity.c[e] + 1.0;
    }
    over_capacity.f[3] = 0.0;
    let (witness, _) = from_solution_json_registered(&over_capacity.to_json())
        .expect("the over-capacity batch still resolves to the same public program");
    let check = witness.check();
    assert!(
        check.conserves && !check.box_ok,
        "an over-capacity ring conserves but breaks 0 ≤ f ≤ c: {check:?}"
    );
    assert!(
        prove_cert_f_refused(&witness),
        "the STARK must REFUSE a clearing that exceeds a posted offerAmount"
    );
}

/// **THE PUBLIC-VALUE TOOTH.** An honest live proof must not verify against a forged cleared
/// volume: the one public scalar is bound to the witness, so a venue cannot publish a
/// different number than the one it proved.
#[test]
fn a_forged_cleared_volume_does_not_verify_against_the_live_proof() {
    let batch = live_batch();
    let budget = resolved_budget(&batch);
    let (cert, _) = clear(&batch, budget, 8000);
    let (witness, _) = from_solution_json_registered(&cert.to_json()).expect("live batch bridges");
    let (desc, proof, pis) = prove_cert_f(&witness).expect("honest live batch proves");
    verify_cert_f(&desc, &proof, &pis).expect("honest public input verifies");

    let mut forged = pis.clone();
    forged[0] = BabyBear::new(pis[0].as_u32() + 1);
    assert!(
        verify_cert_f(&desc, &proof, &forged).is_err(),
        "a live proof of volume V must NOT verify as volume V+1"
    );
}

/// **THE FAIL-CLOSED TOOTH — this is the honest limit of the fix.** Resolution finds the
/// registration a batch already has; it does not manufacture one. A five-order batch has no
/// Lean-emitted descriptor, and is refused with the exact artifact it is missing rather than
/// having its constraints specialised in Rust.
#[test]
fn an_unregistered_live_batch_is_refused_by_name() {
    let mut batch = live_batch();
    batch.push(order("erin", "C", 2, "A", 2));
    let program = map_book(&batch);
    let probe = CertF::from_solution(
        &program.lp,
        &vec![0.0; program.lp.m()],
        &vec![0.0; program.lp.n_nodes],
        0.0,
    );
    let err = resolve_registered_scaling(&probe.to_json())
        .expect_err("a 5-order shape has no Lean-emitted descriptor");
    assert!(
        err.contains("CertFDescriptor.lean") && err.contains("IntegerAdmission"),
        "the refusal must name the missing Lean artifact and obligation: {err}"
    );

    // ...and nothing downstream can be talked into proving it either.
    let approx = solve_cpu(&program.lp, 8000);
    let (f_exact, _box_viol) = restore_feasibility(&program.lp, approx.f.clone());
    let cert = CertF::from_solution(&program.lp, &f_exact, &approx.y, 1.0);
    assert!(
        from_solution_json_registered(&cert.to_json()).is_err(),
        "an unregistered live shape must never bridge"
    );
}

/// **THE RESOLUTION-HONESTY TOOTH.** A batch whose posted weights are NOT the exact
/// fixed-point preimage of a registration must not be rounded into that registration. If it
/// were, the proof would be about constants nobody's batch had.
#[test]
fn a_near_miss_batch_is_not_rounded_into_a_registration() {
    let program = map_book(&live_batch());
    let mut off_grid = program.lp.clone();
    // 1.005 x 100 = 100.5 — adjacent to the registered weight 100, and not its preimage.
    off_grid.w[0] = 1.005;
    let probe = CertF::from_solution(
        &off_grid,
        &vec![0.0; off_grid.m()],
        &vec![0.0; off_grid.n_nodes],
        0.0,
    );
    assert!(
        resolve_registered_scaling(&probe.to_json()).is_err(),
        "a non-integral fixed-point image must be refused, never rounded into a registration"
    );

    // The exact preimage still resolves — the tooth rejects the near miss, not the shape.
    let exact = CertF::from_solution(
        &program.lp,
        &vec![0.0; program.lp.m()],
        &vec![0.0; program.lp.n_nodes],
        0.0,
    );
    assert!(resolve_registered_scaling(&exact.to_json()).is_ok());
}
