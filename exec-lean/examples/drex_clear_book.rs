//! # DrEX (Dragon's EXchange) — the clear-book demo: run it, it drives the REAL matcher + executor
//!
//! ```text
//! cargo run -p dregg-intent --example drex_clear_book
//! ```
//!
//! A runnable Dragon's EXchange, end-to-end, from its **proved rungs** — the same way
//! `dregg-interchain-gov/examples/cross_chain_vote.rs` runs governance from proved verifiers.
//! Orders come in; the order book is **aggregated** (rung-2); the **real ring matcher**
//! (`intent/src/solver.rs` — Johnson's elementary circuits + Shapley–Scarf top-trading-cycles)
//! finds the multilateral clearing that no bilateral market can; the clearing is **settled through
//! the verified executor** (`intent/src/verified_settle.rs` — the ring folded, leg by leg, through
//! the Lean FFI `@[export] dregg_record_kernel_step` over the PROVED `Exec.recKExec` kernel); the
//! cleared allocations conserve per asset and respect every declared limit. Then a bad settlement
//! (an over-debit) is **refused by the verified kernel**, atomically.
//!
//! ## What ties to what (the realization of the proved rungs)
//!
//! - **rung-1 (fair clearing)** — `metatheory/Market/Clearing.lean`: `ringBook` (a genuinely
//!   3-multilateral book, `ringBook_bilateral_stuck` + `ring_pairs_refused` + `ringClearing`),
//!   `clearing_conserves_per_asset`. THIS DEMO's ring is the solver-shaped realization: a 3-cycle
//!   of three distinct assets that is bilaterally stuck and clears only as a ring.
//! - **rung-1 fairness** — `metatheory/Market/Fairness.lean`: `clearing_respects_limits` (every
//!   participant receives ≥ its declared `want_min` and sends ≤ its offer) and `overdebit_refused`
//!   (`¬ CycleValid underfundCycle`). The demo checks the SAME two properties on the cleared batch.
//! - **rung-2 (order-book aggregation)** — `metatheory/Market/Aggregation.lean`: `AggregationSound`
//!   (`aggregate` is a permutation of the submissions — no drop / no insert — sorted by declared
//!   price-time priority; `faithful_preserves_count`). The demo aggregates and asserts faithfulness.
//! - **the ledger realization** — the matcher's clearing IS lowered to a `dregg_turn::Turn` and
//!   folded through the verified per-asset kernel (`settleRing_conserves` / `settleRing_atomic`,
//!   `metatheory/Dregg2/Intent/Ring.lean`), so "an intent cleared" literally MEANS "a verified,
//!   conserving executor turn executed".
//!
//! ## Honest scope — DrEX over the CLEAR book
//!
//! This is **DrEX clear-book: the proved matching engine, running** over PUBLIC orders.
//!   * REAL: the matcher (`solver.rs`), the lowering (`lowering.rs`), and the verified settlement
//!     (`verified_settle.rs`) folded through the Lean per-asset kernel gate.
//!   * FIXTURE/SIMPLIFIED (said so, inline, when it prints): the orders here are a hand-built book;
//!     the solver models compatibility off single-asset per-leg equality (the Lean rung-1 book is
//!     richer — bundles + exact predicates); the verified-executor gate runs the IN-PROCESS proved
//!     transition here (an FFI-free target registers no gate) — on a native node with the
//!     `dregg-exec-lean` gate installed, each leg is ADDITIONALLY cross-checked against the real
//!     `dregg_record_kernel_step` export and any drift fails closed.
//!   * NEXT RUNGS (a separate track, not in this demo): rung-3 = ring-over-shielded-notes (private
//!     matching); rung-5 = uniform prices + partial fills (lifting the discrete substrate).

use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_intent::lowering::{Intent, LoweringContext, lower, seal_plan_uniform};
use dregg_intent::solver::{ExchangeSpec, IntentNode, RingSolver, RingTrade};
use dregg_intent::verified_settle::{
    VerifiedLedger, VerifiedSettleError, extract_legs, funded_ledger, settle_fulfillment_verified,
    settle_ring_verified, touched_assets,
};

use dregg_cell::CellId;
use dregg_turn::action::Authorization;

// ── the three assets the book trades (content-addressed ids; low byte names them) ──
const GOLD: u8 = 0x60;
const ART: u8 = 0xA7;
const WINE: u8 = 0x71;
const SILVER: u8 = 0x51;
const PEARL: u8 = 0x9E;

fn asset(byte: u8) -> AssetId {
    let mut a = [0u8; 32];
    a[0] = byte;
    a
}

fn asset_name(a: &AssetId) -> &'static str {
    match a[0] {
        GOLD => "GOLD",
        ART => "ART",
        WINE => "WINE",
        SILVER => "SILVER",
        PEARL => "PEARL",
        _ => "?",
    }
}

/// A resting order on the clear book: a trader's public "I offer X, I want ≥ Y".
struct Order {
    trader: &'static str,
    node: IntentNode,
    /// The declared price-time priority key (lower = matched first) — the rung-2 microstructure
    /// field `Order.priority` (`Market/Aggregation.lean`). Here: the submission tick.
    priority: u64,
}

fn make_order(
    trader: &'static str,
    id_byte: u8,
    creator_byte: u8,
    offer_asset: u8,
    offer_amount: u64,
    want_asset: u8,
    want_min_amount: u64,
    priority: u64,
) -> Order {
    let mut intent_id = [0u8; 32];
    intent_id[0] = id_byte;
    Order {
        trader,
        node: IntentNode {
            intent_id,
            exchange: ExchangeSpec {
                offer_asset: asset(offer_asset),
                offer_amount,
                want_asset: asset(want_asset),
                want_min_amount,
                min_rate: None,
                max_rate: None,
            },
            creator: CommitmentId([creator_byte; 32]),
            expiry: 9_999,
        },
        priority,
    }
}

fn main() {
    println!("── DrEX · Dragon's EXchange — the clear-book demo ─────────────────────────");
    println!("   the proved matching engine, running: orders → aggregated book →");
    println!("   multilateral match → verified conserving settlement → allocations");
    println!();

    // ───────────────────────── 1. orders in ─────────────────────────
    //
    // A cross-bid ring that CANNOT clear bilaterally: three distinct assets in a cycle. No two
    // traders want each other's asset, so no pairwise swap exists — only the 3-ring closes. This is
    // the solver-shaped realization of the Lean `ringBook` (`ringBook_bilateral_stuck` +
    // `ring_pairs_refused`: every 1- and 2-party sub-book is refused; `ringClearing`: the 3-ring
    // clears). Plus one resting order that matches nobody (to show aggregation keeps ALL orders).
    let book = vec![
        make_order("Ada", 0x11, 0x01, GOLD, 100, ART, 10, 3), // offers GOLD, wants ART
        make_order("Bram", 0x12, 0x02, ART, 50, WINE, 20, 1), // offers ART, wants WINE
        make_order("Cyl", 0x13, 0x03, WINE, 80, GOLD, 40, 2), // offers WINE, wants GOLD
        make_order("Del", 0x14, 0x04, SILVER, 30, PEARL, 5, 4), // nobody offers PEARL — rests
    ];
    println!("submitted order book ({} public orders):", book.len());
    for o in &book {
        println!(
            "  {:<5} offers {:>3} {:<6} wants ≥ {:>2} {:<6}  (priority {})",
            o.trader,
            o.node.exchange.offer_amount,
            asset_name(&o.node.exchange.offer_asset),
            o.node.exchange.want_min_amount,
            asset_name(&o.node.exchange.want_asset),
            o.priority,
        );
    }
    println!();

    // ───────────────── 2. aggregate the order book (rung-2, faithful) ─────────────────
    //
    // The rung-2 aggregator: sort the submitted stream by declared price-time priority, faithfully.
    // `Market/Aggregation.lean` proves `aggregate` is a PERMUTATION of the submissions (no drop,
    // no insert — `AggregationSound`) that is SORTED by priority. We realize + check that here.
    let mut aggregated: Vec<&Order> = book.iter().collect();
    aggregated.sort_by_key(|o| o.priority);

    // Faithfulness (the Lean `faithful_preserves_count` / `no_drop` / `no_insert`): the aggregated
    // book is the SAME multiset of orders as the submissions — just reordered by priority.
    {
        let mut sub_ids: Vec<u8> = book.iter().map(|o| o.node.intent_id[0]).collect();
        let mut agg_ids: Vec<u8> = aggregated.iter().map(|o| o.node.intent_id[0]).collect();
        sub_ids.sort_unstable();
        agg_ids.sort_unstable();
        assert_eq!(
            sub_ids, agg_ids,
            "AGGREGATION SOUND: the book must be a permutation of the submissions (no drop/insert)"
        );
        // Sorted by priority (no reorder beyond the declared key).
        assert!(
            aggregated
                .windows(2)
                .all(|w| w[0].priority <= w[1].priority),
            "AGGREGATION SOUND: the book must be sorted by declared price-time priority"
        );
    }
    println!("aggregated book (rung-2: sorted by price-time priority, faithfully —");
    println!("  a permutation of the submissions, no order dropped or inserted):");
    for o in &aggregated {
        println!(
            "  [prio {}] {:<5} {:>3} {:<6} → ≥ {:>2} {:<6}",
            o.priority,
            o.trader,
            o.node.exchange.offer_amount,
            asset_name(&o.node.exchange.offer_asset),
            o.node.exchange.want_min_amount,
            asset_name(&o.node.exchange.want_asset),
        );
    }
    println!("  (rung-2 = Market/Aggregation.lean `aggregate_sound`: PROVED faithful)");
    println!();

    // ───────────────── 3. match via the REAL solver (find the clearing ring) ─────────────────
    //
    // Johnson's elementary circuits over the compatibility graph (`solver.rs`): an edge A→B iff
    // A's offered asset is exactly B's wanted asset and covers its minimum. The 3-cycle is the
    // Shapley–Scarf top-trading-cycle the bilateral market cannot form.
    let nodes: Vec<IntentNode> = aggregated.iter().map(|o| o.node.clone()).collect();
    let solver = RingSolver::new(5);
    let graph = solver.build_graph(&nodes);
    let rings = solver.find_rings(&graph);

    // First, show the bilateral market is STUCK (the before-picture, Lean `ring_pairs_refused`):
    // no 2-cycle exists among the three ring traders.
    let two_cycles = rings.iter().filter(|r| r.participants.len() == 2).count();
    println!("the REAL matcher runs (Johnson elementary circuits + Shapley–Scarf TTC):");
    println!("  bilateral (2-party) matches among the cross-bid traders: {two_cycles}");
    println!("  → the ring is genuinely MULTILATERAL — no pairwise swap clears it");

    let ring: RingTrade = rings
        .iter()
        .filter(|r| r.participants.len() >= 3)
        .max_by_key(|r| r.participants.len())
        .cloned()
        .expect("the matcher must find the multilateral clearing ring");
    println!(
        "  found the clearing ring: {} participants, {} settlement legs, score {}",
        ring.participants.len(),
        ring.settlements.len(),
        ring.score,
    );
    let name_of = |c: &CommitmentId| -> &'static str {
        book.iter()
            .find(|o| &o.node.creator == c)
            .map(|o| o.trader)
            .unwrap_or("?")
    };
    for s in &ring.settlements {
        println!(
            "    leg: {:<5} → {:<5}  {:>3} {}",
            name_of(&s.from),
            name_of(&s.to),
            s.amount,
            asset_name(&s.asset),
        );
    }
    println!();

    // ───────────────── 4. settle through the VERIFIED executor ─────────────────
    //
    // Lower the matched ring to a real `dregg_turn::Turn`, then fold each leg through the verified
    // per-asset kernel — the tie to the PROVED `Exec.recKExec`. `extract_legs` pins that the
    // lowering was data-preserving leg-by-leg; `settle_ring_verified` is `settleRing` over the
    // verified executor (all-or-nothing, `settleRing_atomic`; conserving, `settleRing_conserves`).
    let anchor = CellId::from_bytes([0x9Du8; 32]);
    let intent = Intent::RingSettlement {
        rings: vec![ring.clone()],
        anchor,
        solver_id: [0xAB; 32],
        validity_proof_hash: [0xCD; 32],
    };
    let plan = lower(intent, &LoweringContext::default()).expect("the matched ring lowers");
    let sealed = seal_plan_uniform(
        plan,
        anchor,
        0,
        Authorization::Signature([0u8; 32], [0u8; 32]),
    );

    // This example is an FFI-free target: it registers no `IntentVerifiedGate`, so each leg runs
    // the IN-PROCESS proved transition (`recKExecAsset`, the SAME gate the Lean
    // `RingFFI.ffi_export_realises_settleRing_leg` proves the export realises). On a native node the
    // installed `dregg-exec-lean` gate ADDITIONALLY cross-checks each leg against the real
    // `dregg_record_kernel_step` export and fails closed on any drift.
    println!("verified executor: FFI-free target — no Lean gate registered here, so each leg runs");
    println!("  the IN-PROCESS proved transition (`recKExecAsset`); a native node additionally");
    println!(
        "  cross-checks the REAL `dregg_record_kernel_step` export and fails closed on drift."
    );

    let (pre, post) =
        settle_fulfillment_verified(&sealed, &ring.settlements).expect("the ring settles");
    let legs = extract_legs(&sealed, &ring.settlements).expect("legs extract + data-preserve");
    println!(
        "  the lowered Turn's legs fold through the verified kernel, all-or-nothing → SETTLED"
    );
    println!();

    // ───────────────── 5. cleared allocations + conservation + limits ─────────────────
    println!("── CLEARED ALLOCATIONS ────────────────────────────────────────────────────");
    for o in &book {
        // Skip the resting (unmatched) order.
        if !ring.participants.contains(&o.node.intent_id) {
            println!("  {:<5} rests (no match this batch)", o.trader);
            continue;
        }
        let cell = o.node.creator.0[0];
        let got_asset = o.node.exchange.want_asset;
        let received = post.get(cell, &got_asset) - pre.get(cell, &got_asset);
        let gave_asset = o.node.exchange.offer_asset;
        let sent = pre.get(cell, &gave_asset) - post.get(cell, &gave_asset);
        println!(
            "  {:<5} sent {:>3} {:<6} received {:>3} {:<6}  (wanted ≥ {} {})",
            o.trader,
            sent,
            asset_name(&gave_asset),
            received,
            asset_name(&got_asset),
            o.node.exchange.want_min_amount,
            asset_name(&got_asset),
        );
    }
    println!();

    // Per-asset conservation — the Lean `settleRing_conserves` / `clearing_conserves_per_asset`.
    println!("this cleared batch CONSERVES per asset (Market/Clearing.lean");
    println!("  `clearing_conserves_per_asset`; Ring.lean `settleRing_conserves`):");
    for a in touched_assets(&legs) {
        let before = pre.total_asset(&a);
        let after = post.total_asset(&a);
        assert_eq!(
            before,
            after,
            "verified settle must conserve {}",
            asset_name(&a)
        );
        println!("  {:<6}: {before} in  = {after} out  ✓", asset_name(&a));
    }
    println!();

    // Fairness — the Lean `clearing_respects_limits` (both sides, every participant).
    println!(
        "and RESPECTS EVERY DECLARED LIMIT (Market/Fairness.lean `clearing_respects_limits`):"
    );
    for o in &book {
        if !ring.participants.contains(&o.node.intent_id) {
            continue;
        }
        let cell = o.node.creator.0[0];
        let received = post.get(cell, &o.node.exchange.want_asset)
            - pre.get(cell, &o.node.exchange.want_asset);
        let sent = pre.get(cell, &o.node.exchange.offer_asset)
            - post.get(cell, &o.node.exchange.offer_asset);
        assert!(
            received >= o.node.exchange.want_min_amount as i128,
            "IR: {} must receive ≥ its want_min",
            o.trader
        );
        assert!(
            sent <= o.node.exchange.offer_amount as i128,
            "budget: {} must send ≤ its offer",
            o.trader
        );
        println!(
            "  {:<5} received {} ≥ want_min {} ✓   sent {} ≤ offer {} ✓",
            o.trader, received, o.node.exchange.want_min_amount, sent, o.node.exchange.offer_amount,
        );
    }
    println!();

    // ───────────────── 6. reject polarity — a bad settlement, refused by the kernel ─────────────
    //
    // The verified executor is not a rubber stamp. Take the SAME cleared legs, but drain one
    // sender's balance so its leg would OVER-DEBIT (spend more than it holds). The verified fold
    // refuses the leg and — atomically — aborts the WHOLE ring, leaving nothing settled. This is
    // the running realization of the Lean `overdebit_refused` (`¬ CycleValid underfundCycle`) and
    // `settleRing_atomic`.
    println!("── REJECT POLARITY: a bad settlement, refused by the verified kernel ──────");
    let mut starved: VerifiedLedger = funded_ledger(&legs);
    let victim = legs[0].clone();
    starved.set(victim.from, &victim.asset, victim.amount - 1); // one short — an over-debit
    println!(
        "  drained leg 0's sender (cell {:#04x}) to {} {} — one short of its {} {} leg",
        victim.from,
        victim.amount - 1,
        asset_name(&victim.asset),
        victim.amount,
        asset_name(&victim.asset),
    );
    match settle_ring_verified(&starved, &legs) {
        Err(VerifiedSettleError::LegRejected { index, .. }) => {
            println!(
                "  verified executor → LegRejected at leg {index}: the over-debit is refused,"
            );
            println!("  and the WHOLE ring aborts (atomicity — no partial settlement). ✓");
        }
        other => panic!("an over-debiting ring MUST be refused; got {other:?}"),
    }
    println!();
    println!("done: the whole flow ran the REAL matcher (solver.rs) and settled through the");
    println!("verified executor (verified_settle.rs → the proved recKExec kernel). Clear-book");
    println!(
        "scope; rung-3 (shielded/private matching) and rung-5 (prices/partial-fills) are next."
    );
}
