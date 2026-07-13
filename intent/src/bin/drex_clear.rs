//! # `drex_clear` — the DrEX clear-book pipeline as a thin JSON CLI (the web wire)
//!
//! ```text
//! echo '<orders-json>' | drex_clear
//! ```
//!
//! This is the SAME real pipeline as `intent/examples/drex_clear_book.rs` — orders →
//! aggregated book (rung-2) → **real ring matcher** (`solver.rs`, Johnson elementary circuits +
//! Shapley–Scarf TTC) → **verified conserving settlement** (`verified_settle.rs`, each leg folded
//! through the proved per-asset kernel `recKExecAsset` / `settle_ring_verified`) → allocations +
//! per-asset conservation + reject-polarity — but parameterized by the REVEALED orders posted on
//! stdin and emitting the cleared result as JSON on stdout. `drex-web/serve.mjs` shells to this so
//! the browser shows the REAL solver's clearing, not a JS mirror.
//!
//! Input  (stdin): a JSON array of revealed orders:
//!   `[{"trader":"Ada","offerAsset":"GOLD","offerAmount":100,"wantAsset":"ART","wantMin":10,"priority":3}, …]`
//! Output (stdout): the real cleared batch (aggregated book, the ring the matcher found, the
//!   per-trader allocations read off the VERIFIED post-ledger, per-asset conservation, and the
//!   over-debit reject the verified kernel refuses). See `Cleared` below for the exact shape.

use std::io::Read;

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

use serde::{Deserialize, Serialize};

/// One revealed order as posted by the web app.
#[derive(Deserialize)]
struct OrderIn {
    trader: String,
    #[serde(rename = "offerAsset")]
    offer_asset: String,
    #[serde(rename = "offerAmount")]
    offer_amount: u64,
    #[serde(rename = "wantAsset")]
    want_asset: String,
    #[serde(rename = "wantMin")]
    want_min: u64,
    priority: u64,
}

#[derive(Serialize)]
struct AggRow {
    trader: String,
    #[serde(rename = "offerAsset")]
    offer_asset: String,
    #[serde(rename = "offerAmount")]
    offer_amount: u64,
    #[serde(rename = "wantAsset")]
    want_asset: String,
    #[serde(rename = "wantMin")]
    want_min: u64,
    priority: u64,
}

#[derive(Serialize)]
struct Leg {
    #[serde(rename = "fromTrader")]
    from_trader: String,
    #[serde(rename = "toTrader")]
    to_trader: String,
    asset: String,
    amount: u64,
}

#[derive(Serialize)]
struct Ring {
    participants: Vec<String>,
    legs: Vec<Leg>,
    score: f64,
}

#[derive(Serialize)]
struct Alloc {
    trader: String,
    rested: bool,
    #[serde(rename = "sentAsset")]
    sent_asset: String,
    sent: i128,
    offer: u64,
    #[serde(rename = "recvAsset")]
    recv_asset: String,
    received: i128,
    #[serde(rename = "wantMin")]
    want_min: u64,
    ir: bool,
    budget: bool,
}

#[derive(Serialize)]
struct Conservation {
    asset: String,
    #[serde(rename = "in")]
    in_: i128,
    out: i128,
    ok: bool,
}

#[derive(Serialize)]
struct Reject {
    victim: String,
    asset: String,
    #[serde(rename = "starvedTo")]
    starved_to: i128,
    need: i128,
    #[serde(rename = "refusedAt")]
    refused_at: i64,
    aborted: bool,
    #[serde(rename = "settledLegs")]
    settled_legs: usize,
}

#[derive(Serialize)]
struct Cleared {
    /// `true` when the whole real pipeline ran to a cleared, conserving, limit-respecting batch.
    ok: bool,
    /// The rung-2 aggregated book (faithful permutation sorted by priority).
    aggregated: Vec<AggRow>,
    #[serde(rename = "aggregateFaithful")]
    aggregate_faithful: bool,
    /// Count of bilateral (2-party) matches — 0 proves the ring is genuinely multilateral.
    #[serde(rename = "twoCycles")]
    two_cycles: usize,
    /// The clearing ring the REAL matcher found (`null` if the book does not clear).
    ring: Option<Ring>,
    /// Per-trader allocation, read off the VERIFIED post-ledger.
    allocations: Vec<Alloc>,
    /// Per-asset conservation (in = out) over the verified settle.
    conservation: Vec<Conservation>,
    #[serde(rename = "limitsOk")]
    limits_ok: bool,
    #[serde(rename = "conservesOk")]
    conserves_ok: bool,
    /// The over-debit the verified kernel refuses (`null` if no ring cleared).
    reject: Option<Reject>,
    /// Provenance string surfaced in the UI — names the real Rust it ran.
    provenance: String,
}

/// A deterministic asset-name ↔ byte dictionary built from first appearance, so arbitrary revealed
/// asset names round-trip while equal names map to equal `AssetId`s (what the solver compares).
struct AssetDict {
    names: Vec<String>,
}
impl AssetDict {
    fn new() -> Self {
        Self { names: Vec::new() }
    }
    fn byte_of(&mut self, name: &str) -> u8 {
        if let Some(i) = self.names.iter().position(|n| n == name) {
            return 0x60 + i as u8;
        }
        self.names.push(name.to_string());
        0x60 + (self.names.len() - 1) as u8
    }
    fn name_of(&self, byte: u8) -> String {
        let i = byte.wrapping_sub(0x60) as usize;
        self.names.get(i).cloned().unwrap_or_else(|| "?".into())
    }
}

fn asset(byte: u8) -> AssetId {
    let mut a = [0u8; 32];
    a[0] = byte;
    a
}

fn fail(msg: &str) -> ! {
    // Emit a structured error the web app can render, then exit non-zero.
    let v = serde_json::json!({ "ok": false, "error": msg });
    println!("{v}");
    std::process::exit(1);
}

fn main() {
    // Orders JSON comes from argv[1] if given (enables a remote/offloaded invocation that cannot
    // pipe local stdin), else from stdin (the local serve.mjs `/clear` wire).
    let mut buf = String::new();
    if let Some(arg) = std::env::args().nth(1) {
        buf = arg;
    } else if std::io::stdin().read_to_string(&mut buf).is_err() {
        fail("could not read orders JSON from stdin");
    }
    let orders: Vec<OrderIn> = match serde_json::from_str(&buf) {
        Ok(o) => o,
        Err(e) => fail(&format!("bad orders JSON: {e}")),
    };
    if orders.is_empty() {
        fail("no orders submitted");
    }

    let mut dict = AssetDict::new();

    // ── 1. build the intent nodes (distinct creator + intent low bytes per order) ──
    struct Row {
        trader: String,
        creator_byte: u8,
        node: IntentNode,
        priority: u64,
    }
    let mut rows: Vec<Row> = Vec::with_capacity(orders.len());
    for (i, o) in orders.iter().enumerate() {
        if i >= 200 {
            fail("too many orders (the verified ledger indexes cells by a distinct low byte)");
        }
        let creator_byte = 0x01 + i as u8;
        let id_byte = 0xB0u8.wrapping_add(i as u8); // distinct from creator bytes
        let offer_b = dict.byte_of(&o.offer_asset);
        let want_b = dict.byte_of(&o.want_asset);
        let mut intent_id = [0u8; 32];
        intent_id[0] = id_byte;
        rows.push(Row {
            trader: o.trader.clone(),
            creator_byte,
            node: IntentNode {
                intent_id,
                exchange: ExchangeSpec {
                    offer_asset: asset(offer_b),
                    offer_amount: o.offer_amount,
                    want_asset: asset(want_b),
                    want_min_amount: o.want_min,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([creator_byte; 32]),
                expiry: 9_999,
            },
            priority: o.priority,
        });
    }

    // ── 2. aggregate the order book (rung-2): sort by priority, assert faithful permutation ──
    let mut agg_idx: Vec<usize> = (0..rows.len()).collect();
    agg_idx.sort_by_key(|&i| rows[i].priority);
    let aggregate_faithful = {
        let mut sub: Vec<u8> = rows.iter().map(|r| r.node.intent_id[0]).collect();
        let mut ag: Vec<u8> = agg_idx.iter().map(|&i| rows[i].node.intent_id[0]).collect();
        sub.sort_unstable();
        ag.sort_unstable();
        let sorted = agg_idx
            .windows(2)
            .all(|w| rows[w[0]].priority <= rows[w[1]].priority);
        sub == ag && sorted
    };
    let aggregated: Vec<AggRow> = agg_idx
        .iter()
        .map(|&i| {
            let r = &rows[i];
            AggRow {
                trader: r.trader.clone(),
                offer_asset: dict.name_of(r.node.exchange.offer_asset[0]),
                offer_amount: r.node.exchange.offer_amount,
                want_asset: dict.name_of(r.node.exchange.want_asset[0]),
                want_min: r.node.exchange.want_min_amount,
                priority: r.priority,
            }
        })
        .collect();

    // ── 3. match via the REAL solver over the aggregated book ──
    let nodes: Vec<IntentNode> = agg_idx.iter().map(|&i| rows[i].node.clone()).collect();
    let solver = RingSolver::new(5);
    let graph = solver.build_graph(&nodes);
    let rings = solver.find_rings(&graph);
    let two_cycles = rings.iter().filter(|r| r.participants.len() == 2).count();

    // The matcher's best clearing (find_rings sorts by score = participant count, descending).
    let ring: Option<RingTrade> = rings.into_iter().next();

    // Helpers over the ORIGINAL rows (name lookups by creator / intent id).
    let name_of_creator = |c: &CommitmentId| -> String {
        rows.iter()
            .find(|r| &r.node.creator == c)
            .map(|r| r.trader.clone())
            .unwrap_or_else(|| "?".into())
    };
    let name_of_cellbyte = |b: u8| -> String {
        rows.iter()
            .find(|r| r.creator_byte == b)
            .map(|r| r.trader.clone())
            .unwrap_or_else(|| "?".into())
    };

    // No clearing ring: honest empty result (every order rests).
    let Some(ring) = ring else {
        let allocations: Vec<Alloc> = rows
            .iter()
            .map(|r| Alloc {
                trader: r.trader.clone(),
                rested: true,
                sent_asset: dict.name_of(r.node.exchange.offer_asset[0]),
                sent: 0,
                offer: r.node.exchange.offer_amount,
                recv_asset: dict.name_of(r.node.exchange.want_asset[0]),
                received: 0,
                want_min: r.node.exchange.want_min_amount,
                ir: false,
                budget: true,
            })
            .collect();
        let out = Cleared {
            ok: false,
            aggregated,
            aggregate_faithful,
            two_cycles,
            ring: None,
            allocations,
            conservation: vec![],
            limits_ok: false,
            conserves_ok: false,
            reject: None,
            provenance: "solver.rs found no clearing ring over the revealed book".into(),
        };
        println!("{}", serde_json::to_string(&out).unwrap());
        return;
    };

    let ring_legs: Vec<Leg> = ring
        .settlements
        .iter()
        .map(|s| Leg {
            from_trader: name_of_creator(&s.from),
            to_trader: name_of_creator(&s.to),
            asset: dict.name_of(s.asset[0]),
            amount: s.amount,
        })
        .collect();
    let ring_out = Ring {
        participants: ring
            .settlements
            .iter()
            .map(|s| name_of_creator(&s.from))
            .collect(),
        legs: ring_legs,
        score: ring.score,
    };

    // ── 4. settle through the VERIFIED executor (lower → fold each leg through recKExecAsset) ──
    let anchor = CellId::from_bytes([0x9Du8; 32]);
    let intent = Intent::RingSettlement {
        rings: vec![ring.clone()],
        anchor,
        solver_id: [0xAB; 32],
        validity_proof_hash: [0xCD; 32],
    };
    let plan = match lower(intent, &LoweringContext::default()) {
        Ok(p) => p,
        Err(e) => fail(&format!("lowering the matched ring failed: {e:?}")),
    };
    let sealed = seal_plan_uniform(
        plan,
        anchor,
        0,
        Authorization::Signature([0u8; 32], [0u8; 32]),
    );
    let (pre, post) = match settle_fulfillment_verified(&sealed, &ring.settlements) {
        Ok(pp) => pp,
        Err(e) => fail(&format!("verified settlement rejected the ring: {e}")),
    };
    let legs = match extract_legs(&sealed, &ring.settlements) {
        Ok(l) => l,
        Err(e) => fail(&format!(
            "leg extraction diverged from the lowered turn: {e}"
        )),
    };

    // ── 5. allocations off the VERIFIED post-ledger + limit checks ──
    let mut allocations: Vec<Alloc> = Vec::with_capacity(rows.len());
    let mut limits_ok = true;
    for r in &rows {
        let participates = ring.participants.contains(&r.node.intent_id);
        if !participates {
            allocations.push(Alloc {
                trader: r.trader.clone(),
                rested: true,
                sent_asset: dict.name_of(r.node.exchange.offer_asset[0]),
                sent: 0,
                offer: r.node.exchange.offer_amount,
                recv_asset: dict.name_of(r.node.exchange.want_asset[0]),
                received: 0,
                want_min: r.node.exchange.want_min_amount,
                ir: false,
                budget: true,
            });
            continue;
        }
        let cell = r.creator_byte;
        let got_asset = r.node.exchange.want_asset;
        let gave_asset = r.node.exchange.offer_asset;
        let received = post.get(cell, &got_asset) - pre.get(cell, &got_asset);
        let sent = pre.get(cell, &gave_asset) - post.get(cell, &gave_asset);
        let ir = received >= r.node.exchange.want_min_amount as i128;
        let budget = sent <= r.node.exchange.offer_amount as i128;
        if !ir || !budget {
            limits_ok = false;
        }
        allocations.push(Alloc {
            trader: r.trader.clone(),
            rested: false,
            sent_asset: dict.name_of(gave_asset[0]),
            sent,
            offer: r.node.exchange.offer_amount,
            recv_asset: dict.name_of(got_asset[0]),
            received,
            want_min: r.node.exchange.want_min_amount,
            ir,
            budget,
        });
    }

    // ── per-asset conservation over the verified settle ──
    let mut conservation: Vec<Conservation> = Vec::new();
    let mut conserves_ok = true;
    for a in touched_assets(&legs) {
        let before = pre.total_asset(&a);
        let after = post.total_asset(&a);
        let ok = before == after;
        if !ok {
            conserves_ok = false;
        }
        conservation.push(Conservation {
            asset: dict.name_of(a[0]),
            in_: before,
            out: after,
            ok,
        });
    }

    // ── 6. reject polarity — drain leg 0's sender one short; the verified kernel MUST refuse ──
    let reject = if legs.is_empty() {
        None
    } else {
        let mut starved: VerifiedLedger = funded_ledger(&legs);
        let victim = legs[0].clone();
        starved.set(victim.from, &victim.asset, victim.amount - 1);
        match settle_ring_verified(&starved, &legs) {
            Err(VerifiedSettleError::LegRejected { index, .. }) => Some(Reject {
                victim: name_of_cellbyte(victim.from),
                asset: dict.name_of(victim.asset[0]),
                starved_to: victim.amount - 1,
                need: victim.amount,
                refused_at: index as i64,
                aborted: true,
                settled_legs: 0,
            }),
            other => fail(&format!(
                "reject-polarity check: an over-debiting ring MUST be refused; got {other:?}"
            )),
        }
    };

    let out = Cleared {
        ok: aggregate_faithful
            && limits_ok
            && conserves_ok
            && reject.as_ref().is_some_and(|r| r.aborted),
        aggregated,
        aggregate_faithful,
        two_cycles,
        ring: Some(ring_out),
        allocations,
        conservation,
        limits_ok,
        conserves_ok,
        reject,
        provenance: "solver.rs (Johnson circuits + Shapley–Scarf TTC) → verified_settle.rs \
                     (each leg folded through the proved recKExecAsset kernel)"
            .into(),
    };
    println!("{}", serde_json::to_string(&out).unwrap());
}
