// drex-clearside.js — the DrEX book fixture + the graded fairness ledger.
//
// ┌─────────────────────────────────────────────────────────────────────────┐
// │ NO MIRROR. The matcher + settlement are the REAL Rust, not JS.            │
// │ The clearing shown by the app is produced by the actual pipeline:         │
// │   intent/src/solver.rs           — Johnson elementary circuits + TTC ring │
// │   intent/src/verified_settle.rs  — folds each leg through the Lean-proved │
// │                                    per-asset kernel (Exec.recKExecAsset)   │
// │   intent/src/bin/drex_clear.rs   — the thin JSON CLI the web wire calls    │
// │   intent/examples/drex_clear_book.rs — the same pipeline, runnable        │
// │ The browser POSTs the revealed orders to serve.mjs `/clear`, which shells  │
// │ to `drex_clear`; the gate (gate/run-gate.mjs) shells to it directly. This  │
// │ file now holds ONLY the demo book fixture + the fairness ledger (Lean      │
// │ citations). The former JS "clear-side mirror" matcher was DELETED.         │
// └─────────────────────────────────────────────────────────────────────────┘
//
// Isomorphic ESM: runs in the browser (app.js) and in Node (gate/run-gate.mjs).

export const ASSETS = ['GOLD', 'ART', 'WINE', 'SILVER', 'PEARL'];

// The canonical DrEX clear-book, byte-for-byte the book in
// intent/examples/drex_clear_book.rs (the 3-ring that is bilaterally STUCK,
// plus one resting order to show aggregation drops nothing). The real matcher
// (solver.rs) runs over exactly these revealed orders.
export function demoBook() {
  return [
    { trader: 'Ada',  offerAsset: 'GOLD',   offerAmount: 100, wantAsset: 'ART',   wantMin: 10, priority: 3, holdings: 120 },
    { trader: 'Bram', offerAsset: 'ART',    offerAmount: 50,  wantAsset: 'WINE',  wantMin: 20, priority: 1, holdings: 60  },
    { trader: 'Cyl',  offerAsset: 'WINE',   offerAmount: 80,  wantAsset: 'GOLD',  wantMin: 40, priority: 2, holdings: 90  },
    { trader: 'Del',  offerAsset: 'SILVER', offerAmount: 30,  wantAsset: 'PEARL', wantMin: 5,  priority: 4, holdings: 40  },
  ];
}

// The proved properties surfaced in the "why it's fair" panel, each with its
// Lean citation and a trust grade. REPLAYABLE = recomputed on THIS batch by the
// REAL pipeline (solver.rs + verified_settle.rs, via /clear) and shown checking.
// PROVED = a Lean theorem (proved for all inputs, not just this batch). ATTESTED
// = produced/attested by the wallet's real crypto.
export function fairnessLedger() {
  return [
    { id: 'aggregate',   label: 'Faithful aggregation',        detail: 'the book is a permutation of the submissions — no order dropped or inserted, sorted by price-time priority', lean: 'Market/Aggregation.lean · aggregate_sound / faithful_preserves_count', grades: ['PROVED', 'REPLAYABLE'] },
    { id: 'multilateral', label: 'Genuinely multilateral',     detail: 'no pairwise swap clears this book; only the ≥3-ring closes (bilateral market is stuck)', lean: 'Market/Clearing.lean · ringBook_bilateral_stuck / ring_pairs_refused / ringClearing', grades: ['PROVED', 'REPLAYABLE'] },
    { id: 'conserves',   label: 'Conserves per asset',         detail: 'for every asset, total in = total out across the cleared batch — nothing minted, nothing burned', lean: 'Market/Clearing.lean · clearing_conserves_per_asset · Ring.lean · settleRing_conserves', grades: ['PROVED', 'REPLAYABLE'] },
    { id: 'limits',      label: 'Respects every declared limit', detail: 'each participant receives ≥ its want_min (individual rationality) and sends ≤ its offer (budget)', lean: 'Market/Fairness.lean · clearing_respects_limits', grades: ['PROVED', 'REPLAYABLE'] },
    { id: 'reject',      label: 'Over-debit refused, atomically', detail: 'a settlement that would over-spend is refused and the whole ring aborts — no partial settlement', lean: 'Market/Fairness.lean · overdebit_refused · Ring.lean · settleRing_atomic', grades: ['PROVED', 'REPLAYABLE'] },
    { id: 'uniform',     label: 'Uniform price · no arbitrage', detail: 'on the priced rung, one clearing price per pair: value-neutral, envy-free, no improving deviation', lean: 'Market/Optimality.lean · uniform_price_no_arbitrage / uniform_price_envy_free / uniform_price_optimal', grades: ['PROVED', 'NOT-IN-THIS-BATCH'] },
    { id: 'solvent',     label: 'Pool solvent forever',         detail: 'a validity-respecting fill schedule keeps the backing pool non-negative for all time', lean: 'Market/Liquidity.lean · pool_solvent_forever / poolStep_solvent', grades: ['PROVED', 'NOT-IN-THIS-BATCH'] },
    { id: 'solvency',    label: 'Your order is solvent + non-inflating', detail: 'the wallet proved value balance (Schnorr excess) AND a Bulletproof range proof per output — your offer is covered and no negative-value wrap inflates supply', lean: 'wallet wasm · prove_conservation / verify_conservation_proof (bulletproofs v5)', grades: ['ATTESTED', 'REPLAYABLE'] },
  ];
}
