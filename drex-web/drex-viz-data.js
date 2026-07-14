// drex-viz-data.js — REAL engine snapshots for the DrEX visualization layer.
//
// ┌───────────────────────────────────────────────────────────────────────────┐
// │ NOT fabricated. Every field below is the VERBATIM stdout of a real fhEgg    │
// │ engine binary, captured by piping a sealed batch through it. The exact      │
// │ commands are recorded in `.provenance` on each object and reproduced here   │
// │ so anyone can regenerate byte-for-byte:                                     │
// │                                                                             │
// │   # the multi-asset barter ring (circulation + Cert-F + verified AIR):      │
// │   cargo build -p fhegg-solver --bin fhegg_clear   # in fhegg-solver/        │
// │   echo '<the demoBook orders>' | fhegg-solver/target/debug/fhegg_clear      │
// │                                                                             │
// │   # the single-pair uniform-price call auction (fold + one crossing):       │
// │   cargo build -p fhegg-solver --bin fhegg_uniform # in fhegg-solver/        │
// │   echo '<the GOLD/ART book>' | fhegg-solver/target/debug/fhegg_uniform      │
// │                                                                             │
// │ drex-viz.html uses these as the offline/standalone snapshot; when served    │
// │ by serve.mjs it re-fetches the ring/certificate/tiers LIVE from the         │
// │ existing POST /clear-shielded endpoint (same engine, live run) and only     │
// │ falls back to this baked snapshot when opened as a bare file.               │
// └───────────────────────────────────────────────────────────────────────────┘

// ── The multi-asset barter ring — fhegg_clear over the canonical DrEX demoBook.
// Ada(GOLD→ART), Bram(ART→WINE), Cyl(WINE→GOLD) close a 3-ring; Del(SILVER→PEARL)
// has no return leg so it rests. Every leg clears 50 (bounded by Bram's ART cap
// 50 — the binding edge). Cert-F: wᵀf = 300 = dual cᵀs, gap ≈ 0, ‖Af‖∞ = 0.
export const RING = {
  provenance: "echo '[{\"trader\":\"Ada\",\"offerAsset\":\"GOLD\",\"offerAmount\":100,\"wantAsset\":\"ART\",\"wantMin\":10,\"priority\":3},{\"trader\":\"Bram\",\"offerAsset\":\"ART\",\"offerAmount\":50,\"wantAsset\":\"WINE\",\"wantMin\":20,\"priority\":1},{\"trader\":\"Cyl\",\"offerAsset\":\"WINE\",\"offerAmount\":80,\"wantAsset\":\"GOLD\",\"wantMin\":40,\"priority\":2},{\"trader\":\"Del\",\"offerAsset\":\"SILVER\",\"offerAmount\":30,\"wantAsset\":\"PEARL\",\"wantMin\":5,\"priority\":4}]' | fhegg-solver/target/debug/fhegg_clear",
  engine: "fhEgg single-phase clearing (fhegg-solver: PDHG circulation + Cert-F)",
  mechanism: "volume-max trade circulation  max wᵀf  s.t. Af=0, 0≤f≤c  (the convex clearing family; uniform-price is its linear-utility floor)",
  assets: ["ART", "GOLD", "WINE", "PEARL", "SILVER"],
  nodes: 5,
  edges: 4,
  iters: 4000,
  orders: [
    { trader: "Ada", offerAsset: "GOLD", offerAmount: 100, wantAsset: "ART", wantMin: 10, priority: 3, clearedFlow: 50.0, filled: true },
    { trader: "Bram", offerAsset: "ART", offerAmount: 50, wantAsset: "WINE", wantMin: 20, priority: 1, clearedFlow: 50.0, filled: true },
    { trader: "Cyl", offerAsset: "WINE", offerAmount: 80, wantAsset: "GOLD", wantMin: 40, priority: 2, clearedFlow: 50.0, filled: true },
    { trader: "Del", offerAsset: "SILVER", offerAmount: 30, wantAsset: "PEARL", wantMin: 5, priority: 4, clearedFlow: 0.0, filled: false },
  ],
  certificate: { clearedVolume: 300.0, dualObjective: 300.0, dualityGap: 0.0, conservationResidual: 0.0, conserves: true, primalBoxed: true, sNonneg: true, dualFeasible: true, gapOk: true, valid: true },
  air: { constraints: 22, terms: 40, witnessCells: 13, accept: true, violated: [] },
  tamper: { what: "break conservation: add 3 units to edge 0 with no return leg (Af≠0)", accept: false, violated: ["conservation", "conservation"] },
  starkStage: {
    status: "NAMED, not run in this demo",
    revealNothingFloor: "the world sees only a STARK over this SAME AIR; the reveal-nothing floor rests on its zero-knowledge",
    wireEntryPoint: "circuit-prove/src/cert_f_air.rs::{from_solution_json → prove_cert_f → verify_cert_f}",
    hides: ["f (the primal flow — who cleared how much)", "π (the node potentials / dual prices)", "s (the dual slacks)"],
  },
  tiers: [
    { tier: "solver-sees (Stage-1, untrusted)", sees: "the plaintext batch — every order, to clear it maximally fast" },
    { tier: "world-sees (the shielded output)", sees: "only the proof: a fair batch cleared, per-asset conservation held — never who traded what (once the STARK stage is wired)" },
  ],
  // The RAW Cert-F certificate — the exact (n, m, edges, w, c, f, π, s, ε) wire.
  // edges are (tail=wantAsset, head=offerAsset) node indices into `assets`.
  solverCert: {
    n_nodes: 5, m_edges: 4,
    edges: [[0, 1], [2, 0], [1, 2], [3, 4]],
    w: [3.0, 1.0, 2.0, 4.0],
    c: [100.0, 50.0, 80.0, 30.0],
    f: [50.0, 50.0, 50.0, 0.0],
    pi: [-2.6666666666666714, 0.33333333333333215, 2.3333333333333393, -2.0, 2.0],
    s: [0.0, 6.000000000000011, 0.0, 0.0],
    epsilon: 0.5, primal_obj: 300.0, dual_obj: 300.0000000000005, duality_gap: 5.115907697472721e-13, feas_residual: 0.0,
  },
};

// ── The single-pair uniform-price call auction — fhegg_uniform over a GOLD/ART
// book. Three bids (limits 0.65/0.60/0.55), three asks (0.45/0.50/0.60). Demand
// (suffix scan, non-increasing) meets supply (prefix scan, non-decreasing); the
// volume-maximising crossing is p* = 0.60 with V* = 160. Cyl's 0.55 bid rests
// (won't pay 0.60); the asks fill pro-rata to 160 (largest-remainder, conserving).
export const UNIFORM = {
  provenance: "echo '{\"pair\":\"GOLD/ART\",\"k\":10,\"priceGrid\":[\"0.30\",…,\"0.75\"],\"orders\":[{\"trader\":\"Ada\",\"side\":\"bid\",\"qty\":100,\"limit\":7},{\"trader\":\"Bram\",\"side\":\"bid\",\"qty\":60,\"limit\":6},{\"trader\":\"Cyl\",\"side\":\"bid\",\"qty\":40,\"limit\":5},{\"trader\":\"Del\",\"side\":\"ask\",\"qty\":80,\"limit\":3},{\"trader\":\"Eve\",\"side\":\"ask\",\"qty\":50,\"limit\":4},{\"trader\":\"Fox\",\"side\":\"ask\",\"qty\":70,\"limit\":6}]}' | fhegg-solver/target/debug/fhegg_uniform",
  engine: "fhEgg uniform-price call auction (fhegg-solver::clearing: fold + one crossing)",
  mechanism: "uniform-price aggregation  p* = argmax_j min(D(j), S(j)),  V* = min(D(p*), S(p*))  (the fhEgg kernel at T=1; an aggregation, not a matching)",
  pair: "GOLD/ART",
  k: 10,
  priceGrid: ["0.30", "0.35", "0.40", "0.45", "0.50", "0.55", "0.60", "0.65", "0.70", "0.75"],
  curves: {
    demand: [200, 200, 200, 200, 200, 200, 160, 100, 0, 0],
    supply: [0, 0, 0, 80, 130, 130, 200, 200, 200, 200],
    matchable: [0, 0, 0, 80, 130, 130, 160, 100, 0, 0],
  },
  crossed: true,
  clearingPriceIndex: 6,
  clearingPriceLabel: "0.60",
  clearedVolume: 160,
  buyVolume: 160,
  sellVolume: 160,
  conserves: true,
  orders: [
    { trader: "Ada", side: "bid", qty: 100, limit: 7, limitLabel: "0.65", fill: 100, active: true, filled: true },
    { trader: "Bram", side: "bid", qty: 60, limit: 6, limitLabel: "0.60", fill: 60, active: true, filled: true },
    { trader: "Cyl", side: "bid", qty: 40, limit: 5, limitLabel: "0.55", fill: 0, active: false, filled: false },
    { trader: "Del", side: "ask", qty: 80, limit: 3, limitLabel: "0.45", fill: 64, active: true, filled: true },
    { trader: "Eve", side: "ask", qty: 50, limit: 4, limitLabel: "0.50", fill: 40, active: true, filled: true },
    { trader: "Fox", side: "ask", qty: 70, limit: 6, limitLabel: "0.60", fill: 56, active: true, filled: true },
  ],
  tiers: [
    { tier: "solver-sees (Stage-1, untrusted)", sees: "the plaintext book — every sealed bid/ask, folded into the curves" },
    { tier: "world-sees (the shielded output)", sees: "only the proof + the public clearing price p* and volume V* — never who bid what (once the STARK/FHE stage is wired)" },
  ],
};
