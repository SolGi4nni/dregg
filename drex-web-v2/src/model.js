// model.js — the DrEX protocol surface as data. The 8-mechanism family, the
// three privacy tiers, and the deposit→shield→clear→settle composition stages —
// each as a plain object the UI renders, with an HONEST `live` flag reflecting
// what is actually wired TODAY (per docs/deos/USER-FACING-STACK-REALITY.md and
// DREGGFI-PRIVACY-TIERS.md). Nothing here decides soundness; it decides what the
// UI is allowed to present as a live control vs. a labelled, deploy-gated one.

// ── The three privacy tiers (DREGGFI-PRIVACY-TIERS.md §1) ──
// `live` = is there a real endpoint today. Only OPEN is fully live end-to-end.
export const TIERS = [
  {
    id: 'open', name: 'Open', order: 2,
    tagline: 'Public book, fair-by-proof.',
    posture: 'Orders are visible; the clearing is a STARK of correctness over a public book. No privacy — but no unfairness either: uniform-price / ring clears are machine-checked fair, conserving, no-mint.',
    whoSees: { world: 'every order + every fill', solver: 'everything', you: 'everything' },
    live: true,
    grade: 'NOW',
  },
  {
    id: 'shielded', name: 'Shielded', order: 1,
    tagline: 'Private from the world; the solver sees.',
    posture: 'Value, owner, offer/want, and allocation live only in the STARK witness under the hiding PCS; the public transcript reveals nothing but [nullifier, root, value-binding]. One computing party (the solver) sees plaintext — this is NOT no-viewer, and is never sold as such.',
    whoSees: { world: 'nothing but the proof + minimal public inputs', solver: 'plaintext orders (one party)', you: 'your own order' },
    live: false,
    grade: 'BUILDING',
    deployDeps: ['Poseidon2 Merkle swap (STARK membership un-forgeable)', 'public signed-data RPC (/bid + /reveal)', 'reveal-nothing theorem (RESEARCH)'],
  },
  {
    id: 'dark', name: 'Dark', order: 0,
    tagline: 'Adversarial no-viewer (t-of-n threshold).',
    posture: 'The clearing runs entirely on ciphertexts; no solver or enclave ever sees an order. Below a t-of-n threshold no coalition learns any order — by the math, not a policy. Only (p*, V*) opens. Bounded to the FHE envelope (uniform-price / Cert-F, ~32–512 orders/pair, minute cadence).',
    whoSees: { world: 'only (p*, V*)', solver: 'nothing below threshold', you: 'your own order' },
    live: false,
    grade: 'FRONTIER',
    deployDeps: ['persistent n-party MPC federation (today: solo committee-of-one)', 'PQ commitment cutover (DLog→Poseidon2)', 'production partial-decrypt-into-shares'],
  },
];

// ── The 8-mechanism family (fhegg-solver + the ring matcher) ──
// `endpoint` names the REAL surface; `live` is true only where a real endpoint
// serves it TODAY. `tier` = the most-private tier the mechanism can honestly run
// at (DREGGFI-PRIVACY-TIERS.md §3, the fhIR tier-as-type table).
export const MECHANISMS = [
  {
    id: 'ring', name: 'Multilateral ring / TTC', family: 'matcher',
    blurb: 'The general intent-matcher: Johnson elementary circuits + Shapley–Scarf top-trading-cycles. Clears rings no pairwise swap can. This is the OPEN-tier clear that is deployable now.',
    orderShape: 'ring',          // offer asset+amount → want asset+min, priority
    endpoint: '/clear', live: true, tier: 'open',
  },
  {
    id: 'uniform', name: 'Uniform-price call auction', family: 'fhegg',
    blurb: 'The fhEgg base case: an aggregation (fold + one crossing), not a matching. One clearing price per pair — value-neutral, envy-free, no-arbitrage. FHE-tractable, so the most-private tier it reaches is DARK.',
    orderShape: 'limit',         // side, quantity, limit price
    endpoint: '/clear-shielded', live: false, tier: 'dark',
  },
  {
    id: 'circulation', name: 'Cert-F circulation clearing', family: 'fhegg',
    blurb: 'Volume-maximizing circulation over a convex program (PDHG), with a primal-dual Cert-F certificate the verified AIR re-checks. Partial fills in [0,1]. Runs shielded today via /clear-shielded (plaintext cert); the reveal-nothing STARK wrap is /prove-shielded.',
    orderShape: 'ring',
    // `live`: BOTH routes are served by v2's serve.mjs (ported from :8781). The
    // engine binaries keep their honest not-built fallbacks; the TIER itself
    // stays a labelled preview (solver-sees plaintext; not live with real money).
    endpoint: '/clear-shielded', live: true, tier: 'shielded',
  },
  {
    id: 'fisher', name: 'Fisher market equilibrium', family: 'fhegg',
    blurb: 'Budget-weighted market equilibrium — each trader spends a budget across goods at equilibrium prices. Verified clearing; engine built (fisher.rs), runner bin not yet wired.',
    orderShape: 'budget',        // budget + per-good utility weights
    endpoint: null, live: false, tier: 'shielded',
  },
  {
    id: 'discriminatory', name: 'Discriminatory (pay-as-bid)', family: 'fhegg',
    blurb: 'Pay-as-bid auction — each winning bid pays its own price (vs. uniform). The other pole of the sealed-bid auction family.',
    orderShape: 'limit',
    endpoint: null, live: false, tier: 'shielded',
  },
  {
    id: 'cfmm', name: 'CFMM optimal routing', family: 'fhegg',
    blurb: 'Convex routing over a public pool curve with private amounts. Engine built (cfmm.rs); public curve, hidden trade size ⇒ most-private tier SHIELDED.',
    orderShape: 'route',         // in asset+amount → out asset, min-out, pools
    endpoint: null, live: false, tier: 'shielded',
  },
  {
    id: 'pricecert', name: 'Price-Cert derivatives', family: 'fhegg',
    blurb: 'State-price LP (European/basket/Asian, barrier, futures, perps) + superhedging dual; American = Snell-envelope LP. One certificate re-checks every clause; an arbitrage market is REJECTED. Runs today via /offering/derivatives (offerings surface).',
    orderShape: 'derivative',    // payoff legs over underlyings + strikes
    endpoint: '/offering/derivatives', live: false, tier: 'dark',
  },
  {
    id: 'package', name: 'Package / combinatorial (AON)', family: 'fhegg',
    blurb: 'All-or-none combinatorial clearing of indivisible bundles + a certified near-optimality bound (α = W/UB). Feasibility ALWAYS proven; exact optimum stays NP-hard. Runs today via /offering/package.',
    orderShape: 'package',       // bundle of (asset, qty) legs, AON, reserve
    endpoint: '/offering/package', live: false, tier: 'shielded',
  },
  {
    id: 'qp', name: 'Portfolio / Markowitz QP', family: 'fhegg',
    blurb: 'Quadratic-program portfolio optimization (ADMM/OSQP, one public KKT factor). Private covariance ⇒ private matrix ⇒ tier SHIELDED. Engine built (qp.rs), runner bin not yet wired.',
    orderShape: 'portfolio',     // target return, per-asset bounds, covariance ref
    endpoint: null, live: false, tier: 'shielded',
  },
];

// ── The deposit→shield→clear→settle composition (SHIELDED-DEPOSIT-BRIDGE.md) ──
// Rendered as a guided journey; each stage carries its honest grade.
export const COMPOSITION = [
  { id: 'deposit', name: 'Deposit',  verb: 'lock a real token, attest it (light client), mint a shielded note', grade: 'EXISTS (glue PoC); escrow contract stub', live: false, phase: 3 },
  { id: 'shield',  name: 'Shield',   verb: 'the note sits in the pool — value+asset hidden, nullifier-gated, undrainable', grade: 'EXISTS (Lean-proven)', live: false, phase: 3 },
  { id: 'clear',   name: 'Clear',    verb: 'match the notes privately — reveal only (p*, V*)', grade: 'EXISTS (one seam: note↔order adapter)', live: false, phase: 3 },
  { id: 'settle',  name: 'Settle',   verb: 'wrap-adapter → on-chain, OR unshield → release', grade: 'PARTIAL (wrap wired, not yet fed a real shielded turn)', live: false, phase: 3 },
];

export const ASSETS = ['GOLD', 'ART', 'WINE', 'SILVER', 'PEARL'];
