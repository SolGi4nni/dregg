# DrEX web prototype

A clickable Dragon's EXchange, **end-to-end real**: place a sealed-bid order,
have your **wallet** (the Dragon's Egg Cipherclerk wasm) **really sign it and
really prove** you can cover it, then watch the batch clear through the **real
matcher** — `intent/src/solver.rs` (Johnson circuits + Shapley–Scarf TTC) →
`intent/src/verified_settle.rs` (each leg folded through the Lean-proved
`recKExecAsset` kernel) — into a fair, conserving fill. Both the wallet AND the
matcher are real; there is no mirror. Every trust claim graded PROVED / ATTESTED
/ REPLAYABLE.

The web app POSTs the batch's revealed orders to serve.mjs `/clear`, which shells
to the `drex_clear` binary (`intent/src/bin/drex_clear.rs`) — the same pipeline as
`cargo run -p dregg-intent --example drex_clear_book`. The shown clearing is the
real solver's, settled through the verified kernel.

See `DESIGN.md` for the full UX + wire. This file is how to run it.

## Prerequisite: build the real matcher once

```
cargo build -p dregg-intent --bin drex_clear
```

serve.mjs prefers the prebuilt `target/debug/drex_clear`; without it the first
`/clear` request falls back to `cargo run` (and blocks while it builds).

## Open the clickable app

```
node drex-web/serve.mjs          # → http://localhost:8781
```

Open http://localhost:8781 in a browser. The header shows
`wallet: Dragon's Egg Cipherclerk · ready` once the wasm loads (~1s). Then:

1. edit the order (or keep the defaults: sell 100 GOLD, want ≥ 10 ART, limit ½);
2. **Review & approve in cipherclerk** → the confirm-intent card pops
   (nonce-bound). Approve.
3. the flow log runs, each step badged with the real engine it ran on
   (**REAL wasm** for the wallet, **REAL solver.rs** / **REAL verified_settle.rs**
   for the matcher): sealed commit → sign order-turn (Ed25519 + hybrid ML-DSA-65
   envelope) → prove solvency (Bulletproofs+Schnorr, verified, then a tamper
   attempt rejected) → prove eligibility (anonymous).
4. **Advance batch → reveal & clear** → the sealed book reveals; the app POSTs the
   revealed orders to `/clear`, the **real** `solver.rs` matcher finds the
   multilateral ring, `verified_settle.rs` folds each leg through the proved
   kernel, and the right panel shows your fill (off the verified post-ledger) +
   the graded "why it's fair" ledger with Lean citations.

The server mounts the extension's `dregg_wasm.js` + `dregg_wasm_bg.wasm` at
`/wasm/` so the page loads the **same** wallet wasm the extension ships — the
proving is real, no mock.

## Run the gate (headless, no browser)

```
node drex-web/gate/run-gate.mjs
```

Drives the whole sealed-bid flow in Node with the real wallet wasm AND the real
matcher (it shells to the same `drex_clear` binary), and prints a `PASS`/`FAIL`
report: real signed order-turn, real solvency proof (verified + tamper-rejected),
real anonymous eligibility, the REAL cleared batch (solver.rs ring +
verified_settle.rs post-ledger), and the graded fairness ledger. This is the
authoritative REAL end-to-end gate.

## Browser self-check (real proving in a real browser)

```
node drex-web/serve.mjs &
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
  --headless=new --virtual-time-budget=20000 --dump-dom \
  http://localhost:8781/gate/browser-check.html
```

Runs `initWallet` + sign + prove + verify + tamper-check + eligibility in
headless Chrome and prints a JSON `result: "PASS"` — proof the wasm proving
executes in an actual browser, not just Node.

## Files
- `index.html` / `app.js` — the DrEX exchange UI + flow orchestration (POSTs the
  revealed orders to `/clear` for the real matcher).
- `drex-wallet.mjs` — isomorphic adapter over the real cipherclerk wasm
  (sign, prove solvency, prove eligibility, sealed commit/reveal).
- `drex-clearside.js` — the demo book fixture + the graded fairness ledger (Lean
  citations). The former JS matcher mirror was deleted; the matcher is now real.
- `serve.mjs` — dev server (mounts the wallet wasm at `/wasm/`, exposes
  `POST /clear` → the `drex_clear` binary = the real matcher + settlement).
- `../intent/src/bin/drex_clear.rs` — the thin JSON CLI: revealed orders in, the
  real cleared batch (solver.rs + verified_settle.rs) out.
- `gate/run-gate.mjs` — the headless Node gate (real wallet + real matcher).
- `gate/browser-check.html` — the in-browser proving self-check.
- `DESIGN.md` — the UX + wire deliverable.
