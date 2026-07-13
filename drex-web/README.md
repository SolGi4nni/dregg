# DrEX web prototype

A clickable Dragon's EXchange: place a sealed-bid order, have your **wallet**
(the Dragon's Egg Cipherclerk wasm) **really sign it and really prove** you can
cover it, then watch the batch clear into a fair, conserving fill — every trust
claim graded PROVED / ATTESTED / REPLAYABLE.

See `DESIGN.md` for the full UX + wire. This file is how to run it.

## Open the clickable app

```
node drex-web/serve.mjs          # → http://localhost:8781
```

Open http://localhost:8781 in a browser. The header shows
`wallet: Dragon's Egg Cipherclerk · ready` once the wasm loads (~1s). Then:

1. edit the order (or keep the defaults: sell 100 GOLD, want ≥ 10 ART, limit ½);
2. **Review & approve in cipherclerk** → the confirm-intent card pops
   (nonce-bound). Approve.
3. the flow log runs, each step badged **REAL wasm** or **clear-side mirror**:
   sealed commit → sign order-turn (Ed25519 + hybrid ML-DSA-65 envelope) →
   prove solvency (Bulletproofs+Schnorr, verified, then a tamper attempt
   rejected) → prove eligibility (anonymous).
4. **Advance batch → reveal & clear** → the sealed book reveals, the multilateral
   ring clears, and the right panel shows your fill + the graded "why it's fair"
   ledger with Lean citations.

The server mounts the extension's `dregg_wasm.js` + `dregg_wasm_bg.wasm` at
`/wasm/` so the page loads the **same** wallet wasm the extension ships — the
proving is real, no mock.

## Run the gate (headless, no browser)

```
node drex-web/gate/run-gate.mjs
```

Drives the whole sealed-bid flow in Node with the real wallet wasm and prints a
`PASS`/`FAIL` report: real signed order-turn, real solvency proof (verified +
tamper-rejected), real anonymous eligibility, the cleared batch, and the graded
fairness ledger. This is the authoritative REAL-proving gate.

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
- `index.html` / `app.js` — the DrEX exchange UI + flow orchestration.
- `drex-wallet.mjs` — isomorphic adapter over the real cipherclerk wasm
  (sign, prove solvency, prove eligibility, sealed commit/reveal).
- `drex-clearside.js` — the labeled matcher/settlement mirror + fairness ledger.
- `serve.mjs` — dev server (mounts the wallet wasm at `/wasm/`).
- `gate/run-gate.mjs` — the headless Node gate.
- `gate/browser-check.html` — the in-browser proving self-check.
- `DESIGN.md` — the UX + wire deliverable.
