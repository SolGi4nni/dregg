# drex-web-v2 — the DrEX terminal (primary surface)

The primary DrEX frontend. Preact + htm + `@preact/signals`, bundled by esbuild
into one self-contained file (zero runtime CDN requests). The extension
(`window.dregg`) is the identity + wallet + signer; this app is the orchestrator.

**Reconciliation (2026-07-17):** the v1 demo's (`drex-web/`, `:8781`) full
endpoint surface is ported here — v2 is no longer a partial seed. `drex-web/`
remains as the legacy scripted walkthrough (wallet-wasm sealed-bid flow + the
headless gate); new UI work lands here.

The full overhaul plan — assessment, architecture, per-mechanism / tier /
sealed-bid / composition / wallet / multichain component design, and the
Open-first phased sequence with per-phase ember-gated deploy dependencies — is
in `docs/deos/DREX-FRONTEND-OVERHAUL.md`.

This runs on **`:8782`** and does not disturb `:8781` (legacy), `:8790`
(offerings), or the games deploy.

## What is wired REAL

- **App shell** — header, node probe, engine report (`GET /engines`: which real
  binary backs each route right now), extension/wallet status, light/dark toggle.
- **Wallet handshake** — detect the installed extension (`window.dregg` /
  `dregg:ready`), connect via `dregg.authorize`, pull the EVM address. Honest
  install prompt when no extension is present (no faked wallet).
- **Tier-dial (first-class)** — Open / Shielded / Dark, with the live
  viewer-lens: the same cleared ring drawn three ways (open = full flows,
  shielded = blurred amounts, dark = 🔒 sealed), reusing `drex-web/drex-viz.js`.
  Shielded/Dark are labelled previews (not live with real money).
- **Open-tier ring order-entry** — build a real batch (validated entry) →
  `POST /clear` → the REAL matcher (`drex_clear`: solver.rs ring match →
  verified_settle.rs kernel fold) → the real cleared result (ring, allocations,
  per-asset conservation, reject-polarity).
- **Shielded Cert-F circulation** — the same batch → `POST /clear-shielded` →
  the REAL fhEgg engine (`fhegg_clear`: PDHG circulation + Cert-F primal-dual
  certificate + the verified AIR gate, honest ACCEPT vs tampered REJECT), then
  `POST /prove-shielded` → the REAL reveal-nothing STARK (`cert_f_prove`): the
  world view carries only the proof + wᵀf; the witness (f/π/s) never leaves the
  server. Both engines keep **honest not-built fallbacks** (the route answers
  with the build command; nothing is faked).
- **Sealed-bid commit→reveal** — the two-phase ceremony routed through the real
  extension (`dregg.sealedBid.commit` / `.reveal`: keccak256 + EIP-712 +
  secp256k1). The on-chain escrow post is labelled deploy-gated.
- **Live-node settle + proof-receipt** — `POST /settle` lands the cleared batch
  as real per-trader Transfer turns on a live dregg node and reads back the turn
  hash, the STARK proof (or the honest committed-but-unattested state), finality,
  pre→post ledger state, and each trader's balance **from the node**. Rendered as
  the proof-receipt card with the re-check pointer (`/api/turn/{h}/proof`).
- **Session receipt ledger** — one row per completed action (clear / shielded
  clear / prove / settle / sealed commit / reveal), built only from real endpoint
  results. Every move is a receipt.
- **Mechanism rail + composition strip** — all 8 mechanisms and the
  deposit→shield→clear→settle journey, each with its honest live-state / grade.

## Run

```
npm install          # 6-package tree: preact, htm, @preact/signals, esbuild
npm run build        # esbuild → dist/app.js
node serve.mjs       # → http://127.0.0.1:8782
node serve.mjs --check   # no-listen self-check: statics, engine binaries, node reachability
```

Engine binaries (all located local-first, honest fallback otherwise):

- `/clear` → `drex_clear` (`cargo build -p dregg-intent --bin drex_clear`), else
  the prebuilt matcher on the build host over ssh (`DREX_REMOTE`, default
  `persvati`).
- `/clear-shielded` → `fhegg_clear` (`cargo build --release --bin fhegg_clear`
  in `fhegg-solver/` — a standalone crate with its own target dir). Local only.
- `/prove-shielded` → `cert_f_prove`
  (`cargo build --release -p dregg-circuit-prove --bin cert_f_prove`). Local only.
- `/settle` → a live dregg node (`dregg-node run --port 8420 --enable-faucet
  --prove-turns`); without one the UI shows the honest offline fallback and keeps
  the labelled local clear.

## Dev (buildless)

`htm` needs no compiler, so `src/` is plain ESM. `npm run build -- --watch`
rebuilds `dist/app.js` on change while `node serve.mjs` serves.

## Honest scope

Live end-to-end today: the Open-tier ring clear, the shielded Cert-F clearing +
reveal-nothing STARK (engine-gated by which binaries are built — surfaced, never
faked), the sealed-bid ceremony's cryptography (extension-signed), and the
solo-node settle. The shielded TIER remains a labelled preview (the solver sees
plaintext; input privacy via note commitments is the named lane), the Dark tier
is FRONTIER, the on-chain sealed-bid escrow and the five not-yet-wired mechanisms
are honestly labelled. Nothing not-yet-live is shown as live with real money.
Nothing here is deployed/hosted — that is a separate, ember-gated lane.
