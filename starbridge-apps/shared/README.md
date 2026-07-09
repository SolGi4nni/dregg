# starbridge-apps/shared

**A shared JS/browser helper library for the starbridge-apps — NOT an app.**

This directory has no `Cargo.toml`, no `FactoryDescriptor`, no `CellProgram`, and installs no
slot caveats. It is the common browser-side plumbing the individual apps reuse so each app's
pages, inspectors, and turn-builders stay thin. **All policy — slot caveats, VKs, constraints,
factory descriptors — lives in the per-app Rust crates**; the JS here is the thinnest possible
shim over the in-browser `DreggRuntime` and the canonical `TurnExecutor`.

## What it provides

| File / dir | Provides |
|---|---|
| `runtime-submit.js` | the real local-preview submission path: `ensureAppCell(uriHint)` lazily mints a REAL runtime cell and maps an app's placeholder URI (`dregg://cell/...`) to its real hex id; `submitTurnSpec(turnSpec)` converts a turn-builder TurnSpec into the wasm `execute_turn` action and runs it as a real signed turn, returning a real receipt. Closes the gap where the read-only `signTurn` stub made every button fail silently — without touching the frame-embedding lane's `app-boot.js`. |
| `app-runtime-ready.js` | per-page boot helper: waits for `app-boot` to attach `window.__starbridgeAppRuntime`, creates the app's real cell + rewrites placeholder URIs on inspector elements, and installs the real `window.dregg.signTurn` (unless the extension cclerk already owns a frozen `window.dregg`). |
| `app-multi-agent.js` | REAL multi-agent + `Authorization::Custom` flows (the in-browser realization of the subscription and governed-namespace apps' Rust executor integration tests): mints a dedicated app cell from genesis + installs its canonical cell-program, creates distinct owner/publisher/consumer/voter agents (real separate cipherclerks signing real turns), and drives per-method turns through `execute_app_turn` / `execute_custom_auth_turn`. The governed-namespace commit uses a real Ed25519 threshold signature. |
| `turn-builders/` | per-app turn-builder presets (`index.js`, `nameservice.js`) — the thin JS shims that produce typed TurnSpec objects mirroring the Rust `build_*_action` builders (`AppCipherclerk::make_action`). The single JS-side source of truth for each app's turn shape; app `pages/` re-export from here. |
| `inspectors/` | the cross-app primitive web components — `<dregg-token-cap>` (a tangible capability/receipt-token view) and `<dregg-status-bar>` — plus per-app domain inspectors (`name.js`: `<dregg-name>`, `<dregg-name-registry>`). Reuses platform vocabulary (`<dregg-cell>`, `<dregg-capability>`) rather than forking it, per `site/STUDIO.md`. |
| `factories/` | JSON mirrors of `FactoryDescriptor` definitions for the in-browser runtime to load without parsing Rust. Content-addressed: any drift from the Rust source produces a different `factory_vk` and the wasm runtime refuses to load it. Today empty — the wasm runtime calls the Rust exports directly; the first mirror (`name_factory.json`) lands when a build-time generator is wired in. |

## Reading order

The per-app Rust crate is always the source of truth for policy. Start from an app's own README
(e.g. `../bounty-board/README.md`) and `src/lib.rs`; this directory is the browser-side glue those
apps share. See `site/STUDIO.md` and the STARBRIDGE-PLAN for the studio/inspector conventions
these helpers follow.
