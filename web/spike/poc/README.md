# In-browser dregg node — real mesh participant (`node.html`)

`node.html` + `mesh.mjs` + `drive-node-headless.mjs` turn the executor POC
into a **real in-browser participant on the live mesh**. The page:

1. **read-syncs** live mesh state from a node over its HTTP API
   (`/status`, `/api/federations`, `/api/blocks`, `/api/receipts`,
   `/api/cells`, `/api/tokens`, `/api/intents`) — the blocklace / federation /
   ledger projections (real DAG height, block count, consensus liveness,
   federation roots);
2. **locally verifies** two turns itself with the wasm-compiled verified Lean
   executor (`execFullForestG` / `dregg_exec_full_forest_auth`) — the verdict
   is computed client-side, not trusted from the node;
3. **relays a node-shaped turn** (`POST /turn/submit`, the real
   `SubmitTurnRequest` shape) and reports the honest outcome.

```
node web/spike/poc/drive-node-headless.mjs [endpoint]   # default: live devnet
```

Drives real headless Chrome over CDP (no puppeteer/npm). The page fetches the
node **cross-origin**; the node's `/api/*` responses carry permissive CORS, so
this is a genuine browser→node interaction. Observed against a healthy node:

```
[node] connection   : ● online (7/7 reads ok)
[node] local-verify : ✓ genuine turn COMMITs (conserved), forged turn ROLLs BACK.
[node] mesh sync    : {"reachable":7,"total":7,"online":true}
[node] submit       : rejected by auth gate (HTTP 403) — expected for an anonymous
                      browser; supply an operator bearer token to relay.
[node] verdict      : PASS (verified executor ran in-browser)
```

## What is REAL vs what is NOT (honest capability matrix)

| capability | status | via | note |
|---|---|---|---|
| **read-sync** | REAL | node HTTP API (`/status`, `/api/*`) | blocklace/federation/ledger projections, polled; works cross-origin |
| **local-verify** | REAL | wasm `execFullForestG` | the proved gated complete-turn executor, run client-side |
| **submit** | best-effort (gated) | `POST /turn/submit` | node parses the well-formed turn then gates inclusion on operator auth: **403** (locked cipherclerk) / **401** (devnet `require_auth` bearer). An anonymous browser cannot make a turn COMMIT — by design. |
| **full gossip** | NOT in browser | libp2p/QUIC blocklace gossip | no browser transport binding; the page participates via the API relay, **not** by joining the gossip mesh directly. |

The load-bearing in-browser guarantee is **local-verify**: it runs fully
client-side and is resilient to a flaky/unreachable node (the live devnet
backend was observed timing out while its static/proxy front stayed up; the
page reports `○ node API unreachable` and still PASSes local verification).

`?endpoint=https://node.example` selects the node (devnet is the default).

### Known devnet CORS limitation (real, measured)

Cross-origin **read-sync was verified end-to-end against a local node**
(`http://127.0.0.1:8420`, 7/7 reads ok). Against the **deployed devnet**
(`devnet.dregg.fg-goose.online`) the browser reads currently fail with
`TypeError: Failed to fetch` because the response carries **duplicate
`Access-Control-Allow-Origin` headers** — one `*` from the fronting proxy and
one origin-echo from the node's own CORS middleware. Browsers reject duplicate
ACAO as a CORS violation. This is a devnet *proxy* misconfiguration (the proxy
and the node should not both emit CORS), not a limitation of the in-browser
node — the page reports it honestly as `○ node API unreachable`. Fix belongs in
the devnet deploy (`docker/Caddyfile` / `site-nginx.conf` or the node's
`--cors-origin` so only one layer sets the header). Until then, point the page
at a node that sets CORS exactly once (e.g. a direct local node).

---

# POC — the REAL verified Lean executor runs in a browser

`index.html` + `drive-headless.mjs` prove that `execFullForestG`
(`@[export] dregg_exec_full_forest_auth`, the PROVED gated complete-turn
executor) runs **in an actual browser engine**, not just under Node:

```
node web/spike/poc/drive-headless.mjs
```

This serves `web/spike` and drives **real headless Chrome** over the DevTools
protocol (no puppeteer/npm). Observed:

```
[poc] status: Lean runtime booted in 237 ms. Running turns…
[poc] turn ① post-state: …"bal":[[0,0,70],[1,0,35]]…,"loglen":1,"ok":1   (COMMIT, conserved)
[poc] turn ② post-state: …"bal":[[0,0,100],[1,0,5]]…,"loglen":0,"ok":0    (ROLLBACK, unchanged)
[poc] verdict: PASS
```

Prereq: `web/spike/out-web/dregg.{mjs,wasm}` (the ES6 browser-shape build,
produced by `build-executor-wasm.sh` + the browser-variant link; ~41 MB wasm).
These are reproducible build artifacts (gitignored).

## Why the wasm is ~41 MB (the bloat, measured)

`Dregg2.Exec.FFI`'s transitive **import** closure is **8,757 modules — 8,099
of them Mathlib, incl. 342 `Mathlib.Tactic.*`** (the whole tactic/elaborator
framework). Lean runs every imported module's `initialize_` at boot, so that
code stays live regardless of `--gc-sections` (init-reachable ≠ compile-time-
only). 16,577 of the linked symbols are `Mathlib.CategoryTheory.*` alone —
pure proof scaffolding from `Dregg2.Core`'s monoidal-category imports, with
zero runtime relevance to a balance transfer.

The tactic imports (`Mathlib.Tactic`, `.Ring`, `.Tauto` in `Exec.Kernel`,
`CryptoKernel`, `Tactics`, `Core`, …) are **proof-time only** — the executor
never invokes `ring`/`tauto` at runtime. They are in the closure because the
runtime defs and the proofs live in the SAME modules.

## The size ladder (module-closure measured)

| Variant | module closure | tactic modules | est. wasm |
|---|---|---|---|
| current FFI | 8,757 | 342 | ~41 MB (measured) |
| trim Dregg2-level tactic imports (state still `Finset`) | ~1,754 | 216 | est. ~10–15 MB |
| runtime state uses `List`/`HashSet` not mathlib `Finset` | ~12 | 0 | **~1–2 MB** (tiny regime, measured for tiny.wasm) |

The hard floor for *touching mathlib `Finset` at all* is ~1,754 modules /
~216 tactic modules — mathlib's own `Finset.Basic` imports tactics at the top.
Single-digit-MB requires moving the **runtime** state representation off
mathlib `Finset` (keep `Finset` in the spec/proofs via a refinement); that's a
real refactor, not a link flag.
