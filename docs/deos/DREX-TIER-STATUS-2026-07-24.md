# DrEX tier status, honestly, 2026-07-24 — what each of Clear/Shielded/Dark actually does today

*Lane drex-tier-audit. This is a STATUS AUDIT, not a plan. Every claim below is either (a) a
direct execution I ran this session (server started, `curl`, `cargo test`, timed), or (b) a
`file:line` citation of the code that decides the behavior. Where a doc says one thing and the
code does another, the code wins and the doc is named as stale. I did not modify
`fhegg-fhe/src/gpu_arena.rs`, `bfv_gpu.rs`, any shader, any `Cargo.toml`, or any other lane's
file — read-only audit, one new file (`git status` before and after: clean of anything but this
doc; nothing committed).*

*Read first (as instructed): `docs/deos/FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`,
`docs/deos/DREX-GPU-RESIDENCY-PLAN.md`, `docs/deos/FHEGG-SAME-OPENING-APEX.md`,
`docs/deos/THE-DARK-BAZAAR.md`, `TESTQALOG.md` tail. Their findings are cited, not repeated.*

---

## 0. The one thing to read if you read nothing else

**The CLEAR tier's flagship "list → clear → settle" journey is broken today, as of a commit
that landed 2 hours before this audit started.** `drex-web-v2`'s own baked-in sample order book
— the three orders a user sees the instant the page loads (`drex-web-v2/src/app.js:42-46`) —
fails when you click Clear. Verified by running the real dev server and posting that exact book:

```
$ curl -s -X POST http://127.0.0.1:8955/clear -H 'Content-Type: application/json' -d '
  [{"trader":"Ada","offerAsset":"GOLD","offerAmount":100,"wantAsset":"ART","wantMin":10,"priority":3},
   {"trader":"Bram","offerAsset":"ART","offerAmount":50,"wantAsset":"WINE","wantMin":20,"priority":1},
   {"trader":"Cyl","offerAsset":"WINE","offerAmount":80,"wantAsset":"GOLD","wantMin":40,"priority":2}]'
{"error":"verified settlement rejected the ring: verified-executor FFI unavailable: no verified gate registered","ok":false}
```

Root cause, precisely: commit `1b8d7827c2` ("twin-deletion sweep… fail-closed", 2026-07-24
11:43am, already in HEAD `339a4767df`) **inverted** `dregg-intent`'s ring settlement
(`intent/src/verified_settle.rs:351-388`, the `#[cfg(not(test))]` `settle_leg_authoritative`) so
the Lean-verified export is now the sole authority and an **unregistered gate REFUSES the ring**
instead of falling back to the in-process Rust fold. The commit message says so itself: `"#10
intent settle INVERTED: shadow_record_kernel_step is authoritative per leg (no gate =>
FfiUnavailable refuses the ring)"` and explicitly flags one downstream consumer that breaks
(`starbridge-apps/tussle`) — **it does not flag `drex_clear`/`drex-web-v2`, which breaks the
same way and is not named anywhere in that commit or in `TESTQALOG.md`.** This audit is the
first place that gap is named.

Why: `intent/src/bin/drex_clear.rs` (the binary `drex-web-v2/serve.mjs` shells out to for
`POST /clear`, `serve.mjs:60-67,109-111`) never calls `register_intent_verified_gate` — and
architecturally *cannot* without adding a new dependency: `dregg-intent`'s own `Cargo.toml` says
so — `"FFI-FREE BY CONSTRUCTION… A native node installs the Lean-backed gate (from
dregg-exec-lean) once at startup"` (`intent/Cargo.toml:32-37`). Only `node/src/lib.rs:609`
(`dregg_exec_lean::register_distributed_gates()`, called at real-node startup) ever registers
it. `drex_clear` is a separate, short-lived CLI process spawned per request
(`serve.mjs:89-106`) — it never talks to a node process for this decision, so a live dregg node
running alongside changes nothing. This is exactly what
`intent/tests/settle_fail_closed.rs:1-13` is a regression test *for* (its own docstring: "This
links `dregg-intent` as a NORMAL dependency… and registers NO verified gate, forcing the
no-export branch… asserts a legitimate, conserving, funded ring… is now REFUSED") — the design
is intentional and correct; `drex_clear`'s binary just hasn't been updated to satisfy it. The fix
is small and named: either link `dregg-exec-lean` into `drex_clear` and call
`register_intent_verified_gate` in its `main()`, or route `/clear` through the live node process
instead of a standalone CLI. Neither is done.

The only order book that currently "clears" through `/clear` is one with **no matching ring at
all** (`solver.rs found no clearing ring over the revealed book`, verified: a single order
returns `ok:false` cleanly, `intent/src/bin/drex_clear.rs:294-326`) — i.e., the demo works only
when there is nothing to settle. The UI itself is honest about the failure (`app.js:478`, "
Matcher error." + raw error text) and correctly gates Settle behind a real ring
(`app.js:466`: `if (!clearing.value || !clearing.value.ring) return;`) so it can't show a
misleading partial settle — the *dishonesty* risk is fully avoided; the *functionality* is not
there. `drex-web-v2/README.md:26-30` ("Open-tier ring order-entry… → the real cleared result")
is now stale against this regression and should be corrected or the README should say what this
doc says.

---

## 1. Architecture correction, before the tier table

The mandate frames "dreggnet-market `certified_clearing` / fhegg-solver settle path" and "the
drex-web-v2 frontend" as one pipeline. **They are not connected in code.** Two independent
products share the same crypto substrate (fhEgg, Cert-F, HidingFri) but nothing wires one to the
other:

- **DrEX** (`drex-web-v2`, `intent`, `fhegg-solver`, `circuit-prove`) is a multilateral
  ring/limit-order trading terminal. `drex-web-v2/serve.mjs` shells directly to standalone Rust
  binaries (`drex_clear`, `fhegg_clear`, `cert_f_prove`); it never imports `dreggnet-market`.
- **The Dark Bazaar** (`dreggnet-market`, `dreggnet-catalog`, `dreggnet-web`/`-telegram`/discord
  `market.rs`) is a game-economy sealed single-item auction house ("list an item → others bid →
  auction settles → receipt", `THE-DARK-BAZAAR.md` §1's "Sealed Exchange" hall). This is the
  actual home of a "list→bid→settle→receipt" UX journey — DrEX's orders are offer/want ring
  entries, not listings.
- `dreggnet-market::certified_clearing` (grep-verified, `dreggnet-market/src/lib.rs:45` +
  `certified_clearing.rs`, `authenticated_receipt.rs:31,109,174,241,284,307,335`) is referenced
  **only inside `dreggnet-market` itself** — no hit in `dreggnet-web`, `-telegram`, `-wechat`,
  `discord-bot`, or `drex-web-v2`. Its own module doc says why it isn't wired: *"This is an
  ADDITIVE path alongside the existing `MarketOffering` clearing — nothing in the live
  LIST/BID/SETTLE flow is rewired yet"* (`certified_clearing.rs:4-6`).

So: I audit both, honestly, as the two things they actually are — DrEX's three-tier dial (what
the mandate names by file path, `drex-web-v2/src/{api,model,app}.js`), and the Dark Bazaar's own
shielded-descriptor status (what the mandate's "private descriptor" language actually points at,
`dreggnet-market/src/private_clearing.rs` + `circuit-prove/src/dark_bazaar_private.rs`).

---

## 2. CLEAR — Tier 2, plaintext, DrEX terminal

| stage | status | evidence |
|---|---|---|
| list/order-entry (client-side book) | **LIVE** | `app.js:42-46` seeds a real book; `bookOrders()` (`app.js:429-430`) validates client-side (`serve.mjs:245-257` re-validates server-side) |
| clear (ring match + verified settle) | **BROKEN** (regression, today) | see §0. `POST /clear` on any order set that finds a ring → 502, `{"ok":false,"error":"verified settlement rejected the ring: verified-executor FFI unavailable: no verified gate registered"}` — reproduced live against the running dev server, twice, with two different order sets including the app's own default book |
| shielded clear (`fhegg_clear`, Cert-F, plaintext-to-solver) | **LIVE** | `POST /clear-shielded` executed live, ~60ms wall time, returned a full solved certificate: `clearedVolume:18, dualityGap:0, conserves:true, air.accept:true` for the 3-order test book (raw output captured this session) |
| prove-shielded (reveal-nothing STARK wrap) | **ABSENT for any real order** (structural, not a fluke) | see §2.1 below |
| settle (land on a live dregg node) | **code path is honest, untested live** (no node running) | `serve.mjs:329-332,340-344` — `/node/status` and `/settle` both correctly answer `{up:false}`/`{nodeUp:false}` when no node listens (verified: `node serve.mjs --check` → `FALL node … unreachable`); the UI's Settle button is correctly gated on a real ring existing (`app.js:466`), so it is unreachable today anyway since clear never produces one |

### 2.1 Why `/prove-shielded` cannot succeed for any real order, not just today's regression

This is independent of §0's regression — a separate, pre-existing structural gap, corroborated
three ways:

1. **Executed**: `POST /prove-shielded` on the 3-order test book →
   `{"ok":false,"stage":"prove","error":"prove_cert_f failed: Cert-F public program is not
   registered as a Lean-emitted descriptor; choose and prove sufficient integer range policies,
   emit certFDescriptorOf(program), byte-pin, and register it before proving"}`.
2. **Code**: `circuit-prove/src/cert_f_air.rs:355-376` hardcodes exactly **two** registered
   programs (`CERT_F_REGISTRY`), a triangle with `epsilon: 0` and a 4-edge graph with
   `epsilon: 2000`. `try_cert_f_descriptor` (`:392-403`) requires an **exact** match on
   `(n_nodes, edges, w, c, epsilon)` or refuses.
3. **Code**: `fhegg-solver/src/bin/fhegg_clear.rs:235` — `let epsilon = 0.5f64;` is a hardcoded
   constant, always. It can never equal `0` or `2000`. **No order a user submits through the web
   UI can ever produce a matching `epsilon`** — the STARK-prove stage of the SHIELDED mechanism
   is unreachable for live traffic by construction, not by bad luck. (Capacities `c` also come
   straight from `offerAmount`, `:210`, so even the toy `epsilon=0` triangle needs
   `offerAmount=1` on every leg to have a chance — moot given the `epsilon` mismatch alone is
   fatal.)

This is corroborated independently by the *other* Cert-F consumer:
`dreggnet-market/src/certified_clearing.rs:29-33` says of its own STARK receipt: *"fails closed
today… each public auction program needs an emission plus proved integer range-admission policy
before registration. Until a book program is registered, the STARK path returns the named
refusal rather than a fake receipt."* Same registry, same gap, two independent modules hit it —
this is the real ceiling of the SHIELDED mechanism's reveal-nothing wrap, not an artifact of one
demo.

### 2.2 `dreggnet-market::certified_clearing` (the "fhegg-solver settle path" named in the mandate)

Traced per §1: it composes `fhegg_solver::wire::settle` (a pure plaintext uniform-price/
first-price LP, not a network endpoint) with the same Cert-F STARK gate, and is **BANKED
WIP** — real, its own tests pass (not run this session; scope-bounded to what's cited above), but
unreachable from any live LIST/BID/SETTLE flow per its own docstring (§1). It is not part of any
UX today.

---

## 3. SHIELDED — Tier 1, `HidingFri`, one trace-builder sees plaintext

| stage | status | evidence |
|---|---|---|
| DrEX mechanism-level route (`/clear-shielded`, plaintext Cert-F, world sees nothing) | **LIVE** (per §2 table) | as above; this is the *mechanism* claim in `model.js:56-64`, distinct from the *tier* claim below |
| DrEX tier-level "Shielded" privacy claim | **honestly marked not-live** | `model.js:19-27` — `live: false, grade: 'BUILDING'`, `deployDeps` names the reveal-nothing theorem as RESEARCH. Consistent with §2.1: the mechanism route runs, the STARK wrap that would make it a genuine tier claim does not |
| private descriptor (`dark_bazaar_private`, N4K4 fixed shielded relation) | **REAL, TESTED, GATED** — not in the live call path | see §3.1 |
| FNSP-v3 (exact anti-double-spend/receipt) | **LIVE** at the node/executor level, but is NOT the value-hiding apex | `turn/src/executor/apply.rs`, `execute.rs`, `mod.rs`, `node/src/lib.rs` all reference it (grep-confirmed); its own scope note (`THE-DARK-BAZAAR.md` §2.3, corroborated by `circuit-prove/src/shielded_exact_apex_v4.rs:1-13`): *"its 76-lane statement publishes `value` and `asset_type`"* — real, live, and structurally not private |
| v4 (the actual "hides value" apex FNSP-v3 is not) | **ABSENT** | `circuit-prove/src/shielded_exact_apex_v4.rs:14-27`, its own doc: *"binding and wire primitives, **not proof acceptance authority**… Until that descriptor is Lean-authored, emitted, assigned a pinned verifier identity… callers must treat [it] as inputs to that future verifier, never as evidence that it already accepted"* |

### 3.1 The private descriptor, traced to exactly where it stops being live

`circuit-prove/src/dark_bazaar_private.rs` is real: a Lean-emitted (`Market/
DarkBazaarPrivateDescriptor.lean`), byte-pinned, `HidingFriPcs`-proving relation for a fixed
`N≤4,K=4` uniform-price book (`DARK-BAZAAR-PRIVATE-N4K4.md`, not re-verified this session — the
doc's own narrow-verification recipe is cited, not rerun, to stay in budget). `dreggnet-market/
src/private_clearing.rs:1-24` joins it to the live `DarkBazaarSession`, and is explicit about its
own ceiling: *"this trace-building process still sees every bid: this is Tier-1/operator-visible,
not Tier-0 no-single-viewer clearing"* — an honest, correctly-scoped module doc.

Whether it's in the *live* call graph, checked by grep + read:

- `dreggnet-catalog/src/private_bazaar_live.rs` **does** call
  `.prepare_private_clearing_zk_with_binding(...)` (line 765) — but that call site is inside
  `#[cfg(test)] mod tests` (module starts line 587) as a test helper (`settle_worker_market`,
  line 737), not in the production path.
- `dreggnet-catalog/src/private_bazaar_worker.rs` — the actual durable worker that persists
  receipts and drives the real host/Telegram/Discord surfaces (wired per
  `dreggnet-web/src/bin/dreggnet-web-server.rs`, `dreggnet-telegram/src/bin/
  dreggnet-telegram-bot.rs`, `discord-bot/src/commands/market.rs`, all grep-confirmed) — has
  **zero** references to `prepare_private_clearing_zk` or any `dark_bazaar_private` type. It only
  handles spool/receipt persistence for a `winner` + `settlement_turn` that already exists
  (`private_bazaar_worker.rs:953-1042` decode/encode the receipt wire).

**Conclusion: the live Sealed Exchange (per `THE-DARK-BAZAAR.md`'s own "LIVE PATH") settles by
plaintext bid revelation today, exactly as `private_clearing.rs`'s docstring already concedes
("this is exactly what the market's own SETTLE already reveals today") — the HidingFri
proof-of-fairness path is real, proven, unit-tested, and sitting one call away from being wired
into the production worker, but is not yet called from it.** This matches, and now has fresh
code-level confirmation of, `THE-DARK-BAZAAR.md`'s own "GATED SUBSTRATE" grade for this piece.

---

## 4. DARK — Tier 0, no-single-viewer FHE

| stage | status | evidence |
|---|---|---|
| DrEX tier/UX surface | **honestly ABSENT, correctly labelled** | `model.js:28-36` (`live:false, grade:'FRONTIER'`), `api.js:83` (`clearDark: {live:false}`). Verified: `serve.mjs` has no `/clear-dark` route at all (grep of the route table, `serve.mjs:259-355`) — the label matches reality exactly, nothing overclaimed |
| threshold-BFV → per-party MPC crossing → attested quorum receipt, end-to-end | **REAL, runs, SEAM (not a product path)** | executed this session: `cargo test -p fhegg-fhe --test dark_clearing_e2e --release` → `authenticated_traders_to_threshold_bfv_to_party_mpc_to_attested_result … ok`, **4.83s**. Quorum variant: `cargo test -p fhegg-fhe --test dark_clearing_quorum_e2e --release` → `authenticated_dark_bazaar_clears_with_one_of_four_custodians_offline … ok`, **6.57s**. Both genuinely exercise collective keygen, authenticated ingress, the fold, masked-boundary opening, and interactive MPC argmax — but every "party" is a local thread/closure inside one test binary (`dark_clearing_e2e.rs:14-15`, `use std::thread`), not a separate host/process. No product surface calls any of this — confirmed by the empty `serve.mjs` route table above and by no non-test caller of the relevant types outside `fhegg-fhe/tests/` and `dreggnet-market`'s own `dark_amm_*` modules (also gated, `dreggnet-market/src/dark_amm_collective.rs`, itself unreferenced by any `-web`/`-telegram`/discord binary, grep-checked) |
| same-opening apex (binds the ciphertext to the public root the proof is about) | **freshly PROVED in Lean + emitted as an IR-2 descriptor, ZERO Rust wiring** | `FHEGG-SAME-OPENING-APEX.md` (today) + `TESTQALOG.md`'s same-opening-gadget section (today, morning). Verified: `metatheory/Market.lean:44` now imports `Market.EmitSameOpeningGadget` (committed at `29427bec84`, 13:20 today) so it's in the checked Lean module graph — but `grep -rl "SameOpeningGadget" --include=*.rs .` returns **nothing**: no `circuit-prove` consumer, no entry in `circuit/src/descriptor_by_name.rs`, no registry analogous to `CERT_F_REGISTRY`. This is a pure SEAM: the relation and its byte-pinned emission both exist and are proved sound (per the apex doc's own honest residuals list), but nothing in Rust has picked it up yet |
| performance readiness, if DARK were wired today | **would currently be a de-optimization, measured** | per the two docs read first: the production fold call profile is K=1 (one upload, one fold), which the AMD measurements + arithmetic derive to **~2.3× SLOWER than CPU** (`FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`, `DREX-GPU-RESIDENCY-PLAN.md` §2) — GPU is not a lever DARK can lean on without the residency plan's R1-R4 first. Separately, the crossing is inherently network-round-trip-bound regardless of any GPU work (`mpc.rs:370-374`, cited in the residency plan: e.g. 221 rounds at `b=16,K=4096`) — "excellent UX" for DARK needs the network-MPC latency story solved, not (only) a GPU story |

---

## 5. The honest one-paragraph answer

**CLEAR** is the only tier that ever looked fully live, and as of a same-day commit it is not:
the ring-clear step fail-closed-refuses every order book that actually clears, including the
app's own default demo (§0); the shielded mechanism route (`/clear-shielded`) genuinely works and
is fast, but its reveal-nothing STARK wrap (`/prove-shielded`) cannot succeed for any real order
by construction of a hardcoded `epsilon` mismatch (§2.1), corroborated independently by
`dreggnet-market`'s own Cert-F consumer hitting the identical wall. **SHIELDED**'s cryptographic
core (the N4K4 HidingFri private-book relation) is real, proved, and unit-tested, but is called
only from test code today — the live Sealed Exchange still settles by plaintext bid revelation
(§3.1), and the module that would actually hide *value* (v4) explicitly documents itself as wire
primitives with no acceptance authority yet. **DARK** has a real, passing, cryptographically
complete in-process test of the full no-single-viewer pipeline (§4), a same-day Lean proof of the
missing cryptographic apex with a byte-pinned emission and zero Rust consumers, and correctly
labels itself FRONTIER everywhere a user would see it — the one tier where the code's honesty
about its own status and the frontend's honesty about that status agree exactly. Nothing here is
"working great with excellent UX" today; the UX layer itself is largely honest about that (correct
error surfacing, correctly-gated Settle button, correct `live:false` labels) — the gap is
entirely in the underlying pipelines, not in the frontend lying about them.
