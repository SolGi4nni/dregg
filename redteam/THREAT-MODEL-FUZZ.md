# Wire / Codec / Marshaller / Executor — Fuzz + Property-Test Threat Model & Findings

Owner: redteam harness (this crate). Companion to the existing
`redteam/tests/{captp,blocklace,gc}_attacks.rs` (CapTP confinement / handoff
non-amplification / GC Byzantine-resistance / blocklace equivocation) and the
`dregg-protocol-tests` invariant suite (conservation / nonce / receipt-chain /
permission / attenuation against the executor).

This document covers the surfaces THIS workflow added harnesses for:

| Surface | Harness | What it attacks |
|---|---|---|
| postcard wire codec + framing | `tests/wire_codec_fuzz.rs` | `dregg_wire::codec::decode/encode`, `Turn` postcard roundtrip |
| Lean-FFI marshaller | `tests/marshal_fuzz.rs` | `unmarshal_result` output parser, `marshal_turn` encoder |
| running Rust executor | `tests/executor_invariants.rs` | conservation / authority / overflow-mint / double-spend / replay |
| live devnet HTTP surface | `tests/devnet_adversarial.rs` + `devnet_probe.sh` | malformed/oversized/injection submission |

## Trust model recap (captp/src/lib.rs + Dregg2/ + node/api.rs)

- **Bearer = authorization.** A swiss number / capability is a secret; possession
  is authority. The executor must faithfully verify per-action signatures over
  the canonical signing message bound to the federation id.
- **The executor is the SOLE state-mutation entry point** (`execute()` in
  `turn/src/executor/execute.rs`). Lean `Dregg2/` *proves* invariants about the
  abstract model; the question this harness answers is whether the *running Rust*
  enforces them. A divergence (Lean-safe, Rust-accepts) is a real bug.
- **`ok`/commit bit is load-bearing.** The marshaller's `unmarshal_result` parser
  reads the Lean library's return string across an FFI trust boundary; a garbage
  string must never be mis-read as `committed=true`.
- **postcard is non-self-describing + positional.** A `skip_serializing_if` on any
  field riding inside `Turn` desyncs the byte stream — the historical bug that
  made every turn with a defaulted optional undecodable, so turns never
  replicated. (Pinned by `turn/tests/integration_postcard_wire_roundtrip.rs` for
  3 hand-shapes; generalized to the whole input space here.)

## The "Lean proves X" vs "Rust enforces X" distinction

The executor harness builds adversarial turns that PASS the shallow guards
(agent exists, nonce matches, fee covered) so the attack reaches the deep
enforcement, then asserts the running `TurnExecutor` REJECTS or no-ops it AND
leaves state byte-identical. Each test is a concrete witness that the proven
invariant survives the projection from Lean model to Rust code.

---

## FINDINGS

### F1 (informational, devnet posture) — privileged write API not publicly reachable; `/health` and `/metrics` shadowed by the SPA

Live probe of `https://devnet.dregg.fg-goose.online` (solo node, dag_height
~46.9k, consensus_live):

```
POST /turn/submit            -> HTTP 405   (GET /turn/submit -> 200 = SPA route)
OPTIONS /turn/submit         -> HTTP 405
POST /cipherclerk/mint       -> HTTP 405
GET  /health                 -> 200 text/html  (SPA, NOT the node's get_status JSON)
GET  /metrics                -> 200 text/html  (SPA, NOT Prometheus)
GET  /status                 -> 200 application/json  (node API, proxied)
GET  /api/cells              -> 200 []          (node API, proxied)
```

The public reverse proxy forwards only a READ allowlist (`/status`, `/api/*`,
`/federation/roots`, `/api/faucet`) to the node and serves the SPA for
everything else. The privileged write routes (`/turn/submit`, `/cipherclerk/*`,
`/cells/*`) are **not reachable unauthenticated through the proxy** — a strong
default posture. Consequence: adversarial *turn submission* against the live
node's executor over HTTP is not possible from outside; the executor-invariant
evidence therefore comes from the in-process `executor_invariants.rs` harness
driving the real `TurnExecutor`.

Two minor inconsistencies worth a note to the SWAP/node owners (LOGGED, not
fixed — node + deploy are owned elsewhere):
- `/health` is intended in `node/src/api.rs` to map to `get_status` (JSON) but
  the proxy serves the SPA for it, so external health checks that hit `/health`
  get HTML. Use `/status` for machine health.
- `/metrics` is likewise SPA-shadowed externally; Prometheus scraping must use
  the origin, not the public host.

Neither is a security break (no data exposure, no DoS), but the health-route
shadow can mask a real outage from a naive `/health` monitor.

### F2 (defended) — input validators reject out-of-bounds / non-hex / injection

```
POST /api/faucet {"recipient":"  ","amount":missing}   -> 422 (clean deserialize error)
POST /api/faucet {"recipient":"../../etc/passwd",amount:999999999999}
                                                        -> 200 {"error":"amount must be between 0 and 10000"}
POST /api/faucet {"recipient":"zzzz","amount":100}      -> 200 {"error":"invalid recipient: must be 64 hex characters"}
POST /api/faucet {"recipient":"AAAA<script>",amount:100}-> 200 {"error":"invalid recipient: must be 64 hex characters"}
GET  /api/cell/<5000-char id>                           -> 400
GET  /api/cell/abc;DROP                                 -> 400
GET  /api/cell/..%2F..%2F..%2Fetc%2Fpasswd             -> 200 (SPA route; no traversal into FS)
```

The faucet enforces its amount bound (0..10000) and a strict 64-hex recipient
format; path-injection recipients are rejected by the hex check, not by
reaching the filesystem. Adversarial cell ids (huge, non-hex, `;`-injection)
return clean 400s. **EVIDENCE the public input validators hold.**

### F3 (defended) — no OOM / DoS from an oversized body

```
POST /turn/submit  --data-binary <16.8 MB>  -> HTTP 405, upload truncated at ~131 KB
```

The proxy refuses the route and cuts the upload early; the node never allocates
a 16 MB+ buffer. The framing codec's own `MAX_MESSAGE_SIZE` (16 MiB) check (it
validates the declared length BEFORE allocating) is the in-process analogue,
exercised by `wire_codec_fuzz::oversize_payload_is_refused_by_encoder`.

### F4 (defended) — node survives the barrage

After all adversarial requests above, `/status` still returns
`{"healthy":true,...,"consensus_live":true}` with a monotonically advancing
`dag_height`. **No crash, no consensus halt, no connection reset.**

### Executor invariants — DEFENDED on the running Rust (`executor_invariants.rs`)

Each ran against a real `TurnExecutor` + `Ledger` (NOT a mock). All are passing
assertions = EVIDENCE the property holds operationally, not just in Lean:

- **Conservation** — 400 proptest cases of adversarial transfers (over-balance,
  random amounts); total ledger value is byte-identical after EVERY step.
- **Authority** — a signature-required cell rejects both `Authorization::Unchecked`
  (the historical bypass) and a real signature from the WRONG key; balances
  unchanged. Confirms the fail-closed authorization path (`authorize.rs`).
- **No overflow-mint** — a transfer that would overflow u64 at the destination is
  rejected (no wrap-around credit).
- **No double-spend** — a 2-transfer turn that overspends rolls back ATOMICALLY
  (no partial debit/credit leak through the journal).
- **No replay** — a committed turn replayed at the same nonce is rejected
  (`NonceReplay`); the recipient is credited exactly once.

### Codec / marshaller robustness — DEFENDED (`wire_codec_fuzz.rs`, `marshal_fuzz.rs`)

- `dregg_wire::codec::decode` is a no-panic total function on 4000 arbitrary
  byte buffers; any decoded `WireMessage` is a codec fixed point (re-encode +
  re-decode is byte-stable — the positional-desync detector).
- `Turn` postcard roundtrip is byte-stable across 2000 generated structural
  shapes (optionals Some/None, forest fan-out/depth, NoteCreate optionals both
  ways). This **generalizes the 3-shape skip_serializing_if regression test** to
  the whole input space: a future `skip_serializing_if` on ANY Turn field is
  caught by the shape that trips its predicate. Truncation + single-bit
  corruption never panic the positional parser.
- `unmarshal_result` (the FFI output parser) is no-panic on 8000 arbitrary
  strings + exhaustive single-bit mutation + every-prefix truncation of valid
  envelopes; a garbage string can never parse to `committed=true` with an
  empty-sentinel state (the commit-laundering guard); out-of-range `status`
  codes are rejected.
- `marshal_turn` encodes every `WireAction` arm without panic and produces
  brace/bracket-balanced wire, under a fuzzed host context.

---

## How to run

```bash
# in-process fuzz + executor property tests (no network):
cargo test -p dregg-redteam

# live devnet barrage (TLS, full output):
redteam/devnet_probe.sh

# gated in-process devnet test (needs a plaintext origin, e.g. an SSH tunnel):
DREGG_DEVNET_REDTEAM=1 DREGG_DEVNET_HOST=127.0.0.1 DREGG_DEVNET_PORT=8080 \
  cargo test -p dregg-redteam --test devnet_adversarial
```

## Assumptions that do NOT hold operationally (honest caveats)

1. **The live executor is not externally fuzzable over HTTP** (F1): the deep
   executor invariants are evidenced in-process, not against the deployed
   binary. If the proxy allowlist ever widens to expose `/turn/submit`, the
   `devnet_adversarial.rs` submission cases become live and must be re-run.
2. **No input decoder for the marshaller** (`marshal_turn` is encode-only; the
   Lean side parses it): the encoder is fuzzed for panic-freedom + structural
   well-formedness, but a full encode→Lean-parse→decode roundtrip would need the
   Lean static lib (`lean-lib` feature) — that lives in `dregg-lean-ffi`'s own
   differential harnesses, not here.
3. The `Turn` postcard fuzzer uses a representative (not exhaustive) effect
   palette — the OPTIONAL-bearing variants where desync hides. The full
   ~50-variant `Effect` enum is not enumerated; a desync on a variant outside the
   palette would be missed. Widening the palette is cheap follow-up.
