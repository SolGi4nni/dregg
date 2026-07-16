# Published-package verification — `@dregg/sdk@0.3.0`

A fresh-consumer check of the package as published on npm (the registry tarball,
not a build from this source tree). Run in a clean temp dir: `npm init -y` then
`npm install @dregg/sdk@0.3.0`. Date: 2026-06-28.

> ## ⚠ CORRECTION (2026-07-16) — `0.3.0` is NOT byte-faithful for capability grants
>
> The "Byte-faithful to the Rust facade | yes" verdict below is **WRONG for the
> `grantCapability` path** and was reached against a **stale oracle**. At HEAD,
> the TS wire encoder (`src/internal/wire.ts::writeCapabilityRef`) wrote seven
> `CapabilityRef` fields and **dropped `provenance`** — a `[u8; 32]` field that
> `cell/src/capability.rs` carries with `#[serde(default)]` (NO
> `skip_serializing_if`), so Rust postcard **emits its 32 bytes**. Every
> SDK-issued turn carrying a `GrantCapability` effect therefore produced postcard
> bytes **32 bytes short** of what the node's `dregg_turn::Turn` decoder expects.
> postcard is non-self-describing and positional, so the node reads the 32 bytes
> *following* the cap (a neighbouring field / the next effect's tag) as
> `provenance` and **desyncs** — the turn fails to decode, or decodes to a
> **different action than the one signed**.
>
> **Why the drift-killer missed it:** `test/wire.test.mjs` compared against
> `wasm/pkg` — a **gitignored, untracked** artifact (`wasm/pkg/.gitignore` = `*`)
> that was a two-week-old, pre-`provenance` snapshot of itself (its embedded serde
> table literally reads `struct CapabilityRef with 7 elements`). The oracle was a
> hand-frozen mirror, not the real freshly-built Rust — so it blessed the same
> omission the encoder made. `package.json`'s `test` built the TS but **never the
> wasm**, and **no CI workflow ran `npm test`**.
>
> **Fixed at HEAD (uncommitted):** `writeCapabilityRef` now emits `provenance`
> (`[0u8;32]` unprovenanced sentinel by default — correct for a direct grant);
> the differential now **rebuilds the wasm oracle fresh** before every run
> (`pretest` → `npm run build:oracle`) and **fails loud** if the oracle is absent.
>
> **A republish is EMBER-GATED — see "Republish requirements" at the bottom.**

> ## ⚠ CORRECTION 2 (2026-07-16) — the SIGNATURE SHAPE is also stale: classical vs the new HYBRID (PQ) default
>
> Building the differential oracle **freshly** (the M30 fix above) surfaced a
> SECOND, deeper divergence the stale oracle hid. The Rust DEFAULT action signer
> (`AgentCipherclerk::sign_action`) now emits `Authorization::HybridSignature`
> (enum variant **10**): ed25519 (64B) **plus** an ML-DSA-65 / FIPS-204 signature
> (**3309B**) and its public key (**1952B**). The TS SDK signs **classical only**
> — `Authorization::Signature` (variant 0, 64B) — because it has no post-quantum
> crypto. So a **TS-signed turn is byte-identical to the LEGACY
> `sign_action_classical`, NOT to the current default signer**, and this is true
> of **every signed turn** (pay, lease, service, transfer, set-field, events,
> *and* grantCapability), not just the `CapabilityRef` path.
>
> **What still holds (verified against the fresh oracle):** the turn ENCODER is
> byte-faithful (incl. the now-fixed `provenance`), the canonical `Turn::hash`
> (v3) matches, and the SIGNING MESSAGE matches — the TS classical 64-byte
> signature equals the **ed25519 half** of the Rust hybrid signature over the
> same `compute_signing_message`. What differs is only the authorization **wire
> shape**.
>
> **Node impact (STAGED, with a dated cliff):** the node still accepts classical
> `Signature` and verifies the ed25519 leg; the PQ half is only *required* once
> the node flips `TurnExecutor::require_pq` (**default off today**). So TS-signed
> turns work **now**, but:
> - they are **not byte-identical** to what the current Rust SDK produces, so any
>   "byte-faithful to the Rust facade" claim is false for signed turns generally;
> - the day `require_pq` flips node-side, **every TS-signed turn is rejected** —
>   the TS SDK cannot produce the ML-DSA-65 half. This is a hard forward
>   dependency, tracked here, not a today-breakage.
>
> **Guarded, not narrated:** `test/wire.test.mjs` now isolates the ENCODER on the
> classical path (green, incl. provenance) and adds an explicit `hybrid
> authorization boundary` test that FAILS if the Rust default ever stops being
> hybrid — so this gap can never silently regress to a false "byte-faithful".
> Closing it for real needs an ML-DSA-65 signer in the TS SDK (ember-gated; see
> "Republish requirements").

## Result: the published package works for a fresh consumer.

| Check | Result | Evidence |
|---|---|---|
| Installs clean from the registry | yes | `added 3 packages, found 0 vulnerabilities` — `@dregg/sdk` + `@noble/ed25519` + `@noble/hashes`. No `dregg-wasm` install nag (it is an *optional* peer). |
| ESM import (`import * from "@dregg/sdk"`) | yes | loads, 46 exports. |
| CJS require (`require("@dregg/sdk")`) | yes | loads, same 46 exports. |
| API produces valid turns | yes | `pay`, `turn().pay()`, `services.invoke` (with pay leg), `execution.lease` all construct + `.sign()` offline (pinned federation id, no node, no wasm) and expose the signed `Action`/`Effect`. |
| Turn ENCODER byte-faithful (postcard layout, incl. `provenance`, + v3 hash) | **yes at HEAD** (was NO for `grantCapability` on 0.3.0 — dropped `provenance`, ⚠ correction 1) | verified against a freshly-built wasm oracle; see below. |
| Signed-turn byte-identical to the current Rust signer | **NO** — TS signs classical, the Rust default is now HYBRID PQ (⚠ correction 2). Byte-identical to the *legacy* `sign_action_classical` only. | see ⚠ correction 2. |
| Live-node round-trip | node-down | the devnet edge is down; no reachable dregg node. The SDK fails cleanly. |

## Public surface (46 exports)

`Identity`, `AgentRuntime`, `TurnBuilder`, `AuthorizedTurn`, `ServiceEconomy`,
`Lease`, `NodeClient`, `Receipt`/`ReceiptStream`/`ReceiptFilter`, `NodeEvents`,
`TrustlineClient`/`ChannelsClient`/`MailboxClient`, `AttestedQuery`, `TurnProof`,
`Pg`, `DeployChecker`, `profiles`, `program`, the `explain*`/`render*` helpers,
the `hex*`/`base64*`/`fieldFromU64` codecs, and the `symbol`/role/method
constants. (`AgentRuntime`/`ServiceEconomy` are the front door; `program`,
`leaseProgramConstraints`, the codecs are the building blocks.)

## API sample (from the published package, no node, no wasm)

`pay`: `method == symbol("pay")`, `target == payer cell`,
`args == [asset, fieldFromU64(amount), to]`, effects = exactly one conserving
`Transfer { from: <payer>, to, amount }`. `services.invoke` with a pay leg →
`[Transfer(payer→provider), <work>]`. `lease.run` → `method == symbol("run")`,
`[SetField(slot 4 → step+1), <work>]`.

## Byte-faithfulness to Rust

Two independent confirmations, both computable inside the published package:

1. **`pay` action shape.** The published TS emits
   `args = [asset, field_from_u64(amount), to]` and one conserving `Transfer`.
   This matches `dregg-payable/src/payable.rs::pay_args` byte-for-byte
   (`vec![asset, field_from_u64(amount), to_felt]`) and the documented
   `resolve_pay` desugar in `sdk/src/service_economy.rs`.
2. **Content-addressed program VK.** `program.canonicalProgramVk(...)` recomputed
   in the published TS for the lease meter program `FieldLte{slot4 ≤ n} ∧
   Monotonic{slot4}` reproduces the Rust `dregg_cell::factory::canonical_program_vk`
   source-of-truth digests exactly for n ∈ {1, 2, 8}. A byte-identical postcard
   encoding is the only way to hit those content addresses.

Both confirmations above are about the **pay / lease** front door (a `Transfer`
and a `SetField`); **neither exercises a `CapabilityRef`**, which is why they held
while the `grantCapability` path drifted (see the ⚠ correction at the top).

The repo's own dev-time wire differential (`test/wire.test.mjs`) asserts byte
equality between the TS wire encoder and the actual Rust `dregg-turn`/`dregg-sdk`
code. **⚠ Until 2026-07-16 its oracle was a gitignored, never-rebuilt `wasm/pkg`
snapshot** — a stale mirror that blessed the encoder's own omissions rather than
catching them. It now rebuilds the wasm fresh (`pretest`) and **fails loud** when
the oracle is absent (verified: hiding the built `.wasm` makes the differential
error, not skip). Because the Rust default signer is now HYBRID PQ (⚠ correction
2) while the TS SDK signs classical, the differential isolates the ENCODER on the
classical path (both sides classical → byte-identical, incl. `provenance` and the
v3 hash), checks the SIGNING MESSAGE separately (TS classical sig == the ed25519
half of the Rust hybrid), and guards the classical-vs-hybrid boundary loud. So
drift in the postcard layout, hashes, or signing message fails here against
**current** Rust. It remains a source-tree test (needs the `dregg-wasm` dev
dependency), not a fresh-consumer test.

⚠ **Building that oracle is not turnkey today.** `npm run build:oracle`
(`wasm-pack build ../wasm --target web`) currently needs two out-of-band unblocks
on a stock macOS box: (a) a wasm-capable C compiler for the `zstd-sys` dep —
`CC_wasm32_unknown_unknown=$(brew --prefix llvm)/bin/clang` (Apple clang has no
wasm target); (b) a pre-existing, committed compile break in `starbridge-v2`
(a `TurnError::CustomProofStateBindingMismatch` match arm is missing in
`starbridge-v2/src/debug.rs` — unrelated to this SDK). Until (b) is fixed on
`main`, the `pretest`/CI oracle build fails and the differential cannot run.

## The wasm peer-dependency story (no gap for the front door)

The core front door (`@dregg/sdk`) is fully wasm-free: the published
`dist/index.{js,mjs}` contain **zero** `dregg-wasm` references, and every
construction + signing path above ran with **no** `dregg-wasm` installed. A basic
user does **not** need `dregg-wasm`.

`dregg-wasm` is referenced only by the **legacy** `@dregg/sdk/wasm` subpath (the
pre-refinement playground surface: token ops, STARK toys, in-browser sim). That
subpath still imports without it (the wasm module is lazy-loaded; it would only
throw when a wasm-backed method is actually called).

`dregg-wasm` is **not published on npm** (`npm view dregg-wasm` → 404; the
manifest lists it as `file:../wasm/pkg`). This is correct for 0.3.0 because the
front door does not use it. It is a real gap **only** for a consumer of the
legacy `@dregg/sdk/wasm` surface — they have no published wasm package to install.

## Live-node round-trip

No reachable dregg node at verification time:
- `devnet.dregg.fg-goose.online` → TLS internal error (down; recovery in flight).
  The SDK surfaces this as a clean `fetch failed`.
- `www.dregg.net` / `dregg.net` → the marketing site (HTML), not a node API.

The full sign → submit → `Receipt` path is covered against a mock node in
`test/service-economy.test.mjs` ("pay rides the full path"). The SDK's
turn-construction (the core) is proven here; only the network bonus is pending a
live node.

## Republish requirements (EMBER-GATED — do NOT `npm publish` autonomously)

The encoder fix is on disk at HEAD, uncommitted and **unpublished**. Publishing is
outward-facing and gated. To ship the fix:

- **Version:** cut `0.3.1` (patch — the public API is unchanged; only the emitted
  wire bytes for the `grantCapability` path change). `package.json` currently pins
  `0.3.0`; bump it.
- **What breaks on `0.3.0` (impact):** any consumer of `@dregg/sdk@0.3.0` that
  builds a turn with a **`grantCapability`** effect — `AgentRuntime.grantCapability`
  → `turns.ts` → `identity.encodeSignedTurn` → `POST /api/turns/submit-signed` —
  emits a `CapabilityRef` **32 bytes short**. The node either rejects the turn
  (postcard "end of buffer") or decodes a **different action than was signed**.
  Turns *without* a cap grant (pay, lease, transfer, set-field, events, the pay/
  lease front door in this doc) are **unaffected** — that path never encodes a
  `CapabilityRef`.
- **Downstream:** first-party consumers that call `grantCapability` (in-repo:
  `sdk-ts/extension`, any agent-runtime user). Anyone only using the pay/lease/
  service front door is unaffected. `dregg-wasm` is not published, so no separate
  wasm republish is needed for the front door.
- **`0.3.0` disposition:** recommend `npm deprecate @dregg/sdk@0.3.0 "grantCapability
  emits a malformed CapabilityRef (missing provenance); use >=0.3.1"`. A hard
  `npm unpublish`/yank is likely unnecessary (the front door works), but is
  ember's call. Deprecate at minimum.
- **Gate the publish on the test:** the current `publish-sdk-ts.yml` builds the
  wasm but **never runs `npm test`** — add a `npm test` (or a push/PR CI running
  it) so the resurrected differential gates future publishes. Otherwise the same
  class of drift ships again. NB the oracle build itself is not turnkey yet (see
  the two unblocks above the Republish section) — CI must set the wasm `CC` and
  the `starbridge-v2` break must be fixed on `main`, or `pretest` fails.

### The HYBRID-PQ signature gap is SEPARATE from the `0.3.1` provenance fix

Correction 2's classical-vs-hybrid divergence is **not** closed by shipping
`0.3.1`. It affects **every** signed turn and is a forward dependency, not a
today-breakage:

- **Today:** classical turns are node-accepted (`require_pq` off), so `0.3.1`
  ships fine as a classical SDK. No action *required* to keep the SDK working now.
- **The cliff:** whenever the node flips `TurnExecutor::require_pq`, **all**
  TS-signed turns (any version, incl. `0.3.1`) are rejected — the TS SDK has no
  ML-DSA-65 signer. Closing this needs an ML-DSA-65 (FIPS 204) signer added to
  the TS SDK so `identity.signAction` can emit `Authorization::HybridSignature`
  (a real feature, ember-gated), coordinated with the node's `require_pq` flip.
- **Recommendation:** decide the ordering deliberately — do **not** flip
  `require_pq` before a hybrid-capable SDK is published, or every JS/TS agent
  drops offline. Track this alongside the PQ-metatheory rollout.

## Verdict

`@dregg/sdk@0.3.0` works for a fresh consumer's **pay/lease/service front door**:
installs clean, imports both ways, builds valid classical turns offline. Two
published-truth corrections at HEAD: **(1)** it was NOT byte-faithful for
`grantCapability` (dropped `provenance`) — fixed on disk, needs a **`0.3.1`**
republish + a `0.3.0` deprecation (ember-gated). **(2)** no signed turn is
byte-identical to the *current* Rust signer, which is now HYBRID PQ
(`Authorization::HybridSignature`, ML-DSA-65); the TS SDK signs classical only.
That is node-accepted today but becomes a hard rejection the moment `require_pq`
flips — a forward dependency needing an ML-DSA-65 signer in the TS SDK, separate
from and larger than the `0.3.1` fix. The legacy `@dregg/sdk/wasm` subpath's
unpublished `dregg-wasm` peer remains a separate, lower note.
