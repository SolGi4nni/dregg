# Published-package verification — `@dregg/sdk@0.3.0`

A fresh-consumer check of the package as published on npm (the registry tarball,
not a build from this source tree). Run in a clean temp dir: `npm init -y` then
`npm install @dregg/sdk@0.3.0`. Date: 2026-06-28.

## Result: the published package works for a fresh consumer.

| Check | Result | Evidence |
|---|---|---|
| Installs clean from the registry | yes | `added 3 packages, found 0 vulnerabilities` — `@dregg/sdk` + `@noble/ed25519` + `@noble/hashes`. No `dregg-wasm` install nag (it is an *optional* peer). |
| ESM import (`import * from "@dregg/sdk"`) | yes | loads, 46 exports. |
| CJS require (`require("@dregg/sdk")`) | yes | loads, same 46 exports. |
| API produces valid turns | yes | `pay`, `turn().pay()`, `services.invoke` (with pay leg), `execution.lease` all construct + `.sign()` offline (pinned federation id, no node, no wasm) and expose the signed `Action`/`Effect`. |
| Byte-faithful to the Rust facade | yes | see below. |
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

The repo's own dev-time wire differential (`test/wire.test.mjs`) signs a turn in
TS and asserts byte equality against the actual Rust `dregg-turn`/`dregg-sdk`
code; that oracle path needs the `dregg-wasm` build (a dev dependency, see below),
so it is a source-tree test, not a fresh-consumer test.

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

## Verdict

`@dregg/sdk@0.3.0` works for a fresh consumer: installs clean, imports both ways,
builds valid byte-faithful turns offline. **No 0.3.1 fix is required for the
documented front door.** The one honest note is the legacy `@dregg/sdk/wasm`
subpath, whose `dregg-wasm` peer is unpublished — a follow-up only if that legacy
surface is meant to be consumable from npm.
