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

> ## ✅ CORRECTION 3 (2026-07-16) — corrections 1+2 are CLOSED on disk; and correction 2 UNDERSTATED the damage
>
> **The hybrid PQ signer is shipped** (uncommitted, unpublished — see below).
> `Identity.signAction` now emits `Authorization::HybridSignature` (variant 10)
> and a TS-signed turn is **byte-identical to the current Rust default signer**,
> driven against a **freshly-built** oracle, and **ACCEPTED by the real Rust
> executor** at `require_pq` both OFF and ON. Details in "The hybrid PQ signer"
> below.
>
> **But building that oracle surfaced a THIRD divergence, and it inverts
> correction 2's severity.** Correction 2 claimed "the SIGNING MESSAGE matches —
> the TS classical sig equals the ed25519 half of the Rust hybrid" and therefore
> "TS-signed turns work **now**; the cliff is the future `require_pq` flip".
> **Both claims were false.** The TS `actionSigningMessage` was at
> **`dregg-action-sig-v2:`** — federation-bound but with **no `turn_nonce`** —
> while Rust has been at **`dregg-action-sig-v3:`** (v3 binds the submitting
> turn's nonce, the Full-commitment replay closure). Different domain string,
> different preimage, different signature.
>
> Driven, not argued — HEAD's v2 message reconstructed and fed to the REAL
> `TurnExecutor::execute`:
>
> ```text
> THE SHIPPED 0.3.0 SIGNING MESSAGE (v2), judged by the real Rust executor:
>   require_pq=OFF (today's node): REJECTED
>   reason: rejected at [0]: invalid authorization: Ed25519 signature verification failed
> ```
>
> So **every TS-signed turn was already rejected by today's node** — pay, lease,
> service, transfer, set-field, events, grantCapability. Not a forward
> dependency; a present-tense, total breakage of the signed path. The published
> `0.3.0` cannot submit *any* turn a node will accept.
>
> **Why this was never caught — the M30 disease, one level deeper.** Correction 1
> found a *stale* oracle. This time the oracle was **absent**: `npm run
> build:oracle` was blocked by the two unblocks documented at the bottom of this
> file, `package.json`'s `test` never built the wasm, and no CI ran `npm test`.
> The "signing message matches" line was written against an oracle **that had
> never been built** — the test could not have passed, because it never ran. A
> claim's confidence tracked its prose, not its execution. Both blockers are now
> clear (the `starbridge-v2` break is fixed on `main`; the wasm `CC` is set in
> `pretest`), the oracle builds, and the suite is green: **88/88**.
>
> **Fixed at HEAD (uncommitted):** `actionSigningMessage` is v3 and takes a
> REQUIRED `turnNonce`; `TurnBuilder.sign()` reads the live nonce (or a pinned
> `NodeClientOptions.nonce` for offline signing); `AuthorizedTurn.submit()`
> re-signs if the nonce moved (the TS mirror of Rust's
> `resign_full_commitment_at`). The old comment claiming "the per-action
> signature stays valid; only the envelope is re-signed" on a nonce race was
> false under v3 and is gone.

> ## ⚠ CORRECTION 2 (2026-07-16) — the SIGNATURE SHAPE is also stale: classical vs the new HYBRID (PQ) default
>
> **⚠ SUPERSEDED by correction 3**: the gap below is CLOSED (the hybrid signer
> is shipped on disk), and this correction's "TS-signed turns work now" /
> "the signing message matches" claims are **WRONG** — see correction 3. Kept
> for the record of what was believed and how it was wrong.
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

## The hybrid PQ signer (on disk, uncommitted, UNPUBLISHED)

The prerequisite that must land before the node can ever flip `require_pq`.

### Implementation choice: `@noble/post-quantum` (ML-DSA-65, FIPS 204)

`src/internal/mldsa.ts` wraps `@noble/post-quantum`'s `ml_dsa65`. Why this and
not the alternatives:

- **Not a hand-roll.** No lattice arithmetic is written here — only the
  parameter/derivation/context plumbing that pins a real FIPS 204
  implementation to dregg's conventions.
- **Not a wasm binding of the Rust signer**, though that was the tempting
  option (wasm/pkg is already the differential oracle). It would have made the
  DEFAULT signer depend on `dregg-wasm`, which **is not published to npm**
  (`npm view dregg-wasm` → 404). The SDK's front door is deliberately wasm-free;
  routing every signed turn through an unpublished package would turn a
  documented non-gap into a hard one. The wasm stays a *dev-time oracle*, which
  is exactly where it has leverage.
- **Same family as the SDK's existing crypto** (`@noble/ed25519`,
  `@noble/hashes` — already direct dependencies), same maintainer, audited,
  actively maintained, pure JS, zero native/wasm deps, tree-shakeable.
- Its ML-DSA-65 lengths agree with the Rust crate's exactly (pk 1952, sig 3309,
  sk 4032) — and, more to the point, agreement is **driven** (below), not
  assumed.

### Key handling: no new key material, no ceremony

Read from Rust, not invented: `dregg_pq::MlDsaKey::from_ed25519_seed` is
`ml_dsa_65::KG::keygen_from_seed(seed)` — FIPS 204 `ML-DSA.KeyGen(ξ = seed)`
over **the same 32-byte ed25519 seed the classical identity already holds**.
`Identity` holds that seed, so `signAction` derives the PQ keypair itself and
caches it. **A caller supplies nothing new**: existing seeds/mnemonics/profiles
keep working unchanged, and a cipherclerk, a node, and a genesis fixture built
from one mnemonic agree on the PQ public key with no separate ceremony. The
1952-byte public key is *carried in the authorization* (a verifier cannot derive
another party's PQ public key from their ed25519 public key), so it never needs
distributing. `Identity.mlDsaPublicKey()` exposes it for enrollment flows.

Two conventions that are **required**, mirrored from Rust and pinned by the
differential: the FIPS 204 `ctx` is `dregg-hybrid-turn-v1`
(`turn/src/pq.rs::HYBRID_TURN_PQ_CTX`), and signing is the **deterministic**
variant (`rnd = {0}^32`; noble's `extraEntropy: false`, Rust's
`try_sign_with_seed(&[0u8; 32], …)`). Determinism is not a preference: the
ML-DSA half is bound into `Action::hash` (discriminant 10, the anti-strip
binding), which flows into `Turn::hash` — a hedged signature would make the same
logical turn hash differently on every signing, breaking turn identity.

### Driven, against a FRESH oracle + the real verifier

- **Byte-identity** (`test/wire.test.mjs`, oracle rebuilt by `pretest`, verified
  fresh: its embedded serde table reads `struct CapabilityRef with 8 elements`
  and it carries `dregg-action-sig-v3`): a TS hybrid-signed turn is
  **byte-identical** to the Rust DEFAULT-signed turn, over a turn exercising
  every modeled effect incl. `provenance`. **Both sides sign** — the oracle gets
  the UNSIGNED turn and signs it through the real
  `AgentCipherclerk::sign_action`. Matching requires the postcard layout, the
  v3 signing message, the ML-DSA key derivation, the deterministic signature,
  and the ctx to all agree simultaneously.
- **The Rust verifier ACCEPTS it** (`test/hybrid-verify.test.mjs` +
  `test/rust-verifier/`): a standalone Rust bin over path deps on the real
  `dregg-turn`/`dregg-cell` decodes the TS bytes with the real `postcard`/`Turn`
  and runs the real **`TurnExecutor::execute`** — the same public entry the node
  calls — at `require_pq` **OFF and ON**. Both accept. It re-implements nothing;
  every verdict is computed by `dregg-turn` itself.
- **The canaries** (a differential that cannot fail proves nothing):
  - sign classical where hybrid is expected → the byte differential goes **RED**
    (the correction-2 bug, reproduced on demand);
  - the same turn signed classical → executor **accepts at `require_pq=off`,
    REJECTS at `require_pq=on`** (`classical-only signature rejected:
    post-quantum (hybrid) authorization required`) — the cliff itself, proving
    the acceptance gate discriminates;
  - a hybrid signature bound to the **wrong turn nonce** → **REJECTED**
    (`hybrid: Ed25519 (classical) signature half failed`) — the v3 nonce binding
    is load-bearing, not decorative.
- The `hybrid authorization boundary` tripwire is **kept**, now guarding the
  other direction: if the Rust default ever stops being hybrid, the TS default
  silently becomes wrong, and that test is where you learn it.
- Suite: **88/88 green**.

### Cost (measured, not estimated)

| | classical | hybrid | delta |
|---|---|---|---|
| Turn wire size (1 effect) | 285 B | 5551 B | **+5266 B (19.5×)** |
| `signAction` | 0.57 ms | 17.07 ms | **+16.5 ms (30×)** |
| ML-DSA-65 keygen | — | 3.02 ms | once per `Identity` (cached) |

`dist/index.mjs` 20.49 KB → **6137 B gzipped**; `@noble/post-quantum`'s ml-dsa
adds ~37 KB unbundled (`ml-dsa.js` 29 KB + `_crystals.js` 7.8 KB), tree-shakeable
and only pulled by the signing path. **3309-byte signatures are not free**: the
19.5× wire growth is the dominant cost and is inherent to ML-DSA-65 (it is the
same cost the Rust SDK already pays). 17 ms/turn is acceptable for an
interactive signing step but would matter for bulk signing.

### What the `require_pq` flip now costs TS users: nothing

That is the point of this work. The same TS-signed turn is accepted at
`require_pq` OFF and ON (driven above), so the flip is a **no-op** for TS
callers on this code — no re-signing, no key ceremony, no API change. The
flip's TIMING remains ember's call; the signer is engineering, and it is done.
**Classical stays available and explicit** (`Identity.signActionClassical`) for
the pre-flip world and for verifiers predating `HybridSignature` — it is
accepted today and goes dark at the flip, exactly as Rust's
`sign_action_classical` does.

## Result: the published package works for a fresh consumer.

| Check | Result | Evidence |
|---|---|---|
| Installs clean from the registry | yes | `added 3 packages, found 0 vulnerabilities` — `@dregg/sdk` + `@noble/ed25519` + `@noble/hashes`. No `dregg-wasm` install nag (it is an *optional* peer). |
| ESM import (`import * from "@dregg/sdk"`) | yes | loads, 46 exports. |
| CJS require (`require("@dregg/sdk")`) | yes | loads, same 46 exports. |
| API produces valid turns | yes | `pay`, `turn().pay()`, `services.invoke` (with pay leg), `execution.lease` all construct + `.sign()` offline (pinned federation id, no node, no wasm) and expose the signed `Action`/`Effect`. |
| Turn ENCODER byte-faithful (postcard layout, incl. `provenance`, + v3 hash) | **yes at HEAD** (was NO for `grantCapability` on 0.3.0 — dropped `provenance`, ⚠ correction 1) | verified against a freshly-built wasm oracle; see below. |
| Action SIGNING MESSAGE matches Rust | **yes at HEAD** (was **NO on 0.3.0 and at HEAD until now** — TS was `sig-v2`, Rust is `sig-v3`; ✅ correction 3) | the v2 message is REJECTED by the real executor; the v3 one is accepted. Driven. |
| Signed-turn byte-identical to the current Rust signer | **yes at HEAD** (was NO — TS signed classical, Rust's default is HYBRID PQ; ✅ correction 3 closes ⚠ correction 2) | TS hybrid-signed turn == Rust default-signed turn, byte for byte, vs a fresh oracle, both sides signing. |
| Rust verifier ACCEPTS a TS-signed turn | **yes at HEAD**, at `require_pq` OFF **and ON** (was **NO at any setting** — the v2 message failed ed25519) | the real `TurnExecutor::execute` via `test/rust-verifier/`. |
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
error, not skip). Since correction 3 the differential no longer dodges the
signature: **both sides sign** and the whole hybrid-signed turn is compared byte
for byte, so drift in the postcard layout, the hashes, the signing message, the
ML-DSA derivation, the signing determinism, or the FIPS 204 ctx fails here
against **current** Rust. It remains a source-tree test (needs the `dregg-wasm`
dev dependency), not a fresh-consumer test.

`test/hybrid-verify.test.mjs` + `test/rust-verifier/` add the half a
byte-differential structurally cannot cover: an encoder-vs-encoder comparison
says the bytes MATCH, never that they are ACCEPTED. The harness runs the real
`TurnExecutor::execute` over the TS bytes at `require_pq` off and on. It is a
standalone cargo workspace (never feature-unifies onto the repo's resolve),
builds via `--manifest-path`, and **fails loud** if it cannot build.

✅ **The oracle now builds.** Both blockers noted in the previous revision are
clear: (b) the `starbridge-v2` `CustomProofStateBindingMismatch` match arm is
present on `main`, and (a) the wasm `CC` is handled — `pretest` needs
`CC_wasm32_unknown_unknown=$(brew --prefix llvm)/bin/clang` on a stock macOS box
(Apple clang has no wasm target). CI must still set that `CC`. **⚠ These two
blockers are the whole reason corrections 1 and 2 shipped false claims: an
oracle that cannot build is an oracle that never ran, and the prose filled the
gap. Keeping the oracle buildable IS the gate — not a convenience.**

⚠ **Oracle limitation (`sign_turn_v3` signs at nonce 0).** `sign_turn_v3` builds
a FRESH `AgentCipherclerk`, whose `next_turn_nonce()` (receipt-chain length) is
**0**, and signs every `Unchecked` action over that — it never reads
`turn.nonce`. Since `sig-v3` binds the nonce, any turn the oracle signs is only
self-consistent at nonce 0, so the byte differentials ride nonce 0 by
construction. This is a fidelity gap in `wasm/src/lib.rs` (out of scope here —
`wasm/` is read-only for this work) and is worth closing so the oracle can sign
at a caller-supplied nonce. The Rust-verifier harness has no such limit and
covers the nonce binding directly (incl. the wrong-nonce falsifier).

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

Everything above is on disk, **uncommitted and unpublished**. Publishing is
outward-facing and gated, and ember's standing call is that the SDK gets a real
overhaul before it is republished at all. Nothing here should be read as "ready
to ship" — it is a record of what a republish would need.

- **Version:** the public API **changed** (`Identity.signAction` takes a required
  `turnNonce`; the default emitted authorization is now `HybridSignature`; new
  `signActionClassical` / `mlDsaPublicKey` / `NodeClientOptions.nonce`). That is
  a **minor** (`0.4.0`), not the previously-planned `0.3.1` patch. `package.json`
  still pins `0.3.0` and is deliberately **not** bumped here.
- **What is broken on `0.3.0` (impact — worse than previously recorded):**
  **every signed turn**, not just `grantCapability`. `0.3.0` signs the
  `dregg-action-sig-v2` message; the node verifies `v3`, so the ed25519 check
  fails and the node **rejects the turn outright** (driven: `invalid
  authorization: Ed25519 signature verification failed`). pay, lease, service,
  transfer, set-field, events, grantCapability — all of it. The
  `grantCapability`/`provenance` defect (correction 1) is real but is now the
  *lesser* of the two: a turn that desyncs is moot when no turn authorizes at
  all. **`0.3.0` cannot submit any turn a node will accept.**
- **`0.3.0` disposition:** deprecate — the earlier "the front door works, a yank
  is likely unnecessary" reasoning **no longer holds**, because the front door
  does not work either. `npm deprecate @dregg/sdk@0.3.0 "signs the obsolete
  dregg-action-sig-v2 message; every signed turn is rejected by the node — use
  >=0.4.0"`. Whether to hard-`unpublish` is ember's call, but the deprecation is
  no longer optional.
- **Downstream:** anyone submitting turns (i.e. everyone). In-repo:
  `sdk-ts/extension` consumes sdk-ts **source** via a build alias, so it picks
  the fix up on rebuild; it typechecks clean against the new API and its
  `builder.sign()` call is unchanged.
- **Gate the publish on the test:** `publish-sdk-ts.yml` builds the wasm but
  **never runs `npm test`** — this is the root cause of both false claims, not a
  side note. A publish gated on a suite that never ran is a publish gated on
  nothing. Add `npm test` to the publish job (and to push/PR CI), with the wasm
  `CC` set so `pretest` can build the oracle. The Rust-verifier harness needs a
  cargo toolchain in CI (~80 s cold build; fails loud rather than skipping).

### Ordering: the flip is now unblocked from the TS side

The hybrid signer is **done and driven** (see "The hybrid PQ signer"), so
`require_pq` is no longer gated on TS work — but it *is* gated on this code being
published, since a published `0.3.0` client cannot produce a PQ half (and, as it
turns out, cannot produce an accepted turn at all). Do not flip `require_pq`
before a hybrid-capable SDK is published, or every JS/TS agent on a published
version drops offline — though on `0.3.0` specifically they are already offline.

## Verdict

`@dregg/sdk@0.3.0` builds well-shaped turns and **cannot get a single one
accepted**: it signs the obsolete `dregg-action-sig-v2` message while the node
verifies `v3`, so every signed turn is rejected on the ed25519 check. The
original "works for a fresh consumer's pay/lease/service front door" verdict
covered construction, imports, and offline shape — none of which is submission.
That is the real lesson of this file: **three revisions of verified-sounding
prose, each written against an oracle that was stale (1), then absent (2, 3)**.
The corrections did not come from re-reading the code more carefully; they came
from finally *building the oracle and running the verifier*.

At HEAD (uncommitted, unpublished) all three are closed and **driven**: the
encoder is byte-faithful incl. `provenance`; the signing message is `v3`; and
`Identity.signAction` emits a HYBRID post-quantum authorization (ed25519 +
ML-DSA-65) that is **byte-identical to the current Rust default signer** against
a freshly-built oracle and **accepted by the real `TurnExecutor::execute` at
`require_pq` both OFF and ON** — with canaries proving each gate can still fail.
The `require_pq` flip now costs TS callers nothing, on this code. Classical
stays available and explicit.

Still open: a republish is EMBER-GATED and wants the SDK overhaul, so `0.3.0`
remains the published (and broken) truth until then — deprecate it. CI must run
`npm test` with a buildable oracle, or this file will simply grow a correction 4.
The wasm oracle's `sign_turn_v3` signs at nonce 0 regardless of `turn.nonce` (a
`wasm/` fidelity gap, out of scope here). No live-node round trip (no reachable
node). The legacy `@dregg/sdk/wasm` subpath's unpublished `dregg-wasm` peer
remains a separate, lower note.
