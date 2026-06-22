# Review — PLAYGROUND web surface

Date: 2026-06-06
Reviewer: subagent (review-first; no risky refactors applied)
Surface dir: `/Users/ember/dev/breadstuffs/site/playground/`
Live serve: `https://devnet.dregg.fg-goose.online/playground/` (serves the modular
`site/playground/index.html`; `site/dist/playground/*` is byte-identical to src)

## TL;DR

The playground is an **entirely browser-local WASM demo gallery**. It does NOT
submit turns, craft node actions, hit the faucet, or read any node receipt /
witness / event API. Every "real" value comes from the in-browser
`pkg/dregg_wasm.js` runtime (`getWasm()`) and the seeded `studio-embed.js`
in-memory runtime — never from `https://devnet.dregg.fg-goose.online`.

Consequences for the task's framing:

- The README's **`/api/turns/submit` "call forest is empty" blocker does not
  affect the playground** — the playground never calls `/api/turns/submit` and
  never constructs a call forest. (That blocker lives in the submit path
  exercised by `scripts/devnet-smoke.sh` / explorer, not here.)
- **Faucet** (`POST /api/faucet`, rate-limited) is **never called** by the
  playground. (Live check: `GET /api/faucet` → 405, so the endpoint exists and
  is POST-only; the playground just doesn't use it.)
- The node **API contract** (receipts `receipt_hash`/`turn_hash`/`has_witness`/
  `witness_count`, `/api/receipts/{hash}/witnesses` → `witnessed_receipts` +
  `artifact_format:"DWR1"`/`witness_artifacts`, events `proof_status`) is
  **not consumed anywhere in the playground**, so there is nothing in the
  playground to bring into alignment with it. Those fields are honored by the
  explorer / devnet-smoke surfaces. Live spot-check confirmed the node emits
  the events contract: `/api/events[0]` has
  `{status:"committed", proof_status:"not_required", turn_hash, cell_id,
  effects:["faucet_materialized_cell"]}`.

So the playground is **healthy as a local demo** but contains **dead
network-integration scaffolding** that pretends to talk to the live node and
silently no-ops. The honesty gap is the main finding.

## What the playground lets a user do

All browser-local, no network writes:

- Tokens / attenuation, STARK proofs, Merkle trees, Datalog policy, private
  notes, capabilities, sovereign cells, bearer caps, factories, private
  transfers, proof composition, gallery, federation (real wasm BFT committees +
  hash-chained blocks, all in-browser), marketplace, effect VM, consensus
  (blocklace) sim, circuit playground, code sandbox, blinded/programmable
  queues, ring trades, inboxes, batch executor, nameservice, delegation v2.
- "Open in Starbridge" deep links to `/starbridge/?at=dregg://…` (live: 200).
- Header nav links (`/apps.html`, `/learn.html`, `/paper.html`, `/demo.html`,
  `/explorer/`, `/starbridge/`) all resolve 200 on the live node.

No "submit turn", no "craft action against node", no "faucet" UI exists.

## Findings (prioritized)

### 1. [MEDIUM — honesty/dead-code] Live-network scaffold is exported but never wired

`playground.js` exports `connectToLiveNetwork()`,
`disconnectFromLiveNetwork()`, and the `state.liveMode`/`state.liveConnection`
fields, plus `handleLiveMessage()`. Grep across all `sections/*` shows **zero
callers** — no UI button, no boot call. The entire WebSocket live path is dead.

- `site/playground/playground.js:348` `connectToLiveNetwork` — no callers.
- `site/playground/playground.js:405` `disconnectFromLiveNetwork` — no callers.
- `site/playground/playground.js:415` `handleLiveMessage` — only reachable from
  the dead connect path.

Worse, the message contract it implements is **invented**: it handles
`msg.type` of `state_update` / `new_block` / `receipt` (lines 417/422/426).
None of these message types exist in the node. The live `/ws` endpoint returns
**401** (auth-gated; a browser has no bearer token), so even if wired it would
fail to connect. Recommendation: either delete this scaffold or gate it behind
a clearly-labeled "experimental / not implemented" toggle. Do NOT leave it as
silent dead code implying live connectivity exists.

### 2. [MEDIUM — contract mismatch on a dead path] `discovery.json` has no `gateway` key

`fetchFederation()` and `connectToLiveNetwork()` read fields that
`discovery.json` does not contain:

- `site/playground/playground.js:330` `state.federation.nodes = data.federation?.length` — live `discovery.json.federation` is `[]`, so nodes is **always 0**.
- `site/playground/playground.js:332` `state.federation.gateway = data.gateway || null` — **no `gateway` key** exists in any produced discovery.json (verified: only the playground *consumes* `gateway`; nothing *produces* it).
- `site/playground/playground.js:355` `if (data.gateway?.ws)` — always falsy, so the WS URL always falls back to the hardcoded `wss://devnet.dregg.fg-goose.online/ws` at line 350.

Net: the "Federation" panel in the right rail will show Status `online` (the
fetch succeeds) but Nodes `--` and Commit = the discovery commit. This is the
contract that *does* matter to the playground (its only real node-API read), and
it's partially stale: it expects a `federation[]` of nodes and a `gateway`
object that the current solo-node discovery.json doesn't emit.

Recommendation (needs design decision, not trivially-safe): either (a) have the
discovery generator emit `gateway: { ws, http }` and a populated `federation[]`,
or (b) simplify `fetchFederation()` to only read fields discovery.json actually
provides (`federation`, `commit`, `updated_at`) and drop the `gateway` read.

### 3. [LOW — dead section] `ci-results` section is orphaned

`sections/ci-results.js` exports `initCiResults()` and targets
`#section-ci-results`, but:

- `playground.js` does **not** import or call `initCiResults` (not in the
  import block lines 4–32, not in `main()` lines 468–494).
- `index.html` has **no** `<div id="section-ci-results">` and **no** nav item.

So the whole section is unreachable dead code. It also fetches
`../../demos/results.json` (`sections/ci-results.js:149`), a path that, from
`/playground/`, resolves to site root `/demos/results.json` — not verified to
exist. Recommendation: either wire it in (add nav item + section div + import +
init + verify `results.json` is deployed) or delete `ci-results.js`.

### 4. [LOW — stale comment] "3 validators, one gateway, local receipts"

`site/dist/playground.html:543` (the separate static landing page, not the app)
describes a federation topology that doesn't match the current solo node
(`/status` → `federation_mode:"solo"`, `peer_count:0`, `latest_height:0`). Cosmetic
copy on a marketing page; flag for ember, low priority.

### 5. [INFO — retired sections] `sections/_retired/*`

`full-turn-proof.js`, `tiered-revocation.js`, `crossfed.js` are in `_retired/`
and not imported. Fine as-is; noting so a future cleanup doesn't mistake them
for live code.

## API-contract conformance

The playground consumes exactly one node-adjacent artifact: `discovery.json`
(static file, served by Caddy, not the dynamic API). It reads `federation`,
`commit`, and the non-existent `gateway` (finding #2). It does **not** touch any
`/api/*` endpoint, so the receipt/witness/event contract from
`deploy/aws/README.md` is **out of scope for this surface** — there is no
field-name drift to fix because no contract fields are referenced. The contract
is the explorer's / devnet-smoke's responsibility.

## Safe fixes applied

None. Every issue found is dead-code removal or a design decision
(discovery.json schema), which the review-first rules classify as refactors to
hand to ember rather than apply blind. No typos, dead links, wrong endpoint
paths, or broken contract field-names were found that could be fixed in a
trivially-safe, behavior-preserving way. (All header nav links resolve 200;
src and `dist` copies are byte-identical.)

## Recommendations for ember (file:line)

- Decide the fate of the dead live-network path: delete
  `site/playground/playground.js:343-433` (connect/disconnect/handleLiveMessage
  + `liveConnection`/`liveMode` state at :58-59) OR build a real, auth-aware,
  clearly-experimental "Live network" toggle. Today it is silent dead code that
  implies a live capability the playground does not have.
- Reconcile `discovery.json` schema with `fetchFederation()`
  (`site/playground/playground.js:324-337`): drop the `gateway` read or emit it.
- Resolve `ci-results` (`site/playground/sections/ci-results.js`): wire it in
  (nav + section div + import + `main()` init + confirm `/demos/results.json`
  deploys) or delete it.
