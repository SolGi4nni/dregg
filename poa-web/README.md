# Path of Angels beta terminal

An install-free, static web surface for the *Path of Angels* ship-side game.
It is intentionally an inhabited field terminal rather than a token or
governance dashboard. The show decides where the Khovokhi goes; this terminal
is where expedition crews learn what the ship contains.

Game semantics are not authored in JavaScript. The browser loads the versioned
`POAG1` bundle emitted from Lean, authenticates the exact manifest using the
detached curator content-epoch signature and an external key pin, checks both
SHA-256 and drift pins for every object, and only then exposes a game control.
A missing, stale, malformed, extra, replayed, or modified artifact leaves the
terminal sealed.

## Run

From the repository root:

```sh
cd poa-web
npm run artifacts
npm test
npm run serve
```

Then open <http://127.0.0.1:4173>. `npm run artifacts` copies the canonical
bundle from `../poa/artifacts/poag1`; it does not generate or reinterpret it.
The server is dependency-free and the finished directory can also be served by
Caddy, nginx, or any static host. The deployment must place the external key pin
at `/poa-curator-key.json`; it is deliberately not inside the POAG1 bundle.
The sync command expects the authorized files at
`poa/artifacts/poag1/manifest.sig.json` and `poa/config/curator-key.json` and
refuses to stage an unsigned or rollback-mismatched content epoch.

To exercise the fail-closed screen without changing the canonical bundle:

```sh
mv public/artifacts/poag1/manifest.json /tmp/poag1-manifest.json
npm run serve
# restore it afterwards
mv /tmp/poag1-manifest.json public/artifacts/poag1/manifest.json
```

## Boundary

- `src/poag1.js` validates and pins the envelope; `src/content-epoch.js`
  authenticates its exact bytes and rejects epoch/counter rollback.
- `src/mission-catalog.js` accepts exactly Signal, Relay, and Salvage from one
  authenticated content epoch, checks their shared three-descriptor content
  root, manifest-bound beta artifacts, zero-economy policy, and preview shapes.
- `src/mission-launcher.js` is the exhaustive controller switch, and its
  `INSTALLED_GAME_IDS` is the single list of games this client can play. Unknown
  games and catalog/descriptor mismatches refuse; neither can fall back to
  Signal.
- `src/game-rack.js` holds the presentation record per game and builds the rack.
  A record cannot enrol its own game: whether a card is `open`, `sealed`,
  `reserved`, or `unsupported` is decided by the signed catalog and the dispatch
  table above.
- `src/run-summary.js` is the one end-of-run screen and the one status ladder.
  `practice` is its own branch and cannot be advanced into the judged path.
- `src/rack-results.js` is a note this browser keeps for itself. Practice and
  judged bests live in separate buckets and are never merged.
- `src/today-board.js` reads what is true today. It re-derives and verifies the
  curator's slot-opening signature rather than believing `open: true`, and every
  unknown lands as a sealed tile.
- `src/signal-runtime.js` consumes Signal's compact outcome oracle. It does not
  score guesses or select outcomes itself.
- `src/finite-table-runtime.js` consumes the complete legal-state closure and
  state × action rows used by Relay Repair and Salvage Lock. Their strict
  decoders and dormant UI mounts live in `relay-*` / `salvage-*`; none of these
  files contains the Lean transition functions.
- `public/artifacts/poag1/` is generated material copied from `poa/`; never
  hand-edit it here.
- The curator panel is a preview/inspection surface. Signing and canon
  promotion remain the responsibility of the curator tool and capability.

A drill opens only after the five-file manifest, curator activation, complete
catalog, and every descriptor validate; until then its card is a sealed slot. A
browser transcript is not a RunReceipt and does not grant score, contribution,
salvage, ranking, or canon status — the end screen's ladder says so on every
run. The Galley is a separate versioned-node surface described below; its
journal receipts must never be inferred from a local drill.

## Adding a game to the rack

Two files, no surgery on the board.

1. **A presentation record** in `GAME_RACK` (`src/game-rack.js`), with exactly
   these fields — `loadRackEntry` refuses any other set:

   | field | what it is |
   |---|---|
   | `gameId` | lowercase id, equal to the descriptor's `game_id` and the catalog's |
   | `name` | display name, ≤ 48 characters |
   | `flavor` | ONE line, ≤ 96 characters, no newline. Mechanical-poetic and setting-neutral: vents, decks, relays, holds. No lore |
   | `session` | `"quick-drill"` (~1 min), `"standard"` (~5 min), `"expedition"` (~10 min), or `null` for a berth |
   | `shape` | the `descriptor-shape.js` shape the emitted descriptor actually has, or `null` for a berth |
   | `eyebrow` | small-caps place label, ≤ 32 characters |
   | `boardLabel` | the board's accessible name, ≤ 64 characters |
   | `columns` | board grid columns, 1–8 |

   `session` and `shape` are null together or not at all, and a record with
   either null can never reach the `open` state. `tests/game-rack.test.mjs`
   checks the claimed shape against the real emitted descriptor.

2. **A controller** in the `FINITE_CONTROLLERS` table of
   `src/mission-launcher.js`, mounting as `(root, descriptor, callbacks)` and
   honouring `callbacks.session`, `onTranscript`, `onReset`. A game landing in
   an existing shape needs no new runtime: reuse `mountFiniteTableController`.

The end screen needs nothing per game — `runOutcome` in `src/run-summary.js` is
keyed by SHAPE, so a new machine-family or parametric game already reports
correctly. Only a genuinely new shape teaches it a row, and it refuses until it
is taught rather than reaching for the nearest one.

Nothing else is required. The card appears the moment the record exists (as a
berth), becomes `sealed` when the controller is installed, and `open` when the
signed catalog enrols the mission.

## Ship platform and evidence grades

The overview is also the ship's between-episode terminal. It joins seven visible
organs without pretending they share one authority:

- **Field drills** consume curator-signed POAG1 content. That signature says
  which rules were offered; it is not a receipt for a player's run.
- **Crew expedition** and **Archive intake** read the small, byte-pinned
  provenance manifests for their Lean-emitted finite tables. The multi-megabyte
  tables stay lazy until their respective labs open.
- **Flight Recorder** checks the configured public predecessor/successor chain.
  The current source is an explicitly labeled three-transition rehearsal, and
  linked replay is never presented as consensus finality.
- **Crew muster** makes the local expedition roles legible while stating that
  officer identity, custody, injury, and progression are not persistent yet.
- **Dark Bazaar** exposes inventory, private-order, clearing, and settlement as
  four independent locked gates. A decorative market cannot make any of them
  true.
- **The Galley** reads the frozen `POA-GALLEY-*-V1` session/status envelopes,
  prepares one opaque action token through the same-origin node, sends the exact
  returned postcard to `dregg.signTurnV3`, and checks the observed receipt
  postcard against its adjacent SHA-256 checksum. That checksum is transport
  integrity, not canonical Dregg receipt verification. Its projection remains
  deliberately opaque until the authoritative presentation schema is frozen.

`src/platform-terminal.js` is a projection over these existing sources. It does
not sign, score, settle, promote canon, or invent a browser fallback. Every
source is loaded and graded independently, so one refusal cannot be hidden by a
different green instrument or erase healthy evidence from the page.

## The game as a DrEX pressure harness

The locked organs describe engineering contracts, not a promise that UI work
has completed them. Platform depth should open only as Dregg/DrEX can supply the
corresponding receipt:

| Game organ | Player loop | Capability required before it can persist |
| --- | --- | --- |
| Watch cycle | rotating drills, one clean run, crew upkeep | authenticated cycle definition, replay protection, settled RunReceipt |
| Galley | take a maintenance/Commons action and inspect its journal wake | sequence-expiring node action, exact signed turn postcard, range/head-bound replay summary, durable pending-intent coordinates, canonical receipt verifier |
| Officer | role, loadout, injury, recovery, reputation | wallet-bound but privacy-conscious profile capability and versioned state transition |
| Expedition | assemble a crew, cross a deck, extract or withdraw | Lean-authored joint state machine, participant signatures, exact contribution and custody output |
| Field archive | compare evidence, form a beta record, seek promotion | artifact lineage, curator capability, supersession and alpha/beta provenance |
| Bazaar | list salvage, submit a sealed order, clear, exchange | owned inventory, private order commitment, same-opening proof, threshold clearing, atomic settlement receipt |
| Choir | answer a ship-scale question with bounded influence | eligibility snapshot, ballot privacy where promised, tally proof, quorum/weight policy, finalized outcome receipt |
| Flight Recorder | inspect what the public system can prove happened | canonical event coordinates, digest continuity, availability window, explicit finality source |

This division is deliberate. Lean should own the state machines, admissibility
rules, contribution algebra, market/ballot policy, and receipt predicates.
Rust and the node should transport, persist, prove, and serve those decisions;
the browser should render them and fail closed. The PoA devnet becomes useful
when a second node can independently replay and verify these exact transitions,
not merely when the primary server can display them.

### Galley V1 wire

The web terminal and extension use one contract and one method set:

- `GET /api/poa/galley/v1/session`
- `POST /api/poa/galley/v1/command` with only
  `POA-GALLEY-COMMAND-PREPARE-V1` plus the server-issued action token
- normal `dregg.signTurnV3(postcard, federationId)` submission
- `GET /api/poa/galley/v1/status`, locating the result by exact turn hash

The page resolves the permissioned `window.dregg.getActiveIdentity()` before
its first session request. All three node requests carry exactly
`X-Dregg-Actor: <64 lowercase hex>`; the command JSON still contains no player
field. The header is a claimed public personalization key, not authentication,
eligibility, signer evidence, or finality. If identity sharing is unavailable
or declined, the Galley remains read-only and sends no session request.

The direct page signer result is also treated as untrusted admission evidence.
`submitted` and `queued` results must return the exact prepared `turnId`; any
returned receipt or node turn hash must agree with it. Only an exact
`submitted` result starts journal observation. Queued, refused, declined,
mismatched, malformed, and thrown-error outcomes stay distinct in the UI and
leave the durable intent for exact later reconciliation or sequence expiry.

Expiry is relative to the Galley journal (`expires_after_sequence`), matching
the Lean runtime rather than trusting browser or server wall clocks. Before a
postcard reaches the signer, the web app and extension durably record only its
world/aggregate/intent/turn coordinates. A restart keeps that intent pending;
it is removed only when the same world reports the exact turn with a
checksum-matched postcard, or when the journal sequence passes its expiry.
The replay window is a suffix whose total, range, and head are bound to the
current projection instead of being accepted as unrelated node testimony.

Caddy exposes those node routes to this site under `/node`. The browser sends
no JSON player field: authoritative signer identity comes from the signed Dregg
turn, never from the preparation header. Ordinary
actions need no Solana wallet. Holder sponsorship is intentionally unadvertised
and refused in V1 until eligibility is a deployment-pinned,
federation-verifiable certificate; a local RPC receipt is not enough. The
byte-pinned cross-client specimen is
`tests/fixtures/galley-wire-v1.json`.

The deeper game can therefore grow outward—crew quarters, cooperative deck
sorties, salvage collections, research plans, auctions, recovery clocks, and
eventually Aspect companions—without collapsing everything into token voting.
Each loop starts local, gains an exact receipt, then gains federation and private
settlement only when those layers exist. Fictional discoveries remain beta
records until the curator deliberately promotes an exact artifact into the
series archive.

`tests/mission-launch-browser.html` is the real-DOM controller harness for the
exact candidate Relay/Salvage bytes. Serve the repository root, open that path,
and require `body[data-status="pass"]`. It deliberately does not pretend the
candidate epoch is signed; signature/rollback checks remain separate and the
production boot stays sealed until operator signing.
