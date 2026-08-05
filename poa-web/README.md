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
- `src/mission-launcher.js` is the exhaustive controller switch. Unknown games
  and catalog/descriptor mismatches refuse; neither can fall back to Signal.
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

The terminal exposes all three selectors only after the five-file manifest,
curator activation, complete catalog, and every descriptor validate. All play is
still visibly `LOCAL // UNSETTLED`: a browser transcript is not a RunReceipt and
does not grant score, contribution, salvage, ranking, or canon status.

## Ship platform and evidence grades

The overview is also the ship's between-episode terminal. It joins six visible
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
