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

`tests/mission-launch-browser.html` is the real-DOM controller harness for the
exact candidate Relay/Salvage bytes. Serve the repository root, open that path,
and require `body[data-status="pass"]`. It deliberately does not pretend the
candidate epoch is signed; signature/rollback checks remain separate and the
production boot stays sealed until operator signing.
