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
- `src/signal-runtime.js` is a generic table interpreter and replay recorder.
  It does not score guesses or select outcomes itself.
- `public/artifacts/poag1/` is generated material copied from `poa/`; never
  hand-edit it here.
- The curator panel is a preview/inspection surface. Signing and canon
  promotion remain the responsibility of the curator tool and capability.
