# Path of Angels protocol boundary

Status: development authority for the protected beta.

Path of Angels is a separate Dregg federation whose game activity can produce
bounded **beta-canon field records**. A field record becomes alpha canon only
when the series curator signs an exact artifact promotion. Games never write
alpha canon directly.

## Semantic authority

The source of truth is `Dregg2.Games.PathOfAngels` in Lean. Runtime code may:

- load a byte-pinned Lean emission;
- render a state supplied by that emission;
- gather an action and submit it to the engine;
- verify a receipt and replay a transition;
- refuse an unknown version, rule, field, or artifact.

Runtime code must not invent a second transition function in Rust or
TypeScript. A UI fixture is not an authority and must be visibly rejected when
its manifest does not match the checked-in Lean emission.

## POAG1 bundle

The checked-in bundle lives at `poa/artifacts/poag1/`. Its manifest is canonical
JSON with no timestamp or host-dependent fields:

```json
{
  "format": "POAG1",
  "schema_version": 1,
  "source_digest": "sha256:<64 lowercase hexadecimal characters>",
  "authority": "Dregg2.Games.PathOfAngels",
  "artifacts": [
    {
      "path": "schema.json",
      "media_type": "application/json",
      "bytes": 0,
      "fnv1a64": "<16 lowercase hexadecimal characters>"
    }
  ]
}
```

The canonical v1 artifact set is:

- `schema.json`
- `catalog.json`
- `games/signal-triangulation.json`

The manifest pins every member but does not pin itself. Curator signatures and
content epochs bind the exact manifest bytes. Consumers reject unknown,
missing, duplicate, path-traversing, length-mismatched, or digest-mismatched
members.

## Receipt domains

Every signed message begins with one of these ASCII domain separators followed
by a NUL byte. Values are serialized in the order documented by the emitted v1
schema; textual concatenation is forbidden.

| Purpose | Domain |
|---|---|
| Game run | `pathofangels.network/run-receipt/v1` |
| Content epoch | `pathofangels.network/content-epoch/v1` |
| Canon promotion | `pathofangels.network/canon-promotion/v1` |
| Bazaar ingress | `pathofangels.network/bazaar-ingress/v1` |
| Devnet identity | `pathofangels.network/federation/v1` |

A run receipt binds at least the PoA federation id, player key, mission id,
mission/rules artifact digest, pre-state digest, post-state digest, bounded
contribution, monotonically increasing player counter, and signature.

A promotion binds the curator key, content epoch, exact POAG1 manifest digest,
exact beta artifact id and digest, target status, and monotonic curator counter.
No promotion by title, URL, mutable database row, or unpinned JSON is valid.

## Canon states

- **beta**: a game-originated field record. It may be queried, collected, or
  superseded, but it is not a statement by the series.
- **alpha**: an exact beta artifact promoted by the curator capability.
- **superseded**: retained for provenance but no longer current.

The public UI should use the diegetic terms **field record** and **series
archive**. The protocol uses beta/alpha because those names make the boundary
unambiguous in tests.

## Contribution boundary

Games may return only the fields declared by the Lean `Contribution` type:
bounded world metrics, score, and predeclared relic identifiers. Applying a
contribution is deterministic and saturates or refuses exactly as the Lean
model specifies. A game cannot:

- create a new metric or relic id;
- exceed its mission budget;
- promote or rewrite canon;
- spend `$DREGG` or grant gameplay power from holdings;
- alter a different federation's state.

## Privacy grades

Claims in UI, logs, and receipts use the weakest accurate grade:

1. `public`
2. `operatorVisibleHidingFri`
3. `processSeparatedThreshold`
4. `independentOperatorThreshold`

The protected beta starts at process separation unless shares are actually
held by independent operators. An in-process committee, multiple processes on
one operator's machines, or a wasm share in the same operator's extension must
not be described as no-single-operator privacy.

## Federation boundary

The PoA devnet has its own genesis, federation id, validator keys, data
directories, ports, metrics labels, and volume names. It may reuse Dregg
binaries and hosts; it must not reuse main-federation identity or mutable state.

The initial mesh is three validators, with the public edge acting only as a
reverse proxy. Anyone may run a follower, verify the lace, submit a signed turn,
or propose admission. Validator admission uses the Lean F-4 gate. Outsider
blocks remain excluded from the participant predecessor graph, wave clock, and
final order.

PoA v1 policy is vouch-first: two distinct admitted vouchers are required.
Transitive admission is the finite least fixed point rooted in genesis seeds.
An unrooted ring cannot admit itself. The bond branch remains disabled for PoA
until a live quote-asset-backed slashable lock is wired.

## Crown journey

The release gate is one reproducible journey:

1. a recognized Path of Angels video offers the opt-in companion;
2. the companion loads an exact POAG1 mission;
3. a legal action is decided by the Lean-owned rules;
4. a signed run receipt finalizes on the PoA federation;
5. the receipt mints or releases one bounded salvage asset;
6. the asset enters a sealed DrEX order;
7. a threshold committee clears it and a same-opening proof binds the private
   opening to the settled public consequence;
8. settlement transfers the exact asset atomically;
9. the bounded contribution updates beta world state;
10. the curator may promote the exact field record;
11. a fresh follower can verify the whole public chain of receipts.

Every step has a hostile twin: wrong federation, wrong domain, stale counter,
unknown mission, altered artifact, excessive contribution, duplicate relic,
wrong session/roster/share, insufficient threshold, replayed settlement, and
promotion without the curator capability must refuse.

## Deployment names

- `beta.pathofangels.network`: password-curtained primary beta surface.
- `node.pathofangels.network`: PoA node API; never the main Dregg node.
- service ports begin at `8421` (HTTP) and `9421` (peer/transport), subject to
  the checked-in deployment manifest.

The beta remains protected with HTTP Basic authentication until the curator
explicitly opens it. The password is deployment state and must not be embedded
in the web bundle or committed configuration.
