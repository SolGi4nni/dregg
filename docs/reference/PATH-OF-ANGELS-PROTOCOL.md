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

The first complete internal network evaluator is
`Dregg2.Games.PathOfAngels.NetworkJudge.processSignalWire`. It strictly decodes
the complete Signal config, world, canon state, finalized carrier, and request;
replays the Lean game; applies the atomic canon/world/counter transition; and
emits a canonical receipt plus successor. `verifySignalTransition` recomputes
that exact transition before accepting output bytes, and the native FFI has no
Rust semantic fallback. None of those facts authenticate a caller-authored
`FinalizedCarrier`: a host adapter must replace submitted Canon/config with
persisted active state, derive the carrier from an already-finalized Dregg turn,
and bind the AIR-authenticated pre-state root before the result is authoritative.

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
      "fnv1a64": "<16 lowercase hexadecimal characters>",
      "sha256": "<64 lowercase hexadecimal characters>"
    }
  ]
}
```

The canonical v1 artifact set is nine members, PATH-ASCENDING — the order is not
decoration, because the content root is framed `path_ascending` and a wrongly
ordered list binds a *different* root rather than raising an error:

- `schema.json`
- `catalog.json`
- `games/artificer-logic.json`
- `games/black-box-reconstruction.json`
- `games/deck-descent.json`
- `games/relay-repair.json`
- `games/salvage-lock.json`
- `games/signal-triangulation.json`
- `games/vent-crawl.json`

This list is a claim about `poa/artifacts/poag1/manifest.json` and about
`POAG1_EXPECTED_ARTIFACTS` in `poa-web/src/poag1.js`, and the two are compared
against `Emit.POAG1_GAME_PATHS` by `poa-web/tests/bundle-enrolment.test.mjs`. It
said five until 2026-08-09, which is the interval in which four games were
enrolled and this file was not touched.

The manifest cryptographically pins every member but does not pin itself.
Curator signatures and content epochs bind the exact manifest bytes. FNV-1a is
only a cheap reproducibility canary; SHA-256 is the content-integrity pin.
Consumers reject unknown,
missing, duplicate, path-traversing, length-mismatched, or digest-mismatched
members.

## Receipt domains

Every signed message begins with one of these ASCII domain separators followed
by a NUL byte. Values are serialized in the order documented by the emitted v1
schema; textual concatenation is forbidden.

| Purpose | Domain |
|---|---|
| Expedition judgement envelope | `pathofangels.network/expedition-judgement-receipt/v2` |
| Lean judge input digest slot | `pathofangels.network/lean-judge-input-digest/v2` |
| Lean judge output digest slot | `pathofangels.network/lean-judge-output-digest/v2` |
| Content epoch | `pathofangels.network/content-epoch/v1` |
| Canon promotion | `pathofangels.network/canon-promotion/v1` |
| Bazaar ingress | `pathofangels.network/bazaar-ingress/v1` |
| Devnet identity | `pathofangels.network/federation/v1` |

The two judge-digest domains label fixed 32-byte slots inside the v2 expedition
envelope; they are not independently signed claims. The outer signature binds
their order and every other claim field. Version 1 expedition envelopes are
incompatible and must be reissued rather than reinterpreted.

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
contribution is deterministic and refuses on overflow exactly as the Lean model
specifies; clipping or saturation is not permitted. A game cannot:

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
reverse proxy. A receipted `join --follow-only` node may verify the lace without
making an admission request; applying for admission is a separate operator act.
Outsider blocks remain excluded from the participant
predecessor graph, wave clock, and final order.

The target PoA admission policy is vouch-first: two distinct admitted vouchers
are required. Transitive admission is the finite least fixed point rooted in
genesis seeds. An unrooted ring cannot admit itself. The bond branch remains
disabled for PoA until a live quote-asset-backed slashable lock is wired.

Current deployment limitation: the node's production admission caller still
feeds the constitutional participant set as both seeds and candidates and has no
live vouch rows. Therefore a Join remains a follower/proposal followed by manual
committee ratification; the two-vouch path is not advertised as live until the
chain-derived vouch registry reaches the F-4 gate.

The public epoch-1 follower trust root is
`poa/deployments/epoch-1/poa-devnet.json` plus its byte-pinned sibling
`bundle/genesis.json`. `release-lock.json` binds those bytes to the active
release receipt's node, semantic source-tree, portable image, runtime-base, and
Linux-gate pins without publishing any validator key. Epoch 1 honestly records
`proposal_neutral_follow=false`: its pinned binary predates the source policy,
so live follower sync remains closed until a newly built and gated receipt binds
that capability to the replacement binary. Federation-bound POAG1
artifacts are emitted only after such a genesis exists; there is no synthetic
pre-genesis federation label.

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
