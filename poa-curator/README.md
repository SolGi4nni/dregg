# Path of Angels curator

This crate is the narrow Sentyr-facing authority edge for POAG1 content. It does
not implement game rules, contribution bounds, or world-state transitions. Those
remain in Lean and are emitted into the POAG1 bundle.

The component does six things:

1. loads `poa/artifacts/poag1/manifest.json` and rejects any non-v1, unknown,
   missing, duplicate, noncanonical-order, traversing, byte-length, SHA-256,
   FNV-1a, or JSON-shape mismatch;
2. selects a Lean-emitted mission, exact predeclared beta artifacts, and an
   optional Lean-emitted bounded preview fixture without recomputing semantics;
3. binds that catalog to the separately verified `poa-devnet.json` federation;
4. signs the **exact manifest bytes** under a content-epoch/counter domain; and
5. signs exact promote/supersede decisions over all four fields of the Lean
   `ArtifactRef` projection; and
6. emits a deterministic, keyless review projection for Sentyr without
   activating or inventing content.

Runtime hydration requires a live `MissionActivationOracle` to admit the exact
authenticated mission template plus detached activation digest. Promotion and
supersession additionally require a live `CanonAdmissionOracle` over the full
action. The crate has no allow-all adapters: production implementations must
invoke Lean's opaque activation witness and current-state admission (`beta` for
promotion, `alpha` for supersession, exact scope, revision, and counter). A
well-shaped signed request is not a canon transition by itself.

## Bounded multi-mission epochs

POAG1 v1 accepts one through three missions. Signal Triangulation remains the
required size-one base; Relay Repair and Salvage Lock are the only additional
descriptor paths. The manifest representation is exactly `schema.json`, then
`catalog.json`, then the selected game paths in ascending byte order. The
schema's `content_root.paths` must repeat that exact game order, and the content
root frames every selected descriptor in that order.

The catalog must contain exactly one mission per descriptor, ordered by strictly
increasing mission id. Mission ids, descriptor assignments, content sessions,
run seeds, exact artifact refs, and fixture ids are unique. Every mission shares
one catalog epoch and content root; deployment binding then requires every
mission federation to equal the separately verified devnet. Descriptor identity fields must
agree with its mission; fixtures must carry that mission's exact run seed. The
bounded ceilings are three missions, eight discoveries and sixteen relic ids per
mission, eight fixtures per mission, and twenty-four fixtures per epoch.

Game-specific transition payloads remain opaque Rust-side: the curator checks
their common identity header and byte commitment, then the
`MissionActivationOracle` asks Lean to admit the exact complete descriptor. Rust
does not acquire a second copy of Relay or Salvage semantics.

## Review an epoch without signing it

`preview-epoch` strictly loads and deployment-binds the exact bundle before it
prints deterministic JSON. The review includes the manifest and content roots,
deployment/federation identity, catalog epoch, and each mission's title,
ruleset, action cap, privacy/reward labels, budget, allowed relics, exact beta
artifact refs, descriptor path, and declared target visibility. It never looks
for an adjacent signature unless the complete verification tuple is supplied.

```sh
cargo run --manifest-path poa-curator/Cargo.toml -- preview-epoch \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment poa/deployments/epoch-1/poa-devnet.json
```

Unsigned output says `"signature_status": "absent"` and carries an explicit
`UNSIGNED WIP` notice. To report `"signature_status": "valid"`, all four
verification inputs are mandatory and must verify against the exact bytes:

```sh
cargo run --manifest-path poa-curator/Cargo.toml -- preview-epoch \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment poa/deployments/epoch-1/poa-devnet.json \
  --pin poa/config/curator-key.json \
  --signature poa/artifacts/poag1/manifest.sig.json \
  --epoch 1 --counter 2
```

Partial verification flags, stale counters, wrong pins, mismatched deployments,
and malformed or byte-drifted bundles refuse without producing preview JSON.
Even a signature-verified preview is not a Lean mission activation.

`manifest.sig.json` is deliberately detached and is not listed by the manifest
it signs. Its strict wire shape is:

```json
{
  "schema": "POA-CONTENT-EPOCH-SIGNATURE-V1",
  "manifest_sha256": "sha256:<64 lowercase hex>",
  "curator_pubkey": "<64 lowercase hex>",
  "content_epoch": 1,
  "counter": 1,
  "signature": "<128 lowercase hex>"
}
```

The verifier must receive the curator public key from outside the fetched
bundle. A bundle-provided key is not a trust anchor. A minimal external pin is:

```json
{"schema":"POA-CURATOR-KEY-V1","curator_pubkey":"<64 lowercase hex>"}
```

The library accepts the repository's canonical `dregg_types::SigningKey` and
calls `dregg_types::{sign,verify}`. It owns no cryptographic implementation. The
small operator binary is the only key-I/O edge; it creates a development beta
key as a raw 32-byte mode-0600 file and never prints secret bytes.

```sh
cargo run --manifest-path poa-curator/Cargo.toml -- keygen \
  --secret /secure/poa-development-curator.key --pin poa/config/curator-key.json

cargo run --manifest-path poa-curator/Cargo.toml -- sign-content \
  --secret /secure/poa-development-curator.key \
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment "$POA_ROOT/poa-devnet.json" --epoch 1 --counter 2

cargo run --manifest-path poa-curator/Cargo.toml -- verify-content \
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment "$POA_ROOT/poa-devnet.json" --epoch 1 --counter 2
```

Run `scripts/poa-devnet.sh verify` before the ceremony. The Rust binding checks
schema/domain/federation equality; it deliberately does not duplicate the node
kit's genesis, validator-key, or operator-policy verification.

The checked-in three-game bundle replaces bytes already signed at epoch 1,
counter 1. Its successor ceremony therefore retains catalog epoch 1 and advances
the rollback counter to 2. The old envelope names a different exact manifest
digest and is refused before signature verification.

The cross-runtime byte/signature vector is
`test-vectors/content-epoch-v1.json`. The signing domain in that vector is the
exact ASCII byte string `pathofangels.network/content-epoch/v1\0`; aliases are
different protocols and must refuse. Those epoch-1 bytes remain unchanged; the
multi-mission set is committed through the existing exact-manifest signature,
not a new signing protocol. Signing also refuses an epoch argument different
from the single epoch authenticated in the catalog.

Canon actions share the exact domain
`pathofangels.network/canon-promotion/v1\0`; the signed action tag distinguishes
promotion from supersession. Its cross-runtime vector is
`test-vectors/canon-promotion-v1.json`.

## Public media companion ceremony

The browser extension discovers episode/post companions from the separate
GET/HEAD-only `companion.pathofangels.network` static origin. The beta and node
remain behind Basic Auth. A `poa-companion/v3` draft binds one exact YouTube
video plus channel, or one exact X post, to the PoA origin, federation,
deployment, verified content epoch/counter, exact POAG1 manifest digest,
independent route sequence, lifetime, actions, and one through eight exact POAG1
asset pins. The signer rejects foreign actions and any asset that does not match
the authenticated bundle's path, URL, media type, byte length and SHA-256.

```sh
cargo run --manifest-path poa-curator/Cargo.toml -- sign-companion \
  --secret /secure/poa-development-curator.key \
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment poa/deployments/epoch-1/poa-devnet.json \
  --content-signature poa/artifacts/poag1/manifest.sig.json \
  --content-epoch 1 --content-counter 4 \
  --draft /secure/review/episode-companion-v3.json \
  --output poa/companion/public/v1/youtube/REAL_VIDEO_ID.json
```

`verify-companion` takes the same public inputs plus `--input` and no secret.
Both commands re-run the content signature and deployment weld. The output is
refuse-overwrite and contains only the strict manifest, public signer, and
signature. No test key is compiled into either command. The checked-in
production route tree is empty until the actual episode identifiers are
author-supplied; test placeholders never leave the test directories.

The component is currently an intentional nested workspace. Its scoped gate is:

```sh
cargo nextest run --manifest-path poa-curator/Cargo.toml
cargo clippy --manifest-path poa-curator/Cargo.toml --all-targets -- -D warnings
```

Artifact directories are expected to be operator-owned, immutable staging
trees. Final-component symlinks are refused and reads use one bounded,
`O_NOFOLLOW` descriptor; an `openat2`/directory-fd walk remains future hardening
for hostile writable ancestor directories.
