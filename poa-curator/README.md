# Path of Angels curator

This crate is the narrow Sentyr-facing authority edge for POAG1 content. It does
not implement game rules, contribution bounds, or world-state transitions. Those
remain in Lean and are emitted into the POAG1 bundle.

The component does five things:

1. loads `poa/artifacts/poag1/manifest.json` and rejects any non-v1, unknown,
   missing, duplicate, traversing, byte-length, SHA-256, FNV-1a, or JSON-shape
   mismatch;
2. selects a Lean-emitted mission, exact predeclared beta artifacts, and an
   optional Lean-emitted bounded preview fixture without recomputing semantics;
3. binds that catalog to the separately verified `poa-devnet.json` federation;
4. signs the **exact manifest bytes** under a content-epoch/counter domain; and
5. signs exact promote/supersede decisions over all four fields of the Lean
   `ArtifactRef` projection.

Runtime hydration requires a live `MissionActivationOracle` to admit the exact
authenticated mission template plus detached activation digest. Promotion and
supersession additionally require a live `CanonAdmissionOracle` over the full
action. The crate has no allow-all adapters: production implementations must
invoke Lean's opaque activation witness and current-state admission (`beta` for
promotion, `alpha` for supersession, exact scope, revision, and counter). A
well-shaped signed request is not a canon transition by itself.

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
  --deployment "$POA_ROOT/poa-devnet.json" --epoch 1 --counter 1

cargo run --manifest-path poa-curator/Cargo.toml -- verify-content \
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment "$POA_ROOT/poa-devnet.json" --epoch 1 --counter 1
```

Run `scripts/poa-devnet.sh verify` before the ceremony. The Rust binding checks
schema/domain/federation equality; it deliberately does not duplicate the node
kit's genesis, validator-key, or operator-policy verification.

The cross-runtime byte/signature vector is
`test-vectors/content-epoch-v1.json`. The signing domain in that vector is the
exact ASCII byte string `pathofangels.network/content-epoch/v1\0`; aliases are
different protocols and must refuse.

Canon actions share the exact domain
`pathofangels.network/canon-promotion/v1\0`; the signed action tag distinguishes
promotion from supersession. Its cross-runtime vector is
`test-vectors/canon-promotion-v1.json`.

The component is currently an intentional nested workspace. Its scoped gate is:

```sh
cargo nextest run --manifest-path poa-curator/Cargo.toml
cargo clippy --manifest-path poa-curator/Cargo.toml --all-targets -- -D warnings
```

Artifact directories are expected to be operator-owned, immutable staging
trees. Final-component symlinks are refused and reads use one bounded,
`O_NOFOLLOW` descriptor; an `openat2`/directory-fd walk remains future hardening
for hostile writable ancestor directories.
