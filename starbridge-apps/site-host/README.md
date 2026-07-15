# starbridge-site-host — the write control plane for verified microsite hosting

A hosted minisite is a cell: its content (path → asset) carries a real
sorted-Poseidon2 `content_root` commitment — the same hash family, heap-root
function, and 8-felt faithful widening the kernel commits an umem heap with — so a
stranger re-witnesses the served bytes against the same collision-resistant root the
kernel understands. This crate is the missing **write** half: the cap-gated,
lease-funded, receipted publish turn.

```
  POST /v1/sites/<name>/publish            (cap-gated, lease-funded, receipted)
    headers: Authorization: Bearer dga1_…  (site-host/<name> cap)
    body:    a serialized SiteContent (the built bundle, path → asset)
       │  1. authorize  — verify the dga1_ cap → the owner subject
       │  2. fund       — a resident non-lapsed hosting lease covers the owner
       │                  (else 402 + an x402 topup hint to auto-fund + retry)
       │  3. publish    — SiteRegistry::publish → SiteCell + signed receipt
       ▼
    201 { published, name, owner, content_root, url, signer, receipt }
```

`SitePublishHandler::respond` is the **one** value-level turn both a CLI (calls it
directly with a decoded credential) and an HTTP gateway (adapts a request into it)
drive — there are no HTTP-server types in the core.

## The three gates

- **cap-gate** (`publish`) — the publish is authorized by a presented `dga1_`
  credential carrying the `site-host/<name>` capability, verified against the
  configured root (`webauth-core` / `dregg-agent`'s credential core). The verified
  subject becomes the published cell's owner; a cap for a different site, a foreign
  root, or none at all is refused (401/403).
- **funding-gate** (`funding`) — a publish is admitted only against a resident,
  non-lapsed `hosted_lease::HostedLease` covering the owner. No lease / a lapsed
  lease fails **closed** (402) — but the refusal carries an **x402-style topup hint**
  (`TopupHint`) naming the lease, the rent asset, an amount, and the retry endpoint,
  plus an `X-Payment-Required` header, so an agent client auto-funds the lease and
  re-POSTs. A self-healing pay loop, not a dead end.
- **receipt** (`registry`) — a publish leaves a `PublishReceipt`; a `signed`
  registry seals it with an ed25519 attestation over the binding fields
  `(seq, name, owner, content_root, asset_count)`, re-verifiable with no trust in the
  host (`verify_receipt`). A tampered field breaks the signature.

## Composition

- **launchpad** (`launch`) — a launch listing becomes a publishable landing page
  through the **same** control plane, its image + metadata content-addressed on IPFS
  (`dregg-ipfs`): `landing_page(listing, ipfs, cfg)` pins the image and a canonical
  metadata JSON, then assembles a self-contained `SiteContent` you publish like any
  other site. A launch and its site share one turn.
- **the read plane** — the parameterized apex (`HostConfig`) resolves `<name>.<apex>`
  to a published cell; the metered serving path is the resident `agent-platform`
  serve loop (not re-implemented here). The apex is configuration — there is no
  hardcoded product domain.

## Durability, metering, quotas, lifecycle

The write plane is more than an in-memory demo:

- **durable storage** (`storage`) — the registry writes through a `StorageBackend`.
  `FsStore` persists each cell as an atomically-written file, each site's receipts as
  an append-only JSONL log, and the publish sequence as a crash-safe counter (atomic
  temp-write + rename), so a restart keeps every published site, every receipt, and
  the publish order. `MemoryStore` is the ephemeral test double (and says so via
  `is_durable()`).
- **metered accept path** (`funding`) — a covered publish DEBITS a bounded,
  lease-funded publish allowance (`PUBLISH_TOPUP_UNITS` per publish); when it is spent
  the gate fails closed with a `402` `Exhausted` x402 hint. The lease lapse is driven
  by the handler's publish clock, so a lease behind on rent is lapsed before it is
  trusted — a single lease no longer funds unlimited free publishing.
- **quotas + rate limiting** (`limits`) — body / per-asset / asset-count / total-bytes
  ceilings return `413` (the body check runs BEFORE decode, the OOM guard), and a
  per-owner fixed-window `RateLimiter` returns `429`.
- **serve == commit** (`SiteCell::serve_verified`) — the read path recomputes the
  commitment over the served bytes and refuses (`500`) content that diverges from the
  published root, so a client and the host can re-witness that served bytes match the
  receipt.
- **lifecycle** — `DELETE /v1/sites/<name>/publish` (cap + owner-gated) unpublishes a
  site and leaves a signed delete tombstone in the append-only receipt history;
  receipts are retained for signed AND unsigned registries.
- **two drivers** (`gateway`, `cli`) — an HTTP-request adapter (`GatewayRequest` →
  `respond`) and a CLI adapter (`publish_bundle` / `unpublish_site`) both drive the
  ONE `respond` turn, so "a CLI and a gateway both drive one turn" is a tested fact.

## What is real here vs the named seam

Real + tested: the content model and real Poseidon2 commitment
(`site::content_root`), the cap-gate, the metered lease-funding gate + x402 hint, the
signed receipt, durable storage, quotas + rate limiting, local serve==commit
re-witness, the unpublish lifecycle, and the IPFS-backed launch page. The remaining
seam — an on-chain `Effect::Write` committing the site cell to a node and a light
client witnessing that write in-circuit, binding the host to serve these exact bytes
over the wire — is the circuit epoch, deliberately not done here; the off-chain
commitment + local re-witness are real today.

## Provenance

Pulled forward and improved from a prior gateway's `sitepublish.rs` + `hosting.rs`.
The improvements over the pull: the funding gate is backed by the resident
`hosted-lease` (a real metered, lapsing durable-execution lease) instead of a funding
shim; the 402 carries an x402-style lease-topup hint; the receipt is a self-contained
ed25519 attestation; the serving apex is parameterized; and the launchpad + IPFS
composition is wired in.
