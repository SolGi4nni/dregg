# The receipt contract — one discipline, across dregg and DreggNet

*Status: grounded to code at HEAD. The authoritative kernel receipt lives in
breadstuffs; the product receipts live in `~/dev/DreggNet`. This document is the
shared contract both speak.*

## The through-line

> A turn is the exercise of an attenuable proof-carrying token over owned state,
> **leaving a verifiable receipt**.

The receipt is the offchain-coordination primitive: parties exchange receipts and
reconcile later, settling on a chain only at a real cross-boundary commitment.
For that to work a receipt must be verifiable by **a party who was not there** —
not a private log the producer could rewrite.

The kernel already embodies this. Above the kernel the product surfaces had
drifted into ~10 distinct "receipt" notions, most of them post-hoc log structs
(a `seq`, a `content_root`, an owner — nothing chained, nothing signed, nothing a
non-witness can re-derive). One even declared an authority it never bound. This
contract re-grounds all of them on the kernel discipline.

## The contract (what a receipt IS)

A **receipt** is a record that is:

1. **prev-hash-chained** — it carries the hash of the previous receipt in its
   producer's stream, so the stream is append-only and tamper-evident (you cannot
   rewrite, insert, or drop a record without breaking every link after it);
2. **signed** (ed25519) or **QC-bearing** (a BLS threshold certificate) — bound to
   a named producer, so a non-witness verifies it with only the producer's public
   key; and
3. **re-witnessable** — its canonical hash is recomputed from its typed fields, so
   anyone can check the record says what it claims and the signature covers it.

Everything in the codebase named "Receipt" must either **BE** such a record, or be
a **typed VIEW** of one (carrying the turn-receipt hash it projects). A struct that
is neither is a *log*, and must not be called a receipt.

### The two kernel exemplars (the source of the discipline)

- **`TurnReceipt`** — `breadstuffs/turn/src/turn.rs`. A turn commits to a
  prev-hash-chained, Ed25519-signed receipt: `previous_receipt_hash` makes the
  stream append-only; `executor_signature` lets a non-witness verify the step;
  the canonical `receipt_hash()` (domain-tag `dregg-receipt-v3`) binds every
  disclosed field. The chain's tamper-evidence is proven in Lean —
  `metatheory/Dregg2/Exec/Receipt.lean`, `theorem chain_tamper_evident` (the
  keystone: two well-linked chains agreeing at the head agree everywhere).
- **`BridgeReceipt` / `BridgeReceiptEnvelope`** — `breadstuffs/cell-crypto/src/note_bridge.rs`.
  A 2-/4-phase cross-federation protocol (Locked → Witnessed → Finalized), chained
  by `previous_phase_receipt_hash`, signed by a BLS `ThresholdQC`. Two federations
  mint across a boundary by exchanging signed envelopes — no shared ledger. **This
  is the high-water mark**: it is exactly the offchain-coordination primitive.

Already-coherent read-side receipts: `dregg-query`'s `RangeCertificate` over an MMR
root (a non-omission receipt) and `storage`'s `DequeueProof` (a delivery receipt).

## The shared product vocabulary — `dreggnet-receipt`

`DreggNet/receipt/` (`dreggnet-receipt`) is the ONE contract for the product
surfaces — dependency-light (serde + blake3 + ed25519), portable, so every product
crate adopts the discipline without a heavy dependency. It provides:

- `trait ReceiptBody` — a typed receipt body exposes its canonical `body_hash()`,
  its `seq()`, and (once sealed) its `attestation()`. A default `receipt_hash()`
  computes the chain hash.
- `struct ReceiptAttestation { prev_receipt_hash, turn_receipt_hash, signer,
  signature }` — the chained, signed lift. `turn_receipt_hash` names the **kernel
  turn receipt this record is a view of** (the "a publish/bind IS a turn" link);
  `None` for an owned-state transition that is itself the root authority.
- `struct ReceiptChain` — the producer-side sealer (a registry owns one): each
  emit `seal`s the next body, signing it and advancing the chain head.
- `fn verify_chain` / `fn verify_chain_from` — the **non-witness verifier**: one
  signer over the whole stream, signatures verify, sequences strictly increase,
  each `prev_receipt_hash` links to the prior receipt's hash.
- `struct BodyHasher` — a domain-separated, length-prefixed field hasher, so a
  product crate hashes its typed fields canonically without depending on blake3.

`fn receipt_hash(body_hash, seq, prev, turn)` is the canonical hash (domain
`dreggnet-receipt-v1`) that is signed and chained.

## Each product "receipt" notion, classified

| Notion | Where | Classification |
|---|---|---|
| `PublishReceipt` | `DreggNet/webapp/src/hosting.rs` | **made real** — a publish IS a turn; `SiteRegistry::signed(..)` seals each publish into a prev-hash-chained, signed stream. A client verifies a publish without trusting the host. |
| `BindReceipt` | `DreggNet/dregg-domains/src/lib.rs` | **made real** — a bind IS a turn; a signed `DomainRegistry` seals each *successful* bind (a rejected bind never advances the chain). |
| `BucketReceipt` / `PutReceipt` / `DeleteReceipt` | `DreggNet/storage/src/registry.rs` | **made real** — each bucket op IS a turn; `BucketRegistry::signed(..)` seals all three kinds into ONE shared chain. |
| `DeployReceipt` | `DreggNet/dregg-deploy/src/workflow.rs` | **typed view** — a deploy IS a publish turn; `DeployReceipt.turn_receipt_hash` carries the underlying `PublishReceipt`'s hash, re-witnessable against the publish chain (no parallel "deploy receipt" notion). |

`signed(..)` takes a 32-byte secret seed: a deployed host configures a persistent
secret; the unsigned default (`new()`) leaves a bare projection — a *log*, honest
about being one (`attest == None`), for the free/local path.

## Why this is the re-grounding

Before: a `DeployReceipt` / `PublishReceipt` recorded *that a chain op happened* —
it did not let a non-witness verify the op or let two parties coordinate offchain
and reconcile later. The receipt had degraded from a coordination primitive to an
audit log the moment it crossed out of the kernel, and one carried an unbound
authority.

After: every product receipt either IS a `TurnReceipt`/`BridgeReceipt`-grade record
(prev-hash-chained + signed + re-witnessable) or is an explicit typed view of one,
verified by the same `verify_chain`. The receipt is again the thing that lets us
*avoid* a chain op, not proof that we did one.

## Proven

- `dreggnet-receipt`: the contract verifier — a sealed chain verifies; an unsigned
  body is rejected; tampering a body, removing a record, a foreign signer, and a
  swapped turn-receipt link are each caught.
- `webapp`: signed publishes form a verifiable receipt chain; a tampered
  `content_root` fails the signature; the free default is a bare projection.
- `storage`: create/put/delete seal into one shared chain that verifies; a tampered
  put fails.
- `dregg-domains`: signed binds form a verifiable chain; a rejected bind does not
  advance the chain; a tampered site fails.
- `dregg-deploy`: a signed deploy's `DeployReceipt.turn_receipt_hash` equals the
  reconstructed publish turn-receipt hash (it is a genuine view).
