# The receipt contract — the kernel discipline

*Status: grounded to code at HEAD. This document defines the substrate's receipt
discipline — the contract every receipt in the verified kernel speaks.*

## The through-line

> A turn is the exercise of an attenuable proof-carrying token over owned state,
> **leaving a verifiable receipt**.

The receipt is the offchain-coordination primitive: parties exchange receipts and
reconcile later, settling on a chain only at a real cross-boundary commitment.
For that to work a receipt must be verifiable by **a party who was not there** —
not a private log the producer could rewrite.

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

Everything named "Receipt" must either **BE** such a record, or be a **typed VIEW**
of one (carrying the turn-receipt hash it projects). A struct that is neither is a
*log*, and must not be called a receipt.

## The two kernel exemplars (the source of the discipline)

- **`TurnReceipt`** — `turn/src/turn.rs`. A turn commits to a
  prev-hash-chained, Ed25519-signed receipt: `previous_receipt_hash` makes the
  stream append-only; `executor_signature` lets a non-witness verify the step;
  the canonical `receipt_hash()` (domain-tag `dregg-receipt-v3`) binds every
  disclosed field. The executor holds an `executor_signing_key`
  (`TurnExecutor::with_executor_signing_key`) and signs
  `canonical_executor_signed_message()` — domain-tag `executor-receipt-sig-v3:`
  over the *full* `receipt_hash` — so a downstream verifier checks the signature
  alone and it attests every field bound into the receipt hash (the legacy `v2`
  narrow prefix message is preserved only for fixtures). The chain's
  tamper-evidence is proven in Lean —
  `metatheory/Dregg2/Exec/Receipt.lean`, `theorem chain_tamper_evident` (the
  keystone: two well-linked chains agreeing at the head agree everywhere).
- **`BridgeReceipt` / `BridgeReceiptEnvelope`** — `cell-crypto/src/note_bridge.rs`.
  A 2-/4-phase cross-federation protocol (Locked → Witnessed → Finalized), chained
  by `previous_phase_receipt_hash`, signed by a BLS `ThresholdQC`. Two federations
  mint across a boundary by exchanging signed envelopes — no shared ledger. **This
  is the high-water mark**: it is exactly the offchain-coordination primitive.

Already-coherent read-side receipts: `dregg-query`'s `RangeCertificate` over an MMR
root (a non-omission receipt) and `storage`'s `DequeueProof` (a delivery receipt).

## The discipline carried upward

Any surface that produces a "receipt" must either BE a `TurnReceipt`/`BridgeReceipt`-grade
record (prev-hash-chained + signed + re-witnessable) or be an explicit typed view
of one, verified the same way. The receipt is the thing that lets parties *avoid*
a chain op, not proof that one happened. A producer-side sealer signs each emitted
body and advances the chain head; a non-witness verifier checks one signer over
the whole stream, that signatures verify, that sequences strictly increase, and
that each `prev_receipt_hash` links to the prior receipt's hash.

## Proven

- `TurnReceipt`: the chain is tamper-evident in Lean
  (`metatheory/Dregg2/Exec/Receipt.lean`, `chain_tamper_evident`); tampering a
  field the effect did not legitimately write makes the turn unprovable (the
  anti-ghost property).
- `BridgeReceipt`: the phase chain is linked by `previous_phase_receipt_hash` and
  carried by a BLS `ThresholdQC`; a non-witness verifies the boundary mint from the
  committee's public keys alone.
</content>
</invoke>
