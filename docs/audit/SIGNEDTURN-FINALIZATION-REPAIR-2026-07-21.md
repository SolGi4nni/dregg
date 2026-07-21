# SignedTurn finalization repair record — 2026-07-21

This is the engineering record for the repair prompted by *Security report:
block finalization does not fully revalidate SignedTurn*. It is deliberately not
a vulnerability-program response, a severity negotiation, a migration plan, or
a pull-request description. Dragon's Egg is a zero-deployment greenfield
system. A security bug is a correctness bug: state must move only under the one
intended authority predicate, every path must implement that predicate, and the
tests must exercise the hostile cases that distinguish it from nearby weaker
predicates.

The source report audited revision
`314455f18943db8cc9534af7556266c79cc8d885`. This record describes the repaired
tree on 2026-07-21. The named functions and tests are the durable anchors; old
line numbers are not.

## Result in one paragraph

The application-payload boundary now has one shared `SignedTurn` validator for
HTTP ingress, consensus finalization, and the PostgreSQL drainer. Before ledger
mutation it verifies the outer Ed25519 half, derives and compares the signer
cell, requires the complete outer ML-DSA half under native node policy, and
checks that the carried ML-DSA key equals an independently enrolled
`(CellId, Ed25519 key, delegation epoch, ML-DSA key)` identity. The inner action
verifier uses the same enrolled-identity rule. Receipt handling is split into an
immutable node-wide log and independent per-agent causal chains; signed receipt
bytes are never relinked. Finalized receipt bytes share the redb transaction
with the finalized state transition and note leaves. Boot recovery rejects a
corrupt, gapped, or causally invalid log as a whole rather than accepting a
shorter prefix. Invalid consensus-finalized application payloads produce a
deterministic rejection record instead of disappearing behind an optimistic
ingress acknowledgement.

That closes the reported authority-substitution and receipt-relinking bugs for
the native enrolled paths. It does **not** invent trust-on-first-use enrollment
for an external user. Durable external-user identity creation/rotation remains
the central architectural residual and is stated plainly below.

## The invariant, stated once

For a native node to accept an outer `SignedTurn`, all of the following must be
true before any fee, nonce, cell, note, or receipt mutation:

1. The Ed25519 signature verifies over the exact canonical `Turn::hash()`.
2. `turn.agent` equals the default cell derived from the outer Ed25519 signer.
3. The outer ML-DSA signature and key are both present.
4. The node independently knows the agent's hybrid identity.
5. The enrolled Ed25519 key equals the outer signer and the live cell owner.
6. The enrolled delegation epoch equals the live cell epoch.
7. The carried ML-DSA key equals the enrolled ML-DSA key.
8. ML-DSA verifies over the same exact turn hash under the enrolled key.
9. The turn's optional predecessor exactly equals that agent's durable receipt
   head; `None` is valid only for that agent's genesis receipt.
10. Decoding consumes the complete payload; trailing bytes are not another
    spelling of the same signed envelope.

Inner hybrid action authorization separately requires both signature halves
over the canonical federation- and nonce-bound action message. Its ML-DSA key is
also checked against the independently enrolled target-cell identity and live
epoch. A valid attacker-owned ML-DSA signature paired with a forged victim
Ed25519 half therefore fails even though each signature is individually valid.

The shared outer predicate lives in
`node/src/signed_turn_validation.rs::validate_signed_turn`. Node executor setup
populates its identity registry from state the node already trusts; it never
learns a key from the envelope currently being checked.

## Disposition of the original findings

| Original finding | Current disposition | Authority |
|---|---|---|
| Finalization omitted signer → agent binding | Repaired in the shared pre-mutation validator | `validate_signed_turn`; hostile victim-agent substitution tests |
| Finalization omitted outer ML-DSA | Repaired; native node admission requires and verifies both outer halves | shared validator; stripped/invalid PQ tests |
| PostgreSQL drainer used a weaker predicate | Repaired at admission by calling the same validator; its durability transaction boundary is discussed under residuals | `node/src/submit_queue_drainer.rs` |
| Outer and inner PQ keys were self-carried authority | Repaired for independently enrolled identities; unknown external users fail closed | `TurnExecutor::enroll_pq_identity`, `verify_hybrid_signature`, shared outer validator |
| HTTP and finalization seeded different receipt heads | Repaired around one durable per-agent head lookup | `AgentCipherclerk::agent_receipt_head_hash` and node call sites |
| Missing predecessor could reset a non-genesis foreign chain | Repaired by exact `Option<[u8;32]>` equality | `validate_receipt_append`; missing-predecessor hostile test |
| Finalized receipts were relinked into one operator chain | Repaired: immutable total log plus per-agent indices; append never edits signed fields | `sdk/src/cipherclerk.rs`; interleaved-agent tests |
| Persistence failure could leave a served but non-durable head | Repaired for node-backed append: persistence is fallible and happens before in-memory mutation | fallible receipt sink; durability hostile tests |
| Corrupt durable tail silently truncated history | Repaired: restore is all-or-error and leaves the existing projection unchanged | `restore_receipt_chain`; corrupt/gap restart tests |
| Invalid finalized payload had no durable application outcome | Repaired by a versioned deterministic rejection record keyed by block id | `FinalizedPayloadRejectionRecord` and finalization integration |
| Consensus block/vote signatures were missing PQ | Original report correctly called this a false positive | existing pinned committee hybrid validation remains unchanged |

## One validator, not three approximations

The source report's most important structural observation was that consensus
authentication and application authorization are different predicates. A
validator's hybrid block signature identifies the proposer. It does not make an
arbitrary opaque turn payload authorized for its claimed agent.

The repair therefore does not add an isolated check to finalization. It moves
the complete outer predicate into one module and calls it from every application
entry:

- direct signed-turn HTTP admission;
- finalized block application; and
- the optional PostgreSQL submission drainer.

The validator returns the already computed turn hash so callers do not
reconstruct a subtly different message. Rejection reasons have stable machine
codes. A finalized invalid payload records only deterministic inputs—block id,
payload hash, optional turn hash, version, and reason code—rather than local
wall-clock or formatting data.

Canonical decoding is part of the predicate. The TypeScript/Rust hostile wire
suite found that `postcard::from_bytes` accepts a valid value followed by
trailing data. Node ingress therefore must use `take_from_bytes` (or an
equivalent exact decoder) and reject a non-empty remainder. Signature validity
does not make two different transport byte strings one canonical artifact.

## Hybrid identity: what changed and what did not

`Authorization::HybridSignature.ml_dsa_pk` and
`SignedTurn.pq_signer` remain in the wire form. They are useful anti-strip data,
but they are no longer identity roots. Required/native verification looks up an
`EnrolledPqIdentity` by target cell and checks:

- target Ed25519 identity;
- delegation epoch; and
- the exact ML-DSA public key.

Enrollment updates are monotone. Repeating an identical enrollment is
idempotent; an epoch rollback or a different key at the same epoch refuses.
Node setup currently enrolls node-held identities and configured federation
member identities from independently trusted material.

Unknown external identities are intentionally not enrolled from a submitted
signature. That would recreate the original key-substitution bug under a new
name. The greenfield completion is to commit the hybrid identity when a cell is
created and require an authenticated, epoch-advancing rotation operation. Until
that exists, a freshly funded remote user correctly fails native admission even
though the SDK can construct a cryptographically valid hybrid envelope.

There is no production migration profile. Native node admission remains on.
Turning it off requires both `DREGG_REQUIRE_PQ=0` (or `false`) and
`DREGG_ALLOW_UNAUDITED_PQ=1`; that double opt-in exists for explicit
unaudited test/library runs and is not deployment evidence.

## Receipt semantics and atomic durability

The old `receipt_chain: Vec<TurnReceipt>` was asked to be two incompatible
things: one agent's predecessor chain and a node-wide observation log. The
repair represents both objects separately:

- an immutable total append log; and
- per-agent index vectors and heads into that log.

An append validates the receipt's claimed predecessor against that receipt's
agent. An unrelated agent's receipt can interleave in the total log without
becoming anyone else's predecessor. `None` is accepted only when that agent has
no head. The receipt object is appended byte-for-byte; the cipherclerk never
fills or rewrites `previous_receipt_hash` after the executor signs it.

Finalized state and receipt durability are welded in
`PersistentStore::commit_finalized_turn_with_notes_and_receipt`. The transaction
checks the dense next receipt index, rejects conflicting bytes, writes the
finalized commit record, note commitments, and exact encoded receipt, and only
then allows the in-memory receipt projection to advance through
`append_receipt_already_durable`. A persistence error leaves the in-memory head
unchanged.

Boot loading requires dense indices, valid decoding, and every agent-scoped
causal link. Any gap, undecodable record, or broken predecessor fails the load;
it is not reinterpreted as permission to roll back to an earlier valid prefix.

## Client surfaces repaired with the boundary

The Rust remote runtime now:

- hybrid-signs the inner action and outer envelope;
- installs the verified ML-DSA producer/verifier hooks or fails closed;
- reads `/api/cell/{agent}.last_receipt_hash`, not the node-wide receipt tip;
  and
- documents that faucet funding does not itself enroll a PQ identity.

The TypeScript SDK now emits the canonical five-field hybrid `SignedTurn` and
requires exact ML-DSA key/signature lengths. Its Rust interoperability harness
checks signer → agent derivation, independently enrolled Ed/PQ identity, both
outer signatures, exact postcard round-trip, and real executor acceptance. It
also rejects absent PQ, valid attacker-key substitution, wrong nonce, and
trailing bytes.

## Captured focused gates

These are narrow current results, not claims that the entire dirty multi-swarm
tree is green:

| Gate | Result | Qualification |
|---|---:|---|
| Turn hybrid identity hostile suite | 9/9 | protocol/wiring run with explicit unaudited PQ test backend |
| Node PQ identity integration | 2/2 | includes victim-Ed + attacker-valid-ML substitution refusal |
| Native no-downgrade policy | 1/1 | one flag alone cannot turn native admission off |
| SDK per-agent receipt/durability suite | 6/6 | interleaving, missing links, immutable bytes, sink failure |
| Persist finalized receipt atomicity/density | 4/4 | dense indices, conflict/replay, atomic transaction |
| Node corrupt-log/restart suite | 3/3 | receipt and MMR head survive; corruption fails closed |
| RemoteRuntime focused tests | 12/12, plus 1/1 envelope | explicit unaudited PQ test backend; no external enrollment claim |
| TypeScript/Rust hybrid wire suite | 6/6 | explicit Rust FIPS-204 backend only in the tiny test harness |
| TypeScript turn/service surfaces | 3/3 and 8/8 | current canonical outer wire |
| Shared outer validator | 4/4 | honest enrolled identity plus stripped, invalid, substituted, and trailing-byte cases |
| Finalized hostile envelope matrix | 1/1 | victim-agent, outer-PQ, trailing-byte, and per-agent-chain refusals before mutation |
| PostgreSQL hostile envelope matrix | 1/1 | exact decode and shared admission predicate; not a live-database durability gate |
| Node library with `pg-mirror-live` | green | persvati compile gate, 21.00s |
| SDK-network strict test server | green | exact postcard consumption at the simulated HTTP boundary |

The focused PQ-exercising node gates explicitly set
`DREGG_ALLOW_UNAUDITED_PQ=1`. They establish transcript, identity, routing, and
refusal behavior; they do not establish verified-core assurance. Production
continues to abort rather than silently substitute the crate primitive when its
verified core is required. The finalization lane did not run its hostile matrix
against the strict verified-core archive, a live PostgreSQL database, or a
Helm-through-multiparty deployment.

## Remaining work, without euphemism

1. **Durable external-user hybrid identity.** Cell/genesis creation must commit
   `(CellId, Ed25519, epoch, ML-DSA)` and authenticated rotation must advance it.
   The current O(number of cells) executor-setup scan is devnet-correct but
   should become a shared/indexed lookup.
2. **Direct-path transaction unification.** Consensus finalization has the
   welded receipt/state transaction. Any solo or PostgreSQL direct mutation path
   that persists receipt and ledger state in separate transactions still has a
   crash window and must be moved onto the same atomic primitive. It is not
   disguised as a migration problem.
3. **Verified-core build closure on the fast nodes.** The behavioral gates above
   need a strict rerun with the verified ML-DSA/ML-KEM Lean archive installed and
   no unaudited test flag.
4. **Cross-language exactness beyond the focused harness.** The full WASM wire
   differential currently aborts because that WASM host cannot install a
   verified PQ core. The focused TypeScript/Rust harness is green; the complete
   WASM production host boundary is not.
5. **Finality-facing rejection observability.** Deterministic rejection records
   exist; operator, client, and game surfaces should expose them so an HTTP
   acknowledgement cannot be mistaken for a committed game turn.
6. **Rejection/cursor atomicity.** A finalized-payload rejection is stored
   deterministically, but its persistence is not welded to the in-memory served
   cursor. A rejection-store failure is logged rather than preventing that
   payload from being considered served.

## Commit ledger for this repair wave

- `06ed2a9a7` — independently enrolled inner PQ identity and fail-closed node
  policy.
- `45a57e19a` — immutable node-wide receipt log plus per-agent causal chains.
- `7d64c71bb` — durable-first append, all-or-error restore, and atomic finalized
  receipt persistence.
- `9cda4f50d` — RemoteRuntime hybrid signing and per-agent head lookup.
- `895c7d098` — canonical TypeScript hybrid envelope and hostile Rust wire
  harness.
- `37a190357` — fixed-width `u64` `SetField` wire key and fail-closed narrow AIR
  projection.
- `4ad5e1be0`, `b9dfba586`, `11246a981` — fixed-width `SetField` consumer
  completion, including game and council boundaries.
- `0e6e419ee` — exact shared `SignedTurn` admission, independently enrolled
  outer PQ identity, per-agent finalized receipts, deterministic rejection
  records, and finalized receipt/state durability weld.
