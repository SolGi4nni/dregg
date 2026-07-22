# Exact frame consensus identity

**Status:** corrective protocol design; the deployed FNSP-v3 frame format does not yet satisfy
this law.  Until the v4 cutover below, the live v3 route is a solo-devnet/local-recovery feature
and MUST refuse committee mode.

## The law

For a finalized turn, every honest committee member given the same finalized block and the same
pre-state MUST derive the same exact activation identifier, exact frame identifier, and exact
successor state.

Equivalently, consensus identity is independent of which validator executed the turn:

```text
consensus_frame_id(core, local_signer_A) = consensus_frame_id(core, local_signer_B)
                                        = H("exact-frame-core-v4", core)
```

A validator signature authenticates an observation of that identifier.  It is not an input to the
identifier.

This is stronger than “the signature is outside the hash”.  A local public key, signature scheme,
signature bytes, wall-clock field, or locally encoded receipt MUST NOT occur anywhere in the
transitive preimage of the consensus activation or frame identifier.

## Why v3 is local, not federation-global

The v3 activation hash commits `executor_public_key`.  Its frame carries that key, verifies the
frame signature against it, and inherits the signer-dependent activation hash.  The node constructs
the key from its local `AgentCipherclerk`.  Two honest validators with distinct local keys therefore
derive distinct activation hashes and frame chains, even when their exact accumulator transitions
are identical.

The current receipt hash is **not yet** a safe consensus coordinate.  Executor signature bytes are
correctly absent from `TurnReceipt::receipt_hash`, but the hash includes `TurnReceipt::timestamp`,
and the finalized executor currently obtains that value from each validator's local wall clock.
The same finalized block can therefore produce different receipt hashes on two honest validators.
Worse, the same local clock also decides expiry, capability, and rate-limit branches, so removing
the timestamp from the hash alone would hide a possible state-transition disagreement rather than
repair it.

V4 must use the finalized receipt identity defined by
[`CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md`](CONSENSUS-TIME-AND-RECEIPT-IDENTITY.md), or remain gated
until `TurnReceipt::receipt_hash` has been version-bumped onto that deterministic finalized core.
Persisting the full locally signed receipt remains useful, but its byte encoding is node-local
evidence and cannot be the identity of a federation-global frame.

## V4 split: common core and local envelope

V4 is a new domain and wire version.  It does not reinterpret a stored v3 row.

`ExactActivationCoreV4` contains only deterministic consensus coordinates:

- protocol/federation and committee epoch identifiers;
- dense receipt cutover index and the deterministic finalized-receipt id at the cutover;
- exact accumulator initial root, count, and domain-separated state commitment; and
- the pinned verifier/program identities governing the exact transition.

`ExactFrameCoreV4` contains only deterministic consensus coordinates:

- activation id, sequence, and prior consensus frame id;
- receipt index, deterministic finalized-receipt id, and the actor's receipt predecessor
  index/hash;
- block id, turn hash, forest hash, actor, and federation id;
- complete deterministic pre/post state commitments;
- exact accumulator before/after points; and
- the accepted statement, proof, consequence, and output-note commitments required by the exact
  relation.

The activation id is `H("exact-activation-core-v4", canonical_activation_core)`.  The frame id is
`H("exact-frame-core-v4", canonical_frame_core)`.  Both encodings are strict, fixed-width, and
canonical.

`LocalExactFrameEnvelopeV4` is stored separately and contains:

- the consensus frame id and finalized block/commit ordinal;
- the local validator identity;
- the local executor receipt bytes;
- a classical signature and the deployed post-quantum signature over the frame id and ordinal;
  and, when assembled, an optional committee finalization certificate over the same message.

The local envelope may differ across honest validators.  Its verifier MUST first recompute the
consensus frame id from the core, then verify all envelope signatures over that exact id.  It cannot
replace, select, or mutate the core.

## Authority and restart

The signer-independent core is written in the same redb transaction as the finalized commit,
receipt identity, exact accumulator CAS, faithful root transition, output notes, and executor
consensus state.  The finalized block order is the primary authority for that core.

The local envelope gives crash/restart evidence that this node actually observed and executed the
core.  Committee mode additionally requires either:

1. an already authenticated finalized-block/attested-root chain which transitively commits the
   exact frame id; or
2. a threshold certificate over `(federation, committee_epoch, block_id, ordinal, frame_id)`.

An envelope quorum is evidence for one pre-existing frame id.  It never resolves two competing
cores by counting signatures after the fact.

Open/recovery performs a full replay of deterministic cores and verifies their local envelopes and
available finality anchors.  Online append uses a derived boundary index only after that replay.

## Cutover and current gate

- V3 tables remain readable as node-local audit/recovery history.
- V3 activation and frame ids MUST NOT be advertised as federation-global.
- The live v3 route MUST require explicit solo consensus, not infer solo operation from a committee
  vector of length zero or one.
- The first committee-capable exact epoch is v4.  Its activation is an explicit flag day from the
  terminal v3/local frame and exact accumulator state.
- A committee deployment MUST fail closed if only the local-envelope signer is configured.

## Mechanical acceptance gates

The v4 implementation is not complete until hostile tests establish all of the following:

1. Two different local signing keys produce byte-identical activation and frame core ids.
2. Their local envelopes differ and both verify against that one frame id.
3. Mutating any consensus field changes the frame id and invalidates every old envelope.
4. Mutating only signature/envelope bytes cannot change the frame id.
5. A local receipt whose signature is valid but whose deterministic finalized-receipt id differs is
   rejected.  Two validators executing the same finalized core at different wall-clock instants
   derive the same id and successor state.
6. A frame/core from a different federation or committee epoch is rejected.
7. Restart replay reconstructs the same head and rejects gaps, forks, signer substitution, and
   partial core/envelope transactions.
8. Multi-node v3 activation is refused; no local-key-dependent frame is silently promoted to
   consensus authority.

## Code cut map

- `turn/src/faithful_note_spend_exact_v3_receipt_epoch.rs`: introduce the v4 core types and hashes;
  keep signer material out of their constructors and encodings.
- `persist/src/exact_fnsp_v3_frame_head.rs`: add versioned core and local-envelope tables, atomic
  write/replay, and derived online heads.  Do not weaken the v3 reader during migration.
- `node/src/exact_fnsp_v3_activation.rs`: replace local-key activation identity with core
  authorization; mint the local envelope separately.
- `node/src/exact_fnsp_v3_execution_authority.rs`: bind executor-produced receipts to the common
  receipt hash and frame core, while retaining the local receipt signature in the envelope.
- `node/src/exact_fnsp_v3_finalization.rs`: atomically commit the core and envelope with the exact
  CAS and full executor consequence, including output notes.
- `node/src/blocklace_sync.rs`: keep v3 explicitly solo and route committee deployments only after
  v4 core/envelope authority and deterministic finalized execution time are installed.
- `metatheory/Dregg2/`: state and prove signer erasure/noninterference for the v4 core hash, plus
  envelope soundness as a statement about a fixed core id.
