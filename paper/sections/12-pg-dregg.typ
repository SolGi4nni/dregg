// =============================================================================
// Section 12: pg-dregg
// =============================================================================

#import "../defs.typ": lean
= pg-dregg: verified durable state <sec-pg>

The receipt chain of @sec-proofs is the truth and the database is a cache.
pg-dregg makes that relationship a concrete deployment: dregg as a PostgreSQL
extension in which *reads are ordinary SQL and writes are verified turns*. State
exists in the database only as the post-image of a turn the verified semantics
accepted. An application queries that state freely with `SELECT`; every mutation
passes through the verifier. It is the embeddable realization --- the verified
executor of @sec-realization reachable from inside a database engine --- and it
carries the kernel's guarantees into a place applications already live.

== The spine invariant

The discipline is one sentence: reads are free SQL, and state mutates only
through verified turns. A state row exists solely as the post-image of a
verified turn, never by a bare SQL `INSERT`, `UPDATE`, or `DELETE`. Ordinary
`SELECT` reads the materialized state with no proof obligation, because reading
cannot violate a guarantee. Writes are the only thing the verifier need gate,
and they are gated at the one door the schema exposes: the commit-log table,
whose `BEFORE INSERT` trigger refuses a batch the chain discipline rejects. The
same capability token of @sec-authority authorizes both sides. A row-security
policy that admits a read and the credential a write must carry evaluate the
same admission decision, so the database's access control and the kernel's
authority are not two systems kept in sync but one decision evaluated in two
places.

== The tiers

pg-dregg realizes the spine invariant in layers, each usable on its own and each
adding one capability of the verified substrate to the database.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*tier*], [*what it adds*]),
    [authorization], [dregg capabilities as row-security policies: a policy
      admits a row only when a configured-issuer credential authorizes the
      action, verified offline against the issuer public key --- the
      @sec-authority admission decision, with no circuit and no network. The
      credential core is the same authorization library the node runs, anchored
      by a Lean--Rust differential],
    [mirror], [the node ships each verified turn's rows into read-only tables
      (turns, cells, capabilities, memory); applications query verified state as
      plain SQL joins, and the sole writer is the verified commit path, so the
      spine invariant holds],
    [verified store], [the commit-log table is the only door to state, and its
      before-insert trigger re-runs the chain check --- turn $N$'s post-root is
      turn $N{+}1$'s pre-root, ordinals dense --- so a reordered, gapped, or
      substituted batch is refused by the database engine itself; a proof gate
      over the same store marks whole windows of turns proof-attested],
    [embeddable executor], [a database function runs a turn in-backend through
      the verified entry, writing the receipt and the post-state in one
      transaction --- the database *is* the kernel, with turn and application
      data sharing one atomic commit],
  ),
  caption: [The pg-dregg tiers. Each is a point at which the verified substrate
    enters the database; the lower tiers are circuit-free and offline.],
)

The lower tiers need no prover: the authorization tier is a credential check
compiled to a row-security predicate, and the mirror tier turns the database
into a query surface over verified state with the node as sole writer.

== The write path

The write spine has two halves. A database user calls a submit function whose
insert is itself row-security-gated; the call records a pending intent in a
queue, and postgres never executes anything at that point. A drainer then
processes each intent through four gates in order. It re-checks the acting
agent's capability, consulting revocation, so a token revoked after enqueue is
refused. It produces the post-image through the executor seam. It admits the
produced batch onto the durable head by the chain check, and a batch that does
not chain never moves the head. It materializes the post-image rows and resolves
the queue row --- executed with the receipt hash, or refused with the reason ---
in one logical commit, so the submitter learns the outcome by reading its own
row.

== The proof gate

The verified store's per-row chain check is structural: it proves the stored
sequence is consistent, not that each turn executed correctly. The proof gate
adds the second half. A recursive whole-chain proof (@sec-proofs) over a span of
finalized turns is presented as serialized bytes, and a set-returning function
verifies it and emits one row per covered ordinal, each tagged proof-attested. A
consumer joins those rows against the turns table to distinguish the
proof-attested prefix from the merely chain-consistent one.

The serialized transport carries the verify-sufficient subset of the fold: the
root proof, the chain-binding proof, and the public scalars. Prover-only
chaining data never crosses the SQL boundary. In the proof-linked build the gate
runs three checks: the verification-key pin against a caller-held anchor, the
carried publics against the binding proof, and the root batch verification. The
verifier it links is the recursion verifier of the descriptor stack --- the same
check the light client makes --- built without the executor or the Lean runtime.
Both the admit and the refuse directions are exercised by a test that folds a
real turn chain, verifies it through the SQL-side transport, and then confirms a
relabeled public and a foreign verification key are refused. The default,
circuit-free build decodes the transport and attests nothing: a proof gate that
cannot verify reports a window as unattested, never as attested.

The producer that folds newly finalized turns into attestation rows is in place
as machinery around a seam: window discipline, watermark resumption, and a check
that binds the fold's claimed coverage to the exact window it was handed are
tested against a deterministic stand-in, and the real circuit fold plugs in
where the circuit is linked. Two edges remain named. The live node-side wiring
of that real fold is one. The transport's state anchors are the other: it
carries the single-element head root rather than the full eight-element anchor,
and a genuine wide anchor is refused rather than mis-attested until the
transport is widened.

== The embeddable executor

The deepest tier embeds the verified executor itself. A database function takes
a turn, runs it in-backend through the compiled Lean entry of @sec-realization,
and writes the receipt and the post-state in the same database transaction as
the application's own writes. The runtime it embeds is the single-threaded,
fork-safe configuration of the Lean runtime: a private allocator that never
overrides the backend's own, lazy task management that runs spawned tasks
inline, and an initialization that omits the event-loop thread. Initialization
happens lazily on the first produced turn, in the worker the engine forked,
never in the postmaster; a failed initialization refuses the turn rather than
committing unverified state. The executor tier is linked only when enabled, so
the default build never sees it.

This tier runs, and the extension's own test suite exercises it inside a live
backend. One test drives the producer directly: the runtime initializes
in-backend, #lean("execFullForestG") executes, and a conserving transfer commits
with post-balances read back from the executor's decoded state. A second test
drives the full SQL path: a submitted turn is drained through the four gates,
executed by the embedded verified executor, and lands as a committed turn row,
with the test first asserting the runtime is live so that a drained turn is one
the executor decided rather than a stand-in fold. When the Lean executor is
linked it wins producer selection; a pure-Rust executor kept at documented
parity with the Lean specification is available as a lighter producer, and the
default build retains a deterministic stand-in so the gate plumbing is testable
with no executor in the build.

This is where the kernel's theorems land directly in the data path.
Conservation, non-amplification of delegated capabilities
(#lean("Spec.gen_conferral_is_attenuation")), nullifier uniqueness, and
authenticated state-root evolution hold of the rows because the function that
wrote them is the verified executor; the post-state is verified by construction
rather than re-checked. One seam remains and is named: the extension does not
link the turn and cell marshalling crates, so the in-backend producer cannot
decode the submitter's signed envelope into the executor's wire turn. It
synthesizes a conserving transfer instead and takes the executor's verdict and
post-state as authoritative. Full in-backend decoding of an arbitrary submitted
turn is the open edge (@sec-limitations).

The runtime boundary this tier crosses is the one the seL4 port also crossed
(@sec-sel4). A postgres backend is a forked, single-threaded process under the
engine's error handling; a protection domain offers no threads and no ambient
services at all. Both hosts require the Lean runtime to run with no worker
thread and no event loop, and the same excision --- omit the event-loop
initialization, keep the allocator private --- serves both. One executor, two
hosts, one boundary.

== Scope

pg-dregg is a mirror, a verified-write gate, and an embedded light-client
backend for the database, not a full node. The authorization and mirror tiers
are circuit-free and live. The verified-store chain check is live, and the proof
gate verifies real recursive folds in the proof-linked build. The embeddable
executor runs the verified step in-backend under the extension's tests. The
named edges are full in-backend decoding of an arbitrary submitted turn, the
live wiring of the node-side proof producer, and the wide-anchor transport.
Federation across databases is structural: replication is single-writer
fan-out, and a subscriber re-runs the chain check on the replicated rows,
refusing a tampered or reordered stream and confirming it holds the whole
published prefix rather than a truncation. @sec-limitations states the
in-progress edges as checkable facts.
