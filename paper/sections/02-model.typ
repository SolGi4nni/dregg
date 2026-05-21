// =============================================================================
// Section 2: System Model
// =============================================================================

= System Model

== Cells

A _cell_ is the fundamental unit of isolated state, analogous to a Mina zkApp account or an E object. Each cell holds:

- A content-addressed identity $"CellId" in {0,1}^(256)$.
- Mutable state: 8 generic field slots $s_0, ..., s_7 in FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear prime).
- A _capability list_ (c-list): the set of capabilities the cell may exercise.
- Permission requirements specifying what authorization kind is needed for each action type.
- An optional verification key for ZK proof validation.

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

== Turns

A _turn_ is an atomic transaction over one or more cells, analogous to a Mina ZkappCommand or an E turn. A turn contains:

- A _call forest_: a tree of actions, executed depth-first.
- A fee (in computrons) covering execution cost.
- A nonce (monotonically increasing per cell) for replay protection.
- Authorization: Ed25519 signature, ZK proof, or both.

If any action in the call forest fails, all effects are rolled back via journal replay. This provides atomicity.

== Silos and Federations

A _silo_ is a node that holds cells, executes turns, and participates in federation consensus. A _federation_ is a committee of 3--64 silos sharing a trust root. Federation members run Morpheus @morpheus adaptive BFT consensus to agree on attested Merkle roots, revocation tree updates, and budget rebalancing epochs. The honest-majority assumption is standard: tolerate $< n\/3$ Byzantine members.

== Trust Assumptions

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, center),
    table.header([*Layer*], [*Assumption*], [*PQ?*]),
    [External proofs (STARKs)], [Collision-resistant hash], [Yes],
    [Merkle commitments], [Collision-resistant hash], [Yes],
    [Macaroon HMAC chain], [PRF security of HMAC-SHA256], [Yes],
    [Federation QCs (BLS12-381)], [Bilinear DH in $GG_1 times GG_2$], [No],
    [Node identity (Ed25519)], [DLP in twisted Edwards], [No],
    [Sealed secrets (X25519)], [CDH in Curve25519], [No],
  ),
  caption: [Trust assumptions by layer. Items marked "No" are confined within federation trust boundaries.],
)

The critical invariant: *everything that crosses a trust boundary is post-quantum secure*. Classical cryptography exists only between parties that already trust each other.

== Execution Model

=== Pipeline Execution with Topological Ordering

The executor processes turns not only individually but in _pipelines_: batches of turns with declared dependency edges. A pipeline $P = (T, E)$ where $T = {t_0, ..., t_n}$ and $E subset.eq T times T$ is a DAG of dependency edges. The executor computes a topological ordering and processes turns in causal order. If turn $t_i$ fails and $t_j$ depends on $t_i$, then $t_j$ receives a `DependencyFailed` error without executing.

=== BudgetGate Integration

Every turn pays a fee in _computrons_. The executor integrates Stingray @stingray bounded counters directly: each silo holds a local budget slice $"slice"(i) = "balance" dot (f+1)/(2f+1)$ and debits locally without coordination until exhaustion. The executor checks $"fee" <= "remaining"$ before execution (fail-fast) and debits atomically upon commit. Budget accounting uses checked arithmetic throughout---overflow produces an executor error, never wraps.

=== Conservation Invariant

For any turn $t$ with actions $a_1, ..., a_k$, the executor enforces:

$ sum_i "balance_change"(a_i) + "fee"(t) = 0 $

Value cannot be created or destroyed within a turn. The fee is debited from the agent cell and does not reappear---it is the cost of execution.

== E-Style Distributed Object Semantics

=== EventualRef and Promise Pipelining

In E @elang, a message send returns a _promise_ that resolves when the target processes the message. Multiple messages can be sent to the resolution of a pending promise without waiting for it to resolve---_promise pipelining_ eliminates round-trip latency in distributed object protocols.

Pyana implements this via `EventualRef`: a reference to the output of a pending turn, identified by the turn's hash and an output slot index. A turn may target an `EventualRef` rather than a concrete `CellId`, declaring a dependency that the executor resolves during pipeline execution. The `Target` type is a sum:

$ "Target" = "Concrete"("CellId") | "Eventual"("source_turn": ["u8"; 32], "slot": "u32") $

When the source turn commits, its outputs (granted capabilities, created cells, state updates) populate a resolution table. Dependent turns rewrite their `EventualRef` targets to concrete `CellId` values before execution.

=== Three-Party Introduction

Object-capability systems form new communication paths through _introductions_: Alice, holding capabilities to both Bob and Carol, introduces Bob to Carol by granting Bob a (possibly attenuated) capability to Carol. In Pyana, an `Effect::Introduce` during a turn emits a `RoutingDirective`:

$ "RoutingDirective" = ("sender": "CellId", "target": "CellId", "authorizing_turn": ["u8"; 32], "expires": "Option"("u64")) $

The node's routing table is populated from these directives. No global directory exists---all communication paths are introduced, not discovered.

=== Comparison with E and Cap'n Proto

E's promise pipelining requires a live vat (process) hosting the target object. Cap'n Proto @capnproto extends this to RPC with three-party handoff across address spaces, but within a single trust domain. Pyana differs in three respects:

+ *Proof-carrying*: A pipelined message carries (or can generate) a STARK proof that the sender is authorized to invoke the target. No live vat is needed to check authorization---verification is offline.
+ *Asynchronous, no blocking IPC*: Pipelines are submitted as batches with explicit dependency DAGs. There is no synchronous call semantics.
+ *Privacy*: The introduction graph is private to the parties involved. A routing directive is visible only to the node executing the turn and the introduced parties.
