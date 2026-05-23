// =============================================================================
// Section 3: Authorization Semantics
// =============================================================================

= Authorization Semantics

== Multi-Modal Authorization

Pyana supports five authorization modes, each suited to different trust contexts:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Mode*], [*Mechanism*], [*Use Case*]),
    [Signature], [Ed25519 over turn hash], [Standard agent-initiated turns],
    [Proof], [STARK proof of authorization (Datalog evaluation)], [Cross-boundary, privacy-preserving],
    [Breadstuff], [Macaroon HMAC chain with caveats], [Attenuated delegation within a trust domain],
    [Bearer], [BearerCapProof (signed or STARK delegation chain)], [One-shot tokens, tickets, ephemeral access],
    [Unchecked], [No verification (genesis only)], [System bootstrap],
  ),
  caption: [Authorization modes. A turn declares which mode it uses; the executor validates accordingly.],
)

The Bearer mode carries a `BearerCapProof`: either a signed Ed25519 delegation chain (fast, non-private) or a STARK proof that a valid delegation chain exists (private, post-quantum). The choice is made at delegation time based on the desired privacy/performance tradeoff.

== Capabilities as Datalog Facts

Authorization state is encoded as a set of Datalog facts. A fact is a ground atom $"fact" := "predicate"("term"_1, ..., "term"_k)$. Attenuation transforms a fact set $F$ into $F' subset.eq F$ by removing facts. The HMAC chain in a macaroon token makes removal of caveats cryptographically impossible---attenuation is irreversible.

== Dual-Mode Evaluation

The same Datalog rules yield the same answer in two modes:

- *Trusted mode* (local evaluation): Cost $tilde 8 mu s$. Used within a trust boundary.
- *Trustless mode* (STARK proof): The prover generates a STARK proof that Datalog evaluation produced `allow`. Cost $tilde 64 mu s$ prove, $tilde 438 mu s$ verify.

Both modes evaluate identical rules over identical data. The proof attests to the computation, not to a separate protocol.

== Capability Derivation and Revocation

=== The Capability Derivation Tree

In seL4 @sel4, every capability exists in a _Capability Derivation Tree_ (CDT): a tree rooted at the original untyped memory capability, where each child is derived (copied with possible attenuation) from its parent. The kernel traverses this tree synchronously to revoke an entire subtree in $O(n)$ time.

Pyana maintains a distributed analog. Each delegation step records:

$ "DelegationEdge" = ("parent": "CapHash", "child": "CapHash", "attenuation": Delta, "epoch": "u64") $

These edges form a tree committed to a Merkle structure. The CDT is not enforced by a kernel---it is _proved_ by the delegator at each step.

=== The Duality: Enforce vs. Prove

The key intellectual distinction:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Property*], [*seL4 (kernel-enforced)*], [*Pyana (proof-carried)*]),
    [Tree structure], [In-kernel data structure], [Merkle-committed proof tree],
    [Revocation], [Kernel walks tree synchronously], [Verifiable revocation claim],
    [Latency], [Instantaneous (same address space)], [Bounded staleness],
    [Distribution], [Single machine], [Cross-group],
    [Trust model], [Kernel is TCB], [Hash function is TCB],
    [Verification], [Hardware-enforced access], [STARK proof of non-membership],
  ),
  caption: [CDT duality: seL4 ENFORCES the tree; Pyana PROVES the tree.],
)

In seL4, revocation is authoritative because the kernel IS the tree---traversal and deletion are the same operation. In Pyana, the tree is a claim that anyone can verify: the delegator proves their capability descends from a valid root, and the revoker proves non-membership in the current valid set.

=== Delegation: Snapshot + Refresh

Delegation follows a snapshot-refresh model with bounded staleness. A child cell receives a point-in-time snapshot of its parent's c-list:

$ "DelegatedRef" = ("source", "snapshot": ["CapabilityRef"], "epoch", "refreshed_at", "max_staleness") $

The child acts offline using the snapshot. Acceptors (remote verifiers) reject presentations where $"now" - "refreshed_at" > "max_staleness"$. This creates a configurable tradeoff between availability and revocation freshness.

=== RevocationChannel: Opt-in Synchrony

For applications requiring instant revocation (high-value credentials, safety-critical access), Pyana provides an opt-in synchrony primitive: the _RevocationChannel_. A capability enrolled in a RevocationChannel is checked against a real-time revocation feed before acceptance. This restores seL4-like instant revocation at the cost of requiring channel liveness.

A `RevocationChannel` is a circuit breaker between a revoker and one or more subjects. Subjects voluntarily subscribe and check channel state before exercising delegated capabilities. The channel is a leaf in a group-attested Merkle tree (the "channel tree").

The lifecycle is: (1) Revoker creates a channel. (2) Subject subscribes by adding `channel_id` to their `DelegatedRef`. (3) Before exercising a gated capability, the subject checks `channel_state == Active`---one hash lookup in local state. (4) Revoker trips the channel via a signed `TripEvent`. (5) Reference group includes the trip in the next block; the attested root updates. (6) Gossip propagates the new attestation. Connected subjects learn of the trip within one consensus round.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, center),
    table.header([*Mode*], [*Revocation Latency*], [*Requires Liveness*], [*Analogy*]),
    [No check], [$infinity$ (never revoked)], [No], [Bearer token],
    [Epoch-stale], [$<= "max_staleness"$], [No], [OCSP stapling],
    [Channel-sync], [Real-time], [Yes (channel)], [CRL push],
    [Kernel-sync], [Instantaneous], [Yes (kernel)], [seL4 CDT],
  ),
  caption: [Revocation modes from weakest to strongest. Pyana supports the first three; seL4 achieves the fourth by being a kernel.],
)

The design philosophy: instant revocation is not free in a distributed system. Rather than pretending it is (and failing under partition), Pyana makes the cost explicit and lets applications choose their revocation tier.

== Provable CapTP Effects

Four CapTP operations are encoded as provable effects in the Effect VM, enabling STARK proofs of protocol correctness:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Effect*], [*What the STARK Proves*], [*Public Inputs*]),
    [ExportSturdyRef], [Swiss number correctly registered; capability exported with valid EffectMask], [Target hash, export epoch],
    [EnlivenRef], [Sturdy ref resolved; swiss number valid; live reference correctly issued], [Session ID, import slot],
    [DropRef], [Reference correctly released; refcount decremented; session epoch valid], [Session epoch, export ID],
    [ValidateHandoff], [Handoff certificate valid: Ed25519 signature verifies, recipient matches, one-time use], [Introducer key, recipient key],
  ),
  caption: [CapTP effects as provable operations. Each can be composed with authorization proofs into a single STARK.],
)

These effects enable fully trustless CapTP: a sovereign cell can prove it correctly performed a distributed capability operation without trusting the executor.

== Generalized Intent Solver

=== The Discovery Problem

Object-capability systems solve authorization but not discovery: if you need a capability to communicate, how do you find someone who holds the capability you need? Traditional answers (directories, service registries) violate the principle of least authority by publishing capability inventories.

=== Five Item Types

The intent solver operates over 5 exchangeable item types:

+ *Fungible tokens*: Computrons, stablecoins, LP tokens (divisible, interchangeable).
+ *Non-fungible tokens*: Unique identifiers (cell IDs, credential hashes).
+ *Capabilities*: Attenuated bearer tokens (service access, compute budgets).
+ *Compute*: CPU/GPU time commitments (inference slots, proof generation).
+ *Data*: Content-addressed blobs (models, datasets, query results).

=== Ring Trades

When no bilateral match exists, the solver finds multi-party cycles. A ring trade $(A -> B -> C -> A)$ satisfies all three parties simultaneously. The solver uses Johnson's algorithm bounded to cycle length $k <= 5$ over a directed compatibility graph.

=== Trustless 7-Layer Protocol

Intent fulfillment follows a 7-layer trustless protocol: SUBMIT (threshold-encrypted), BATCH (consensus-determined boundary), DECRYPT (threshold ceremony after batch seal), SOLVE (open competition with bonds), PROVE (STARK validity proof per solution), SELECT (deterministic scoring + challenge window), SETTLE (atomic compound turn). Front-running is structurally impossible: intents are encrypted until after the batch boundary is finalized. See @sec-intents for the full protocol.

== Nameservice as Capability Discovery <sec-nameservice-auth>

Nameservice resolution is a form of authorization: resolving a name yields a capability reference (specifically, a sturdy ref). The petname architecture (local petnames, edge names, proposed names) provides human-readable paths to capabilities without global naming authority. Resolution through the DFA-governed namespace requires proving route validity and ACL satisfaction---making name lookup itself a provable operation.

== Sealer/Unsealer Pairs

=== Construction

E's sealer/unsealer primitive enables rights amplification: the sealer encrypts data that only the unsealer holder can read. Pyana implements this with X25519 Diffie-Hellman:

- *Key generation*: X25519 keypair. `sealer_public` = public key; `unsealer_secret` = private key.
- *Sealing*: Fresh ephemeral X25519 keypair $arrow.r$ DH(ephemeral, sealer_public) $arrow.r$ ChaCha20-Poly1305 encryption.
- *Unsealing*: DH(unsealer_secret, ephemeral_public) $arrow.r$ same shared secret $arrow.r$ decrypt.

Each seal uses a fresh ephemeral key, providing forward secrecy.

=== Partition-Tolerant Offline Transfer

The critical use case: transferring a capability to a party that is currently offline or unreachable. The sender seals the capability under the recipient's `sealer_public`. The sealed box can traverse untrusted channels---the ciphertext reveals nothing about the capability. When the recipient comes online, they unseal using their `unsealer_secret`.

This enables a form of offline capability delegation that neither UCAN (requires online verification of the full chain) nor traditional capability systems (require live introduction) support.

=== Relationship to Rights Amplification

In E, sealer/unsealer pairs enable brand-checking: "only the holder of this specific unsealer can access this data." Pyana extends this pattern cryptographically---the sealed box carries a BLAKE3 commitment that binds the ciphertext to the capability without revealing it, enabling verification that the box contains a well-formed capability even without unsealing.
