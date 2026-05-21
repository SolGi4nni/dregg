// =============================================================================
// Section 3: Authorization Semantics
// =============================================================================

= Authorization Semantics

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
    [Distribution], [Single machine], [Cross-federation],
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

A `RevocationChannel` is a circuit breaker between a revoker and one or more subjects. Subjects voluntarily subscribe and check channel state before exercising delegated capabilities. The channel is a leaf in a federation-attested Merkle tree (the "channel tree").

The lifecycle is: (1) Revoker creates a channel. (2) Subject subscribes by adding `channel_id` to their `DelegatedRef`. (3) Before exercising a gated capability, the subject checks `channel_state == Active`---one hash lookup in local state. (4) Revoker trips the channel via a signed `TripEvent`. (5) Federation includes the trip in the next block; the attested root updates. (6) Gossip propagates the new attestation. Connected subjects learn of the trip within one consensus round.

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

=== RevocationChannel vs. Epoch Bumps

The existing `delegation_epoch` mechanism requires the child to _poll_ for staleness. The child discovers a bump only when it checks, creating an action window up to `max_staleness`. Channels improve on this in three ways:

+ *Push via gossip.* The trip is carried by federation attestation gossip. A connected subject learns within one consensus round.
+ *Provably visible.* A verifier can require "your action must include a channel-active proof at height >= H." Third-party verification becomes possible.
+ *Targeted.* A channel gates a single delegation without disturbing others. Epoch bumps revoke ALL children.

Channels are a policy choice at delegation time, not a protocol mandate. A `DelegatedRef` without a `channel_id` behaves as today: epoch-based, poll-on-staleness.

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

== Privacy-Preserving Intent Marketplace

=== The Discovery Problem

Object-capability systems solve authorization but not discovery: if you need a capability to communicate, how do you find someone who holds the capability you need? Traditional answers (directories, service registries) violate the principle of least authority by publishing capability inventories.

=== Architecture

The intent engine inverts discovery. Rather than revealing held capabilities, agents broadcast _needs_ and privately evaluate whether they can satisfy others' needs:

+ *Public intents*: A page broadcasts "I need capability matching spec $S$" as a content-addressed `Intent` identified by a blinded `CommitmentId`. The intent reveals the _shape_ of needed capability without revealing the requester's identity.
+ *Private matching*: Wallets evaluate intents locally using Datalog: "does any token in my wallet satisfy spec $S$?" This evaluation never leaves the wallet.
+ *STARK fulfillment*: If a match exists, the wallet generates a STARK proof of capability satisfaction---proving "I hold a token that satisfies $S$" without revealing which token, what delegation chain, or what else it holds.

=== Anti-Frontrunning via Commit-Reveal

Intent fulfillment uses a commit-reveal protocol: the satisfier first publishes a commitment $C = H("intent_id" || "satisfier_secret")$, then reveals the proof. This prevents a frontrunner from observing a match proof in the gossip network and racing to submit their own fulfillment.

=== What This Solves

The intent marketplace enables capability discovery without a capability directory. The requester learns only that _someone_ can satisfy their need. The satisfier reveals only that they _can_ satisfy it (via STARK), not what they hold. The gossip network sees intents (public needs) but never capabilities (private holdings).
