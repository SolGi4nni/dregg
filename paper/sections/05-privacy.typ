// =============================================================================
// Section 5: Privacy Architecture
// =============================================================================

= Privacy Architecture

Pyana provides zero-knowledge authorization proofs where a prover demonstrates "I hold a valid attenuated capability chain from a group-registered issuer that satisfies your request" without revealing the chain, intermediate states, or other capabilities. However, production anonymous credential systems require additional properties beyond basic ZK authorization. This section describes the full privacy architecture from current state through target state.

== Gap Analysis: Path to Anonymous Credential Parity

Parity with Idemix/BBS+/AnonCreds requires six properties:

+ *Unlinkable multi-show*: The same credential presented N times produces N presentations that cannot be correlated by any party (including colluding verifiers).
+ *Issuer anonymity within set*: A verifier cannot determine which reference group member issued the underlying credential.
+ *Predicate proofs over attributes*: "Prove age >= 18" without revealing the exact value. Arbitrary boolean combinations of such predicates.
+ *Selective disclosure with cryptographic binding*: The prover chooses which attributes to reveal; unrevealed attributes are cryptographically guaranteed to satisfy the policy.
+ *Revocable anonymity*: Credentials can be revoked without breaking unlinkability for non-revoked credentials.
+ *Offline verification*: All of the above must work without contacting the issuer or reference group (already achieved for the STARK path).

== Current Linkability Problem

`PresentationPublicInputs` currently exposes `initial_root` and `final_root`. These are deterministic for a given token---any verifier receiving two proofs can check whether they share the same `final_root` and conclude they came from the same credential. Even with blinded issuer membership (in progress via `BlindedMerklePoseidon2StarkAir`), two presentations from the same attenuated token share the same `final_root`.

== Target: Unlinkable Presentation

A fully private, unlinkable presentation proof exposes only:

$ "PublicInputs" = ("group_root", "request_predicate", "timestamp", "blinded_tag", "revocation_root", "revealed_commitment") $

The `initial_root` and `final_root` become private witness. The `blinded_presentation_tag` is:

$ "blinded_tag" = "Poseidon2"("final_root" || "nonce" || "randomness") $

This tag is fresh per presentation (unlinkable), but deterministic given the token and nonce (for replay detection within a session). The STARK proves correct derivation from the real `final_root` without revealing it.

== Proof Structure (Target)

The unified recursive proof composes six sub-proofs internally:

+ *Blinded Issuer Membership (ring proof)*: Proves "some leaf in the group tree is my issuer" without revealing which. Public: blinded leaf, group root. Private: leaf hash, blinding factor, Merkle path.

+ *Fold Chain Validity (IVC)*: Proves "attenuation chain from issuer root to final root is valid." Both initial and final roots are private witness. Binding: final root feeds into derivation as state root.

+ *Derivation (multi-step Datalog)*: Proves "the final capability set authorizes this request." Public: request predicate. Private: state root (= final root), rules, body facts, substitutions.

+ *Body Fact Membership*: Proves "each body fact in the derivation exists in the tree at final root." All private---fact hashes and Merkle paths are witness.

+ *Non-Revocation*: Proves "my credential's ancestor hashes are not in the revocation set." Public: revocation set root. Private: ancestor hashes, non-membership witnesses.

+ *Presentation Randomization*: Proves "blinded tag is correctly derived from final root." Public: blinded tag. Private: final root, nonce, randomness.

== Blinded Queues <sec-blinded-queues>

A _blinded queue_ is a programmable queue (see @sec-effect-vm) where withdrawal is anonymized via nullifiers. The construction:

+ *Deposit*: Any cell enqueues a message commitment $C = "Poseidon2"("msg" || "randomness")$. The commitment is public; the content and randomness are private.
+ *Withdrawal*: A cell dequeues by presenting a nullifier $nu = "Poseidon2"(C || k)$ where $k$ is the withdrawal key. A STARK proves: (a) $C$ is in the queue's KZG commitment, (b) $nu$ is correctly derived from $C$ and $k$, (c) the withdrawer knows $k$.
+ *Fairness*: Each commitment can be withdrawn exactly once (nullifier uniqueness). The queue enforces FIFO ordering via the KZG polynomial structure---withdrawals must target the oldest uncommitted position.
+ *Unlinkability*: The nullifier reveals no information about which deposit it corresponds to (Poseidon2 preimage resistance).

Blinded queues enable privacy-preserving message delivery, anonymous voting, and fair resource allocation without revealing the mapping between depositors and withdrawers.

== Private Cell Migration

Sovereign cells can migrate between reference groups without revealing their identity or state:

=== Stealth Registration

+ The migrating cell derives a stealth address for the target group using the group's scan key: $"addr" = "group_spend_key" + "derive_ed25519"("BLAKE3"("DH"(r, "group_scan_key")))$.
+ The cell registers under the stealth address---the target group cannot link the registration to any known identity.
+ An IVC proof accompanies registration, proving valid history from genesis without revealing the history itself.

=== STARK Migration Proof

The migration proof demonstrates:
- The cell was validly registered in the source group (Merkle membership under source root).
- The cell's IVC chain is valid (all state transitions were sound).
- The cell's state commitment is correctly carried over (binding between old and new commitment).
- No double-registration: a nullifier derived from the source registration prevents registering the same cell twice.

The source group learns only that "some cell deregistered." The target group learns only that "some cell with valid history registered." No party can link the two events.

== Fixed-Size Proof Padding

STARK proof size is proportional to trace length, which leaks information about the computation performed (delegation chain length, derivation depth, number of effects). To mitigate timing and size-based analysis:

=== Padding Strategy

All proofs are padded to one of a small set of canonical sizes: ${2^(10), 2^(12), 2^(14), 2^(16)}$ trace rows. Padding rows use the `Noop` opcode (Effect VM) or zero-valued constraint rows (other AIRs) that satisfy all constraints trivially. The prover selects the smallest canonical size that fits the actual trace.

=== Timing Mitigation

Proof generation time is normalized: after computing the proof, the prover delays response until a fixed time quantum (configurable, default 500ms granularity). This prevents an observer from correlating response time with proof complexity.

=== Size Classes

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Size Class*], [*Trace Rows*], [*Proof Size*]),
    [Small], [$2^(10)$ (1024)], [$tilde$18 KiB],
    [Medium], [$2^(12)$ (4096)], [$tilde$24 KiB],
    [Large], [$2^(14)$ (16384)], [$tilde$32 KiB],
    [XLarge], [$2^(16)$ (65536)], [$tilde$40 KiB],
  ),
  caption: [Proof size classes. All proofs within a class are indistinguishable by size.],
)

== CapTP Privacy Model

=== Swiss Numbers Are Executor-Internal

Swiss numbers (256-bit bearer secrets for sturdy refs) never cross trust boundaries in cleartext. They are:

- Generated and stored within the target executor's swiss table.
- Transmitted to authorized parties via sealed boxes (X25519 authenticated encryption).
- Never included in STARK public inputs (they are private witness when proving CapTP effects).
- Revocable by the executor at any time (removing the swiss table entry).

An observer monitoring network traffic sees only encrypted sturdy ref URIs. The swiss number is meaningful only to the target executor---it is not a globally meaningful identifier.

=== Session Privacy

CapTP sessions between strands reveal communication patterns (who talks to whom) but not content:

- Message bodies are encrypted (X25519 per-message ephemeral keys).
- Message sizes are padded to fixed quanta (preventing content-length analysis).
- Session epochs are monotonic but do not reveal absolute time or message count.

=== Reference Group Boundary Enforcement

Messages crossing reference group boundaries are filtered by `PeerRole`:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*PeerRole*], [*Permitted Messages*], [*Privacy Guarantee*]),
    [Member], [All CapTP messages], [Full protocol access],
    [Observer], [Read-only (no mutations, no exports)], [Cannot modify state],
    [Relay], [Store-and-forward only (encrypted, no decryption)], [Cannot read content],
    [External], [Sturdy ref enlivenment only], [Minimal surface],
  ),
  caption: [PeerRole-based message filtering at reference group boundaries.],
)

The boundary enforcer inspects message types (not content) and rejects messages inconsistent with the sender's role. This prevents information leakage from misconfigured or compromised relay nodes.

== The Sovereignty Escape Hatch

For maximum privacy, a cell can go fully sovereign:

+ *Deregister* from all reference groups (publish final IVC proof).
+ *Operate peer-to-peer*: Interact only via direct STARK proofs with chosen counterparties.
+ *Zero metadata leakage*: No consensus participation, no block production, no ordering service sees any activity.
+ *Re-register on demand*: When federation services are needed, re-register with a fresh stealth address.

The sovereignty escape hatch is the privacy nuclear option: total invisibility at the cost of losing ordering services, discovery, and store-and-forward delivery. Cells can oscillate between sovereign privacy and group participation based on their current needs.

== Predicate Proofs

Range proofs and membership tests are supported within the existing derivation AIR via `CircuitLtCheck` and `CircuitGteCheck` constraints. A `PredicateBuilder` API (designed, not yet exposed) composes predicates like "age >= 18 AND country IN {US, CA, UK} AND tier >= 2" into a single STARK proof by mapping to the derivation witness's check columns.

The existing multi-step AIR already supports these checks---the work is building the ergonomic API and ensuring full composition produces a single verifiable proof.

== Revocable Unlinkability

The fundamental tension: perfect unlinkability means no party can identify a specific credential. Revocation requires the _issuer_ to identify credentials without verifiers being able to do so.

Resolution (Camenisch-Lysyanskaya style adapted to STARKs):

+ At issuance, the issuer assigns $"revocation_handle" = "Poseidon2"("issuer_secret", "credential_id")$. This handle is known only to the issuer.
+ The credential holder proves non-membership of their revocation handle in the revocation set---but the handle itself is private witness (never revealed to verifiers).
+ To revoke, the issuer adds the handle to the revocation set. The next proof attempt fails (the handle IS in the set).
+ The `NonRevocationAir` proves non-membership. The extension: derive `revocation_handle` from the credential's root inside the circuit.

This achieves "issuer-revocable, verifier-unlinkable"---the strongest achievable property without trusted hardware.

== Comparison with Existing Systems

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, center, center, center, center),
    table.header([*Property*], [*Idemix*], [*BBS+*], [*AnonCreds*], [*Pyana (target)*]),
    [Unlinkable multi-show], [Yes], [Yes], [Yes], [Yes],
    [Selective disclosure], [Yes], [Yes], [Yes], [Yes],
    [Predicate proofs], [GE only], [No], [Limited], [Arbitrary],
    [Issuer anonymity], [No], [No], [No], [Yes (ring)],
    [Post-quantum], [No], [No], [No], [Yes (STARK)],
    [Offline verify], [No], [Yes], [Partial], [Yes],
    [Proof size], [$tilde$2 KiB], [$tilde$1 KiB], [$tilde$5 KiB], [$tilde$48--80 KiB],
    [Prove time], [$tilde$50ms], [$tilde$10ms], [$tilde$100ms], [$tilde$200--500ms],
    [Verify time], [$tilde$30ms], [$tilde$5ms], [$tilde$50ms], [$tilde$10ms],
    [Programmable policy], [No], [No], [Limited], [Full Datalog],
  ),
  caption: [Privacy comparison. Pyana trades larger proofs for post-quantum security, programmable policy, and issuer anonymity.],
)

== Privacy Migration Path

The privacy architecture is deployed in phases:

*Phase 1 (in progress):* Complete issuer unlinkability via `BlindedMerklePoseidon2StarkAir`. Issuer is anonymous within the reference group ring. Same-token presentations remain linkable.

*Phase 2:* Remove `final_root` from public inputs. Add `blinded_presentation_tag`. Presentations become fully unlinkable. This is the single highest-impact change.

*Phase 3:* Predicate proof API. Build `PredicateBuilder` mapping to existing circuit machinery. No new circuit work needed.

*Phase 4:* Unified recursive proof. Single $tilde$48--80 KiB proof covering all components. Eliminates structural leakage.

*Phase 5:* Revocable unlinkability. Revocation handle derivation inside the circuit. Protocol-level change (new field in token format).

*Phase 6 (future):* Reference group privacy---turns encrypted or proved without revealing content to validators. See @sec-federation-privacy.

== Implemented Privacy Mechanisms

Beyond the credential privacy pipeline (Phases 1--6 above), several privacy mechanisms are operational today:

=== Stealth Addresses

Pyana implements stealth addresses for unlinkable payment receipt. The construction uses X25519 Diffie-Hellman for shared secret derivation and Ed25519 for the actual recipient key:

+ Sender computes ephemeral X25519 keypair $(r, R = r dot G)$.
+ Shared secret $s = "BLAKE3"("DH"(r, "recipient_scan_key"))$.
+ Stealth address derived: $"addr" = "recipient_spend_key" + "derive_ed25519"(s)$.
+ View tag $= s[0]$ enables fast scanning (recipients check one byte before attempting full derivation).

Recipients scan by: check view tag (skip 255/256 irrelevant transactions), then attempt full derivation.

=== Pedersen Commitments

Value commitments use Pedersen commitments over Ristretto with per-asset-type generators:

$ C = v dot G_"value" + r dot H + a dot G_"asset" $

where $G_"value"$, $H$, and $G_"asset"$ are independent generators (derived via hash-to-group with distinct domain separators). The asset type $a$ is hidden inside the commitment---a verifier cannot determine the asset type without the opening.

=== Bulletproof Range Proofs

Range proofs use Bulletproofs over Ristretto to prove $v in [0, 2^(64))$ without revealing $v$. These are verified in the executor (not merely checked for non-empty bytes). The `RangeProofAir` also supports in-circuit range verification for STARK-based proofs.

=== Dandelion++ Stem Routing

Transaction propagation uses Dandelion++ @dandelion to obscure the originator's network identity. In the stem phase, transactions are forwarded along a random path ($p = 0.9$ forwarding probability, $tilde$10 hops expected before fluff). The fluff phase uses standard gossip. This prevents a network observer from correlating transaction origin with IP address.

=== Delay Pool and Dummy Traffic

Intent fulfillments pass through a _delay pool_: a 30-second batching window that collects fulfillments and releases them simultaneously, mixed with dummy traffic. This prevents timing correlation between intent broadcast and fulfillment response. The pool uses BLAKE3-keyed MAC authentication (encrypt-then-MAC) for SSE-encrypted intent streams.

=== Commitment Tree Root History

Proofs may reference any recent Merkle root (not only the latest). The reference group maintains a sliding window of recent roots with TTL-based expiry. This accommodates proof generation latency: a prover can generate a STARK proof against root $R_n$ even if the current root has advanced to $R_(n+k)$, provided $R_n$ is still within the acceptance window.

== Private Vickrey Auction (4-Phase Protocol)

Pyana implements a fully private Vickrey (sealed-bid second-price) auction where no party learns any bid value, the payment amount, or the winner's identity. The protocol uses a combination of garbled circuits, oblivious transfer, threshold cryptography, Pedersen commitments, ring proofs, and stealth addresses:

=== Phase 1: Bid Commitment

Each bidder $i$ commits their bid $b_i$ using a Pedersen commitment $C_i = b_i dot G + r_i dot H$ and submits it to the auction contract. A STARK range proof proves $b_i in [0, 2^(64))$ without revealing $b_i$. The commitment is binding (bidder cannot change their bid) and hiding (no one learns the bid value).

=== Phase 2: Threshold-Encrypted Bid Revelation

After the commitment deadline, bidders encrypt their bid openings $(b_i, r_i)$ under the reference group's threshold public key. No single group member can decrypt---$t$-of-$n$ threshold decryption is required. The encrypted bids are submitted on-chain.

=== Phase 3: Garbled Circuit Evaluation

The reference group collectively evaluates a garbled circuit that computes the Vickrey outcome:
- Inputs: All bid values (threshold-decrypted within the secure computation)
- Computation: Find the highest bid (winner) and second-highest bid (payment)
- Outputs: Only the winner index and payment amount---individual bid values are NOT output

Oblivious transfer (OT) is used between group members during garbled circuit evaluation to prevent any subset from learning intermediate values. The garbled circuit construction ensures that the group learns only the final output, not the individual inputs.

=== Phase 4: Anonymous Settlement

Settlement hides the winner's identity from all observers:
- The payment amount $p$ (second-highest bid) is committed via Pedersen: $C_p = p dot G + r_p dot H$.
- The winner proves in zero knowledge (ring proof over the bidder set) that they are the winning bidder without revealing which commitment $C_i$ is theirs.
- Payment is sent to a stealth address derived for the auctioneer---network observers cannot link the payment to the auction.
- The winner receives the item via a fresh stealth address---the auctioneer cannot link the winner's payment identity to their receiving address.

=== Security Properties

- *Bid privacy*: No party (including the reference group) learns any bid value except the second-highest price.
- *Winner privacy*: The winner's identity is hidden behind a ring proof. Even the auctioneer cannot identify which bidder won.
- *Payment privacy*: The payment amount and flow are hidden behind Pedersen commitments and stealth addresses.
- *Fairness*: The threshold requirement prevents a coalition smaller than $t$ group members from learning bids early.
- *Correctness*: The garbled circuit evaluation is verifiable---a STARK proof attests that the circuit was evaluated correctly on the threshold-decrypted inputs.

*Status:* The 4-phase protocol is implemented. Garbled circuit evaluation uses Poseidon2-based garbling (STARK-friendly). OT uses the Simplest OT protocol over Ristretto. The ring proof uses a Schnorr-based linkable ring signature adapted for the bidder commitment set. End-to-end auction execution is tested with up to 64 bidders.

== Post-Quantum Safety

All privacy additions maintain PQ safety:
- Blinding uses Poseidon2 (algebraic hash, no curves)
- Presentation randomization uses Poseidon2
- Non-revocation uses Poseidon2 Merkle proofs
- Predicates use BabyBear field arithmetic
- The recursive verifier uses FRI (hash-based)
- Blinded queues use Poseidon2 nullifiers (PQ-secure)
- Fixed-size padding reveals no computational structure
- Stealth addresses use X25519/Ed25519 (classical; confined within peer relationships)
- Pedersen/Bulletproofs use Ristretto (classical; value privacy only, not cross-group)

The non-PQ components (BLS12-381 threshold signatures, Ed25519, X25519, Ristretto) are confined within reference group trust boundaries or peer relationships. Everything that crosses a trust boundary uses hash-based (PQ-secure) proofs. The PQ migration roadmap awaits lattice threshold signature standardization for BLS replacement.
