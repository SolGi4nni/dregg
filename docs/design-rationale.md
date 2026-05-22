# Design Rationale: Why Pyana Exists This Way

## System Identity

Pyana: prove what you can do without showing who you are.

Private, portable, offline-verifiable authorization proofs for mutually suspicious agents. The system lets software agents prove authorization without revealing who authorized them, what else they can do, or that they are the same agent who acted before.

The core promise is unlinkable capability delegation verified by zero-knowledge proof. An agent presents evidence it holds sufficient authority for some action, and the verifier learns nothing beyond "this action is authorized" — not the delegation chain, not the delegator's identity, not other capabilities the agent holds.

## The E Lineage

Pyana is a faithful implementation of Mark Miller's capability security model from E, translated into a proof-verification architecture.

**Direct correspondences:**

- **C-lists** become `CapabilitySet` with unforgeable references — each agent holds an enumerable set of capabilities, never ambient authority.
- **Attenuation-only delegation** enforces monotone narrowing — you can only grant subsets of what you hold.
- **Sealer/unsealer pairs** become cryptographic Brand patterns via X25519 — the E pattern of "only the holder of the unsealer can extract the sealed value" maps directly to asymmetric encryption.
- **Granovetter introductions** become `Effect::Introduce` with lifetime bounds — capabilities flow only along existing edges in the capability graph, with explicit expiry.
- **Delegation snapshots** become `DelegatedRef` for offline verification — frozen capability evidence that can be checked without network access.

**What pyana transforms:** Cells are verified state-slots rather than live objects. Proofs authorize state transitions rather than routing messages. The verification layer replaces the execution layer as the enforcement mechanism. This is the fundamental architectural shift — E enforced capabilities at message-dispatch time; pyana enforces them at proof-verification time.

**What pyana adds beyond E:** Private capabilities via ZK, federation consensus as trust anchor, cross-domain portability via proof-carrying notes, and conservation laws enabling economic coordination.

**The key tension:** Privacy versus accountability. E required caller identification for accountability — you could always ask "who sent this message?" Pyana's ZK breaks this intentionally. Unlinkability IS the feature for its threat model: surveillance resistance across trust boundaries. Resolution: the `Either` authorization mode allows both paths. Systems that need accountability use signature-based auth; systems that need privacy use proof-based auth; systems that need both offer either.

**The incomplete promise:** Eventual refs exist but don't cross turn boundaries. True async promises mediated by the causal DAG would reunite E's live-object model with pyana's proof-verification layer. This remains future work.

## Trust Topology

A federation is simultaneously a consensus group, a trust domain, a state silo, and a namespace. This conflation is intentional — one primitive instead of four reduces the combinatorial surface of trust assumptions.

BFT consensus exists specifically for three things: revocation ordering, attested root agreement, and double-spend prevention. Everything else is proof-carrying and requires no consensus. If you can verify a proof offline, you never need to ask a federation about it.

The expected deployment is many small federations (organization-scale, 4-20 nodes) connected via asymmetric bridges. Not one global chain. Each org runs its own trust domain, and cross-org interactions happen via proof exchange rather than shared state.

Semi-trust decomposition:
- **Coordinator** provides liveness (not safety) — it can delay but not forge.
- **BFT** provides ordering (not execution) — it sequences but doesn't interpret.
- **Proofs** provide authorization (not identity) — they attest capability without attribution.

No single component has full authority. Safety emerges from their composition.

## Economic Model

Two products coexist in one system:

1. **Private authorization infrastructure** — capabilities, atomicity, audit trails. This is the capability-security layer.
2. **Private multi-asset ledger** — notes, conservation, bridges. This is the value layer.

Notes are not just payments. They are transferable capabilities with conservation laws. A bounty is a capability-note: it grants authority AND transfers value in one atomic object. The economic layer makes capabilities composable with real-world incentives.

Computron metering serves as DoS protection, not resource pricing. The fee model prevents spam; it does not create a market for block space. Node honesty depends on contractual relationships between federation members, not fee revenue. Security is cryptographic, not economic — this is not a system where "it costs more to attack than you gain."

## Privacy Model

The privacy stance is "private authorization, public execution."

ZK hides credential chains from verifiers — when an agent presents a proof of authorization, the verifier learns nothing about the delegation path that established that authorization. Federation nodes, however, see execution — they process state transitions and know which cells changed.

This is coherent for the target use case: cross-silo authorization where you want to hide delegation paths from relying parties while accepting that your own infrastructure (your federation) sees state transitions. You trust your own nodes; you don't trust the counterparty's verifier.

The implicit threat model: the adversary is the verifier/relying party and network observers. NOT the federation executor. This should be made explicit in future documentation, as it bounds where the privacy guarantees apply.

## Minimal Viable System

The shippable core is approximately 12 crates and 80k LOC: `types` + `cell` + `token` + `circuit` (core) + `commit` + `federation` + `bridge` + `sdk` + `wire` + `node`. This mints tokens, attenuates capabilities, presents them privately, and verifies non-revocation. It ships with the custom STARK backend alone.

## What Needs Recursion

Recursive proof composition is required for:
- **Unbounded delegation chains** — constant-size proof regardless of delegation depth.
- **Mina L1 interop** — Mina's architecture expects recursive verification.
- **Recursive state compression** — light clients that verify federation state without replaying history.

Most real deployment scenarios work with bounded-depth STARK proofs. Recursion is an optimization for scale, not a prerequisite for correctness. The system is designed to ship without it and add it later.

### Recursion levels (what the external verifier must do)

1. **Mina-equivalent** (target): All verification in-circuit except the `sg` MSM. External
   verifier does only `batch_dlog_accumulator_check` — one batch MSM over SRS generators.
2. **Assisted recursion** (operational): All IPA operations deferred. External verifier runs
   full `kimchi::verifier::verify` including the complete IPA batch check.
3. **Pure computation** (STARK): No recursion. Full FRI + Merkle + constraint checking.

IPA fundamentally requires external MSM. There is no fully "self-verifying" IPA proof —
the correct claim is "constant-size proof with minimal external verification."
