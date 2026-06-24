# `dregg` Caveat Discharge Model

## What Caveat Discharge Is Here

`dregg` extends standard macaroon discharge in two directions. First, classic third-party caveats: a `MacaroonToken` carries `discharges: Vec<Macaroon>` which are verified during the HMAC chain check (`self.inner.verify(&*self.root_key, &self.discharges)`). The holder collects discharge macaroons from external services before presentation.

Second, and more novel: the `Revocable` caveat (type 15) and `Budget` caveat (type 14) implement *stateful discharge*. These require the verifier to supply external state (`not_revoked`, `budget_states`) proving the caveat still holds. This inverts standard discharge: instead of the holder obtaining a discharge token, the *verifier* must attest freshness. The fail-closed semantics mean missing state is denial, not passthrough.

## Progressive Disclosure via Three Verification Modes

The fulfillment protocol implements progressive trust escalation through `VerificationMode`:

1. **Private** -- STARK proof only. Proves "I hold a valid capability satisfying your spec" with zero additional disclosure. The verifier learns the conclusion (allow/deny) and the accumulated hash, nothing else.

2. **Selective** -- STARK proof + `revealed_facts_commitment`. The prover chooses which derived facts to disclose. The commitment (`poseidon2(hash(fact_1) || ... || hash(fact_n))`) binds revealed facts to the STARK, so the prover cannot lie about what was derived. The verifier sees chosen facts, not the full chain.

3. **Trusted** -- Real HMAC-chained attenuated macaroon. Full token disclosure with cryptographic integrity. Cheapest to verify (~0.5us) but maximum revelation.

A holder can start at Private (proving only "I am authorized"), escalate to Selective (revealing the service grant but not the issuer or delegation depth), and finally provide Trusted mode if the counterparty demands HMAC-verifiable delegation.

## Contextual Predicates

The `PredicateProgram` system (`predicate_program.rs`) is remarkably expressive. Leaf predicates include:

- **Range** (value >= threshold, value < threshold, etc.)
- **Membership/NonMembership** (set inclusion via Merkle/accumulator proofs)
- **Temporal** (predicate held for N consecutive blocks)
- **Relational** (my committed value vs. their committed value)
- **CommittedThreshold** (value >= hidden threshold, where the threshold itself is private)
- **Arithmetic** (expression over multiple inputs satisfies a comparison)

These compose with AND/OR/Threshold(k-of-n)/ThresholdBelow. The `CommittedThreshold` predicate is particularly powerful: the verifier commits to a secret threshold, the prover proves their value exceeds it, and *neither party learns the other's value*. Context (timestamps, IP ranges) enters through the `AuthRequest` and becomes part of the trace -- provable in ZK without revealing the context values.

## Third-Party Discharge in Zero Knowledge

Yes, this is implemented. The `BridgePresentationBuilder` produces a STARK proof covering the entire authorization derivation -- including any third-party attestation facts committed to the token state. The `WirePresentationProof` strips the trace before transmission, so the verifier sees:

- The federation root (which third-party ecosystem)
- The action binding (what was authorized)
- The STARK proof (valid derivation exists)

But NOT: which issuer, which rules fired, what attestation facts existed, or how deep the delegation chain was. Ring membership (blinded issuer proof) makes even the issuer unlinkable across presentations. A third-party caveat discharge becomes: "some member of this federation attested something that, combined with my credentials, satisfies your policy."

## Delegation Chains as Selective Disclosure

In `dregg`, attenuation IS the disclosure mechanism. The fold chain (root state -> attenuated state -> further attenuated state) is proven via STARK without revealing intermediate states. Each fold step removes facts (narrowing), and the `FoldWitness` proves the removal was from the committed state.

This differs fundamentally from BBS+/Idemix attribute selection. In those systems, you select which attributes to reveal from a fixed credential. In `dregg`, you *construct a narrower credential* by adding caveats, then prove the narrowed version satisfies the request. The attenuation chain itself is the privacy tool: you never present the root token, only a provably-derived restriction of it. The `MAX_FOLD_DEPTH` limit exists for soundness, not expressiveness.

## Private Policy Evaluation (The Datalog Dimension)

This is the most distinctive feature. The `derivation_air.rs` circuit proves a single Datalog rule application in ZK: given committed body facts and a substitution, it derives a head fact. The `multi_step_air` chains multiple derivation steps. The verifier sees only that the conclusion is `allow` -- not which rules fired, what facts were matched, or what the substitution was.

Concretely: the policy rules (`full_policy()` in `datalog_verify.rs`) define when to allow. The `DerivationWitness` contains the rule ID, body fact hashes, and substitution -- all private. The circuit enforces:
- Body facts exist in the committed state (Merkle membership)
- Substitution correctly resolves head terms (selector constraints)
- Equal/MemberOf/GTE/LT checks pass under the substitution
- The derived hash matches the public input

The policy root is committed via `compute_policy_root()` (hashing full rule structures, not just IDs), so the prover cannot swap rules. But the *evaluation trace* is private. This means: the verifier publishes a policy commitment, the prover demonstrates satisfaction, and neither the specific rule path nor the matching facts are revealed. No other system we are aware of proves Datalog evaluation in ZK with this level of privacy for the policy itself.

What it enables: authorization decisions where the verifier does not learn *why* access was granted -- only that it was, under a committed policy. Combined with ring membership, even the identity of the policy evaluator is hidden.
