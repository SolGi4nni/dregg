// =============================================================================
// Section 5: Privacy Architecture
// =============================================================================

= Privacy Architecture

Pyana provides zero-knowledge authorization proofs where a prover demonstrates "I hold a valid attenuated capability chain from a federation-registered issuer that satisfies your request" without revealing the chain, intermediate states, or other capabilities. However, production anonymous credential systems require additional properties beyond basic ZK authorization. This section describes the full privacy architecture from current state through target state.

== Gap Analysis: Path to Anonymous Credential Parity

Parity with Idemix/BBS+/AnonCreds requires six properties:

+ *Unlinkable multi-show*: The same credential presented N times produces N presentations that cannot be correlated by any party (including colluding verifiers).
+ *Issuer anonymity within set*: A verifier cannot determine which federation member issued the underlying credential.
+ *Predicate proofs over attributes*: "Prove age >= 18" without revealing the exact value. Arbitrary boolean combinations of such predicates.
+ *Selective disclosure with cryptographic binding*: The prover chooses which attributes to reveal; unrevealed attributes are cryptographically guaranteed to satisfy the policy.
+ *Revocable anonymity*: Credentials can be revoked without breaking unlinkability for non-revoked credentials.
+ *Offline verification*: All of the above must work without contacting the issuer or federation (already achieved for the STARK path).

== Current Linkability Problem

`PresentationPublicInputs` currently exposes `initial_root` and `final_root`. These are deterministic for a given token---any verifier receiving two proofs can check whether they share the same `final_root` and conclude they came from the same credential. Even with blinded issuer membership (in progress via `BlindedMerklePoseidon2StarkAir`), two presentations from the same attenuated token share the same `final_root`.

== Target: Unlinkable Presentation

A fully private, unlinkable presentation proof exposes only:

$ "PublicInputs" = ("federation_root", "request_predicate", "timestamp", "blinded_tag", "revocation_root", "revealed_commitment") $

The `initial_root` and `final_root` become private witness. The `blinded_presentation_tag` is:

$ "blinded_tag" = "Poseidon2"("final_root" || "nonce" || "randomness") $

This tag is fresh per presentation (unlinkable), but deterministic given the token and nonce (for replay detection within a session). The STARK proves correct derivation from the real `final_root` without revealing it.

== Proof Structure (Target)

The unified recursive proof composes six sub-proofs internally:

+ *Blinded Issuer Membership (ring proof)*: Proves "some leaf in the federation tree is my issuer" without revealing which. Public: blinded leaf, federation root. Private: leaf hash, blinding factor, Merkle path.

+ *Fold Chain Validity (IVC)*: Proves "attenuation chain from issuer root to final root is valid." Both initial and final roots are private witness. Binding: final root feeds into derivation as state root.

+ *Derivation (multi-step Datalog)*: Proves "the final capability set authorizes this request." Public: request predicate. Private: state root (= final root), rules, body facts, substitutions.

+ *Body Fact Membership*: Proves "each body fact in the derivation exists in the tree at final root." All private---fact hashes and Merkle paths are witness.

+ *Non-Revocation*: Proves "my credential's ancestor hashes are not in the revocation set." Public: revocation set root. Private: ancestor hashes, non-membership witnesses.

+ *Presentation Randomization*: Proves "blinded tag is correctly derived from final root." Public: blinded tag. Private: final root, nonce, randomness.

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

*Phase 1 (in progress):* Complete issuer unlinkability via `BlindedMerklePoseidon2StarkAir`. Issuer is anonymous within the federation ring. Same-token presentations remain linkable.

*Phase 2:* Remove `final_root` from public inputs. Add `blinded_presentation_tag`. Presentations become fully unlinkable. This is the single highest-impact change.

*Phase 3:* Predicate proof API. Build `PredicateBuilder` mapping to existing circuit machinery. No new circuit work needed.

*Phase 4:* Unified recursive proof. Single $tilde$48--80 KiB proof covering all components. Eliminates structural leakage.

*Phase 5:* Revocable unlinkability. Revocation handle derivation inside the circuit. Protocol-level change (new field in token format).

*Phase 6 (future):* Federation privacy---turns encrypted or proved without revealing content to validators. See @sec-federation-privacy.

== Post-Quantum Safety

All privacy additions maintain PQ safety:
- Blinding uses Poseidon2 (algebraic hash, no curves)
- Presentation randomization uses Poseidon2
- Non-revocation uses Poseidon2 Merkle proofs
- Predicates use BabyBear field arithmetic
- The recursive verifier uses FRI (hash-based)

The only non-PQ component remains BLS12-381 threshold signatures in the federation layer, on the PQ migration roadmap awaiting lattice threshold signature standardization.
