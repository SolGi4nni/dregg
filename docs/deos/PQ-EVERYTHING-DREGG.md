# The post-quantum boundary of dregg at HEAD

**HEAD audit: 2026-07-21.** Dregg contains real post-quantum organs, including
ML-DSA, ML-KEM, lattice FHE, hash/AIR proofs, and hybrid consensus admission. It
does **not** yet have an end-to-end post-quantum fhEgg/Dark Bazaar apex, shielded
transfer, game/network perimeter, or interchain endpoint. A curve operation can
be harmless compatibility code, but a curve verifier on an acceptance path is a
load-bearing classical assumption.

This document is the conservative system map. Scheme-specific reduction details
remain in [`docs/PQ-CRYPTO.md`](../PQ-CRYPTO.md); the shielded-value cutover is in
[`docs/deos/PQ-SHIELDED-COMMITMENT.md`](PQ-SHIELDED-COMMITMENT.md).

## What “native PQ” means

A **native-PQ receipt** has no acceptance condition whose soundness,
authorization, confidentiality, or liveness-integrity depends only on factoring
or discrete logarithms. A hybrid construction counts only when:

1. its PQ half is mandatory and fail-closed;
2. the PQ public key is independently enrolled and bound to the same identity,
   role, epoch, and message as the classical half; and
3. removing every classical check does not create a forgery path.

The useful audit is the **Shor projection**: pretend Ed25519, X25519, Ristretto,
ECDSA, RSA, BLS, KZG, Groth16, and classical VRFs are rubber stamps. An accepted
forgery must still require breaking ML-DSA, ML-KEM, a hash/FRI floor, or a pinned
lattice-FHE assumption. The current turn hybrid fails this test: Ed25519 is bound
to the target cell, while ML-DSA is verified against a key carried inside the
authorization, and `require_pq` defaults off
(`turn/src/executor/authorize.rs`, `turn/src/executor/mod.rs`). A quantum attacker
that forges Ed25519 can supply its own valid ML-DSA key and signature.

The target theorem should separate cryptographic acceptance from functional
correctness and external systems:

```text
NativePQAccept cfg receipt ∧ Forged receipt
  → MLDsaBreak ∨ MLKemBreak ∨ HashBreak ∨ FriBreak ∨ FheBreak

NativePQAccept cfg receipt ∧ AIRSound cfg
  → ImplementsLeanTransition receipt
```

Foreign-chain consensus, public WebPKI, passkey authenticators, and hardware
attestation roots are listed separately as external assumptions; they must not be
silently imported into the native theorem.

## Ground-truth classification

“Built” means code exists at HEAD, not that every primitive is audited or that a
whole-system theorem has been discharged. “Replace” means the component is
classically load-bearing or insufficiently bound on a current/native path.

| Surface | Class | HEAD fact / required boundary |
|---|---|---|
| Consensus finality and node turn admission | **Built PQ organ** | Hybrid Ed25519∧ML-DSA identity/enrollment exists and is enabled for central consensus (`node/src/executor_setup.rs`, `blocklace/src/finality.rs`, `node/src/finalization_votes.rs`). This does not automatically cover other receipt producers. |
| ML-DSA / ML-KEM cores | **Built PQ organ** | Routed implementations and Lean reduction shapes exist. The assumptions are Module-SIS/Module-LWE plus stated idealisations; “axiom clean” is not a concrete security estimate. |
| Hybrid KEM | **Built PQ organ** | `dregg-pq/src/hybrid_kem.rs` combines X25519 and ML-KEM. CapTP/orb have hybrid KEX organs. Generic network and PartyMPC paths have not all adopted them. |
| Hash/AIR privacy proofs | **Built PQ-shaped organ** | Poseidon2/BLAKE3/SHA and Plonky3 HidingFRI contain no DLog step. Statistical hiding is real; adversarial FRI soundness is still conditional on the named extractor/query/transcript floors. |
| BFV / TFHE | **Built PQ candidate** | Lattice-based confidentiality/compute organs exist. Concrete parameter strength, correctness/noise, DKG, and decryption assumptions need pinned estimator artifacts; a “128-bit HE-standard” label is not a proof. |
| One-time lattice LB-VRF | **Built research organ** | `dice::ServerVrf` uses `pqvrf`, but `pqvrf` explicitly lacks production codec, constant-time/zeroization/fault audit, and independent review. The live hybrid timeout can fall back to drand alone. |
| fhEgg BFV↔private-root proof | **Replace** | `fhegg-fhe/src/private_book_bfv_zk.rs` is Bulletproof R1CS over Ristretto/Pedersen with Merlin Fiat-Shamir. It explicitly relies on DLog and is not PQ. |
| fhEgg clearing quorum | **Replace** | `fhegg-fhe/src/attestation.rs::AuthenticatedQuorumVerifier` is Ed25519. Require an enrolled Ed25519∧ML-DSA roster, or PQ-only signatures in the native profile. |
| fhEgg PartyMPC | **Replace** | `fhegg-fhe/src/mpc_party/transport.rs` authenticates with Ed25519 and uses static Curve25519 DH. The file explicitly provides neither forward secrecy nor PQ confidentiality. Use mandatory enrolled ML-DSA and X25519×ML-KEM, then address malicious-share/triple correctness separately. |
| fhEgg custody / threshold lane | **Replace** | `private_book_distributed_inputs.rs` and `threshold/quorum.rs` retain Ristretto/Pedersen/Bulletproof/Schnorr and Ed25519. They are not the live distributed proof backend, and the current apex prover still sees the complete witness. |
| Turn authorization | **Replace** | Make `require_pq` native-profile mandatory and bind the ML-DSA key to the same enrolled cell identity/epoch. A self-carried valid PQ key is not an identity boundary. |
| Deployed `Effect::ShieldedTransfer` | **Replace** | `turn/src/executor/apply.rs::apply_shielded_transfer` verifies HidingFRI membership/nullifiers, then calls Ristretto/Pedersen Schnorr conservation and Bulletproof ranges. Privacy is PQ-shaped; no-mint soundness is Shor-broken. |
| Shielded `value_link_binding` | **Replace** | `cell-crypto/src/value_commitment.rs` reduces u64 value and asset type modulo BabyBear and emits one felt. It aliases `x` with `x+p`, has only a one-field collision space, and is test/compatibility code rather than a deployed PQ commitment. |
| Federation receipts / cross-federation handoff | **Replace** | `ReceiptQc::HybridVotes` has enrolled hybrid semantics, but a live producer still emits bare Ed25519 `Votes`, and the cross-federation handoff step accepts classical forms. Native PQ must select mandatory `HybridVotes`; BLS `Threshold` is interop-classical. |
| HINTS governance / threshold QC | **Replace or exclude** | The default `turn` feature links BLS12-381/KZG for governed custom authorization. Its current non-test registration surface is limited, but any use is classical. Do not put it in the native profile. |
| Game randomness | **Replace or mark external** | Live Descent/day-world randomness verifies drand BLS. ECVRF is curve-based. A server-missed hybrid draw derives from the beacon alone, so drand is then the sole classical integrity floor. Mature the lattice/hash VRF or treat drand as an explicit classical external beacon. |
| Stealth addresses / note encryption / OT | **Replace** | Active note privacy uses Curve25519 one-time addressing/ECIES; it is harvest-now-decrypt-later exposed. Chou–Orlandi Curve25519 OT is classical and appears demo/reference-only. |
| Generic QUIC/TLS/gossip | **Replace or external** | Native QUIC uses P-256 certificates and gossip Ed25519. Public HTTP uses ordinary WebPKI. Orb's hybrid X25519+ML-KEM KEX does not make classical certificate authentication PQ. |
| Passkeys | **External ceiling + replace app root** | WebAuthn uses ES256/P-256 or RS256; PRF output currently unwraps an Ed25519 root and link/credential PoP is Ed25519. Keep PRF as custody if useful, but bind claims/PoP to an enrolled PQ key. Authenticator algorithm support remains external. |
| TEE attestation | **External ceiling** | Nitro is rooted in X.509/ECDSA P-384, SNP in P-384 reports and AMD RSA-PSS roots, and TDX DCAP in ECDSA. Putting an ML-KEM key in report data does not upgrade the vendor quote root. Label these `hardware-attested/classical-root`. seL4 supplies local isolation, not a PQ remote-attestation root. |
| Ethereum / Cosmos / Solana | **External ceiling** | Ethereum finality uses BLS12-381 and wallet secp256k1; Tendermint uses Ed25519 plus ICS23 and Cosmos wallet secp256k1; Solana consensus/wallet authorization is Ed25519. These are foreign-domain assumptions, not native-PQ claims. |
| Groth16 settlement wrappers | **Interop-classical** | EVM/Cosmos/Solana settlement wraps the native proof in BN254 Groth16/pairings. The inner FRI proof does not make the outer verifier PQ. A native-PQ endpoint stops at transparent FRI unless the host chain gains a PQ verifier. |
| Storage KZG | **Legacy/optional** | `storage` has KZG feature/dependency baggage, but no live storage KZG call was found. KZG remains classical if reactivated. A BN254 field used only as arithmetic is not itself a curve assumption; pairings/KZG/Groth16 are. |

## The exact fhEgg / Dark Bazaar apex

The green apex test composes several independent guarantees. They must not be
collapsed into one “PQ” label.

| Leg | What it establishes | PQ status at HEAD |
|---|---|---|
| BFV ciphertexts | Encrypted order representation and homomorphic computation | Lattice/PQ candidate, subject to concrete parameters and threshold/DKG assumptions. |
| HidingFRI Dark Bazaar proof | Private clearing semantics and public `(p*, V*)` | Curve-free and statistically hiding; adversarial FRI soundness remains conditional. |
| BFV/private-root same opening | Ciphertexts encode the same private book committed by the semantic root | **Classical Bulletproof/Ristretto DLog.** This is why Ristretto MSM dominates the measured CPU profile. |
| Clearing quorum | Parties endorsed the exact claim | **Classical Ed25519.** It authenticates a threshold, not malicious-MPC correctness. |
| PartyMPC transport | Routed private ingress and reconstructed output | **Classical Ed25519 + Curve25519.** Semi-honest/trusted-preprocessing caveats remain. |
| Game-turn core | Turn authorization/settlement | ML-DSA code executes, but its key is not independently identity-bound and the requirement defaults off. |

Therefore GPU Ristretto MSM is a sensible optimization only for the current
prototype. It accelerates a classical proof; it cannot upgrade its security.

## Shortest no-curve proof path using existing code

Do not redesign the whole proof system. Keep the already-authored semantic proof
and replace only the classical join:

1. Retain `Market/DarkBazaarPrivateDescriptor.lean` and the existing HidingFRI
   proof of private clearing semantics.
2. Add a separate Lean-authored descriptor that takes the identical private
   orders/root and proves the exact public-key BFV equations, including the
   canonical public-key and ciphertext roots.
3. Express the degree-4096 relation as a radix-2 NTT AIR: twist, twelve forward
   stages, pointwise products, inverse transform, message/error equations, and
   faithful RNS limb/carry/quotient constraints. Avoid the current randomized
   equation compression as the final soundness boundary.
4. Emit the descriptor through the existing `EmitByName.lean` /
   `scripts/emit_descriptors.py` path and prove a theorem of the form
   `Satisfied2 → ExactPrivateBookBfvOpening`.
5. Use the existing BFV relation/message table and WGPU NTT only as witness
   generation and differential oracles. They are not proof authority.
6. Prove with Plonky3 HidingFRI and bind both proofs to one faithful, wide public
   statement. Then make ML-DSA identity and ML-KEM transport mandatory.

This yields a native route of:

```text
Lean transition semantics
  → emitted IR2/AIR
  → Plonky3 HidingFRI (private witness)
  → transparent FRI recursion / native verifier
  → faithful wide hash commitment
```

No Ristretto, BLS, KZG, Groth16, BN254 pairing, or trusted setup belongs in that
native route. Existing direct recursion re-proves retained witnesses under a
non-hiding configuration rather than verifying HidingFRI recursively, so privacy
of recursive composition needs an explicit audit; do not infer it from the base
proof.

## Hash and FRI margins for the native profile

“Hash-based” means Shor does not directly apply; it does not by itself mean
128-bit PQ security.

- A faithful eight-BabyBear digest is about 248 output bits. Generic quantum
  collision search is approximately `2^(n/3)`, so the generic collision margin
  is about 82.7 bits, not 124 or 128. A 256-bit SHA/BLAKE digest gives about
  85.3 quantum collision bits; generic preimage resistance is about 128 bits.
- For a conservative 128-bit quantum **collision-bearing** commitment, target at
  least 384 output bits. With canonical BabyBear limbs that means at least 13
  limbs; 16 limbs is a simple conservative profile. This is a sizing floor, not
  a substitute for Poseidon2 cryptanalysis.
- Fiat-Shamir/FRI needs a QROM argument and unbiased challenge sampling. Current
  Lean soundness modules retain `FriLdtExtractV3` as a hypothesis, and the
  verifier-composition audit names a word-to-proof/query bridge and biased
  `sampleBits` seam. Statistical zero knowledge proves hiding, not soundness.
- Domain separation, canonical encodings, transcript binding, and all committed
  public roots must be part of the theorem statement. One field element is not a
  security-strength receipt commitment.

## Concrete lattice-FHE admission gate

For every BFV and TFHE parameter set admitted by the native profile, check in a
reproducible lattice-estimator artifact containing:

- exact ring dimension, moduli chain, plaintext modulus, secret and error
  distributions, and estimator version/commit;
- classical and quantum primal, dual, hybrid, and relevant module/ring attack
  estimates, with the minimum reported explicitly;
- correctness/noise budget for every deployed circuit depth, including key
  switching, bootstrapping, aggregation, threshold decryption, and smudging;
- DKG/key-well-formedness and malicious-share assumptions; and
- a regression gate that fails when parameters or distributions change without
  regenerating the artifact.

The repository's `default_parameters_128` / “HE-standard” comments are useful
orientation, not this evidence.

## Profiles that keep claims honest

- **`native-pq`**: mandatory enrolled ML-DSA and ML-KEM; transparent wide-hash
  AIR/FRI proofs; pinned FHE parameter artifacts; no classically load-bearing
  curve/RSA verifier.
- **`interop-classical`**: BLS/KZG/Groth16, drand, foreign-chain consensus and
  wallets. Receipts name the classical dependency instead of inheriting the
  native theorem.
- **`external-ceiling`**: WebPKI, passkeys, and TEE vendor roots. Application
  proofs can remain PQ inside the envelope, but the external root is labelled.

The completion gate is not “no curve crates in the dependency graph.” It is:
run the Shor projection over every native acceptance path, verify that the
remaining PQ key is independently enrolled, and produce the theorem + concrete
parameter artifacts above. Until then the accurate fhEgg statement is:
**a private, proven composite apex with real PQ components and explicitly
classical proof, quorum, identity-binding, transport, and external seams.**
