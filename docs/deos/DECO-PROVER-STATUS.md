# DECO/zkTLS Stripe money-in — the PROVER — status (honest)

Complements `docs/deos/DECO-MONEY-IN-STATUS.md` (the verifier + Lean crown). That
note documented the wired **verifier** and named the one remaining external piece:
the DECO **prover** — the thing that PRODUCES a `DecoPaymentAttestation` with a
genuine STARK proof. This note documents that prover, now in-tree as the
`dregg-deco-prove` crate, and states the honest status of each of its two layers.

The prover has two layers, deliberately separated. Layer 1 (the STARK over the
disclosed facts) is **real crypto, complete**. Layer 2 (the live-TLS-origin
attestation) ships as a **named interim** — do NOT read it as live-trustless-TLS.

## Layer 1 — the STARK/DECO-leaf prover core (REAL)

`deco-prove/src/prover.rs::prove_stripe_deco(facts, salt) -> DecoPaymentAttestation`.

Given disclosed Stripe payment facts (`amount_cents, currency, recipient,
payment_intent_id`) + a transcript-commitment opening `salt`, it:

1. projects the four facts to felts via the ONE canonical encoder
   `dregg_circuit::dsl::deco_payment::stripe_payment_facts_felts` (the SAME
   projection the executor felt-attach, the deployed `stripeMint` producer, and the
   in-AIR DECO leaf all decompose through);
2. proves the commitment as a foldable recursion leaf over the **deployed DECO leaf
   AIR** (`circuit-prove::deco_leaf_adapter::prove_deco_leaf_with_claim`) — a genuine
   STARK that recomputes `m1 = hash_fact(amountCents, [currency, recipient])`, the
   identity `payment_hash = hash_fact(m1, [paymentIntentId])`, the transcript
   commitment `hash_fact(payment_hash, [salt])`, and the amount range
   `1 ≤ amountCents < 2^30` IN-AIR, pinning the facts + identity at First-row PIs;
3. serializes the leaf's `BatchStarkProof` into `zk_tls_proof`
   (`serialize_deco_leaf_proof`; the prover-only `CircuitProverData` is never carried,
   the same posture as `WholeChainProofBytes`);
4. returns the `DecoPaymentAttestation` whose committed `payment_hash` is the canonical
   recompute == the leaf's in-AIR-exposed identity.

**Unforgeable at prove time.** A forged fact (bumped amount, wrong recipient, tampered
identity) is UNSAT at the leaf — the `PiBinding{First}` pins + the in-AIR `hash_fact`
recompute make a facts↔identity mismatch un-provable (`deco_leaf_adapter`'s
`forged_amount_does_not_fold` / `forged_payment_hash_does_not_fold` teeth). So the
prover **cannot** emit a passing attestation for a forged fact.

**Round-trips through the REAL verifier.** `verify_stripe_deco_stark` decodes +
structurally validates the carried proof and binds its exposed identity to the facts;
then `dregg_bridge::stripe_deco::StripeMirrorState::verify_deco_payment` (the ACTUAL
verifier, not a mock) accepts honest facts and mints the conserved amount. A forged
fact is refused by BOTH the STARK re-verify (`ProofFactsMismatch`) and the bridge
felt-commitment binding (`DecoCommitmentMismatch`) — no mint.

Full FRI re-verification of the leaf is performed by the recursion verifier when the
leaf is FOLDED into the per-turn aggregate (each child is re-verified in-circuit); the
transport tooth over the bytes is structural + exposed-claim binding.

Tests (all round-trip the real `stripe_deco.rs` verifier):

- `deco-prove/tests/roundtrip.rs::deco_prover_full_stark_roundtrip_mints` (SLOW,
  `--ignored`, ~12s): genuine STARK → `verify_stripe_deco_stark` → real bridge verifier
  → conserved mint; tampered facts refused by both teeth. **PASSES.**
- `deco-prove/tests/roundtrip.rs::deco_prover_facts_roundtrip_through_real_verifier_and_mints`
  (FAST): the prover's projection → real verifier → mint + conservation; forged refused.
- `circuit-prove::deco_leaf_adapter::deco_leaf_proof_serializes_and_reads_back_claim`
  (SLOW): a real proof serializes and its bytes decode + validate + expose the same claim.

## Layer 2 — the MPC-TLS / notary capture (NAMED INTERIM — not yet trustless)

`deco-prove/src/notary.rs`. Proving that the disclosed facts came from a **live TLS
session with Stripe's own API** needs a TLSNotary-style capture. The trustless
realization is **MPC-TLS**: the notary co-derives the TLS session secret, learns
nothing of the plaintext, and therefore cannot fabricate a transcript it did not
co-witness. That is not in-tree.

### What ships (the interim)

A **semi-honest notary** that observed the real Stripe TLS session, extracted the
disclosed `PaymentFacts`, and signs (real ed25519 — the SAME curve/lib the bridge's
off-AIR §8 carrier already trusts) the Poseidon2 transcript commitment
`transcriptCommit = hash_fact(payment_hash, [salt])`. `NotaryKeypair::attest` produces
it; `verify_notary_attestation` checks the pinned notary anchor + the ed25519 signature
(strict) + that the commitment opens to the presented facts + salt.

### The trust boundary (named, not laundered)

- **Trusted in the interim (the gap):** the notary HONESTLY observed a genuine Stripe
  TLS session and did not fabricate the disclosed facts. A dishonest notary could sign
  facts for a payment that never settled. This is exactly the gap MPC-TLS closes.
- **Already trustless (NOT the notary's job):** that the disclosed facts bind to the
  minted amount/recipient/intent — Layer 1's STARK + the bridge felt-commitment binding
  enforce this cryptographically. A notary cannot make a forged-facts attestation mint.

So the notary attests **origin** (this came from a Stripe session); the STARK attests
**integrity** (these exact facts are what was committed and minted). The interim trusts
the former; the latter is proven.

### Assessment: `tlsn` integration vs the interim

A full `tlsn` (TLSNotary) MPC-TLS integration pulls a tokio async runtime, a TLS
backend, and the two-party-computation prover/verifier stack — a large surface with its
own version graph, and it needs a running notary service. It was scoped as the named
remaining layer rather than force-fit here; the interim's ed25519 notary attestation is
real crypto with an explicit, single-sentence trust boundary. Flipping origin to
trustless = replacing `deco-prove/src/notary.rs` with an MPC-TLS `tlsn`-style capture,
with **no change** to `deco-prove/src/prover.rs` or the bridge verifier — Layer 1 and
the verifier are origin-agnostic.

## Crates touched

- `deco-prove/` (NEW): the prover core + the interim notary layer + the e2e tests.
- `circuit-prove/src/deco_leaf_adapter.rs`: added `serialize_deco_leaf_proof` /
  `verify_deco_leaf_proof_bytes` (the `zk_tls_proof` transport teeth) + tests.
- `Cargo.toml`: added `deco-prove` to workspace members.

No Lean sources, no bridge verifier semantics, and none of the lease-refactor files
were changed. The bridge stays light (it does not depend on the heavy recursion prover;
`deco-prove` does).

## What flips to live-trustless money-in

Layer 1 is done. The single remaining step to live-trustless Stripe money-in is
replacing the interim notary (Layer 2) with an in-tree MPC-TLS capture. When that
lands, production flips `MoneyIn::HmacWebhook` → `MoneyIn::Deco` at the one call site
(`bridge/src/stripe_deco.rs::verify_money_in`), and the money-in is trustless
end-to-end.
