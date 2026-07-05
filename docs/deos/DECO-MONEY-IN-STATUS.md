# DECO-verified Stripe money-in — status (honest)

The Stripe money-in has a **proven, DECO/zkTLS-verified path** wired alongside the
original trusted-HMAC-webhook oracle. This note states exactly what is proven,
what is wired, and the one remaining external piece — so nobody reads it as
"live-trustless money-in" before it is.

## The two paths (one entry, `bridge/src/stripe_deco.rs`)

`StripeMirrorState::verify_money_in(MoneyIn)` dispatches a money-in source to a
`VerifiedPayment` for the committed bridge mint:

- **`MoneyIn::Deco(&DecoPaymentAttestation)`** — the intended **trustless** path.
  Mint only against a DECO attestation: a zkTLS proof that a live TLS session with
  Stripe's API disclosed a settled payment. `verify_deco_payment` runs the DECO
  leaf's own teeth in the executor domain.
- **`MoneyIn::HmacWebhook { .. }`** — the explicitly-labeled **trusted FALLBACK**
  (`// FALLBACK: trusted HMAC until the DECO prover lands — NOT trustless`). Trusts
  a valid `Stripe-Signature` HMAC under a shared webhook secret. The only working
  money-in today. Kept so production flips to `MoneyIn::Deco` with a one-variant
  change at the call site.

## What is PROVEN

`metatheory/Dregg2/Crypto/Deco.lean`: an accepting DECO proof PROVES a genuine
Stripe-authenticated payment (`deco_authenticates_payment`, `deco_verify_sound`,
`deco_binds_payment`), modulo the named §8 carriers (STARK extractability, ed25519
EUF-CMA, HMAC unforgeability, Poseidon2 CR) and the external Web-PKI / honest-Stripe
floor. The six Stripe money-in apexes back the mint-against-lock semantics.

## What is WIRED (the deployable half)

`verify_deco_payment` re-runs the DECO leaf's anti-vacuity tooth in the executor
domain:

1. **gate 5 (range):** `1 ≤ amountCents < 2^30` (`DecoAmountOutOfRange`).
2. **gates 3/4 + identity (felt-commitment binding):** recompute the felt
   `payment_hash` over the disclosed facts through the ONE canonical encoder
   `dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt` — the SAME projection
   the executor felt-attach, the deployed `stripeMint` producer, and the in-AIR DECO
   leaf (`circuit-prove::deco_leaf_adapter`) all decompose through — and REFUSE any
   attestation whose committed `payment_hash` disagrees (`DecoCommitmentMismatch`).
   This is the executor-domain twin of the leaf's `forged_amount_does_not_fold` and
   the `DecoBackingAttack` red-team.
3. currency + amount bounds (shared with the HMAC path).

Conservation (`live_supply ≤ total_verified_payments`) holds on the DECO path
exactly as on the HMAC path — the mint draws against recorded backing via the same
`mint_against_payment` route. Tests: `bridge/src/stripe_deco.rs::tests` (valid DECO
attestation mints the conserved amount; three forged-facts shapes refused; gate-5
range; currency/bounds; retry dedup; the `verify_money_in` flip).

## ⚑ THE PROVER GAP (do NOT claim live-trustless money-in yet)

The DECO *verification* is proven and wired; the DECO **prover** — the zkTLS client
that runs a live Stripe TLS session and EMITS a `DecoPaymentAttestation` carrying a
genuine STARK proof (`DecoPaymentAttestation::zk_tls_proof`) — is the one external
piece NOT yet in this tree. Until it lands, the commitment binding rebinds the
disclosed facts to the committed identity (refusing a tampered attestation) but does
NOT by itself prove the facts came from a genuine Stripe session; that is exactly
what the STARK carrier delivers, verified when the prover exists. So the HMAC
fallback remains the live money-in, and `MoneyIn::Deco` becomes live-trustless the
moment the prover is in-tree.

## Agent twin

`dregg-agent/src/stripe.rs` is a **standalone demo stub** (dregg-agent is
substrate-only, no bridge/circuit deps by design): it mints into its OWN private
ed25519 receipt chain, not the shared value layer. Labeled as such; the real earn
routes through `bridge`'s DECO money-in above.
