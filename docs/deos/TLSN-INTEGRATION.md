# TLSNotary / MPC-TLS for the DECO money-in — integration design + first slice (honest)

This note designs the trustless realization of the DECO Layer-2 origin attestation
(replacing the semi-honest ed25519 notary) with **TLSNotary / MPC-TLS**, and records the
**first real slice** now in-tree: the Layer-2 tlsn-attestation **interface + adapter**,
exercised end-to-end by a real tlsn-format Stripe fixture.

Companion notes: `docs/deos/DECO-PROVER-STATUS.md` (Layer 1 STARK + the interim notary),
`docs/deos/DECO-MONEY-IN-STATUS.md` (the verifier + Lean crown).

---

## 1. tlsn availability + current API (grounded, not assumed)

- **Not on crates.io.** `crates.io/api/v1/crates/tlsn-core` → **404**; a `q=tlsn` search
  returns **0** crates. The local panamax mirror has no `tlsn*`. TLSNotary is
  **git-only**: `github.com/tlsnotary/tlsn`, a path-based Cargo workspace.
- **Latest tag `v0.1.0-alpha.15`** (workspace still `0.x` **alpha**; `main` active
  mid-2026). Members: `tlsn`, `tlsn-core`, `tlsn-mpc-tls`, `tlsn-deap`, `tlsn-formats`,
  `tlsn-attestation`, `tlsn-key-exchange`, `tlsn-hmac-sha256`, `tlsn-cipher`,
  `tlsn-server-fixture(-certs)`, `tlsn-tls-core`, `tlsn-sdk-core`, `tlsn-wasm`, harness
  crates.
- **Dep weight (heavy).** The 2PC core is `mpz-*` (privacy-ethereum/mpz, pinned rev
  `v0.1.0-alpha.6`), plus `rustls`, `k256`/`p256`, `aes-gcm`, a `tokio` async runtime,
  `hyper`, and `websocket-relay`. It is **not a pure library**: producing an attestation
  needs a **running notary service** the Prover connects to and co-runs the TLS session
  with.
- **Current prover → notary → verifier flow** (from `crates/examples/attestation/*` @
  alpha.15):
  1. **Prover** opens a `Session` to the notary socket; `handle.new_prover(ProverConfig)`
     then `.commit(MpcTlsConfig { max_sent_data, max_recv_data })`.
  2. `prover.connect(TlsClientConfig{ server_name, root_certs })` runs the **MPC-TLS**
     handshake with the target server (2PC — the notary co-derives session keys, sees no
     plaintext). HTTP request/response over `hyper`.
  3. `HttpTranscript::parse(prover.transcript())` → `TranscriptCommitConfig`
     (`DefaultHttpCommitter`) → `prover.prove(ProveConfig)`. The notary returns a signed
     **`Attestation`**; the prover holds **`Secrets`**.
  4. **Presentation:** `secrets.transcript_proof_builder()` + `builder.reveal_recv(
     json.get("amount"))` etc. **selectively disclose** authenticated spans → a
     **`Presentation`** (bincode).
  5. **Verifier:** `presentation.verify(&CryptoProvider)` →
     `PresentationOutput { server_name, connection_info.time, transcript }` where
     `transcript` is a `PartialTranscript` (undisclosed bytes set to fill `X`);
     `presentation.verifying_key()` is the notary key the verifier **pins**.
- **Verdict: not vendorable as an in-lane trustless run.** It needs a live notary
  service + the `mpz` alpha 2PC stack + a live Stripe TLS session, on a `0.x`-alpha,
  churning, tokio-async surface. Standing that up here would be a force-fit and could not
  be green-gated. → we build the **interface + adapter + real fixture** (the honest
  Branch-2 outcome) and name the remaining wiring exactly.

---

## 2. Architecture

```
   Stripe API  ── MPC-TLS session (2PC) ──►  PROVER (our infra)  +  NOTARY (self-hosted)
   GET /v1/payment_intents/{id}              co-run TLS; notary sees NO plaintext
   {"status":"succeeded","amount":..}                 │
                                                       ▼  selective disclosure
                                        tlsn Presentation  ──►  presentation.verify()
                                        (auth transcript,        PresentationOutput
                                         facts disclosed,        { server_name, time,
                                         Bearer secret redacted)   PartialTranscript }
                                                       │
                                                       ▼  ADAPTER (this slice)
                             deco_prove::tlsn_attest::verify_tlsn_presentation
                             pin server=api.stripe.com · pin notary · sig · selective
                             disclosure · status==succeeded · parse facts
                                                       │  StripePaymentFacts
                                                       ▼
                             prover::prove_stripe_deco → DecoPaymentAttestation
                             (Layer 1 STARK — REAL, unchanged)
                                                       │
                                                       ▼
                             bridge::verify_deco_payment ── Ok ──► Effect::Mint (Σδ=0)
```

**Notary: self-hosted vs public service.**
- *Self-hosted notary* (recommended for money-in): we run the notary; trust reduces to
  "the notary ran the tlsn protocol honestly" — and under MPC-TLS even a byzantine notary
  **cannot fabricate** a transcript (it never holds the plaintext session), so the residual
  is availability/liveness, not integrity. This is the strong posture.
- *Public notary service* (e.g. a community notary): removes our operational burden but
  the verifier must pin that notary's key and trust its attestation policy. Same
  cryptographic non-fabrication guarantee; different key-management/trust-anchor choice.
Either way the DECO verifier **pins** the notary `VerifyingKey` — a wrong-notary
presentation is refused (`TlsnAdapterError::WrongNotary`).

---

## 3. The swap: how the tlsn attestation replaces the semi-honest notary

`deco-prove/src/notary.rs` (Layer 2a, the interim) has a notary **sign a commitment to
facts it claims it saw** — trust = the notary honestly observed and did not fabricate.
`deco-prove/src/tlsn_attest.rs` (Layer 2b, this slice) has the adapter **read the facts
out of an authenticated transcript** the notary co-produced but could not forge. Both
emit the SAME `StripePaymentFacts`; Layer 1 (`prover.rs`) and the bridge verifier
(`stripe_deco.rs`) are **origin-agnostic and untouched**. Production origin moves from
`NotaryKeypair::attest` to `verify_tlsn_presentation` when the notary+2PC are wired, and
`bridge::verify_money_in` flips `MoneyIn::HmacWebhook → MoneyIn::Deco` at one call site.

**Selective disclosure over the Stripe object.** The prover discloses exactly the payment
facts and nothing else:
- from the **response**: `id`, `amount`, `currency`, `status`, and
  `metadata.dregg_recipient` (the same recipient key the HMAC path reads);
- from the **request**: only the target path — the `Authorization: Bearer sk_live_…`
  secret is **redacted** (the killer property: prove the payment without revealing your
  Stripe API key).

---

## 4. The first real slice (in-tree, green) — what it IS and IS NOT

**Crate:** `deco-prove/` extended with `src/tlsn_attest.rs` (+ `lib.rs` re-exports, +
the `notary.rs` swap-point pointer, + `tests/roundtrip.rs` e2e). No new crate; Layer 1
and the bridge verifier unchanged.

**IS — a real, non-vacuous adapter over a real tlsn-format fixture:**
- Models the exact `presentation.verify()` output (`TlsnVerifyingKey`, `server_name`,
  `connection_time`, `PartialTranscript{ data, authed }`, disclosed-fact spans) — the
  type correspondence to `tlsn-core` alpha.15 is tabled in the module docs.
- The fixture is a realistic authenticated `GET api.stripe.com/v1/payment_intents/{id}`
  HTTP/1.1 transcript with the Bearer secret redacted and the fact JSON value-spans
  disclosed (undisclosed bytes = fill `X`, tlsn's `set_unauthed(b'X')`).
- The adapter enforces, non-vacuously (each has a biting test): **server pinning**,
  **notary pinning**, the **presentation signature** (tampering a disclosed byte breaks
  it), **selective disclosure** (a redacted amount/recipient is *unreadable* → refused,
  not silently defaulted), the **`succeeded`** gate, and fact parsing.
- End-to-end: the extracted facts feed the DECO attestation and mint the **conserved**
  amount through the **REAL** `stripe_deco` verifier; a forged selective disclosure is
  refused before any mint (`tests/roundtrip.rs::tlsn_presentation_binds_into_layer2_and_mints`).

**IS NOT — a live trustless MPC-TLS run.** The signature curve is modeled as ed25519 (the
in-tree curve; tlsn's real notary uses secp256k1/p256 — a config detail). The 2PC
session-integrity — the reason the notary's signature is *trustless* rather than *trusted*
— is modeled **structurally** (authenticated ranges) but **not executed**. The fixture
stands in for a verified presentation. We do **not** claim live-trustless-Stripe money-in.

---

## 5. The trust boundary — removed vs remaining

**tlsn REMOVES** (once the 2PC is wired): trust that the notary *honestly observed and did
not fabricate* the Stripe session. Under MPC-TLS the notary co-derives the session secret
without ever seeing plaintext, so it cannot forge a transcript it did not co-witness — a
signed presentation *is* a genuine `api.stripe.com` session.

**REMAINING honest boundary (named):**
1. The **Web-PKI / honest-Stripe floor** — that `api.stripe.com`'s certificate chain is
   genuine and Stripe reports settlement truthfully. (Irreducible; shared with any oracle.)
2. The **standard crypto carriers** — MPC-TLS soundness, the notary signature scheme,
   and (Layer 1) STARK extractability + Poseidon2 CR.
3. **In THIS slice specifically** — the 2PC session-binding is modeled, not run.

---

## 6. Exact remaining wiring to full live-Stripe money-in

1. **Stand up a notary** — self-host the `tlsn` notary server (or pin a public one),
   manage its `VerifyingKey` as the DECO anchor.
2. **Add the `tlsn` prover deps** — git-pin `tlsn`/`tlsn-core`/`tlsn-mpc-tls` (+ `mpz`
   rev), behind a `deco-prove` feature so the heavy tokio/rustls/2PC surface stays out of
   the default build until it is exercised live.
3. **Run the live MPC-TLS session** — `Prover::connect(api.stripe.com)` for
   `GET /v1/payment_intents/{id}` with the merchant's key, `reveal_recv` the fact spans,
   `reveal_sent` only the target (redact the Bearer secret) → a real `Presentation`.
4. **Feed `presentation.verify()` output into the adapter** — replace the fixture's
   modeled `PresentationOutput` with the real one (the field map already matches);
   `verify_tlsn_presentation` binds it to `StripePaymentFacts` unchanged.
5. **Flip production origin** — `NotaryKeypair::attest` → `verify_tlsn_presentation`; then
   `bridge::verify_money_in` `MoneyIn::HmacWebhook → MoneyIn::Deco`. Money-in is trustless
   end-to-end.

Layer 1 (the STARK) and the bridge verifier require **no change** at any step — they are
origin-agnostic by construction.
