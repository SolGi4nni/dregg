# TLSNotary / MPC-TLS for the DECO money-in — integration design + the REAL slice (honest)

This note designs the trustless realization of the DECO Layer-2 origin attestation
(replacing the semi-honest ed25519 notary) with **TLSNotary / MPC-TLS**, and records the
two slices now in-tree:

1. **The modeled adapter** (`deco-prove/src/tlsn_attest.rs`) — the Layer-2 interface over a
   tlsn-format Stripe fixture; the default build.
2. **THE REAL INTEGRATION** (`deco-prove/src/tlsn_live.rs`, cargo feature `tlsn-live`) — the
   **vendored (git-pinned) tlsn stack** running a **genuine local MPC-TLS 2PC roundtrip**
   against a controllable test HTTPS server: a real `tlsn` Prover + a real local Notary do
   the 2PC handshake, the Prover selectively discloses the payment facts (hiding the
   `Authorization` secret), the Notary signs a real `Attestation`, the Prover builds a real
   `Presentation`, and `presentation.verify()` yields a real `PresentationOutput` whose
   authenticated facts drive a **conserved DECO mint** through the real `stripe_deco`
   verifier. **This is not a model.** The only remaining step to full production is
   operational: point the Prover at live `api.stripe.com` (§7).

> **Status:** the `mpz` 2PC stack + tlsn @ `v0.1.0-alpha.15` **compile and run** in this
> workspace (nightly 1.98, edition 2024). The real roundtrip test passes in ~1s of 2PC.
> The earlier "not vendorable as an in-lane trustless run" verdict (§1) is **superseded** —
> see §4b/§7.

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
- **Verdict (SUPERSEDED 2026-07-05).** The original note judged this "not vendorable as an
  in-lane trustless run." That was too pessimistic: the `mpz` alpha 2PC stack + tlsn
  alpha.15 **do compile and run** here, and a **local** MPC-TLS roundtrip needs **no
  external notary binary and no live Stripe session** — the Notary is a real `tlsn`
  verifier spawned as an in-process task over `tokio::io::duplex`, and the target is a
  controllable local test HTTPS server. So the REAL machinery is now in-tree and
  green-gated behind the `tlsn-live` feature (§4b). What genuinely remains is only
  operational: swapping the local test server for live `api.stripe.com` (§7).

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
stands in for a verified presentation. This modeled slice is the **default build**.

---

## 4b. THE REAL slice (in-tree, green, feature `tlsn-live`) — vendored tlsn, live-local MPC-TLS

**Crate/feature:** `deco-prove` gains the `tlsn-live` cargo feature and
`src/tlsn_live.rs` (+ `tests/tlsn_live_roundtrip.rs`). The heavy `mpz` 2PC / tokio /
rustls backend is an **optional build feature** — with it off, the default build compiles
none of it and stays light (the no-reflexive-features rule targets *runtime* toggles; an
optional heavy crypto backend behind a *build* feature is the sanctioned use).

**Vendoring.** tlsn is **git-only**; we pin it the way the workspace pins its other git
forks (Plonky3, emberian/stylo, zed-industries/async-process, …): a **git dep at an exact
rev**, not a path/patch vendor-copy. In `deco-prove/Cargo.toml`:

```toml
tlsn                      = { git = "https://github.com/tlsnotary/tlsn", rev = "47aee45b53e06648c1b2ad3689b367b8c923fdec", optional = true }
tlsn-formats              = { git = "…", rev = "47aee45…", optional = true }
tlsn-server-fixture-certs = { git = "…", rev = "47aee45…", optional = true }
# rev 47aee45… == tag v0.1.0-alpha.15
```

tlsn is a path-based workspace, so depending on `tlsn` transitively resolves the whole
tree (+ the `mpz` `v0.1.0-alpha.6` 2PC crates + `tlsn-utils`) at the pinned rev; Cargo.lock
records all of it. **Note (API drift):** at alpha.15 the Prover and Verifier live in a
single unified `tlsn` crate (not the older `tlsn-prover`/`tlsn-verifier`/`tlsn-common`
split); `tlsn-core` is re-exported as `tlsn::{config, connection, transcript, webpki}` and
the attestation surface as `tlsn::attestation`.

**What the real slice DOES (`tlsn_live.rs`):**
- Stands up a **controllable test HTTPS server** (in-process, over `tokio::io::duplex`)
  presenting the `tlsn-server-fixture` cert (`test-server.io`) and returning a
  Stripe-payment-shaped JSON `{"id":…,"amount":2500,"currency":"usd","status":"succeeded",
  "metadata":{"dregg_recipient":"<64hex>"}}`. It reuses the fixture's exact `futures-rustls`
  TLS 1.2 path so it is MPC-TLS-compatible.
- Spawns a **real local Notary** (a `tlsn` verifier that runs the MPC-TLS commitment
  protocol and signs a real secp256k1 `Attestation`) as an in-process task.
- Runs a **real `tlsn` Prover** that performs the **MPC-TLS 2PC handshake** (the notary
  co-derives session keys, sees no plaintext), `GET /v1/payment_intents/{id}` with the
  `Authorization: Bearer …` secret, then **selectively discloses**: request target + all
  headers **except the `Authorization` value** (redacted), and the response payment facts.
- Builds a real `Presentation`; the verifier runs `presentation.verify()` → a real
  `PresentationOutput`; the disclosed facts are extracted from the **authenticated**
  response transcript, gated on `status == succeeded`, and handed to Layer 1 unchanged →
  `DecoPaymentAttestation` → **conserved mint** through the REAL `stripe_deco` verifier.

**Proven (green, non-vacuous), `tests/tlsn_live_roundtrip.rs`:**
- the honest roundtrip mints the conserved amount (2500) through the real bridge verifier;
- the `Authorization` secret is **hidden** (absent from the authenticated sent transcript);
- a **tampered `Presentation`** is refused by the real `presentation.verify()` (real
  crypto, not a structural check) — no mint;
- a wrong **server pin** is refused.

The default (non-feature) build stays green with the modeled tests (§4); the real roundtrip
runs under `cargo test -p dregg-deco-prove --features tlsn-live`.

**Honest boundary of THIS slice:** the server is a local test server, not `api.stripe.com`
(the fixture cert is for `test-server.io`, so the server pin here is `test-server.io`; live
pins `api.stripe.com`). Everything else — the 2PC, the attestation, selective disclosure,
the presentation, `verify()` — is the genuine tlsn machinery.

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

## 7. The remaining step to full live-Stripe money-in — OPERATIONAL, not code

The machinery (§4b) is built and green. What remains is a **deploy step**, not new
integration code:

1. **~~Add the `tlsn` prover deps~~ — DONE** (§4b: git-pinned behind `tlsn-live`).
2. **~~Run a local MPC-TLS session~~ — DONE** (real prover + notary + verifier, local test
   server, real presentation + verify + mint).
3. **Stand up / pin a notary for production** — self-host the `tlsn` notary (or pin a
   public one) and manage its `VerifyingKey` as the DECO anchor. (Locally the notary is an
   in-process task; production wants a durable service or a pinned public one.)
4. **Point the Prover at live `api.stripe.com`** — swap the local test server for a real
   `Prover::connect(api.stripe.com)` `GET /v1/payment_intents/{id}` with the merchant's key
   and Stripe's real Web-PKI chain; pin the server name to `api.stripe.com` instead of the
   local `test-server.io`. The disclosure logic (redact `Authorization`, reveal the facts)
   is unchanged.
5. **Flip production origin** — route `bridge::verify_money_in` `MoneyIn::HmacWebhook →
   MoneyIn::Deco` at the one call site.

Layer 1 (the STARK) and the bridge verifier require **no change** at any step — they are
origin-agnostic by construction. `tlsn_live::verify_stripe_presentation` already extracts
`StripePaymentFacts` from a real `PresentationOutput`; the live path reuses it verbatim.

**Remaining honest trust boundary at full-live:** the Web-PKI / honest-Stripe floor
(§5.1), the standard crypto carriers (MPC-TLS soundness, the notary signature scheme, STARK
extractability + Poseidon2 CR). The 2PC session-binding — modeled in §4, **executed** in
§4b — is no longer a named gap: it runs.
