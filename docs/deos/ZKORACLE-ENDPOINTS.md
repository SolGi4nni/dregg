# zkOracle endpoints — the generality proof (verify any web fact)

The zkOracle attestation (`dregg-zkoracle-prove`) was born over one endpoint — an
Anthropic `POST /v1/messages` session. Its three legs — **authentic** (a tlsn/MPC-TLS
session with a pinned host, secrets redacted), **well-formed** (a real JSON CFG parse
certificate), **injection-free** (the `neg`-complement handlebars matcher) — plus the
cross-leg content-commitment weld are **endpoint-agnostic**. This document records the
generalization: a new verified-web-oracle is DATA (`EndpointSpec`) plus a response schema,
not a fork of the prover.

## The endpoint config

`authentic::EndpointSpec` factors out the endpoint-specific bits:

| field           | what it pins / shapes                                        |
|-----------------|-------------------------------------------------------------|
| `server_name`   | the TLS host the session is pinned to (`api.github.com`, …) |
| `method`        | the request line method (`POST` / `GET`)                    |
| `secret_header` | the redacted secret header, or `None` for a public endpoint |

`EndpointConfig = EndpointSpec + expected_notary` is the canonical config the whole
prover/verifier (`prove_zkoracle` / `verify_zkoracle`) takes. The authentic-leg verifier
(`verify_endpoint_presentation`) and the fixture producer (`build_endpoint_fixture`) are
driven entirely by the spec; the redaction step runs iff `secret_header` is `Some`. The
Anthropic endpoint is now just `EndpointSpec::anthropic_messages()`; `AnthropicConfig` is a
thin back-compat newtype that `Deref`s to `EndpointConfig`, so the original Anthropic API is
unchanged (no regression). The per-endpoint *response schema* (the typed fact a body parses
into) lives with each endpoint module (`endpoints::github`, `endpoints::price`).

## The three endpoints

### Anthropic — `POST api.anthropic.com/v1/messages` (`endpoints`-external, the origin)

Authed (`x-api-key` redacted — prove the response without revealing the key), and the one
endpoint where the **injection-free** leg is load-bearing: the user field is a committed
substring of the authenticated body, checked against `neg (.* {{ .*)`.

### GitHub — `GET api.github.com/repos/{owner}/{repo}/commits/{sha}` (`endpoints::github`)

Public, no auth. `verify_github_commit` runs the full `verify_zkoracle` (authentic ∧
well-formed ∧ weld), parses `owner`/`repo`/`sha` from the **authenticated request target**
and `author`/`date`/`message`/`sha` from the **authenticated response body**, and
cross-checks the two `sha`s — so the response is provably about the commit that was asked
for. The extracted `GithubCommitFact` is: the commit exists, by `{author}`, at `{date}`,
with `{message}`.

**Injection-free leg: N/A.** A read-only commit lookup has no user-supplied field, so the
attestation uses an empty field (vacuously injection-free). The honest teeth are authentic
∧ well-formed ∧ the cross-leg weld ∧ the sha cross-check. A consumer that wants to splice
the commit `{message}` into a prompt template can run the same injection leg over it — the
machinery is shared — but that is the consumer's policy, not this fact.

Refusals proven: a tampered session (`BadNotarySignature`), a response for a **different
sha** than requested (`ShaMismatch`), a malformed body (no CFG certificate), a wrong-server
pin.

### Price — `GET api.coinbase.com/v2/prices/{asset}/spot` (`endpoints::price`)

Public, no auth. `verify_coinbase_spot` yields an `AttestedPrice { asset, amount, time,
attestation }`: `{asset}` (from the authenticated target, cross-checked against the body's
`base-currency`) quoted at `{amount}` (from the authenticated body, a decimal string — no
float rounding) at `{time}` (the authenticated TLS session time; Coinbase spot returns no
body timestamp, so the quote time is the moment the session happened — notary-signed).

**The `PriceOracle` interface — the contract for the auditable-fund lane.** The downstream
consumer depends on the trait `PriceOracle { fn price(asset) -> AttestedPrice }`, not on the
prover internals, and can re-verify the carried attestation with `verify_coinbase_spot` to
trust the amount trustlessly. `CoinbaseSpotOracle` is the fixture-backed
implementation; behind `tlsn-live`, `prove_coinbase_live` / `verify_coinbase_live` run
the same interface against the live `api.coinbase.com` over genuine MPC-TLS.

Refusals proven: a tampered amount (`BadNotarySignature` — a wrong price cannot be
attested), a response for a **different asset** than requested (`AssetMismatch`), an unknown
asset (interface-level).

## What is REAL vs the live-endpoint operational remainder

The honest boundary, endpoint by endpoint:

- **REAL, default (light) build:** the CFG parse-certificate prover+verifier over genuine
  JSON, the injection matcher, the authentic-leg adapter (server/notary pinning +
  presentation signature + spec-driven redaction), the cross-leg weld, and — per endpoint —
  the request/response cross-check and typed fact extraction. All exercised end-to-end over
  a fixture presentation (the modeled tlsn notary + a realistic transcript), verifying
  through the real `verify_zkoracle`; forgeries refuted.
- **REAL behind `tlsn-live`:** a genuine local MPC-TLS 2PC roundtrip (vendored TLSNotary, a
  real Notary + Prover, `presentation.verify()`) against an endpoint-shaped test HTTPS
  server, endpoint-parameterized (`LiveExchange::{messages, github_commit, coinbase_spot}`):
  method + path + optional secret header + response body. The authenticated body drives the
  CFG + fact legs; a tampered presentation fails the real `verify()`. The local server
  presents the `tlsn-server-fixture` cert (`test-server.io`), so the pin there is that
  domain.
- **REAL behind `tlsn-live`, LIVE HOSTS:** genuine MPC-TLS 2PC against the live
  `api.coinbase.com:443` and `api.github.com:443` (`tlsn_live.rs`, the real-host path): a
  real `TcpStream` to the real host, the Mozilla/webpki root store (the genuine cert chain
  verifies; the SNI pins the real domain), and a SEPARATE hosted notary reached over a real
  socket, whose verifying key the verifier pins out-of-band and which persists to a durable
  trust root (`notary_server::load_or_generate_notary_key`, `zkoracle-prove/tests/notary_durable_key.rs`).
  The packaged pairs are `endpoints::price::{prove_coinbase_live, verify_coinbase_live}`
  and `endpoints::github::{prove_github_live, verify_github_live}`;
  `examples/coinbase_live.rs` is the portable-proof demo (prove against the live host →
  write the proof file → re-verify from the file, trusting only the host pin + the
  published notary key); `tlsn_live::run_url_roundtrip_blocking` covers any
  `GET https://{host}{path}`.
- **Operational remainder (a deploy step, NAMED, not built):** two pieces. The live authed
  `api.anthropic.com` session — a real key + the secret-header redaction against the live
  host (`ZKORACLE-PROVER-STATUS.md`); the public endpoints above carry no secret, so this
  leg is exercised only fixture/local so far. And an independently DEPLOYED public notary —
  today the separate notary party is hosted by the prover's operator
  (`notary_server::spawn_hosted_notary`) with a durable pinnable key, not run by a third
  party.

## Test map

- Default build (`cargo test -p dregg-zkoracle-prove`): the Anthropic suite (no regression),
  `endpoints::github::tests::*`, `endpoints::price::tests::*` — each endpoint verifies and
  every forgery/mismatch is refused, all through the real verifier.
- `--features tlsn-live` (`deco-prove/tests/tlsn_live_roundtrip.rs`): the real local MPC-TLS roundtrip
  for Anthropic, GitHub, and Coinbase — authentic body → CFG cert → fact, tamper refused.
  The durable notary trust root is exercised hermetically in `zkoracle-prove/tests/notary_durable_key.rs`.
- Live-host runs (need network): `cargo run -p dregg-zkoracle-prove --example coinbase_live
  --features tlsn-live` (prove against the real host, re-verify the portable proof file);
  `coinbase_inproc` is the in-process variant.
