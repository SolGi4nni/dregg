# zkOracle — the PROVER — status (honest)

Makes `metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound` LIVE — the Rust
realization that PRODUCES and VERIFIES a zkOracle attestation over an Anthropic
`POST /v1/messages` session, exactly as `deco-prove` made `Crypto/Deco` live. It
generalizes the DECO/tlsn machinery from Stripe to the Anthropic API.

The attestation certifies a request is simultaneously **authentic ∧ well-formed ∧
injection-free** — the three conjuncts of `zkOracle_sound`. It lives in the new
`dregg-zkoracle-prove` crate. Each leg is stated below with its honest status.

## The three legs (all REAL in the default build)

### 1. Authentic — the tlsn/MPC-TLS (DECO/zkTLS) attestation (`authentic.rs`)

`zkOracle_sound`'s **authentic** conjunct (`∃ w, DecoRelation … decoStmt w`): a
verified tlsn presentation certifies the disclosed response body came from a genuine TLS
session with the pinned `api.anthropic.com`, with the **`x-api-key` secret REDACTED** —
the killer property: prove what the model returned WITHOUT revealing your Anthropic key.

`verify_anthropic_presentation` enforces, in order: server pinning (`api.anthropic.com`),
notary pinning, the presentation signature (ed25519 — the curve deco-prove already uses;
tlsn's real notary uses secp256k1/p256, a notary-config detail), and the api-key
redaction (the secret must NOT appear in the authenticated request bytes). A tampered
disclosed byte breaks the signature; a wrong-server / wrong-notary / leaked-key
presentation is refused. This is the exact shape of `deco-prove/src/tlsn_attest.rs`,
generalized Stripe→Anthropic.

### 2. Well-formed — a JSON CFG parse certificate (`cfg.rs`)

`zkOracle_sound`'s **well-formed** conjunct (`body ∈ jsonGrammar.language`): a
`producesChain`-shaped derivation certificate over the response JSON body, matching
`Crypto/Cfg.lean` one-for-one (`Symbol`/`Rule`/`producesChain`/`CfgAccepts`). Unlike
`Cfg.lean`'s hand-written 5-token demo grammar, this is a **real JSON grammar** (objects
with members, arrays with elements, strings/numbers/booleans/null, nesting through
`Value`) plus a recursive-descent parser that emits the leftmost derivation certificate
over any standard JSON body — e.g. an actual Anthropic messages response.

`prove_cfg_cert(body)` lexes + parses + emits the certificate; a **malformed body yields
none**. `verify_cfg_cert(cert, body)` **re-tokenizes the body itself** (so the certificate
is checked against the authenticated bytes, not the prover's word) and checks `CfgAccepts`:
non-empty chain, head `[N(Value)]`, tail `body.tokens.map(terminal)`, and every step a
valid single-rule `Produces`. Arbitrary-depth nesting is the canonical NON-regular property
the DFA cascade provably cannot certify — the CFG layer is doing real work.

### 3. Injection-free — the `neg`-complement handlebars matcher (`injection.rs`)

`zkOracle_sound`'s **injection-free** conjunct
(`InjectionFree field := derives field (.neg injectionTemplate) = true`): the user field
UNMATCHES the injection template `.* {{ .*` ("contains the handlebars delimiter `{{`"),
stated directly as a match against the **native verified complement** `neg` — dregg's
boolean-closed derivative matcher, the Rust `dregg_dfa::Re::not()` (the `Neg` arm of the
Brzozowski derivative, `dfa/src/derivative.rs`, the Rust side of `Crypto/Deriv`). No regex
engine without a verified complement can state this.

The catch genuinely DISCRIMINATES, matching the Lean `#eval` pair: the benign field
`"hi"` matches `neg template` → accepted; the malicious field `"{{x"` does not → rejected.

## Composition (`attestation.rs`)

`verify_zkoracle` is the Rust realization of the `zkOracle_sound` composition:
ACCEPT iff all three legs verify; any leg failing → REFUSE (the failing leg named). The
well-formed leg's certificate is checked against the **authenticated response body** the
authentic leg extracts — binding well-formedness to a genuine session, not an arbitrary
blob. `prove_zkoracle` refuses to even PRODUCE an attestation for an injecting user
field (the guard cannot mint an attestation for an injecting request — the operational
mirror of `Demo.malicious_not_injection_free`).

## The cross-leg weld — ONE committed response, not three independent objects

Verifying the three legs is not enough on its own: they must be about the **same request**.
The adversarial audit found that pre-weld the legs referenced independent objects — the
well-formed leg was already bound to the authenticated body (it re-tokenizes it), but the
**injection-free leg ran over a free-standing `user_field`** unrelated to the session. So a
splice — an authentic + well-formed session whose real content INJECTS, certified
"injection-free" by supplying a benign standalone field — was accepted.

The weld threads **ONE shared Poseidon2 content commitment** across the three legs
(`content_commitment` = `dregg_circuit::poseidon2::hash_bytes` over the authenticated
response body, the SAME sponge primitive the content-root uses):

- **authentic** yields the response body; `verify_zkoracle` recomputes the commitment
  and refuses any attestation whose committed value disagrees (`CrossLegMismatch`);
- **well-formed** checks its certificate against that same authenticated body;
- **injection-free** runs over a committed SUBSTRING of that same authenticated body — the
  field is a `FieldSpan` the verifier extracts ITSELF (`prove_zkoracle` refuses a field
  that is not a substring of the authenticated response, `FieldNotInResponse`), NOT a
  free-standing input a splicer could swap.

So the attestation now proves authentic ∧ well-formed ∧ injection-free about the SAME
committed response. A spliced attestation (evidence about body A stapled onto an authentic
session for body B) is REFUSED — the `cross_leg_splice_is_refused` /
`unbound_injection_field_splice_now_refused` tests confirm the regression direction
(accepted pre-weld → refused post-weld). This is the 3-way analogue of the DECO
body-binding closed in `bridge/src/stripe_deco.rs` (the felt-commitment `payment_hash`).

### ⚑ The Lean-side weld is the coordinated follow-up (Alif's work)

This is the **Rust-side** weld: the prover realization now proves one-request. The Lean
`metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound` still states the three legs
over **independent objects** (`decoStmt`, `body`, `field`). Closing that — a
shared-commitment hypothesis binding `decoStmt.facts` ↔ `body` ↔ `field` to one committed
response, mirroring this `content_commitment` — is the coordinated Lean-side follow-up (Alif's
lane). It is NOT edited here.

## What is REAL vs the operational remainder

- **REAL (default build, `cargo test -p dregg-zkoracle-prove`, 21 tests green):** the
  CFG parse-certificate prover+verifier over genuine JSON, the injection-free
  `neg`-complement matcher (dregg-dfa's verified derivative `Re`), the authentic-leg tlsn
  adapter (server/notary pinning + presentation-signature + api-key redaction), and their
  composition. A full attestation ACCEPTS; a forged/tampered presentation, a malformed
  body, and a `{{`-bearing field each independently REFUSE; the injection catch
  discriminates. All through the REAL `verify_zkoracle`, not a mock.

- **REAL behind `tlsn-live`** (`--features tlsn-live --test tlsn_live_roundtrip`, PASSES,
  ~1.3 s after build): a genuine local MPC-TLS 2PC roundtrip against an Anthropic-shaped
  HTTPS endpoint — vendored TLSNotary @ `v0.1.0-alpha.15` (the SAME rev deco-prove pins),
  a real Notary + Prover, the 2PC handshake (the Notary co-derives session keys and sees
  no plaintext), a `POST /v1/messages` with the `x-api-key` header selectively hidden, a
  signed `Attestation`, a real `Presentation`, and `presentation.verify()`. The
  authenticated response body drives the CFG + injection legs. A tampered presentation
  fails the real `verify()`; server pinning refuses a non-pinned host. This is
  `deco-prove/src/tlsn_live.rs` generalized `GET`→`POST`, `Authorization`→`x-api-key`, and
  the response shaped as an Anthropic messages object. The heavy `mpz`/tokio/rustls
  backend is a build feature so the default build stays light (the sanctioned use of a
  feature — an optional heavy crypto backend, not a runtime toggle).

- **Operational remainder (NAMED, not built):** pointing the Prover at the live
  `api.anthropic.com` — a real Anthropic TLS session with a real merchant key and a
  deployed/pinned notary. The `tlsn-live` machinery is exactly that path with the server
  swapped: the local test server presents the `tlsn-server-fixture` cert (`test-server.io`),
  so the server pin there is that domain; live-Anthropic pins `api.anthropic.com`. The 2PC
  session-integrity that makes the notary signature *trustless* is exercised locally; a
  deployed notary + a live session is a deploy step, not new crypto.

## The compact certificate — O(tokens) wire, long-context scale

The attestation's well-formed leg carries a **compact certificate**
(`cfg.rs::CompactCert`): the leftmost derivation's RULE SEQUENCE (one byte per step),
replayed by `verify_cfg_compact` as a pushdown run — O(tokens) time and space, fully
iterative on both prove and verify (no recursion: 100k-deep and 10M-token bodies are
heap-bounded). The Lean side is `Dregg2/Crypto/CfgCompact.lean` (`#assert_axioms`-clean):
`Replay` is the machine, `compact_sound` proves an accepted replay implies language
membership, and `compact_to_chain` rebuilds the `CfgAccepts` chain object — the wire
format changed, the theorem the capstone consumes did not. `expand_compact` is
`compact_to_chain`'s Rust twin, and `compact_expands_to_the_exact_chain` pins the two
provers to the identical leftmost derivation.

The original form-chain (`ParseCertificate`, `Cfg.lean::chain`-shaped) remains as the
small-input spec bridge. It is O(tokens²) symbols and its recursive prover is
stack-bounded near 65k dense tokens — measured below; it is not the scale path.

## Measured paces (2026-07-06, Apple Silicon dev box, release build)

`cargo run -p dregg-zkoracle-prove --example paces --release` — per-leg + end-to-end,
median-of-k. Axes: TEXT (bytes grow; a JSON string lexes to ONE token), TRANSCRIPT (a
long multi-turn context of ~26-LLM-token content blocks — ≈256k / 1M / 10M LLM tokens at
~4 bytes each), DENSE (pure JSON-token growth, the certificate's stress axis), DEEP
(nesting, the stack-safety pole).

| case | bytes | jtokens | cert bytes | cert prove | cert verify | commit | PROVE e2e | VERIFY e2e |
|---|---|---|---|---|---|---|---|---|
| text-1k (single response) | 1.2k | 51 | 43 | 1 µs | 2 µs | 274 µs | **318 µs** | **314 µs** |
| text-256k | 262k | 51 | 43 | 189 µs | 197 µs | 56.6 ms | 56.6 ms | 56.5 ms |
| **ctx-256k-LLM-tok** | 990k | 100k | 90k | 1.04 ms | 993 µs | 214 ms | **216 ms** | **215 ms** |
| **ctx-1M-LLM-tok** | 4.0M | 400k | 360k | 4.1 ms | 4.0 ms | 849 ms | 863 ms | 852 ms |
| **ctx-10M-LLM-tok** | 39.6M | 4.0M | 3.6M | 40 ms | 39 ms | 8.5 s | 8.6 s | 8.7 s |
| dense-1M | 2.1M | 2.1M | 2.1M | 12.7 ms | 12.5 ms | 458 ms | 473 ms | 471 ms |
| dense-10.5M | 21M | 21M | 21M | 130 ms | 130 ms | 4.6 s | 4.7 s | 4.8 s |
| deep-100k | 200k | 200k | 300k | 1.6 ms | 1.2 ms | 43 ms | 45 ms | 46 ms |

Old form-chain contrast (why the compact form is the wire): dense-16.4k → 537M symbols,
~640 ms each way; dense-32.8k → **2.15G symbols, ~2.2–2.5 s**; ~65k → its recursive
prover overflows the thread stack. The same dense-16.4k on the compact path: 33 kB cert,
~200 µs each way.

Refuse paths (hostiles bounce FAST, before any heavy leg): forged notary sig **33 µs** ·
cross-leg splice **35 µs** · injection match alone **12 µs**. The live local MPC-TLS 2PC
roundtrip (`tlsn-live` test) completes in **~0.4 s** warm.

Readings:
- **A single model response attests in ~320 µs each way**; a **256k-LLM-token context in
  ~215 ms**, **1M in ~0.9 s**, **10M in ~8.6 s** — at every long-context size both
  directions are dominated by the linear Poseidon2 `content_commitment` (~215 µs/KiB);
  certificate prove/verify never exceeds ~130 ms even at 21M JSON tokens.
- The certificate scaling wall is CLOSED (was: O(tokens²) form-chain, quadratic time +
  GB-scale allocation + a stack-overflow near 65k dense tokens). The remaining scale
  frontier at 10M-token contexts is the sequential Poseidon2 sponge itself; if ~9 s
  matters for that tier, the lane is a chunked/Merkle content commitment (parallelizable)
  — a commitment-shape decision that touches the weld, not certificate machinery.

## 🏆 The CROWN — the confined brain's turn, ATTESTED (`deos-hermes`)

The prover above PRODUCES an attestation over a `/v1/messages` session. The crown WELDS
that into the confined brain: a jailed LLM turn now yields BOTH the jail-confinement
evidence AND a zkOracle attestation of the model's reasoning. `deos-hermes` — where a
brain runs INSIDE a firmament OS-jail (file/exec/network denied) and its model-provider
call rides EXACTLY the granted egress socket door (`egress.rs` / `host.rs`) — now depends
on `dregg-zkoracle-prove` and attests each turn.

- **`deos-hermes/src/attest.rs` (NEW) — `AttestationCarrier`.** `attest_turn(agent_text)`
  shapes the confined brain's OWN turn output into an Anthropic messages response body and
  binds that text injection-free, then calls `prove_zkoracle` → a `ZkOracleAttestation`
  proving the turn was authentic (the session) ∧ well-formed (the response JSON CFG cert)
  ∧ injection-free (no `{{` in the model's words, a committed substring of the response).
  `clean_field` keeps the `{` / `}` bytes so a genuine injection attempt in the model's
  output still fires the leg (the catch is preserved, not sanitized away).

- **`deos-hermes/src/host.rs` — `DreggHost::run_hosted_agent_attested(...)`.** The SAME
  jailed run that proves confinement (`run_hosted_agent_net`: jailed + provider door open +
  sibling denied), then attaches the attestation to the run's `HostedAgentReport` (new
  `attestation: Option<ZkOracleAttestation>` field). One run → both proofs.

- **Real-locally (default, light): the modeled authentic carrier.** The default path uses
  the crate's modeled ed25519 authentic adapter over the exact response bytes + the REAL
  JSON CFG cert + the REAL verified injection matcher — no HTTP/TLS. It proves the whole
  PRODUCE→VERIFY plumbing hermetically.

- **Real-locally (`zk-live`): a genuine local MPC-TLS 2PC roundtrip.**
  `deos-hermes/src/attest.rs::attest_turn_live` (feature `zk-live` → the crate's `tlsn-live`)
  drives the real local 2PC roundtrip (server + notary + prover in-process; the notary sees
  no plaintext; a real `presentation.verify()`) and attests over the body that roundtrip
  AUTHENTICATED — so the certified bytes came from a real 2PC session, not a fixture
  literal. Heavy `mpz`/tokio/rustls backend behind the feature; the default stays light.

- **The crown test (`deos-hermes/tests/crown_attested_turn.rs`, 2 tests green):**
  `jailed_turn_is_also_attested` — a jailed brain run over the granted provider door
  produces an attestation `verify_zkoracle` ACCEPTS, WHILE the confinement teeth hold
  (jailed, base tools neutralized, granted socket open, sibling denied, tool-calls still
  receipted). `hostile_turns_are_refused_each_on_its_leg` — a tampered session →
  `NotAuthentic`, a malformed response → `NotWellFormed`, an injecting turn → `Injection`.
  Plus 5 `attest.rs` unit tests. So the green is load-bearing: a real turn is certified.

### Honest boundaries of the crown

- The attestation's **authentic *leg*** is still the modeled ed25519 carrier over the
  response bytes, even in `zk-live` (where the bytes ARE really-authenticated by the 2PC
  roundtrip run in the same call). **Fusing the real tlsn `PresentationOutput` into the
  authentic leg** — so the leg IS the MPC-TLS presentation, not the modeled carrier — is
  part of the operational remainder, alongside the live `api.anthropic.com` session.

- **Binding the attestation into the agent's R2 kernel turn** — so the receipt-on-the-ledger
  carries the zkOracle proof — is the natural next weld, but it touches `agent-platform`
  (a hot shared tree) and is **NOT wired here**. This lane proves the confined brain
  PRODUCES a verifiable attestation of its turn; carrying it onto the ledger is the named
  follow-up.

## Trust base

Per-leg: the tlsn/MPC-TLS soundness + the notary signature scheme (authentic), the JSON
grammar as a transparent denotational spec (well-formed), and dregg's verified `neg`
complement (injection-free) — plus the external Web-PKI / honest-Anthropic floor. These
are exactly the carriers `zkOracle_sound` names (the two STARK `extractable` carriers +
the §8 crypto floor + the external Web-PKI floor).

## Crates touched

- `zkoracle-prove/` (NEW): the 3-leg prover+verifier + the cross-leg weld + the real
  tlsn-live lane + tests.
- `Cargo.toml`: added `zkoracle-prove` to workspace members + default-members.
- `zkoracle-prove/Cargo.toml`: added `dregg-circuit` (path) for the Poseidon2 sponge
  (`hash_bytes`, the shared content commitment) — a workspace path dep, not a new external
  crate.
- `deos-hermes/` (the CROWN weld): `src/attest.rs` (NEW — `AttestationCarrier`,
  `attest_turn`, `attest_turn_live`), `src/host.rs` (`run_hosted_agent_attested` +
  `HostedAgentReport::attestation`), `src/lib.rs` (re-exports), `tests/crown_attested_turn.rs`
  (NEW). `deos-hermes/Cargo.toml`: added `dregg-zkoracle-prove` (path, default-light) +
  the `zk-live` feature (→ `dregg-zkoracle-prove/tlsn-live`). No `agent-platform` edit
  (the R2-turn binding is the named follow-up).

No Lean sources, no gentian/assurance/`orb` files, no lease files, and nothing in `_attic`
were changed. The default build depends on `dregg-dfa` + `dregg-circuit` (for the Poseidon2
content commitment) + `ed25519-dalek` + `sha2`; the heavy tlsn backend is behind the
`tlsn-live` feature.
