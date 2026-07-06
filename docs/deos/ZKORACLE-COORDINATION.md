# zkOracle — coordination notes (Rust prover ⇄ Lean capstone)

Context: the Rust prover realizing `Crypto/ZkOracle.lean::zkOracle_sound` landed
(`zkoracle-prove`, `0ecb97c15`), plus an adversarial audit of the Lean. This records the
**Lean-side follow-ups** the Rust side found, for whoever owns `Crypto/ZkOracle.lean` (Alif).
The Rust side is NOT editing the Lean — these are flagged, not touched.

## The load-bearing one — the cross-leg weld (Lean side)
`zkOracle_sound` proves `authentic(decoStmt) ∧ well-formed(body) ∧ injection-free(field)` for
**three independent objects** — nothing binds `decoStmt.facts`, `body`, and `field` to the SAME
request bytes. The doc discloses this honestly (`ZKORACLE-CFG-HYPERGRAPH.md:98-100`). It is the
3-way analogue of the DECO body-binding gap that was just closed in `bridge/src/stripe_deco.rs`.

- **Rust side (done / in progress):** the prover now threads ONE shared Poseidon2 commitment over the
  authenticated response bytes, and `verify_zkoracle` refuses a cross-leg splice (`CrossLegMismatch`).
- **Lean side (yours):** add the shared-commitment hypothesis to `zkOracle_sound` — bind
  `decoStmt.facts` ↔ `body` ↔ `field` via one Poseidon2 root threaded as a shared witness — so the
  theorem is about one request, matching the Rust realization.

## Two honest toy→real upgrades (Lean side, lower priority, both disclosed in-source)
- `Json.jsonGrammar` (`ZkOracle.lean:126-144`) is a 5-token toy (certifies nested-brackets, does not
  parse real Anthropic JSON). The Rust prover (`zkoracle-prove/src/cfg.rs`) already has a fuller JSON
  grammar (objects/members, arrays, str/num/bool/null) emitting the `producesChain` cert — could be
  ported/mirrored into Lean if a real-JSON membership theorem is wanted.
- `injectionTemplate` (`:53-54`) is a single-sentinel (`{{`) — the `neg`-complement MECHANISM is real and
  proven; the PATTERN is a delimiter-breakout toy (a real "ignore previous instructions" injection has no
  `{{` and evades it). Upgrading the pattern is honest hardening; the verified-complement machinery carries
  whatever pattern you give it.

## What is genuinely real (audit credit)
`zkOracle_sound` is a real composition (2 `verify_sound` derivations + a proven-both-polarities
injection predicate), carriers are honest typeclass Props, `#assert_axioms`-clean, no `sorry`/`axiom`.
The `neg` complement is anchored to `Correctness.lean:267`. The generic bridges (Hypergraph/GraphRewrite)
are clean. Nothing here is a defect — these are the named next builds for a one-request live attestation.
