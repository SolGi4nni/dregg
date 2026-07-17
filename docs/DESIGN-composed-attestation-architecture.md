# Composed Attestation Architecture — one substrate, an efficiency dial, Lean-authored witnesses

How to get a **maximally flexible AND extremely efficient** attestation/witness/proof
setup by composing the regular/DFA layer with the CFG/graph-rewrite layer. Grounded in
three read-only sweeps (2026-07-16); the substrate is ~80% built and the composition is
*unassembled*, not *unbuilt*.

## 1. The unification — one certificate substrate (already exists)

`metatheory/Dregg2/Crypto/Hypergraph.lean` factors out a **relation-parametric certificate**:
`chain R` (`:39`), `Cert R start goal c` (`:46`), and `bridge R : (∃c, Cert R start goal c) ↔
ReflTransGen R start goal` (`:88`) — for ANY relation `R`. It already unifies:
- **CFG** — `cfg_parse_via_reduction` (`:134`, `R := g.Produces`),
- **hyperedge replacement** — `hypergraph_reduction_bridge` (`:125`),
- **DPO graph rewriting** — `GraphRewrite.lean::graphRewrite_bridge` (`:93`, `R := RewriteStep`).

**A DFA run is exactly `chain` over the transition relation δ, and `Dfa.lean::dfa_bridge`
(`:142`) is exactly `Hypergraph.bridge` specialized** — but `Dfa.lean` does not import
`Hypergraph` and is not expressed as `Cert δ`.

**THE LINCHPIN LEMMA (the whole architecture's keystone): re-express `Dfa.DfaAccepts`
(`Dfa.lean:73`) as an instance of `Hypergraph.Cert δ` / `Hypergraph.bridge`.** Then regular
recognition and CF derivation — and hyperedge replacement, and DPO rewriting — are provably
the *same certificate object*, differing only in the relation `R` (δ vs `Produces` vs
`RewriteStep`). One lemma makes "distinction = recognition = derivation = rewrite" a formal
fact, not a slogan. Everything below builds on it.

## 2. The efficiency dial — cheapest circuit per certificate

Each `Cert R` compiles to a circuit; use the cheapest that suffices:
- **Regular (δ, stackless) → `dfa_routing` STARK** (`circuit/src/dsl/dfa_routing.rs:126`):
  **7 columns, degree ≤ 6, deployed and already parametric** over an arbitrary transition
  table (`TableFunction` interpolation). A token — e.g. a hole's no-brace data — is a linear
  DFA scan: no stack, no substitution, no bit-decomposition.
- **CF (Produces, stack) → the derivation circuit** (`circuit/src/dsl/derivation.rs`, C1–C28,
  stack-extended per `docs/DESIGN-parse-as-derivation.md`): **371–384 columns, degree 8** —
  it pays for general Horn-rule power (unification, membership, 30-bit comparisons) a regular
  token never needs.
- **Quantified: the regular leaf is ~50× narrower** (7 vs 371). That is the concrete reason to
  push flat/leaf recognition down to the DFA circuit and reserve the derivation circuit for
  genuine nesting.

**CF cites a regular leaf by committed hash — no new primitive.** The derivation row already
binds a body atom to "a committed hash proven elsewhere" (the body↔membership-leaf gate,
`derivation.rs:153,900`). The DFA circuit already exposes exactly such a commitment for a
recognized span (`dfa_routing.rs:52` `route_commitment`, the Lean
`route_commitment_binds_trace` pivot). So a CF row carries a leaf field "this terminal-span's
DFA `route_commitment = C`", the cheap `dfa_routing` proof attests `C` for that span, and the
CF proof cites `C` as a committed side-condition — **the same committed-hash gate, pointed at
a DFA route commitment instead of a Merkle leaf.** A sub-proof cited by hash, not a lookup.

**The fold composes a mix of leaf kinds into one root.** `ivc_turn_chain.rs::aggregate_tree`
(`:3643`) folds via `merge_two_segment_proofs` on each child's exposed segment claim + an
in-band per-child VK pin — the combine is *circuit-agnostic* (it does not require both children
to be the same circuit). Delta to mix DFA-leaf + CF-structure proofs: (a) redefine segment
endpoints as **token-span offsets** (so a DFA leaf over `[i,j)` and a CF leaf over `[0,n)`
compose by continuity), (b) add a **leaf-kind tag**, (c) widen the root VK pin
(`verify_turn_chain_recursive:3696`) to admit an **enumerated set** of leaf VKs. The engine,
segment algebra, and VK-pinning are already generic.

## 3. Lean-authored witnesses, exported to Rust/wasm

Today trace/witness generation is **hand-rolled Rust** (`circuit/src/*_witness.rs`,
`effect_vm/trace.rs`; the CFG-cert twin `zkoracle-prove/src/cfg.rs` is hand-written, JSON-only,
not wasm-exposed) — the last dual-authoring gap the census warned about. The
`renderWithProof`/`Cert` *generator* now lives in Lean (`HandlebarsWitness.renderRules`, proven
by `renderRules_accepts`) but is **not exported**.

The export machinery is fully general and already carries non-crypto *verdicts*
(`dregg_grain_r3_verify`, `dregg_holding_grant_weight`, `dregg_blocklace_finalize`): the
`String→String @[export]` ABI + the `dregg-lean-ffi/src/lean_init.c` C-bridge + the
`lean_string_bridge` grow-and-retry marshaller (`dregg-lean-ffi/src/lib.rs:1031`) + the
`OnceLock<Fn>` install seam (`dregg-pq/src/mldsa.rs`). **A `renderWithProof`-style witness
generator returning a serialized `(output, ruleSeq)` fits the same ABI with no new machinery.**
Missing: (i) an `@[export]` on a serializing wrapper + an executable `Bool` `replayCheck`
(today `Replay` is a `Prop`), (ii) a Rust/wasm consumer. Then Rust and wasm *call the
Lean-authored witness* instead of reimplementing it — the ML-KEM pattern, applied to witnesses.

## 4. The extension participates in networks

`extension/src/netlayer.ts` already verifies federation receipt-stream attestations client-side
(4-gate fail-closed); `offering-sign.ts` already produces Ed25519 attestations. The extension
loads the full 50 MB proving wasm (`background.ts:238`) but calls only 4 trivial functions.
`wasm/src/lib.rs` can already prove/verify predicate/threshold/membership in-browser — but has
**no CFG/DFA recognizer or render-with-proof**. Wire the (3)-exported witness + a wasm-bindgen
`render_with_proof` / `verify_rewrite_cert` into the extension → a **browser produces and
verifies rewrite-attestations natively**, and networks of them form. Every render a receipt,
in the browser, on the witness the kernel trusts.

## First slice (highest leverage) + honest gaps

**First slice: the linchpin lemma** — `Dfa.DfaAccepts` as `Hypergraph.Cert δ`. Small, isolated,
and it unifies the entire grammar/rewrite/recognition stack onto one certificate object; the
efficiency dial, circuit embedding, witness export, and extension all build on it.

Localized gaps (each named, none blocking a capability):
- **The `Value↪Nat` weld** — one faithfulness-carrying encoding lemma closes both the
  powerset-table-equality gap (`Deriv/Determinize.lean:171`) and the compiler-table↔AIR-table
  gap, connecting the verified `Matches`-faithful DFA to the cryptographically-bound AIR table.
- **Verified-emitter parametricity** — the deployed Rust `dfa_routing` is generic, but no Lean
  proof yet says "arbitrary table ⇒ interpolant = step" (verified emitters are per-DFA today).
- **Witness export** — the `@[export]` + `Bool replayCheck` + Rust/wasm consumer.
- **Fold heterogeneity** — token-span segment endpoints + leaf-kind tag + multi-VK root
  admission.

## Performance — the named post-convergence deliverable

The efficiency claims here are **estimates from column counts and structure, not measured**.
Before this is called production-ready, benchmark a realistic/production-like schema on the
deployed config — because the numbers are *entirely layer-dependent* and the two that matter
most do not exist yet:

- **What exists now** (plaintext `CompactCert` / per-hole `derives` re-check): verify is O(tokens),
  the "receipt" is derivation-sized — cheap to check, but **not succinct**. Measuring *this* would
  give a profile that does not reflect the intended product.
- **What determines the real story** (unbuilt — the parse-as-derivation circuit): STARK prove
  (expensive, ~seconds), STARK verify (fast, ~ms), proof size (succinct, ~KB). The perf question
  is meaningful only *after the zk-succinct path lands*, which is exactly why "after it converges."

The benchmark must **exercise the efficiency dial**, or it proves nothing: a realistic schema is
mostly simple regular-guard holes (cheap DFA leaves) with *some* nested/CF structure. Measure
prove/verify/proof-size across the layers — plaintext re-check vs DFA-leaf STARK vs CF-derivation
STARK vs the *folded composed* form — on the deployed FRI config (`ir2_config`, `log_blowup=6`),
real Poseidon2 params, real prover hardware, over a realistic document size + hole count + guard
(regex→DFA) complexity. The headline number to confirm-or-refute: **does pushing regular leaves to
the 7-column DFA circuit and reserving the 371-column derivation circuit for genuine nesting
actually buy the ~50× on a real workload** — and how the fold's per-leaf recursion cost trades
against it. (Security is a *separate* axis with its own asterisk — see the deployed-FRI-bits
reality; a fast proof at a weak soundness radius is not the same product.)

**The through-line, as engineering:** distinction = recognition = derivation = rewrite — one
certificate substrate (`Cert R`), an efficiency dial across circuits (cheap regular leaves, CF
structure, folded to one root), Lean-authored witnesses exported to Rust/wasm, the browser
participating. The philosophy made into an architecture.
