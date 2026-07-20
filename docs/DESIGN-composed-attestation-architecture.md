# Composed Attestation Architecture — one substrate, four rungs, an efficiency dial

How the regular/DFA layer, the visibly-pushdown layer, and the CFG/graph-rewrite layer
compose on **one certificate substrate**. Originally written (2026-07-16) as a proposal;
the substrate, the linchpin, and the parse-as-derivation circuit are now **built and
committed**. This doc describes what exists, with `file:line` anchors, and marks what
remains proposed.

> **Status correction (2026-07-19).** Sections 5 and “Honest limits” predate the symbolic
> derivative closure.  Flat `PredRE` emptiness and language equivalence over the infinite `Value`
> alphabet are now decidable and runnable on the registered symbolic fragment
> (`SymbolicMinterms` → `SymbolicFixpoint` → `EquivalenceFixpoint`, widened by
> `SymbolicMintermsPlus`).  What remains proposed is the *visibly-pushdown* symbolic lift and the
> deployed heterogeneous-circuit composition, not infinite-alphabet regular equivalence itself.

## 1. The substrate — `Cert R` for ANY relation (BUILT)

`metatheory/Dregg2/Crypto/Chain.lean` is the **leaf module** (Mathlib + `Dregg2.Tactics`
only) carrying the relation-parametric certificate every instance rides on:

- `chain R c` (`Chain.lean:35`) — every consecutive pair of `c` is one `R`-step;
- `Cert R start goal c` (`Chain.lean:42`) — a non-empty chain with pinned endpoints;
- `bridge R : (∃ c, Cert R start goal c) ↔ ReflTransGen R start goal` (`Chain.lean:84`);
- `Cert.map` (`Chain.lean:111`) — certificates are functorial along relation-preserving maps;
- `Cert.foldSound` (`Chain.lean:125`) — the generic "walk the chain, accumulate output,
  carry a semantic invariant" induction (see §4).

`Crypto/Hypergraph.lean` sits above it (imports `Chain`, `Hypergraph.lean:21`) with the
generic instances: `hypergraph_reduction_bridge` (`:60`, hyperedge replacement) and
`cfg_parse_via_reduction` (`:69`, `R := g.Produces` ⇒ grammar membership; `Cfg.cfg_bridge`
is literally an alias of it, not a second induction). `GraphRewrite.lean::graphRewrite_bridge`
is the match-driven contextual-replacement instance. All declarations live in the
`Dregg2.Crypto.Hypergraph` namespace, so
downstream references are unchanged.

## 2. The four rungs — one `Hypergraph.bridge`, four relations (BUILT)

The design's linchpin — "re-express `DfaAccepts` as `Hypergraph.Cert δ`" — is landed, and
the ladder grew two rungs beyond it:

| Rung | Relation `R` | File | Keystone |
|---|---|---|---|
| REGULAR (DFA) | `delta` (`DfaAsCert.lean:55`) — stackless step chaining | `Crypto/DfaAsCert.lean` | `dfaAccepts_as_cert` (`:76`) |
| VISIBLY-PUSHDOWN (VPA) | `R_vpa` (`VpaAsCert.lean:138`) — class-driven stack action | `Crypto/VpaAsCert.lean` | `vpaAccepts_as_cert` (`:183`) |
| CONTEXT-FREE grammar | `g.Produces` | `Crypto/Hypergraph.lean` | `cfg_parse_via_reduction` (`:69`) |
| CONTEXT-FREE machine | `ReplayStep g` (`ReplayAsCert.lean:72`) — one pushdown-replay move | `Crypto/ReplayAsCert.lean` | `replay_as_cert` (`:117`) |

The identifications are definitional where it matters: since the chain-dedup refactor,
`Dfa.chained` (`Dfa.lean:67`) is *defined as* `Hypergraph.chain (fun a b => b.state = a.next)`,
so `chained_iff_chain` (`DfaAsCert.lean:62`) is `Iff.rfl`. Acceptance = the `Cert` conjunct
plus machine-specific boundary/validity side-conditions (initial state, accepting state,
per-step `δ`-validity) riding alongside, the same way CFG's start-symbol/goal-word are its
`Cert`'s fixed endpoints.

The unification is stated as a theorem, not a slogan:

- `regular_and_cf_share_substrate` (`DfaAsCert.lean:123`) — DFA and CFG acceptance are the
  same `Hypergraph.bridge` at two relations, side by side;
- `three_rungs_share_substrate` (`VpaAsCert.lean:228`) — regular ⊗ visibly-pushdown ⊗
  context-free, one bridge, three relations, with the VPL rung slotted between.

All rungs are `#assert_axioms`-clean with concrete non-vacuity runs (the `a⁺b` DFA's `"aab"`
trace through the `Cert` form, the bracket-chain VPA, the bracket-pair replay).

## 3. The parse-as-derivation circuit — COMPLETE and UNCONDITIONAL (BUILT)

The CF rung is not only metatheory: the Dyck pushdown-parse circuit is deployed and its
soundness chain is unconditional, keyed on the byte-pinned descriptor the loader serves.

- **Circuit**: `circuit/src/dsl/dyck_stack.rs` — `dyck_parse_descriptor` (`:540`),
  `dyck_parse_circuit` (`:848`), the honest witness builder (`build_nested_witness`, `:917`),
  and the IR-v2 lift (`lift_witness_to_v2`, `:1139`) onto the Lean-emitted descriptor. A
  trace satisfying the descriptor IS an accepting leftmost pushdown replay.
- **Lean authoring + byte pin**: `metatheory/Dregg2/Circuit/Emit/DyckStackEmit.lean` —
  `dyckParseDesc` (`:446`) with a `#guard` byte-pinning its exact wire form (`:461`); any
  drift on either side breaks the Lean `#guard` or the on-disk drift gate.
- **The loader LOADS it**: `circuit/src/descriptor_by_name.rs:151` registers
  `dregg-dyck-parse-v1` → the Lean-emitted golden (`DYCK_PARSE_JSON`, `:274`,
  `include_str!` of `descriptors/by-name/dyck-parse.json`); the loader-flip test (`:508`)
  checks the deployed dispatch serves the emitted, byte-pinned shape. Prove-path teeth:
  `circuit-prove/tests/dyck_parse_tamper.rs`.
- **Refinement + capstone**: `Circuit/Emit/DyckStackRefine.lean` (row-level refinement) and
  `Circuit/Emit/DyckStackReplay.lean`, culminating in
  `parse_sat_imp_replay_emit_unconditional` (`DyckStackReplay.lean:934`): a trace satisfying
  the deployed, emit-authored descriptor has its **read-off** word (`decodedWord`, defined
  *from the trace*) accepted by the Dyck replay — no tape↔word hypothesis anywhere. Fired on
  the shipped witness by `witTrace_replays_unconditional` (`:954`) with every hypothesis
  discharged by computation.

## 4. `Cert.foldSound` — the multi-month induction, subsumed and paying forward (BUILT)

The design named one hard multi-row induction: "forward trace of per-row-valid pushdown
steps ⇒ backward `Replay`, certificate reconstructed by `rulesOf`". That induction exists
(`AbstractMachine.lean:122`, `mrun_imp_replay`; the machine layer was extracted down from
the circuit module so Crypto never imports Circuit) — and the generic `Cert.foldSound`
**subsumes** it:

- `mrun_imp_replay_via_fold` (`ReplayAsCert.lean:216`) re-derives the identical statement as
  one `Cert.foldSound` application: the bespoke content splits into `mrun_cert` (`:200`, the
  run IS a chain certificate over `MStep`) + `mstep_step` (`:172`, one local step prepends
  soundly), and the fold supplies the whole assembly. `subsumption_stmt_eq` (`:233`)
  elaborates only because the statement types coincide.
- `Crypto/CertFoldForward.lean` demonstrates the **forward** direction on a machine the
  substrate never saw (a depth-counter bracket acceptor): two whole-run theorems
  (`run_closes` `:106`, `run_decode` `:114`, composed as `accept_sound` `:121`, plus the
  refusal pole `cl_no_cert` `:164`) each fall out of a single `Cert.foldSound` application —
  no `induction` keyword in the file. Net: ~40 lines of chain-walking induction per future
  machine → ~10 lines of per-step content.

## 5. The VPL rung — honest verdict, and the one real win in progress

Per `docs/DESIGN-visibly-pushdown-reframe.md`: the visibly-pushdown reframe **names** the
templater's `Separated`/`Excludes` class as the visibly-nested boundary — it does **not
dissolve** the uniqueness/inverse wall. VPA determinism yields a unique *run*; unique *data*
recovery still needs the boundary-at-forced-position argument (`split_unique`), whose
precondition — the delimiter is a genuine return symbol, never hole content — IS `Excludes`,
renamed not removed.

What the rung genuinely buys, beyond the substrate slot itself: the root VPL property is
proved — `run_height` (`VpaAsCert.lean:289`) / `stack_height_input_determined` (`:324`), the
stack height at every position is a function of the input word alone — and it opens the one
capability the general-CFG rung provably cannot have: **decidable template
equivalence/inclusion** on the finite visibly-nested fragment (CFL equivalence is
undecidable; VPL equivalence is EXPTIME-decidable, Alur–Madhusudan).

That route is **in progress** in `Crypto/VpaDecidable.lean`:

- PROVED: `Lang` (the nested-word language), **intersection** via the product VPA
  (`prodVpa` `:95`, `prodVpa_lang` `:326`, both directions — the zip direction is the
  constructive face of input-determined stack height), `lang_wellMatched` (`:450`, pinning
  the universe for relative complement), and the pure-logic reduction
  `equiv_iff_symmDiff_empty` (`:488`).
- NAMED, not proved: `ComplementClosure` (`:523`) and the emptiness decision — the latter
  deliberately not stated as a `Prop`, because every Prop-level phrasing found so far is a
  classical tautology; the genuine artifact must be a decision *procedure*.

## 6. Lean-authored witnesses — exported (Lean side BUILT; the bridge is next)

The `renderWithProof` generator lives in Lean and is now **exported**:
`Crypto/HandlebarsFFI.lean` exposes, over the `String → String @[export]` ABI (the
`dregg_grain_r3_verify` precedent):

- `@[export dregg_render_with_proof]` (`HandlebarsFFI.lean:322`) — prover side; runs the
  computable `render`/`renderRules` (`HandlebarsWitness.lean:77`), whose output is proven to
  be the accepting witness for every `safe` input (`renderRules_accepts`,
  `HandlebarsWitness.lean:186`);
- `@[export dregg_replay_check]` (`:335`) — verifier side, backed by `replayCheckB`
  (`:166`), a **computable decider** for the `Prop` `Replay` with `replayCheckB_iff` (`:172`)
  proving it decides `Replay` exactly, on fuel provably equal to the exact step count. Both
  fail closed on malformed wires.

**Still proposed**: the C-bridge registration (`dregg-lean-ffi/src/lean_init.c` +
`lean_string_bridge`) and the Rust/wasm consumer — today no Rust caller invokes these two
exports, so `zkoracle-prove/src/cfg.rs` remains a hand-written twin until the consumer
lands. The marshalling machinery is general and already carries three verdict exports; the
remaining work is wiring, not new machinery.

## 7. The efficiency dial (deployed leaves; composition PROPOSED)

Each `Cert R` compiles to a circuit; use the cheapest that suffices:

- **Regular (δ, stackless) → `dfa_routing`** (`circuit/src/dsl/dfa_routing.rs:126`):
  7 columns, deployed, parametric over an arbitrary transition table; public
  `route_commitment` binds the trace (the Lean `route_commitment_binds_trace` pivot).
- **CF (stack) → the derivation circuit** (`circuit/src/dsl/derivation.rs`, C1–C28) and the
  Dyck pushdown-parse circuit (§3): they pay for stack/unification power a regular token
  never needs. The regular leaf is ~50× narrower by column count — the structural reason to
  push flat recognition down to the DFA circuit and reserve derivation for genuine nesting.
- **CF cites a regular leaf by committed hash** — the derivation row's body↔membership-leaf
  gate (`derivation.rs:153,900`) pointed at a DFA `route_commitment` instead of a Merkle
  leaf. No new primitive; still unassembled (below).

**PROPOSED — fold heterogeneity.** The fold engine
(`circuit-prove/src/ivc_turn_chain.rs::aggregate_tree` `:3752`, via
`merge_two_segment_proofs` `:3687` with in-band per-child VK pins) is circuit-agnostic.
Mixing DFA-leaf + CF-structure proofs under one root still needs: (a) token-span segment
endpoints, (b) a leaf-kind tag, (c) the root VK pin (`verify_turn_chain_recursive` `:3805`)
widened to an enumerated leaf-VK set.

**PROPOSED — grammar generalization.** The deployed parse circuit is the one-bracket Dyck
grammar; the Lean chain (§3) is stated against that grammar's descriptor. Arbitrary-grammar
emission is the generalization axis.

**PROPOSED — the efficiency-dial benchmark.** The ~50× is a column-count estimate, not a
measurement. The meaningful benchmark exercises the dial — plaintext re-check vs DFA-leaf
STARK vs CF-derivation STARK vs the folded composed form — on the deployed FRI config, real
Poseidon2 params, a realistic schema (mostly regular-guard holes, some nesting), measuring
prove/verify/proof-size and the fold's per-leaf recursion cost against the leaf savings.
(Security is a separate axis: see the deployed-FRI-bits reality in
`memory/project-fri-soundness-reality.md`; a fast proof at a weak soundness radius is a
different product.)

## 8. The extension (PROPOSED, unchanged)

`extension/src/netlayer.ts` verifies federation receipt-stream attestations client-side;
`offering-sign.ts` produces Ed25519 attestations; `wasm/src/lib.rs` proves/verifies
predicate/threshold/membership in-browser. Wiring the §6 exports through a wasm-bindgen
`render_with_proof` / `verify_rewrite_cert` would let a browser produce and verify
rewrite-attestations natively. Depends on the §6 bridge landing first.

## Honest limits

- **Infinite data alphabet**: the flat symbolic-regular rung is now built: `PredRE` emptiness and
  equivalence are decidable over the infinite `Value` alphabet on the registered symbolic
  predicate-cover fragment, and the adaptive `Sim` fixpoint runs the checked examples.  The
  remaining boundary is the symbolic **VPA** lift for visibly nested protocols, plus the explicitly
  fail-closed predicate classes not yet supplied with finite witness covers; it is no longer honest
  to call the infinite alphabet categorically “out of VPL scope.”
- **The uniqueness wall is real**: unique data recovery rests on the delimiter-guarded
  class (`Excludes`), not on VPA determinism (§5).
- **The `Value↪Nat` weld** (`Deriv/Determinize.lean:171`) — the faithfulness-carrying
  encoding lemma connecting the verified `Matches`-faithful DFA to the AIR table — remains
  open, as does verified-emitter parametricity for `dfa_routing` (per-DFA today).

**The through-line, as shipped:** distinction = recognition = derivation = rewrite is a
theorem (`three_rungs_share_substrate`), the CF rung runs unconditionally against the
byte-pinned deployed descriptor, and every future machine's whole-run induction is one
`Cert.foldSound` application. The remaining work is composition (fold heterogeneity),
generalization (arbitrary grammars), the FFI bridge, and the measurement.
