# pickles-poseidon-harness — the R4a-scaled PROVE + VERIFY + BIND test on a REAL Poseidon circuit

This standalone crate scales the **R4a** milestone (`pickles-r4-harness`, a toy `p = a·b` circuit) up
to the smallest MEANINGFUL circuit: a single **Poseidon permutation** — 11 custom `Poseidon` gate rows
carrying the 165 round constants that byte-match o1js, plus a closing `Zero` gate — **authored in
Lean** (`Dregg2.Circuit.Emit.KimchiRenderPoseidon`: `KimchiCustomGates.poseidonRowCoeffs` for the
coeffs, `KimchiPlacement.place` for the wires, `PastaPoseidon.Ref.permFrom` for the witness) and
PROVED + VERIFIED on the pure-Rust prover (`o1-labs/proof-systems` tag 0.3.0). No OCaml, no Node, no
o1js in the path. House Law #1: the circuit is Lean-authored; `proof-systems` only RUNS it.

It closes the gap the R4a work named: the R4a wire-fidelity check used EMPTY-coeff circuits, so the
real Poseidon coefficients had never been in an actual PROOF. Here they are — the 165 byte-exact
round constants now CONSTRAIN a real kimchi proof, and the permutation's output equals the o1js
`Poseidon.hash([1])` gold (= dregg's own `Ref.hash [1]`), so the coeffs are shown to compute the
RIGHT hash in a proof, not merely to match a byte-diff.

Standalone (empty `[workspace]` table) with a `[[bin]]` declaration so it is not a "dark" tracked
`.rs`, kept OUT of the breadstuffs workspace because it pins `proof-systems` at `tag = "0.3.0"`, a
different rev than the workspace's `emberian/proof-systems` patch. Same shape/reason as
`pickles-r4-harness`.

## What the test asserts (`src/main.rs`, `mod poseidon_r4`)

| test | property |
|---|---|
| `good_witness_verifies` | the Lean-synthesized Poseidon circuit's witness PROVES + `verify()==true` |
| `output_matches_o1js_gold` | the permutation output lane 0 (witness col 0, row 11) equals the o1js `Poseidon.hash([1])` gold `7555…828141` (= dregg `Ref.hash [1]`) |
| `witness_tamper_rejected` | flipping one intermediate round-state limb (`s(1)[0]+1`) is REJECTED — the Poseidon round constraint bites |
| `coeff_tamper_rejected` | flipping one of the 165 round constants (`rc[0][0]+1`) makes the good witness fail — the byte-exact coeff actually CONSTRAINS, it is not inert |
| `unconstrained_flip_accepted` | flipping an UNCONSTRAINED cell (the Zero-gate row, col 5) is ACCEPTED — so the two rejections above are the constraints biting, not a blanket rejection (non-vacuity) |

Rejection is by the **proof** (a non-vanishing quotient at `ProverProof::create`), not a debug
assertion: the index is built with `disable_gates_checks = true`, which skips the prover's debug-mode
witness preflight (`index.verify(..).expect("incorrect witness")`) — the cryptographic constraints are
unaffected by that flag.

## Run (one command)

```sh
cargo test --manifest-path metatheory/fixtures/pickles-poseidon-harness/Cargo.toml --release -- --nocapture
```

`--release` matters — arkworks field ops in debug make proving much slower.
MEASURED green (Rust 1.92, proof-systems tag 0.3.0): `5 passed; 0 failed` in ~1.5s;
`verify() == true` on the Lean Poseidon circuit MEASURED at **~0.9s** (`cargo run --release`).

The `main()` binary runs the same sequence as a demo against a directory (argv[1], default
`fixtures/`), so it can be pointed at a FRESH Lean render (`/tmp/pickles-poseidon`) to drive the live
pipeline with no committed fixture in the path:

```sh
cargo run --manifest-path metatheory/fixtures/pickles-poseidon-harness/Cargo.toml --release -- /tmp/pickles-poseidon
```

## Provenance / regenerate the fixture

`fixtures/poseidon.json` is emitted by `Dregg2.Circuit.Emit.EmitPoseidonJson`'s `main` (a thin driver
over `KimchiRenderPoseidon.poseidonJson` — the single source of truth). It is a GENERATED artifact;
regenerate only when that Lean module changes:

```sh
cd metatheory
lake build Dregg2.Circuit.Emit.KimchiRenderPoseidon              # elaborate the circuit + its #guards
lake env lean --run Dregg2/Circuit/Emit/EmitPoseidonJson.lean    # writes /tmp/pickles-poseidon/poseidon.json
cp /tmp/pickles-poseidon/poseidon.json fixtures/pickles-poseidon-harness/fixtures/  # from repo root
```

The circuit: input `[1,0,0]` (absorbing `[1]` into a zero sponge state), one full 55-round Poseidon
permutation over Pasta Fp. Witness column/row layout is transcribed from `poseidon.rs::generate_witness`
(`STATE_ORDER = [0,2,3,4,1]`); the placed wires are identity self-wires — exactly `Wire::for_row` /
`create_poseidon_gadget`'s standalone-hash wiring, since the state chains across rows through the
gate's `Next`-row reference, needing no copy constraint. `KimchiRenderPoseidon`'s `#guard`s pin the
structure and the output-equals-gold in `lake build` (via the `PicklesSynthesis` aggregate).

## Scope

This is a kimchi **inner** proof of a Lean-synthesized Poseidon circuit — byte-exact FIDELITY of the
gate rows/coeffs/placement + a real binding proof, and cross-agreement of dregg's own Poseidon
evaluator with `proof-systems`' Poseidon (mediated by `verify()==true`). It is NOT a soundness proof,
NOT "machine-checked Pickles", and NOT a Mina-valid Pickles proof (that is R4b / Phase B). The
reportable increment: the o1js-free Lean-render → pure-Rust-prove pipeline works for a REAL circuit
(Poseidon), not just a toy.
