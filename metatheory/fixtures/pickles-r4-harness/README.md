# pickles-r4-harness — the R4a PROVE + VERIFY + BIND test for Lean-synthesized kimchi circuits

This standalone crate is the committed CI form of the **R4a** milestone from
`docs/PICKLES-SYNTHESIS-EPOCH-SCOPE.md` §10: a circuit **authored in Lean**
(`Dregg2.Circuit.Emit.KimchiPlacement.place` + `KimchiRender` coeffs/witness) is a real, provable,
**binding** kimchi circuit on the pure-Rust prover (`o1-labs/proof-systems`) — no OCaml, no Node, no
o1js in the path. House Law #1: the circuit is Lean-authored; `proof-systems` only RUNS it.

It mirrors the sibling `kimchi-extractors` / `pickles-extractors` fixture crates: a standalone package
(empty `[workspace]` table) with a `[[bin]]` declaration so it is not a "dark" tracked `.rs`, kept OUT
of the breadstuffs workspace because it pins `proof-systems` at `tag = "0.3.0"`, a different rev than
the workspace's `emberian/proof-systems` patch.

## What the test asserts (`src/main.rs`, `mod r4a`)

Each `#[test]` reads a committed Lean-emitted fixture from `fixtures/` and asserts ONE property:

| test | property |
|---|---|
| `good_witness_verifies` | the Lean-synthesized binding circuit's good witness PROVES + `verify()==true` |
| `gate_tamper_rejected` | flipping a witness cell that breaks `p = a·b` (a=5→6) is REJECTED — the Lean generic-gate coeffs are LIVE, not vacuous |
| `copy_tamper_rejected` | flipping the free copy cell `p@(1,3)` (35→99) is REJECTED — ONLY the copy permutation can catch this, so the R1 placement WIRES are load-bearing in a real proof |
| `nocopy_control_accepts_flip` | the SAME (1,3) flip on the no-copy control circuit is ACCEPTED — proving the `copy_tamper_rejected` rejection was the placement wire, nothing else |
| `render_fidelity_case_a` / `_case_b` | the Lean-rendered `place` wires equal the o1js byte-goldens, cell-for-cell (Lean → JSON → Rust round-trip is faithful) |

Both binding polarities (gate-constraint AND copy-permutation) plus the isolating control are present:
a test that only checked `accept` would be half a test.

## Run (one command)

```sh
cargo test --manifest-path metatheory/fixtures/pickles-r4-harness/Cargo.toml --release -- --nocapture
```

`--release` matters — arkworks field ops in debug make proving ~orders of magnitude slower.
MEASURED green on hbox (Rust 1.92, proof-systems tag 0.3.0): `6 passed; 0 failed` in ~2.1s.

Red-path CONFIRMED (the tests genuinely fail when they should): corrupting a golden wire in
`fixtures/caseA.json` fails `render_fidelity_case_a`; zeroing the row-0 `Mul` coeffs in
`fixtures/binding.json` (dropping the `p=a·b` constraint) makes `gate_tamper_rejected` fail because the
tamper is then accepted.

The `main()` binary runs the same sequence as a demo/regeneration driver against a directory (argv[1],
default `fixtures/`), so it can also be pointed at a FRESH Lean render (`/tmp/pickles-r4`) to drive the
live pipeline with no committed fixture in the path:

```sh
cargo run --manifest-path metatheory/fixtures/pickles-r4-harness/Cargo.toml --release -- /tmp/pickles-r4
```

## Provenance / regenerate the fixtures

`fixtures/{binding,nocopy,caseA,caseB}.json` are emitted by `Dregg2.Circuit.Emit.KimchiRender`'s `main`
(the single source of truth — the Lean placement + render). They are GENERATED artifacts; regenerate
only when that Lean module changes:

```sh
cd metatheory
lake build PicklesSynthesis                                   # elaborate the render + its cone
lake env lean --run Dregg2/Circuit/Emit/KimchiRender.lean     # writes /tmp/pickles-r4/{binding,nocopy,caseA,caseB}.json
cp /tmp/pickles-r4/{binding,nocopy,caseA,caseB}.json fixtures/pickles-r4-harness/fixtures/  # from repo root
```

- `binding.json` — the smallest provable Lean-placed circuit that BINDS: row 0 `Mul` (`p=a·b`), row 1
  `Const 35` (`p=35`), `p` copy-wired across `(0,2)→(1,0)→(1,3)`. `a=5, b=7, p=35`.
- `nocopy.json` — the same gates WITHOUT the `p@(1,3)` copy wire (the control).
- `caseA.json` / `caseB.json` — the R1 placement wire-fidelity goldens (`x+y===8`; and the smallest
  cross-row copy) — `placed_wires` (from Lean `place`) vs `o1js_wires` (o1js 2.15.0 goldens).

## Scope

R4a is a kimchi **inner** proof of a Lean-synthesized circuit — byte-exact FIDELITY + a real binding
proof. It is NOT a Mina-valid Pickles proof and NOT a recursion-soundness theorem (that is R4b / Phase
B). See `docs/PICKLES-SYNTHESIS-EPOCH-SCOPE.md` §10.
