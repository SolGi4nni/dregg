# Kimchi reality-gate extractors — preserved because they were one `git clean` from gone

These two files produce the **ground truth** for the Mina/Kimchi reality gates
(`metatheory/kimchi_real_proof.json` → `KimchiRealProofGate.lean`, and the Poseidon-firing
fixture → `KimchiPoseidonGate.lean`). Without them the fixtures cannot be regenerated and the
gates' differentials become unreproducible numbers.

**They lived only as UNTRACKED files inside a third-party checkout** (`~/dev/proof-systems/kimchi/
examples/`), which `docs/MINA-REALITY-GATE.md` described as "committed in that repo" — false, and
caught by `docs/AUDIT-MINA-KIMCHI.md`. Copied here verbatim on 2026-07-27 so the gate's provenance
survives a `git clean`, a re-clone, or a rev bump in that checkout.

## Provenance

- Source checkout: `~/dev/proof-systems` (o1-labs `proof-systems`), rev **`f6d958dc05`** at copy time.
- `reality_gate_export.rs` — builds `create_circuit(0, 5)`, proves it over Vesta/Pasta, asserts the
  real `kimchi::verifier::verify` ACCEPTS, then dumps every oracle value via `proof.oracles(...)`
  (the exact `to_batch` path) as JSON. This is the fixture the C5/C8 differentials consume.
- `reality_gate_poseidon_export.rs` — the same, plus a full `create_poseidon_gadget`, so the emitted
  proof has `poseidon_selector(ζ) ≠ 0`. This is what makes the six transcribed custom-gate bodies
  and the C3 `v`/`u` challenge re-derivation NON-VACUOUS rather than a source reading.

⚠ The `36a8b510` rev cited in the Lean headers is a hardcoded `println!` in the extractor, not a
recorded fact — true for the original fixture (reflog-confirmed) but nothing enforces it. The rev
above is what the checkout reads TODAY. If you regenerate, re-record both.

## To regenerate

Copy the file back into `<proof-systems>/kimchi/examples/`, then `cargo run --example
reality_gate_export` (resp. `..._poseidon_export`) from that checkout, and replace the JSON /
the Lean literals. The Lean side byte-matches the JSON (audited: all 30 literals).
