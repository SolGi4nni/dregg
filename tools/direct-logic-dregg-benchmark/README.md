# Production-derived direct-logic benchmark

This directory bridges the formally certified DREGG Boolean workloads to the
actual Rust DescriptorIR2/BatchSTARK backend without a hand-written semantic
reconstruction.

The source of truth is
`Dregg2.Metatheory.DirectLogicDreggWorkloads`. `Emit.lean` imports that module
and writes, for Admission, Upgrade, Clearance, and Strand:

- the exact naive-source and certified-optimized `emitVmJson2` bytes;
- the exact `canonicalRow` for each descriptor;
- the shared canonical public residual vector and Boolean truth vector; and
- a Lean-computed layout/resource manifest.

The selected accepting branches are coherent production cases:

| workload | true/false atom assignment |
|---|---|
| Admission | all common gates true; `validUntil = none`; timed branch false |
| Upgrade | control and subject true; current-proof branch false; owner signature true |
| Clearance | mask and time true; unconfined true; subject membership false |
| Strand | seed true; vouch and bond branches false |

The formal module proves that these Boolean skeletons are equivalent to the
named DREGG decisions. It intentionally leaves arithmetic, hashes, container
membership, and lifecycle tests at the existing atom boundary.

## Regenerate and check

From `metatheory/`:

```sh
lake env lean --run ../tools/direct-logic-dregg-benchmark/Emit.lean
```

Then, from the repository root:

```sh
cargo run -p dregg-circuit --release \
  --bin direct_logic_dregg_workloads_benchmark -- --print-pins
cargo nextest run -p dregg-circuit \
  -E 'binary(direct_logic_dregg_workloads_benchmark)'
```

The BLAKE3 pins in the Rust harness are reviewed constants. Regenerating
fixtures must not silently rewrite them: a formal/compiler change first causes
the Rust gate to fail, then a reviewer compares the new Lean bytes and updates
the pins deliberately.

## Capture

```sh
cargo build -p dregg-circuit --release \
  --bin direct_logic_dregg_workloads_benchmark
DREGG_DLOGIC_PROVE_SAMPLES=25 \
DREGG_DLOGIC_VERIFY_SAMPLES=75 \
DREGG_DLOGIC_WARMUPS=5 \
  target/release/direct_logic_dregg_workloads_benchmark > raw.log
python3 tools/direct-logic-dregg-benchmark/summarize.py raw.log > summary.csv
```

Each measured proof is verified outside its timed proving interval. Source and
optimized runs alternate order per sample, use the same public truth
assignment, and use identical backend parameters.

In release mode the prover's producer-side self-verification is disabled. The
tamper gate therefore mints a proof, when necessary, and requires the actual
consumer verifier to reject it. Debug/test builds may refuse earlier because
their producer self-verification is enabled.

The checked capture and full methodology are in
`docs/deos/artifacts/direct-logic-dregg-workloads-2026-07-22-m2-max/`.
