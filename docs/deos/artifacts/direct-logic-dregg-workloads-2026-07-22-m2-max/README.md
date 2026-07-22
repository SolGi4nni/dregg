# DREGG direct-logic source/optimizer live capture (2026-07-22)

This capture upgrades the earlier toy direct-logic measurements to four
Boolean decisions actually named and consumed by the DREGG development:

- fail-closed turn Admission, including receipt-head binding;
- anti-brick program Upgrade authorization;
- structured credential Clearance; and
- stake/vouch/bond Strand admission in front of finality.

It measures this chain:

```text
production DREGG predicate
  <- proved Boolean-skeleton equivalence in Lean
  -> naive source Formula / certified optimized Formula
  -> proved public BoolGraph -> DescriptorIR2 lowering
  -> exact Lean emitVmJson2 bytes + canonical public trace
  -> Rust parse_vm_descriptor2
  -> prove_vm_descriptor2
  -> verify_vm_descriptor2
```

Rust does not reconstruct the formulas or witnesses. `Emit.lean` imports the
formal workload module and emits both endpoints and both canonical traces.
The Rust harness BLAKE3-pins those bytes before parsing them, recomputes layout
and nonlinear-multiplication counts from the parsed IR, and checks that each
source/optimized pair uses the same public truth assignment.

## Exact certified resource changes

These are deterministic facts about the emitted relations, not timing claims.

| workload | width | constraints | nonlinear multiplications | auxiliaries | descriptor bytes |
|---|---:|---:|---:|---:|---:|
| Admission source | 77 | 121 | 108 | 65 | 17,845 |
| Admission optimized | 47 | 71 | 58 | 35 | 10,091 |
| Upgrade source | 21 | 33 | 28 | 17 | 4,978 |
| Upgrade optimized | 15 | 23 | 18 | 11 | 3,427 |
| Clearance source | 21 | 33 | 28 | 17 | 4,978 |
| Clearance optimized | 15 | 23 | 18 | 11 | 3,427 |
| Strand source | 11 | 17 | 13 | 8 | 2,713 |
| Strand optimized | 11 | 17 | 13 | 8 | 2,713 |

Thus Admission removes 50 constraints and 50 nonlinear multiplications;
Upgrade and Clearance each remove 10 constraints and 10 nonlinear
multiplications; Strand is already in optimizer normal form and changes
nothing. These reductions are certified even if a particular benchmark host
is noisy.

## Captured proof sizes

Proof byte counts are one retained postcard encoding per variant. Unlike the
relation ledgers, the exact serialized size can vary with proof contents.

| workload | source bytes | optimized bytes |
|---|---:|---:|
| Admission | 14,016 | 11,894 |
| Upgrade | 10,431 | 10,081 |
| Clearance | 10,469 | 10,157 |
| Strand | 9,850 | 9,850 |

All eight proofs reported `degree_bits=0` for their one-row main traces.

## Timing capture

Twenty-five proving and seventy-five verification samples were retained for
every variant after five warmups. Source and optimized order alternated by
round. Every measured proof was verified outside the timed proving interval.

| workload | variant | prove median / p95 (ms) | verify median / p95 (ms) |
|---|---|---:|---:|
| Admission | source | 58.388 / 154.992 | 0.858 / 4.409 |
| Admission | optimized | 39.245 / 111.219 | 0.603 / 3.901 |
| Upgrade | source | 102.989 / 182.911 | 0.379 / 6.998 |
| Upgrade | optimized | 48.448 / 119.544 | 0.381 / 2.100 |
| Clearance | source | 237.162 / 384.875 | 0.404 / 11.629 |
| Clearance | optimized | 7.269 / 80.565 | 0.419 / 6.153 |
| Strand | source | 18.409 / 68.116 | 0.373 / 9.373 |
| Strand | optimized | 11.398 / 134.119 | 0.345 / 11.455 |

**No timing speedup is claimed from this capture.** The shared host was under
severe concurrent load (33.61 / 26.37 / 24.91 immediately after capture), and
the distributions are wide and non-monotone. Most decisively, Strand source
and optimized are byte-identical, yet their proving medians and p95s differ;
some optimized verification medians or p95s are also worse. This is a useful
noise/control result, not evidence for a performance ratio. The full raw
samples, rather than a selected ratio, are checked in as `raw.log`.

## Binding and tamper result

Each descriptor binds atom residual columns to public inputs. The harness
changed public input 0 while retaining the Lean-authored row and required the
actual consumer verifier to reject the resulting proof for all eight
variants. In release mode `prove_vm_descriptor2` deliberately skips its
producer-side self-verification and may return such an invalid proof; consumer
`verify_vm_descriptor2` is the soundness boundary. The raw log records all
eight `TAMPER,...,verifier_rejected` results.

## Reproduction

```sh
cd metatheory
lake env lean --run ../tools/direct-logic-dregg-benchmark/Emit.lean
cd ..
cargo build -p dregg-circuit --release \
  --bin direct_logic_dregg_workloads_benchmark
DREGG_DLOGIC_PROVE_SAMPLES=25 \
DREGG_DLOGIC_VERIFY_SAMPLES=75 \
DREGG_DLOGIC_WARMUPS=5 \
  target/release/direct_logic_dregg_workloads_benchmark > raw.log
python3 tools/direct-logic-dregg-benchmark/summarize.py raw.log > summary.csv
```

The attempted persvati offload failed before compilation because its build
lane filesystem was full. This capture therefore used the already-warm local
release target; the failure and fallback are recorded in `META.txt`.

## Scope boundary

The formal theorems are exact at the Boolean skeleton. The production atoms
(hashes, arithmetic comparisons, lifecycle tests, list membership, capability
lookup, and receipt comparison) keep their existing implementations. This is
therefore stronger than a toy formula benchmark, but it is not yet a proof
that every interior atom has been lowered through this new compiler.

`SHA256SUMS` binds the formal sources, emitter, all generated fixtures, Rust
harness, lockfile, raw samples, and summary used by this capture.
