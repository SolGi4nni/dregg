# Direct-logic descriptor translation validation — 2026-07-22

This artifact records independent Rust consumption of the exact JSON emitted
from two Lean-authored, public-statement-bound direct-logic descriptors:

1. `GabbayDescriptorIR2PublicBinding.publicDescriptor`, the direct public
   three-entry successor table; and
2. `DirectLogicBoolGraphDescriptorIR2.publicDescriptor factorAfter`, the
   materialized optimized factor specimen.

The executable evidence is:

- `circuit/tests/direct_logic_descriptor_translation_validation.rs`, which
  uses the production Rust parser and live prover; and
- `tools/direct-logic-descriptor-assurance/verify.py`, a second independent
  standard-library JSON parser and concrete evaluator.

## Exact byte roots

The test reads the literal on the right side of a Lean `#guard` rather than a
second hand-maintained JSON fixture.  Each literal is guarded equal to
`emitVmJson2` in its owning Lean module, then independently BLAKE3-pinned in
Rust before parsing.

| Descriptor | decoded bytes | BLAKE3 |
|---|---:|---|
| public Gabbay direct table | 1,740 | `0f2c4f6cb245c0fc41d66cf35aead9e2d17df43d5827f48cab1aa092aa409e0a` |
| public optimized BoolGraph factor | 2,654 | `b76b68ff0e5a70ebd31d13f7d04340cd8719ed5ccd69ce9b6bb3df766661da13` |

The fail-closed Rust loader rejects a changed byte image before parsing.  The
tests deliberately make two changes that remain syntactically valid JSON: a
layout mutation and an arithmetic-expression mutation.  Both parse under the
ordinary parser and both are refused by the reviewed-byte pin.

## Coverage

The public Gabbay specimen checks:

- parser acceptance;
- 6 public inputs, 6 trace columns, and 7 constraints (6 PI bindings plus one
  arithmetic gate);
- honest trace acceptance and one-cell public-statement tamper refusal;
- live `prove_vm_descriptor2` / `verify_vm_descriptor2` acceptance and prover
  refusal after a public-input tamper; and
- exhaustive differential agreement on 8,000 small canonical tables: every
  triple of inputs in `0..=3` crossed with every triple of outputs in `0..=4`.

The public BoolGraph specimen checks:

- parser acceptance;
- 4 public inputs, 12 trace columns, and 18 constraints (4 PI bindings plus 14
  graph/acceptance gates);
- honest canonical trace acceptance and public-residual tamper refusal;
- live proof acceptance/verification and prover refusal after a public-input
  tamper; and
- all 16 assignments to the four source atoms, reconstructing Lean's canonical
  postorder witness independently in Rust and comparing descriptor acceptance
  with `(a0 && a1) || (a0 && a2)`.

Run only this evidence with:

```sh
cargo nextest run -p dregg-circuit \
  --test direct_logic_descriptor_translation_validation

python3 tools/direct-logic-descriptor-assurance/verify.py
```

Recorded on 2026-07-22:

```text
GabbayDescriptorIR2PublicBinding.lean:
  #assert_all_clean: 29 keystones pinned kernel-clean
DirectLogicBoolGraphDescriptorIR2.lean:
  #assert_all_clean: 39 keystones pinned kernel-clean

Rust descriptor assurance:
  test result: ok. 10 passed; 0 failed; 0 ignored
Python descriptor assurance:
  Gabbay 8000 exhaustive rows; BoolGraph 16 exhaustive truth assignments;
  all checks passed
```

## Assurance boundary

This is differential and translation-validation evidence.  It demonstrates
agreement for the committed specimens and enumerated domains, plus two live
proof round trips.  It is **not** a kernel theorem that the Rust JSON parser,
concrete evaluator, trace assembly, or STARK prover refines the Lean model.
The Lean correctness theorems and exact-byte guards remain the formal side of
the boundary; this test exercises the independently implemented Rust side.
