# Direct-logic descriptor translation validation — 2026-07-22

> **Updated 2026-07-23 — the Gabbay specimen recorded below was REPAIRED.**
> As first recorded, the public Gabbay descriptor's acceptance gate was the sum
> of three squared residuals, which is not a faithful conjunction over BabyBear
> (`284861408 ^ 2 = -1` there, so a canonical FALSE table made the gate vanish).
> The bound that closed the gap lived only in a Lean-side
> `LiveProjectionCertificate` that no emitted byte checked. That shape is
> RETIRED. Acceptance is now three LINEAR atoms plus a 30-bit range LOOKUP on
> each of the six entry columns, all emitted. Every Gabbay number in this
> document — byte length, BLAKE3, constraint count — is the REPAIRED descriptor;
> the retired figures are kept only where explicitly labelled retired.

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
| public Gabbay direct table (repaired) | 1,580 | `74c4898aa2b939ead8a303e8eee8307b0e8ae2fb9e2b6fbf13b76c41262942b8` |
| public optimized BoolGraph factor | 2,654 | `b76b68ff0e5a70ebd31d13f7d04340cd8719ed5ccd69ce9b6bb3df766661da13` |

The retired Gabbay shape was 1,740 bytes at BLAKE3
`0f2c4f6cb245c0fc41d66cf35aead9e2d17df43d5827f48cab1aa092aa409e0a`; that image
is unsound and must not be re-pinned. The Python checker pins the same repaired
bytes by SHA-256, `9f5ef0608f6088f992292736d91cd9a7bec235b9868d55f3065350e3434f6dd5`.

The fail-closed Rust loader rejects a changed byte image before parsing.  The
tests deliberately make two changes that remain syntactically valid JSON: a
layout mutation and an arithmetic-expression mutation.  Both parse under the
ordinary parser and both are refused by the reviewed-byte pin.

## Coverage

The public Gabbay specimen checks:

- parser acceptance;
- 6 public inputs, 6 trace columns, and 15 constraints: 6 PI bindings, 3 LINEAR
  acceptance atoms (`output j - input j - 1`, one per column), and 6 range
  LOOKUPS against the declared 30-bit range table id `2`, one per entry column.
  (Retired shape, for contrast: 7 constraints — 6 PI bindings plus one
  sum-of-squares arithmetic gate — with no emitted bound at all. The
  descriptor's `ranges` field is `[]` in both; the enforcing instrument is the
  six lookups, never `ranges`.);
- honest trace acceptance and one-cell public-statement tamper refusal;
- live `prove_vm_descriptor2` / `verify_vm_descriptor2` acceptance and prover
  refusal after a public-input tamper;
- both halves of the repair, each pinned load-bearing by a table the other half
  would accept: the BabyBear cancellation table (in range, refused by atoms
  `#6`/`#7`) and an out-of-range cell (all three successor equations hold in the
  field, refused by the range tooth); and
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
cargo test -p dregg-circuit \
  --test direct_logic_descriptor_translation_validation

python3 tools/direct-logic-descriptor-assurance/verify.py
```

Run it in the DEV profile, the way CI invokes `cargo test --workspace`. With
`debug_assertions` on, plonky3's `check_constraints` panics at the first
unsatisfied constraint instead of returning `Err`, so the two prover-refusal
tests catch the unwind and assert on the panic message — which names the exact
violated constraint indices, a stronger assertion than `is_err()`. The caught
panic is expected: `libtest` captures it, so nothing is printed while the tests
pass; under `--nocapture` a
`thread ... panicked at check_constraints.rs:133` line appears from those two
tests, and it is the refusal being observed, not a failure.

Re-recorded on 2026-07-23, against the REPAIRED Gabbay descriptor (the
2026-07-22 figures — 29 Gabbay keystones, 10 Rust tests — were the retired
shape):

```text
GabbayDescriptorIR2PublicBinding.lean:
  #assert_all_clean: 40 keystones pinned kernel-clean
DirectLogicBoolGraphDescriptorIR2.lean:
  #assert_all_clean: 39 keystones pinned kernel-clean
DirectLogicAdversarialFalsifierV2.lean:
  #assert_all_clean: 21 keystones pinned kernel-clean

Rust descriptor assurance:
  test result: ok. 12 passed; 0 failed; 0 ignored
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

### Named residual: the honest range table

The range half of the Gabbay repair is enforced by LOOKUPS, and a lookup bounds
a column only against the table it looks into.  The Lean statement relation
`StatementSatisfied` therefore carries `HonestRangeTable trace`
(`trace.tf .range = rangeRows 30`) as an explicit premise, and the abstract
carrier `Satisfied2` does **not** enforce it — it fixes the memory and map-op
tables structurally (`memTableFaithful`, `mapTableFaithful`) but has no
corresponding field for `.range`.  With a forged range table the out-of-range
wrap witness passes every emitted gate.

That premise is discharged in deployment, not in the carrier: the Rust assembly
CONSTRUCTS the limb decomposition for a range lookup at the width pinned by the
committed table id rather than reading a prover-supplied table
(`circuit/src/descriptor_ir2.rs`), and the Python evaluator here models the same
honest table.  So the discharge is exactly the Rust-side evidence this artifact
records — it is not a Lean theorem.  This is a carrier-level residual, uniform
across every range tooth in the codebase and not specific to this descriptor;
it is stated in full in `Dregg2.Verify.DirectLogicAdversarialFalsifierV2` §0.
