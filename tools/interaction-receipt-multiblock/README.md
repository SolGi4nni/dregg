# Multi-block interaction-receipt wire validator

This isolated validator emits `descriptorAtDepth 25` from the proved Lean
construction and checks its complete JSON wire image: 36 public/trace columns,
36 first-row PI bindings, six fixed-arity 15 hash sites, exact before/after
domain columns, exact public predecessor-digest chaining, and seven zero pads
in each final eleven-word payload block.

Run from the repository root:

```sh
python3 tools/interaction-receipt-multiblock/validate.py
```

The validator is a serialization guard, not an independent semantic proof.
Arbitrary-witness soundness and constructive completeness are theorems in
`metatheory/Dregg2/Calculus/IntensionalCCCInteractionMultiBlockDescriptorIR2.lean`.
