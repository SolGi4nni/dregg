# Typed linear predicate descriptor check

`verify.py` runs the Lean emitter for the production-shaped interchain
trust-rung instance, parses the exact JSON wire image, and checks its guarded
layout.  In particular, public inputs bind raw `tag`/`payload` columns 4 and 5;
the four atom residual columns are computed by in-descriptor affine equations
and are not caller-published truth bits.

Run from the repository root:

```sh
python3 tools/typed-linear-predicate-descriptor/verify.py
```

This is a narrow serialization/layout smoke test.  The semantic assurance is
the kernel-checked arbitrary-trace soundness and constructive-completeness
theorems in `TypedLinearPredicateDescriptorIR2.lean`.
