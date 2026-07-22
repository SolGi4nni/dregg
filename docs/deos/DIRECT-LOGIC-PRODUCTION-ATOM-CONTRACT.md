# Direct logic: production predicate front-end boundary

The formal artifact is
`metatheory/Dregg2/Metatheory/DirectLogicDreggProductionPredicates.lean`.
It adds a reusable typed front end and four production-derived workloads
without changing the earlier workload corpus.

## The reusable boundary

`ProductionPredicate Input n` contains exactly four pieces:

1. `atomBits : Input → Fin n → Bool`, the typed observation interface;
2. `source : Formula n`, the natural Boolean AST;
3. `decision : Input → Prop`, the production-level meaning; and
4. `correct`, an all-input equivalence between evaluating the AST and the
   production decision.

`ProductionPredicate.compile` is shared by every instance. It runs the checked
optimizer and lowers the result to the public quadratic BoolGraph
DescriptorIR2. The generic theorems provide:

- optimized-AST semantic correctness;
- constructive completeness via the compiler-generated canonical trace; and
- arbitrary-trace soundness when a `PublicAtomContract` is supplied.

The last condition is deliberate. The current public descriptor binds an atom
residual vector, but does not by itself authenticate that vector to the state,
receipt, bridge message, or proof commitment from which the atoms should have
been computed. `PublicAtomContract` names that exact remaining obligation:
every public zero residual must agree with `atomBits` for the authenticated
typed input. A future in-AIR atom/context gadget should construct this contract.
The Boolean compiler does not assume it.

## Production provenance

| Workload | Production source | Exact decision |
|---|---|---|
| Transfer | `Dregg2/Exec/Kernel.lean` | whether `Exec.exec` commits, including positional-or-cap authority, amount, availability, distinctness, and live-account membership |
| Note spend | `Dregg2/Circuit/Spec/notenullifier.lean` | whether `execFullA (.noteSpendA …)` commits, exactly proof-valid and nullifier-fresh |
| Interchain | `Dregg2/Bridge/InterchainAdapterDecision.lean` | the fail-closed `reachedConsensusWire` verdict, including unknown-tag refusal |
| Recursive fold | `Dregg2/Bridge/HoldingFoldRecursive.lean` | four bounded steps of the actual `foldAccept` conjunction |

## Exact live ledgers

These are natural, already-factored ASTs. The checked optimizer leaves all four
unchanged; no DNF-expanded baseline is used.

| Workload | Atoms / PIs | Graph constraints | Accepting constraints | Nonlinear multiplications | Aux columns | Trace width |
|---|---:|---:|---:|---:|---:|---:|
| Transfer | 7 | 33 | 41 | 33 | 20 | 27 |
| Note spend | 2 | 8 | 11 | 8 | 5 | 7 |
| Interchain | 4 | 18 | 23 | 18 | 11 | 15 |
| Four-leaf fold | 4 | 18 | 23 | 18 | 11 | 15 |

Each number is a `by decide` theorem over the same descriptor sealed by
`checkPublicLive`; source and optimized values are equal in every row. These
are absolute Boolean-composition costs, not whole-prover timings and not costs
for the still-external arithmetic, membership, cryptographic verification, or
context-authentication gadgets.

## Verification

Run locally from `metatheory/`:

```sh
lake env lean Dregg2/Metatheory/DirectLogicDreggProductionPredicates.lean
lake build Dregg2.Metatheory.DirectLogicDreggProductionPredicates
```

The module pins the four production equivalences, their arbitrary-trace
composition theorems, and the reusable front-end soundness/completeness
theorems with `#assert_axioms`.
