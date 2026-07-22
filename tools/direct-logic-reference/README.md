# DREGG direct-logic reference compiler

This directory contains a standalone, standard-library Python executable
specification for the two corrected finite-field constructions formalized in
Lean:

- a positive residual graph, where equality is a nonnegative square,
  conjunction/universal quantification is addition, and
  disjunction/existential quantification is multiplication;
- an exact one-means-true Boolean graph with inverse-witness zero tests and an
  integer-to-field atom-fidelity certificate.

The positive plan is admitted only when its static bound certificate proves
that every materialized residual and partial accumulator is strictly below the
chosen prime modulus before projection. Negation is explicitly outside this
positive fragment. The Boolean plan admits an equality only when its static
integer difference bound is also below the modulus; wider natural terms need a
multi-limb/range lowering and are rejected explicitly by this single-field
reference.

This is a compiler, evaluator, witness-plan checker, and symbolic cost
certificate generator. It is not a proof system and it does not report Python
execution time as a prover speedup.

## Source schema

Inputs use `dregg.direct-logic.source.v1`:

```json
{
  "schema": "dregg.direct-logic.source.v1",
  "modulus": 2013265921,
  "model": [
    {"name": "cap", "value": 7, "bound": 15}
  ],
  "formula": {
    "op": "forall",
    "binder": "i",
    "domain": [0, 1, 2],
    "body": {
      "op": "eq",
      "lhs": {"op": "add", "args": [
        {"op": "var", "name": "cap"},
        {"op": "var", "name": "i"}
      ]},
      "rhs": {"op": "add", "args": [
        {"op": "var", "name": "i"},
        {"op": "var", "name": "cap"}
      ]}
    }
  }
}
```

Terms are `lit`, `var`, binary `add`, and binary `mul`. Formulae are `top`,
`bottom`, `eq`, `not`, binary `and`, binary `or`, and finite `forall`/`exists`.
Quantifier domains are explicit strictly increasing arrays. Variables and
terms range over bounded naturals. The prime modulus is checked rather than
trusted.

The compiler grounds each finite quantifier deterministically and uses a
balanced reduction. Equality term evaluation is exposed in atom metadata and
reported on a cost axis separate from the logic graph.

## Commands

```sh
cd tools/direct-logic-reference
python3 direct_logic_reference.py compile fixtures/hash-source.json -o /tmp/plan.json
python3 direct_logic_reference.py optimize fixtures/hybrid-source.json -o /tmp/hybrid.json
python3 direct_logic_reference.py check /tmp/plan.json
python3 direct_logic_reference.py check /tmp/hybrid.json
python3 direct_logic_reference.py evaluate fixtures/hash-source.json
python3 -m unittest discover -s tests -v
```

All command output is canonical JSON: sorted keys, compact separators, ASCII
escaping, and one trailing LF. A compiled wrapper contains a SHA-256 digest of
the canonical inner artifact. `check` verifies that digest, recompiles from the
embedded source, checks every primitive witness equation/bound, and compares
both admitted plans with the source semantics.

`optimize` emits the separately versioned
`dregg.direct-logic.hybrid-artifact.v1`; ordinary `compile` remains byte-stable
at artifact v1. The optimizer keeps a cost/bound Pareto frontier for the
residual presentation at every grounded subformula and the cheapest Boolean
presentation. It enumerates native gates and two explicit boundaries:

- `residual_to_boolean`: an inverse-witness zero test;
- `boolean_to_residual`: the materialized complement `r = 1 - b`.

The checked objective is lexicographic in multiplications, equations,
witnesses, conversions, and materialized nodes. Maximum constraint degree and
term-evaluation work remain visible without being collapsed into that score.
The artifact includes the selected derivation and independently reconstructed
all-Boolean/all-no-wrap baselines. This is a symbolic algebraic objective, not
a wall-clock or prover-speed claim.

## Formal correspondence and limits

The positive connective direction and no-wrap obligation mirror
`Dregg2.Metatheory.FOLArithmetizationCorrected` and
`Dregg2.Metatheory.IntegerProjectionSoundness`. The Boolean primitive equations
and cost coordinates mirror `Dregg2.Logic.BoolGraph` and
`Dregg2.Metatheory.ArithmetizationCost`.

The generated object is a model-specific reference witness plan. It does not
claim a Rust-to-Lean refinement, an emitted DREGG descriptor, proof-system
soundness, zero knowledge, proving latency, finality, or a performance ratio.
