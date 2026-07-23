# DESIGN — Peephole layout optimizer: the asserted-conjunction zero-test elision

Status: design (read-only lane; no code changed). Substrate: this is **Lean-authored
AIR/optimizer** work — every rewrite below is a `PassiveOptimization` instance whose
`SecurityRefinement`/`CompletenessPreservation` are machine-checked theorems over the
*actual emitted* `EffectVmDescriptor2`, reusing the already-proven contracts in
`Dregg2/Circuit/PassiveDescriptorOptimization.lean`. No Rust AIR is authored.

## 1. The regression, stated at the emitted-object level

The typed front end
(`Dregg2/Metatheory/TypedLinearPredicateDescriptorIR2.lean`) lowers a `Program pub sec
atoms` = (`atomTerms : Fin atoms → AffineTerm`, `source : Formula atoms`) with **no
optimizer between `Program` and the emitted descriptor**. Every atom `a` (an affine
equality `affineTermₐ = 0`) is lowered by `nodesAt` (`DirectLogicBoolGraphDescriptorIR2.lean:135`)
to a **`zeroTest`** node:

```
| .atom a => [.zeroTest a.val base (base + 1)]
```

whose `Node.constraints` (same file, lines 87–91) are **three degree-≤2 gates** —
a bit gate `out·(out−1)=0`, a kill gate `x·out=0`, and an inverse gate
`x·inv+out−1=0` — plus **two witness columns** (`out`, `inv`). The cost model
(`ArithmetizationCost.lean:120`) charges the atom `zeroTestGateCost = ⟨eq 3, mult 3,
wit 2, deg 2, cells 0⟩`. Every binary `and`/`or` then adds `booleanBinaryGateCost =
⟨2, 2, 1, 2, 0⟩` (2 gates, 1 witness, 2 mults). This is reified **even inside a pure
conjunction** — where the atom's Boolean *value* is never actually needed, only its
truth.

The zero-test machinery exists to compute the field indicator `[x=0] ∈ {0,1}` so the
bit can be consumed by `∨`/`¬`. Inside an **asserted-true conjunction** (every conjunct
must hold for the single accepting `output=1`), that indicator is dead weight: a plain
linear gate `affineTermₐ = 0` says exactly the same thing in one degree-1 constraint
with zero witnesses and zero multiplications.

### Is the zero-test load-bearing inside a conjunction? No — and that is the finding.

Under the accept equation `outputAt = 1` (`TypedLinearPredicateDescriptorIR2.lean:154`)
the output of an and-tree is the product of its child bits, so acceptance **forces every
asserted atom bit to 1, hence every asserted residual to 0**. A direct linear assertion
`affineTermₐ = 0` is therefore equivalent *at the only accepting assignment* to the whole
zeroTest+and+accept apparatus for that atom. The inverse witness `inv = x⁻¹` is only ever
needed to prove the *contrapositive* leg (`x ≠ 0 ⟹ bit = 0`) — which matters solely when
the bit can legitimately be 0, i.e. under a `∨`, a `¬`, or any non-asserted position.
**The ~10x for conjunction-context equalities is a real, recoverable regression, not
intrinsic.** The one genuine side condition is DAG sharing (§6): an atom bit that is *also*
consumed in a non-asserted position must keep its zeroTest.

## 2. The rewrite rule

Define the **asserted frontier** of `source`: the atoms reachable from the root through
`and`-edges only (no `or`, no `not` on the path). Split

```
source  ≡  (⋀ a ∈ assertedAtoms)  ∧  residualFormula
```

up to ∧-associativity/commutativity (a `Formula.Holds` congruence — trivial induction).

**Rule R1 (zero-test elision).** For each `a ∈ assertedAtoms`, replace its contribution
— the `zeroTest` node's 3 gates and 2 witnesses, plus the `and`-node that consumes its
bit — with a single linear gate

```
gate ((atomTermsₐ).toWindowAt (rawBase atoms))        -- asserts affineTermₐ = 0, degree ≤ 1
```

(`atomLinkBody` without the residual-column subtraction; `AffineTerm.toWindowAt_degree`
already proves degree ≤ 1). The residual column `col a`, the atom's `out`/`inv` columns,
and the collapsed and-spine outputs become **unreferenced**. `residualFormula` (the
non-asserted remainder, e.g. an `∨`/`¬` subtree) is lowered unchanged by the existing
compiler and its output feeds the accept gate as before; if the frontier is the whole
formula, `residualFormula = ⊤` and the accept gate is dropped.

The pass is therefore **two composed `PassiveOptimization`s**:

- **`P_rw : descriptor p → descriptor_rw p`** — same `traceWidth`; constraint list swaps
  the asserted atoms' zeroTest/and/accept gates for direct linear equality gates. Trace
  columns are physically unchanged (the elided witnesses become dead).
- **`P_e1 : descriptor_rw p → compactE1 …`** — the **already-certified E1 dead-column
  deletion** removes the now-dead residual/`out`/`inv`/and-output columns and compacts.

## 3. Which proven contract each half discharges

Everything below instantiates predicates from
`Dregg2/Circuit/PassiveDescriptorOptimization.lean`; nothing new is added to that framework.

| Obligation | Contract | How it is discharged |
|---|---|---|
| `P_rw` public ABI unchanged | `PublicABIEquivalent` | pins untouched; `piCount` equal; `publicBindingSlots` equal (only window-gates change). |
| `P_rw` target accept ⟹ source accept | `SecurityRefinement` | `toSource` overwrites the dead witness region with the **canonical** zero-residual witnesses: `col a := 0`, `out := zeroBit 0 = 1`, `inv := zeroInv 0 = 0`, and-outputs `:= 1`. Then every source gate holds by the *already-proven* `zero_witness_gate`, `field_nodes_valid_of_matches`, `node_constraints_hold_of_field_valid`, and `canonical_accept_holds`. Non-vacuous: `toSource` is a concrete column rewrite. |
| `P_rw` source accept ⟹ target accept | `CompletenessPreservation` | source acceptance gives every asserted residual `= 0` via the *already-proven* `sound` / `atom_link_field`; the target's linear gates are exactly those equalities, so `toTarget = id` works. |
| `P_rw` cost non-increase | new `peephole_exact_resources` (style of `descriptor_exact_resources`) + `≤` vs source | pure `graphCost`/counting equality, no new framework. |
| `P_e1` target accept ⟹ source accept | `E1.security` / `derivedPass` **(already proven)** | dead columns satisfy `compactE1Ok`; reuse `checkedDerived_secure`. |
| `P_e1` source accept ⟹ target accept | `checkedDerived_complete` **(already proven)** | `EffectVmDescriptor2PassiveOptimization.E1`. |
| whole pass | `SatisfiabilityPreservation` | `preservation_comp` of the two `SatisfiabilityPreservation`s (combinator already proven, `PassiveDescriptorOptimization.lean:256`). |

`P_rw`'s two legs together are `SatisfiabilityPreservation P_rw`; composing with E1's via
the proven `security_comp` / `completeness_comp` / `preservation_comp` yields
`SatisfiabilityPreservation (P_rw.comp P_e1)` — the end-to-end statement "the peephole
descriptor is equisatisfiable with, and no weaker than, the original," over the real
emitted bytes.

## 4. Pilot: the field-delta conjunction, recomputed against `descriptor_exact_resources`

Pilot program (a state-transition "field delta" check): `pub = 4`, `sec = 0`, `atoms = 4`
affine equalities `eqConst(inputᵢ, cᵢ)`, `source = and (and (and a0 a1) a2) a3` — a pure
conjunction, the exact shape the arithmetizer over-reifies. (`graphCost` totals are
∧-nesting-invariant, so left/right/balanced nesting give identical numbers.)

**Generated now** (via `descriptor_exact_resources`, `TypedLinearPredicateDescriptorIR2.lean:201`):

- `graphCost = ⟨eq 18, mult 18, wit 11, …⟩`  (4·zeroTest ⟨12,12,8⟩ + 3·and ⟨6,6,3⟩)
- `witnessCount = graphCost.witnesses = 11`
- `traceWidth = atoms + (pub+sec) + witnessCount = 4 + 4 + 11 = 19`
- `constraints.length = pub + atoms + graphCost.equations + 1 = 4 + 4 + 18 + 1 = 27`
- nonlinear multiplications `= 18`

**Hand emit** (what a human writes for "assert 4 field equalities on 4 public inputs"):

- 4 public pins + 4 linear equality gates → `constraints = 8`
- `traceWidth = 4` (only the input columns), `multiplications = 0`

**Peephole output** (`P_rw` then E1) — reaches the hand ideal exactly:

- `P_rw`: constraints `→ 8` (4 pins + 4 direct `affineTermᵢ = 0` gates), `traceWidth`
  still 19 with **15 dead columns** (4 residual + 11 boolean witness), `mult → 0`.
- `E1`: deletes the 15 dead columns → `traceWidth → 4`, constraints `8`, `mult 0`.

### Pilot numbers, generated vs hand vs peephole

| metric | generated | hand | peephole | recovery |
|---|---|---|---|---|
| descriptor constraints | 27 | 8 | **8** | full |
| trace width (columns) | 19 | 4 | **4** | full |
| nonlinear multiplications | 18 | 0 | **0** | full |

Excluding the 4 shared public pins, the generated non-pin constraint count is 23 vs the
hand ideal 4 (**5.75×**); the peephole closes it entirely.

**General formula (pure conjunction of `k` equalities, `p` public inputs).** Generated:
constraints `= p + 6k − 1`, extra columns (beyond inputs) `= 4k − 1`, multiplications
`= 5k − 2`. Hand/peephole: constraints `= p + k`, extra columns `= 0`, multiplications
`= 0`. Asymptotic constraint ratio `→ 6×` and columns/mults `→ 0` — the conjunction
fraction of any "10x-class" mixed program is fully recovered; the `∨`/`¬` remainder keeps
its zero-tests (correctly).

## 5. The hard part

Not the rule and not the cost lemma (both mechanical). The labor is `P_rw`'s
`SecurityRefinement`: `toSource` must rebuild the **entire elided postorder witness
region** — the asserted atoms' `out`/`inv` *and* every and-spine output up to the root —
as canonical values, then show *every* source gate (`descriptor p`'s zeroTest, and, and
accept constraints) holds. This is exactly `canonical_complete`'s obligation but entered
from "residuals are 0" instead of "`p.Holds input`." It is **assembly of already-proven
lemmas** (`zero_witness_gate`, `field_nodes_valid_of_matches`,
`node_constraints_hold_of_field_valid`, `canonical_accept_holds`,
`field_output_of_matches`), not new metatheory. The second fiddly piece is producing the
E1 kill-set for `descriptor_rw`'s dead columns and discharging its shape/ceiling
certificate (`compactE1Ok_of_ceiling`); the dead region is contiguous
(`boolBase … traceWidth`) plus the residual block, which fits E1's derived kill-set shape.

## 6. Honesty / side conditions

- **Not intrinsic.** The zero-test is load-bearing *only* off the asserted frontier
  (`∨`, `¬`, non-asserted positions). R1 fires exclusively on the frontier; the
  remainder compiles unchanged. Stated as an eligibility predicate, not a global rewrite.
- **DAG sharing.** In the current tree `Formula` each atom occurrence is independent, so
  no hazard. If a future fanout/DAG front end shares one atom bit between an asserted
  conjunct and an `∨`-consumer, R1 must fire only when *all* consumers are asserted; the
  eligibility check must be occurrence-wise, not atom-wise. Flagged for the DAG front end.
- **Cost is a separate theorem.** The `PassiveOptimization` framework carries no cost
  predicate; cost non-increase is a `peephole_exact_resources` counting lemma in the
  established `descriptor_exact_resources`/`factor_emitted_exact` style, compared `≤`
  against the source — reusing the cost model, not restating semantics.

## 7. Effort: weeks vs days

- **Days (~3–4):** R1 + `peephole_exact_resources` + the `CompletenessPreservation` leg
  (easy, via `sound`) + the `SecurityRefinement` leg, **stopping before E1** so
  `descriptor_rw` keeps the dead columns but already has the cheap constraint list. This
  kills the **multiplication and constraint** regression (18→0 mult, 27→8 constraints on
  the pilot) — the dominant proving-cost terms — leaving only column count unrecovered.
- **~1.5–2 weeks:** add the E1 composition (kill-set + `compactE1Ok` cert + `preservation_comp`)
  to also collapse `traceWidth` (19→4), plus `#assert_all_clean` on the full pass and a
  tampered-certificate `#guard` canary.

Recommendation in `residual`/`recommendation` fields below.
