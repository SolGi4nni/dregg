# Corrected logic compilation: one typed denotation, proof and FHE lowerings

Status: design, grounded against the code at HEAD on 2026-07-21. Nothing in this
document is a claim that the compiler below already exists. It is the smallest
construction that reuses the existing predicate, descriptor, fhIR, BFV, TFHE, and
MPC work without treating a finite-field slogan as a semantics.

## 1. The decision

Build one typed logic front-end with a Boolean denotation, then lower it through
two separately proved backends:

```
                    TypedLogic formula phi
                              |
                       Bool denotation
                              |
                 +------------+------------+
                 |                         |
           proof relation                FHE plan
       EffectVmDescriptor2          BFV / TFHE / MPC mix
                 |                         |
       Satisfied2 -> eval phi       decrypt/run = eval phi
                 +------------+------------+
                              |
                same committed input opening
```

The common object is the source denotation, not a shared polynomial. A proof
relation and an encrypted program have different cost asymmetries and may use
different witnesses. Requiring their traces or polynomials to be identical would
throw away the strongest optimization in each backend.

This also avoids a fourth policy grammar. The existing `Pred`, `RelPred`,
`ArithPred`, and `QuantPred` surfaces become source adapters into the typed core.
They remain useful authoring interfaces; the new core is the point at which
backend selection, range assumptions, leakage, and costs become explicit.

## 2. What can be retained from the Gabbay encoding

Use zero as truth only as a certified intermediate representation, never as the
definition of source truth.

Over nonnegative integers or rationals, the following residual compilation is
exact:

- equality: `R(x = y) = (x-y)^2`;
- conjunction: `R(p and q) = R(p) + R(q)`;
- disjunction: `R(p or q) = R(p) * R(q)`;
- bounded universal: sum the body residuals;
- bounded existential: multiply the body residuals.

It is attractive for FHE precisely where it uses additions: a large conjunction
or bounded universal can become one additive fold followed by one zero decision.
It is unattractive where it uses products: disjunction, existence, interpolation,
and reified negation consume multiplicative depth or PBS/LUT work.

The safe carrier must be part of the compilation certificate. There are three
legitimate modes:

1. `ExactQ`: rational/integer semantics outside the proof field.
2. `NoWrap`: every residual and every partial sum is nonnegative and strictly
   below the plaintext/constraint modulus. This is the same style of obligation
   already enforced by `Market.FhIRClearingPlan.expectedNoWrap` and
   `fhegg-fhe/src/fhir/mod.rs::certify_runnable`.
3. `PrimeProduct`: only the product-zero law is used, over a proved prime
   plaintext field. This validates equality/existential products but does not
   validate conjunction/universal sums.

Without one of those certificates the residual lowering must refuse. In
particular, finite-field cancellation is not a tolerable approximation.

For general formulas the proof backend should instead use an exact Boolean
false-bit representation. If `b = 0` means true and `b = 1` means false, then:

```
not(b)       = 1 - b
and(b,c)     = b + c - b*c
or(b,c)      = b*c
forall(bs)   = OR of the false bits
exists(bs)   = product of the false bits
```

Every bit is constrained by `b*(b-1)=0`. An arbitrary field residual `r` is
reified into a false bit with an inverse witness `z`:

```
r * (1-b) = 0
r * z     = b
b * (b-1) = 0
```

These constraints prove `b=0 iff r=0` over a field. They do not depend on an
ordering or positivity fiction inside that field. Affine inequalities should use
the existing range/decomposition pattern, not a signed polynomial residual; see
`Dregg2.Circuit.Emit.Predicates{Arithmetic,Le,Lt}Emit`.

## 3. Typed source language

The first implementation only needs finite executable types:

```lean
inductive LogicTy
  | bool
  | uint (bits : Nat)
  | sint (bits : Nat)
  | field
  | enum (card : Nat)
  | prod (a b : LogicTy)
  | vec (n : Nat) (a : LogicTy)
  | arr (domainCard : Nat) (a b : LogicTy)

inductive Formula (Gamma : List LogicTy)
  | eq | le | lt
  | and | or | not
  | forallFin (n : Nat)
  | existsFin (n : Nat)
  | memberCommitted
```

Terms should be intrinsically typed (de Bruijn environments are sufficient).
Every numeric type carries its range in the type; every finite quantifier carries
its public cardinality in syntax. Function values at this stage are finite tables.
Application is extensional lookup, and function equality is equality of every
table entry. This gives a real finite higher-order fragment without pretending
that arbitrary functions have a compact finite encoding.

Each input also carries:

- visibility: public, committed, or opened;
- source binding: record field, commitment opening, ciphertext slot, or public
  constant;
- a public range;
- an allowed leakage label.

Define `evalTerm` and `evalFormula` before any polynomial operation. All backend
theorems target this evaluator.

## 4. Proof-relation lowering

The output is a Lean-authored `EffectVmDescriptor2`, plus a witness layout and a
refinement proof. Rust remains a strict descriptor interpreter.

### 4.1 Atoms

- `x = y`: use the raw zero residual `r=x-y`, then either require `r=0` when the
  formula is an assertion or use the exact inverse-witness false-bit gadget
  above. Square only when this atom enters the positive `ExactQ`/`NoWrap`
  residual-sum fragment; a field zero test does not need positivity.
- `x != y`: use an inverse witness, as the existing neq descriptors do.
- `x <= y`: force `d=y-x` and range-check `d` at the declared width. A false-bit
  comparison needs two gated range decompositions, one for each ordering; a
  top-level asserted comparison needs only the accepting side.
- committed membership: retain `QuantifiedPredicate.memberOf`'s witnessed Merkle
  seam. It is not compiled by reading cleartext fields.
- function application: prefer a lookup row or a Merkle/RAM opening. Full
  interpolation is a fallback for tiny public tables, not the default relation.

### 4.2 Connectives and quantifiers

Use false-bit gates when a subformula result is consumed as data. If a conjunction
or universal occurs only as the top-level assertion, concatenate all child
relations and omit the result bits entirely. This is both smaller and clearer:
acceptance means every child constraint holds.

Bounded quantifiers unroll over their public finite range. Witness-indexed early
exit is forbidden. An existential proof may, however, use a bounded witness index
plus a selector/range proof when only existence is claimed; this is a proof
witness optimization and is not equivalent to encrypted search.

The generic compiler theorem should have both directions:

```lean
theorem lowerProof_sound
    (h : Satisfied2 hash (lowerProof cfg phi).descriptor minit mfin maddrs trace) :
    evalFormula env phi = true

theorem lowerProof_complete
    (h : evalFormula env phi = true) :
    Exists fun trace =>
      Satisfied2 hash (lowerProof cfg phi).descriptor minit mfin maddrs trace
```

Soundness is the acceptance bar. Completeness prevents a compiler that rejects
valid formulas and is necessary before calling this a compilation rather than a
sound recognizer.

`RelationalClosure.constraintBudget` and
`ArithmeticClosure.constraintBudget` are useful source-size upper bounds, but
they are not yet a generic emitted-descriptor compiler. The closure lane is
complete only when `Satisfied2` refinement is proved for the emitted descriptor,
as the existing per-predicate `*Refine.lean` files do.

## 5. FHE lowering

The FHE target is a typed plan, not the current convex `Expr` grammar. The current
fhIR reject list is correct for an optimizer: arbitrary disjunction,
secret-indexed memory, and secret products must not be smuggled into the cheap
convex class. Add a sibling `LogicPlan` and let its compiler select an explicit
carrier:

### 5.1 `BfvResidual`

Use for a certified positive/no-wrap fragment.

- atom residuals are encrypted integers;
- conjunction/universal is ciphertext addition;
- disjunction/existential is a balanced multiplication tree only when the
  multiplication/noise certificate admits it;
- the output is a residual; custodians run one equality-to-zero decision at the
  declared boundary.

This is where the corrected Gabbay construction materially helps fhEgg: a
universal over thousands of already-nonnegative residuals is an additive fold,
which matches `bfv_lean::fold`, `gpu_arena::ResidentFoldPlan`, and the collective
BFV path. It does not make comparison or residual construction free.

### 5.2 `BfvBoolean`

Use when inputs are already encrypted canonical bits with a proof/same-opening
certificate. AND/OR reduce with balanced multiplication trees. SIMD-pack the bits
and reduce slots with rotations. This avoids a PBS per connective but consumes
BFV multiplicative depth and relinearization.

### 5.3 `TfheBoolean`

Use for comparisons, zero tests, negation/table LUTs, and mixed Boolean logic.
The actual resident scalar-greater-than adapter consumes sixteen radix-4 blocks
for `u32` and executes a sixteen-PBS state chain; it should be costed as
`CmpScalar(32)`, not as one abstract comparison. Keep the state and LUTs resident
with `greater_than_scalar_resident`.

### 5.4 `BfvThenMpc`

Use the live fhEgg cut: BFV performs the additive/SIMD work, threshold custodians
derive shares only at the result boundary, and PartyMPC performs equality or
comparison. `fhegg-fhe/src/fhir/private_box.rs` already has reveal-only
`run_equality` and `run_comparison` shapes. This is usually superior to sending a
large BFV aggregate through a TFHE crossing.

The FHE correctness theorem should be phrased over primitive operation laws, as
`Market.FhEggRustDenotation.TfheU32PrimitiveLaws` already demonstrates:

```lean
theorem lowerFhe_correct
    (laws : PrimitiveLaws ops)
    (hnw : PlanNoWrap plan)
    (hsrc : RustPlanRefines plan rustPlan) :
    decryptResult ops key (rustPlan.run key (encryptEnv env)) =
      evalFormula env phi
```

For residual plans the conclusion is instead
`decryptResidual(...) = 0 <-> evalFormula env phi = true`.

## 6. Backend cost algebras

Do not collapse costs to one number or market a context-free multiplier.

```text
ProofCost =
  rows, traceWidth, maxDegree, mulGates, boolGates, rangeBits,
  lookups, hashLookups, witnessCells, publicInputs, challenges

FheCost =
  bfAdds, publicScalarMuls, ctCtMuls, mulDepth, rotations,
  pbsChains(width), lutPbs, keySwitches, relins,
  noiseBound, plaintextAbsBound, slots,
  uploads, downloads, openedBits
```

Sequential composition adds work counts and dependency depth. Parallel composition
adds work counts but takes the maximum dependency depth. Bounds and noise compose
with the carrier's proved arithmetic, not with an informal heuristic. Leakage is a
separate manifest; it is never traded against runtime silently.

Backend selection is constrained optimization:

1. discard candidates that fail type, same-opening, no-wrap/noise, resource, or
   leakage checks;
2. Pareto-prune the remaining cost vectors;
3. select with a calibrated deployment policy (latency, memory, bandwidth, or
   proof-size weights).

This extends `FhIRAdmissible.Manifest`: add exact logic capabilities and the two
cost vectors rather than weakening its existing `publicOps`, `boundedDims`,
`noIntegrality`, and `traceIndepCert` promises.

## 7. Correct optimization rewrites

Every rewrite returns a denotation proof and a cost inequality under explicit
premises.

- associative balancing: turn product/Boolean reductions into balanced trees;
  semantics is associativity, FHE depth becomes `ceil(log2 n)`;
- zero-residual simplification: in a field/product-only context, compile equality
  to `x-y`, not `(x-y)^2`. For `exists i, x_i=y_i`, reduce the raw differences
  first and test the one product for zero; squaring every leaf adds work but no
  soundness;
- universal residual fusion: `sum(map residual xs)` becomes a resident/SIMD fold;
  premise is nonnegative residuals plus a no-wrap bound on every partial sum;
- quantifier slot packing: pack a public finite range, then rotate-reduce;
  premise pins the slot layout and padding identity;
- atom hoisting/CSE: evaluate a repeated atom once; premise is identical source
  environment and visibility label;
- public function-table one-hot lowering: replace secret indexing by
  `sum_i selector_i * table_i`, with Boolean selectors and `sum selectors=1`;
- TFHE table lowering: one public LUT/PBS for a small unary table;
- proof-side lookup lowering: replace interpolation with an authenticated table
  row and lookup argument;
- existential witness lowering on the proof side: replace full scan by a bounded
  index and selected body proof. Never apply this to FHE computation, which must
  find the result without a prover-chosen witness;
- boundary deferral: retain a BFV residual through all additive work and perform
  one zero/comparison decision in MPC at egress;
- Boolean dualization/De Morgan: choose the form with fewer expensive operations
  only after proving the backend's bit representation canonical.

Polynomial interpolation should be selected only when its measured
multiplication depth/work beats one-hot, lookup, or PBS. Gabbay's existence proof
that a finite function has a polynomial representation is not a cost theorem.

## 8. Same-opening is the composition keystone

Two correct pipelines can still process different inputs. The joint result needs
a relation tying the record/commitment opened in `Satisfied2` to the exact
ciphertext plaintext under the declared BFV/TFHE parameters.

```lean
structure SameOpening (env : Env Gamma) (stmt : ProofStatement)
    (cipherInputs : CipherInputs) : Prop where
  proofRootOpens : ...
  cipherOpens : ...
  valuesEqual : ...
  parameterDigestEqual : ...
  rangeEqual : ...
```

Then the useful dual theorem is:

```lean
theorem proof_fhe_agree
    (hsame : SameOpening env stmt cts)
    (hproof : ProofAccepts proofPlan stmt proof)
    (hfhe : FheRunCorrect fhePlan cts out) :
    decrypt out = true
```

The hiding proof relation should be authoritative for the sealed source; the FHE
program is an untrusted evaluator until same-opening is proved. A hash of two
unrelated byte strings is not this theorem.

## 9. First pilot: the existing `QuantifiedPredicate`

Do not begin with arbitrary HOL. Begin with the two discriminating examples
already proved in `Dregg2.Authority.QuantifiedPredicate`.

### 9.1 `allBelowCap`

Source: `forall i in [0,1,2], q[i] <= capacity`.

- existing source theorem: `forall_eq_andFold` and `compile_sound`;
- proof lowering: open the record once, emit three `capacity-q[i]` range gadgets,
  and top-level-conjoin by accepting all three rows. Prove `Satisfied2 ->
  allBelowCap.evalClear rec = true`; add a complete honest trace and the existing
  `qBad` refusal;
- encrypted computation: this atom is a comparison, so a raw positive residual
  is not free. If `capacity` is public, select `TfheBoolean` (three scalar
  comparison chains, therefore 48 radix-block PBS transitions for the current
  `u32` resident adapter, then Boolean reduction). If `capacity` is secret, that
  scalar adapter is not sufficient; use a generic ciphertext comparison or
  `BfvThenMpc` (share the differences and run comparisons). A
  `BfvResidual` plan is admissible only if the caller supplies independently
  validated nonnegative violation residuals and their same-opening proof.

This pilot stops the compiler from pretending that signed inequality is equality
to zero.

### 9.2 `anyIsFive`

Source: `exists i in [0,1,2], q[i] = 5`.

- proof lowering: either three equality false bits and their product, or a
  bounded witness index plus selected equality proof;
- BFV lowering: compute the balanced product of the three raw differences
  `(q[i]-5)` over a proved prime plaintext carrier, then make one
  equality-to-zero decision at egress. This is two ciphertext multiplications at
  multiplicative depth two for `N=3`; the per-leaf squares are unnecessary.
  Product-zero is sound in a field; no conjunction-sum premise is used;
- TFHE alternative: three equality/zero LUTs followed by encrypted OR.

The pilot's joined theorem is:

```lean
theorem quantified_dual_agreement (p : QuantPred Nat)
    (hp : SupportedPilot p) (hsame : SameOpening ...) :
    ProofAccepts (compileProof p) ... <->
    decrypt (runFhe (compileFhe p) ...) = true
```

Both `qOk` and `qBad` must exercise both sides. Report the exact proof and FHE cost
vectors for both examples.

## 10. Build order

1. Add the intrinsically typed finite logic AST and Boolean evaluator in Lean.
2. Add adapters from `RelPred` and `QuantPred`; prove evaluator preservation.
3. Implement the `allBelowCap` proof compiler into a new isolated descriptor and
   prove `Satisfied2` soundness/completeness with both-polarity traces.
4. Define the four FHE plan carriers and the symbolic cost algebras in Lean; give
   transparent primitive-law models for non-vacuity.
5. Implement `anyIsFive` as prime-product BFV residual plus one MPC equality
   boundary; prove the residual theorem and primitive-law refinement.
6. Emit canonical Lean plans; Rust strictly decodes them. Do not hand-author a
   semantic twin in Rust.
7. Build and prove the same-opening relation before advertising a joined result.
8. Generalize finite vectors to finite function tables, then closure
   conversion/defunctionalization for the bounded higher-order fragment.

The success criterion for the first milestone is not “FOL maps to polynomials.”
It is: one existing quantified predicate, one Lean-authored proof relation, one
Lean-specified encrypted execution, an exact same-input theorem, both truth
values witnessed, and cost manifests that explain why each backend choice was
made.
