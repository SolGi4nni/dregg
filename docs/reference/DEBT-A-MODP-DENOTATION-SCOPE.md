# DEBT-A — the ℤ→mod-p AIR denotation refactor (scope + grounding)

## 0. The finding (given)

The deployed Effect-VM AIR is a constraint system over BabyBear, whose prime is
`p = 2013265921`; Rust names that modulus and defines every `BabyBear` operation by reduction
modulo `p` (`circuit/src/field.rs:1-17`, `:263-287`, `:290-359`).  The Lean descriptor denotation,
however, takes an `Assignment := Nat → ℤ` (`metatheory/Dregg2/Circuit.lean:52-74`), evaluates emitted
expressions in `ℤ` (`metatheory/Dregg2/Exec/CircuitEmit.lean:116-126`), and asks for literal integer
zero (`metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:277-284`).  These are different solution sets.

This document takes the established counterexample as given.  The deployed
`dregg-accumulator-nonrev-emit-v2` descriptor contains the affine gate
`diff[0] - alpha_aux[0] + hash[0]`, i.e. columns `12 - 32 + 0`
(`metatheory/Dregg2/Circuit/Emit/AccumulatorNonRevocationEmit.lean:104-111`, `:145-150`, `:168-178`).
At canonical representatives `(col12,col32,col0) = (p-1,0,1)`, the BabyBear result is zero while the
integer result is `p ≠ 0`.  The already-committed field beachhead independently proves the general
phenomenon: canonical inputs do not prevent a gate residual from being `p` in `ℤ` and `0` in BabyBear
(`metatheory/Dregg2/Circuit/FieldIntegerLift.lean:93-138`), and proves that field acceptance does not
imply the old integer `MainAirAccept` (`:144-168`).

Therefore the old `Satisfied2` solution set is a strict subset of the deployed field solution set.
The implication chain from the deployed verifier to old `MainAirAccept`/`Satisfied2` cannot be
inhabited in general; this is modeling vacuity, not merely a missing theorem
(`metatheory/Dregg2/Circuit/AirChecksSatisfied.lean:209-235`, `:269-310`).

## 1. Benign-gap check (is a canonicalization invariant enforced?)

**Verdict: no invariant closes the gap.  The refactor is required.**

There is a real but insufficient invariant on the Rust side:

- The production trace generator returns `Vec<Vec<BabyBear>>` and BabyBear public inputs
  (`circuit/src/effect_vm/trace.rs:81-103`, `:389-409`).  The IR-v2 assembler accepts and stores all
  main and auxiliary traces in that type (`circuit/src/descriptor_ir2.rs:3570-3582`, `:3630-3652`).
- `BabyBear::new`, `new_canonical`, deserialization, addition, subtraction, and multiplication all
  reduce modulo `p` (`circuit/src/field.rs:74-87`, `:100-132`, `:290-359`).  The receipt wire exports
  the in-memory trace as `u32` field cells (`turn/src/witnessed_receipt.rs:110-125`, `:153-165`).

Thus the Rust prover does emit reduced field elements.  But reduction of **operands** is not a bound
on the unreduced integer **polynomial residual**.  The affine deployed gate above reaches exactly
`p` from three canonical operands (`AccumulatorNonRevocationEmit.lean:104-111`).  The committed lift
file says the same thing structurally: its subtraction lift needs explicit representative bounds,
and notes that `VmTrace` does not carry them (`FieldIntegerLift.lean:29-48`).

There is no Lean boundary invariant to add the missing fact.  `VmTrace` is only a list of unrestricted
integer assignments, an unrestricted integer public assignment, and integer tables
(`metatheory/Dregg2/Circuit/DescriptorIR2.lean:423-435`).  `envAt` merely selects those rows; it does
not reduce or cast them (`:437-443`).  `Satisfied2` adds row constraints, range teeth explicitly
listed by the descriptor, and memory/table conditions, but no all-column canonicality or
all-residual centered-range field (`:599-617`).  Some production paths validate particular semantic
limbs, but explicitly say those checks are prover-side and do not add universal STARK constraints
(`circuit/src/effect_vm/trace.rs:400-425`); IR-v2 likewise range-checks only descriptor-declared wires
(`circuit/src/descriptor_ir2.rs:3647-3659`).

The existing Rust denotational differential deliberately avoids this case: its independent Lean
oracle is over `i128`, and its corpus keeps values much smaller than `p` so reduction is never
load-bearing (`circuit/tests/ir2_denotational_differential.rs:83-104`, `:106-142`).  It therefore
cannot supply a theorem that every deployed residual is literally zero in `ℤ`.

The benign-gap fork is consequently closed: canonical Rust cells exist, but the stronger invariant
needed to validate the integer denotation does not.  It is also false for a deployed gate, so adding
it as a purported well-formedness premise would exclude valid BabyBear witnesses rather than model
the deployed AIR.

## 2. The ℤ-denotation surface (file:line)

The hard-coded surface is:

| Definition | Integer commitment |
|---|---|
| `Assignment` | `Nat → ℤ` (`metatheory/Dregg2/Circuit.lean:52-58`). |
| `EmittedExpr.eval` | Returns `Int`; both arithmetic constructors use integer `+`/`*` (`metatheory/Dregg2/Exec/CircuitEmit.lean:116-122`). |
| `VmRowEnv` | `loc`, `nxt`, and `pub` are all the integer `Assignment` (`metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:257-267`). |
| `VmGate.holds` | Requires `body.eval env.loc = 0` in `ℤ` (`EffectVmEmit.lean:277-284`). |
| `VmConstraint.holdsVm` | Gate/boundary bodies require integer zero; transitions and PI pins require integer equality (`EffectVmEmit.lean:431-447`). |
| `WindowExpr.eval` | Returns `ℤ` and evaluates both rows with integer arithmetic (`metatheory/Dregg2/Circuit/DescriptorIR2.lean:323-349`). |
| `WindowConstraint.holdsAt` | Requires that integer evaluation to be exactly zero (`DescriptorIR2.lean:360-376`). |
| `Table`, `TraceFamily`, `VmTrace`, `envAt` | Tables, rows, and public inputs remain integer-valued; `envAt` performs no reduction (`DescriptorIR2.lean:423-443`). |
| `Lookup.holdsAt` | Compares integer-evaluated tuples with integer table rows (`DescriptorIR2.lean:445-448`). |
| `MapOp.rowAt`/`mapLog` | Builds integer rows from integer expression evaluation and tests the integer guard against `1` (`DescriptorIR2.lean:565-573`). |
| `VmConstraint2.holdsAt` | Delegates arithmetic arms to integer `holdsVm`/`holdsAt`; lookup and map arms also receive integer environments (`DescriptorIR2.lean:575-597`). |
| `Satisfied2.rowConstraints` | Quantifies `VmConstraint2.holdsAt` over every row; all other row/table carriers are still attached to the same integer trace (`DescriptorIR2.lean:599-617`). |
| `arithResidual` | Returns `ℤ`; every base/window residual is calculated with integer arithmetic (`metatheory/Dregg2/Circuit/AirChecksSatisfied.lean:90-113`). |
| `MainAirAccept` | Its quotient and zerofier are integer-valued, and its identity is an equality in `ℤ` (`AirChecksSatisfied.lean:209-224`). |

Two already-committed definitions are the correct beachhead rather than part of the defect:
`MainAirAcceptF` asks for the cast residual to vanish in BabyBear
(`metatheory/Dregg2/Circuit/FieldIntegerLift.lean:50-57`), and `constraintPoly` is genuinely a
`Polynomial BabyBear` whose row evaluation is the BabyBear image of the old residual
(`metatheory/Dregg2/Circuit/TraceColumnInterp.lean:69-90`, `:170-204`).

## 3. The ripple (consumers, classified)

### Census and counting rule

At HEAD, the reproducible exact-token census is:

```text
rg -l -w 'Satisfied2|holdsAt|holdsVm' Dregg2 -g '*.lean' | sort -u

Satisfied2: 147 files / 2143 token occurrences
holdsAt:     93 files /  683 token occurrences
holdsVm:    145 files / 1084 token occurrences
union:      220 distinct Lean files
```

This is an intentionally conservative **migration upper bound**: token occurrences include comments
and proof scripts, while the 220-file union answers which files can be made stale by a semantic rename
or changed simp normal form.  The classification below is mutually exclusive and sums to 220.

| Class | Files | What changes | Criticality |
|---|---:|---|---|
| (i) Recent DEBT-A AIR chain | 3 | `AirChecksSatisfied`, `AirLegsDischarged`, `AlgoStarkSoundInstance`.  They explicitly route `MainAirAccept` through `holdsAt` to `Satisfied2` (`AirChecksSatisfied.lean:239-295`; `AirLegsDischarged.lean:145-190`; `AlgoStarkSoundInstance.lean:138-180`). | **Soundness-critical and currently vacuous in application.** |
| (ii) Apex / `StarkSound` / circuit-soundness path | 17 | `CircuitSoundness{,Assembled}`, all eight `Closure*` files, `CustomApex`, `DescriptorRefinesComplete`, `FriVerifier{,Bridge}`, `GroundedApex`, `NormalizeToShapeSound`, and `AssuranceCaseGrounded`.  The load-bearing target is `StarkSound.extract : accept → ∃ …, Satisfied2 …` (`CircuitSoundness.lean:375-387`), and `descriptorRefines` consumes that witness (`:225-239`). | **Soundness-critical.** The apex theorem remains a valid implication, but its deployed premise is not realizable until restated over the field denotation. |
| (iii) Per-effect descriptor/refinement family | 179 | 132 files under `Circuit/Emit/`, 19 `RotatedKernel*`, 11 `Deos/`, 6 `Circuit/Argus/`, 3 `Satisfied2Faithful*`, plus 8 isolated refinement/support files.  Representative consumers extract integer equations from `holdsAt` using `linear_combination` (`AccumulatorNonRevocationRefine.lean:278-335`); `Satisfied2Faithful` literally extends old `Satisfied2` (`Satisfied2Faithful.lean:95-118`). | **Soundness-critical for each deployed descriptor**, though emitters that only construct syntax are incidental until their refinement theorem consumes the denotation. |
| (iv) Completeness/non-vacuity | 14 | The 12 `CircuitCompleteness*` files plus `WitnessRealizing` and `FloorsNonVacuous`.  Concrete old witnesses are constructed both vacuously on an empty trace (`CircuitCompletenessNonVacuity.lean:105-137`) and meaningfully on a nonempty transfer trace (`CircuitCompletenessNonVacuityReal.lean:571-680`). | **Not needed for the soundness implication**, but required to show the replacement denotation and gate sets are inhabited. |
| Core/decider/support | 7 | `DescriptorIR2`, `FieldIntegerLift`, `DecideSatisfied2{,Golden}`, `DecideMapMerkle`, `LogUpSoundness`, `MapMerkleRoot`.  The current decider explicitly decides integer zero and integer table membership (`DecideSatisfied2.lean:55-103`, `:113-150`). | Mixed: core definitions are critical; goldens and deciders are validation infrastructure. |

The 17-file apex set is identifiable directly from the proof spine: `CircuitSoundness` opens
`Satisfied2` (`CircuitSoundness.lean:87-90`), assembled soundness describes the per-effect
`Satisfied2 → Encode` readout (`CircuitSoundnessAssembled.lean:35-50`), and `FriVerifierBridge`
states that verifier acceptance must yield a `Satisfied2` witness
(`metatheory/Dregg2/Circuit/FriVerifierBridge.lean:75-85`).  The 179-file descriptor class is not
incidental bulk: proofs routinely unfold `EmittedExpr.eval` and use ordered-ring tactics on the
result (`AccumulatorNonRevocationRefine.lean:278-335`; `AdjacencyMembershipRefine.lean:114-122`).
Those proof arguments are precisely where a field cutover can require mathematical reworking rather
than a type rename.

## 4. Migration plan (A1 vs A2, step list, blast radius, riskiest step)

### A1: immediate mutation

A1 changes `VmRowEnv`, expression evaluation, `holdsVm`/`holdsAt`, `VmTrace`, and `Satisfied2` in
place to concrete BabyBear semantics.  It is the cleanest final API, but it invalidates the stable
reduction interface that per-effect proofs intentionally consume (`EffectVmEmit.lean:449-457`) and
immediately exposes the 220-file union.  Expected edit blast radius: **roughly 185-220 Lean files**;
the lower end assumes many syntax-only/comment references survive and compatibility simp lemmas absorb
some callers.  It also makes the DEBT-A, apex, descriptor, and completeness changes inseparable.

### A2: additive field denotation, then deliberate retirement

Recommend A2.  This introduces no new soundness assumption or typeclass carrier: every new definition
is concrete over the already-modeled `BabyBear` (`TraceColumnInterp.lean:20-29`).  The steps are:

1. Beside the old definitions, add field evaluation for `EmittedExpr` and `WindowExpr`, plus
   `VmConstraint.holdsVmF`, `WindowConstraint.holdsAtF`, and `VmConstraint2.holdsAtF`.  Constants are
   cast and `+`/`*` occur in BabyBear.  Keep the wire syntax unchanged; only denotation changes
   (`CircuitEmit.lean:99-108`, `DescriptorIR2.lean:332-358`).
2. Add `Satisfied2F` with field-valued row constraints.  Preserve the non-arithmetic memory/map/hash
   meaning deliberately, converting canonical field cells only at their semantic boundary; do not
   pretend raw integer polynomial equality survives.  `Satisfied2`'s nine fields provide the exact
   checklist (`DescriptorIR2.lean:606-617`).
3. Prove the field analogue of `arithResidual_zero_forces_holdsAt` and route existing
   `MainAirAcceptF`/`OodInterpF` into `Satisfied2F.rowConstraints`.  The interpolation theorem already
   lands in BabyBear (`FieldIntegerLift.lean:55-90`; `TraceColumnInterp.lean:195-204`).
4. Re-state `AirLegsDischarged` and `AlgoStarkSoundInstance` against `MainAirAcceptF` and
   `Satisfied2F`; delete no integer theorem yet (`AirLegsDischarged.lean:145-190`;
   `AlgoStarkSoundInstance.lean:146-180`).
5. Change `StarkSound.extract`, `descriptorRefines`, and the assembled apex to target `Satisfied2F`
   (`CircuitSoundness.lean:225-239`, `:375-387`).  Migrate the 17-file apex slice and keep an explicit
   no-old-`Satisfied2` gate on this path.
6. Migrate descriptor proofs in cohorts.  Reprove semantic integer conclusions from field equations
   only where the descriptor's actual range/canonical decomposition justifies the lift.  Do not use a
   blanket field-to-integer premise: `VmRange.holds` is descriptor-local
   (`EffectVmEmit.lean:397-405`), and the accumulator descriptor has no legacy `ranges`
   (`AccumulatorNonRevocationEmit.lean:168-178`).
7. Rebuild the 14 completeness/non-vacuity witnesses for `Satisfied2F`, including a nonempty
   wraparound-sensitive witness; the current meaningful witness is at
   `CircuitCompletenessNonVacuityReal.lean:571-680`.
8. Update `DecideSatisfied2` and the Rust differential to execute field arithmetic.  In particular,
   remove the differential's “values much smaller than p” escape hatch
   (`circuit/tests/ir2_denotational_differential.rs:83-104`) and add the deployed affine counterexample.
9. Once the apex and all deployed registry descriptors are field-only, rename the `F` definitions to
   the canonical names and retire the integer AIR denotation.  Keep integer encodings only where they
   are semantic data, not where they stand for field evaluation.

The additive beachhead is **about 7-12 Lean files** through step 4.  The apex cut is another **17
files**.  A complete retirement still approaches the **220-file upper bound**, with **179 descriptor
files** dominating.  A2 changes sequencing and reviewability, not the final amount of proof work.

**Riskiest step: step 6, the per-effect refinement cutover.**  Existing theorems use `linarith`,
`omega`, `linear_combination`, integer order, and `Int.toNat` after unfolding `holdsAt`; examples are
`AccumulatorNonRevocationRefine.lean:270-335`, `AdjacencyMembershipRefine.lean:114-122`, and
`DeployedCapTree.lean:568-569`.  Field equality alone does not support those ordered-ring conclusions.
Each proof must show that its semantic decoding/range teeth make the required lift valid, or state its
conclusion in the field.  This is the point most likely to uncover further underconstrained descriptors.

### Theorem disposition

- `MainAirAccept`, `mainAirAccept_forces_residual`, `mainAirAccept_forces_rowConstraints`, and
  `airAccept_forces_satisfied2` are internally valid integer theorems
  (`AirChecksSatisfied.lean:220-235`, `:239-310`) but **not theorems about deployed acceptance**.  Re-state
  them over BabyBear; retain old versions only as clearly named integer-model lemmas until retirement.
- `airAccept_forces_satisfied2_transferV3` and `airAccept_forces_satisfied2_allArith` inherit the same
  vacuity and must be re-stated (`AirLegsDischarged.lean:145-190`).
- `AlgoStarkSoundInstance`'s extraction hypotheses and construction must use `MainAirAcceptF` and
  `Satisfied2F` (`AlgoStarkSoundInstance.lean:117-180`).
- `StarkSound.extract` must be **re-stated**, not bridged from field acceptance to old `Satisfied2`
  (`CircuitSoundness.lean:375-387`).  The present `lightclient_unfoolable` family is logically true
  under its old class hypothesis but vacuous for the deployed verifier; it must be re-proved after the
  class target changes (`CircuitSoundness.lean:471-485`).
- Old per-effect `Satisfied2 → spec` theorems can remain true because their premise is stronger than
  field satisfaction, but they are insufficient for deployed soundness.  They need field versions;
  `descriptorRefines` is the registry-wide consumer (`CircuitSoundness.lean:225-239`).
- Existing old-`Satisfied2` completeness witnesses remain valid witnesses of the stronger integer
  predicate, but do not establish non-vacuity of the new soundness target.  Construct parallel field
  witnesses before retiring them (`CircuitCompletenessNonVacuity.lean:105-137`;
  `CircuitCompletenessNonVacuityReal.lean:571-680`).
- `MainAirAcceptF`, `OodInterpF`, `ood_forces_mainAirAccept_field`, and `constraintPoly` are reusable
  as written (`FieldIntegerLift.lean:50-90`; `TraceColumnInterp.lean:170-204`).

## 5. Beyond the AIR

The commitment tower itself is **not** affected by this particular mismatch.  `recStateCommit` is a
semantic application of abstract hash/compression functions, and its equalities are equalities of
commitment outputs backed by explicit injectivity hypotheses (`metatheory/Dregg2/Circuit/StateCommit.lean:180-220`,
`:280-284`).  `CommitSurface` packages those functions and binding facts; it does not evaluate an AIR
polynomial or assert that an integer residual models a BabyBear residual
(`metatheory/Dregg2/Circuit/CircuitSoundness.lean:105-150`).  Do **not** change `StateCommit`, kernel
balances, conservation sums, or abstract hash codomains merely because they use `ℤ`.

There is, however, a second modeling surface worth a separate audit.  The older generic circuit IR
openly calls `ℤ` a “field stand-in”: `Assignment`, `Expr.eval`, `Constraint.holds`, and `satisfied` are
all integer semantics (`metatheory/Dregg2/Circuit.lean:52-91`), and `satisfiedEmitted` preserves those
semantics (`metatheory/Dregg2/Exec/CircuitEmit.lean:114-157`).  Higher-level predicates such as
`satisfiedS` and `satisfiedE` consume that generic satisfaction relation
(`StateCommit.lean:323-362`; `EffectCommit.lean:331-358`).  If any of those predicates is claimed as
the direct denotation of a deployed field constraint system, the same wraparound question applies.
They are not the `StarkSound.extract → Satisfied2` path scoped in this document
(`CircuitSoundness.lean:375-387`), so they should receive a follow-up census rather than be folded into
this flag day.

Likewise, not every `= 0` over `ℤ` is suspect.  Kernel conservation and balance equations describe
integer-valued protocol quantities, while lookup membership and commitment equality describe semantic
relations.  The defect criterion is narrower: an integer equality is being used as the denotation of
a deployed BabyBear `assert_zero` polynomial.  On the current apex, that criterion selects the
descriptor row semantics and `MainAirAccept`, not the state-commitment or kernel-spec tower
(`DescriptorIR2.lean:589-617`; `AirChecksSatisfied.lean:90-113`, `:220-224`).

## 6. Recommendation

Proceed with **A2, staged-additive then cut over**, and treat it as required rather than optional.  The
Rust canonical-value invariant is real, but it cannot make the deployed three-term affine residual
literally zero in `ℤ` (`circuit/src/field.rs:14-17`; `AccumulatorNonRevocationEmit.lean:104-111`).

Gate the work in this order: concrete field denotation → field AIR chain → 17-file apex cut → deployed
descriptor cohorts → field non-vacuity/differential → retirement.  Do not introduce a new assumed
soundness carrier, and do not try to rescue old `Satisfied2` with a universal residual-bound premise;
the deployed gate refutes that premise.  A2 keeps the first reviewable slice to roughly 7-12 files,
while acknowledging that full retirement is a 185-220-file proof migration dominated by the 179-file
descriptor family.  The key acceptance condition is grep-zero for old `Satisfied2` on the
`StarkSound`/apex path, plus a differential case whose residual is `p` in `ℤ` and zero in BabyBear
(`CircuitSoundness.lean:375-387`; `circuit/tests/ir2_denotational_differential.rs:83-104`).
