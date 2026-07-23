# DESIGN — range/lookup-table faithfulness in the `Satisfied2` carrier

Status: read-only scoping (2026-07-23). No code changed. Site counts are the deliverable measurement.

## TL;DR — this is a MODELING GAP, not a live vuln

The deployed Rust circuit **fully enforces** range-table faithfulness. The Lean carrier `Satisfied2`
does **not**, so the abstract accept-set is strictly looser than the deployed accept-set. Every
soundness argument that passes through a range/lookup tooth therefore carries an `hrange`-shaped
premise (`t.tf .range = rangeRows bits`) that the loose carrier supplies as a free lever instead of a
structural fact. The fix shape already exists (`Satisfied2Faithful.rangeTableFaithful`) and is already
consumed by the rotation/refinement rungs; the residual is that the **base** carrier and the
per-descriptor statement predicates still take the honest-range obligation as an explicit premise.

## The hole, precisely

`Dregg2/Circuit/DescriptorIR2.lean:649` — `structure Satisfied2` carries table-faithfulness for two of
the shared tables and **omits** the third:

```
memTableFaithful : t.tf .memory = (memLog d t).map opRow      -- line 659
mapTableFaithful : t.tf .mapOps = mapLog d t                  -- line 660
-- NO field pinning t.tf .range  NOR  t.tf .poseidon2
```

A lookup's denotation (`Lookup.holdsAt`, `DescriptorIR2.lean:488`) is membership against **whatever the
prover put in that table**:

```
def Lookup.holdsAt (tf) (env) (l) : Prop := l.tuple.map (·.eval env.loc) ∈ tf l.table
```

For a range lookup `l.table = .range`, and `tf .range` is a free witness field of `VmTrace`. So a
forged `.range` table whose rows include an out-of-range value (e.g. `[2013265920]` alongside the
honest `[0, 2^30)` rows) makes the membership hold for a value the range check is supposed to reject.
`lookup_replaces_range` (`DescriptorIR2.lean:1431`) makes the dependence explicit: it can only conclude
`VmRange.holds` **given** the hypothesis `hr : tf .range = rangeRows bits`.

The falsifier's §0 (`Dregg2/Verify/DirectLogicAdversarialFalsifierV2.lean:63-127`) is the authoritative
statement of this and names the concrete residual: `borderWrapClaim` passes with a forged range table
because it is refused by the range tooth alone, so its refusal genuinely needs `HonestRangeTable`.
`wrapClaim` survives an arbitrary `tf .range` because it is refused by the linear atoms, which read no
table. That file's `StatementSatisfied` already carries `HonestRangeTable trace` as an *explicit
premise* precisely because `Satisfied2` will not supply it.

`Satisfied2Public` does **not** close it: its `PublicTablesFaithful` leg is
`TableDef.publicContentsFaithful` (`DescriptorIR2.lean:452`), which is `True` at a `.rangeLimb` sem
(only `.exactPublicRows` tables are pinned; a 30-bit range table cannot be carried as descriptor-literal
rows). Confirmed against the source.

## The fix shape — already exists

`Dregg2/Circuit/Satisfied2Faithful.lean:109` — `structure Satisfied2Faithful extends Satisfied2` adds
the two missing conjuncts as **structural fields** (not free levers):

```
chipTableFaithful  : ChipTableSoundN permOut (t.tf .poseidon2)   -- the poseidon2 chip table
rangeTableFaithful : t.tf .range = rangeRows BAL_LIMB_BITS        -- the range table
```

`ChipTableReduction.lean:305` (`chip_and_range_faithful_of_honest` / `tableFaithfulness_of_arith_and_
range`) derives **both** conjuncts from the named `Poseidon2ChipArithSound` floor + acceptance +
the structural range equation — no fresh opaque floor. So the machinery to discharge the conjunct at
the emit boundary is present. `Satisfied2Faithful` is **not orphaned**: it is imported/consumed by 27
Lean files, including the deployed `RotatedKernelRefinement*` family and `EffectVmEmitRotationV3`.

## The multi-width nuance (do not under-scope the fix)

`rangeTableFaithful` pins only the canonical `.range` (30-bit `BAL_LIMB_BITS`). The wide graduation
lowers non-30-bit range teeth into **width-tagged custom tables**: `rangeTidW bits = .custom
(RANGE_W_TID_BASE + bits)` (`EffectVmEmitV2.lean:1607`; Rust `RANGE_W_TID_WIRE_BASE = 69`,
`CUSTOM_RANGE_WIDTHS = [15, 16]`). The honest pin for those is the **family** form already stated in
`EffectVmEmitV2.lean:1614`: `∀ b ∈ WIDE_RANGE_WIDTHS, tf (rangeTidW b) = rangeRows b`. A single-field
fix pinning only `.range` leaves the 15-bit availability-weld borrow limbs and 16-bit note-spend lanes
looking into an unpinned `.custom` table. The correct faithfulness conjunct is the per-width family, not
the scalar equation.

## Does the deployed Rust already enforce it? YES — fully

`circuit/src/descriptor_ir2.rs`:

1. **Content pinned.** `Ir2Air::ByteTable` (line 3060): `value = row index` — `when_first_row` asserts
   `local[0] = 0`, `when_transition` asserts `next[0] = local[0] + 1`. The table cannot lie about its
   values; range checks ride limb decomposition + LogUp byte queries against this bus, never a
   prover-supplied table.
2. **Height pinned, verify-side.** `verify_vm_descriptor2` (line 6256-6273) refuses any range instance
   whose committed degree ≠ the deployed `BYTE_TABLE_HEIGHT` (`= 1 << LIMB_BITS`), because "a taller
   table widens the limb range." Test `ir2_oversized_byte_table_refuses` (line 7639) commits a
   double-height table and asserts the verifier rejects it.

So the prover cannot forge the range table in the deployed circuit. The honest-table obligation is
discharged **by construction** at the Rust assembly (it *builds* the limb decomposition), which is
outside the Lean carrier. **This is a Lean modeling gap: the abstract `Satisfied2` accept-set is looser
than the real one. It is not an exploit against `verify_vm_descriptor2`.**

## Blast radius (the measurement)

Descriptors (`circuit/descriptors/by-name/*.json`): **52 total, 43 carry a lookup, 13 carry a range
table** — matches the survey.

Lean carrier:
- Base `Satisfied2` **producers** (sites that construct the structure and would need the new field):
  **~62 files, ~85 `rowConstraints :=` / 88 `memTableFaithful :=` constructor sites.**
- Direct **extenders** of base `Satisfied2`: **8** structures — `Satisfied2Public`, `Satisfied2U`,
  `Satisfied2Custom` (DescriptorIR2), `Satisfied2Faithful`, `GraduateWideNarrow`'s, `EffectVmEmitV2`'s
  two, `FiniteLogicDescriptorIR2`'s. (`Satisfied2Staged` in `CustomApex` is a separate `structure`, not
  an extend.)
- Files already **consuming** `Satisfied2Faithful`: **27**.

## Safety — does adding a field red-umbrella the tree?

**Consumers do not break; producers do.** Adding a required field to `Satisfied2` only *strengthens* the
hypothesis, so every theorem taking `h : Satisfied2 …` keeps compiling (it gains a field). There is **no
logical red umbrella on the downstream/consumer side.** What breaks is the ~62 producer files: each must
supply the new `rangeTableFaithful` field. For the honest completeness/non-vacuity witnesses this is
mechanical — their traces are built honest, so `tf .range = rangeRows bits` holds by construction, and
several already prove exactly this (`traceOf_honest_range`, `directTraceOf_honest_range`; helpers exist
in `GabbayDescriptorIR2`, `GabbayDescriptorIR2PublicBinding`, `PresentationRefine`, `RangeProof`). For
the **adversarial** producers (the falsifier's forged-range counterexample), the field is
*unsatisfiable* — which is the whole point: the tightened carrier excludes exactly those traces.

Two real hazards, not umbrellas:
1. **Duplicate-field collision.** `Satisfied2Faithful` already declares `rangeTableFaithful`; adding the
   same field to the base makes it a re-declaration. A base-field fix must delete the derived duplicate
   (and reconcile the `BAL_LIMB_BITS` literal vs the width-family form).
2. **Under-coverage of custom-width tables** (see the multi-width nuance): pinning only `.range` is
   incomplete.

## The precise fix (recommended shape)

Do **not** bolt a scalar `t.tf .range = rangeRows BAL_LIMB_BITS` field onto base `Satisfied2` — it
under-covers the wide/custom range widths and collides with the existing derived field. Instead:

**Option R (range-faithful extension, additive, low-risk):** introduce one carrier conjunct expressing
the *per-width family* honest-range fact —
`rangeFamilyFaithful : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b` — and make it the
carrier the **per-descriptor soundness statements** (the falsifier's `StatementSatisfied` and the 43
lookup-bearing by-name descriptors' statements) quantify over, exactly as the rotation rungs already
route through `Satisfied2Faithful`. Discharge the conjunct at the emit/assembly boundary via the
existing `tableFaithfulness_of_arith_and_range` / `rangeTidW_pins_subsume_bal` lemmas. This moves the
premise from a free lever to a structural conjunct without touching the ~62 base producers.

**Option B (fold into base `Satisfied2`):** add the family field to base `Satisfied2`, delete
`Satisfied2Faithful.rangeTableFaithful`'s scalar duplicate, and fix ~85 producer sites. Higher churn,
uniform result. Only worth it if the goal is that *no* `Satisfied2` witness can ever be range-loose.

Either way, note the honest-table fact ultimately discharges at the Rust assembly (outside the Lean
carrier); porting the premise into the carrier **moves** it to the emit boundary, it does not delete it.
The correspondence lemma "the Rust `ByteTable` AIR + height pin ⟹ `rangeFamilyFaithful`" is the true
floor and is currently a modeling correspondence, not a Lean theorem.

## Severity verdict

MODELING GAP (deployed Rust is sound), not a live exploit. Severity = faithfulness debt: the Lean
accept-set is looser than the deployed one, so range-dependent Lean soundness conclusions are
conditional on a premise the loose carrier omits. Uniform across the codebase (every range lookup reads
`t.tf .range`). The repair is a carrier tightening, not a security patch.
