/-
# Dregg2.Verify.RangeFamilyFaithfulRoute — routing the Gabbay descriptor's soundness through a
per-width RANGE-FAMILY faithfulness conjunct (design doc: `docs/DESIGN-range-table-faithfulness.md`,
Option R).

## The hole this closes (a MODELING GAP, not a live vuln)

`DescriptorIR2.Satisfied2` pins the memory and map-ops auxiliary tables (`memTableFaithful`,
`mapTableFaithful`) but NOT the range/lookup table. A range lookup's denotation
(`Lookup.holdsAt`) is membership against `t.tf .range` — a FREE witness field — so a prover can
forge a `.range` table whose rows include an out-of-range value and every emitted range tooth
still passes. `DirectLogicAdversarialFalsifierV2.§0` is the authoritative statement of this and
names the concrete residual: `borderWrapClaim` (input `2^30 - 1 = 2013265920`, a genuine field
wrap of the successor equation) is refused by the RANGE TOOTH ALONE, so its refusal genuinely
needs the honest-range premise. `StatementSatisfied` therefore already carries the SCALAR
`HonestRangeTable trace` (`t.tf .range = rangeRows 30`) as an explicit premise.

## Severity — settled by reading the deployed Rust

The deployed circuit ENFORCES range-table faithfulness on the wire. `circuit/src/descriptor_ir2.rs`
`Ir2Air::ByteTable` fixes `value = row index` (`when_first_row` asserts `local[0] = 0`,
`when_transition` asserts `next[0] = local[0] + 1`), so the table cannot lie about its values; and
`verify_vm_descriptor2` refuses any range instance whose committed degree differs from the deployed
`BYTE_TABLE_HEIGHT = 1 << LIMB_BITS` (test `ir2_oversized_byte_table_refuses`). The honest-table
obligation is discharged BY CONSTRUCTION at Rust assembly (it BUILDS the limb decomposition),
which is outside the Lean carrier. So this is a Lean MODELING GAP — the abstract accept-set is
looser than the deployed one — NOT an exploit against `verify_vm_descriptor2`.

## What this file lands (Option R, additive, no base-carrier change)

The scalar `HonestRangeTable` under-covers the wide graduation: non-30-bit range teeth lower into
width-tagged custom tables (`rangeTidW bits`), whose honest pin is the FAMILY form
`∀ b ∈ WIDE_RANGE_WIDTHS, tf (rangeTidW b) = rangeRows b` (`EffectVmEmitV2`). This file:

  * `RangeFamilyFaithful` — the reusable per-width-family carrier conjunct, quantifying over
    `WIDE_RANGE_WIDTHS = [15, 30]` (the 15-bit availability-weld borrow limbs beside the 30-bit
    balance limbs), the way the rotation rungs route through `Satisfied2Faithful.rangeTableFaithful`.
  * `RangeFamilyFaithful.honestRangeTable` — the family conjunct SUBSUMES the scalar
    (`rangeTablesWide_range`: `rangeTidW BAL_LIMB_BITS = .range`), so any statement routed through it
    keeps the 30-bit guarantee the Gabbay teeth need.
  * `StatementSatisfiedFamily` / `statement_sound_family` — the Gabbay descriptor's soundness routed
    THROUGH the family carrier: a forged range table is no longer admissible, because the carrier
    pins the honest interval at every allowed width.
  * `borderWrap_family_statement_refused`, `wrapClaim_family_statement_refused` — the two falsifier
    counterexamples, refused under the family-routed statement. `borderWrapClaim`-with-a-forged-range
    is inadmissible.
  * NON-VACUITY: `successor_family_statement_has_witness` — the TRUE successor table still has a
    live family-honest witness, so the refusals reject the counterexample rather than everything.
    The witness populates both range widths via `familyTables`; `satisfied2_public_tf_congr` transfers
    the existing `direct_trace_complete` proof across the `.range`/`.memory`/`.mapOps`-agreeing tf.

The honest-table fact ultimately discharges at the Rust assembly; routing the premise into the
carrier MOVES it to the emit boundary (dischargeable via `range_table_faithful_of_structural` /
`tableFaithfulness_of_arith_and_range`), it does not delete it. This does NOT add a field to the
base `Satisfied2` (which would red-umbrella ~62 producers) — it routes the SOUNDNESS STATEMENTS.

## Remaining consumers (named, not landed here)

The 43 lookup-bearing by-name descriptors' soundness statements each still route through bare
`Satisfied2` or the scalar `HonestRangeTable`; porting them to `RangeFamilyFaithful` is the same
two-line pattern (`statement_sound_family`). The base-carrier fold (Option B) and the Rust↔Lean
correspondence lemma "`ByteTable` AIR + height pin ⟹ `RangeFamilyFaithful`" remain.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Verify.DirectLogicAdversarialFalsifierV2
import Dregg2.Circuit.Emit.EffectVmEmitV2

namespace Dregg2.Verify.RangeFamilyFaithfulRoute

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmRange)
open Dregg2.Metatheory.GabbayMatrixSemantics
open Dregg2.Metatheory.GabbayDescriptorIR2
open Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding
open Dregg2.Verify.DirectLogicAdversarialFalsifierV2
open Dregg2.Circuit.Emit.EffectVmEmitV2 (WIDE_RANGE_WIDTHS rangeTidW RANGE_W_TID_BASE
  rangeTablesWide_range rangeTidW_bal)

set_option autoImplicit false

/-! ## §1 — the reusable per-width-family faithfulness carrier + the scalar subsumption. -/

/-- **`RangeFamilyFaithful t`** — the per-width range-table faithfulness conjunct: at EVERY allowed
range width `b ∈ WIDE_RANGE_WIDTHS`, the trace's width-tagged range table (`rangeTidW b`) is the
genuine honest interval `rangeRows b`. This is the carrier the per-descriptor SOUNDNESS statements
quantify over, moving the honest-range obligation from a free lever to a structural conjunct — the
family form (not the scalar `.range` pin), so the wide graduation's 15-bit borrow limbs and 30-bit
balance limbs are BOTH covered. -/
def RangeFamilyFaithful (t : VmTrace) : Prop :=
  ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b

/-- The family conjunct SUBSUMES the scalar `HonestRangeTable` (`rangeTidW BAL_LIMB_BITS = .range`,
and `BAL_LIMB_BITS = WIRE_BITS = 30`). So a statement routed through `RangeFamilyFaithful` keeps the
30-bit honest-interval guarantee the Gabbay range teeth read. -/
theorem RangeFamilyFaithful.honestRangeTable {t : VmTrace} (h : RangeFamilyFaithful t) :
    HonestRangeTable t := by
  have hbal := rangeTablesWide_range (tf := t.tf) h
  -- `hbal : t.tf .range = rangeRows BAL_LIMB_BITS`; `HonestRangeTable` is the same at `WIRE_BITS`,
  -- and `BAL_LIMB_BITS` and `WIRE_BITS` are both `30` (defeq).
  exact hbal

/-! ## §2 — the Gabbay descriptor's soundness, routed THROUGH the family carrier. -/

/-- **`StatementSatisfiedFamily`** — the Gabbay public statement relation with its honest-range
premise carried as the per-width FAMILY conjunct `RangeFamilyFaithful` rather than the scalar
`HonestRangeTable`. Everything else is unchanged (`withPublic` swaps only the public statement). -/
def StatementSatisfiedFamily (hash : List Int -> Int) (claim : ThreeEntryTable)
    (trace : VmTrace) : Prop :=
  trace.rows ≠ [] /\ RangeFamilyFaithful trace /\
    Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace)

/-- The family-routed statement implies the scalar-premised `StatementSatisfied`: soundness is
MONOTONE in the premise, so the family conjunct (strictly stronger) discharges it. -/
theorem StatementSatisfiedFamily.toStatement {hash : List Int -> Int} {claim : ThreeEntryTable}
    {trace : VmTrace} (h : StatementSatisfiedFamily hash claim trace) :
    StatementSatisfied hash claim trace :=
  ⟨h.1, h.2.1.honestRangeTable, h.2.2⟩

/-- **Soundness, routed through the family conjunct.** A canonical claim with a family-honest
satisfying witness genuinely `Holds`: the forged-range lever is gone because `RangeFamilyFaithful`
pins the honest interval at every allowed width. -/
theorem statement_sound_family (hash : List Int -> Int) (claim : ThreeEntryTable)
    (hclaim : CanonicalTable claim) (trace : VmTrace)
    (hs : StatementSatisfiedFamily hash claim trace) :
    Holds (sourceValuation claim) 0 successorSkolemFormula :=
  statement_sound hash claim hclaim trace hs.toStatement

/-! ## §3 — the falsifier counterexamples, refused under the family-routed statement. -/

/-- **`borderWrapClaim`-with-a-forged-range is inadmissible.** The border wrap
(`input 0 = 2013265920`, a real field wrap of the successor equation refused by the range tooth
ALONE) has NO family-honest satisfying trace: routing through `RangeFamilyFaithful` closes the
forged-range escape the scalar carrier left open. -/
theorem borderWrap_family_statement_refused (hash : List Int -> Int) :
    ¬ (∃ trace, StatementSatisfiedFamily hash borderWrapClaim trace) := by
  intro hex
  exact borderWrapClaim_not_holds
    (statement_sound_family hash borderWrapClaim borderWrapClaim_canonical
      hex.choose hex.choose_spec)

/-- **The BabyBear sum-of-squares cancellation, refused under the family-routed statement too.**
`wrapClaim` is killed by the linear atoms (table-free), so it survives any `tf .range`; routing
through the family conjunct keeps it refused, so neither half of the repair masks the other. -/
theorem wrapClaim_family_statement_refused (hash : List Int -> Int) :
    ¬ (∃ trace, StatementSatisfiedFamily hash wrapClaim trace) := by
  intro hex
  exact wrapClaim_not_holds
    (statement_sound_family hash wrapClaim wrapClaim_canonical
      hex.choose hex.choose_spec)

/-! ## §4 — NON-VACUITY: the true successor table still has a family-honest witness.

`familyTables` populates BOTH allowed range widths (the 30-bit shared `.range` and the 15-bit
width-tagged `.custom (RANGE_W_TID_BASE + 15)`), so it satisfies `RangeFamilyFaithful`. It agrees
with the existing `traceTables` at `.range`/`.memory`/`.mapOps`, so `satisfied2_public_tf_congr`
transfers the honest completeness proof across. This shows the family refusals reject the
counterexample, not every statement. -/

/-- The family-honest auxiliary tables: the genuine interval at every allowed range width. -/
def familyTables : TraceFamily := fun tid =>
  match tid with
  | .range => rangeRows WIRE_BITS
  | .custom n => if n = RANGE_W_TID_BASE + 15 then rangeRows 15 else []
  | _ => []

/-- The honest witness trace with BOTH range widths populated (rows/pub from `directTraceOf`). -/
def familyTraceOf (table : ThreeEntryTable) : VmTrace :=
  { directTraceOf table with tf := familyTables }

theorem familyTables_rangeFamilyFaithful (table : ThreeEntryTable) :
    RangeFamilyFaithful (familyTraceOf table) := by
  intro b hb
  simp only [WIDE_RANGE_WIDTHS, BAL_LIMB_BITS, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · -- b = 15: `rangeTidW 15 = .custom (RANGE_W_TID_BASE + 15)`, and `familyTables` pins it to
    -- `rangeRows 15` (unfold the defs; `rangeRows` is never expanded).
    have htid : rangeTidW 15 = TableId.custom (RANGE_W_TID_BASE + 15) := if_neg (by decide)
    simp only [familyTraceOf, familyTables, htid, RANGE_W_TID_BASE, if_pos]
  · -- b = 30 = BAL_LIMB_BITS: `rangeTidW 30 = .range`, pinned to `rangeRows WIRE_BITS = rangeRows 30`.
    have htid : rangeTidW 30 = TableId.range := rangeTidW_bal
    simp only [familyTraceOf, familyTables, htid, WIRE_BITS]

/-- **The tf-congruence for `publicDescriptor`.** Its constraints read `tf` only through the six
`.range` range lookups, its `memLog`/`mapLog` are empty, and its `hashSites`/`ranges` are empty. So
`Satisfied2` transfers across any `tf` agreeing at `.range`/`.memory`/`.mapOps` (with equal
rows/pub). This is the reusable lemma that lets an honest witness populate additional width tables
harmlessly. -/
theorem satisfied2_public_tf_congr {hash : List Int -> Int} {t1 t2 : VmTrace}
    (hrows : t2.rows = t1.rows) (hpub : t2.pub = t1.pub)
    (hrange : t2.tf .range = t1.tf .range)
    (hmem : t2.tf .memory = t1.tf .memory)
    (hmap : t2.tf .mapOps = t1.tf .mapOps)
    (h : Satisfied2 hash publicDescriptor (fun _ => 0) (fun _ => ((0 : Int), 0)) [] t1) :
    Satisfied2 hash publicDescriptor (fun _ => 0) (fun _ => ((0 : Int), 0)) [] t2 := by
  have henv : ∀ i, envAt t2 i = envAt t1 i := by
    intro i; simp only [envAt, hrows, hpub]
  -- the per-constraint tf-congruence: `publicDescriptor`'s constraints read tf only at `.range`.
  have hcongr : ∀ (c : VmConstraint2), c ∈ publicDescriptor.constraints →
      ∀ (env : VmRowEnv) (isF isL : Bool),
        (c.holdsAt hash t2.tf env isF isL ↔ c.holdsAt hash t1.tf env isF isL) := by
    intro c hc env isF isL
    simp only [publicDescriptor, publicConstraints, publicPins, publicAtoms,
      publicRangeLookups, rangeLookup, always, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [VmConstraint2.holdsAt, Lookup.holdsAt, hrange]
  refine ⟨?_, ?_, ?_, h.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [hrows] at hi
    rw [henv i, hrows]
    exact (hcongr c hc (envAt t1 i) _ _).2 (h.rowConstraints i hi c hc)
  · intro i _hi
    trivial
  · intro i _hi r hr
    simp [publicDescriptor] at hr
  · intro op hop
    rw [memLog_publicDescriptor] at hop
    cases hop
  · rw [memLog_publicDescriptor]; trivial
  · rw [memLog_publicDescriptor]; exact memCheck_nil _ _
  · rw [memLog_publicDescriptor, List.map_nil, hmem]
    have h2 := h.memTableFaithful
    rwa [memLog_publicDescriptor, List.map_nil] at h2
  · rw [mapLog_publicDescriptor, hmap]
    have h2 := h.mapTableFaithful
    rwa [mapLog_publicDescriptor] at h2

/-- **NON-VACUITY.** The true successor table has a family-honest satisfying witness — so the
family-routed refusals above reject the counterexamples specifically, not every statement. -/
theorem successor_family_statement_has_witness (hash : List Int -> Int) :
    ∃ trace, StatementSatisfiedFamily hash successorEntries trace := by
  refine ⟨familyTraceOf successorEntries, ?_, familyTables_rangeFamilyFaithful successorEntries, ?_⟩
  · simp [familyTraceOf, directTraceOf]
  · -- transfer the honest completeness proof across `familyTables` (agrees at `.range`/mem/map).
    have hbase := direct_trace_complete hash successorEntries
      successorEntries_wireBounded successorEntries_holds
    refine satisfied2_public_tf_congr (t1 := directTraceOf successorEntries)
      (t2 := withPublic successorEntries (familyTraceOf successorEntries))
      ?_ ?_ ?_ ?_ ?_ hbase
    · simp [withPublic, familyTraceOf, directTraceOf]
    · simp [withPublic, familyTraceOf, directTraceOf]
    · -- `.range`: both `familyTables` and `traceTables` pin it to `rangeRows WIRE_BITS`.
      simp only [withPublic, familyTraceOf, familyTables, directTraceOf, traceTables]
    · -- `.memory`: empty in both.
      simp only [withPublic, familyTraceOf, familyTables, directTraceOf, traceTables]
    · -- `.mapOps`: empty in both.
      simp only [withPublic, familyTraceOf, familyTables, directTraceOf, traceTables]

/-! ## §5 — axiom hygiene. -/

#assert_axioms RangeFamilyFaithful.honestRangeTable
#assert_axioms statement_sound_family
#assert_axioms borderWrap_family_statement_refused
#assert_axioms wrapClaim_family_statement_refused
#assert_axioms satisfied2_public_tf_congr
#assert_axioms successor_family_statement_has_witness

end Dregg2.Verify.RangeFamilyFaithfulRoute
