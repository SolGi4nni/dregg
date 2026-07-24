/-
# Dregg2.Circuit.ShieldedValueRangeDischarge — the in-AIR `VALUE_BITS` range gadget: the
# §C no-wraparound bound of `emitted_conservation_int` DISCHARGED against an emitted object.

**This is Lean-authored AIR.** `ShieldedSpendPortResidual.emitted_conservation_int` lifts the
value-link's mod-p conservation (`Σ value ≡ Σ out_val [ZMOD p]`) to ℤ EQUALITY under a NAMED
no-wraparound bound (both prefix sums in `[0, p)`). This module authors the range gadget that
FORCES that bound and discharges it: the hypothesis becomes a proved fact about the emitted
descriptor.

## The gadget (reuse, not reinvention)

The Rust shape is `shielded_ring_clearing_nleg_air.rs:397-408` / `VALUE_BITS = 27` (line 130):
every conservation value bit-decomposed so it provably lies in `[0, 2^VALUE_BITS)`, with
`N · 2^VALUE_BITS ≤ p` asserted at descriptor-build time (`15 · 2^27 = p − 1`). In the Lean IR
the PROVEN range mechanism is range-by-lookup (`DescriptorIR2` §8, "kills the range-bit
columns"), and the 27-bit table already EXISTS: `LexCompare8Emit`'s `.custom LEX_RANGE_TID`
table (`lexRangeTableDef`, content contract `tf (.custom LEX_RANGE_TID) = rangeRows 27`). So
`shieldedValueLinkRangedDesc` is the value-link descriptor PLUS two lookups per row —
`value ∈ [0, 2^27)`, `out_val ∈ [0, 2^27)` — against that SAME shared table. Zero new columns,
zero new tables, no bit-decomposition re-authored.

## What is PROVED

  * **`ranged_satisfies_base`** — constraint-superset transport: a satisfying ranged trace
    satisfies the plain value-link descriptor, so every landed value-link/conservation theorem
    applies unchanged.
  * **`emitted_values_in_range`** — the gadget's tooth, sound direction: on a satisfying trace
    (against the faithful 27-bit table) EVERY row's `value` and `out_val` lie in
    `[0, 2^VALUE_BITS)`.
  * **`emitted_prefix_sums_bounded`** — with row count ≤ `MAX_CLEARING_ROWS = 15`
    (`15 · 2^27 = p − 1`), both conservation prefix sums land in `[0, p)` — the exact bound
    `emitted_conservation_int` names.
  * **⚑ `emitted_conservation_int_ranged`** — THE DISCHARGE: `Σ value = Σ out_val` in ℤ, no
    range hypothesis — it is proved from the emitted object. Remaining hypotheses are
    STRUCTURAL, not crypto: the range-table content contract (`rangeRows` is definitionally
    `[0, 2^27)` — `ChipTableReduction` records this is not a crypto lever) and the clearing
    width `≤ 15` (the Rust `ring_no_wrap_ok` build-time assert).
  * **`wraparound_mint_int_unsat`** — the ℤ tooth: an integer-unbalanced trace is UNSAT
    against the ranged descriptor even when it is FIELD-balanced.
  * **The load-bearing canary** — `wrapMintTrace` mints `p` units disguised as 0
    (`Σ value = 0`, `Σ out_val = p`, field-conserving since `p ≡ 0`):
    `wraparound_mint_accepted_by_base` proves the PLAIN descriptor ACCEPTS it;
    `wraparound_mint_refused_by_ranged` proves the ranged descriptor REFUSES it. The gadget is
    the thing standing between field conservation and an over-mint — proved, not asserted.
  * **Non-vacuity** — `honest_ranged_satisfies`: the value-link module's honest balanced 2-row
    witness (5+3 in, 4+4 out) satisfies the RANGED descriptor (its values are in range);
    `conservation_int_fires_on_ranged_witness` runs the discharged ℤ-lift on it.

## What stays open (honest)

This lane closes ONLY the §C range residual. Still open from the residual module's list: the
§D wide-value-binding structural lane; the §D Ristretto-retire deploy; the §B
`FoldReachIsMember` Poseidon2 second-preimage floor; the Rust producer/emit wiring + VK regen.
The full 64-bit amount range stays the off-AIR carrier exactly as in Rust (`VALUE_BITS = 27`
caps in-AIR amounts; the deployed cap discipline is unchanged by this lane).

## Axiom hygiene

Additive: a new descriptor + bridge theorems; no deployed descriptor/registry touch. No new
crypto floor enters — this lane REMOVES a named hypothesis. `#assert_axioms` ⊆ {propext,
Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.ShieldedSpendPortResidual
import Dregg2.Circuit.Emit.LexCompare8Emit

namespace Dregg2.Circuit.ShieldedValueRangeDischarge

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TableDef TraceFamily VmTrace zeroAsg
   envAt Satisfied2 rangeRows range_row_mem_iff memLog mapLog memOpsOf mapOpsOf opRow
   emitVmJson2)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)
open Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor
open Dregg2.Circuit.Emit.LexCompare8Emit (LEX_RANGE_TID lexRangeTableDef)
open Dregg2.Circuit.ShieldedSpendPortResidual (P emitted_conservation_int)

set_option autoImplicit false

/-! ## §1 — the ranged descriptor: the value-link block + two 27-bit range lookups per row. -/

/-- The in-AIR range-gadget bit width — the Rust `VALUE_BITS = 27`
(`shielded_ring_clearing_nleg_air.rs:130`; `p = 15·2^27 + 1`). -/
def VALUE_BITS : Nat := 27

/-- The no-wrap clearing width: `MAX_CLEARING_ROWS · 2^VALUE_BITS = p − 1` — the Lean twin of
the Rust `ring_no_wrap_ok` build-time assert at its maximal `N`. -/
def MAX_CLEARING_ROWS : Nat := 15

/-- Per-row range lookup: the input `value` cell lies in the 27-bit table. -/
def lkValRange : VmConstraint2 := .lookup ⟨.custom LEX_RANGE_TID, [.var cVAL]⟩

/-- Per-row range lookup: the `out_val` cell lies in the 27-bit table. -/
def lkOutRange : VmConstraint2 := .lookup ⟨.custom LEX_RANGE_TID, [.var cOUT]⟩

/-- The ranged constraint list: the two range lookups + the whole value-link block. -/
def rangedConstraints : List VmConstraint2 :=
  lkValRange :: lkOutRange :: linkClearConstraints

/-- **`shieldedValueLinkRangedDesc`** — the value-link + Σ-conservation descriptor with the
in-AIR `VALUE_BITS` range gadget welded on (the §C residual's emitted object). Reuses the
LexCompare8 27-bit range table (`.custom LEX_RANGE_TID`, content contract
`tf = rangeRows 27`); same trace width, same PIs. Staged-additive: no deployed descriptor or
registry entry changes here. -/
def shieldedValueLinkRangedDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-value-link-conserve-ranged::v1"
  , traceWidth  := VLINK_WIDTH
  , piCount     := VLINK_PI_COUNT
  , tables      := [lexRangeTableDef]
  , constraints := rangedConstraints
  , hashSites   := []
  , ranges      := [] }

-- Non-vacuous structural pins; the BabyBear identity making 15 the exact no-wrap width.
#guard shieldedValueLinkRangedDesc.traceWidth == 9
-- E7 narrowing: the two `hash_fact` sites ride the 18-wide `TID_P2_NARROW` bus, so the 2 x 7
-- exposed permutation lane columns are gone (pure tail truncation, no index moved).
#guard shieldedValueLinkRangedDesc.traceWidth
         + 2 * (Dregg2.Circuit.DescriptorIR2.CHIP_OUT_LANES - 1) == 23
#guard shieldedValueLinkRangedDesc.piCount == 2
#guard shieldedValueLinkRangedDesc.constraints.length == 11
#guard decide ((MAX_CLEARING_ROWS : ℤ) * 2 ^ VALUE_BITS + 1 = P)

/-! ## §2 — transport: a ranged witness satisfies the plain value-link descriptor. -/

private theorem memOpsOf_ranged_nil : memOpsOf shieldedValueLinkRangedDesc = [] := rfl
private theorem memOpsOf_base_nil : memOpsOf shieldedValueLinkDesc = [] := rfl
private theorem mapOpsOf_ranged_nil : mapOpsOf shieldedValueLinkRangedDesc = [] := rfl
private theorem mapOpsOf_base_nil : mapOpsOf shieldedValueLinkDesc = [] := rfl

private theorem memLog_ranged_eq (t : VmTrace) :
    memLog shieldedValueLinkRangedDesc t = memLog shieldedValueLinkDesc t := by
  unfold Dregg2.Circuit.DescriptorIR2.memLog
  rw [memOpsOf_ranged_nil, memOpsOf_base_nil]

private theorem mapLog_ranged_eq (t : VmTrace) :
    mapLog shieldedValueLinkRangedDesc t = mapLog shieldedValueLinkDesc t := by
  unfold Dregg2.Circuit.DescriptorIR2.mapLog
  rw [mapOpsOf_ranged_nil, mapOpsOf_base_nil]

/-- **Constraint-superset transport.** A trace satisfying the ranged descriptor satisfies the
plain value-link descriptor — every landed value-link theorem (`value_link_bound`,
`conservation_holds`, both teeth) applies to ranged witnesses unchanged. -/
theorem ranged_satisfies_base (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t) :
    Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t := by
  refine ⟨?_, hsat.rowHashes, hsat.rowRanges, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    exact hsat.rowConstraints i hi c
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
  · intro op hop
    exact hsat.memClosed op (by rw [memLog_ranged_eq]; exact hop)
  · rw [← memLog_ranged_eq]; exact hsat.memDisciplined
  · rw [← memLog_ranged_eq]; exact hsat.memBalanced
  · rw [← memLog_ranged_eq]; exact hsat.memTableFaithful
  · rw [← mapLog_ranged_eq]; exact hsat.mapTableFaithful

/-! ## §3 — the gadget's tooth: every value cell is 27-bit-bounded. -/

/-- **The range tooth (sound direction).** On a satisfying ranged trace, against the faithful
27-bit table (`rangeRows` is DEFINITIONALLY `[0, 2^27)` — the content contract, not a crypto
floor), EVERY row's `value` and `out_val` lie in `[0, 2^VALUE_BITS)`. -/
theorem emitted_values_in_range (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t)
    (hrt : t.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS) :
    ∀ i, i < t.rows.length →
      (0 ≤ valAt t i ∧ valAt t i < 2 ^ VALUE_BITS)
      ∧ (0 ≤ outAt t i ∧ outAt t i < 2 ^ VALUE_BITS) := by
  intro i hi
  have hv := hsat.rowConstraints i hi lkValRange
    (by simp [shieldedValueLinkRangedDesc, rangedConstraints])
  have ho := hsat.rowConstraints i hi lkOutRange
    (by simp [shieldedValueLinkRangedDesc, rangedConstraints])
  simp only [lkValRange, lkOutRange, Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, List.map_cons, List.map_nil,
    EmittedExpr.eval, envAt] at hv ho
  rw [hrt] at hv ho
  have hv' := (range_row_mem_iff _ VALUE_BITS).mp hv
  have ho' := (range_row_mem_iff _ VALUE_BITS).mp ho
  exact ⟨by simpa [valAt, rowAt] using hv', by simpa [outAt, rowAt] using ho'⟩

/-- Out-of-range `value` cell ⇒ UNSAT (the tooth, refusal direction). -/
theorem out_of_range_value_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hrt : t.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS)
    (i : Nat) (hi : i < t.rows.length)
    (hbad : ¬ (0 ≤ valAt t i ∧ valAt t i < 2 ^ VALUE_BITS)) :
    ¬ Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t :=
  fun hsat => hbad (emitted_values_in_range hash minit mfin maddrs t hsat hrt i hi).1

/-- Out-of-range `out_val` cell ⇒ UNSAT (the tooth, refusal direction). -/
theorem out_of_range_out_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hrt : t.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS)
    (i : Nat) (hi : i < t.rows.length)
    (hbad : ¬ (0 ≤ outAt t i ∧ outAt t i < 2 ^ VALUE_BITS)) :
    ¬ Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t :=
  fun hsat => hbad (emitted_values_in_range hash minit mfin maddrs t hsat hrt i hi).2

/-! ## §4 — bounded prefix sums: `≤ 15` in-range rows cannot wrap mod p. -/

/-- In-range summands bound the running sum: `0 ≤ prefixSum f n < (n + 1) · B`. -/
theorem prefixSum_nonneg_lt (f : Nat → ℤ) (B : ℤ) :
    ∀ n, (∀ i, i ≤ n → 0 ≤ f i ∧ f i < B) →
      0 ≤ prefixSum f n ∧ prefixSum f n < ((n : ℤ) + 1) * B := by
  intro n
  induction n with
  | zero =>
      intro h
      have h0 := h 0 (Nat.le_refl 0)
      refine ⟨by simpa [prefixSum] using h0.1, ?_⟩
      have he : (((0 : Nat) : ℤ) + 1) * B = B := by norm_num
      rw [he]
      simpa [prefixSum] using h0.2
  | succ m ih =>
      intro h
      have hm := ih (fun i hi => h i (Nat.le_succ_of_le hi))
      have hs := h (m + 1) (Nat.le_refl _)
      constructor
      · simpa [prefixSum] using add_nonneg hm.1 hs.1
      · have hexp : (((m + 1 : Nat) : ℤ) + 1) * B = ((m : ℤ) + 1) * B + B := by
          push_cast; ring
        rw [hexp, show prefixSum f (m + 1) = prefixSum f m + f (m + 1) from rfl]
        exact add_lt_add hm.2 hs.2

/-- **The no-wraparound bound, DISCHARGED.** On a satisfying ranged trace of at most
`MAX_CLEARING_ROWS = 15` rows, both conservation prefix sums land in `[0, p)` — exactly the
named hypothesis of `emitted_conservation_int` (`15 · 2^27 = p − 1`). -/
theorem emitted_prefix_sums_bounded (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t)
    (hrt : t.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS)
    (hlen : t.rows.length ≤ MAX_CLEARING_ROWS) :
    (0 ≤ prefixSum (valAt t) (t.rows.length - 1)
      ∧ prefixSum (valAt t) (t.rows.length - 1) < P)
    ∧ (0 ≤ prefixSum (outAt t) (t.rows.length - 1)
      ∧ prefixSum (outAt t) (t.rows.length - 1) < P) := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have hrange := emitted_values_in_range hash minit mfin maddrs t hsat hrt
  have hval := prefixSum_nonneg_lt (valAt t) (2 ^ VALUE_BITS) (t.rows.length - 1)
    (fun i hi => (hrange i (by omega)).1)
  have hout := prefixSum_nonneg_lt (outAt t) (2 ^ VALUE_BITS) (t.rows.length - 1)
    (fun i hi => (hrange i (by omega)).2)
  have hlift : ((t.rows.length - 1 : Nat) : ℤ) + 1 ≤ (MAX_CLEARING_ROWS : ℤ) := by
    have hx : t.rows.length - 1 + 1 ≤ MAX_CLEARING_ROWS := by omega
    exact_mod_cast hx
  have hBpos : (0 : ℤ) ≤ 2 ^ VALUE_BITS := by positivity
  have hcap : (((t.rows.length - 1 : Nat) : ℤ) + 1) * 2 ^ VALUE_BITS
      ≤ (MAX_CLEARING_ROWS : ℤ) * 2 ^ VALUE_BITS :=
    mul_le_mul_of_nonneg_right hlift hBpos
  have hP : (MAX_CLEARING_ROWS : ℤ) * 2 ^ VALUE_BITS < P := by decide
  exact ⟨⟨hval.1, ((lt_of_lt_of_le hval.2 hcap).trans hP)⟩,
         ⟨hout.1, ((lt_of_lt_of_le hout.2 hcap).trans hP)⟩⟩

/-! ## §5 — ⚑ THE DISCHARGE: ℤ conservation with no range hypothesis. -/

/-- **⚑ THE §C DISCHARGE (`emitted_conservation_int_ranged`).** A satisfying trace of the
ranged descriptor (≤ 15 rows, faithful 27-bit table) conserves in ℤ:
`Σ value = Σ out_val` EXACTLY — `emitted_conservation_int`'s named no-wraparound bound is now
a PROVED consequence of the emitted object's own range lookups. The remaining hypotheses are
structural, not crypto: the range-table content contract and the build-time clearing width. -/
theorem emitted_conservation_int_ranged (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t)
    (hrt : t.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS)
    (hlen : t.rows.length ≤ MAX_CLEARING_ROWS) :
    prefixSum (valAt t) (t.rows.length - 1) = prefixSum (outAt t) (t.rows.length - 1) := by
  obtain ⟨⟨hV0, hVp⟩, hO0, hOp⟩ :=
    emitted_prefix_sums_bounded hash minit mfin maddrs t hne hsat hrt hlen
  exact emitted_conservation_int hash minit mfin maddrs t hne
    (ranged_satisfies_base hash minit mfin maddrs t hsat) hV0 hVp hO0 hOp

/-- **The ℤ mint tooth.** An integer-unbalanced trace — even a FIELD-balanced one (a
wraparound mint) — admits no satisfying assignment against the ranged descriptor. -/
theorem wraparound_mint_int_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hrt : t.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS)
    (hlen : t.rows.length ≤ MAX_CLEARING_ROWS)
    (hforge : prefixSum (valAt t) (t.rows.length - 1)
      ≠ prefixSum (outAt t) (t.rows.length - 1)) :
    ¬ Satisfied2 hash shieldedValueLinkRangedDesc minit mfin maddrs t :=
  fun hsat =>
    hforge (emitted_conservation_int_ranged hash minit mfin maddrs t hne hsat hrt hlen)

/-! ## §6 — non-vacuity + the load-bearing canary.

One trace family for all witnesses: the honest chip rows, the wrap chip row, and the GENUINE
27-bit table at `.custom LEX_RANGE_TID` (`rangeRows 27` is carried symbolically — membership
facts are proven via `range_row_mem_iff`, the `2^27`-row list is never evaluated). -/

/-- The all-zero `hash_fact` chip row (`hzero` digests/lanes are 0) — the wrap-mint row's
leaf/binding site (value 0, all facts 0). -/
def wrapChipRow : List ℤ :=
  [7, 0, 0, 0, 0, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The WIDE physical Poseidon2 chip rows the canary families name. -/
def rangedChipTbl : List (List ℤ) := [chipL0, chipV0, chipL1, chipV1, wrapChipRow]

/-- The canary trace family: honest + wrap chip rows on ONE physical chip serving TWO buses (the
narrow bus is the 18-prefix, exactly the deployed Rust `narrow_hist`), and the genuine 27-bit range
table. `LEX_RANGE_TID = 27` never collides with `poseidon2narrow = .custom 3`. -/
def rangedTf : TraceFamily := fun tid =>
  if tid = TableId.custom LEX_RANGE_TID then rangeRows VALUE_BITS
  else if tid = TableId.poseidon2 then rangedChipTbl
  else if tid = Dregg2.Circuit.DescriptorIR2.poseidon2narrow then
    Dregg2.Circuit.ChipNarrowLookup.narrowTable rangedChipTbl
  else []

/-- The canary family wires the NARROW bus to the 18-prefix of its wide chip table
(definitional). -/
theorem rangedTf_narrow_wire :
    rangedTf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (rangedTf TableId.poseidon2) := by
  simp [rangedTf, Dregg2.Circuit.DescriptorIR2.poseidon2narrow, LEX_RANGE_TID]

/-- The honest balanced 2-row witness (5+3 in ≡ 4+4 out) over the ranged trace family. -/
def honestRangedTrace : VmTrace := { rows := [honRow0, honRow1], pub := zeroAsg, tf := rangedTf }

/-- The 27-bit-table content contract, discharged for the canary family (via `if_pos` — the
`2^27`-row table itself is never evaluated). -/
theorem rangedTf_custom : rangedTf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS := by
  simp [rangedTf]

theorem rangedTf_range :
    honestRangedTrace.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS := by
  show honestRangedTrace.tf (.custom LEX_RANGE_TID) = rangeRows VALUE_BITS
  simp only [honestRangedTrace]
  exact rangedTf_custom

/-- A range-lookup row obligation discharged symbolically (never evaluating the table). -/
private theorem ranged_range_row (t : VmTrace) (htf : t.tf = rangedTf) (i : Nat) (col : Nat)
    (h0 : 0 ≤ (t.rows.getD i zeroAsg) col)
    (hlt : (t.rows.getD i zeroAsg) col < 2 ^ VALUE_BITS) :
    VmConstraint2.holdsAt hzero t.tf (envAt t i)
      (i == 0) (i + 1 == t.rows.length)
      (.lookup ⟨.custom LEX_RANGE_TID, [.var col]⟩) := by
  show Lookup.holdsAt t.tf (envAt t i) ⟨.custom LEX_RANGE_TID, [.var col]⟩
  unfold Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt
  rw [htf]
  show [(t.rows.getD i zeroAsg) col] ∈ rangedTf (.custom LEX_RANGE_TID)
  rw [rangedTf_custom]
  exact (range_row_mem_iff _ VALUE_BITS).mpr ⟨h0, hlt⟩

/-- **The ranged descriptor is SATISFIABLE by the honest balanced clearing** — the value-link
module's witness values (5, 3 in / 4, 4 out) are 27-bit in-range, so nothing honest is lost. -/
theorem honest_ranged_satisfies :
    Satisfied2 hzero shieldedValueLinkRangedDesc (fun _ => 0) (fun _ => (0, 0)) []
      honestRangedTrace := by
  have hmemlog : memLog shieldedValueLinkRangedDesc honestRangedTrace = [] := rfl
  have hmaplog : mapLog shieldedValueLinkRangedDesc honestRangedTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    have hi2 : i = 0 ∨ i = 1 := by
      have hx : i < 2 := hi
      omega
    simp only [shieldedValueLinkRangedDesc, rangedConstraints, List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · -- the value range lookup: 5 / 3 ∈ [0, 2^27)
      rcases hi2 with rfl | rfl
      · exact ranged_range_row honestRangedTrace rfl 0 cVAL (by decide) (by decide)
      · exact ranged_range_row honestRangedTrace rfl 1 cVAL (by decide) (by decide)
    · -- the out_val range lookup: 4 / 4 ∈ [0, 2^27)
      rcases hi2 with rfl | rfl
      · exact ranged_range_row honestRangedTrace rfl 0 cOUT (by decide) (by decide)
      · exact ranged_range_row honestRangedTrace rfl 1 cOUT (by decide) (by decide)
    · -- the nine value-link constraints: the value-link module's own script, extended tf
      simp only [linkClearConstraints, valueLinkConstraints, conservationConstraints,
        claimPins, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hi2 with rfl | rfl <;>
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [lkLeafCommit, lkValueBinding, accStep, accWindow, wsub, seedBody,
          esub, eadd, emul, eneg, ev, ek,
          Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
          Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt,
          Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt,
          Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm,
          Dregg2.Circuit.DescriptorIR2.WindowExpr.eval,
          envAt, honestRangedTrace, rangedTf, rangedChipTbl,
          Dregg2.Circuit.DescriptorIR2.poseidon2narrow,
          Dregg2.Circuit.ChipNarrowLookup.narrowTable,
          Dregg2.Circuit.ChipNarrowLookup.narrowRow, EmittedExpr.eval,
          List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
        decide
  · -- rowHashes: no hash sites
    intro i _
    exact trivial
  · -- rowRanges: no v1 ranges
    intro i _ r hr
    simp [shieldedValueLinkRangedDesc] at hr
  · -- memAddrsNodup
    simp
  · -- memClosed
    intro op hop
    rw [hmemlog] at hop
    cases hop
  · -- memDisciplined
    rw [hmemlog]
    trivial
  · -- memBalanced
    rw [hmemlog]
    rfl
  · -- memTableFaithful
    rw [hmemlog]
    rfl
  · -- mapTableFaithful
    rw [hmaplog]
    rfl

/-- **The discharged ℤ-lift FIRES on the honest witness** — `8 = 8` with no range hypothesis
supplied from outside: the bound came from the emitted object. -/
theorem conservation_int_fires_on_ranged_witness :
    prefixSum (valAt honestRangedTrace) (honestRangedTrace.rows.length - 1)
      = prefixSum (outAt honestRangedTrace) (honestRangedTrace.rows.length - 1) :=
  emitted_conservation_int_ranged hzero (fun _ => 0) (fun _ => (0, 0)) [] honestRangedTrace
    (by simp [honestRangedTrace]) honest_ranged_satisfies rangedTf_range (by decide)

/-! ### The load-bearing canary: a wraparound mint (field-balanced, ℤ-unbalanced). -/

/-- The wrap-mint row: value 0 in, `out_val = p` out (`Σ value ≡ Σ out_val [ZMOD p]` HOLDS —
`p ≡ 0` — while ℤ conservation is violated by exactly `p`), accumulator threaded `−p`. -/
def wrapMintRow : Assignment := fun j =>
  if j = 7 then 2013265921 else if j = 8 then -2013265921 else 0

/-- The single-row wraparound-mint trace. -/
def wrapMintTrace : VmTrace := { rows := [wrapMintRow], pub := zeroAsg, tf := rangedTf }

-- The canary really is a field-conserving ℤ-mint: Σ value = 0, Σ out_val = p, mod-p balanced.
#guard decide (valAt wrapMintTrace 0 = 0 ∧ outAt wrapMintTrace 0 = 2013265921)
#guard decide (prefixSum (valAt wrapMintTrace) 0
  ≡ prefixSum (outAt wrapMintTrace) 0 [ZMOD 2013265921])
#guard decide (¬ (prefixSum (valAt wrapMintTrace) 0 = prefixSum (outAt wrapMintTrace) 0))

/-- **The plain value-link descriptor ACCEPTS the wraparound mint** — field conservation
cannot see it (`p ≡ 0 [ZMOD p]`). This is the §C hole made concrete: without the range
gadget, a satisfying witness mints `p` units. -/
theorem wraparound_mint_accepted_by_base :
    Satisfied2 hzero shieldedValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) [] wrapMintTrace := by
  have hmemlog : memLog shieldedValueLinkDesc wrapMintTrace = [] := rfl
  have hmaplog : mapLog shieldedValueLinkDesc wrapMintTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by
      have hx : i < 1 := hi
      omega
    subst hi0
    simp only [shieldedValueLinkDesc, linkClearConstraints, valueLinkConstraints,
      conservationConstraints, claimPins, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lkLeafCommit, lkValueBinding, accStep, accWindow, wsub, seedBody,
        esub, eadd, emul, eneg, ev, ek,
        Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt,
        Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm,
        Dregg2.Circuit.DescriptorIR2.WindowExpr.eval,
        envAt, wrapMintTrace, rangedTf, rangedChipTbl,
        Dregg2.Circuit.DescriptorIR2.poseidon2narrow,
        Dregg2.Circuit.ChipNarrowLookup.narrowTable,
        Dregg2.Circuit.ChipNarrowLookup.narrowRow, EmittedExpr.eval,
        List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  · intro i _
    exact trivial
  · intro i _ r hr
    simp [shieldedValueLinkDesc] at hr
  · simp
  · intro op hop
    rw [hmemlog] at hop
    cases hop
  · rw [hmemlog]
    trivial
  · rw [hmemlog]
    rfl
  · rw [hmemlog]
    rfl
  · rw [hmaplog]
    rfl

/-- **The ranged descriptor REFUSES the same wraparound mint** — `out_val = p ∉ [0, 2^27)`.
Together with `wraparound_mint_accepted_by_base` this proves the gadget is LOAD-BEARING: it is
exactly the thing standing between field conservation and an over-mint. -/
theorem wraparound_mint_refused_by_ranged :
    ¬ Satisfied2 hzero shieldedValueLinkRangedDesc (fun _ => 0) (fun _ => (0, 0)) []
      wrapMintTrace :=
  out_of_range_out_unsat hzero (fun _ => 0) (fun _ => (0, 0)) [] wrapMintTrace
    (by simp only [wrapMintTrace]; exact rangedTf_custom) 0 (by decide) (by decide)

/-! ## §7 — the byte-pinned wire golden. -/

/-- Exact emitted-wire golden (generated via `emitVmJson2 shieldedValueLinkRangedDesc`).
Rust includes these bytes verbatim at the coordinated integrator step. -/
def SHIELDED_VALUE_LINK_RANGED_GOLDEN : String :=
  "{\"name\":\"dregg-shielded-value-link-conserve-ranged::v1\",\"ir\":2,\"trace_width\":9,\"public_input_count\":2,\"tables\":[{\"id\":32,\"name\":\"lex_range_27\",\"arity\":1,\"sem\":\"range\",\"bits\":27}],\"constraints\":[{\"t\":\"lookup\",\"table\":32,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"lookup\",\"table\":32,\"tuple\":[{\"t\":\"var\",\"v\":7}]},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":4}},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":5}]},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":6}]},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":4}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":7}}}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":8}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 shieldedValueLinkRangedDesc == SHIELDED_VALUE_LINK_RANGED_GOLDEN

/-! ## §8 — axiom hygiene. -/

#assert_axioms ranged_satisfies_base
#assert_axioms emitted_values_in_range
#assert_axioms out_of_range_value_unsat
#assert_axioms out_of_range_out_unsat
#assert_axioms prefixSum_nonneg_lt
#assert_axioms emitted_prefix_sums_bounded
#assert_axioms emitted_conservation_int_ranged
#assert_axioms wraparound_mint_int_unsat
#assert_axioms honest_ranged_satisfies
#assert_axioms conservation_int_fires_on_ranged_witness
#assert_axioms wraparound_mint_accepted_by_base
#assert_axioms wraparound_mint_refused_by_ranged

end Dregg2.Circuit.ShieldedValueRangeDischarge
