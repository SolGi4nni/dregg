/-
# Dregg2.Circuit.Satisfied2FaithfulActive — the KEYSTONE made WHOLE: ONE active+faithful witness.

## What this unifies (two half-witnesses → one object)

The non-vacuity story for the deployed accept-set was carried by TWO separate witnesses that "composed"
in prose but were never a single term:

  * `FloorsNonVacuous.satisfied2Faithful_transferV3` inhabits the FULL `Satisfied2Faithful` (the genuine
    chip/range faithful tables — `ChipTableSoundN permOutZ` on `.poseidon2`, `rangeRows BAL_LIMB_BITS`
    on `.range`) BUT with ZERO main rows: every per-row Gate/Transition leg is `∀ i < 0`, vacuous. The
    faithful tables are there; the per-row transfer arithmetic NEVER FIRES.
  * `CircuitCompletenessNonVacuityReal.satisfied2_transferV3_real` carries the REAL active transfer row
    (the genuine debit `bal 100 → 90`, the nonce tick `0 → 1`, `amount = 10`, `direction = 1`) so the
    per-row gates GENUINELY bite — BUT it proves only the bare `Satisfied2`, with its auxiliary tables
    built as the rows' OWN evaluated lookup tuples (`tfOf2`, pure membership). No chip/range FAITHFUL
    conjunct: the `.range` table is the membership list, NOT `rangeRows`; the `.poseidon2` table's
    soundness is never asserted.

This module builds the SINGLE term `satisfied2Faithful_transferV3_active` that is BOTH at once:

  * the SAME two-row active trace (`realRow` the genuine debit row, `lastRow` the wrap row carrying
    row 0's after-state) — so the per-row transfer arithmetic gates FIRE, not vacuously;
  * AND a `tf` laying down the GENUINE deployed faithful tables: `.poseidon2` is a `ChipTableSoundN
    permOutZ` table (every row a real `chipRowN permOutZ ins`), `.range = rangeRows BAL_LIMB_BITS`
    (the deployed limb table), `.memory`/`.mapOps = []` (`graduateV1` emits none).

## Why ONE `tf` carries BOTH legs (the empirical reconciliation)

The 40 chip lookups of the live `transferV3` (`graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)`)
each evaluate, on the active rows, to a tuple whose 8-lane OUTPUT block is ALL-ZERO (the digest/lane
columns are high trace columns the active rows never populate). So every evaluated chip tuple IS a genuine
`chipRowN permOutZ ins` row of the all-zero-squeeze genuine permutation `permOutZ` (`FloorsNonVacuous`):
the `Satisfied2` lookup leg (membership) and the `ChipTableSoundN permOutZ` faithful leg are satisfied by
ONE table — the union of the two rows' evaluated chip tuples (which `tfOf2 transferV3 realRow lastRow`
already IS on `.poseidon2`). The two after-balance limb range lookups land at `[90]`/`[0]` (`realRow`) and
`[0]`/`[0]` (`lastRow`), all inside `[0, 2^30)`, so the deployed `rangeRows BAL_LIMB_BITS` table CONTAINS
them (`range_row_mem_iff`) — the `Satisfied2` range leg holds against the GENUINE faithful range table, not
a membership stand-in. So a SINGLE `tf` simultaneously discharges the active per-row lookups AND carries
the chip/range faithfulness as `Satisfied2Faithful` conjuncts.

## The result

`satisfied2Faithful_transferV3_active : Satisfied2Faithful permOutZ permOut0 transferV3 …
activeFaithfulTrace` is the keystone made WHOLE: the full deployed accept-set is inhabited by a REAL
active turn whose per-row transfer gates genuinely fire AND whose chip/range tables are genuinely
faithful — ONE object, not two composed. The collapse recipe `satisfied2Faithful_satisfiedVm` FIRES on
it, flowing to the rung layer with NO free chip/range lever.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The faithful object is a CONSTRUCTED term:
the chip-table soundness is a `decide`-checked structural fact over the concrete two-row chip table (every
row a genuine `chipRowN permOutZ ins`), the range leg is `rangeRows` membership, the per-row gates are the
genuine `CircuitCompletenessNonVacuityReal` discharge. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompletenessNonVacuityReal
import Dregg2.Circuit.FloorsNonVacuous

namespace Dregg2.Circuit.Satisfied2FaithfulActive

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.CircuitCompletenessNonVacuityReal
open Dregg2.Circuit.FloorsNonVacuous (permOutZ permOut0 permOutZ_width permOutZ_lane0)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — the genuine chip-table soundness of the active union table (a `decide`-checked structural fact).

The active `.poseidon2` table is `tfOf2 transferV3 realRow lastRow .poseidon2`: the union of the two
rows' evaluated chip-lookup tuples. EVERY such tuple has an ALL-ZERO 8-lane output block (the digest/lane
columns are high trace columns the active rows leave at `0`), so each IS a genuine `chipRowN permOutZ ins`
row of the all-zero-squeeze genuine permutation `permOutZ`. We capture this as a DECIDABLE per-row
predicate and `decide` the whole concrete table — no `native_decide`, a real kernel-checked enumeration. -/

/-- The unpadded input recovered from a chip row: drop the arity tag, take `arity` entries. -/
def insOf (r : List ℤ) : List ℤ := (r.drop 1).take (r.headD 0).toNat

/-- A row is a GENUINE `chipRowN permOutZ` row: its recovered input fits the rate, and the row IS
`chipRowN permOutZ (its input)` (so its output block is the all-zero squeeze). Decidable for a concrete
row. -/
def genuineChipRowZ (r : List ℤ) : Prop :=
  ChipArityAdmitted (insOf r).length ∧ r = chipRowN permOutZ (insOf r)

instance : DecidablePred genuineChipRowZ := fun r => by unfold genuineChipRowZ; infer_instance

/-- A table all of whose rows are genuine `chipRowN permOutZ` rows is `ChipTableSoundN permOutZ`. -/
theorem soundN_of_all {tbl : Table} (h : ∀ r ∈ tbl, genuineChipRowZ r) :
    ChipTableSoundN permOutZ tbl := by
  intro r hr
  obtain ⟨hlen, heq⟩ := h r hr
  exact ⟨insOf r, hlen, heq⟩

set_option maxRecDepth 8192 in
/-- **The active union chip table is `ChipTableSoundN permOutZ`.** Every one of the two rows' evaluated
chip tuples is a genuine `chipRowN permOutZ ins` row (all-zero squeeze) — a kernel-`decide`-checked
enumeration of the concrete table. So the active `.poseidon2` table is genuinely chip-faithful. -/
theorem activeChipTbl_sound :
    ChipTableSoundN permOutZ (tfOf2 transferV3 realRow lastRow .poseidon2) :=
  soundN_of_all (by decide)

/-! ## §2 — the FAITHFUL active `tf`: the genuine chip table on `.poseidon2`, the genuine range table on
`.range`, empty mem/map. It AGREES with `tfOf2` everywhere EXCEPT `.range`, where it lays down the
deployed `rangeRows BAL_LIMB_BITS` instead of the membership stand-in. -/

/-- The faithful auxiliary tables for the active trace: the union chip table on `.poseidon2` (genuinely
`ChipTableSoundN permOutZ`), the genuine deployed limb table on `.range`, empty elsewhere. On
`.poseidon2`/`.memory`/`.mapOps` it AGREES with `tfOf2 transferV3 realRow lastRow` (so the existing chip /
mem / map discharges port directly); only `.range` is swapped to the genuine `rangeRows`. -/
def activeFaithfulTf : TraceFamily := fun tid =>
  if tid = .range then rangeRows BAL_LIMB_BITS
  else tfOf2 transferV3 realRow lastRow tid

theorem activeFaithfulTf_poseidon2 :
    activeFaithfulTf .poseidon2 = tfOf2 transferV3 realRow lastRow .poseidon2 := by
  unfold activeFaithfulTf; rfl
theorem activeFaithfulTf_range : activeFaithfulTf .range = rangeRows BAL_LIMB_BITS := by
  unfold activeFaithfulTf; rfl
theorem activeFaithfulTf_memory :
    activeFaithfulTf .memory = tfOf2 transferV3 realRow lastRow .memory := by
  unfold activeFaithfulTf; rfl
theorem activeFaithfulTf_mapOps :
    activeFaithfulTf .mapOps = tfOf2 transferV3 realRow lastRow .mapOps := by
  unfold activeFaithfulTf; rfl

/-- **The active+faithful trace.** The SAME two active rows as `realTransferTrace` (the genuine debit
`realRow`, the wrap `lastRow`), but the `tf` carries the GENUINE faithful tables: the union chip table on
`.poseidon2` (`ChipTableSoundN permOutZ`), the deployed `rangeRows BAL_LIMB_BITS` on `.range`. -/
def activeFaithfulTrace : VmTrace where
  rows := [realRow, lastRow]
  pub  := realPub
  tf   := activeFaithfulTf

@[simp] theorem activeFaithfulTrace_rows : activeFaithfulTrace.rows = [realRow, lastRow] := rfl
@[simp] theorem activeFaithfulTrace_rows_ne : activeFaithfulTrace.rows ≠ [] := by simp

theorem envAt_activeFaithfulTrace_zero :
    envAt activeFaithfulTrace 0 = { loc := realRow, nxt := lastRow, pub := realPub } := by
  simp [envAt, activeFaithfulTrace, List.getD]
theorem envAt_activeFaithfulTrace_one :
    envAt activeFaithfulTrace 1 = { loc := lastRow, nxt := zeroAsg, pub := realPub } := by
  simp [envAt, activeFaithfulTrace, List.getD]

/-! ## §3 — the per-row constraint discharge against the FAITHFUL `tf`.

Identical in spirit to `CircuitCompletenessNonVacuityReal.row{0,1}_constraints_hold`, but the table is
`activeFaithfulTf`, not `tfOf2`. The only difference is on `.range`: there the faithful `tf` is the genuine
`rangeRows BAL_LIMB_BITS`, so a range lookup is discharged by `lookup_range_complete` (the active row's
after-balance limb is in `[0, 2^30)`), NOT by membership in a row-built table. The base constraints
(`base_constraints_hold`) and the chip lookups (membership in the union table, which `activeFaithfulTf`
carries unchanged on `.poseidon2`) port directly. -/

/-- A lookup whose table is `.poseidon2` holds against `activeFaithfulTf` iff it holds against the union
table `tfOf2 transferV3 realRow lastRow` — the faithful `tf` carries the `.poseidon2` table UNCHANGED
(only `.range` is swapped). So every chip lookup discharge ports from the `tfOf2` machinery directly. -/
theorem chip_holdsAt_iff (l : Lookup) (hl : l.table = .poseidon2) (env : VmRowEnv) :
    l.holdsAt activeFaithfulTf env ↔ l.holdsAt (tfOf2 transferV3 realRow lastRow) env := by
  unfold Lookup.holdsAt
  rw [hl, activeFaithfulTf_poseidon2]

/-- The two after-balance-limb range lookups of the live transfer descriptor, discharged against the
GENUINE `rangeRows BAL_LIMB_BITS`. On the ACTIVE row the wires are `saCol BALANCE_LO = 90`,
`saCol BALANCE_HI = 0`, both in `[0, 2^30)`; on the WRAP row both are `0`. So the deployed limb table
CONTAINS the looked-up rows — the faithful range leg holds. -/
theorem range_lookup_holds_active (r : VmRange)
    (hr : r ∈ (rotateV3FrozenAuthority transferVmDescriptor).ranges)
    (env : VmRowEnv) (hwire : VmRange.holds env r) :
    (rangeLookup r).holdsAt activeFaithfulTf env := by
  -- both transfer ranges have `bits = 30 = BAL_LIMB_BITS`; align so `activeFaithfulTf_range` applies.
  have hbits : r.bits = BAL_LIMB_BITS := by
    rw [show (rotateV3FrozenAuthority transferVmDescriptor).ranges
          = [⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩] from rfl] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  -- `rangeLookup r = ⟨.range, [.var r.wire]⟩`; against `activeFaithfulTf .range = rangeRows BAL_LIMB_BITS`.
  have hrt : activeFaithfulTf .range = rangeRows r.bits := by rw [hbits]; exact activeFaithfulTf_range
  exact lookup_range_complete r.bits activeFaithfulTf hrt env r.wire hwire

/-- On the ACTIVE row both range-checked after-balance limbs are in `[0, 2^30)`: `saCol BALANCE_LO = 90`,
`saCol BALANCE_HI = 0`. So every transfer range tooth `VmRange.holds`. -/
theorem range_holds_realRow (r : VmRange)
    (hr : r ∈ (rotateV3FrozenAuthority transferVmDescriptor).ranges) :
    VmRange.holds envReal r := by
  -- the ranges are exactly `[⟨saCol BALANCE_LO, 30⟩, ⟨saCol BALANCE_HI, 30⟩]`.
  rw [show (rotateV3FrozenAuthority transferVmDescriptor).ranges
        = [⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩] from rfl] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨_, _, _, _, _, _, _, _, _, halo, _, hahi, _, _⟩ := realRow_vals
  rcases hr with rfl | rfl
  · -- BALANCE_LO = 90 ∈ [0, 2^30).
    refine ⟨?_, ?_⟩ <;> simp only [VmRange.holds, envReal] <;> rw [halo] <;> norm_num
  · -- BALANCE_HI = 0 ∈ [0, 2^30).
    refine ⟨?_, ?_⟩ <;> simp only [VmRange.holds, envReal] <;> rw [hahi] <;> norm_num

/-- On the WRAP row both range-checked after-balance limbs are `0` (the wrap row's own after block is
all-zero), hence in `[0, 2^30)`. -/
theorem range_holds_lastRow (r : VmRange)
    (hr : r ∈ (rotateV3FrozenAuthority transferVmDescriptor).ranges) :
    VmRange.holds { loc := lastRow, nxt := zeroAsg, pub := realPub } r := by
  rw [show (rotateV3FrozenAuthority transferVmDescriptor).ranges
        = [⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩] from rfl] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  -- `lastRow` is `0` off cols 54, 56; the after-balance limbs `saCol BALANCE_LO = 76`,
  -- `saCol BALANCE_HI = 77` are neither, so both read `0`.
  have hzlo : lastRow (saCol state.BALANCE_LO) = 0 := lastRow_zero_of (by decide) (by decide)
  have hzhi : lastRow (saCol state.BALANCE_HI) = 0 := lastRow_zero_of (by decide) (by decide)
  rcases hr with rfl | rfl
  · refine ⟨?_, ?_⟩ <;> simp only [VmRange.holds] <;> rw [hzlo] <;> norm_num
  · refine ⟨?_, ?_⟩ <;> simp only [VmRange.holds] <;> rw [hzhi] <;> norm_num

/-- **Row 0 (the ACTIVE real transfer row) satisfies every `transferV3` constraint against the FAITHFUL
`tf`.** Base constraints by `base_constraints_hold`; chip lookups by membership in the union `.poseidon2`
table (which the faithful `tf` carries unchanged); range lookups by `lookup_range_complete` against the
genuine `rangeRows` (the after-balance limbs `90`/`0` are in `[0, 2^30)`). -/
theorem row0_faithful_constraints_hold (hash : List ℤ → ℤ) :
    ∀ c ∈ transferV3.constraints,
      c.holdsAt hash activeFaithfulTrace.tf (envAt activeFaithfulTrace 0) (0 == 0) (0 + 1 == 2) := by
  intro c hc
  rw [envAt_activeFaithfulTrace_zero]
  show c.holdsAt hash activeFaithfulTf envReal true false
  rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl] at hc
  have hc' := hc
  rw [graduateV1] at hc'
  simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc'
  rcases hc' with (⟨c₀, hc₀, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨r, hr, rfl⟩
  · -- a re-anchored base constraint — discharged on the ACTIVE row (`true false`).
    show c₀.holdsVm envReal true false
    exact base_constraints_hold c₀ hc₀
  · -- a chip lookup: hits the `realRow` summand of the union `.poseidon2` table.
    refine (chip_holdsAt_iff _ rfl envReal).mpr ?_
    exact lookup_holdsAt_tfOf2_left (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor))
      realRow lastRow envReal rfl _ hc
  · -- a range lookup: against the genuine `rangeRows`, the after-balance limb is in `[0, 2^30)`.
    exact range_lookup_holds_active r hr envReal (range_holds_realRow r hr)

/-- **Row 1 (the WRAP row) satisfies every `transferV3` constraint against the FAITHFUL `tf`.** On the
last row the per-row gates are vacuous; the boundary-LAST pins read zero columns; chip lookups hit the
`lastRow` summand of the union table; range lookups are `0 ∈ [0, 2^30)` against `rangeRows`. -/
theorem row1_faithful_constraints_hold (hash : List ℤ → ℤ) :
    ∀ c ∈ transferV3.constraints,
      c.holdsAt hash activeFaithfulTrace.tf (envAt activeFaithfulTrace 1) (1 == 0) (1 + 1 == 2) := by
  intro c hc
  rw [envAt_activeFaithfulTrace_one]
  show c.holdsAt hash activeFaithfulTf { loc := lastRow, nxt := zeroAsg, pub := realPub } false true
  rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl] at hc
  have hc' := hc
  rw [graduateV1] at hc'
  simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc'
  rcases hc' with (⟨c₀, hc₀, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨r, hr, rfl⟩
  · -- a re-anchored base constraint, on the LAST row (`false true`). `.base`'s `holdsAt` is `holdsVm`,
    -- independent of `tf`, so the real-file last-row discharge (`row1_constraints_hold`) applies verbatim.
    show c₀.holdsVm { loc := lastRow, nxt := zeroAsg, pub := realPub } false true
    have hmem : (VmConstraint2.base c₀) ∈ transferV3.constraints := by
      rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
        graduateV1]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨c₀, hc₀, rfl⟩))))
    have := row1_constraints_hold hash (.base c₀) hmem
    rw [envAt_realTransferTrace_one] at this
    exact this
  · -- a chip lookup: hits the `lastRow` summand of the union `.poseidon2` table.
    refine (chip_holdsAt_iff _ rfl { loc := lastRow, nxt := zeroAsg, pub := realPub }).mpr ?_
    exact lookup_holdsAt_tfOf2_right (graduateV1 (rotateV3FrozenAuthority transferVmDescriptor))
      realRow lastRow { loc := lastRow, nxt := zeroAsg, pub := realPub } rfl _ hc
  · -- a range lookup: `0 ∈ [0, 2^30)` against the genuine `rangeRows`.
    exact range_lookup_holds_active r hr _ (range_holds_lastRow r hr)

/-! ## §4 — the full `Satisfied2` for the ACTIVE+FAITHFUL trace.

The per-row leg is `row{0,1}_faithful_constraints_hold` (the genuine transfer arithmetic / nonce /
direction / frame gates, the transition, the boundary/rotated PI pins, the welds, the frozen-authority
continuity, the chip lookups, AND the range lookups against the genuine `rangeRows` — all on the active
rows). The hash-site / legacy-range legs are vacuous (`graduateV1` emits neither). The memory / map legs
collapse against the empty boundary (`graduateV1` emits no mem/map ops, and the faithful `tf`'s
`.memory`/`.mapOps` agree with the empty `tfOf2` there). -/

/-- The `.memory` leg of `tfOf2` is empty: every graduated constraint is a `.base` or a chip / range
`.lookup`, never a `.memory`-tabled lookup, so the `filterMap` skips all. -/
theorem tfOf2_memory_nil : tfOf2 transferV3 realRow lastRow .memory = [] := by
  have htf : ∀ a : Assignment, tfOf transferV3 a .memory = [] := by
    intro a
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      tfOf, List.filterMap_eq_nil_iff]
    intro c hc
    rcases constraints_graduateV1_shapes _ c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
    · rfl
    · show (if l.table = TableId.memory then _ else none) = none
      rw [if_neg]
      have : l.table = TableId.poseidon2 ∨ l.table = TableId.range := by
        rw [graduateV1] at hc
        simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc
        rcases hc with (⟨c₀, _, hc1⟩ | ⟨i, _, hc1⟩) | ⟨r, _, hc1⟩
        · exact absurd hc1 (by simp)
        · left; injection hc1 with hc1; rw [← hc1]; rfl
        · right; injection hc1 with hc1; rw [← hc1]; rfl
      rcases this with h | h <;> rw [h] <;> decide
  rw [tfOf2, htf, htf, List.append_nil]

/-- The `.mapOps` leg of `tfOf2` is empty: same `filterMap`-skip argument as `.memory`. -/
theorem tfOf2_mapOps_nil : tfOf2 transferV3 realRow lastRow .mapOps = [] := by
  have htf : ∀ a : Assignment, tfOf transferV3 a .mapOps = [] := by
    intro a
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      tfOf, List.filterMap_eq_nil_iff]
    intro c hc
    rcases constraints_graduateV1_shapes _ c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
    · rfl
    · show (if l.table = TableId.mapOps then _ else none) = none
      rw [if_neg]
      have : l.table = TableId.poseidon2 ∨ l.table = TableId.range := by
        rw [graduateV1] at hc
        simp only [List.mem_append, List.mem_map, List.mem_mapIdx] at hc
        rcases hc with (⟨c₀, _, hc1⟩ | ⟨i, _, hc1⟩) | ⟨r, _, hc1⟩
        · exact absurd hc1 (by simp)
        · left; injection hc1 with hc1; rw [← hc1]; rfl
        · right; injection hc1 with hc1; rw [← hc1]; rfl
      rcases this with h | h <;> rw [h] <;> decide
  rw [tfOf2, htf, htf, List.append_nil]

/-- `activeFaithfulTrace.tf` IS `activeFaithfulTf` (function-level `rfl` — no application, no evaluation
of the size-`2^30` range table). -/
theorem activeFaithfulTrace_tf : activeFaithfulTrace.tf = activeFaithfulTf := rfl

/-- The range leg of the trace, read off WITHOUT projecting through `activeFaithfulTf` (which would whnf
the `2^30` `rangeRows`). -/
theorem activeFaithfulTrace_range : activeFaithfulTrace.tf .range = rangeRows BAL_LIMB_BITS := by
  rw [activeFaithfulTrace_tf, activeFaithfulTf_range]

/-- The poseidon2 leg of the trace, read off via `rw` (no projection whnf). -/
theorem activeFaithfulTrace_poseidon2 :
    activeFaithfulTrace.tf .poseidon2 = tfOf2 transferV3 realRow lastRow .poseidon2 := by
  rw [activeFaithfulTrace_tf, activeFaithfulTf_poseidon2]

theorem activeFaithfulTrace_memory : activeFaithfulTrace.tf .memory = [] := by
  rw [activeFaithfulTrace_tf, activeFaithfulTf_memory, tfOf2_memory_nil]
theorem activeFaithfulTrace_mapOps : activeFaithfulTrace.tf .mapOps = [] := by
  rw [activeFaithfulTrace_tf, activeFaithfulTf_mapOps, tfOf2_mapOps_nil]

/-- **`satisfied2_activeFaithful` — the `Satisfied2` core of the active+faithful trace.** The per-row
gates GENUINELY bite (the real debit / nonce tick on row 0); the memory / map / legacy-range legs collapse
exactly as in the empty case, now read off the FAITHFUL `tf` (`.memory`/`.mapOps` are `[]` there). -/
theorem satisfied2_activeFaithful (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash transferV3 minit mfin [] activeFaithfulTrace where
  rowConstraints := by
    intro i hi c hc
    have hlen : activeFaithfulTrace.rows.length = 2 := by simp [activeFaithfulTrace_rows]
    rw [hlen] at hi ⊢
    interval_cases i
    · exact row0_faithful_constraints_hold hash c hc
    · exact row1_faithful_constraints_hold hash c hc
  rowHashes := by
    intro i hi
    show siteHoldsAll hash _ transferV3.hashSites
    rw [show transferV3.hashSites = [] from rfl]
    trivial
  rowRanges := by
    intro i hi r hr
    rw [show transferV3.ranges = [] from rfl] at hr
    simp at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1] at hop
    simp at hop
  memDisciplined := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    trivial
  memBalanced := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  memTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    -- t.tf .memory = [] = [].map opRow.
    rw [activeFaithfulTrace_memory, List.map_nil]
  mapTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      mapLog_graduateV1]
    rw [activeFaithfulTrace_mapOps]

/-! ## §5 — THE KEYSTONE MADE WHOLE: ONE `Satisfied2Faithful` term, active AND faithful. -/

/-- **`satisfied2Faithful_transferV3_active` — THE UNIFIED WITNESS.** The FULL `Satisfied2Faithful` object
for the live `transferV3`, inhabited by the ACTIVE+FAITHFUL trace: the `Satisfied2` core
(`satisfied2_activeFaithful` — the genuine per-row transfer arithmetic `bal 100 → 90`, `nonce 0 → 1`
GENUINELY firing) PLUS the four faithful conjuncts — the permutation width (`permOutZ_width`), the lane-0
digest identity (`permOutZ_lane0`), the genuine chip-table soundness (`activeChipTbl_sound`: every chip
row of the active union table IS a real `chipRowN permOutZ ins`), and the genuine range table
(`activeFaithfulTf_range`: `rangeRows BAL_LIMB_BITS`). So the deployed accept-set is inhabited by a REAL
active turn whose per-row gates bite AND whose chip/range tables are genuinely faithful — ONE object, not
two composed half-witnesses. -/
theorem satisfied2Faithful_transferV3_active (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Dregg2.Circuit.Satisfied2Faithful.Satisfied2Faithful
      permOutZ permOut0 transferV3 minit mfin [] activeFaithfulTrace where
  toSatisfied2 := satisfied2_activeFaithful permOut0 minit mfin
  permWidth := permOutZ_width
  chipHashIsLane0 := permOutZ_lane0
  chipTableFaithful := by
    rw [activeFaithfulTrace_poseidon2]; exact activeChipTbl_sound
  rangeTableFaithful := activeFaithfulTrace_range

/-- **`satisfied2Faithful_active_inhabited` — the active+faithful object is NON-EMPTY, over a NON-EMPTY
trace.** There exist a permutation, digest, memory boundary and a trace with `rows ≠ []` inhabiting
`Satisfied2Faithful` of the live `transferV3` whose per-row transfer gates genuinely fire. The keystone's
non-vacuity is realized by a REAL active turn, not the empty trace. -/
theorem satisfied2Faithful_active_inhabited :
    ∃ (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
      (maddrs : List ℤ) (t : VmTrace),
      t.rows ≠ [] ∧ Dregg2.Circuit.Satisfied2Faithful.Satisfied2Faithful
        permOut hash transferV3 minit mfin maddrs t :=
  ⟨permOutZ, permOut0, fun _ => 0, fun _ => (0, 0), [], activeFaithfulTrace,
   activeFaithfulTrace_rows_ne,
   satisfied2Faithful_transferV3_active (fun _ => 0) (fun _ => (0, 0))⟩

/-- **The collapse recipe FIRES on the unified active+faithful witness.** From the inhabited object the v1
denotation `satisfiedVm` holds on every (now NON-EMPTY) row WITHOUT any free chip/range lever — the
structure CARRIES them. Unlike the empty-trace keystone, here the conclusion ranges over REAL active rows,
so the recipe flows a GENUINELY ACTIVE faithful object to the rung layer. -/
theorem active_collapse_recipe
    (hgrad : Dregg2.Circuit.Emit.EffectVmEmitV2.graduable
      (rotateV3FrozenAuthority transferVmDescriptor) = true) :
    ∀ i, i < activeFaithfulTrace.rows.length →
      satisfiedVm permOut0 (rotateV3FrozenAuthority transferVmDescriptor)
        (envAt activeFaithfulTrace i) (i == 0) (i + 1 == activeFaithfulTrace.rows.length) :=
  Dregg2.Circuit.Satisfied2Faithful.satisfied2Faithful_satisfiedVm permOutZ permOut0
    (rotateV3FrozenAuthority transferVmDescriptor) (fun _ => 0) (fun _ => (0, 0)) []
    activeFaithfulTrace hgrad (satisfied2Faithful_transferV3_active (fun _ => 0) (fun _ => (0, 0)))

/-! ## §6 — axiom hygiene. -/

#assert_axioms activeChipTbl_sound
#assert_axioms range_lookup_holds_active
#assert_axioms row0_faithful_constraints_hold
#assert_axioms row1_faithful_constraints_hold
#assert_axioms satisfied2_activeFaithful
#assert_axioms satisfied2Faithful_transferV3_active
#assert_axioms satisfied2Faithful_active_inhabited
#assert_axioms active_collapse_recipe

end Dregg2.Circuit.Satisfied2FaithfulActive
