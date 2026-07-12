/-
# `Dregg2.Circuit.AirLegsDischarged` — discharging the EIGHT explicit premises of
`AirChecksSatisfied.airAccept_forces_satisfied2` AT THE DEPLOYED DESCRIPTOR `transferV3`.

## HONEST SCOPE (first sentence)

At the DEPLOYED descriptor `transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)`,
SIX of the eight explicit premises of `airAccept_forces_satisfied2` are DISCHARGED here for an
ARBITRARY accepting trace (`rowHashes`, `rowRanges`, `memAddrsNodup`, `memClosed`, `memDisciplined`,
`memBalanced`); the two that REMAIN are `hbus` (the lookup arm — LogUp membership soundness) and the
`mem`/`mapTableFaithful` pair (reduced to the aux-table-emptiness assembly obligation
`t.tf .memory = [] ∧ t.tf .mapOps = []`). So `airAccept ⟹ Satisfied2` is NOT full for `transferV3`:
it reduces to `hbus` + the two table-emptiness assembly facts. It is FULL only for the all-arithmetic,
mem/map/lookup-free `embedV1` shape whose aux tables are empty (`airAccept_forces_satisfied2_allArith`
below), where `hbus` is vacuous — but even there the table-assembly emptiness is an IRREDUCIBLE
structural fact about the committed trace, never an AIR-arithmetic consequence.

## READ THE ARGUMENT, NOT THE NAME (the two teeth this file pays for)

* **`rowHashes` / `rowRanges` are discharged STRUCTURALLY, NOT via the chip/range TABLE soundness.**
  For the GRADUATED deployed descriptor `transferV3.hashSites = []` and `transferV3.ranges = []` — the
  legacy in-row Poseidon2 sites and in-row range teeth are EMPTY (the hashing/range work graduated to
  the chip/range LOOKUP tables). So `siteHoldsAll _ _ [] = True` and `∀ r ∈ [], …` are vacuous for
  EVERY trace. Wiring `deployedChipTbl_sound : ChipTableSoundN permOutDeployed …` or
  `RangeTableSound …` into `rowHashes`/`rowRanges` would be a CATEGORY ERROR: those results are about
  the chip/range TABLE contents, which feed the LOOKUP arm `hbus` (below), not the empty in-row
  `hashSites`/`ranges` fields. `Satisfied2` has NO chip-table-faithfulness field (that lives in the
  extended `Satisfied2Faithful`), so `deployedChipTbl_sound` is not one of these eight premises at all.

* **The `mem`/`mapTableFaithful` legs are NOT LogUp — they are the table-assembly emptiness.** For
  `transferV3` the memory/map LOGS are empty for EVERY trace (`memLog_graduateV1` / `mapLog_graduateV1`:
  `memOpsOf (graduateV1 d) = []`), so the two faithfulness legs collapse to `t.tf .memory = []` and
  `t.tf .mapOps = []`. No `transferV3` constraint reads either table, so AIR acceptance does not force
  them — this is the IRREDUCIBLE assembly obligation (the committed aux tables ARE the gathered logs),
  kept here as two honest hypotheses. NOT faked.

## THE LogUp VERDICT (the un-discharged `hbus`)

`hbus` requires, for every non-arithmetic `transferV3` constraint (all `.lookup`, chip or range),
`Lookup.holdsAt t.tf env = (l.tuple.map (·.eval env.loc)) ∈ t.tf l.table` — the evaluated tuple is a
row of the committed table. AIR acceptance does NOT force this: `arithResidual (.lookup _) = 0` by
construction, so the quotient check is silent on lookups. The bridge "the LogUp bus balances ⟹ the
looked-up multiset is supported by the table" is EXPLICITLY out of the Lean semantics —
`Dregg2.Circuit.Lookup` (`Lookup.lean:17-18`): "LogUp is merely how the prover ENFORCES it
efficiently — that lives in the Rust AIR, not in this semantics." So `hbus` REMAINS, reducing to
(a) LogUp permutation-argument soundness (NOT modeled in Lean) PLUS (b) chip/range table faithfulness
(`deployedChipTbl_sound` / `RangeTableSound` — these ARE at the deployed argument). `hbus_is_lookup`
below pins the shape: every remaining `hbus` obligation is a chip/range lookup membership.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free. NEW file; imports read-only.
No carrier introduced; no `def …Sound`; the two remaining legs are honest hypotheses.
-/
import Mathlib.Tactic
import Dregg2.Circuit.AirChecksSatisfied
import Dregg2.Circuit.RotatedKernelRefinement

namespace Dregg2.Circuit.AirLegsDischarged

open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 memLog_graduateV1 mapLog_graduateV1
  constraints_graduateV1_shapes)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3FrozenAuthority)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Crypto

set_option autoImplicit false

/-- `transferV3` IS the graduated frozen-authority transfer descriptor (definitional). -/
theorem transferV3_eq_grad :
    transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) := rfl

/-! ## §1 — the STRUCTURAL emptiness facts of the deployed descriptor (hold for EVERY trace). -/

/-- The deployed descriptor has NO legacy in-row hash sites (they graduated to the chip table). -/
theorem transferV3_hashSites : transferV3.hashSites = [] := rfl

/-- The deployed descriptor has NO legacy in-row range teeth (they graduated to the range table). -/
theorem transferV3_ranges : transferV3.ranges = [] := rfl

/-- The deployed descriptor's memory log is EMPTY for every trace (`graduateV1` emits no mem ops). -/
theorem memLog_transferV3 (t : VmTrace) : memLog transferV3 t = [] := by
  rw [transferV3_eq_grad]; exact memLog_graduateV1 _ t

/-- The deployed descriptor's map-ops log is EMPTY for every trace (`graduateV1` emits no map ops). -/
theorem mapLog_transferV3 (t : VmTrace) : mapLog transferV3 t = [] := by
  rw [transferV3_eq_grad]; exact mapLog_graduateV1 _ t

/-! ## §2 — the six DISCHARGED premises (each for an ARBITRARY trace). -/

/-- **`rowHashes` DISCHARGED** — `transferV3.hashSites = []`, so `siteHoldsAll` is `True` on every row.
NOT the chip-table soundness: this is the empty legacy in-row site list. -/
theorem hHashes_transferV3 (hash : List ℤ → ℤ) (t : VmTrace) :
    ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) transferV3.hashSites := by
  intro i _
  rw [transferV3_hashSites]; trivial

/-- **`rowRanges` DISCHARGED** — `transferV3.ranges = []`, so the range field is vacuous on every row.
NOT `RangeTableSound`: this is the empty legacy in-row range list. -/
theorem hRanges_transferV3 (t : VmTrace) :
    ∀ i < t.rows.length, ∀ r ∈ transferV3.ranges, r.holds (envAt t i) := by
  intro i _ r hr
  rw [transferV3_ranges] at hr
  simp at hr

/-- **`memClosed` DISCHARGED** — the memory log is empty, so no op needs an address (any `maddrs`). -/
theorem hClosed_transferV3 (t : VmTrace) (maddrs : List ℤ) :
    ∀ op ∈ memLog transferV3 t, op.addr ∈ maddrs := by
  intro op hop
  rw [memLog_transferV3] at hop
  simp at hop

/-- **`memDisciplined` DISCHARGED** — `Disciplined []` (the empty log is per-op disciplined). -/
theorem hDisc_transferV3 (t : VmTrace) :
    MemoryChecking.Disciplined (memLog transferV3 t) := by
  rw [memLog_transferV3]; trivial

/-- **`memBalanced` DISCHARGED** — over the empty address boundary `[]` and empty log, the multiset
balance `initSet + writeSet = readSet + finalSet` reads `0 = 0` for any `minit`/`mfin`. This is the
honest declared boundary of a mem-op-free descriptor (no address touched). -/
theorem hBal_transferV3 (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (t : VmTrace) :
    MemoryChecking.MemCheck minit mfin [] (memLog transferV3 t) := by
  rw [memLog_transferV3]
  simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
    MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]

/-! ## §3 — the REMAINING `hbus` leg: its exact shape is a chip/range LOOKUP membership. -/

/-- **Every remaining `hbus` obligation is a `.lookup`** — the non-arithmetic `transferV3` constraints
are exactly the chip / range lookups (`graduateV1` emits only `.base` and `.lookup`; `.base` is
arithmetic). So `hbus` reduces to `Lookup.holdsAt t.tf env = (tuple.map eval) ∈ t.tf l.table` for each
chip/range lookup — the LogUp membership the AIR quotient check does NOT force (`arithResidual = 0` on
`.lookup`), and whose bus-balance⟹membership bridge is out of the Lean semantics (`Lookup.lean:17`). -/
theorem hbus_is_lookup (c : VmConstraint2) (hc : c ∈ transferV3.constraints) (hA : ¬ isArith c) :
    ∃ l : Lookup, c = .lookup l := by
  rw [transferV3_eq_grad] at hc
  rcases constraints_graduateV1_shapes _ c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
  · exact absurd (show isArith (VmConstraint2.base c₀) from trivial) hA
  · exact ⟨l, rfl⟩

/-! ## §4 — THE ASSEMBLY: `airAccept ⟹ Satisfied2` for `transferV3`, reduced to `hbus` + table
emptiness. Of the eight explicit premises, SIX are supplied here (`rowHashes`, `rowRanges`,
`memAddrsNodup := []`, `memClosed`, `memDisciplined`, `memBalanced`); `hbus` is carried (LogUp) and the
two faithfulness legs collapse to `t.tf .memory = []` / `t.tf .mapOps = []`. -/

/-- **`airAccept_forces_satisfied2_transferV3` — the deployed-descriptor reduction.** For the live
`transferV3`, an accepting AIR quotient trace (`hAir`) plus the LogUp lookup arm (`hbus`) plus the
aux-table-emptiness assembly facts (`hMemEmpty`/`hMapEmpty`) yields the full `Satisfied2` against the
empty declared address boundary. The other six premises are discharged structurally (see §2). -/
theorem airAccept_forces_satisfied2_transferV3
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (t : VmTrace)
    (hAir : MainAirAcceptF transferV3 t)
    (hbus : ∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length))
    (hMemEmpty : t.tf .memory = [])
    (hMapEmpty : t.tf .mapOps = []) :
    Satisfied2 hash transferV3 minit mfin [] t :=
  airAccept_forces_satisfied2 hash transferV3 minit mfin [] t
    hAir hbus
    (hHashes_transferV3 hash t)
    (hRanges_transferV3 t)
    List.nodup_nil
    (hClosed_transferV3 t [])
    (hDisc_transferV3 t)
    (hBal_transferV3 minit mfin t)
    (by rw [memLog_transferV3, List.map_nil]; exact hMemEmpty)
    (by rw [mapLog_transferV3]; exact hMapEmpty)

/-! ## §5 — the FULL corollary: for an all-arithmetic, mem/map/lookup-free descriptor whose aux
tables are empty, `airAccept ⟹ Satisfied2` with NO carried LogUp premise (`hbus` vacuous). Even here
the table-assembly emptiness is an explicit structural fact about the committed trace. -/

/-- **`airAccept_forces_satisfied2_allArith` — FULL `airAccept ⟹ Satisfied2` (no LogUp).** When every
declared constraint is arithmetic, `hashSites`/`ranges` are empty, and the descriptor declares no
mem/map ops (`memLog d t = []`, `mapLog d t = []`), AIR acceptance alone (plus the empty-aux-table
assembly facts) forces the WHOLE `Satisfied2`. `hbus` is discharged by `hall` (no non-arith
constraint), so nothing rides the un-modeled LogUp bus. -/
theorem airAccept_forces_satisfied2_allArith
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (t : VmTrace)
    (hAir : MainAirAcceptF d t)
    (hall : ∀ c ∈ d.constraints, isArith c)
    (hNoHash : d.hashSites = []) (hNoRange : d.ranges = [])
    (hNoMem : memLog d t = []) (hNoMap : mapLog d t = [])
    (hMemEmpty : t.tf .memory = []) (hMapEmpty : t.tf .mapOps = []) :
    Satisfied2 hash d minit mfin [] t :=
  airAccept_forces_satisfied2 hash d minit mfin [] t
    hAir
    (fun _ _ c hc hA => absurd (hall c hc) hA)
    (by intro i _; rw [hNoHash]; trivial)
    (by intro i _ r hr; rw [hNoRange] at hr; simp at hr)
    List.nodup_nil
    (by intro op hop; rw [hNoMem] at hop; simp at hop)
    (by rw [hNoMem]; trivial)
    (by rw [hNoMem]; simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet])
    (by rw [hNoMem, List.map_nil]; exact hMemEmpty)
    (by rw [hNoMap]; exact hMapEmpty)

#assert_axioms memLog_transferV3
#assert_axioms hHashes_transferV3
#assert_axioms hRanges_transferV3
#assert_axioms hClosed_transferV3
#assert_axioms hDisc_transferV3
#assert_axioms hBal_transferV3
#assert_axioms hbus_is_lookup
#assert_axioms airAccept_forces_satisfied2_transferV3
#assert_axioms airAccept_forces_satisfied2_allArith

end Dregg2.Circuit.AirLegsDischarged
