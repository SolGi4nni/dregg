/-
# Dregg2.Circuit.BornEmptyCommit — digest carriers for born-empty per-cell side tables.

Account-growth effects reset every indexed slot at a fresh `CellId` (`bornEmptyCellSlots` in
`RecordKernel.lean`). This module bundles those maps for `funcComponent` wiring in the v2
multi-component frameworks (`EffectCommit3`+).

ADDITIVE: imports `EffectCommit2`; edits none.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.BornEmptyCommit

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Authority
open Dregg2.Exec

set_option linter.dupNamespace false

/-- Per-cell maps reset on account growth (everything in `bornEmptyAt` except `bal`). -/
structure BornEmptySideTables where
  cell         : CellId → Value
  caps         : Caps
  delegate     : CellId → Option CellId
  delegations  : CellId → List Cap
  slotCaveats  : CellId → List SlotCaveat
  lifecycle    : CellId → Nat
  deathCert    : CellId → Nat

theorem BornEmptySideTables.ext {a b : BornEmptySideTables}
    (hcell : a.cell = b.cell) (hcaps : a.caps = b.caps) (hdel : a.delegate = b.delegate)
    (hdgs : a.delegations = b.delegations) (hsc : a.slotCaveats = b.slotCaveats)
    (hlif : a.lifecycle = b.lifecycle) (hdc : a.deathCert = b.deathCert) : a = b := by
  cases a; cases b; simp_all

def readBornEmptySide (k : RecordKernelState) : BornEmptySideTables :=
  { cell := k.cell, caps := k.caps, delegate := k.delegate, delegations := k.delegations
    slotCaveats := k.slotCaveats, lifecycle := k.lifecycle, deathCert := k.deathCert }

def expectedBornEmptySide (k : RecordKernelState) (fresh : CellId) : BornEmptySideTables :=
  { cell := fun c => if c = fresh then default else k.cell c
    caps := fun l => if l = fresh then [] else k.caps l
    delegate := fun c => if c = fresh then none else k.delegate c
    delegations := fun c => if c = fresh then [] else k.delegations c
    slotCaveats := fun c => if c = fresh then [] else k.slotCaveats c
    lifecycle := fun c => if c = fresh then 0 else k.lifecycle c
    deathCert := fun c => if c = fresh then 0 else k.deathCert c }

/-- Authority-side tables born empty at `fresh` (factory create leg after cell/caveat install). -/
structure BornEmptyAuthorityTables where
  caps        : Caps
  lifecycle   : CellId → Nat
  deathCert   : CellId → Nat
  delegate    : CellId → Option CellId
  delegations : CellId → List Cap

theorem BornEmptyAuthorityTables.ext {a b : BornEmptyAuthorityTables}
    (hcaps : a.caps = b.caps) (hlif : a.lifecycle = b.lifecycle) (hdc : a.deathCert = b.deathCert)
    (hdel : a.delegate = b.delegate) (hdgs : a.delegations = b.delegations) : a = b := by
  cases a; cases b; simp_all

def readBornEmptyAuthority (k : RecordKernelState) : BornEmptyAuthorityTables :=
  { caps := k.caps, lifecycle := k.lifecycle, deathCert := k.deathCert
    delegate := k.delegate, delegations := k.delegations }

def expectedBornEmptyAuthority (k : RecordKernelState) (fresh : CellId) : BornEmptyAuthorityTables :=
  { caps := fun l => if l = fresh then [] else k.caps l
    lifecycle := fun c => if c = fresh then 0 else k.lifecycle c
    deathCert := fun c => if c = fresh then 0 else k.deathCert c
    delegate := fun c => if c = fresh then none else k.delegate c
    delegations := fun c => if c = fresh then [] else k.delegations c }

/-- Create-leg cell metadata born empty at `fresh` (spawn: before authority handoff). -/
structure BornEmptyCellMeta where
  cell        : CellId → Value
  slotCaveats : CellId → List SlotCaveat
  lifecycle   : CellId → Nat
  deathCert   : CellId → Nat

theorem BornEmptyCellMeta.ext {a b : BornEmptyCellMeta}
    (hcell : a.cell = b.cell) (hsc : a.slotCaveats = b.slotCaveats)
    (hlif : a.lifecycle = b.lifecycle) (hdc : a.deathCert = b.deathCert) : a = b := by
  cases a; cases b; simp_all

def readBornEmptyCellMeta (k : RecordKernelState) : BornEmptyCellMeta :=
  { cell := k.cell, slotCaveats := k.slotCaveats, lifecycle := k.lifecycle, deathCert := k.deathCert }

def expectedBornEmptyCellMeta (k : RecordKernelState) (fresh : CellId) : BornEmptyCellMeta :=
  { cell := fun c => if c = fresh then default else k.cell c
    slotCaveats := fun c => if c = fresh then [] else k.slotCaveats c
    lifecycle := fun c => if c = fresh then 0 else k.lifecycle c
    deathCert := fun c => if c = fresh then 0 else k.deathCert c }

theorem bornEmptyCellMeta_post_iff (k : RecordKernelState) (fresh : CellId) (k' : RecordKernelState) :
    readBornEmptyCellMeta k' = expectedBornEmptyCellMeta k fresh ↔
      (k'.cell = fun c => if c = fresh then default else k.cell c)
      ∧ (k'.slotCaveats = fun c => if c = fresh then [] else k.slotCaveats c)
      ∧ (k'.lifecycle = fun c => if c = fresh then 0 else k.lifecycle c)
      ∧ (k'.deathCert = fun c => if c = fresh then 0 else k.deathCert c) := by
  constructor
  · intro h
    dsimp [readBornEmptyCellMeta, expectedBornEmptyCellMeta] at h
    exact ⟨congrArg BornEmptyCellMeta.cell h, congrArg BornEmptyCellMeta.slotCaveats h,
      congrArg BornEmptyCellMeta.lifecycle h, congrArg BornEmptyCellMeta.deathCert h⟩
  · rintro ⟨hcl, hsc, hlif, hdc⟩
    apply BornEmptyCellMeta.ext hcl hsc hlif hdc

theorem bornEmptySide_post_iff (k : RecordKernelState) (fresh : CellId) (k' : RecordKernelState) :
    readBornEmptySide k' = expectedBornEmptySide k fresh ↔
      (k'.cell = fun c => if c = fresh then default else k.cell c)
      ∧ (k'.caps = fun l => if l = fresh then [] else k.caps l)
      ∧ (k'.delegate = fun c => if c = fresh then none else k.delegate c)
      ∧ (k'.delegations = fun c => if c = fresh then [] else k.delegations c)
      ∧ (k'.slotCaveats = fun c => if c = fresh then [] else k.slotCaveats c)
      ∧ (k'.lifecycle = fun c => if c = fresh then 0 else k.lifecycle c)
      ∧ (k'.deathCert = fun c => if c = fresh then 0 else k.deathCert c) := by
  constructor
  · intro h
    dsimp [readBornEmptySide, expectedBornEmptySide] at h
    exact ⟨congrArg BornEmptySideTables.cell h, congrArg BornEmptySideTables.caps h,
      congrArg BornEmptySideTables.delegate h, congrArg BornEmptySideTables.delegations h,
      congrArg BornEmptySideTables.slotCaveats h, congrArg BornEmptySideTables.lifecycle h,
      congrArg BornEmptySideTables.deathCert h⟩
  · rintro ⟨hcl, hcp, hdel, hdgs, hsc, hlif, hdc⟩
    apply BornEmptySideTables.ext hcl hcp hdel hdgs hsc hlif hdc

theorem bornEmptyAt_iff_side_and_bal (k : RecordKernelState) (fresh : CellId) (k' : RecordKernelState) :
    bornEmptyAt k fresh k' ↔
      readBornEmptySide k' = expectedBornEmptySide k fresh
      ∧ (k'.bal = fun c a => if c = fresh then 0 else k.bal c a) := by
  dsimp [bornEmptyAt]
  constructor
  · rintro ⟨hcl, hcp, hdel, hdgs, hsc, hlif, hdc, hbal⟩
    refine ⟨?_, hbal⟩
    exact (bornEmptySide_post_iff k fresh k').mpr ⟨hcl, hcp, hdel, hdgs, hsc, hlif, hdc⟩
  · rintro ⟨hside, hbal⟩
    obtain ⟨hcl, hcp, hdel, hdgs, hsc, hlif, hdc⟩ :=
      (bornEmptySide_post_iff k fresh k').mp hside
    exact ⟨hcl, hcp, hdel, hdgs, hsc, hlif, hdc, hbal⟩

/-- `ActiveComponent` for the born-empty side-table bundle (non-`bal`). -/
def bornEmptySideComponent {St Args : Type} (toKernel : St → RecordKernelState)
    (fresh : St → Args → CellId) (D : BornEmptySideTables → ℤ) (hD : Function.Injective D) :
    ActiveComponent St Args where
  digest    := fun k => D (readBornEmptySide k)
  expected  := fun pre args => D (expectedBornEmptySide (toKernel pre) (fresh pre args))
  postClause := fun pre args post =>
    readBornEmptySide post = expectedBornEmptySide (toKernel pre) (fresh pre args)
  binds     := fun _ _ _ h => hD h
  encodes   := fun _ _ _ h => congrArg D h

def bornEmptyAuthorityComponent {St Args : Type} (toKernel : St → RecordKernelState)
    (fresh : St → Args → CellId) (D : BornEmptyAuthorityTables → ℤ) (hD : Function.Injective D) :
    ActiveComponent St Args where
  digest    := fun k => D (readBornEmptyAuthority k)
  expected  := fun pre args => D (expectedBornEmptyAuthority (toKernel pre) (fresh pre args))
  postClause := fun pre args post =>
    readBornEmptyAuthority post = expectedBornEmptyAuthority (toKernel pre) (fresh pre args)
  binds     := fun _ _ _ h => hD h
  encodes   := fun _ _ _ h => congrArg D h

def bornEmptyCellMetaComponent {St Args : Type} (toKernel : St → RecordKernelState)
    (fresh : St → Args → CellId) (D : BornEmptyCellMeta → ℤ) (hD : Function.Injective D) :
    ActiveComponent St Args where
  digest    := fun k => D (readBornEmptyCellMeta k)
  expected  := fun pre args => D (expectedBornEmptyCellMeta (toKernel pre) (fresh pre args))
  postClause := fun pre args post =>
    readBornEmptyCellMeta post = expectedBornEmptyCellMeta (toKernel pre) (fresh pre args)
  binds     := fun _ _ _ h => hD h
  encodes   := fun _ _ _ h => congrArg D h

/-! ### Spawn create-leg bundle (`bal` + born-empty cell metadata, authority handoff separate). -/

structure SpawnCreateLeg where
  bal      : CellId → AssetId → ℤ
  cellMeta : BornEmptyCellMeta

theorem SpawnCreateLeg.ext {a b : SpawnCreateLeg} (hbal : a.bal = b.bal)
    (hmeta : a.cellMeta = b.cellMeta) : a = b := by
  cases a; cases b; simp_all

def readSpawnCreateLeg (k : RecordKernelState) : SpawnCreateLeg :=
  { bal := k.bal, cellMeta := readBornEmptyCellMeta k }

def expectedSpawnCreateLeg (k : RecordKernelState) (fresh : CellId) : SpawnCreateLeg :=
  { bal := fun c a => if c = fresh then 0 else k.bal c a
    cellMeta := expectedBornEmptyCellMeta k fresh }

theorem spawnCreateLeg_post_iff (k : RecordKernelState) (fresh : CellId) (k' : RecordKernelState) :
    readSpawnCreateLeg k' = expectedSpawnCreateLeg k fresh ↔
      (k'.bal = fun c a => if c = fresh then 0 else k.bal c a)
      ∧ readBornEmptyCellMeta k' = expectedBornEmptyCellMeta k fresh := by
  constructor
  · intro h
    dsimp [readSpawnCreateLeg, expectedSpawnCreateLeg] at h
    exact ⟨congrArg SpawnCreateLeg.bal h, congrArg SpawnCreateLeg.cellMeta h⟩
  · rintro ⟨hbal, hmeta⟩
    apply SpawnCreateLeg.ext hbal hmeta

theorem bornEmptyAuthority_post_iff (k : RecordKernelState) (fresh : CellId) (k' : RecordKernelState) :
    readBornEmptyAuthority k' = expectedBornEmptyAuthority k fresh ↔
      (k'.caps = fun l => if l = fresh then [] else k.caps l)
      ∧ (k'.lifecycle = fun c => if c = fresh then 0 else k.lifecycle c)
      ∧ (k'.deathCert = fun c => if c = fresh then 0 else k.deathCert c)
      ∧ (k'.delegate = fun c => if c = fresh then none else k.delegate c)
      ∧ (k'.delegations = fun c => if c = fresh then [] else k.delegations c) := by
  constructor
  · intro h
    dsimp [readBornEmptyAuthority, expectedBornEmptyAuthority] at h
    exact ⟨congrArg BornEmptyAuthorityTables.caps h, congrArg BornEmptyAuthorityTables.lifecycle h,
      congrArg BornEmptyAuthorityTables.deathCert h, congrArg BornEmptyAuthorityTables.delegate h,
      congrArg BornEmptyAuthorityTables.delegations h⟩
  · rintro ⟨hcp, hlif, hdc, hdel, hdgs⟩
    apply BornEmptyAuthorityTables.ext hcp hlif hdc hdel hdgs

def spawnCreateLegComponent {St Args : Type} (toKernel : St → RecordKernelState)
    (fresh : St → Args → CellId) (D : SpawnCreateLeg → ℤ) (hD : Function.Injective D) :
    ActiveComponent St Args where
  digest    := fun k => D (readSpawnCreateLeg k)
  expected  := fun pre args => D (expectedSpawnCreateLeg (toKernel pre) (fresh pre args))
  postClause := fun pre args post =>
    readSpawnCreateLeg post = expectedSpawnCreateLeg (toKernel pre) (fresh pre args)
  binds     := fun _ _ _ h => hD h
  encodes   := fun _ _ _ h => congrArg D h

#assert_axioms bornEmptyCellMeta_post_iff
#assert_axioms bornEmptySide_post_iff
#assert_axioms bornEmptyAt_iff_side_and_bal
#assert_axioms spawnCreateLeg_post_iff
#assert_axioms bornEmptyAuthority_post_iff

end Dregg2.Circuit.BornEmptyCommit