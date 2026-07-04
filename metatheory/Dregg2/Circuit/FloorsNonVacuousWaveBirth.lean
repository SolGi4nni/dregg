/-
# Dregg2.Circuit.FloorsNonVacuousWaveBirth — the CELL-BIRTH `*TraceReadout` carriers are NON-VACUOUS.

Companion to `FloorsNonVacuousWave` (the cellSeal/apex readouts): the three account-GROWTH effect
readouts in `RotatedKernelRefinementBirth` (`CreateCellTraceReadout` / `CreateFromFactoryTraceReadout`
/ `SpawnTraceReadout`) each PREMISE their consuming `<e>_descriptorRefines_sat` rung. A premise that is
secretly UNINHABITABLE makes its rung VACUOUSLY satisfiable. This module exhibits a CONCRETE inhabiting
term per readout, so each rung is NON-vacuous (the premise is satisfiable, not secretly empty).

Per readout we build:
  * the active-row trace `readoutTrace r0` whose designated row 0 carries the effect's runtime selector
    hot (`SEL_CREATE_CELL_RT` / `SEL_FACTORY_RT` / `SEL_SPAWN_RT`);
  * a `pre → post` boundary that GROWS the account set (`post.accounts = insert newCell pre.accounts`),
    so the `growthDecodes` implication's conclusion is `rfl` (the WitnessDecodes seam is realized by
    construction — the boundary IS the kernel set-insert);
  * a discharged guard: `caps actor := [Cap.node newCell …]` so `mintAuthorizedB` (and, for spawn,
    `confersEdgeTo target`) holds, with `newCell ∉ pre.accounts` for freshness;
  * born-empty per-cell post maps matching `bornEmptyAt`/the spec's `if c = newCell then … else pre…`
    forms exactly, and (factory) a trivial CONFORMING `FactoryEntry` registered at `vk = 0`;
  * the receipt log advance + the side-table frame (all `rfl`, post built from pre).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Every field is a CONSTRUCTED term / `rfl` /
`decide`; no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.FloorsNonVacuousWave
import Dregg2.Circuit.RotatedKernelRefinementBirth

namespace Dregg2.Circuit.FloorsNonVacuousWaveBirth

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt)
open Dregg2.Circuit.FloorsNonVacuous (permOutZ)
open Dregg2.Circuit.FloorsNonVacuousWave (readoutTrace readoutTrace_rows_len readoutTrace_loc0)
open Dregg2.Circuit.RotatedKernelRefinementBirth
  (CreateCellTraceReadout CreateFromFactoryTraceReadout SpawnTraceReadout)
open Dregg2.Circuit.Spec.AccountGrowth
  (createReceipt bornEmptyAt spawnCapsMap spawnDelegateMap spawnDelegationsMap spawnEpochAtMap)
open Dregg2.Circuit.Spec.FactoryCreation
  (factoryReceipt factoryPostCell factoryPostCaveats factoryBornCell factoryBornCaveats)
open Dregg2.Exec (RecChainedState RecordKernelState FactoryEntry findFactory mintAuthorizedB)
open Dregg2.Authority (Cap)

set_option autoImplicit false

/-! ## §1 — `CreateCellTraceReadout` INHABITED.

Active row 0 hot at `SEL_CREATE_CELL_RT = 31`. The boundary grows `∅` by the fresh cell `0`; the actor
`0` holds `Cap.node 0` (mint authority); `0 ∉ ∅` (freshness); the post per-cell maps are the born-empty
`if c = 0 then default/[]/… else pre…` forms (`pre = post` off `accounts`+born-empty). -/

/-- The active-row assignment: hot at `SEL_CREATE_CELL_RT`, zero elsewhere. -/
def createCellRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT then 1 else 0

/-- The pre boundary: empty account set, actor `0` holds the privileged mint cap `node 0`. -/
def createCellPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default,
                caps := fun a => if a = 0 then [Cap.node 0] else [] },
    log := [] }

/-- The post boundary: the account set GROWN by `0`, born-empty per-cell maps at `0`, the receipt
prepended. Built from `createCellPre.kernel` so every framed side-table is `rfl`. -/
def createCellPost : RecChainedState :=
  { kernel := { createCellPre.kernel with
      accounts := insert 0 createCellPre.kernel.accounts
      cell := fun c => if c = 0 then default else createCellPre.kernel.cell c
      caps := fun l => if l = 0 then [] else createCellPre.kernel.caps l
      delegate := fun c => if c = 0 then none else createCellPre.kernel.delegate c
      delegations := fun c => if c = 0 then [] else createCellPre.kernel.delegations c
      slotCaveats := fun c => if c = 0 then [] else createCellPre.kernel.slotCaveats c
      lifecycle := fun c => if c = 0 then 0 else createCellPre.kernel.lifecycle c
      deathCert := fun c => if c = 0 then 0 else createCellPre.kernel.deathCert c
      bal := fun c a => if c = 0 then 0 else createCellPre.kernel.bal c a },
    log := createReceipt 0 0 :: createCellPre.log }

/-- **`CreateCellTraceReadout` is INHABITED.** -/
def createCell_readout :
    CreateCellTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace createCellRow0) createCellPre createCellPost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [createCellRow0]
  growthDecodes := fun _ => rfl
  guard := by constructor
              · decide
              · decide
  born := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  logAdv := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frFactories := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl

theorem createCell_readout_inhabited :
    Nonempty (CreateCellTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0))
      [] (readoutTrace createCellRow0) createCellPre createCellPost 0 0) :=
  ⟨createCell_readout⟩

#assert_axioms createCell_readout

/-! ## §2 — `CreateFromFactoryTraceReadout` INHABITED.

Active row 0 hot at `SEL_FACTORY_RT = 13`, `vk = 0`. A trivial CONFORMING factory entry (empty caveats,
empty initial fields) is registered at vk-key `0` (`findFactory [(0, e)] 0 = some e`, `e.conforms`); the
post `cell`/`slotCaveats` are the factory-install maps over the born-empty bases; the rest are the
born-empty `if c = 0 then … else pre…` forms. -/

/-- A trivial CONFORMING factory entry: no caveats, no initial fields ⇒ `conforms = true`. -/
def factoryE : FactoryEntry := { caveats := [], initialFields := [], programVk := 0 }

def factoryRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT then 1 else 0

/-- The pre boundary: empty accounts, actor `0` holds `node 0`, the factory `factoryE` registered at
content key `0`. -/
def factoryPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default,
                caps := fun a => if a = 0 then [Cap.node 0] else [],
                factories := [(0, factoryE)] },
    log := [] }

def factoryPost : RecChainedState :=
  { kernel := { factoryPre.kernel with
      accounts := insert 0 factoryPre.kernel.accounts
      cell := factoryPostCell (factoryBornCell factoryPre.kernel 0) 0 factoryE
      slotCaveats := factoryPostCaveats (factoryBornCaveats factoryPre.kernel 0) 0 factoryE
      caps := fun l => if l = 0 then [] else factoryPre.kernel.caps l
      delegate := fun c => if c = 0 then none else factoryPre.kernel.delegate c
      delegations := fun c => if c = 0 then [] else factoryPre.kernel.delegations c
      lifecycle := fun c => if c = 0 then 0 else factoryPre.kernel.lifecycle c
      deathCert := fun c => if c = 0 then 0 else factoryPre.kernel.deathCert c
      bal := fun c a => if c = 0 then 0 else factoryPre.kernel.bal c a },
    log := factoryReceipt 0 0 :: factoryPre.log }

/-- **`CreateFromFactoryTraceReadout` is INHABITED.** -/
def createFromFactory_readout :
    CreateFromFactoryTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace factoryRow0) factoryPre factoryPost 0 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [factoryRow0]
  growthDecodes := fun _ => rfl
  e := factoryE
  guard := by
    refine ⟨by decide, ?_, by decide, by decide, by decide⟩
    decide
  frCell := rfl
  frSlotCaveats := rfl
  frBal := rfl
  frCaps := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  logAdv := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frFactories := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl

theorem createFromFactory_readout_inhabited :
    Nonempty (CreateFromFactoryTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0)
      (fun _ => (0, 0)) [] (readoutTrace factoryRow0) factoryPre factoryPost 0 0 0) :=
  ⟨createFromFactory_readout⟩

#assert_axioms createFromFactory_readout

/-! ## §3 — `SpawnTraceReadout` INHABITED.

Active row 0 hot at `SEL_SPAWN_RT = 32`. The actor `9` holds `node 0` (= `node target`, conferring the
parent edge) and `node 1` (= `node child`, the mint authority over child). `target = 0 ∈ accounts`,
`child = 1 ∉ accounts`. The post per-cell maps are the born-empty forms; the cap handoff maps are the
`spawnCapsMap`/`spawnDelegateMap`/`spawnDelegationsMap` (the PHASE-D residual, carried). -/

def spawnRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = Dregg2.Circuit.Emit.EffectVmEmitSpawn.SEL_SPAWN_RT then 1 else 0

/-- The pre boundary: `target = 0` live, actor `9` holds `node 0` (parent edge) + `node 1` (child mint),
`child = 1` fresh. -/
def spawnPre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default,
                caps := fun a => if a = 9 then [Cap.node 0, Cap.node 1] else [] },
    log := [] }

def spawnPost : RecChainedState :=
  { kernel := { spawnPre.kernel with
      accounts := insert 1 spawnPre.kernel.accounts
      cell := fun c => if c = 1 then default else spawnPre.kernel.cell c
      slotCaveats := fun c => if c = 1 then [] else spawnPre.kernel.slotCaveats c
      lifecycle := fun c => if c = 1 then 0 else spawnPre.kernel.lifecycle c
      deathCert := fun c => if c = 1 then 0 else spawnPre.kernel.deathCert c
      bal := fun c a => if c = 1 then 0 else spawnPre.kernel.bal c a
      caps := spawnCapsMap spawnPre.kernel 9 1 0
      delegate := spawnDelegateMap spawnPre.kernel 9 1
      delegations := spawnDelegationsMap spawnPre.kernel 9 1
      delegationEpochAt := spawnEpochAtMap spawnPre.kernel 9 1 },
    log := createReceipt 9 1 :: spawnPre.log }

/-- **`SpawnTraceReadout` is INHABITED** (for EVERY `Cap8Scheme` — the cap-handoff decode seam
`capsMoveDecodes` is an implication discharged `fun _ => rfl`, scheme-independent). -/
def spawn_readout (S8 : Dregg2.Circuit.DeployedCapTree.Cap8Scheme) :
    SpawnTraceReadout S8 (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace spawnRow0) spawnPre spawnPost 9 1 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [spawnRow0]
  growthDecodes := fun _ => rfl
  guard := by
    refine ⟨by decide, ?_, by decide, by decide⟩
    decide
  frCell := rfl
  frSlotCaveats := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frBal := rfl
  capsMoveDecodes := fun _ => rfl
  capHandoff := rfl
  delegateHandoff := rfl
  delegationsHandoff := rfl
  logAdv := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frFactories := rfl
  frDelegationEpoch := rfl
  epochStampResidual := rfl
  frHeaps := rfl

theorem spawn_readout_inhabited (S8 : Dregg2.Circuit.DeployedCapTree.Cap8Scheme) :
    Nonempty (SpawnTraceReadout S8 (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace spawnRow0) spawnPre spawnPost 9 1 0) :=
  ⟨spawn_readout S8⟩

#assert_axioms spawn_readout

end Dregg2.Circuit.FloorsNonVacuousWaveBirth
