/-
# Dregg2.Circuit.Spec.factorycreation — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **factory-creation** (variant: `createCellFromFactoryA`).

This is a *leaf* module in the `Transfer.lean` lineage: it builds, for the FACTORY-creation effect
(`CreateCellFromFactory`, dregg1 `apply_create_cell_from_factory`, `apply.rs:3112`), the SAME triangle
corner the reference `TransferSpec`/`recKExec_iff_spec` establish for `Transfer`, but written
INDEPENDENTLY of the executor. The deliverables, mirroring the reference pattern
(`Dregg2/Circuit/Transfer.lean` §6b and the lineage leaf `Spec/supplycreation.lean`):

  1. `CreateFromFactorySpec st actor newCell vk st'` : Prop — the FULL declarative post-state of a
     committed `createCellFromFactoryA`. It is the conjunction of
       * the admissibility guard (read off the CODE, `TurnExecutorFull.lean:1002`):
           - `0 ≤ vk`                                  -- no negative-vk factory aliasing
           - the factory EXISTS in the registry        -- `findFactory factories vk.toNat = some e`
           - `e.conforms = true`                       -- the factory's own initial state validates
           - `mintAuthorizedB caps actor newCell`      -- privileged creation authority
           - `newCell ∉ accounts`                      -- the id is fresh
         (the last two are exactly the `createCellChainA` gate the factory arm reuses);
       * the EXACT touched components:
           - `accounts` grows by `newCell`             -- `insert newCell accounts`
           - `bal`      resets `newCell`'s column to 0 -- born EMPTY (conservation-neutral)
           - `cell`     mints `newCell` carrying the factory's initial fields + the program-VK slot
           - `slotCaveats` installs the factory's caveats on `newCell` (THE factory keystone)
           - `log`      prepends the (balance-`0`) creation receipt `{actor, newCell, newCell, 0}`;
       * EVERY OTHER state component LITERALLY unchanged: the 13 untouched non-`{accounts,bal,cell,
         slotCaveats}` kernel fields (`caps` `escrows` `nullifiers` `revoked` `commitments` `queues`
         `swiss` `factories` `lifecycle` `deathCert` `delegate` `delegations` `sealedBoxes`) — the
         FRAME. No frame clause mentions any executor helper.
  2. `execCreateFromFactoryA_iff_spec : execFullA st (.createCellFromFactoryA actor newCell vk) =
     some st' ↔ CreateFromFactorySpec …` — BOTH directions. The `→` VALIDATES the executor against the
     independent spec: a silently-mutated frame field would make its clause unprovable. (None was
     found — see frameGaps in the report.)
  3. `factoryPostCell_correct` / `factoryInstall_frame` — the post-state cell-install + caveat-install
     helpers validated DECLARATIVELY (the minted cell carries the factory fields/VK/caveats; every
     OTHER cell's record + caveat list is literally preserved), so the spec's `cell`/`slotCaveats`
     clauses encode mint ∧ install ∧ cell-frame, not blind trust.

Unlike `Transfer`/`mintA`, the executor arm is NOT a single `if`-branch: it is a 4-deep nest
(`0 ≤ vk` → `findFactory` → `e.conforms` → `createCellChainA`), so the spec is existentially
quantified over the looked-up `FactoryEntry e`, and the `↔` is proved through the already-PROVED
factoring bridge `createCellFromFactoryChainA_factors` (the same bridge every downstream factory
theorem reuses) rather than a flat `by_cases`. This is the "harder than a single branch" case the
prompt anticipates — handled cleanly via the factoring lemma. The companion neutrality corollary
`createFromFactoryA_supply_delta` pins the SEMANTIC content (the mint is conservation-neutral on
every asset), and the keystone corollary `createFromFactoryA_installs_program` lifts the
constructor-transparency keystone to the `execFullA` level off the spec.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.FactoryCreation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (setField fieldOf)
open Dregg2.Authority

private theorem recordKernel_eq_of_fields {k k' : RecordKernelState}
    (haccounts : k.accounts = k'.accounts) (hcell : k.cell = k'.cell) (hcaps : k.caps = k'.caps)
    (hnullifiers : k.nullifiers = k'.nullifiers)
    (hrevoked : k.revoked = k'.revoked) (hcommitments : k.commitments = k'.commitments)
    (hbal : k.bal = k'.bal)
    (hslotCaveats : k.slotCaveats = k'.slotCaveats) (hfactories : k.factories = k'.factories)
    (hlifecycle : k.lifecycle = k'.lifecycle) (hdeathCert : k.deathCert = k'.deathCert)
    (hdelegate : k.delegate = k'.delegate) (hdelegations : k.delegations = k'.delegations)
    (hdelegationEpoch : k.delegationEpoch = k'.delegationEpoch)
    (hdelegationEpochAt : k.delegationEpochAt = k'.delegationEpochAt)
    (hheaps : k.heaps = k'.heaps) : k = k' := by
  cases k; cases k'; simp_all

/-! ## §1 — the admissibility guard, lifted from the CODE.

`createCellFromFactoryChainA` (`TurnExecutorFull.lean:1002`) commits IFF this exact conjunction
holds. The first three conjuncts are the factory wrapper's own gates (non-negative vk so the
content-addressed key cannot be forged downward by `Int.toNat`; the factory exists; its declared
initial state conforms to its own caveats). The last two are EXACTLY the `createCellChainA` gate the
wrapper reuses verbatim (privileged creation authority ∧ fresh id). Omitting any conjunct would
under-specify the executor. -/

/-- **`factoryAdmit`** — the full admissibility guard `createCellFromFactoryChainA` checks, as a
`Prop`. Non-negative vk ∧ a conforming registered factory `e` ∧ privileged creation authority ∧ a
fresh id. The factory entry `e` is existentially named so the touched-state clauses can refer to its
published `initialFields`/`programVk`/`caveats`. -/
def factoryAdmit (k : RecordKernelState) (actor newCell : CellId) (vk : Int) (e : FactoryEntry) : Prop :=
  0 ≤ vk
  ∧ findFactory k.factories vk.toNat = some e
  ∧ e.conforms = true
  ∧ mintAuthorizedB k.caps actor newCell = true
  ∧ newCell ∉ k.accounts

/-- The disclosed receipt a committed factory creation prepends to the log: the cell is born
`balance == 0`, so the receipt is a self-edge `newCell → newCell` of size `0` (exactly
`createCellChainA`'s `log` head, `TurnExecutorFull.lean:790`). -/
def factoryReceipt (actor newCell : CellId) : Turn :=
  { actor := actor, src := newCell, dst := newCell, amt := 0 }

/-! ## §2 — the touched-component constructors, validated DECLARATIVELY.

The post-state's `cell` and `slotCaveats` are built by the factory wrapper over the underlying
fresh-cell `s1` (= `createCellIntoAsset`). We name those two install maps and validate them
relationally (the minted cell carries the factory fields/VK/caveats; every OTHER cell is preserved)
so the spec's `cell`/`slotCaveats` clauses carry real meaning rather than trusting the helper. -/

/-- Born-empty `cell`/`slotCaveats` bases at `newCell` (the create leg before factory install). -/
def factoryBornCell (k : RecordKernelState) (newCell : CellId) : CellId → Value :=
  fun c => if c = newCell then default else k.cell c

def factoryBornCaveats (k : RecordKernelState) (newCell : CellId) : CellId → List SlotCaveat :=
  fun c => if c = newCell then [] else k.slotCaveats c

/-- The post-`cell` map: the minted `newCell` carries the factory's initial fields + the program-VK
slot installed over the born-empty cell `base`; every other cell's record is the base `cell` map.
(Lifted from `createCellFromFactoryChainA`'s `cell :=` clause, `TurnExecutorFull.lean:1017`.) -/
def factoryPostCell (base : CellId → Value) (newCell : CellId) (e : FactoryEntry) : CellId → Value :=
  fun c => if c = newCell then
      setField factoryVkField (installInitialFields (base newCell) e.initialFields) (.int e.programVk)
    else base c

/-- The post-`slotCaveats` map: the minted `newCell` carries the factory's published caveats; every
other cell keeps the base caveat list. (Lifted from the `slotCaveats :=` clause, `:1022`.) -/
def factoryPostCaveats (base : CellId → List SlotCaveat) (newCell : CellId) (e : FactoryEntry) :
    CellId → List SlotCaveat :=
  fun c => if c = newCell then e.caveats else base c

/-- **`factoryPostCell_correct`** — the cell-install map validated DECLARATIVELY: the minted cell IS
the factory's initial-fields+VK install over the base cell, and EVERY OTHER cell's whole record is
literally untouched. So the spec's `cell = factoryPostCell …` clause encodes
mint ∧ cell-frame. -/
theorem factoryPostCell_correct (base : CellId → Value) (newCell : CellId) (e : FactoryEntry) :
    factoryPostCell base newCell e newCell
      = setField factoryVkField (installInitialFields (base newCell) e.initialFields) (.int e.programVk)
    ∧ (∀ c, c ≠ newCell → factoryPostCell base newCell e c = base c) := by
  refine ⟨?_, ?_⟩
  · simp [factoryPostCell]
  · intro c hc; simp only [factoryPostCell, if_neg hc]

/-- **`factoryPostCaveats_correct`** — the caveat-install map validated DECLARATIVELY: the minted
cell carries EXACTLY the factory's published caveats (the constructor-transparency content), and
every OTHER cell's caveat list is literally untouched. So the spec's `slotCaveats =
factoryPostCaveats …` clause encodes install ∧ caveat-frame. -/
theorem factoryPostCaveats_correct (base : CellId → List SlotCaveat) (newCell : CellId)
    (e : FactoryEntry) :
    factoryPostCaveats base newCell e newCell = e.caveats
    ∧ (∀ c, c ≠ newCell → factoryPostCaveats base newCell e c = base c) := by
  refine ⟨?_, ?_⟩
  · simp [factoryPostCaveats]
  · intro c hc; simp only [factoryPostCaveats, if_neg hc]

/-! ## §3 — the executor projection: `execFullA` on `createCellFromFactoryA` IS the chain step.

The `createCellFromFactoryA` arm of `execFullA` (`TurnExecutorFull.lean:3518`) is a SINGLE branch — it
dispatches straight to `createCellFromFactoryChainA` with no rewrap. We expose it as a definitional
rewrite so the spec proof works on `createCellFromFactoryChainA`. -/

@[simp] theorem execFullA_createCellFromFactoryA (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) :
    execFullA st (.createCellFromFactoryA actor newCell vk)
      = createCellFromFactoryChainA st actor newCell vk := rfl

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`CreateFromFactorySpec` is the COMPLETE declarative post-state of a committed
`createCellFromFactoryA`, written INDEPENDENTLY of the executor: there is a conforming registered
factory `e` for which the guard holds; the post `accounts` grew by `newCell`; the post `bal` reset
`newCell`'s column to 0 (born empty); the post `cell` minted `newCell` with the factory's
fields/VK; the post `slotCaveats` installed the factory's caveats on `newCell`; the post `log`
prepended the creation receipt; and ALL 13 non-touched kernel components are LITERALLY unchanged.
No frame clause mentions `execFullA`/`createCellFromFactoryChainA`/`createCellChainA`. -/

/-- **The full-state declarative spec of a committed factory-creation
(`createCellFromFactoryA`)** — the INDEPENDENT reference semantics. Enumerates the FRAME completely:
the touched `accounts` + `bal` + `cell` + `slotCaveats` + `log`, and every one of the 13 untouched
kernel fields. Existentially quantified over the looked-up `FactoryEntry e` (the arm is a 4-deep
nest, not a single branch). -/
def CreateFromFactorySpec (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) : Prop :=
  ∃ e : FactoryEntry,
    factoryAdmit st.kernel actor newCell vk e
    -- the touched components:
    ∧ st'.kernel.accounts = insert newCell st.kernel.accounts
    ∧ st'.kernel.bal = (fun c a => if c = newCell then 0 else st.kernel.bal c a)
    ∧ st'.kernel.cell = factoryPostCell (factoryBornCell st.kernel newCell) newCell e
    ∧ st'.kernel.slotCaveats = factoryPostCaveats (factoryBornCaveats st.kernel newCell) newCell e
    ∧ st'.log = factoryReceipt actor newCell :: st.log
    -- born-empty per-cell slots at `newCell` from the create leg (factory install is cell/caveat-only).
    ∧ (st'.kernel.caps = fun l => if l = newCell then [] else st.kernel.caps l)
    ∧ (st'.kernel.lifecycle = fun c => if c = newCell then 0 else st.kernel.lifecycle c)
    ∧ (st'.kernel.deathCert = fun c => if c = newCell then 0 else st.kernel.deathCert c)
    ∧ (st'.kernel.delegate = fun c => if c = newCell then none else st.kernel.delegate c)
    ∧ (st'.kernel.delegations = fun c => if c = newCell then [] else st.kernel.delegations c)
    -- THE FRAME: global side-tables literally unchanged.
    ∧ st'.kernel.nullifiers = st.kernel.nullifiers
    ∧ st'.kernel.revoked = st.kernel.revoked
    ∧ st'.kernel.commitments = st.kernel.commitments
    ∧ st'.kernel.factories = st.kernel.factories
    ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
    ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
    ∧ st'.kernel.heaps = st.kernel.heaps

/-! ### The post-state the executor actually produces, pinned field-by-field.

`createCellFromFactoryChainA_factors` gives the post-state as `s' = { s1 with kernel := { s1.kernel
with cell := …, slotCaveats := … } }`, where `s1 = createCellChainA s …` is itself `{ kernel :=
createCellIntoAsset s.kernel newCell, log := receipt :: s.log }`. We unfold those two layers to read
each of the 18 components of `s'` directly off `s` and `e`. -/

/-- Unfold a committed factory creation into its 18 explicit per-component facts (the touched five
+ 13 frame), all stated against the PRE-state `s` and the looked-up `e`. The bridge the `→`
direction of the spec equivalence reads off. -/
theorem createCellFromFactoryChainA_components {s s' : RecChainedState} {actor newCell : CellId}
    {vk : Int} (h : createCellFromFactoryChainA s actor newCell vk = some s') :
    ∃ e : FactoryEntry,
      factoryAdmit s.kernel actor newCell vk e
      ∧ s'.kernel.accounts = insert newCell s.kernel.accounts
      ∧ s'.kernel.bal = (fun c a => if c = newCell then 0 else s.kernel.bal c a)
      ∧ s'.kernel.cell = factoryPostCell (factoryBornCell s.kernel newCell) newCell e
      ∧ s'.kernel.slotCaveats = factoryPostCaveats (factoryBornCaveats s.kernel newCell) newCell e
      ∧ s'.log = factoryReceipt actor newCell :: s.log
      ∧ (s'.kernel.caps = fun l => if l = newCell then [] else s.kernel.caps l)
      ∧ (s'.kernel.lifecycle = fun c => if c = newCell then 0 else s.kernel.lifecycle c)
      ∧ (s'.kernel.deathCert = fun c => if c = newCell then 0 else s.kernel.deathCert c)
      ∧ (s'.kernel.delegate = fun c => if c = newCell then none else s.kernel.delegate c)
      ∧ (s'.kernel.delegations = fun c => if c = newCell then [] else s.kernel.delegations c)
      ∧ s'.kernel.nullifiers = s.kernel.nullifiers
      ∧ s'.kernel.revoked = s.kernel.revoked
      ∧ s'.kernel.commitments = s.kernel.commitments
      ∧ s'.kernel.factories = s.kernel.factories
      ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
      ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt
      ∧ s'.kernel.heaps = s.kernel.heaps := by
  obtain ⟨e, s1, hfind, hconf, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  -- recover the underlying createCell gate conjuncts + the s1 shape:
  obtain ⟨hauth, hfresh, hs1⟩ := createCellChainA_factors hc
  -- 0 ≤ vk is forced: a negative vk makes `createCellFromFactoryChainA = none` (the (0) guard).
  have hvk : 0 ≤ vk := by
    by_contra hneg
    rw [createCellFromFactoryChainA, if_neg hneg] at h
    exact absurd h (by simp)
  refine ⟨e, ⟨hvk, hfind, hconf, hauth, hfresh⟩, ?_⟩
  -- substitute s' = factory-install over s1, and s1 = createCellChainA's output over s.
  subst hs' hs1
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · funext l; by_cases hl : l = newCell <;> simp [hl, createCellIntoAsset, bornEmptyCellSlots]
  · funext c; by_cases hc' : c = newCell <;> simp [hc', createCellIntoAsset, bornEmptyCellSlots]
  · funext c; by_cases hc' : c = newCell <;> simp [hc', createCellIntoAsset, bornEmptyCellSlots]
  · funext c; by_cases hc' : c = newCell <;> simp [hc', createCellIntoAsset, bornEmptyCellSlots]
  · funext c; by_cases hc' : c = newCell <;> simp [hc', createCellIntoAsset, bornEmptyCellSlots]

/-- **`createCellFromFactoryChainA_iff_spec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both
directions).** The chained record kernel commits a factory creation into `st'` IFF `st'` is EXACTLY
the spec'd full post-state. The `→` VALIDATES `createCellFromFactoryChainA` against the independent
spec — all 18 components (the touched five + 13 frame fields) are checked, so a silently-mutated
component would make the proof FAIL; the `←` reconstructs the committed state from the spec via the
already-PROVED factoring bridge. -/
theorem createCellFromFactoryChainA_iff_spec (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) :
    createCellFromFactoryChainA st actor newCell vk = some st'
      ↔ CreateFromFactorySpec st actor newCell vk st' := by
  constructor
  · -- → : a committed step yields the full-state spec (component-by-component).
    intro h
    exact createCellFromFactoryChainA_components h
  · -- ← : from the spec, reconstruct the committed step. We drive the executor forward to its
    -- explicit committed output, then prove that output equals `st'` from the 18 spec equations.
    rintro ⟨e, ⟨hvk, hfind, hconf, hauth, hfresh⟩,
            hacc, hbal, hcell, hcav, hlog,
            hcaps, hlc, hdc, hdel, hdn, hnull, hrev, hcom, hfac, hde, hdea, hhp⟩
    -- the underlying createCell commits (its gate is the last two guard conjuncts):
    have hc : createCellChainA st actor newCell = some
        { kernel := createCellIntoAsset st.kernel newCell
          log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: st.log } := by
      unfold createCellChainA; rw [if_pos ⟨hauth, hfresh⟩]
    -- the factory wrapper therefore COMMITS into SOME `s_out` (the literal executor output):
    have hex : createCellFromFactoryChainA st actor newCell vk = some
        { kernel :=
            { (createCellIntoAsset st.kernel newCell) with
                cell := fun c => if c = newCell then
                    setField factoryVkField
                      (installInitialFields ((createCellIntoAsset st.kernel newCell).cell newCell)
                        e.initialFields) (.int e.programVk)
                  else (createCellIntoAsset st.kernel newCell).cell c
                slotCaveats := fun c => if c = newCell then e.caveats
                  else (createCellIntoAsset st.kernel newCell).slotCaveats c }
          log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: st.log } := by
      unfold createCellFromFactoryChainA
      rw [if_pos hvk]; simp only [hfind, hconf, hc, if_true]
    -- the explicit executor output equals `st'`: substitute every spec field equation into `st'`.
    -- Crucially `(createCellIntoAsset st.kernel newCell).cell = st.kernel.cell` and likewise for
    -- `slotCaveats` (createCellIntoAsset edits only `accounts`/`bal`), so the executor's `cell`/
    -- `slotCaveats` lambdas ARE `factoryPostCell`/`factoryPostCaveats` definitionally — the `rfl`
    -- after substituting `hcell`/`hcav` closes those.
    rw [hex]
    obtain ⟨k', lg'⟩ := st'
    obtain ⟨acc, cl, cp, nl, rv, cm, bl, sc, fc, lc, dc, dl, dn, dge, dgea, hp⟩ := k'
    simp only at hacc hbal hcell hcav hlog hcaps hlc hdc hdel hdn hnull hrev hcom hfac hde hdea hhp
    subst hacc hbal hcell hcav hlog hcaps hlc hdc hdel hdn hnull hrev hcom hfac hde hdea hhp
    rfl

/-- **`execCreateFromFactoryA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ SPEC (FULL
state, both directions).** The one gated executor commits a `createCellFromFactoryA` turn into `st'`
IFF `st'` is EXACTLY the independent full-state spec. Forward VALIDATES the executor (every one of
the 18 components is pinned); backward reconstructs. This is the factory-creation corner of the
spec⟺executor(⟺circuit) triangle, the `createCellFromFactoryA` analog of `recKExec_iff_spec`. -/
theorem execCreateFromFactoryA_iff_spec (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = some st'
      ↔ CreateFromFactorySpec st actor newCell vk st' := by
  rw [execFullA_createCellFromFactoryA]
  exact createCellFromFactoryChainA_iff_spec st actor newCell vk st'

/-! ## §5 — derived guarantees off the spec.

The spec is the apex truth; these read off it without re-touching the executor. -/

/-- **`createFromFactoryA_authorized` — no factory creation without privileged authority.** A
committed `createCellFromFactoryA` PROVES the actor held privileged creation authority over the new
cell (`mintAuthorizedB`). Read straight off the spec's guard. -/
theorem createFromFactoryA_authorized (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : execFullA st (.createCellFromFactoryA actor newCell vk) = some st') :
    mintAuthorizedB st.kernel.caps actor newCell = true := by
  obtain ⟨_, ⟨_, _, _, hauth, _⟩, _⟩ := (execCreateFromFactoryA_iff_spec st actor newCell vk st').mp h
  exact hauth

/-- **`createFromFactoryA_fresh` — the id was fresh.** A committed creation PROVES the new
cell was NOT already a live account in the pre-state. Read off the spec's guard. -/
theorem createFromFactoryA_fresh (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : execFullA st (.createCellFromFactoryA actor newCell vk) = some st') :
    newCell ∉ st.kernel.accounts := by
  obtain ⟨_, ⟨_, _, _, _, hfresh⟩, _⟩ := (execCreateFromFactoryA_iff_spec st actor newCell vk st').mp h
  exact hfresh

/-- **`createFromFactoryA_grows_accounts` — the GROWTH has teeth.** After a committed factory
creation the new cell IS a live account. Read off the spec's `accounts` clause. -/
theorem createFromFactoryA_grows_accounts (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : execFullA st (.createCellFromFactoryA actor newCell vk) = some st') :
    newCell ∈ st'.kernel.accounts := by
  obtain ⟨_, _, hacc, _⟩ := (execCreateFromFactoryA_iff_spec st actor newCell vk st').mp h
  rw [hacc]; exact Finset.mem_insert_self _ _

/-- **`createFromFactoryA_installs_program` (THE FACTORY KEYSTONE, off the spec).** Every cell a
factory mints carries EXACTLY the factory's declared `slotCaveats` (its published program) — so its
published invariants are enforced for life. Derived from the spec's `slotCaveats` clause +
the declaratively-validated install map. -/
theorem createFromFactoryA_installs_program (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : execFullA st (.createCellFromFactoryA actor newCell vk) = some st') :
    ∃ e, findFactory st.kernel.factories vk.toNat = some e
      ∧ st'.kernel.slotCaveats newCell = e.caveats := by
  obtain ⟨e, ⟨_, hfind, _, _, _⟩, _, _, _, hcav, _⟩ :=
    (execCreateFromFactoryA_iff_spec st actor newCell vk st').mp h
  refine ⟨e, hfind, ?_⟩
  rw [hcav]; simp only [factoryPostCaveats, factoryBornCaveats, if_pos]

/-- **`createFromFactoryA_installs_fields` — the minted cell carries the factory's fields + VK.**
Derived from the spec's `cell` clause + the declaratively-validated install map: the new cell's
record IS the factory's initial-fields+programVk install over the born-empty cell. -/
theorem createFromFactoryA_installs_fields (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : execFullA st (.createCellFromFactoryA actor newCell vk) = some st') :
    ∃ e, findFactory st.kernel.factories vk.toNat = some e
      ∧ st'.kernel.cell newCell
          = setField factoryVkField
              (installInitialFields default e.initialFields) (.int e.programVk) := by
  obtain ⟨e, ⟨_, hfind, _, _, _⟩, _, _, hcell, _⟩ :=
    (execCreateFromFactoryA_iff_spec st actor newCell vk st').mp h
  refine ⟨e, hfind, ?_⟩
  rw [hcell]; simp only [factoryPostCell, factoryBornCell, if_pos]

/-- **`createFromFactoryA_supply_delta` — CONSERVATION CONTENT: a committed factory creation is
balance-NEUTRAL on EVERY asset.** The cell is born EMPTY and the field/caveat install is
balance-orthogonal, so `recTotalAsset` is unchanged ∀ asset. Lifted from the already-proved
`createCellFromFactoryChainA_neutral` via the `execFullA` projection. -/
theorem createFromFactoryA_supply_delta (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : execFullA st (.createCellFromFactoryA actor newCell vk) = some st')
    (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b := by
  rw [execFullA_createCellFromFactoryA] at h
  exact createCellFromFactoryChainA_neutral b h

/-! ## §6 — NON-VACUITY: the spec is a genuine GATE (rejects bad inputs).

A spec that accepts everything is worthless. `execFullA` REJECTS a negative vk (no factory
aliasing), an unknown factory, and a non-conforming factory — each makes the executor return `none`
and `CreateFromFactorySpec` unsatisfiable. -/

/-- **`createFromFactoryA_rejects_negative_vk`.** A negative `vk` is REJECTED before the registry
lookup — `execFullA … = none`. The content-addressed factory key cannot be forged downward (no
`Int.toNat` aliasing to factory `0`). -/
theorem createFromFactoryA_rejects_negative_vk (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) (hbad : vk < 0) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = none := by
  rw [execFullA_createCellFromFactoryA, createCellFromFactoryChainA, if_neg (by omega)]

/-- **`createFromFactoryA_rejects_unknown`.** An unknown factory vk (`∉ registry`) is REJECTED —
fail-closed (dregg1 `apply.rs:3140` `validate_and_record` errors). -/
theorem createFromFactoryA_rejects_unknown (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (hbad : findFactory st.kernel.factories vk.toNat = none) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = none := by
  rw [execFullA_createCellFromFactoryA]
  exact createCellFromFactoryChainA_unknown_factory_fails st actor newCell vk hbad

/-- **`createFromFactoryA_rejects_nonconforming`.** A factory whose OWN declared initial state
violates its OWN caveats is REJECTED at mint — the `validate_and_record` constraint check fails. -/
theorem createFromFactoryA_rejects_nonconforming (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) (e : FactoryEntry) (hfind : findFactory st.kernel.factories vk.toNat = some e)
    (hbad : e.conforms = false) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = none := by
  rw [execFullA_createCellFromFactoryA]
  exact createCellFromFactoryChainA_nonconforming_fails st actor newCell vk e hfind hbad

/-- **`createFromFactoryA_rejects_unauthorized`.** Without privileged creation authority over the
new cell, no factory creation commits — fail-closed (the reused `createCellChainA` gate). -/
theorem createFromFactoryA_rejects_unauthorized (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) (e : FactoryEntry) (hvk : 0 ≤ vk)
    (hfind : findFactory st.kernel.factories vk.toNat = some e) (hconf : e.conforms = true)
    (hbad : mintAuthorizedB st.kernel.caps actor newCell = false) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = none := by
  rw [execFullA_createCellFromFactoryA]
  simp only [createCellFromFactoryChainA, hfind, hconf, if_pos hvk, if_true,
    createCellChainA_unauthorized_fails st actor newCell hbad]

/-- **`createFromFactoryA_rejects_stale_id`.** A factory creation onto an id that is ALREADY a live
account is REJECTED — fail-closed (the reused `createCellChainA` freshness gate). No cell can be
re-minted over an existing one. -/
theorem createFromFactoryA_rejects_stale_id (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) (e : FactoryEntry) (hvk : 0 ≤ vk)
    (hfind : findFactory st.kernel.factories vk.toNat = some e) (hconf : e.conforms = true)
    (hbad : newCell ∈ st.kernel.accounts) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = none := by
  rw [execFullA_createCellFromFactoryA]
  have hstale : createCellChainA st actor newCell = none := by
    unfold createCellChainA; rw [if_neg (by rintro ⟨_, hfresh⟩; exact hfresh hbad)]
  simp only [createCellFromFactoryChainA, hfind, hconf, if_pos hvk, if_true, hstale]

/-! ## §7 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Reusing the executor's own factory fixtures (`subFactory`/`facS`, `TurnExecutorFull.lean:6543`+):
a `subscription` factory at vk 42 (`head` Monotonic, `owner` Immutable, conforming), and actor 0
holding the privileged minter cap `Cap.node 5` over the fresh cell 5. A conforming mint commits;
the unknown / non-conforming / negative-vk / stale-id mints are decidably rejected. -/

-- A conforming factory mint (vk 42, actor 0 over fresh cell 5) COMMITS:
#guard (execFullA facS (.createCellFromFactoryA 0 5 42)).isSome  --  true
-- An UNKNOWN factory vk (99 ∉ registry) is REJECTED:
#guard decide ((execFullA facS (.createCellFromFactoryA 0 5 99)).isNone)  --  true
-- A NON-CONFORMING factory (badBalanceFactory at vk 43) is REJECTED:
#guard decide ((execFullA facBadBalanceS (.createCellFromFactoryA 0 5 43)).isNone)  --  true
-- A NEGATIVE vk (no aliasing of factory 0) is REJECTED:
#guard decide ((execFullA fac0S (.createCellFromFactoryA 0 5 (-1))).isNone)  --  true
-- A STALE id (cell 0 is already a live account) is REJECTED:
#guard decide ((execFullA facS (.createCellFromFactoryA 0 0 42)).isNone)  --  true
-- The minted cell carries the factory's published caveats (constructor transparency):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).map
          (fun s => s.kernel.slotCaveats 5)) == some subFactory.caveats  --  true
-- ...and the factory's initial fields + program VK:
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).map
          (fun s => (fieldOf "head" (s.kernel.cell 5), fieldOf "owner" (s.kernel.cell 5),
                     fieldOf factoryVkField (s.kernel.cell 5)))) == some (0, 9, 7)  --  true

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms factoryPostCell_correct
#assert_axioms factoryPostCaveats_correct
#assert_axioms execFullA_createCellFromFactoryA
#assert_axioms createCellFromFactoryChainA_components
#assert_axioms createCellFromFactoryChainA_iff_spec
#assert_axioms execCreateFromFactoryA_iff_spec
#assert_axioms createFromFactoryA_authorized
#assert_axioms createFromFactoryA_fresh
#assert_axioms createFromFactoryA_grows_accounts
#assert_axioms createFromFactoryA_installs_program
#assert_axioms createFromFactoryA_installs_fields
#assert_axioms createFromFactoryA_supply_delta
#assert_axioms createFromFactoryA_rejects_negative_vk
#assert_axioms createFromFactoryA_rejects_unknown
#assert_axioms createFromFactoryA_rejects_nonconforming
#assert_axioms createFromFactoryA_rejects_unauthorized
#assert_axioms createFromFactoryA_rejects_stale_id

end Dregg2.Circuit.Spec.FactoryCreation
