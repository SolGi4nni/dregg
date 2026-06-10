/-
# Dregg2.Circuit.Argus.Effects.CreateCellFromFactory — `CreateCellFromFactory` welded into the Argus
IR. The LAST account-growing effect (the factory-templated sibling of `CreateCell`).

## THE SHAPE — `CreateCell` PLUS the factory install (mint a cell carrying a published program).

`createCellFromFactoryChainA` (`Exec/TurnExecutorFull.lean:1019`) is `CreateCell` with a richer gate
and two extra component writes on the freshly-minted cell:

    createCellFromFactoryChainA s actor newCell vk
      = if 0 ≤ vk then
          match findFactory s.kernel.factories vk.toNat with
          | none   => none                                  -- (1) unknown factory: fail closed
          | some e => if e.conforms = true then              -- (2) factory's own state validates
              match createCellChainA s actor newCell with    -- (3) the createCell gate (priv + fresh)
              | some s1 => some { s1 with kernel := { s1.kernel with
                    cell        := install factory initialFields + programVk slot at newCell
                    slotCaveats := install factory caveats at newCell } }
              | none => none
            else none
        else none                                            -- (0) negative vk: no factory aliasing

So: the SAME structural account growth `CreateCell` performs (`allocCell`, whose `interp` IS
`createCellIntoAsset` — grow `accounts`, reset born-empty per-cell slots), wrapped in the factory
admissibility gate, THEN two record-update writes on the minted cell — `cell` (the factory's initial
fields + the program-VK slot) and `slotCaveats` (the factory's published caveats, THE constructor
keystone). The two extra writes are exactly the §A component-write primitives `setCell`/`setSlotCaveats`
the IR already carries — NO new primitive is needed (the prompt's hypothesis confirmed: `allocCell`
suffices for the growth, the factory read is a guard, and the field/caveat installs are component writes).

## THE TERM (gate, then alloc, then the two factory installs)

`createCellFromFactoryStmt actor newCell vk` =
    seq (guard <factory gate>)
      (seq (allocCell (fun _ => newCell))
        (seq (setCell {newCell} <factory cell leaf>)
             (setSlotCaveats <factory caveats map>)))

The factory cell-leaf / caveats-map closures re-derive the looked-up `FactoryEntry` from the
INTERMEDIATE state's `factories` registry (via `findFactory k.factories vk.toNat`); since neither
`allocCell` nor `setCell` touches `factories`, the lookup is STABLE through the chain, so the closures
see the SAME `e` the gate validated — matching `createCellFromFactoryChainA`'s post-state term-for-term.

## WHAT THIS MODULE PROVES (mirroring `Effects/CreateCell.lean` — the account-growth weld template)

  1. `interp_createCellFromFactoryStmt_eq_chainK` — THE CORNERSTONE (executor-refinement): `interp` of
     the factory-create term IS the raw-kernel factory allocator (the 4-deep gate, then the factory
     install `factoryKernelPost` over `createCellIntoAsset`) — by construction. `factoryKernelPost` is
     proved to be EXACTLY the kernel `createCellFromFactoryChainA` installs (`factoryKernelPost_eq_chain`).
  2. `interp_createCellFromFactoryStmt_chained` — the cornerstone exposed at the `execFullA` level (the
     `createCellFromFactoryA` arm is a single dispatch to `createCellFromFactoryChainA`), both directions.
  3. `createCellFromFactory_compile_sound` — THE COMPILE WELD against the factory effect's OWN full-state
     v2 quint (`EffectCommit5`) descriptor (`createFromFactoryE` / `createCellFromFactoryA_full_sound`,
     `Inst/createCellFromFactoryA.lean`): a satisfying circuit witness AGREES with the WHOLE post-state the
     IR term's executor produces — every one of the 18 components (`accounts` grown, `bal`/born-empty
     authority slots reset at `newCell`, the factory `cell`/`slotCaveats` installs, the creation receipt,
     every global side-table frozen). The circuit pins `CreateFromFactoryCircuitSpec`; we bridge it to the
     executor's `CreateFromFactorySpec` (the bundled-vs-explicit born-empty-authority forms are PROVABLY
     equivalent via `bornEmptyAuthority_post_iff`), then collapse to one welded post-state.
  4. Non-vacuity teeth: a concrete factory mint genuinely GROWS `accounts` (fresh id absent→present) AND
     installs the factory's published caveats; the gate REJECTS a negative vk, an unknown factory, an
     unauthorized creation, and a re-mint of a live id (fail-closed).

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the whole-function /
digest-injectivity assumptions enter ONLY inside the reused `createCellFromFactoryA_full_sound` (its
hypotheses), never in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only (`Argus/Stmt` for the IR + `Inst/createCellFromFactoryA` for the audited quint
descriptor; the executor⟺spec corner rides in transitively via the Inst import). This file owns only its
own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState

namespace Dregg2.Circuit.Argus.Effects.CreateCellFromFactory

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (setField)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/createCellFromFactoryA.lean` so the standalone-descriptor names resolve.
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit5 (satisfiedE2Quint encodeE2Quint)
open Dregg2.Circuit.BornEmptyCommit
  (BornEmptyAuthorityTables bornEmptyAuthority_post_iff)
open Dregg2.Circuit.Spec.FactoryCreation
  (factoryAdmit factoryReceipt factoryBornCell factoryBornCaveats factoryPostCell factoryPostCaveats
    CreateFromFactorySpec execCreateFromFactoryA_iff_spec createFromFactoryA_grows_accounts
    createFromFactoryA_installs_program)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
  (CreateFromFactoryArgs createFromFactoryE createCellFromFactoryA_full_sound
    CreateFromFactoryCircuitSpec RestIffNoFactoryTouched)

/-! ## §1 — the factory-create effect as an Argus IR term (gate, then alloc, then the two factory installs).

`createCellFromFactoryChainA` is a 4-deep gate (`0 ≤ vk` → factory found → conforms → createCell gate),
then `createCellIntoAsset` (the structural growth), then the factory `cell`/`slotCaveats` installs on the
minted cell. We capture its kernel action term-for-term: a `Bool` `guard` of the EXACT gate, then
`allocCell (fun _ => newCell)` (the §A′ structural allocator, the ONLY primitive that grows `accounts`),
then `setCell {newCell}` (the factory initial-fields+VK install) and `setSlotCaveats` (the factory
caveats install) — both §A component-write primitives. The factory entry the two installs reference is
re-derived from the intermediate state's `factories` registry, which `allocCell`/`setCell` leave fixed. -/

/-- The factory-create admissibility gate as a `Bool` — exactly `createCellFromFactoryChainA`'s 4-deep
`if`/`match` nest: non-negative vk (no `Int.toNat` aliasing of factory `0`), a registered factory that
`conforms`, then the reused `createCellChainA` gate (privileged creation authority ∧ a fresh id). The
factory lookup is a `match` on `findFactory`; `none` ⇒ `false`. This decodes to the spec's existential
`∃ e, factoryAdmit …`. -/
def createCellFromFactoryGuard (actor newCell : CellId) (vk : Int) (k : RecordKernelState) : Bool :=
  decide (0 ≤ vk)
    && (match findFactory k.factories vk.toNat with
        | none   => false
        | some e => e.conforms)
    && mintAuthorizedB k.caps actor newCell
    && decide (newCell ∉ k.accounts)

/-- The post-`cell` map the term writes: re-derive the looked-up `FactoryEntry` from the (intermediate)
state's `factories` registry and install its initial fields + the program-VK slot at `newCell`, every
other cell preserved — EXACTLY `createCellFromFactoryChainA`'s `cell :=` clause. The `none` arm is dead
under the gate. -/
def factoryCellWrite (vk : Int) (newCell : CellId) (k : RecordKernelState) : CellId → Value :=
  fun c => if c = newCell then
      (match findFactory k.factories vk.toNat with
        | some e => setField factoryVkField (installInitialFields (k.cell newCell) e.initialFields) (.int e.programVk)
        | none   => k.cell c)
    else k.cell c

/-- The post-`slotCaveats` map the term writes: install the looked-up factory's published caveats on
`newCell`, every other cell preserved — EXACTLY `createCellFromFactoryChainA`'s `slotCaveats :=` clause. -/
def factoryCaveatsWrite (vk : Int) (newCell : CellId) (k : RecordKernelState) : CellId → List SlotCaveat :=
  fun c => if c = newCell then
      (match findFactory k.factories vk.toNat with | some e => e.caveats | none => k.slotCaveats c)
    else k.slotCaveats c

/-- **The factory-create effect as an IR term: gate, then alloc, then the two factory installs.** Mirrors
`createCellStmt` (gate, then `allocCell`) but the gate is the factory wrapper's 4-deep gate and the body
chains the two extra factory component writes after the allocation: `setCell {newCell}` (the factory
initial-fields + program-VK install) and `setSlotCaveats` (the factory caveats install). Both extra
writes read their `FactoryEntry` off the post-`allocCell` `factories` registry, which `allocCell` leaves
unchanged — so they see the SAME `e` the gate validated. -/
def createCellFromFactoryStmt (actor newCell : CellId) (vk : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (createCellFromFactoryGuard actor newCell vk))
    (RecStmt.seq (RecStmt.allocCell (fun _ => newCell))
      (RecStmt.seq
        (RecStmt.setCell ({newCell} : Finset CellId) (fun k _ => factoryCellWrite vk newCell k newCell))
        (RecStmt.setSlotCaveats (fun k => factoryCaveatsWrite vk newCell k))))

/-! ## §2 — the cornerstone: `interp` of the factory-create term IS the raw-kernel factory allocator. -/

/-- A field-wise extensionality for `RecordKernelState` (the structure carries no `@[ext]`): two states
agreeing on every component are equal. The local analog of the spec file's `recordKernel_eq_of_fields`. -/
theorem recordKernelState_ext {k k' : RecordKernelState}
    (haccounts : k.accounts = k'.accounts) (hcell : k.cell = k'.cell) (hcaps : k.caps = k'.caps)
    (hnullifiers : k.nullifiers = k'.nullifiers)
    (hrevoked : k.revoked = k'.revoked) (hcommitments : k.commitments = k'.commitments)
    (hbal : k.bal = k'.bal) (hqueues : k.queues = k'.queues) (hswiss : k.swiss = k'.swiss)
    (hslotCaveats : k.slotCaveats = k'.slotCaveats) (hfactories : k.factories = k'.factories)
    (hlifecycle : k.lifecycle = k'.lifecycle) (hdeathCert : k.deathCert = k'.deathCert)
    (hdelegate : k.delegate = k'.delegate) (hdelegations : k.delegations = k'.delegations)
    (hsealedBoxes : k.sealedBoxes = k'.sealedBoxes)
    (hdelegationEpoch : k.delegationEpoch = k'.delegationEpoch)
    (hdelegationEpochAt : k.delegationEpochAt = k'.delegationEpochAt) : k = k' := by
  cases k; cases k'; simp_all

/-- `factoryAdmit` is a conjunction of decidable propositions (a `0 ≤ vk`, a `findFactory` equality, two
`Bool = true`, and a `Finset` non-membership), so it is decidable. -/
instance (k : RecordKernelState) (actor newCell : CellId) (vk : Int) (e : FactoryEntry) :
    Decidable (factoryAdmit k actor newCell vk e) := by
  unfold factoryAdmit; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The existential gate `∃ e, factoryAdmit k actor newCell vk e` is decidable: the witness, if any, is
the UNIQUE looked-up `findFactory k.factories vk.toNat` (a functional lookup), so the existential reduces
to a decision over that single candidate (mirrors the Inst file's `createFromFactoryGuardProp` instance). -/
instance factoryAdmitExists_decidable (k : RecordKernelState) (actor newCell : CellId) (vk : Int) :
    Decidable (∃ e : FactoryEntry, factoryAdmit k actor newCell vk e) := by
  cases hf : findFactory k.factories vk.toNat with
  | none =>
    exact isFalse (by rintro ⟨e, _, hfind, _⟩; rw [hf] at hfind; exact absurd hfind (by simp))
  | some e =>
    by_cases hga : factoryAdmit k actor newCell vk e
    · exact isTrue ⟨e, hga⟩
    · refine isFalse ?_
      rintro ⟨e', hvk, hfind, hrest⟩
      rw [hf] at hfind
      exact hga ⟨hvk, hf, (Option.some.inj hfind) ▸ hrest⟩

/-- The factory-create `Bool` gate decodes to the spec's existential admissibility `∃ e, factoryAdmit`.
The factory analog of `createCellGuard_iff`. The `match` on `findFactory` collapses to the existential:
`true` iff the lookup succeeds with a conforming entry AND the createCell gate holds. -/
theorem createCellFromFactoryGuard_iff (actor newCell : CellId) (vk : Int) (k : RecordKernelState) :
    createCellFromFactoryGuard actor newCell vk k = true
      ↔ ∃ e : FactoryEntry, factoryAdmit k actor newCell vk e := by
  unfold createCellFromFactoryGuard factoryAdmit
  cases hf : findFactory k.factories vk.toNat with
  | none =>
    -- the `match` arm is `false`, and `factoryAdmit`'s `findFactory … = some e'` is now `none = some e'`.
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, false_iff, not_exists]
    rintro e ⟨_, hfind, _⟩
    exact absurd hfind (by simp)
  | some e =>
    -- the `match` arm is `e.conforms`; `factoryAdmit`'s lookup is now `some e = some e'`.
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨hvk, hconf⟩, hauth⟩, hfresh⟩
      exact ⟨e, hvk, rfl, hconf, hauth, hfresh⟩
    · rintro ⟨e', hvk, hfind, hconf, hauth, hfresh⟩
      have heq : e = e' := Option.some.inj hfind
      subst heq
      exact ⟨⟨⟨hvk, hconf⟩, hauth⟩, hfresh⟩

/-- The `factories` registry is FIXED by `allocCell`: `createCellIntoAsset` resets per-cell slots and grows
`accounts`, never the global `factories` list. So the factory lookup the two installs perform on the
post-`allocCell` state agrees with the lookup on the pre-state — the closures see the SAME entry the gate
validated. -/
theorem createCellIntoAsset_factories (k : RecordKernelState) (newCell : CellId) :
    (createCellIntoAsset k newCell).factories = k.factories := by
  simp [createCellIntoAsset, bornEmptyCellSlots]

/-- The born-empty cell at `newCell` reads `default` (`createCellIntoAsset` reset its `cell` slot). The
helper that lets the factory leaf's `installInitialFields ((createCellIntoAsset …).cell newCell)` reduce
to `installInitialFields default`, matching the spec's `factoryBornCell`. -/
theorem createCellIntoAsset_cell_fresh (k : RecordKernelState) (newCell : CellId) :
    (createCellIntoAsset k newCell).cell newCell = default := by
  simp [createCellIntoAsset, bornEmptyCellSlots]

/-- **`factoryKernelPost`** — the explicit kernel post-state of a committed factory creation: the factory
`cell`/`slotCaveats` installs over the born-empty allocator `createCellIntoAsset k newCell`. This is the
kernel the term's `interp` produces on a successful gate; `factoryKernelPost_eq_chain` proves it IS the
kernel `createCellFromFactoryChainA` installs (modulo the receipt log). -/
def factoryKernelPost (vk : Int) (newCell : CellId) (k : RecordKernelState) : RecordKernelState :=
  let k1 := createCellIntoAsset k newCell
  { k1 with
      cell        := factoryCellWrite vk newCell k1
      slotCaveats := factoryCaveatsWrite vk newCell k1 }

/-- **The cornerstone (factory account allocation).** `interp` of the factory-create term IS the
raw-kernel factory allocator: it commits to `factoryKernelPost` (the factory install over
`createCellIntoAsset`) precisely when the 4-deep gate (`∃ e, factoryAdmit`) holds, and rejects otherwise —
the same partial function `createCellFromFactoryChainA` runs on the kernel, by construction
(`factoryKernelPost_eq_chain` then identifies the post-state with the chained executor's kernel). The
`allocCell` clause supplies the account growth; the two following component writes supply the factory
installs, reading the registry off the (unchanged) intermediate state. -/
theorem interp_createCellFromFactoryStmt_eq_chainK (actor newCell : CellId) (vk : Int)
    (k : RecordKernelState) :
    interp (createCellFromFactoryStmt actor newCell vk) k
      = if (∃ e : FactoryEntry, factoryAdmit k actor newCell vk e)
        then some (factoryKernelPost vk newCell k) else none := by
  by_cases hg : createCellFromFactoryGuard actor newCell vk k = true
  · -- ADMIT: the guard fires (`some k`), the `allocCell` clause installs `createCellIntoAsset k newCell`,
    -- then the two component writes read off that (unchanged-`factories`) intermediate state.
    rw [if_pos ((createCellFromFactoryGuard_iff actor newCell vk k).mp hg)]
    -- reduce the term: guard fires → `allocCell` → `setCell {newCell}` → `setSlotCaveats`, each `interp`
    -- clause threading through `Option.bind`.
    simp only [createCellFromFactoryStmt, interp, hg, if_true, Option.bind_some]
    -- the committed kernel: `{ { createCellIntoAsset k newCell with cell := setCell-map } with
    -- slotCaveats := factoryCaveatsWrite … }`. Show it = `factoryKernelPost` field-wise; only `cell`
    -- differs syntactically (`c ∈ {newCell}` vs the `if c = newCell` inside `factoryCellWrite`).
    congr 1
    apply recordKernelState_ext <;> first | rfl | skip
    funext c
    simp only [Finset.mem_singleton, factoryKernelPost, factoryCellWrite]
    by_cases hc : c = newCell <;> simp [hc]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded gate.
    rw [if_neg (fun hp => hg ((createCellFromFactoryGuard_iff actor newCell vk k).mpr hp))]
    simp only [createCellFromFactoryStmt, interp, hg, if_false, Option.bind_none, Bool.false_eq_true]

#assert_axioms interp_createCellFromFactoryStmt_eq_chainK

/-- **`factoryKernelPost_eq_chain`** — the term's kernel post-state IS the chained executor's kernel. On a
committed `createCellFromFactoryChainA st actor newCell vk = some st'`, the kernel `st'.kernel` equals
`factoryKernelPost vk newCell st.kernel` — the factory install over `createCellIntoAsset`. So the
cornerstone's `factoryKernelPost` is EXACTLY what the executor produces (the only chained-vs-kernel delta
is the receipt log, handled in §3). -/
theorem factoryKernelPost_eq_chain {st st' : RecChainedState} {actor newCell : CellId} {vk : Int}
    (h : createCellFromFactoryChainA st actor newCell vk = some st') :
    st'.kernel = factoryKernelPost vk newCell st.kernel := by
  obtain ⟨e, s1, hfind, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
  obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
  subst hs' hs1
  -- `s1.kernel = createCellIntoAsset st.kernel newCell`; the install lambdas match `factoryCellWrite`/
  -- `factoryCaveatsWrite` because `(createCellIntoAsset …).factories = st.kernel.factories` (lookup `some e`).
  simp only [factoryKernelPost]
  apply recordKernelState_ext <;> first | rfl | skip
  · -- the `cell` install: the executor's `setField …` lambda over `e` IS `factoryCellWrite` (lookup `some e`).
    funext c
    simp only [factoryCellWrite, createCellIntoAsset_factories, hfind]
  · -- the `slotCaveats` install: the executor's `e.caveats` lambda IS `factoryCaveatsWrite` (lookup `some e`).
    funext c
    simp only [factoryCaveatsWrite, createCellIntoAsset_factories, hfind]

#assert_axioms factoryKernelPost_eq_chain

/-! ## §3 — lifting the cornerstone to the CHAINED executor `execFullA` / `createCellFromFactoryChainA`.

The standalone descriptor (§4) is keyed on the chained executor `execFullA` / `createCellFromFactoryChainA`
over `RecChainedState` (kernel + receipt log). The `createCellFromFactoryA` arm of `execFullA` is a single
dispatch to `createCellFromFactoryChainA` (`Spec/factorycreation.lean:153`). We expose the bridge: the
Argus term's kernel meaning IS the chained executor's kernel meaning, with the receipt-log prepend the
only chained-vs-raw delta (carried explicitly). -/

/-- **`interp_createCellFromFactoryStmt_chained` — the IR term's executor, lifted to the chained
`execFullA` (both directions).** The unified action executor commits a `createCellFromFactoryA` turn into
`st'` IFF the IR term's `interp` commits on the kernel to `st'.kernel` AND `st'.log` is the creation
receipt prepended. So the Argus term's kernel meaning IS the chained executor the descriptor speaks about
(the receipt-log update is the only chained-vs-raw delta — carried explicitly, not papered). -/
theorem interp_createCellFromFactoryStmt_chained (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) (st' : RecChainedState) :
    execFullA st (.createCellFromFactoryA actor newCell vk) = some st'
      ↔ interp (createCellFromFactoryStmt actor newCell vk) st.kernel = some st'.kernel
        ∧ st'.log = factoryReceipt actor newCell :: st.log := by
  -- `execFullA st (.createCellFromFactoryA …)` reduces definitionally to `createCellFromFactoryChainA st …`.
  show createCellFromFactoryChainA st actor newCell vk = some st' ↔ _
  rw [interp_createCellFromFactoryStmt_eq_chainK]
  constructor
  · -- → : a committed chained step gives the kernel commit (its `factoryKernelPost`) + the receipt log.
    intro h
    refine ⟨?_, createCellFromFactoryChainA_chainlink h⟩
    -- the gate held (the executor committed), so the cornerstone's `if` fires; the kernel is
    -- `factoryKernelPost`, which `factoryKernelPost_eq_chain` identifies with `st'.kernel`.
    obtain ⟨e, s1, hfind, hconf, hc, _⟩ := createCellFromFactoryChainA_factors h
    obtain ⟨hauth, hfresh, _⟩ := createCellChainA_factors hc
    have hvk : 0 ≤ vk := by
      by_contra hneg
      rw [createCellFromFactoryChainA, if_neg hneg] at h; exact absurd h (by simp)
    have hgate : ∃ e : FactoryEntry, factoryAdmit st.kernel actor newCell vk e :=
      ⟨e, hvk, hfind, hconf, hauth, hfresh⟩
    rw [if_pos hgate, factoryKernelPost_eq_chain h]
  · -- ← : from the kernel commit + receipt log, reconstruct the committed chained step.
    rintro ⟨hk, hl⟩
    by_cases hg : ∃ e : FactoryEntry, factoryAdmit st.kernel actor newCell vk e
    · -- the gate holds ⇒ the executor commits into SOME `s_out`; show `s_out = st'` from its kernel + log.
      rw [if_pos hg] at hk
      simp only [Option.some.injEq] at hk
      obtain ⟨e, hvk, hfind, hconf, hauth, hfresh⟩ := hg
      have hc : createCellChainA st actor newCell = some
          { kernel := createCellIntoAsset st.kernel newCell
            log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: st.log } := by
        unfold createCellChainA; rw [if_pos ⟨hauth, hfresh⟩]
      -- the executor COMMITS into some `s_out` (the explicit factory-install branch fires):
      have hsome : (createCellFromFactoryChainA st actor newCell vk).isSome = true := by
        unfold createCellFromFactoryChainA
        rw [if_pos hvk]; simp only [hfind, hconf, hc, if_true, Option.isSome_some]
      obtain ⟨s_out, hex⟩ := Option.isSome_iff_exists.mp hsome
      rw [hex]
      -- `s_out.kernel = factoryKernelPost = st'.kernel` (hk + factoring) and the logs match (chainlink + hl).
      have hsk : s_out.kernel = st'.kernel := (factoryKernelPost_eq_chain hex).trans hk
      have hsl : s_out.log = st'.log := (createCellFromFactoryChainA_chainlink hex).trans hl.symm
      obtain ⟨k_o, lg_o⟩ := s_out
      obtain ⟨k', lg'⟩ := st'
      simp only at hsk hsl
      rw [hsk, hsl]
    · -- the gate fails ⇒ the cornerstone's `if` is `none`, contradicting the committed kernel `some`.
      rw [if_neg hg] at hk; exact absurd hk (by simp)

#assert_axioms interp_createCellFromFactoryStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of the factory effect's OWN standalone QUINT circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against the factory effect's GENUINE standalone descriptor `createFromFactoryE …` (the v2
`EffectCommit5` QUINT circuit whose soundness is `createCellFromFactoryA_full_sound`,
`Inst/createCellFromFactoryA.lean`). The circuit pins `CreateFromFactoryCircuitSpec` (born-empty authority
slots BUNDLED as one `BornEmptyAuthorityTables` digest); the executor pins `CreateFromFactorySpec` (the
same five slots written EXPLICITLY). The two are PROVABLY equivalent on those slots via
`bornEmptyAuthority_post_iff` (a clean `↔`), so both name the SAME whole post-state, which we collapse via
spec functionality. -/

/-- The Argus circuit interpretation of a factory-create term: the factory effect's OWN audited standalone
v2 `EffectCommit5` QUINT circuit step — the full-state arithmetization `satisfiedE2Quint S
(createFromFactoryE …) (encodeE2Quint …)` satisfied on the encoded `(st, args, st')` triple. Its soundness
`createCellFromFactoryA_full_sound` pins `CreateFromFactoryCircuitSpec`. The factory-keyed analog of
`createCellCircuit`. -/
def createCellFromFactoryCircuit
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (st : RecChainedState) (args : CreateFromFactoryArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2Quint S (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
    (encodeE2Quint S (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
      st args st')

/-- **`circuitSpec_implies_spec` — the circuit's bundled born-empty form recovers the executor's explicit
spec.** `CreateFromFactoryCircuitSpec` (born-empty authority slots bundled in a `BornEmptyAuthorityTables`
digest) implies `CreateFromFactorySpec` (the same five slots written EXPLICITLY): the bundled equality
`readBornEmptyAuthority st'.kernel = expectedBornEmptyAuthority st.kernel newCell` decodes to the five
component equalities via `bornEmptyAuthority_post_iff`; every OTHER conjunct is shared verbatim. The
converse of `Inst.CreateCellFromFactoryA.CreateFromFactorySpec_implies_circuitSpec`. -/
theorem circuitSpec_implies_spec (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) (h : CreateFromFactoryCircuitSpec st actor newCell vk st') :
    CreateFromFactorySpec st actor newCell vk st' := by
  obtain ⟨e, hadmit, hacc, hbal, hcell, hsc, hauth, hlog, hEsc, hNull, hRev, hCom, hQ, hSw, hFac, hSB⟩ := h
  -- decode the bundled born-empty authority digest into the five explicit per-cell slot equalities.
  obtain ⟨hcaps, hlif, hdc, hdel, hdgs⟩ :=
    (bornEmptyAuthority_post_iff st.kernel newCell st'.kernel).mp hauth
  exact ⟨e, hadmit, hacc, hbal, hcell, hsc, hlog, hcaps, hlif, hdc, hdel, hdgs,
    hEsc, hNull, hRev, hCom, hQ, hSw, hFac, hSB⟩

/-- **`factorySpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CreateFromFactorySpec st actor newCell vk ·` are equal. Rather than re-derive field-by-field, we route
through the PROVEN executor⟺spec corner `execCreateFromFactoryA_iff_spec`: each `CreateFromFactorySpec`
reconstructs the SAME committed value `execFullA st (.createCellFromFactoryA actor newCell vk) = some ·`,
and `some` is injective. So `CreateFromFactorySpec` is functional — it determines the post-state — and the
circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem factorySpec_unique {st st₁ st₂ : RecChainedState} {actor newCell : CellId} {vk : Int}
    (h₁ : CreateFromFactorySpec st actor newCell vk st₁)
    (h₂ : CreateFromFactorySpec st actor newCell vk st₂) :
    st₁ = st₂ := by
  have e₁ : execFullA st (.createCellFromFactoryA actor newCell vk) = some st₁ :=
    (execCreateFromFactoryA_iff_spec st actor newCell vk st₁).mpr h₁
  have e₂ : execFullA st (.createCellFromFactoryA actor newCell vk) = some st₂ :=
    (execCreateFromFactoryA_iff_spec st actor newCell vk st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`createCellFromFactory_compile_sound` — the welded soundness (factory-create slice), against the
factory effect's OWN descriptor.**

Suppose, for the Argus factory-create term `createCellFromFactoryStmt actor newCell vk` (with
`args = ⟨actor, newCell, vk⟩`):
  * the standalone factory circuit `createCellFromFactoryCircuit S … st args st'` (= `createFromFactoryE`'s
    full-state v2 QUINT arithmetization satisfied on the encoded triple) holds, under the realizable
    whole-function / digest portals (`hRest`, `hLog`, and the injectivity hypotheses on
    `LE`/`cN`/`DBal`/`DCell`/`DSC`/`DAuth`);
  * the IR term's EXECUTOR commits the chained step: `execFullA st (.createCellFromFactoryA actor newCell
    vk) = some st''` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the one the IR term's executor produces:
`st' = st''`. I.e. the factory effect's OWN circuit and the IR term AGREE on the WHOLE 18-component state
(`accounts` GROWN by `newCell`, `bal`/born-empty authority slots RESET at `newCell`, the factory `cell`
fields + program-VK installed, the factory `slotCaveats` installed, the creation receipt prepended, every
global side-table frozen) — the full `CreateFromFactorySpec`, not a projection. So the circuit the prover
runs for the factory create pins the complete state the IR term's executor produces. -/
theorem createCellFromFactory_compile_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : RestIffNoFactoryTouched S.RH) (hLog : logHashInjective S.LH)
    (st st' st'' : RecChainedState) (actor newCell : CellId) (vk : Int)
    (hcirc : createCellFromFactoryCircuit S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      st ⟨actor, newCell, vk⟩ st')
    (hexec : execFullA st (.createCellFromFactoryA actor newCell vk) = some st'') :
    st' = st'' := by
  -- circuit side: the factory effect's OWN audited soundness forces `CreateFromFactoryCircuitSpec`, which
  -- we bridge to the executor's explicit `CreateFromFactorySpec` on `(st, args, st')`. `hcirc` unfolds
  -- definitionally to the raw `satisfiedE2Quint` the soundness theorem consumes.
  have hcspec : CreateFromFactoryCircuitSpec st actor newCell vk st' :=
    createCellFromFactoryA_full_sound S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      hRest hLog st ⟨actor, newCell, vk⟩ st' (by unfold createCellFromFactoryCircuit at hcirc; exact hcirc)
  have hspec : CreateFromFactorySpec st actor newCell vk st' :=
    circuitSpec_implies_spec st actor newCell vk st' hcspec
  -- executor side: the independent executor⟺spec corner turns the committed step into the same spec.
  have hspec' : CreateFromFactorySpec st actor newCell vk st'' :=
    (execCreateFromFactoryA_iff_spec st actor newCell vk st'').mp hexec
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every component + the log).
  exact factorySpec_unique hspec hspec'

#assert_axioms createCellFromFactory_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely GROWS `accounts` AND installs the factory program, and the
gate REJECTS forged inputs (fail-closed).

We reuse the executor's own factory fixtures (`facS`, `subFactory` at vk 42; actor `0` holds the minter
cap `Cap.node 5` over the fresh cell `5`). The headline tooth: the fresh id `5` is ABSENT before and
PRESENT after — the structural growth `allocCell` realizes — AND the minted cell carries the factory's
published caveats (constructor transparency). The rejection lemmas show the gate fails closed five ways. -/

-- The factory mint of FRESH cell `5` (actor `0`, vk `42`) genuinely COMMITS at the term level…
#guard (interp (createCellFromFactoryStmt 0 5 42) facS.kernel).isSome
-- …and the growth is OBSERVABLE: cell `5` is ABSENT before and PRESENT after (the structural alloc).
#guard ¬ ((5 : CellId) ∈ facS.kernel.accounts)
#guard (((interp (createCellFromFactoryStmt 0 5 42) facS.kernel).map (fun k => decide ((5 : CellId) ∈ k.accounts))) == some true)
-- …the minted cell carries the factory's published caveats (THE constructor-transparency tooth):
#guard (((interp (createCellFromFactoryStmt 0 5 42) facS.kernel).map (fun k => k.slotCaveats 5)) == some subFactory.caveats)
-- …born EMPTY in the per-asset ledger at the fresh id:
#guard (((interp (createCellFromFactoryStmt 0 5 42) facS.kernel).map (fun k => k.bal 5 0)) == some 0)
-- A NEGATIVE vk (no factory-0 aliasing) is REJECTED:
#guard (interp (createCellFromFactoryStmt 0 5 (-1)) facS.kernel).isNone
-- An UNKNOWN factory vk (99 ∉ registry) is REJECTED:
#guard (interp (createCellFromFactoryStmt 0 5 99) facS.kernel).isNone
-- A STALE id (cell 0 is already a live account) is REJECTED:
#guard (interp (createCellFromFactoryStmt 0 0 42) facS.kernel).isNone

/-- **`createCellFromFactoryStmt_grows_accounts` — the IR term genuinely GROWS `accounts` (PROVED,
non-vacuous).** On the executor's own `facS` fixture, the factory mint of fresh cell `5` (actor `0`, vk
`42`) COMMITS, and the committed post-state has cell `5` as a live account (PRESENT after) while it was
ABSENT before. This is the `accounts`-growth `allocCell` realizes — now driven by a factory-templated
create, the last account-growing effect. -/
theorem createCellFromFactoryStmt_grows_accounts :
    ∃ k', interp (createCellFromFactoryStmt 0 5 42) facS.kernel = some k'
      ∧ (5 : CellId) ∈ k'.accounts ∧ (5 : CellId) ∉ facS.kernel.accounts := by
  -- the committed chained executor output exists (decidable on the concrete fixture).
  have hsome : (execFullA facS (.createCellFromFactoryA 0 5 42)).isSome = true := by decide
  obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hk, _⟩ := (interp_createCellFromFactoryStmt_chained facS 0 5 42 st').mp hst'
  refine ⟨st'.kernel, hk, ?_, ?_⟩
  · exact createFromFactoryA_grows_accounts facS 0 5 42 st' hst'
  · decide

#assert_axioms createCellFromFactoryStmt_grows_accounts

/-- **`createCellFromFactoryStmt_installs_program` — the minted cell carries the factory's program
(PROVED, the constructor-transparency tooth).** On the `facS` fixture, the committed factory mint installs
EXACTLY `subFactory`'s published caveats on the minted cell `5` — so its published invariants are enforced
for life. Non-vacuous: it is the genuine factory caveat list, not `[]`. -/
theorem createCellFromFactoryStmt_installs_program :
    ∃ k', interp (createCellFromFactoryStmt 0 5 42) facS.kernel = some k'
      ∧ k'.slotCaveats 5 = subFactory.caveats := by
  have hsome : (execFullA facS (.createCellFromFactoryA 0 5 42)).isSome = true := by decide
  obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hk, _⟩ := (interp_createCellFromFactoryStmt_chained facS 0 5 42 st').mp hst'
  refine ⟨st'.kernel, hk, ?_⟩
  obtain ⟨e, hfind, hcav⟩ := createFromFactoryA_installs_program facS 0 5 42 st' hst'
  -- `findFactory facS.kernel.factories 42 = some subFactory` on the fixture, so `e = subFactory`.
  have he : e = subFactory := Option.some.inj (Eq.trans hfind.symm (by decide))
  rw [hcav, he]

#assert_axioms createCellFromFactoryStmt_installs_program

/-- **`createCellFromFactoryStmt_rejects_negative_vk` — fail-closed (no factory-0 aliasing).** A factory
create with a negative `vk` does NOT commit — `interp` returns `none`. The content-addressed factory key
cannot be forged downward by `Int.toNat`. -/
theorem createCellFromFactoryStmt_rejects_negative_vk (actor newCell : CellId) (vk : Int)
    (k : RecordKernelState) (hbad : vk < 0) :
    interp (createCellFromFactoryStmt actor newCell vk) k = none := by
  rw [interp_createCellFromFactoryStmt_eq_chainK, if_neg]
  rintro ⟨e, hvk, _⟩; omega

/-- **`createCellFromFactoryStmt_rejects_unknown` — fail-closed (unknown factory).** A factory create
whose `vk` is not in the registry does NOT commit — `interp` returns `none`. -/
theorem createCellFromFactoryStmt_rejects_unknown (actor newCell : CellId) (vk : Int)
    (k : RecordKernelState) (hbad : findFactory k.factories vk.toNat = none) :
    interp (createCellFromFactoryStmt actor newCell vk) k = none := by
  rw [interp_createCellFromFactoryStmt_eq_chainK, if_neg]
  rintro ⟨e, _, hfind, _⟩; rw [hbad] at hfind; exact absurd hfind (by simp)

/-- **`createCellFromFactoryStmt_rejects_unauthorized` — fail-closed (no privileged creation cap).** A
factory create whose actor lacks privileged creation authority over the fresh id does NOT commit. -/
theorem createCellFromFactoryStmt_rejects_unauthorized (actor newCell : CellId) (vk : Int)
    (k : RecordKernelState) (hbad : mintAuthorizedB k.caps actor newCell = false) :
    interp (createCellFromFactoryStmt actor newCell vk) k = none := by
  rw [interp_createCellFromFactoryStmt_eq_chainK, if_neg]
  rintro ⟨e, _, _, _, hauth, _⟩; rw [hbad] at hauth; exact absurd hauth (by simp)

/-- **`createCellFromFactoryStmt_rejects_stale` — fail-closed (no re-minting a live id).** A factory
create onto an id that is ALREADY a live account does NOT commit — the freshness conjunct fails. -/
theorem createCellFromFactoryStmt_rejects_stale (actor newCell : CellId) (vk : Int)
    (k : RecordKernelState) (hbad : newCell ∈ k.accounts) :
    interp (createCellFromFactoryStmt actor newCell vk) k = none := by
  rw [interp_createCellFromFactoryStmt_eq_chainK, if_neg]
  rintro ⟨e, _, _, _, _, hfresh⟩; exact hfresh hbad

#assert_axioms createCellFromFactoryStmt_rejects_negative_vk
#assert_axioms createCellFromFactoryStmt_rejects_unknown
#assert_axioms createCellFromFactoryStmt_rejects_unauthorized
#assert_axioms createCellFromFactoryStmt_rejects_stale

end Dregg2.Circuit.Argus.Effects.CreateCellFromFactory
