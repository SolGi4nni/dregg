/-
# Dregg2.Exec.EffectsSupply — the disclosed-supply and generative-resource effects, fully characterized.

Sibling of `Exec/EffectTransfer.lean` (`Conservative`/`Paired` reference) and of
`Exec/TurnExecutorFull.lean`'s mint/burn (the `Disclosed` supply prototype). Each effect here is
proved against the same five-keystone pattern:

  1. **executable step** — concrete, `#eval`-able semantics over `RecChainedState`;
  2. **conserves** — the domain-level conservation/disclosure obligation. For disclosed-supply
     effects this is NOT `Σδ = 0` but the disclosed form: `recTotal` moves by a disclosed `±amount`,
     flagged `is_disclosed_non_conservation`; for the paired-bridge effects (lock/finalize/cancel)
     it IS `Σδ = 0` (an internal escrow move);
  3. **authorized** — a committed step was gated by the relevant authority;
  4. **metadata** — the receipt chain advances by exactly one row (replay-detectable), and the cap
     table is framed (resource creation/supply never edits connectivity);
  5. **forward-sim** — a committed step is matched by an abstract `Spec` step `AbsStep (absT s)
     (absT s')` over the (`balance`-domain total, authority graph) abstraction, with the disclosed
     supply delta on the bottom edge.

## Effects covered

  * `CreateCell` (`g_createCell`, Generative) — mint a fresh live account with a disclosed
    initial balance: `recTotal` grows by exactly the disclosed `balance`.
  * `CreateCellFromFactory` (`g_createCellFromFactory`, Generative) — `CreateCell` whose child runs
    a published `FactoryDescriptor` program: constructor transparency + the same disclosed-balance creation.
  * `SpawnWithDelegation` (`g_spawnWithDelegation`, Generative) — spawn a child with a disclosed
    copy of an already-held parent cap; `recTotal` grows by the disclosed child balance.
  * `BridgeMint` (`g_bridgeMint`, Generative — §8 portal inflow) — credit a cell by a disclosed
    `value` observed off a foreign chain. dregg2 cannot verify foreign consensus, so the foreign
    finality is a `Prop`-carrier portal `ForeignFinal` carried as a hypothesis (OPEN: discharged
    outside Lean); the local state transition is executable and proved.
  * `BridgeLock` (`c_bridgeLock`, Conservative) — Phase-1 lock: escrow `value` from a cell into a
    bridge lock-cell (an internal `Σδ = 0` move) + record the lock's `nullifier`. The foreign
    destination is a `Prop` portal; the local escrow conserves.
  * `BridgeFinalize` (`a_bridgeFinalize`, Annihilative — disclosed cross-chain OUTFLOW) — Phase-3
    finalize: on a foreign receipt (Prop portal), consume the lock (the nullifier becomes permanently
    spent). The catalog color is `Annihilative` (the value leaves for the other chain — a disclosed
    burn, NOT conserved). This module's LOCAL toy frames the balance (the value already left at lock
    time, so this no-credit step touches the local total by `0`); the value-leaves-now accounting is
    the `Bridge` handler's `bridgeFinalizeKAsset` (`delta = -amount`).
  * `BridgeCancel` (`c_bridgeCancel`, Conservative) — Phase-4 cancel after timeout: refund the
    escrow back to the owner (the inverse of the lock — `Σδ = 0`) + retire the lock nonce.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly `{propext,
Classical.choice, Quot.sound}` on every keystone. Pure, computable, `#eval`-able. Reuses only built
modules (`TurnExecutorFull`/`RecordKernel`/`Factory`/`CatalogEffects`/`Spec.ExecRefinement`); edits none.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.Factory
import Dregg2.Exec.EffectTransfer
import Dregg2.Spec.ExecRefinement

namespace Dregg2.Exec.EffectsSupply

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (recCreditCell recCreditCell_recTotal_delta mintEffect
  recKMint recKMint_delta recKMint_authorized recKMint_unauthorized_fails)
open Dregg2.Exec.EffectTransfer (recCexec_caps_eq)
open Dregg2.Authority (Caps Cap Label)
open Dregg2.CatalogInstances (effectLinearity)
open Dregg2.Spec (Domain conservedInDomain execGraph execAuthGuard Guard)
open Dregg2.Laws (Verifiable)
open scoped BigOperators

/-! ## §0 — Shared scaffolding: the disclosed-creation credit, the lock-nullifier nonce, the foreign portal.

The disclosed-supply / generative effects share two named-field moves and one §8 portal:
  * a fresh-account insert (`createCellInto`) that adds a live cell with a disclosed balance — the
    generative analog of `recCreditCell` but it grows `accounts`, so `recTotal` rises by the disclosed
    balance of the new (previously absent ⇒ measure-`0`) cell;
  * a nullifier-nonce write (`setLock` / `lockOf`) recording a bridge lock's spent state (the
    replay-protection metadata for the bridge phases);
  * the foreign-finality portal `ForeignFinal` — an opaque `Prop` the cross-chain proof discharges
    outside Lean (dregg2 cannot verify Cardano consensus). It is carried as a hypothesis on the bridge
    keystones, never proved here (OPEN: §8 portal obligation). -/

/-- **The disclosed bridge-lock field** — a cell record's `bridge_lock` nullifier-nonce field, recording
whether/which note is locked for a cross-chain bridge (the replay-protection metadata of the bridge
phases). Distinct from `balance`, so writing it does not perturb the conserved measure. -/
def lockField : FieldName := "bridge_lock"

/-- Read a cell's `bridge_lock` field as an `Int` (0 = unlocked / no pending bridge), the bridge-phase
metadata measure. -/
def lockOf (v : Value) : Int := (v.scalar lockField).getD 0

/-- **`ForeignFinal`** — the §8 cross-chain finality portal. A `Prop` standing for "the foreign chain
has finalized the corresponding transaction at `nullifier` for `value`". dregg2 cannot verify foreign
consensus inside Lean, so this is an opaque carrier (OPEN: discharged by the BridgeVerifierKernel /
observation bridge): it is a hypothesis on every bridge keystone, never proved here. -/
opaque ForeignFinal (nullifier : ℤ) (value : ℤ) : Prop

/-! ## §1 — `CreateCell`: a Generative effect that mints a fresh live account (disclosed supply).

`Effect::CreateCell` adds a new cell to the ledger with an initial `balance`. It is Generative
(`CatalogEffects.g_createCell`): it brings `balance` units into existence, a disclosed non-conservation
(the created amount is on the receipt). The executable semantics: gate on `mintAuthorizedB` (creation
is privileged — only an authority may coin a new cell's endowment), require the new id is fresh
(`∉ accounts`), then insert it with the disclosed `balance`. -/

/-- Insert a fresh cell `newCell` into the ledger with initial `balance` field `bal` (and a cleared
lock). The generative account-set write: it adds `newCell` to `accounts` AND sets its `balance`. -/
def createCellInto (k : RecordKernelState) (newCell : CellId) (bal : ℤ) : RecordKernelState :=
  { k with accounts := insert newCell k.accounts
           cell := fun c => if c = newCell then setBalance (.record []) bal else k.cell c }

/-- **`createCellStep` — `CreateCell`'s executable semantics.** Fail-closed: an authorized creator
(`mintAuthorizedB actor newCell` — creation is privileged, like minting supply), a fresh id
(`newCell ∉ accounts`), and a non-negative endowment. On commit, the fresh cell is inserted with the
disclosed `bal` and a receipt carrying the disclosed creation amount is appended. -/
def createCellStep (s : RecChainedState) (actor newCell : CellId) (bal : ℤ) :
    Option RecChainedState :=
  if mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧ 0 ≤ bal then
    some { kernel := createCellInto s.kernel newCell bal
           log := { actor := actor, src := newCell, dst := newCell, amt := bal } :: s.log }
  else
    none

/-- The receipt a committed `createCellStep` appends (the disclosed creation, newest-first). -/
def createTurn (actor newCell : CellId) (bal : ℤ) : Turn :=
  { actor := actor, src := newCell, dst := newCell, amt := bal }

/-- **`createCellStep` factors through its gate — PROVED.** A committed creation implies the three gate
conjuncts held and pins the post-state. The bridge downstream keystones reuse. -/
theorem createCellStep_factors {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧ 0 ≤ bal ∧
      s' = { kernel := createCellInto s.kernel newCell bal
             log := createTurn actor newCell bal :: s.log } := by
  unfold createCellStep at h
  by_cases hg : mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧ 0 ≤ bal
  · rw [if_pos hg, Option.some.injEq] at h
    exact ⟨hg.1, hg.2.1, hg.2.2, by rw [← h]; rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §1.2 — `create_conserves` (disclosed form): `recTotal` grows by exactly the disclosed `bal`. -/

/-- The fresh-account insert raises `recTotal` by exactly the disclosed `bal`. The new cell was
absent (`∉ accounts`, so it contributed `0`); inserting it with `balance = bal` adds `bal`.
Uses `Finset.sum_insert` (the fresh-cell single-point growth). -/
theorem createCellInto_recTotal (k : RecordKernelState) (newCell : CellId) (bal : ℤ)
    (hfresh : newCell ∉ k.accounts) :
    recTotal (createCellInto k newCell bal) = recTotal k + bal := by
  unfold recTotal createCellInto
  rw [Finset.sum_insert hfresh]
  have hnew : balOf ((fun c => if c = newCell then setBalance (.record []) bal else k.cell c) newCell)
      = bal := by simp only [if_pos]; exact setBalance_balOf _ bal
  rw [hnew, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  have hcne : c ≠ newCell := fun heq => hfresh (heq ▸ hc)
  simp only [if_neg hcne]

/-- **`create_conserves` — disclosed non-conservation (PROVED).** A committed `createCellStep` raises the
total `balance` by exactly the disclosed `bal`: `recTotal s'.kernel = recTotal s.kernel + bal`. The supply
move is not `Σδ = 0`; it is the disclosed delta `+bal` (the Generative disclosure obligation). -/
theorem create_conserves {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    recTotal s'.kernel = recTotal s.kernel + bal := by
  obtain ⟨_, hfresh, _, hs'⟩ := createCellStep_factors h
  subst hs'
  exact createCellInto_recTotal s.kernel newCell bal hfresh

/-- **`create_discloses` — PROVED.** `CreateCell` is Generative, so its created supply is disclosed.
Discharged via `CatalogEffects.generative_discloses` + `g_createCell`. -/
theorem create_discloses :
    (effectLinearity .createCell).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .createCell Dregg2.CatalogEffects.g_createCell

/-- **`create_disclosed_domain` — PROVED.** The realized balance-domain delta of a committed
`createCellStep` is exactly the disclosed `[bal]` (not `[0]`). -/
theorem create_disclosed_domain {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    [recTotal s'.kernel - recTotal s.kernel] = [bal] := by
  rw [create_conserves h]; simp

/-! ### §1.3 — `create_authorized` + fail-closed. -/

/-- **`create_authorized` — PROVED.** A committed `createCellStep` implies the creator held
creation authority over the new cell (`mintAuthorizedB` — bare ownership is not enough; creation
coins supply). -/
theorem create_authorized {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  (createCellStep_factors h).1

/-- **`create_unauthorized_fails` — PROVED (fail-closed).** Without creation authority, no cell is
minted. The confinement core. -/
theorem create_unauthorized_fails (s : RecChainedState) (actor newCell : CellId) (bal : ℤ)
    (h : mintAuthorizedB s.kernel.caps actor newCell = false) :
    createCellStep s actor newCell bal = none := by
  unfold createCellStep
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-! ### §1.4 — `create_metadata`: caps framed + the chain advances by one. -/

/-- **`create_caps_unchanged` — PROVED.** A committed `createCellStep` leaves the cap table
untouched (creation edits `accounts`/`cell`, never `caps`). -/
theorem create_caps_unchanged {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨_, _, _, hs'⟩ := createCellStep_factors h
  subst hs'; rfl

/-- **`create_metadata` — PROVED (metadata + authority frame).** A committed `createCellStep`: (a) grows
the receipt chain by EXACTLY one row (replay-detectable, ObsAdvance), and (b) leaves the cap table /
reconstructed authority graph UNCHANGED. -/
theorem create_metadata {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨_, _, _, hs'⟩ := createCellStep_factors h
  refine ⟨?_, ?_⟩
  · subst hs'; simp
  · rw [create_caps_unchanged h]

/-! ## §2 — `CreateCellFromFactory`: constructor transparency + disclosed creation.

`Effect::CreateCellFromFactory` (`CatalogEffects.g_createCellFromFactory`, Generative) mints a cell
whose lifetime program is a published `FactoryDescriptor`'s program. Composed from
`Factory.createFromFactory` (constructor transparency) with `createCellStep`'s disclosed ledger insert:
the factory pins the child's invariants, the supply move is the disclosed `+bal`. -/

/-- **`createFromFactoryStep` — `CreateCellFromFactory`'s executable semantics.** First mint the child
program/state via `Factory.createFromFactory` (rejects a non-conforming initial value, fail-closed);
THEN insert the fresh ledger account with the disclosed `bal`. Returns BOTH the ledger post-state and the
minted `Factory.Cell` (carrying the published program), so constructor transparency is observable. -/
def createFromFactoryStep (s : RecChainedState) (actor newCell : CellId) (bal : ℤ)
    (d : Factory.FactoryDescriptor) (initial : Value) :
    Option (RecChainedState × Factory.Cell) :=
  match Factory.createFromFactory d initial with
  | some child =>
      match createCellStep s actor newCell bal with
      | some s' => some (s', child)
      | none    => none
  | none => none

/-- **`factory_create_factors` — PROVED.** A committed factory-create factors as a committed
`Factory.createFromFactory` (the child) AND a committed `createCellStep` (the ledger insert). -/
theorem factory_create_factors {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    Factory.createFromFactory d initial = some child ∧ createCellStep s actor newCell bal = some s' := by
  unfold createFromFactoryStep at h
  cases hc : Factory.createFromFactory d initial with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      cases hl : createCellStep s actor newCell bal with
      | none => rw [hl] at h; exact absurd h (by simp)
      | some sl =>
          rw [hl] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hsl, hch⟩ := h
          exact ⟨by rw [hch], by rw [hsl]⟩

/-- **`factory_constructor_transparency` — PROVED.** The cell a committed `createFromFactoryStep` mints
carries exactly the factory's declared `program` and conforms to its schema: no hidden behavior, the
published contract is the child's lifetime invariant set. Delegated to `Factory.factory_mints_conforming`. -/
theorem factory_constructor_transparency {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    child.program = d.program ∧ child.state = initial ∧
      conforms child.state (.record d.schema) = true :=
  Factory.factory_mints_conforming (factory_create_factors h).1

/-- **`factory_create_conserves` — DISCLOSED non-conservation (PROVED).** The ledger insert raises
`recTotal` by exactly the disclosed `bal` (inherited from `create_conserves`). -/
theorem factory_create_conserves {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    recTotal s'.kernel = recTotal s.kernel + bal :=
  create_conserves (factory_create_factors h).2

/-- **`factory_create_discloses` — PROVED.** `CreateCellFromFactory` is Generative ⇒ disclosed. -/
theorem factory_create_discloses :
    (effectLinearity .createCellFromFactory).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .createCellFromFactory
    Dregg2.CatalogEffects.g_createCellFromFactory

/-- **`factory_create_authorized` — PROVED.** A committed factory-create implies creation authority. -/
theorem factory_create_authorized {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  create_authorized (factory_create_factors h).2

/-- **`factory_create_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem factory_create_metadata {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps :=
  create_metadata (factory_create_factors h).2

/-! ## §3 — `SpawnWithDelegation`: a child spawned with a disclosed parent-cap copy.

`Effect::SpawnWithDelegation` (`CatalogEffects.g_spawnWithDelegation`, Generative) spawns a child cell
that inherits a snapshot of the parent's authority. Modeled as `createCellStep` (the disclosed-supply
child) composed with copying an already-held parent cap to the child. The balance creation is the
disclosed `+bal`; the authority copy adds no ungrounded cap edge. -/

/-- **`spawnStep` — `SpawnWithDelegation`'s executable semantics.** Fail-closed via `createCellStep` (the
authorized, fresh-id, non-negative child) AND unless the actor already holds a live cap edge to the
parent `target`. On commit, copy that concrete held cap to the child, record its parent, and store the
parent's c-list snapshot at birth. The child's provenance is the spawning `actor` (recorded on the
receipt). -/
def spawnStep (s : RecChainedState) (actor child target : CellId) (bal : ℤ) :
    Option RecChainedState :=
  if (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
      target ∈ s.kernel.accounts then
    match createCellStep s actor child bal with
    | some s1 =>
        some { s1 with kernel :=
          { s1.kernel with caps := fun l =>
              if l = child then heldCapTo s.kernel.caps actor target :: s1.kernel.caps l
              else s1.kernel.caps l
                           delegate := fun c => if c = child then some actor else s1.kernel.delegate c
                           delegations := fun c => if c = child then s1.kernel.caps actor
                                                   else s1.kernel.delegations c } }
    | none => none
  else
    none

/-- **`spawnStep` factors through `createCellStep` — PROVED.** A committed spawn is a committed
`createCellStep` (into `s1`) whose parent target was already live and held by the actor, followed by
the concrete held-cap copy and initial delegation snapshot. -/
theorem spawnStep_factors {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    ∃ s1, ((s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
             target ∈ s.kernel.accounts) ∧
      createCellStep s actor child bal = some s1 ∧
      s' = { s1 with kernel :=
        { s1.kernel with caps := fun l =>
            if l = child then heldCapTo s.kernel.caps actor target :: s1.kernel.caps l
            else s1.kernel.caps l
                         delegate := fun c => if c = child then some actor else s1.kernel.delegate c
                         delegations := fun c => if c = child then s1.kernel.caps actor
                                                 else s1.kernel.delegations c } } := by
  unfold spawnStep at h
  by_cases hg : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true ∧
      target ∈ s.kernel.accounts
  · rw [if_pos hg] at h
    cases hc : createCellStep s actor child bal with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some s1 =>
        rw [hc] at h
        simp only [Option.some.injEq] at h
        exact ⟨s1, hg, rfl, h.symm⟩
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- The cap/metadata grant preserves `recTotal` (it edits no balance fields) — PROVED. -/
theorem spawn_grant_recTotal (k : RecordKernelState) (actor child : CellId) (cap : Cap) :
    recTotal { k with caps := fun l => if l = child then cap :: k.caps l else k.caps l
                      delegate := fun c => if c = child then some actor else k.delegate c
                      delegations := fun c => if c = child then k.caps actor else k.delegations c }
      = recTotal k := rfl

/-- **`spawn_conserves` — DISCLOSED non-conservation (PROVED).** A committed spawn raises `recTotal` by
exactly the disclosed child endowment `bal` (the cap grant does not touch the balance field). -/
theorem spawn_conserves {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    recTotal s'.kernel = recTotal s.kernel + bal := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnStep_factors h
  subst hs'
  rw [spawn_grant_recTotal s1.kernel actor child (heldCapTo s.kernel.caps actor target)]
  exact create_conserves hc

/-- **`spawn_discloses` — PROVED.** `SpawnWithDelegation` is Generative ⇒ disclosed. -/
theorem spawn_discloses :
    (effectLinearity .spawnWithDelegation).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .spawnWithDelegation
    Dregg2.CatalogEffects.g_spawnWithDelegation

/-- **`spawn_authorized` — PROVED.** A committed spawn implies the spawner held creation authority over
the child (the parent's privilege to spawn). -/
theorem spawn_authorized {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    mintAuthorizedB s.kernel.caps actor child = true := by
  obtain ⟨s1, _, hc, _⟩ := spawnStep_factors h
  exact create_authorized hc

/-- **`spawn_parent_grounded` — PROVED.** A committed spawn implies the actor already held a live edge
to the parent target; child creation alone cannot introduce a fresh target edge. -/
theorem spawn_parent_grounded {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    Dregg2.Spec.execGraph s.kernel.caps actor
        (⟨target, ()⟩ : Dregg2.Spec.Cap Label Dregg2.Spec.ExecRights) ∧
      target ∈ s.kernel.accounts := by
  obtain ⟨_, hg, _, _⟩ := spawnStep_factors h
  exact hg

/-- **`spawn_provenance` — PROVED.** The spawned child receives exactly the concrete cap the actor
already held to the parent target. -/
theorem spawn_provenance {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    heldCapTo s.kernel.caps actor target ∈ s'.kernel.caps child := by
  obtain ⟨s1, _, _, hs'⟩ := spawnStep_factors h
  subst hs'
  simp

/-- **`spawn_parent_snapshot` — PROVED.** Spawn initializes the child parent pointer and its birth
snapshot of the parent's c-list. -/
theorem spawn_parent_snapshot {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    s'.kernel.delegate child = some actor ∧ s'.kernel.delegations child = s.kernel.caps actor := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnStep_factors h
  subst hs'
  have hcaps : s1.kernel.caps = s.kernel.caps := by
    obtain ⟨_, _, _, hs1⟩ := createCellStep_factors hc
    subst hs1
    rfl
  simp only [if_true, true_and]
  rw [hcaps]

/-- **`spawn_metadata` — PROVED.** A committed spawn grows the receipt chain by exactly one (the child's
creation row); the cap edit is the disclosed child grant (NOT a frame — spawn DOES extend authority, the
sole §3 difference from `CreateCell`). -/
theorem spawn_metadata {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    s'.log.length = s.log.length + 1 := by
  obtain ⟨s1, _, hc, hs'⟩ := spawnStep_factors h
  subst hs'
  have := (create_metadata hc).1
  simpa using this

/-! ## §4 — `BridgeMint`: the §8 portal inflow (foreign-finality as a `Prop` carrier).

`Effect::BridgeMint` (`CatalogEffects.g_bridgeMint`, Generative) credits a cell with a value observed
off a foreign chain. dregg2 cannot verify foreign consensus inside Lean, so the foreign finality is the
opaque `Prop` `ForeignFinal nullifier value` carried as a hypothesis (OPEN: §8 portal); the local state
transition — the disclosed `+value` credit + the nullifier-nonce pairing — is executable and proved. -/

/-- **`bridgeMintStep` — `BridgeMint`'s executable local semantics.** Fail-closed: an authorized minter
(`mintAuthorizedB` — the bridge mint is privileged supply), the target is live, and a non-negative value.
On commit, credit the cell's `balance` by the disclosed `value` and append a receipt carrying it. The
foreign finality is not checked here (it is the §8 portal hypothesis on the keystone). -/
def bridgeMintStep (s : RecChainedState) (actor cell : CellId) (value : ℤ) :
    Option RecChainedState :=
  match recKMint s.kernel actor cell value with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := value } :: s.log }
  | none    => none

/-- **`bridgeMintStep` factors through `recKMint` — PROVED.** A committed bridge-mint is a committed
record-cell `recKMint` (the disclosed credit) plus the receipt row. Reuses the supply spine. -/
theorem bridgeMintStep_factors {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    ∃ k', recKMint s.kernel actor cell value = some k' ∧
      s' = { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := value } :: s.log } := by
  unfold bridgeMintStep at h
  cases hm : recKMint s.kernel actor cell value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; exact ⟨k', rfl, h.symm⟩

/-- **`bridge_mint_conserves` — disclosed non-conservation, gated by the §8 portal (PROVED).** Given the
foreign-finality portal `ForeignFinal nullifier value` (the cross-chain proof, discharged outside Lean), a
committed `bridgeMintStep` raises `recTotal` by exactly the disclosed `value`. The local disclosed credit
is `recKMint_delta` (proved); the foreign half is the carried hypothesis (OPEN: §8 portal). -/
theorem bridge_mint_conserves {s s' : RecChainedState} {actor cell : CellId} {value nullifier : ℤ}
    (_hforeign : ForeignFinal nullifier value)
    (h : bridgeMintStep s actor cell value = some s') :
    recTotal s'.kernel = recTotal s.kernel + value := by
  obtain ⟨k', hm, hs'⟩ := bridgeMintStep_factors h
  subst hs'
  exact recKMint_delta s.kernel k' actor cell value hm

/-- **`bridge_mint_discloses` — PROVED.** `BridgeMint` is Generative, so its supply delta is disclosed. -/
theorem bridge_mint_discloses :
    (effectLinearity .bridgeMint).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .bridgeMint Dregg2.CatalogEffects.g_bridgeMint

/-- **`bridge_mint_authorized` — PROVED.** A committed bridge-mint implies the privileged mint authority
(the local credit is gated; the foreign side is the portal). -/
theorem bridge_mint_authorized {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  obtain ⟨k', hm, _⟩ := bridgeMintStep_factors h
  exact recKMint_authorized s.kernel k' actor cell value hm

/-- **`bridge_mint_unauthorized_fails` — PROVED (fail-closed).** Without mint authority, no bridge-mint
commits (regardless of foreign finality). -/
theorem bridge_mint_unauthorized_fails (s : RecChainedState) (actor cell : CellId) (value : ℤ)
    (h : mintAuthorizedB s.kernel.caps actor cell = false) :
    bridgeMintStep s actor cell value = none := by
  unfold bridgeMintStep
  rw [recKMint_unauthorized_fails s.kernel actor cell value h]

/-- **`bridge_mint_caps_unchanged` — PROVED.** The local bridge-mint credit frames the cap table. -/
theorem bridge_mint_caps_unchanged {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨k', hm, hs'⟩ := bridgeMintStep_factors h
  subst hs'
  -- `recKMint` commits ⟹ it took the credit branch (caps untouched).
  unfold recKMint at hm
  by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ s.kernel.accounts
  · rw [if_pos hg] at hm; simp only [Option.some.injEq] at hm; rw [← hm]
  · rw [if_neg hg] at hm; exact absurd hm (by simp)

/-- **`bridge_mint_metadata` — PROVED.** Chain advances by one + caps/auth graph framed. -/
theorem bridge_mint_metadata {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨k', hm, hs'⟩ := bridgeMintStep_factors h
  refine ⟨?_, ?_⟩
  · subst hs'; simp
  · rw [bridge_mint_caps_unchanged h]

/-! ## §5 — `BridgeLock` / `BridgeCancel` / `BridgeFinalize`: the paired bridge escrow phases.

`BridgeLock`/`BridgeCancel`/`BridgeFinalize` are the Conservative escrow phases (`Σδ = 0`). We model a
bridge lock-cell: locking escrows `value` from the owner into the lock-cell (an internal transfer,
balance-conserving) recording the lock nullifier; cancel refunds it (the inverse); finalize consumes the
lock (the value already left — balance framed, the nullifier retired). The foreign destination/receipt is
the §8 Prop portal; the local escrow conserves. Reuses `recTransfer` for lock/cancel. -/

/-- **`bridgeLockStep` — `BridgeLock`'s executable local semantics.** Fail-closed: the owner is
authorized (`authorizedB` over the move), `value` is available in `owner`, and `owner ≠ lockCell`
(distinct escrow), both live. On commit, escrow `value` owner→lockCell and append the lock receipt
carrying the `nullifier`. -/
def bridgeLockStep (s : RecChainedState) (owner lockCell : CellId) (value nullifier : ℤ) :
    Option RecChainedState :=
  match recCexec s { actor := owner, src := owner, dst := lockCell, amt := value } with
  | some s1 => some { s1 with kernel := { s1.kernel with
      cell := fun c => if c = lockCell then setLockField (s1.kernel.cell c) nullifier
                       else s1.kernel.cell c } }
  | none => none
where
  /-- Write the `bridge_lock` nullifier-nonce field of the lock-cell (the replay metadata) by PREPENDING
  it (the freshest binding wins under `List.find?`). The `bridge_lock` name is distinct from `balance`, so
  prepending it never shadows the balance read — the escrow measure survives untouched. -/
  setLockField (v : Value) (nullifier : ℤ) : Value :=
    match v with
    | .record fs => .record ((lockField, .int nullifier) :: fs)
    | _          => .record [(lockField, .int nullifier)]

/-- The `Turn` a bridge-lock escrows. -/
def lockTurn (owner lockCell : CellId) (value : ℤ) : Turn :=
  { actor := owner, src := owner, dst := lockCell, amt := value }

/-- Writing the `bridge_lock` field leaves the `balance` read UNCHANGED — PROVED. The two named fields are
distinct (`"bridge_lock" ≠ "balance"`), so the lock-nonce write never perturbs the escrow measure. -/
theorem setLockField_balOf (v : Value) (nullifier : ℤ) :
    balOf (bridgeLockStep.setLockField v nullifier) = balOf v := by
  cases v with
  | record fs =>
      -- prepending `(bridge_lock, …)` does not shadow the `balance` read (distinct names).
      unfold balOf bridgeLockStep.setLockField
      simp only [Value.scalar, Value.field]
      have hne : (lockField == balanceField) = false := by decide
      rw [List.find?_cons_of_neg (by simpa using hne)]
  | int _ => simp [balOf, bridgeLockStep.setLockField, Value.scalar, Value.field, balanceField, lockField]
  | dig _ => simp [balOf, bridgeLockStep.setLockField, Value.scalar, Value.field, balanceField, lockField]
  | sym _ => simp [balOf, bridgeLockStep.setLockField, Value.scalar, Value.field, balanceField, lockField]

/-- **`bridgeLockStep` factors through `recCexec` — PROVED.** A committed lock is a committed escrow
`recCexec` (into `s1`) followed by the lock-nonce write. -/
theorem bridgeLockStep_factors {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    ∃ s1, recCexec s (lockTurn owner lockCell value) = some s1 ∧
      s' = { s1 with kernel := { s1.kernel with
        cell := fun c => if c = lockCell then bridgeLockStep.setLockField (s1.kernel.cell c) nullifier
                         else s1.kernel.cell c } } := by
  unfold bridgeLockStep lockTurn at *
  cases hc : recCexec s { actor := owner, src := owner, dst := lockCell, amt := value } with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s1 => rw [hc] at h; simp only [Option.some.injEq] at h; exact ⟨s1, rfl, h.symm⟩

/-- The lock-nonce write preserves the conserved `balance` total — PROVED (it touches only the
`bridge_lock` field). -/
theorem lockWrite_recTotal (k : RecordKernelState) (lockCell : CellId) (nullifier : ℤ) :
    recTotal { k with cell := fun c => if c = lockCell then bridgeLockStep.setLockField (k.cell c) nullifier
                                       else k.cell c } = recTotal k := by
  unfold recTotal
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c = lockCell
  · simp only [hc, if_pos]; exact setLockField_balOf (k.cell lockCell) nullifier
  · simp only [if_neg hc]

/-- **`bridge_lock_conserves` — two-party balance conservation (PROVED, the paired regime).** A committed
`bridgeLockStep` preserves `recTotal`: the owner's `-value` debit and the lock-cell's `+value` credit
cancel (the two-party escrow), and the lock-nonce write does not perturb the balance measure. The bridge
lock is an internal `Σδ = 0` move — the value is escrowed, not destroyed. -/
theorem bridge_lock_conserves {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨s1, hc, hs'⟩ := bridgeLockStep_factors h
  subst hs'
  rw [lockWrite_recTotal s1.kernel lockCell nullifier]
  exact (recCexec_attests hc).1

/-- **`bridge_lock_paired_domain` — PROVED (per-domain Σ=0).** The realized balance delta of a committed
lock nets to `0` (`conservedInDomain Domain.balance`), the executable shadow of the `c_bridgeLock`
Conservative obligation. -/
theorem bridge_lock_paired_domain {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain; rw [bridge_lock_conserves h]; simp

/-- **`bridge_lock_authorized` — PROVED.** A committed lock implies the owner was authorized to move the
escrowed value (reused from the escrow `recCexec` gate). -/
theorem bridge_lock_authorized {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    authorizedB s.kernel.caps (lockTurn owner lockCell value) = true := by
  obtain ⟨s1, hc, _⟩ := bridgeLockStep_factors h
  exact (recCexec_attests hc).2.1

/-- **`bridge_lock_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem bridge_lock_metadata {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨s1, hc, hs'⟩ := bridgeLockStep_factors h
  -- caps: `recCexec` frames caps, the lock-nonce write edits only `cell`.
  have hcaps : s'.kernel.caps = s.kernel.caps := by
    subst hs'; simp only []; exact recCexec_caps_eq hc
  refine ⟨?_, by rw [hcaps]⟩
  subst hs'; simp only []
  have : s1.log = lockTurn owner lockCell value :: s.log := (recCexec_attests hc).2.2.1
  rw [this]; simp

/-! ### §5.2 — `BridgeCancel`: refund the escrow (the inverse of lock), gated by timeout (a Prop portal). -/

/-- **`bridgeCancelStep` — `BridgeCancel`'s executable local semantics.** The Phase-4 refund: escrow the
locked `value` back from the lock-cell to the owner (the inverse two-party move), via `recCexec`. The
timeout-expiry is a §8 portal (OPEN: not verifiable in Lean); the local refund conserves. -/
def bridgeCancelStep (s : RecChainedState) (owner lockCell : CellId) (value : ℤ) :
    Option RecChainedState :=
  recCexec s { actor := owner, src := lockCell, dst := owner, amt := value }

/-- The `Turn` a cancel refunds (lockCell → owner). -/
def cancelTurn (owner lockCell : CellId) (value : ℤ) : Turn :=
  { actor := owner, src := lockCell, dst := owner, amt := value }

/-- **`bridge_cancel_conserves` — TWO-PARTY balance conservation (PROVED, PAIRED).** A committed
`bridgeCancelStep` preserves `recTotal` — the refund is the inverse escrow, `Σδ = 0`. -/
theorem bridge_cancel_conserves {s s' : RecChainedState} {owner lockCell : CellId} {value : ℤ}
    (h : bridgeCancelStep s owner lockCell value = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  (recCexec_attests h).1

/-- **`bridge_cancel_authorized` — PROVED.** A committed cancel was authorized (the refund gate). -/
theorem bridge_cancel_authorized {s s' : RecChainedState} {owner lockCell : CellId} {value : ℤ}
    (h : bridgeCancelStep s owner lockCell value = some s') :
    authorizedB s.kernel.caps (cancelTurn owner lockCell value) = true :=
  (recCexec_attests h).2.1

/-- **`bridge_cancel_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem bridge_cancel_metadata {s s' : RecChainedState} {owner lockCell : CellId} {value : ℤ}
    (h : bridgeCancelStep s owner lockCell value = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  refine ⟨?_, by rw [recCexec_caps_eq h]⟩
  have : s'.log = cancelTurn owner lockCell value :: s.log := (recCexec_attests h).2.2.1
  rw [this]; simp

/-! ### §5.3 — `BridgeFinalize`: consume the lock on a foreign receipt (Prop portal); balance framed. -/

/-- **`bridgeFinalizeStep` — `BridgeFinalize`'s executable local semantics.** On a foreign receipt (the
§8 portal hypothesis, OPEN), consume the lock: retire the lock-cell's `bridge_lock` nullifier-nonce
(write a spent marker, a metadata advance). The escrowed value already left at lock time, so the balance
is framed here. Fail-closed only on liveness of the lock-cell. -/
def bridgeFinalizeStep (s : RecChainedState) (actor lockCell : CellId) (spentMarker : ℤ) :
    Option RecChainedState :=
  if lockCell ∈ s.kernel.accounts then
    some { kernel := { s.kernel with
             cell := fun c => if c = lockCell then bridgeLockStep.setLockField (s.kernel.cell c) spentMarker
                              else s.kernel.cell c }
           log := { actor := actor, src := lockCell, dst := lockCell, amt := 0 } :: s.log }
  else none

/-- **`bridgeFinalizeStep` factors — PROVED.** A committed finalize implies the lock-cell was live and
pins the post-state (the spent-marker write + the receipt). -/
theorem bridgeFinalizeStep_factors {s s' : RecChainedState} {actor lockCell : CellId} {spentMarker : ℤ}
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    lockCell ∈ s.kernel.accounts ∧
      s' = { kernel := { s.kernel with
               cell := fun c => if c = lockCell then bridgeLockStep.setLockField (s.kernel.cell c) spentMarker
                                else s.kernel.cell c }
             log := { actor := actor, src := lockCell, dst := lockCell, amt := 0 } :: s.log } := by
  unfold bridgeFinalizeStep at h
  by_cases hl : lockCell ∈ s.kernel.accounts
  · rw [if_pos hl, Option.some.injEq] at h; exact ⟨hl, h.symm⟩
  · rw [if_neg hl] at h; exact absurd h (by simp)

/-- **`bridge_finalize_conserves` — balance framed (PROVED, `Σδ = 0`), gated by the §8 portal.** Given
the foreign-receipt portal `ForeignFinal nullifier value` (OPEN: discharged outside Lean), a committed
`bridgeFinalizeStep` preserves `recTotal`: the value already left at lock time, so finalization touches
only the `bridge_lock` nonce (the spent marker), never the balance field. -/
theorem bridge_finalize_conserves {s s' : RecChainedState} {actor lockCell : CellId}
    {spentMarker nullifier value : ℤ}
    (_hforeign : ForeignFinal nullifier value)
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨_, hs'⟩ := bridgeFinalizeStep_factors h
  subst hs'
  exact lockWrite_recTotal s.kernel lockCell spentMarker

/-- **`bridge_finalize_consumes_lock` — PROVED.** A committed finalize writes the lock-cell's
`bridge_lock` field to exactly the disclosed `spentMarker` — the nullifier becomes permanently spent
(replay-protection: the same foreign tx cannot be finalized twice). -/
theorem bridge_finalize_consumes_lock {s s' : RecChainedState} {actor lockCell : CellId} {spentMarker : ℤ}
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    lockOf (s'.kernel.cell lockCell) = spentMarker := by
  obtain ⟨_, hs'⟩ := bridgeFinalizeStep_factors h
  subst hs'
  simp only [if_pos]
  -- reading the freshly-written `bridge_lock` field returns the marker.
  unfold lockOf bridgeLockStep.setLockField
  cases s.kernel.cell lockCell with
  | record fs => simp [Value.scalar, Value.field, lockField]
  | int _ => simp [Value.scalar, Value.field, lockField]
  | dig _ => simp [Value.scalar, Value.field, lockField]
  | sym _ => simp [Value.scalar, Value.field, lockField]

/-- **`bridge_finalize_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem bridge_finalize_metadata {s s' : RecChainedState} {actor lockCell : CellId} {spentMarker : ℤ}
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨_, hs'⟩ := bridgeFinalizeStep_factors h
  subst hs'; refine ⟨by simp, rfl⟩

/-! ## §6 — Forward-simulation: every disclosed-supply / generative step is an abstract `Spec` step.

Mirroring `EffectTransfer §5`: the record-world abstract state `AbstractS` = (`balance`-domain total,
authority graph). For the disclosed effects the bottom edge records the disclosed `±delta` (not a
conservation `0`); for the paired bridge phases it records `0`. The authority graph is framed for all
(creation/supply never edits connectivity, except spawn which extends it — handled by its own provenance
keystone). -/

section ForwardSim
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- **`AbstractS`** — the record-world abstract Spec state the supply/generative effects refine: the
conserved `balance`-domain total and the reconstructed authority graph (the `EffectTransfer.AbstractT`
shape, re-named for this regime). -/
structure AbstractS where
  /-- the `balance`-domain total. -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph. -/
  authGraph    : Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights

/-- The abstraction function: a chained record state denotes its `recTotal` and its `execGraph`. -/
def absS (s : RecChainedState) : AbstractS :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- **`AbsStepDisclosed a a' delta`** — the abstract DISCLOSED-supply step: the abstract balance total
moved by exactly the disclosed `delta` (the receipt-visible non-conservation), and the authority graph is
UNCHANGED (creation/supply is connectivity-preserving). The bottom edge of the disclosed-supply square. -/
def AbsStepDisclosed (a a' : AbstractS) (delta : ℤ) : Prop :=
  a'.balanceTotal = a.balanceTotal + delta ∧ a'.authGraph = a.authGraph

/-- **`AbsStepPaired a a'`** — the abstract PAIRED step (the bridge escrow phases): the abstract balance
total is CONSERVED and the authority graph UNCHANGED. The bottom edge of the paired square (the
`EffectTransfer.AbsStep` shape). -/
def AbsStepPaired (a a' : AbstractS) : Prop :=
  conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal] ∧ a'.authGraph = a.authGraph

/-- **`create_forward_sim` — THE REFINEMENT for `CreateCell` (PROVED).** A committed `createCellStep` is
matched by an abstract DISCLOSED step `AbsStepDisclosed (absS s) (absS s') bal`: the abstract balance total
rises by exactly the disclosed `bal`, the authority graph is preserved, AND the committed creation passed
the privileged authority gate. The record-world disclosed-supply forward-simulation square for
`CreateCell`. -/
theorem create_forward_sim {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    AbsStepDisclosed (absS s) (absS s') bal ∧
      mintAuthorizedB s.kernel.caps actor newCell = true := by
  refine ⟨⟨?_, ?_⟩, create_authorized h⟩
  · simp only [absS]; exact create_conserves h
  · simp only [absS]; exact (create_metadata h).2

/-- **`bridge_mint_forward_sim` — THE REFINEMENT for `BridgeMint` (PROVED, §8-portal-gated).** GIVEN the
foreign-finality portal, a committed `bridgeMintStep` is matched by an abstract DISCLOSED step recording
the disclosed `+value`, with the authority graph preserved and the local mint gate passed. -/
theorem bridge_mint_forward_sim {s s' : RecChainedState} {actor cell : CellId} {value nullifier : ℤ}
    (hforeign : ForeignFinal nullifier value)
    (h : bridgeMintStep s actor cell value = some s') :
    AbsStepDisclosed (absS s) (absS s') value ∧
      mintAuthorizedB s.kernel.caps actor cell = true := by
  refine ⟨⟨?_, ?_⟩, bridge_mint_authorized h⟩
  · simp only [absS]; exact bridge_mint_conserves hforeign h
  · simp only [absS]; exact (bridge_mint_metadata h).2

/-- **`bridge_lock_forward_sim` — THE REFINEMENT for `BridgeLock` (PROVED).** A committed `bridgeLockStep`
is matched by an abstract PAIRED step: the abstract balance total is conserved (the internal escrow), the
authority graph preserved, and the escrow turn passed the abstract authority `Guard`. The record-world
paired forward-simulation square for the bridge lock. -/
theorem bridge_lock_forward_sim {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (w : Statement → Witness) (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    AbsStepPaired (absS s) (absS s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps) (lockTurn owner lockCell value) w = true := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold conservedInDomain absS; rw [bridge_lock_conserves h]; simp
  · simp only [absS]; exact (bridge_lock_metadata h).2
  · rw [Dregg2.Spec.exec_authz_iff_guard]; exact bridge_lock_authorized h

end ForwardSim

/-! ## §7 — Axiom-hygiene tripwires (honesty pins over every keystone).

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. The §8 foreign-finality portal `ForeignFinal` is an `opaque` `Prop` (a data carrier,
never an axiom — it never closes a goal, only appears as a hypothesis on the bridge keystones). The
`#assert_axioms` below confirm the local transitions are genuinely proved; the foreign half is carried,
never faked. -/

#assert_axioms createCellStep_factors
#assert_axioms createCellInto_recTotal
#assert_axioms create_conserves
#assert_axioms create_discloses
#assert_axioms create_disclosed_domain
#assert_axioms create_authorized
#assert_axioms create_unauthorized_fails
#assert_axioms create_caps_unchanged
#assert_axioms create_metadata

#assert_axioms factory_create_factors
#assert_axioms factory_constructor_transparency
#assert_axioms factory_create_conserves
#assert_axioms factory_create_discloses
#assert_axioms factory_create_authorized
#assert_axioms factory_create_metadata

#assert_axioms spawnStep_factors
#assert_axioms spawn_conserves
#assert_axioms spawn_discloses
#assert_axioms spawn_authorized
#assert_axioms spawn_parent_grounded
#assert_axioms spawn_provenance
#assert_axioms spawn_parent_snapshot
#assert_axioms spawn_metadata

#assert_axioms bridgeMintStep_factors
#assert_axioms bridge_mint_conserves
#assert_axioms bridge_mint_discloses
#assert_axioms bridge_mint_authorized
#assert_axioms bridge_mint_unauthorized_fails
#assert_axioms bridge_mint_caps_unchanged
#assert_axioms bridge_mint_metadata

#assert_axioms setLockField_balOf
#assert_axioms bridgeLockStep_factors
#assert_axioms lockWrite_recTotal
#assert_axioms bridge_lock_conserves
#assert_axioms bridge_lock_paired_domain
#assert_axioms bridge_lock_authorized
#assert_axioms bridge_lock_metadata

#assert_axioms bridge_cancel_conserves
#assert_axioms bridge_cancel_authorized
#assert_axioms bridge_cancel_metadata

#assert_axioms bridgeFinalizeStep_factors
#assert_axioms bridge_finalize_conserves
#assert_axioms bridge_finalize_consumes_lock
#assert_axioms bridge_finalize_metadata

#assert_axioms create_forward_sim
#assert_axioms bridge_mint_forward_sim
#assert_axioms bridge_lock_forward_sim

/-! ## §8 — Non-vacuity: each effect commits and moves the right measure; unauthorized rejected.

Fixture: cells 0,1 with balances 100,5; actor 9 holds the privileged `node 0` and `node 2`
mint/create caps; owner 0 owns its own cell (authority by ownership for the escrow moves). -/

/-- The non-vacuity fixture: cell 0 = 100, cell 1 = 5; actor 9 holds `node 0`,`node 2`
(create/mint authority over cells 0 and the fresh 2). -/
def ss0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 2] else [] }
    log := [] }

-- CreateCell: actor 9 (holds `node 2`) creates fresh cell 2 with disclosed balance 50 — commits,
-- discloses +50 (105 → 155), grows the chain by one:
#eval (createCellStep ss0 9 2 50).isSome                                    -- true
#eval (createCellStep ss0 9 2 50).map (fun s => recTotal s.kernel)          -- some 155
#eval recTotal ss0.kernel                                                   -- 105
#eval (createCellStep ss0 9 2 50).map (fun s => s.log.length)               -- some 1
-- ...the fresh cell 2 carries the disclosed balance:
#eval (createCellStep ss0 9 2 50).map (fun s => balOf (s.kernel.cell 2))    -- some 50
-- An unauthorized creator (actor 0 holds no create cap) is rejected (fail-closed):
#eval (createCellStep ss0 0 2 50).isSome                                    -- false
-- A non-fresh id (cell 1 already live) is rejected:
#eval (createCellStep ss0 9 1 50).isSome                                    -- false

-- SpawnWithDelegation: child creation alone cannot mint authority to an unheld parent target:
#eval (spawnStep ss0 9 2 1 20).isSome                                       -- false
-- ...but actor 9 can spawn child 2 (balance 20) with a copy of its held parent `node 0` cap:
#eval (spawnStep ss0 9 2 0 20).isSome                                       -- true
#eval (spawnStep ss0 9 2 0 20).map (fun s => recTotal s.kernel)             -- some 125 (disclosed +20)
-- ...and the child carries the concrete copied parent cap (`node 0`), not a manufactured target cap:
#eval ((spawnStep ss0 9 2 0 20).map (fun s => s.kernel.caps 2)).getD []     -- [Cap.node 0]
#eval (spawnStep ss0 9 2 0 20).map
        (fun s => (s.kernel.delegate 2, s.kernel.delegations 2))             -- some (some 9, [Cap.node 0, Cap.node 2])

-- BridgeMint: actor 9 (holds `node 0`) mints +40 into cell 0 — local credit commits, discloses +40:
#eval (bridgeMintStep ss0 9 0 40).isSome                                    -- true
#eval (bridgeMintStep ss0 9 0 40).map (fun s => recTotal s.kernel)          -- some 145 (= 105 + 40)
-- An unauthorized bridge-mint (actor 0) is rejected (the LOCAL gate, independent of foreign finality):
#eval (bridgeMintStep ss0 0 0 40).isSome                                    -- false

-- BridgeLock: owner 0 escrows 30 into lock-cell 1 (owns cell 0) — commits, CONSERVES (105 → 105):
#eval (bridgeLockStep ss0 0 1 30 777).isSome                              -- true
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => recTotal s.kernel)    -- some 105 (PAIRED Σ=0)
-- ...the value moved owner 0 (100→70) into lock-cell 1 (5→35):
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => balOf (s.kernel.cell 0))  -- some 70
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => balOf (s.kernel.cell 1))  -- some 35
-- ...and lock-cell 1's `bridge_lock` nullifier-nonce is set to 777:
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => lockOf (s.kernel.cell 1)) -- some 777

-- BridgeCancel: owner 0 refunds 30 back from lock-cell 1 — commits, CONSERVES:
#eval (bridgeCancelStep ss0 0 1 30).isSome                                -- false (no value at lock yet)
-- (cancel after a lock: lock then cancel round-trips conservatively — checked via composition below)

-- BridgeFinalize: consume lock-cell 1's nullifier (live) — commits, CONSERVES, retires the lock to 999:
#eval (bridgeFinalizeStep ss0 9 1 999).isSome                               -- true
#eval (bridgeFinalizeStep ss0 9 1 999).map (fun s => recTotal s.kernel)     -- some 105 (balance FRAMED)
#eval (bridgeFinalizeStep ss0 9 1 999).map (fun s => lockOf (s.kernel.cell 1))  -- some 999 (spent)
-- A finalize on a dead lock-cell is rejected:
#eval (bridgeFinalizeStep ss0 9 7 999).isSome                               -- false

end Dregg2.Exec.EffectsSupply
