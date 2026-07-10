/-
# Dregg2.Circuit.FinGrantSpawnSquares — DEBT-B effect-coverage: the two closable uncovered effects.

`FinProgramSquares` + `FinCreateCellSquares` (committed) proved the commuting square
`denote (finInterp p f) = interp p (denote f)` for 30 Argus `*Stmt` programs. Of the 33 deployed `Effect`
variants, six have a distinct apply method and NO Argus program. Four are genuinely out of finite-map scope
(`ShieldedTransfer` = STARK/DEBT-A; `Notify`/`React`/`Promise` = the reactive Track-2 subsystem). This file
closes the remaining TWO — `GrantCapability` and `SpawnWithDelegation` — by modeling each deployed apply
(read from `turn/src/executor/apply.rs`) as an Argus `RecStmt` program over already-covered primitives and
proving its square.

## FINDING (honest, both PROVED).
* **`GrantCapability`** (`apply_grant_capability`) — its KERNEL MUTATION is
  `to_cell.capabilities.grant_ref(cap)`: install into the RECIPIENT (`to`) c-list a cap over `cap.target`
  derived from the granter (`from`)'s held cap over that target. This is the SAME `setCaps`/`grant` writer as
  `introduce` — DEFINITIONALLY `introduceCaps from to target` (`grant k.caps to (heldCapTo k.caps from
  target)`). So GrantCapability REDUCES to `introduce`'s covered writer; the ONLY difference is the guard
  (cross-cell `Delegate` permission + 3-axis attenuation + self-grant bypass, vs. introduce's Granovetter
  connectivity) — a `Pure` domain-restrictor the finite refinement handles uniformly, here left abstract
  (`φ`). Square: `pureThenWriter_square` + the committed `introduceCaps_finiteDiff`.
* **`SpawnWithDelegation`** (`apply_spawn_with_delegation`) — reads the parent (`action_target`), CREATES a
  child cell (`Cell::with_balance` + `insert_cell`), and DELEGATES by writing TWO child fields:
  `child.delegate = Some(parent)` and `child.delegation = DelegatedRef(parent's c-list snapshot, …)`. So its
  mutation is the `seq` COMPOSITION of three covered writers — `allocCell` (`denote_finAllocCell`,
  unconditional) ⨾ `setDelegate` (the parent-pointer write, `denote_finSetDelegate`) ⨾ `setDelegations` (the
  c-list snapshot `k.caps parent`, `denote_finSetDelegations`) — composed via `denote_seq_compose`. The two
  snapshot FiniteDiffs are single-child point diffs, proved here as REAL theorems. NOTE: the deployed
  `DelegatedRef` also stamps `delegation_epoch`/timestamp; the finite model (matching the covered
  `refreshDelegationStmt`) abstracts the snapshot to its `delegations` c-list column — the load-bearing
  authority content — so those metadata stamps are out of the modeled `delegations` write.

Builds ON committed `FinCreateCellSquares`/`FinAllocCell`/`FinInterp`/`FinProgramSquares` + Argus terms;
edits NOTHING committed. Sorry-free; no carrier.
-/
import Dregg2.Circuit.FinCreateCellSquares

namespace Dregg2.Circuit.FinGrantSpawnSquares

open Dregg2.Exec
open Dregg2.Exec (grant heldCapTo)
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.FinInterp
open Dregg2.Circuit.FinAllocCell
open Dregg2.Circuit.FinProgramSquares (pureThenWriter_square introduceCaps_finiteDiff)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Argus.Effects.Introduce (introduceCaps introduceGate)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## §1 — `GrantCapability` — REDUCES to `introduce`'s covered `setCaps`/`grant` writer.

The deployed `apply_grant_capability` mutation is `to_cell.capabilities.grant_ref(cap)` — install into the
recipient `to`'s c-list a cap over `cap.target` sourced from the granter `from`'s held cap. That IS
`introduceCaps from to target` (the `introduce` writer). We model the guard abstractly (`φ`) — the deployed
cross-cell-permission + attenuation gate is a `Pure` domain-restrictor that does not affect the writer
square — and assemble via the committed `pureThenWriter_square`. -/

/-- **The `GrantCapability` effect as an Argus IR term.** A `Pure` guard `φ` (the deployed cross-cell
`Delegate`-permission + 3-axis attenuation gate) then the `introduce` cap-graph writer: copy the granter's
held cap over `target` into the recipient `to`'s c-list. `to` = the recipient slot, `from` = the granter,
`target` = `cap.target`. -/
def grantCapabilityStmt (frm recp target : CellId) (φ : RecordKernelState → Bool) : RecStmt :=
  RecStmt.seq (RecStmt.guard φ) (RecStmt.setCaps (introduceCaps frm recp target))

/-- **`grantCapabilityStmt_square`** — R1's `hpres` for the deployed `GrantCapability` effect term. The
finite step (guard leaf via `finInterp`, then the `introduceCaps` `setCaps` write, touched slot `{to}`)
denotes to `interp (grantCapabilityStmt …)`. The writer square is the committed `denote_finSetCaps` under
`introduceCaps_finiteDiff` — the SAME discharge `introduce` uses; GrantCapability adds nothing new to the
mutation, only a different (abstract) guard. -/
theorem grantCapabilityStmt_square (frm recp target : CellId) (φ : RecordKernelState → Bool)
    (f : FinKernelState) :
    ((finInterp (.guard φ) f).bind
      (fun f' => some (finSetCaps (introduceCaps frm recp target) {recp} f'))).map denote
      = interp (grantCapabilityStmt frm recp target φ) (denote f) := by
  unfold grantCapabilityStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCaps (introduceCaps frm recp target) {recp} g
      (introduceCaps_finiteDiff frm recp target g)) f

/-! ## §2 — `SpawnWithDelegation` — a `seq` COMPOSITION of covered writers (allocCell ⨾ setDelegate ⨾
setDelegations).

The deployed `apply_spawn_with_delegation` births a child and writes two child fields: `delegate := parent`
and `delegation := parent's c-list snapshot`. We model it as three covered leaves. The two snapshot writes
are single-child point diffs (FiniteDiff off `{child}`), proved here. -/

/-- The `delegate`-pointer write leaf: set `child.delegate := some parent`, leave every other cell's
delegate pointer untouched (`k.delegate c`). Matches deployed `child_cell.delegate = Some(*action_target)`. -/
def spawnDelegateLeaf (parent child : CellId) : RecordKernelState → CellId → Option CellId :=
  fun k c => if c = child then some parent else k.delegate c

/-- The `delegations`-snapshot write leaf: set `child.delegations := parent's live c-list` (`k.caps
parent`), leave every other cell's snapshot untouched. Matches deployed `child_cell.delegation =
DelegatedRef(snapshot = parent.capabilities, …)`, modeled (as `refreshDelegationStmt` does) at the
`delegations` c-list column. -/
def spawnDelegationsLeaf (parent child : CellId) : RecordKernelState → CellId → List Cap :=
  fun k c => if c = child then k.caps parent else k.delegations c

/-- **The `SpawnWithDelegation` effect as an Argus IR term.** A `Pure` guard `φ` (the deployed
parent-`action_target`-exists precondition), then the child allocation (`allocCell`), then the two
delegation writes (`setDelegate` ⨾ `setDelegations`). -/
def spawnWithDelegationStmt (parent child : CellId) (φ : RecordKernelState → Bool) : RecStmt :=
  RecStmt.seq (RecStmt.guard φ)
    (RecStmt.seq (RecStmt.allocCell (fun _ => child))
      (RecStmt.seq (RecStmt.setDelegate (spawnDelegateLeaf parent child))
        (RecStmt.setDelegations (spawnDelegationsLeaf parent child))))

/-- The `delegate`-pointer write is a single-child diff off `{child}`: every OTHER cell keeps its parent
pointer. Discharges the `setDelegate` FiniteDiff side condition. -/
theorem spawnDelegateLeaf_finiteDiff (parent child : CellId) (g : FinKernelState) :
    ∀ c, c ∉ ({child} : Finset CellId) →
      spawnDelegateLeaf parent child (denote g) c = (denote g).delegate c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  simp only [spawnDelegateLeaf, if_neg hc]

/-- The `delegations`-snapshot write is a single-child diff off `{child}`: every OTHER cell keeps its
snapshot. Discharges the `setDelegations` FiniteDiff side condition. -/
theorem spawnDelegationsLeaf_finiteDiff (parent child : CellId) (g : FinKernelState) :
    ∀ c, c ∉ ({child} : Finset CellId) →
      spawnDelegationsLeaf parent child (denote g) c = (denote g).delegations c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  simp only [spawnDelegationsLeaf, if_neg hc]

/-- **`spawnWithDelegationStmt_square`** — R1's `hpres` for the deployed `SpawnWithDelegation` effect term.
The finite step composes the four leaves — guard ⨾ `allocCell` ⨾ `setDelegate` ⨾ `setDelegations` — through
the committed `denote_seq_compose`; each leaf's square is `denote_finInterp` / `denote_finAllocCell`
(unconditional) / `denote_finSetDelegate` (FiniteDiff §2) / `denote_finSetDelegations` (FiniteDiff §2). -/
theorem spawnWithDelegationStmt_square (parent child : CellId) (φ : RecordKernelState → Bool)
    (f : FinKernelState) :
    ((finInterp (.guard φ) f).bind (fun f1 =>
      (some (finAllocCell (fun _ => child) f1)).bind (fun f2 =>
        (some (finSetDelegate (spawnDelegateLeaf parent child) {child} f2)).bind (fun f3 =>
          some (finSetDelegations (spawnDelegationsLeaf parent child) {child} f3))))).map denote
      = interp (spawnWithDelegationStmt parent child φ) (denote f) := by
  unfold spawnWithDelegationStmt
  exact denote_seq_compose
    (fun g => denote_finInterp (.guard φ) trivial g)
    (fun g => denote_seq_compose
      (fun g' => by rw [Option.map_some]; exact denote_finAllocCell (fun _ => child) g')
      (fun g' => denote_seq_compose
        (fun g'' => by
          rw [Option.map_some]
          exact denote_finSetDelegate (spawnDelegateLeaf parent child) {child} g''
            (spawnDelegateLeaf_finiteDiff parent child g''))
        (fun g'' => by
          rw [Option.map_some]
          exact denote_finSetDelegations (spawnDelegationsLeaf parent child) {child} g''
            (spawnDelegationsLeaf_finiteDiff parent child g''))
        g')
      g)
    f

/-! ## §3 — TEETH (both polarities), for each of the two.

Positive: the deployed write fires on a concrete state (denotation obtained VIA the square, not by
evaluating the noncomputable `setOver`/`setDelegateList`). Negative: an under-approximated (empty) touched
set makes the FiniteDiff obligation FALSE — the square cannot be discharged with a mismatched touched set. -/

section Teeth

/-! ### GrantCapability. On `finInit` the granter (`1`) holds no cap, so `heldCapTo` yields `Cap.null`; the
`grant` still INSTALLS that cap into the recipient (`0`)'s empty slot — the write genuinely changes `0`'s
c-list from `[]` to `[Cap.null]`. -/

/-- **POSITIVE — the deployed GrantCapability writer fires.** Granting (granter `1`, recipient `0`, target
`2`) installs a cap into recipient `0`'s c-list: `[] → [Cap.null]`. -/
theorem grantCapability_fires :
    (denote (finSetCaps (introduceCaps 1 0 2) {0} finInit)).caps 0 = [Cap.null] := by
  have hsq := denote_finSetCaps (introduceCaps 1 0 2) {0} finInit
    (introduceCaps_finiteDiff 1 0 2 finInit)
  have hd := Option.some.inj (by simpa only [interp] using hsq)
  rw [hd]
  show introduceCaps 1 0 2 (denote finInit) 0 = [Cap.null]
  simp [introduceCaps, grant, heldCapTo, denote, finInit, CanonMap.get_empty]

/-- **NEGATIVE — the GrantCapability `setCaps` FiniteDiff BITES over the EMPTY touched set.** The genuine
`introduceCaps` write changes recipient `0`'s slot (`[] → [Cap.null]`), so the agreement-off-`∅` obligation
is FALSE — an under-approximated touched set cannot discharge the square. -/
theorem grantCapability_notFiniteDiff_over_empty :
    ¬ (∀ l, l ∉ (∅ : Finset Label) →
        introduceCaps 1 0 2 (denote finInit) l = (denote finInit).caps l) := by
  intro hall
  have h0 := hall 0 (by simp)
  rw [show introduceCaps 1 0 2 (denote finInit) 0 = [Cap.null] from by
        simp [introduceCaps, grant, heldCapTo, denote, finInit, CanonMap.get_empty]] at h0
  rw [show (denote finInit).caps 0 = [] from by simp [denote, finInit, CanonMap.get_empty]] at h0
  exact absurd h0 (List.cons_ne_nil _ _)

/-! ### SpawnWithDelegation. On `finInit` the child (`0`) has `delegate = none`; the deployed spawn sets
`child.delegate := some parent` — genuinely changing it. -/

/-- **POSITIVE — the deployed SpawnWithDelegation `delegate` write fires.** Spawning child `0` under parent
`1` sets `0`'s delegation-parent pointer to `some 1` (was `none`). -/
theorem spawnWithDelegation_delegate_fires :
    (denote (finSetDelegate (spawnDelegateLeaf 1 0) {0} finInit)).delegate 0 = some 1 := by
  have hsq := denote_finSetDelegate (spawnDelegateLeaf 1 0) {0} finInit
    (spawnDelegateLeaf_finiteDiff 1 0 finInit)
  have hd := Option.some.inj (by simpa only [interp] using hsq)
  rw [hd]
  show spawnDelegateLeaf 1 0 (denote finInit) 0 = some 1
  simp [spawnDelegateLeaf]

/-- **NEGATIVE — the SpawnWithDelegation `setDelegate` FiniteDiff BITES over the EMPTY touched set.** The
genuine write changes child `0`'s parent pointer (`none → some 1`), so the agreement-off-`∅` obligation is
FALSE. -/
theorem spawnWithDelegation_notFiniteDiff_over_empty :
    ¬ (∀ c, c ∉ (∅ : Finset CellId) →
        spawnDelegateLeaf 1 0 (denote finInit) c = (denote finInit).delegate c) := by
  intro hall
  have h0 := hall 0 (by simp)
  rw [show spawnDelegateLeaf 1 0 (denote finInit) 0 = some 1 from by simp [spawnDelegateLeaf]] at h0
  rw [show (denote finInit).delegate 0 = none from by simp [denote, finInit]] at h0
  exact absurd h0 (by simp)

end Teeth

end Dregg2.Circuit.FinGrantSpawnSquares
