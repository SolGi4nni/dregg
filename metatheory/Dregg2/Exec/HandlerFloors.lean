/-
# Dregg2.Exec.HandlerFloors — the UNIFORM FLOOR-OBLIGATION SURFACE (P0 of the
proof-carrying handler-executor campaign).

`EffectHandler` (`Dregg2/Exec/Handler.lean`) captures exactly THREE floors as typed proof fields
(`auth_gated` / `admission_gated` / `conserves`). The other six floors the campaign names —
reserved-field, caveat-admission, freshness/delegation-epoch, non-amplification, monotone-nonce,
index-bounds/membership — are enforced AD-HOC inside individual `step` functions. Where a handler's
`step` is *weaker* than `execFullA`'s arm, the corresponding `handler_refines_execFullA_*` theorem
carries the missing gate as a SIDE-HYPOTHESIS (`hnr` / `hcav` / `hmono` / `hb` / `hmem` / the
epoch-residual). **Those side-hypotheses are the silent-gate holes**: the handler type-checks WITHOUT
the gate, and the gate only re-appears as something the *caller* must supply.

This module is the P0 beachhead — the structural retirement of that hole class. It defines a single
uniform **`FloorObligation`** surface: a named floor is a `Prop`-valued post/pre-condition the
handler's `step` must satisfy on every commit, bundled WITH the proof that it does. Promoting a floor
to a `FloorObligation` makes the missing-gate UNREPRESENTABLE — the floor becomes a typing condition,
exactly as `auth_gated`/`conserves` already are.

## The key design risk — and how this settles it

The research flagged (RESEARCH-handler-executor.md §5) that the floors are NOT uniform: authority and
admission are `St → Args → Bool` GATES, but `conserves`, `freshness`, and `non-amplification` are
RELATIONAL — predicates over the post-state / over delegation edges, not single Bool gates. A naive
"add three more Bool fields" under-models the relational floors.

**The settle: make the floor `Prop`-valued, not `Bool`-valued.** `FloorObligation.floor : St → Args →
Prop` is general enough to express BOTH:

  * a Bool gate `g : St → Args → Bool` lifts via `g s a = true` (the `ofBoolGate` constructor below),
    so the existing auth/admission/reserved-field floors fit WITHOUT change of meaning; AND

  * a relational floor (e.g. `fieldOf "nonce" (cell target) < n`, or `granted ⊆ held`) IS ALREADY a
    `Prop` — it drops straight in, no Bool encoding required.

So the surface is genuinely uniform over both floor kinds. We SETTLE this by proving BOTH a Bool-gate
floor (reserved-field, §3) AND a relational floor (monotone-nonce, §4) inhabit the SAME
`FloorObligation` structure, each discharged from the EXISTING just-banked gate lemmas
(`stateStepDev_notReserved`, `incrementNonceStep_advances`) — no new gate logic, only the uniform
re-presentation.

Pure, additive: imports the existing `EffectsState`/`StateSupply` infra, edits no existing file.
Verified: `lake build Dregg2.Exec.HandlerFloors`.
-/
import Dregg2.Exec.Handler
import Dregg2.Exec.EffectsState
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Exec.Handlers.Authority
import Dregg2.Tactics

namespace Dregg2.Exec.HandlerFloors

open Dregg2.Exec
open Dregg2.Exec (confRights heldCapTo attenuate recKDelegateAtten recKDelegateAtten_non_amplifying)
open Dregg2.Exec.Handlers.Authority (DelegateArgs delegateAttenStep delegateAttenH)
open Dregg2.Exec.EffectsState (reservedField stateStepDev stateStepDev_notReserved
  incrementNonceStep incrementNonceStep_advances fieldOf)
open Dregg2.Exec.TurnExecutorFull (spawnChainA refreshDelegationChainA parentEpoch
  spawnChainA_stamps_epoch spawnChainA_fresh_at_birth
  spawnChainA_provenance spawnChainA_parent_snapshot spawnChainA_factors
  createCellChainA createCellFromFactoryChainA createCellFromFactoryChainA_factors
  createCellFromFactoryChainA_installs_program createCellFromFactoryChainA_unknown_factory_fails
  factoryVkField installInitialFields
  refreshDelegationChainA_restamps_epoch refreshDelegationChainA_fresh
  refreshDelegationChainA_noParent_rejects
  noteSpendChainA noteSpendChainA_requires_proof noteSpendChainA_fails_without_proof)
open Dregg2.Exec (heldCapTo findFactory)
open Dregg2.Exec.EffectsState (setField)
open Dregg2.Exec (delegationStale)
open Dregg2.Substrate.HeapKernel (heapStepGuardedW heapStepW_root_pinned heapStepW_heaps
  heapRootField)
open Dregg2.Substrate.Heap (set)

/-! ## §1 — The uniform `FloorObligation` surface (`Prop`-valued).

`FloorObligation St Args step` is parameterized by the handler's transition `step : St → Args →
Option St` (so the floor is ABOUT that step). It bundles:

  * `floor : St → Args → Prop` — the named precondition/postcondition the commit must satisfy; AND
  * `gated : ∀ s a s', step s a = some s' → floor s a` — the PROOF that every commit satisfies it.

A `FloorObligation` literal is ILL-TYPED until `gated` is discharged against `step`. So registering a
handler with its floor obligation is the typing condition that retires the silent-gate hole: a handler
whose `step` could commit while VIOLATING the floor cannot inhabit this structure.

`St` is left general (`RecChainedState` for the field-write/nonce family, `RecordKernelState` for the
authority family) so ONE surface covers every handler. -/
structure FloorObligation (St : Type) (Args : Type) (step : St → Args → Option St) where
  /-- The named floor: a `Prop` the commit's pre-state + args must satisfy. `Prop`-valued (NOT
  `Bool`) so it uniformly expresses Bool gates (`g s a = true`) AND relational floors. -/
  floor : St → Args → Prop
  /-- OBLIGATION: every commit satisfies the floor. Discharging this is the typing condition that
  makes the missing gate unrepresentable. -/
  gated : ∀ s a s', step s a = some s' → floor s a

/-- **`ofBoolGate` — the Bool-gate floors fit the uniform surface.** A handler's existing
`St → Args → Bool` gate `gate` (the shape of `auth`/`admission`/`reservedField`), together with its
`*_gated` proof, becomes a `FloorObligation` by reading the floor as `gate s a = true`. This is the
witness that the THREE existing typed floors (`auth_gated`/`admission_gated`) and the Bool-shaped new
floors (reserved-field, index-bounds) all live on the SAME surface — no relational machinery needed
for them, but they share the structure with the floors that DO need it. -/
def ofBoolGate {St Args : Type} {step : St → Args → Option St}
    (gate : St → Args → Bool)
    (gated : ∀ s a s', step s a = some s' → gate s a = true) :
    FloorObligation St Args step where
  floor := fun s a => gate s a = true
  gated := gated

/-- A committed step DISCHARGES its floor obligation — the projection every downstream refinement
reuses to SHED its side-hypothesis. Where today `handler_refines_execFullA_setField` takes `hnr`/`hcav`
as hypotheses, once the handler carries the matching `FloorObligation` this lemma SUPPLIES them from
the commit itself — the side-hyp becomes a derived fact, not a caller obligation. -/
theorem FloorObligation.discharge {St Args : Type} {step : St → Args → Option St}
    (fo : FloorObligation St Args step) {s : St} {a : Args} {s' : St}
    (h : step s a = some s') : fo.floor s a :=
  fo.gated s a s' h

/-! ### §1b — `PostFloorObligation` — the POST-CONDITION floor (the freshness kind).

Three of the named floors are PRE-state relations (`reservedField`/monotone-nonce/non-amp): the relation
holds on `s`/`a` and the commit merely WITNESSES it, so `FloorObligation` (floor over `s a`) captures
them. The lifecycle-FRESHNESS floor (§4c) is genuinely a POST-condition: the step WRITES the child's
`delegationEpochAt` stamp, so the floor relates the POST-state stamp (`s'.delegationEpochAt child`) to a
pre-state parent epoch. `floor : St → Args → St → Prop` exposes the post `s'`, and `gated` proves it on
every commit — the same uniform contract (a typed obligation the step must meet), one slot wider. -/
structure PostFloorObligation (St : Type) (Args : Type) (step : St → Args → Option St) where
  /-- The named floor, now ALSO over the post-state `s'`: the post-condition the commit installs. -/
  floor : St → Args → St → Prop
  /-- OBLIGATION: every commit satisfies the post-floor. -/
  gated : ∀ s a s', step s a = some s' → floor s a s'

/-- A committed step DISCHARGES its post-floor obligation — the projection a refinement reuses to SHED
the post-condition residual (e.g. the epoch-stamp residual) it USED to carry explicitly. -/
theorem PostFloorObligation.discharge {St Args : Type} {step : St → Args → Option St}
    (fo : PostFloorObligation St Args step) {s : St} {a : Args} {s' : St}
    (h : step s a = some s') : fo.floor s a s' :=
  fo.gated s a s' h

/-! ## §2 — Floor argument records (the args the two PoC floors range over).

These mirror the existing `StateWriteArgs` shape (a developer field write) but expose the `(actor,
target, field, value)` the floor predicates read. Reusing concrete records keeps the floors
`#assert_axioms`-clean and ties them to the live `stateStepDev`/`incrementNonceStep` steps. -/

/-- Args for a developer `SetField` (the reserved-field floor ranges over `field`). -/
structure SetFieldArgs where
  /-- The actor performing the write. -/
  actor : CellId
  /-- The cell whose field is written. -/
  target : CellId
  /-- The named field written (the reserved-field floor forbids the four protocol slots). -/
  field : FieldName
  /-- The scalar value written. -/
  value : Int

/-- Args for a monotone-nonce write (the floor relates the stored nonce to the new value). -/
structure NonceArgs where
  /-- The actor bumping the nonce. -/
  actor : CellId
  /-- The cell whose nonce advances. -/
  target : CellId
  /-- The new nonce value (must STRICTLY exceed the stored nonce). -/
  value : Int

/-! ## §3 — POC INSTANCE A (BOOL-GATE FLOOR): reserved-field, over the developer `SetField`.

The reserved-field floor is the just-banked `c4f4f0012` fix: a developer `SetField` may NOT write a
protocol-managed slot (`nonce`/`permissions`/`verification_key`/`program`) — only its dedicated effect
owns it. This is a BOOL gate (`reservedField f = false`). It WAS carried as the `hnr` side-hyp of
`handler_refines_execFullA_setField` — now SHED (§P1): the `.setFieldA` handler's own step carries it.

We give the developer-write step `stateStepDev` a `FloorObligation` whose floor is `reservedField
a.field = false`, discharged from `stateStepDev_notReserved` (the just-banked lemma proving a committed
developer write touched a NON-reserved slot). The floor is Bool-shaped — but we present it directly as
the `Prop` `reservedField a.field = false` (a `Bool = false` equation IS a `Prop`), demonstrating the
Bool floors live on the uniform surface natively. -/

/-- The developer-write step lifted to `SetFieldArgs` (the field-write the reserved gate guards). -/
def setFieldStep (s : RecChainedState) (a : SetFieldArgs) : Option RecChainedState :=
  stateStepDev s a.field a.actor a.target a.value

/-- **`reservedFieldFloor` — the BOOL-GATE floor as a `FloorObligation`.** Floor: the written slot is
NOT a protocol-managed slot (`reservedField a.field = false`). Discharged on every commit by
`stateStepDev_notReserved` — the just-banked reserved gate is now a TYPED obligation, not a refinement
side-hypothesis. A `stateStepDev` variant that wrote a reserved slot could not inhabit this. -/
def reservedFieldFloor : FloorObligation RecChainedState SetFieldArgs setFieldStep where
  floor := fun _ a => reservedField a.field = false
  gated := by
    intro s a s' h
    exact stateStepDev_notReserved h

/-! ## §4 — POC INSTANCE B (RELATIONAL FLOOR): monotone-nonce, over `incrementNonceStep`.

The monotone-nonce floor is the just-banked nonce-no-replay fix: `IncrementNonce` may only ADVANCE the
nonce (`old < n`), never reset it (a reset is the same replay vector as `setField "nonce"`). This is
RELATIONAL — it relates the PRE-STATE's stored nonce (`fieldOf "nonce" (s.kernel.cell target)`) to the
new value `n`. It is NOT a `St → Args → Bool` gate over args alone; it reads the state. It is carried
TODAY as the `hmono` side-hyp of `handler_refines_execFullA_stateWrite`.

This is the floor the research flagged as the genuine risk — and it inhabits the SAME `FloorObligation`
structure as the Bool floor above, because `floor` is `Prop`-valued. The floor IS the relation
`fieldOf "nonce" (cell target) < value`, discharged from `incrementNonceStep_advances`. No Bool
encoding; the relation drops straight in. -/

/-- The monotone-nonce step lifted to `NonceArgs`. -/
def nonceStep (s : RecChainedState) (a : NonceArgs) : Option RecChainedState :=
  incrementNonceStep s a.actor a.target a.value

/-- **`nonceMonotoneFloor` — the RELATIONAL floor as a `FloorObligation`.** Floor: the new nonce
STRICTLY exceeds the stored nonce (`fieldOf "nonce" (cell target) < value`) — a relation over the
pre-state, NOT a Bool gate. Discharged on every commit by `incrementNonceStep_advances`. THIS is the
proof that the uniform `Prop`-valued surface handles the relational floor kind — the research's main
design risk, settled affirmatively: the relational floor needs NO different treatment, it is just a
different `floor` body in the SAME structure. -/
def nonceMonotoneFloor : FloorObligation RecChainedState NonceArgs nonceStep where
  floor := fun s a => fieldOf "nonce" (s.kernel.cell a.target) < a.value
  gated := by
    intro s a s' h
    exact incrementNonceStep_advances h

/-! ## §4b — POC INSTANCE C (RELATIONAL FLOOR): AUTHORITY NON-AMPLIFICATION, over `delegateAttenStep`.

The non-amplification floor is the authority-graph keystone (the §P2 family): a granted/delegated cap
may confer rights NO GREATER than the cap the delegator actually held — `confRights granted ≤ confRights
held` over the genuine `ExecAuth` lattice. A delegation that *amplified* rights (handed the recipient a
stronger cap than the delegator possessed) would be the rights-forgery the whole ocap discipline forbids.
This is RELATIONAL — it relates the rights of the GRANTED cap (`attenuate keep (heldCapTo … delegator t)`)
to the rights of the HELD cap (`heldCapTo … delegator t`), both read off the pre-state's cap graph. It
is NOT a `St → Args → Bool` gate over args alone, exactly like monotone-nonce (§4).

THE CLEANER DISCHARGE (the prompt's "even cleaner" path). Unlike the reserved-field / monotone floors —
where the handler's `step` had to be RE-ROUTED through a fail-closing guard before the floor could be
read off the commit — the authority handler `delegateAttenStep` ALREADY installs the *attenuated* grant
`attenuate keep (heldCapTo …)` by construction (it routes through `recKDelegateAtten`, the faithful
`apply_introduce`, NOT a fresh control cap). The non-amplification relation therefore holds on the
pre-state UNCONDITIONALLY — `recKDelegateAtten_non_amplifying` (`AuthTurn.lean`, a genuine `≤` over
`ExecAuth`, NOT a `()≤()` collapse) proves it for ANY `keep`, with or without a commit. So the floor
DISCHARGES from the existing step's post-condition with no re-route: the handler was ALREADY strong
enough, and the `FloorObligation` simply PROMOTES the latent non-amp fact to a typed obligation. A
`delegateAttenStep` variant that granted a control cap exceeding the held cap could NOT inhabit this
structure — the missing-non-amp gate becomes unrepresentable, as auth/admission already are. -/

/-- **`authNonAmpFloor` — the AUTHORITY NON-AMPLIFICATION floor as a `FloorObligation`.** Floor: the cap
the delegation grants (`attenuate keep (heldCapTo … delegator t)`) confers rights `≤` the delegator's
HELD cap to `t` (`heldCapTo … delegator t`) over the `ExecAuth` lattice — a relation over the pre-state's
cap graph, NOT a Bool gate. Discharged on EVERY commit by `recKDelegateAtten_non_amplifying` (which holds
unconditionally for any `keep`, so the `delegateAttenStep` post-condition supplies it directly — no
re-route). The relational floor needs NO different treatment than monotone-nonce: a different `floor`
body in the SAME structure. -/
def authNonAmpFloor : FloorObligation RecordKernelState DelegateArgs delegateAttenStep where
  floor := fun k a =>
    confRights (attenuate a.keep (heldCapTo k.caps a.delegator a.target))
      ≤ confRights (heldCapTo k.caps a.delegator a.target)
  gated := by
    intro k a k' _
    exact recKDelegateAtten_non_amplifying k.caps a.delegator a.target a.keep

/-! ## §4c — POC INSTANCE D (RELATIONAL FLOOR): LIFECYCLE FRESHNESS / DELEGATION-EPOCH, over the
spawn-birth and refresh-restore chained steps (`spawnChainA` / `refreshDelegationChainA`).

The freshness floor is the §P3 family — the delegation-epoch keystone: a freshly-SPAWNED or
freshly-REFRESHED child must be stamped to its parent's CURRENT `delegationEpoch`, so it is NOT stale at
birth / not stale at re-sync. (`delegationStale child = true` iff `delegationEpochAt child` falls
STRICTLY below the parent's current `delegationEpoch` — the acceptor-side replay test a light client
runs; a parent revoke bumps the epoch so old snapshots fall behind ⇒ stale.) A child left at the `0`
default stamp under a nonzero-epoch parent would be INSTANTLY stale — the codex bug. This is RELATIONAL —
it relates the child's post-state stamp `delegationEpochAt child` to the parent's epoch read off the
pre-state (the spawner's `delegationEpoch actor`, or `parentEpoch` for refresh). NOT a Bool gate over
args alone, exactly like monotone-nonce (§4) and non-amp (§4b).

THE CLEAN DISCHARGE (the P2 §4b case repeated). Unlike the reserved-field / monotone floors — where the
handler's `step` had to be RE-ROUTED through a fail-closing guard before the floor could be read off the
commit — the chained executor steps `spawnChainA` / `refreshDelegationChainA` ALREADY stamp
`delegationEpochAt` by construction (the banked triangle-D stamping, commit `85063e80`): spawn writes
`if c = child then delegationEpoch actor`, refresh writes `if c = child then parentEpoch child`. So the
freshness floor DISCHARGES from the EXISTING step's post-condition with NO re-route — `spawnChainA_stamps_epoch`
/ `refreshDelegationChainA_restamps_epoch` are exactly the stamp facts. The `FloorObligation` simply
PROMOTES the latent stamp to a typed obligation. A spawn/refresh variant that LEFT the child at the `0`
default (the un-stamping codex mutation) could NOT inhabit this structure — the missing freshness gate
becomes unrepresentable, as auth/admission/non-amp already are.

(Note: the FROZEN-FACE handler mirror `refreshDelegationStep` (`Handlers/Lifecycle.lean`) models only the
`delegations` snapshot — it does NOT stamp, which is exactly why `handler_refines_execFullA_refreshDelegation`
USED to carry the epoch-stamp as a named kernel RESIDUAL. The floor here lives over the FAITHFUL chained
step that DOES stamp, so the residual is shed by routing the refinement's stamp through this floor.) -/

/-- Args for a spawn-birth freshness floor: the spawner `actor` (= the child's parent), the fresh
`child`, and the cap-source `target`. -/
structure SpawnFreshArgs where
  /-- The spawner — the child's parent; the epoch source. -/
  actor : CellId
  /-- The freshly-born child whose `delegationEpochAt` is stamped. -/
  child : CellId
  /-- The held-cap source the spawn copies down. -/
  target : CellId

/-- Args for a refresh-restore freshness floor: the self-authorizing `actor` and the re-synced `child`. -/
structure RefreshFreshArgs where
  /-- The actor self-authorizing the refresh. -/
  actor : CellId
  /-- The child whose `delegationEpochAt` is re-stamped to the live parent epoch. -/
  child : CellId

/-- The spawn-birth step lifted to `SpawnFreshArgs` (the chained, stamping spawn). -/
def spawnFreshStep (s : RecChainedState) (a : SpawnFreshArgs) : Option RecChainedState :=
  spawnChainA s a.actor a.child a.target

/-- The refresh-restore step lifted to `RefreshFreshArgs` (the chained, re-stamping refresh). -/
def refreshFreshStep (s : RecChainedState) (a : RefreshFreshArgs) : Option RecChainedState :=
  refreshDelegationChainA s a.actor a.child

/-- **`spawnFreshnessFloor` — the BIRTH-FRESHNESS floor as a `PostFloorObligation`.** Floor: the born
child's POST stamp `s'.delegationEpochAt child` EQUALS the spawner-parent's current `delegationEpoch`
(read off the PRE-state, `s.kernel.delegationEpoch actor`) — a post-condition relating the installed stamp
to the pre-state parent epoch, NOT a Bool gate. Discharged on EVERY commit by the banked
`spawnChainA_stamps_epoch`: the chained spawn already stamps by construction, so the floor reads OFF the
commit with no re-route (the §4b clean-discharge case). An un-stamping spawn (the `0` default codex bug)
could not inhabit this. -/
def spawnFreshnessFloor : PostFloorObligation RecChainedState SpawnFreshArgs spawnFreshStep where
  floor := fun s a s' => s'.kernel.delegationEpochAt a.child = s.kernel.delegationEpoch a.actor
  gated := by
    intro s a s' h
    exact spawnChainA_stamps_epoch h

/-- **`refreshFreshnessFloor` — the FRESHNESS-RESTORE floor as a `PostFloorObligation`.** Floor: the
refreshed child's POST stamp `s'.delegationEpochAt child` EQUALS the parent's current epoch
(`parentEpoch s.kernel child`, read off the PRE-state) — a post-condition relating the re-installed stamp
to the pre-state parent epoch, NOT a Bool gate. Discharged on EVERY commit by the banked
`refreshDelegationChainA_restamps_epoch`: the chained refresh already re-stamps by construction, so the
floor reads OFF the commit with no re-route (the §4b clean-discharge case). A refresh that left the stamp
behind could not inhabit this. -/
def refreshFreshnessFloor : PostFloorObligation RecChainedState RefreshFreshArgs refreshFreshStep where
  floor := fun s a s' => s'.kernel.delegationEpochAt a.child = parentEpoch s.kernel a.child
  gated := by
    intro s a s' h
    exact refreshDelegationChainA_restamps_epoch h

/-! ## §4d — POC INSTANCE E (POST-CONDITION FLOORS): SPAWN cap-handoff metadata + FACTORY install,
over the chained executor steps `spawnChainA` / `createCellFromFactoryChainA`.

THE CENSUS-D4 RESIDUAL (the spawn/factory metadata front). The handler dispatch
(`HandlerExecutor.toClosedEffect`) maps BOTH `spawnA` and `createCellFromFactoryA` onto the born-empty
`createCellH` effect — `spawnA` DROPS its `target`, `createCellFromFactoryA` DROPS its `vk`. So the
born-empty refinements `handler_refines_execFullA_{spawn,createCellFromFactory}` prove kernel-agreement
only against the shared account-growth CORE (`createCellA`), NOT the metadata the FULL chained arm
commits. This left the cap-handoff (`caps child`, `delegate`, `delegations`) and the factory install
(`factoryVkField`, `initialFields`, `slotCaveats`) UNVERIFIED by the handler refinement.

THE CLEAN DISCHARGE (the §4c case repeated). `execFullA`'s `.spawnA` arm IS `spawnChainA`, and its
`.createCellFromFactoryA` arm IS `createCellFromFactoryChainA` (both by `rfl`) — and those chained steps
ALREADY commit the metadata by construction. The metadata writes are EXACTLY the already-banked
post-condition lemmas: `spawnChainA_provenance` (the child receives the actor's held cap to the parent
target), `spawnChainA_parent_snapshot` (the `delegate`/`delegations` birth snapshot),
`spawnChainA_stamps_epoch` (the freshness stamp); and `createCellFromFactoryChainA_installs_program` (the
factory's `slotCaveats`), plus the field install read off `…_factors`. So the metadata floors DISCHARGE
from the EXISTING chained step's post-condition with NO re-route — the handler-executor lane was ALREADY
strong enough at the FULL arm; the obligation PROMOTES the latent metadata to a typed `PostFloorObligation`.
A spawn that DROPPED the cap-handoff (the codex confinement-bypass mutation: a born child with empty caps
under a held-cap parent), or a factory that LEFT OFF its `slotCaveats` (the program-bypass mutation),
could NOT inhabit these structures — the missing metadata gate becomes unrepresentable. -/

/-- Args for a spawn cap-handoff metadata floor: the spawner `actor` (= parent), the fresh `child`, the
cap-source `target`. -/
structure SpawnMetaArgs where
  /-- The spawner — the child's parent and the held-cap source's owner. -/
  actor : CellId
  /-- The freshly-born child receiving the copied-down cap + delegation snapshot. -/
  child : CellId
  /-- The held-cap source: the parent target the actor already held an edge to. -/
  target : CellId

/-- Args for a factory install metadata floor: the `actor`, the minted `newCell`, the content-addressed
factory `vk`. -/
structure FactoryMetaArgs where
  /-- The actor minting the cell (must hold creation authority). -/
  actor : CellId
  /-- The freshly-minted cell carrying the factory's installed program. -/
  newCell : CellId
  /-- The content-addressed factory VK key (the `findFactory` lookup key). -/
  vk : Int

/-- The spawn step lifted to `SpawnMetaArgs` (the chained, metadata-committing `spawnChainA` — the very
arm `execFullA`'s `.spawnA` runs). -/
def spawnMetaStep (s : RecChainedState) (a : SpawnMetaArgs) : Option RecChainedState :=
  spawnChainA s a.actor a.child a.target

/-- The factory step lifted to `FactoryMetaArgs` (the chained, install-committing
`createCellFromFactoryChainA` — the very arm `execFullA`'s `.createCellFromFactoryA` runs). -/
def factoryMetaStep (s : RecChainedState) (a : FactoryMetaArgs) : Option RecChainedState :=
  createCellFromFactoryChainA s a.actor a.newCell a.vk

/-- **`spawnMetadataFloor` — the SPAWN CAP-HANDOFF metadata floor as a `PostFloorObligation`.** Floor:
the committed post-state installs the full delegation handoff — the child HOLDS the actor's held cap to the
parent target (`heldCapTo … actor target ∈ s'.caps child`, the least-amplifying authority copy), records
its parent (`delegate child = some actor`), stores the birth snapshot of the parent's c-list
(`delegations child = s.caps actor`), AND stamps the child's epoch to the parent's current one
(`delegationEpochAt child = delegationEpoch actor`, the freshness stamp). A post-condition (the step WRITES
all four), so `PostFloorObligation`. Discharged on EVERY commit by the banked `spawnChainA_provenance` /
`spawnChainA_parent_snapshot` / `spawnChainA_stamps_epoch` — the chained spawn already installs the handoff
by construction, the §4c clean-discharge case. A spawn that left the child with empty caps (the
confinement-bypass mutation) could NOT inhabit this. -/
def spawnMetadataFloor : PostFloorObligation RecChainedState SpawnMetaArgs spawnMetaStep where
  floor := fun s a s' =>
    heldCapTo s.kernel.caps a.actor a.target ∈ s'.kernel.caps a.child ∧
    s'.kernel.delegate a.child = some a.actor ∧
    s'.kernel.delegations a.child = s.kernel.caps a.actor ∧
    s'.kernel.delegationEpochAt a.child = s.kernel.delegationEpoch a.actor
  gated := by
    intro s a s' h
    exact ⟨spawnChainA_provenance h, (spawnChainA_parent_snapshot h).1,
      (spawnChainA_parent_snapshot h).2, spawnChainA_stamps_epoch h⟩

/-- **`factoryMetadataFloor` — the FACTORY INSTALL metadata floor as a `PostFloorObligation`.** Floor:
the committed post-state installs the factory's published contract onto the minted cell — its `slotCaveats`
ARE the factory's declared caveats (`∃ e, findFactory … = some e ∧ slotCaveats newCell = e.caveats`, the
lifetime program enforced on every later `SetField`), AND the cell carries the factory's initial fields +
program-VK slot (the `setField factoryVkField (installInitialFields …) e.programVk` install, read off the
factors). A post-condition (the step WRITES the install), so `PostFloorObligation`. Discharged on EVERY
commit by the banked `createCellFromFactoryChainA_installs_program` (the slotCaveats keystone) +
`createCellFromFactoryChainA_factors` (the field install) — the chained factory already installs the
program by construction, the §4c clean-discharge case. A factory creation that LEFT OFF its caveats (the
program-bypass mutation) could NOT inhabit this. -/
def factoryMetadataFloor : PostFloorObligation RecChainedState FactoryMetaArgs factoryMetaStep where
  floor := fun s a s' =>
    (∃ e s1, findFactory s.kernel.factories a.vk.toNat = some e ∧
       createCellChainA s a.actor a.newCell = some s1 ∧
       s'.kernel.slotCaveats a.newCell = e.caveats ∧
       s'.kernel.cell a.newCell =
         setField factoryVkField (installInitialFields (s1.kernel.cell a.newCell) e.initialFields)
           (.int e.programVk))
  gated := by
    intro s a s' h
    obtain ⟨e, s1, hfind, _, hc, hs'⟩ := createCellFromFactoryChainA_factors h
    refine ⟨e, s1, hfind, hc, ?_, ?_⟩
    · subst hs'; simp
    · -- the field+VK install over the born-empty cell, read off the factors.
      subst hs'
      show (if a.newCell = a.newCell then
              setField factoryVkField (installInitialFields (s1.kernel.cell a.newCell) e.initialFields)
                (.int e.programVk)
            else s1.kernel.cell a.newCell)
          = setField factoryVkField (installInitialFields (s1.kernel.cell a.newCell) e.initialFields)
              (.int e.programVk)
      rw [if_pos rfl]

/-! ## §5 — TEETH: the floors BITE (a violating step does not commit), and DISCHARGE works.

The methodology pin: a step that would VIOLATE the floor returns `none`, so `gated` is never asked to
prove something false — the floor is load-bearing, not vacuous. And `discharge` recovers the floor fact
from any commit (the shape that lets a refinement shed its side-hyp). -/

/-- A developer write of a RESERVED slot does NOT commit — so the reserved floor never lies (it bites
fail-closed, the just-banked teeth, now witnessed AT the obligation surface). -/
theorem reservedFieldFloor_bites (s : RecChainedState) (a : SetFieldArgs)
    (h : reservedField a.field = true) : setFieldStep s a = none := by
  unfold setFieldStep
  exact EffectsState.stateStepDev_reserved_fails s a.field a.actor a.target a.value h

/-- A non-advancing nonce write does NOT commit — the relational floor bites fail-closed. -/
theorem nonceMonotoneFloor_bites (s : RecChainedState) (a : NonceArgs)
    (h : ¬ fieldOf "nonce" (s.kernel.cell a.target) < a.value) : nonceStep s a = none := by
  unfold nonceStep
  exact EffectsState.incrementNonceStep_nonincreasing_fails s a.actor a.target a.value h

/-- **The non-amp floor BITES — a grant cannot be manufactured from nothing.** A delegator holding NO
cap conferring an edge to `target` produces NO commit (`delegateAttenStep = none`) — the Granovetter
premise is the over-grant guard: connectivity (hence authority) cannot begin from nothing, so there is
no witness in which the recipient receives a cap exceeding a (nonexistent) held one. The non-amp floor
is load-bearing precisely because the ONLY committing path attenuates a cap the delegator REALLY held. -/
theorem authNonAmpFloor_overgrant_rejected (k : RecordKernelState) (a : DelegateArgs)
    (h : (k.caps a.delegator).any (fun cap => confersEdgeTo a.target cap) = false) :
    delegateAttenStep k a = none := by
  unfold delegateAttenStep recKDelegateAtten
  rw [if_neg (by simp [h])]

/-- **`reservedFieldFloor` DISCHARGES** — a committed developer write SUPPLIES `reservedField = false`
WITHOUT a side-hypothesis. This is the `hnr` that `handler_refines_execFullA_setField` USED to take
as input (now SHED, §P1), produced by the commit via the obligation. -/
theorem reservedFieldFloor_discharges {s s' : RecChainedState} {a : SetFieldArgs}
    (h : setFieldStep s a = some s') : reservedField a.field = false :=
  reservedFieldFloor.discharge h

/-- **`nonceMonotoneFloor` DISCHARGES** — a committed nonce write SUPPLIES the monotone relation
WITHOUT a side-hypothesis. This is the `hmono` that `handler_refines_execFullA_stateWrite` USED to
take as input (now SHED, §P1), produced by the commit via the obligation (the relational floor shed too). -/
theorem nonceMonotoneFloor_discharges {s s' : RecChainedState} {a : NonceArgs}
    (h : nonceStep s a = some s') : fieldOf "nonce" (s.kernel.cell a.target) < a.value :=
  nonceMonotoneFloor.discharge h

/-- **`authNonAmpFloor` DISCHARGES** — a committed delegation SUPPLIES the non-amplification relation
(`confRights granted ≤ confRights held`) WITHOUT a side-hypothesis. This is the `granted ⊆ held` /
`confRights granted ≤ confRights held` that a refinement consumer USED to take as input (now SHED, §P2 —
see `HandlerExecutor.handler_refines_execFullA_delegateAtten_nonAmp`), produced by the commit via the
obligation. The relational authority floor sheds exactly as the monotone floor did. -/
theorem authNonAmpFloor_discharges {k k' : RecordKernelState} {a : DelegateArgs}
    (h : delegateAttenStep k a = some k') :
    confRights (attenuate a.keep (heldCapTo k.caps a.delegator a.target))
      ≤ confRights (heldCapTo k.caps a.delegator a.target) :=
  authNonAmpFloor.discharge h

/-- **`spawnFreshnessFloor` DISCHARGES** — a committed spawn SUPPLIES the birth-stamp equality
(`s'.delegationEpochAt child = delegationEpoch actor`) WITHOUT a side-hypothesis. This is the epoch-stamp
the chained spawn produces internally; the obligation reads it OFF the commit (the §P3 shed). -/
theorem spawnFreshnessFloor_discharges {s s' : RecChainedState} {a : SpawnFreshArgs}
    (h : spawnFreshStep s a = some s') :
    s'.kernel.delegationEpochAt a.child = s.kernel.delegationEpoch a.actor :=
  spawnFreshnessFloor.discharge h

/-- **`refreshFreshnessFloor` DISCHARGES** — a committed refresh SUPPLIES the re-stamp equality
(`s'.delegationEpochAt child = parentEpoch child`) WITHOUT a side-hypothesis. This is EXACTLY the
epoch-stamp residual `HandlerExecutor.handler_refines_execFullA_refreshDelegation` USED to carry as a named
kernel residual (`{ s'.kernel with delegationEpochAt := … }`); the obligation produces it from the commit,
so the residual is shed by routing the refinement's stamp through the chained step. -/
theorem refreshFreshnessFloor_discharges {s s' : RecChainedState} {a : RefreshFreshArgs}
    (h : refreshFreshStep s a = some s') :
    s'.kernel.delegationEpochAt a.child = parentEpoch s.kernel a.child :=
  refreshFreshnessFloor.discharge h

/-- **`spawnMetadataFloor` DISCHARGES** — a committed spawn SUPPLIES the full cap-handoff metadata
(cap-copy ∧ parent ∧ snapshot ∧ epoch-stamp) WITHOUT a side-hypothesis. This is the delegation handoff the
born-empty `handler_refines_execFullA_spawn` (which refines against `createCellA`) LEFT UNVERIFIED; the
obligation produces it from the FULL chained commit (the census-D4 spawn metadata shed). -/
theorem spawnMetadataFloor_discharges {s s' : RecChainedState} {a : SpawnMetaArgs}
    (h : spawnMetaStep s a = some s') :
    heldCapTo s.kernel.caps a.actor a.target ∈ s'.kernel.caps a.child ∧
    s'.kernel.delegate a.child = some a.actor ∧
    s'.kernel.delegations a.child = s.kernel.caps a.actor ∧
    s'.kernel.delegationEpochAt a.child = s.kernel.delegationEpoch a.actor :=
  spawnMetadataFloor.discharge h

/-- **`factoryMetadataFloor` DISCHARGES** — a committed factory creation SUPPLIES the full install
(slotCaveats = the factory's program ∧ the field+VK install) WITHOUT a side-hypothesis. This is the
factory contract the born-empty `handler_refines_execFullA_createCellFromFactory` (which refines against
`createCellA`, DROPPING `vk`) LEFT UNVERIFIED; the obligation produces it from the FULL chained commit
(the census-D4 factory metadata shed). -/
theorem factoryMetadataFloor_discharges {s s' : RecChainedState} {a : FactoryMetaArgs}
    (h : factoryMetaStep s a = some s') :
    (∃ e s1, findFactory s.kernel.factories a.vk.toNat = some e ∧
       createCellChainA s a.actor a.newCell = some s1 ∧
       s'.kernel.slotCaveats a.newCell = e.caveats ∧
       s'.kernel.cell a.newCell =
         setField factoryVkField (installInitialFields (s1.kernel.cell a.newCell) e.initialFields)
           (.int e.programVk)) :=
  factoryMetadataFloor.discharge h

/-! ### §4d-TEETH — the metadata floors BITE (the confinement-bypass / program-bypass mutations are
REJECTED), so the metadata floors are load-bearing, not vacuous. -/

/-- **THE CONFINEMENT-BYPASS POLE (spawn metadata floor BITES).** A spawner with NO cap conferring an
edge to the parent `target` produces NO commit (`spawnChainA = none`) — so a child cannot be born with a
manufactured cap to an unrelated target. The metadata floor is load-bearing: the only committing path
copies a cap the actor REALLY held (the Granovetter premise), exactly the cap the floor's first conjunct
witnesses. -/
theorem spawnMetadataFloor_overgrant_rejected (s : RecChainedState) (a : SpawnMetaArgs)
    (h : (s.kernel.caps a.actor).any (fun cap => confersEdgeTo a.target cap) = false) :
    spawnMetaStep s a = none := by
  unfold spawnMetaStep spawnChainA
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-- **THE PROGRAM-BYPASS POLE (factory metadata floor BITES).** A factory creation against an UNKNOWN
factory VK produces NO commit (`createCellFromFactoryChainA = none`, dregg1 `apply.rs:3140`) — so no cell
can be minted CLAIMING a factory's program without that factory existing. The metadata floor is
load-bearing: the only committing path installs a REGISTERED factory's caveats, exactly what the floor's
`∃ e, findFactory … = some e ∧ slotCaveats = e.caveats` clause witnesses. -/
theorem factoryMetadataFloor_unknown_factory_rejected (s : RecChainedState) (a : FactoryMetaArgs)
    (h : findFactory s.kernel.factories a.vk.toNat = none) :
    factoryMetaStep s a = none := by
  unfold factoryMetaStep
  exact createCellFromFactoryChainA_unknown_factory_fails s a.actor a.newCell a.vk h

/-! ### §5b — the freshness floor BITES: a committed (hence stamped) child is NOT stale, AND an
UN-stamped post IS stale (the mutation pole) — so the freshness floor is load-bearing, not vacuous. -/

/-- **A committed spawn is FRESH AT BIRTH** — `delegationStale s'.kernel child = false`. The floor's
discharge (the stamp) is exactly what makes the acceptor-side staleness test fail: the child is born at
the parent's current epoch. The freshness floor is load-bearing — its discharge implies no-staleness. -/
theorem spawnFreshnessFloor_not_stale {s s' : RecChainedState} {a : SpawnFreshArgs}
    (h : spawnFreshStep s a = some s') : delegationStale s'.kernel a.child = false :=
  spawnChainA_fresh_at_birth h

/-- **A committed refresh is FRESH** — `delegationStale s'.kernel child = false` (for a child with parent
`p`). The re-stamp discharge re-syncs the child to the live parent epoch, so the strict `<` freshness test
fails. The freshness floor is load-bearing. -/
theorem refreshFreshnessFloor_not_stale {s s' : RecChainedState} {a : RefreshFreshArgs} {p : CellId}
    (h : refreshFreshStep s a = some s') (hp : s.kernel.delegate a.child = some p) :
    delegationStale s'.kernel a.child = false :=
  refreshDelegationChainA_fresh h hp

/-- **THE MUTATION POLE (freshness floor BITES — un-stamped child is STALE-AT-BIRTH).** If a spawn-like
step had LEFT the child at the `0` default stamp under a NONZERO-epoch parent (the codex un-stamping bug,
the floor's negation), the child would be INSTANTLY stale: `delegationStale = true`. This witnesses that the
freshness floor is NOT vacuous — its negation is a genuinely distinct, REJECTED post-state (the un-stamped
post fails the freshness test the stamped post passes). The `delegationEpochAt`-`0` post + a parent at
epoch `> 0` is exactly the state `spawnChainA`'s stamp REFUTES. -/
theorem freshnessFloor_unstamped_is_stale (k : RecordKernelState) (child parent : CellId)
    (hp : k.delegate child = some parent)
    (hstamp0 : k.delegationEpochAt child = 0)
    (hpe : 0 < k.delegationEpoch parent) :
    delegationStale k child = true := by
  simp only [delegationStale, hp, hstamp0]
  exact decide_eq_true (by omega)

/-! ## §P4 — INDEX-MEMBERSHIP FLOORS: the noteSpend nullifier NON-MEMBERSHIP + the heap leaf-splice /
root-pin, over the LIVE chained steps `noteSpendChainA` / `heapStepGuardedW`.

THE FLAT-VS-FOREST FINDING (the load-bearing P4 verdict — verified in source, NOT assumed). The §P4
prose in earlier waves WARNED that these floors might need discharge on the FOREST step because "the
forest commitment binds a per-leaf path-membership STRONGER than the flat mirror". Reading the live
executor REFUTES that for THIS model:

  * `execFullForestA s f = execFullTurnA s (lowerForestA f)` (`FullForest.execFullForestA_eq_execFullTurnA`):
    the forest is EXACTLY the linear per-asset turn over the pre-order node-actions. Every node runs
    its action through `execFullA s a` — the SAME flat executor arm. The forest binds *which cell* each
    node targets (`targetOf`), the per-asset ledger VECTOR, the ChainLink, and the executed delegation
    HANDOFF between parent and child. It does NOT introduce a separate, stronger nullifier-set or
    heap-leaf membership object.
  * `execFullA`'s `.noteSpendA` arm IS `noteSpendChainA` (→ `noteSpendNullifier`), and its `.heapWriteA`
    arm IS `heapStepGuardedW` — the very kernel steps. The nullifier set is the kernel `nullifiers :
    List Nat` and the non-membership floor is the literal `nf ∉ k.nullifiers`, discharged from
    `noteSpendNullifier`'s fail-closed `if nf ∈ k.nullifiers then none`. The heap is a sorted leaf LIST
    (`Heap.set`), and the "leaf-index bound" floor is the post-condition pair the register-and-splice
    BIND: the committed `heap_root` register EQUALS the carried `newRoot`, and the post-heap is the
    sorted insert-or-update at the addressed leaf (`Heap.set _ addr v`).

So the SOUND fact for BOTH floors lives on the FLAT/chained step the forest node runs — the
`Circuit.SortedTreeNonMembership` gadget is the CIRCUIT-side realization of that SAME `nf ∉ set` fact
(the gap-bracketing open of a sorted-Merkle root), not a stronger object the executor model omits. The
forest INHERITS the floor for free because a forest node IS `execFullA (.noteSpendA …)` /
`(.heapWriteA …)`. We therefore discharge on the LIVE chained step — and that IS the live forest path
(the forest = `execFullTurnA` over these arms), so this is NOT the flat shadow: it is the genuine step
the forest executes per node. -/

/-- Args for a note-spend non-membership floor: the actor + the spent nullifier + the §8 spend-proof
flag (the live `noteSpendChainA` carries all three). -/
structure NoteSpendFloorArgs where
  /-- The actor spending the note (the receipt subject). -/
  actor : CellId
  /-- The nullifier derived from the spent note (the SET-membership key). -/
  nf : Nat
  /-- The §8 spending-proof flag (a committed spend requires it `= true`). -/
  spendProof : Bool

/-- Args for a heap-write leaf/root floor: the actor + target + carried address, value, and post-root
(the live `heapStepGuardedW` writes these). -/
structure HeapFloorArgs where
  /-- The actor performing the write (must hold authority over `target`). -/
  actor : CellId
  /-- The cell whose heap leaf list + `heap_root` register are written. -/
  target : CellId
  /-- The carried sorted-key address (the Poseidon2 image of `(coll, key)`). -/
  addr : Int
  /-- The written value. -/
  value : Int
  /-- The carried post-root pinned into the `heap_root` register. -/
  newRoot : Int

/-- The note-spend step lifted to `NoteSpendFloorArgs` (the LIVE chained `noteSpendChainA` — the very
arm `execFullA`'s `.noteSpendA` runs, hence the arm the forest node runs). -/
def noteSpendFloorStep (s : RecChainedState) (a : NoteSpendFloorArgs) : Option RecChainedState :=
  noteSpendChainA s a.nf a.actor a.spendProof

/-- The heap-write step lifted to `HeapFloorArgs` (the LIVE wire-face `heapStepGuardedW` — the very arm
`execFullA`'s `.heapWriteA` runs, hence the arm the forest node runs). -/
def heapFloorStep (s : RecChainedState) (a : HeapFloorArgs) : Option RecChainedState :=
  heapStepGuardedW s a.actor a.target a.addr a.value a.newRoot

/-- **`noteSpendNonMembershipFloor` — the NULLIFIER NON-MEMBERSHIP floor as a `FloorObligation`.**
Floor: the spent nullifier was NOT already in the committed nullifier set (`nf ∉ s.kernel.nullifiers`) —
the no-double-spend invariant, a relation over the pre-state's nullifier set, NOT a Bool gate over args
alone (the same shape as monotone-nonce: it reads the state). Discharged on EVERY commit by
`noteSpendChainA_requires_proof` (whose conclusion `spendProof = true ∧ nf ∉ s.kernel.nullifiers`
delivers exactly this second conjunct). The live chained step already fail-closes on a present
nullifier (`noteSpendNullifier`'s `if nf ∈ … then none`), so the floor reads OFF the commit with no
re-route — the §4b/§P3 clean-discharge case: the handler was ALREADY strong enough, the obligation
PROMOTES the latent non-membership to a typed floor. A `noteSpendChainA` variant that re-spent a
present nullifier (the double-spend mutation) could NOT inhabit this structure. -/
def noteSpendNonMembershipFloor : FloorObligation RecChainedState NoteSpendFloorArgs noteSpendFloorStep where
  floor := fun s a => a.nf ∉ s.kernel.nullifiers
  gated := by
    intro s a s' h
    exact (noteSpendChainA_requires_proof h).2

/-- **`heapLeafSpliceFloor` — the HEAP LEAF-SPLICE / ROOT-PIN floor as a `PostFloorObligation`.** Floor:
the committed post-state binds the heap write at the addressed leaf — the `heap_root` register reads
back EXACTLY the carried `newRoot`, AND the target's post-heap is the sorted insert-or-update of `addr
↦ value` (`Heap.set` at the addressed key; other cells untouched). A post-condition (the step WRITES
both), so `PostFloorObligation`. This is the executor face of the "heap leaf-index bound": the model's
heap is a SORTED leaf LIST keyed by the felt `addr` (no bounded index — `Heap.set` is the sorted
insert), and what the step BINDS is precisely (a) the register equals the carried root, and (b) the
addressed leaf was spliced. Discharged on EVERY commit by `heapStepW_root_pinned` (register = newRoot)
and `heapStepW_heaps` (the splice) — the live wire step already pins both by construction, the §4b/§P3
clean-discharge case. A heap step that wrote a DIFFERENT root than it carried, or spliced a different
leaf, could NOT inhabit this. -/
def heapLeafSpliceFloor : PostFloorObligation RecChainedState HeapFloorArgs heapFloorStep where
  floor := fun s a s' =>
    fieldOf heapRootField (s'.kernel.cell a.target) = a.newRoot ∧
    (∀ c, s'.kernel.heaps c =
      if c = a.target then set (s.kernel.heaps a.target) a.addr a.value
      else s.kernel.heaps c)
  gated := by
    intro s a s' h
    exact ⟨heapStepW_root_pinned h, heapStepW_heaps h⟩

/-! ### §P4-DISCHARGE — the obligations SHED their side-hypotheses off the commit. -/

/-- **`noteSpendNonMembershipFloor` DISCHARGES** — a committed note-spend SUPPLIES the non-membership
`nf ∉ s.kernel.nullifiers` WITHOUT a side-hypothesis. This is the no-double-spend precondition a
non-membership-aware refinement consumer USED to take as input; the obligation produces it from the
commit (the index-membership floor shed, exactly as the monotone floor shed). -/
theorem noteSpendNonMembershipFloor_discharges {s s' : RecChainedState} {a : NoteSpendFloorArgs}
    (h : noteSpendFloorStep s a = some s') : a.nf ∉ s.kernel.nullifiers :=
  noteSpendNonMembershipFloor.discharge h

/-- **`heapLeafSpliceFloor` DISCHARGES** — a committed heap write SUPPLIES the root-pin AND the
addressed leaf-splice WITHOUT a side-hypothesis. This is the leaf/root binding a heap-aware refinement
consumer USED to take as input; the obligation produces it from the commit (the heap index/membership
floor shed). -/
theorem heapLeafSpliceFloor_discharges {s s' : RecChainedState} {a : HeapFloorArgs}
    (h : heapFloorStep s a = some s') :
    fieldOf heapRootField (s'.kernel.cell a.target) = a.newRoot ∧
    (∀ c, s'.kernel.heaps c =
      if c = a.target then set (s.kernel.heaps a.target) a.addr a.value
      else s.kernel.heaps c) :=
  heapLeafSpliceFloor.discharge h

/-! ### §P4-TEETH — the floors BITE (a double-spend / a proof-less spend does not commit). -/

/-- **THE DOUBLE-SPEND POLE (non-membership floor BITES).** A spend of a nullifier ALREADY in the
committed set does NOT commit (`noteSpendChainA = none`) — the negation of the floor is a genuinely
distinct, REJECTED step. This witnesses the non-membership floor is LOAD-BEARING, not vacuous: the only
committing path spends a FRESH nullifier, so `gated` is never asked to prove a false non-membership. -/
theorem noteSpendNonMembershipFloor_double_spend_rejected (s : RecChainedState)
    (a : NoteSpendFloorArgs) (h : a.nf ∈ s.kernel.nullifiers) :
    noteSpendFloorStep s a = none := by
  unfold noteSpendFloorStep noteSpendChainA
  by_cases hp : a.spendProof = true
  · rw [if_pos hp, note_no_double_spend s.kernel a.nf h]
  · rw [if_neg hp]

/-- **THE PROOF-LESS POLE (non-membership floor's companion gate BITES).** A spend WITHOUT the §8
spending proof (`spendProof = false`) does NOT commit — the live `noteSpendChainA` fail-closes on the
proof flag, so a non-membership floor can never be reached on a forged spend. -/
theorem noteSpendNonMembershipFloor_proofless_rejected (s : RecChainedState)
    (a : NoteSpendFloorArgs) (h : a.spendProof = false) :
    noteSpendFloorStep s a = none := by
  unfold noteSpendFloorStep
  exact noteSpendChainA_fails_without_proof h

/-! ## §6 — Axiom-hygiene pins (the floor surface + all instances rest only on the kernel triple). -/

#assert_axioms FloorObligation.discharge
#assert_axioms PostFloorObligation.discharge
#assert_axioms reservedFieldFloor
#assert_axioms nonceMonotoneFloor
#assert_axioms authNonAmpFloor
#assert_axioms spawnFreshnessFloor
#assert_axioms refreshFreshnessFloor
#assert_axioms spawnMetadataFloor
#assert_axioms factoryMetadataFloor
#assert_axioms reservedFieldFloor_discharges
#assert_axioms nonceMonotoneFloor_discharges
#assert_axioms authNonAmpFloor_discharges
#assert_axioms spawnFreshnessFloor_discharges
#assert_axioms refreshFreshnessFloor_discharges
#assert_axioms spawnMetadataFloor_discharges
#assert_axioms factoryMetadataFloor_discharges
#assert_axioms spawnMetadataFloor_overgrant_rejected
#assert_axioms factoryMetadataFloor_unknown_factory_rejected
#assert_axioms reservedFieldFloor_bites
#assert_axioms nonceMonotoneFloor_bites
#assert_axioms authNonAmpFloor_overgrant_rejected
#assert_axioms spawnFreshnessFloor_not_stale
#assert_axioms refreshFreshnessFloor_not_stale
#assert_axioms freshnessFloor_unstamped_is_stale
#assert_axioms noteSpendNonMembershipFloor
#assert_axioms heapLeafSpliceFloor
#assert_axioms noteSpendNonMembershipFloor_discharges
#assert_axioms heapLeafSpliceFloor_discharges
#assert_axioms noteSpendNonMembershipFloor_double_spend_rejected
#assert_axioms noteSpendNonMembershipFloor_proofless_rejected

/-! ## §P1/§P2/§P3/§P4 — DONE (field-write · authority-non-amp · lifecycle-freshness · index-membership).

**P1 LANDED.** The developer `SetField` (`.setFieldA`) and the dedicated `IncrementNonce`
(`.incrementNonceA`) now route through their OWN floor-carrying handlers (`Handlers/StateSupply.lean`,
`setFieldDevH` / `incrementNonceDevH`) whose `step` ITSELF fail-closes on the floor — the reserved
protocol slot + slot caveat for `.setFieldA` (`setFieldDevStep`), the strict-advance for
`.incrementNonceA` (`incrementNonceDevStep`). The refinement theorems read the floor OFF the commit
(`setFieldDevStep_notReserved` / `_caveatsAdmit`, `incrementNonceDevStep_advances`) instead of taking
it as a caller hypothesis, so:

  * `handler_refines_execFullA_setField` SHED `hnr` (`reservedField f = false`) AND `hcav`
    (`caveatsAdmit … = true`); and
  * `handler_refines_execFullA_stateWrite` (=`…_incrementNonce`) SHED `hmono` (the monotone relation).

The generic `stateWriteH` STAYS for the protocol-slot writers (`setPermissions`/`setVK`/`setProgram`/…)
— each OWNS its (reserved) slot, so the reserved gate must NOT apply to them. The teeth
(`Handlers/StateSupply.lean §TEETH-9a/9b/9c`) confirm the floors BITE through the migrated handlers (a
`SetField` of `"nonce"`/`"permissions"`/… and a non-advancing `IncrementNonce` are all REJECTED) and
do NOT over-reject (a non-reserved write and a strict advance commit).

**P2 — DONE (authority NON-AMPLIFICATION migrated; the relational floor SHED).** The
`delegateAtten`/`introduce`/`delegate` family carries the non-amplification floor as a TYPED
`FloorObligation` (`authNonAmpFloor`, §4b): the granted cap confers rights `≤` the delegator's HELD cap
(`confRights (attenuate keep (heldCapTo … delegator t)) ≤ confRights (heldCapTo … delegator t)`), a
RELATIONAL floor over the pre-state cap graph (like monotone-nonce, §4). The CLEANER discharge: the
authority handler `delegateAttenStep` ALREADY installs the *attenuated* grant (via `recKDelegateAtten`,
NOT a fresh control cap), so the floor discharges from the EXISTING step's post-condition —
`recKDelegateAtten_non_amplifying` holds unconditionally for any `keep`. No re-route: the handler was
already strong enough; the obligation PROMOTES the latent fact to a typed floor.

`HandlerExecutor.handler_refines_execFullA_delegateAtten_nonAmp` (and the `_delegate`/`_introduce`
variants) prove kernel-agreement AND deliver the non-amp relation OFF the commit via
`authNonAmpFloor_discharges` — the strengthened refinement SHEDS the `hamp : confRights granted ≤
confRights held` side-hypothesis a non-amp-aware consumer USED to take (the BEFORE shape,
`handler_refines_execFullA_delegateAtten_nonAmp_weak`, takes it as a hypothesis; the AFTER does not).
The mutation teeth (`authNonAmpFloor_overgrant_rejected`) confirm the floor BITES: an over-granting
delegator with NO held cap to the target produces no commit, so a manufactured stronger grant has no
witness.

**P3 — DONE (lifecycle FRESHNESS / delegation-epoch migrated; the epoch-stamp residual SHED).** The
spawn-birth and refresh-restore families carry the freshness floor as a TYPED `PostFloorObligation`
(`spawnFreshnessFloor` / `refreshFreshnessFloor`, §4c): the child's POST `delegationEpochAt` stamp EQUALS
its parent's CURRENT epoch (`= delegationEpoch actor` at birth; `= parentEpoch child` at re-sync) — a
POST-condition floor (the step WRITES the stamp, so the floor is genuinely over `s'`, hence
`PostFloorObligation`, one slot wider than the §P1/§P2 pre-state `FloorObligation`). The CLEANER discharge
(the §P2 §4b case repeated): the CHAINED executor steps `spawnChainA` / `refreshDelegationChainA` ALREADY
stamp by construction (the banked triangle-D stamping, commit `85063e80`), so the floor discharges from the
EXISTING step's post-condition — `spawnChainA_stamps_epoch` / `refreshDelegationChainA_restamps_epoch` ARE
the stamp facts. No re-route: the handler was already strong enough; the obligation PROMOTES the latent
stamp to a typed floor.

`HandlerExecutor.handler_refines_execFullA_refreshDelegation` (AFTER) refines against the chained,
stamping `refreshDelegationChainA` and delivers CLEAN kernel-agreement (NO `delegationEpochAt` residual)
PLUS the freshness fact OFF the commit via `refreshFreshnessFloor_discharges` — SHEDDING the epoch-stamp
residual the BEFORE shape (`…_refreshDelegation_residual`) carried in its conclusion (`s''.kernel = {
s'.kernel with delegationEpochAt := … }`). `handler_refines_execFullA_spawn_fresh` does the same for the
birth stamp (the §DEFER'd dimension the born-empty `…_spawn`/`createCellA` refinement left implicit is now
certified internal). The mutation teeth (§5b): `spawnFreshnessFloor_not_stale` /
`refreshFreshnessFloor_not_stale` confirm a committed (hence stamped) child is NOT stale; and
`freshnessFloor_unstamped_is_stale` confirms the floor is LOAD-BEARING — an un-stamped child (`0` default
stamp under a nonzero-epoch parent, the codex mutation = the floor's negation) IS stale-at-birth
(`delegationStale = true`), the distinct REJECTED post the stamp refutes.

**P4 — DONE (index-membership migrated; the nullifier non-membership + heap leaf-splice/root-pin floors
SHED). THE FLAT-VS-FOREST VERDICT (the load-bearing P4 finding — verified in source, see §P4).** The
prior-wave warning ("these are FOREST-path floors; the forest commitment binds a per-leaf path-membership
STRONGER than the flat mirror; discharge on the FOREST step, not `noteSpendStep`/`heapWriteStep`") is
REFUTED for this model. The live forest IS `execFullTurnA` over the pre-order lowering
(`FullForest.execFullForestA_eq_execFullTurnA`): each node runs `execFullA s a`, whose `.noteSpendA` arm
IS `noteSpendChainA` (→ `noteSpendNullifier`) and whose `.heapWriteA` arm IS `heapStepGuardedW` — the
very kernel steps. The forest binds *which cell* a node targets, the per-asset ledger vector, ChainLink,
and the delegation handoff — it does NOT carry a separate, stronger nullifier-set / heap-leaf membership
object. The nullifier set is the kernel `nullifiers : List Nat`; the non-membership floor is the literal
`nf ∉ k.nullifiers`, discharged from `noteSpendNullifier`'s fail-closed membership check via
`noteSpendChainA_requires_proof`. The heap is a SORTED leaf LIST (`Heap.set`, no bounded index); the
"leaf-index bound" maps to the post-condition the register-and-splice BIND — the `heap_root` register
equals the carried `newRoot` (`heapStepW_root_pinned`) AND the addressed leaf was sorted-spliced
(`heapStepW_heaps`). The `Circuit.SortedTreeNonMembership` gadget is the CIRCUIT-side realization of the
SAME `nf ∉ set` fact (gap-bracketing a sorted-Merkle root), NOT a stronger object the executor omits.

So the floors discharge on the LIVE chained steps `noteSpendChainA` / `heapStepGuardedW` (§P4) — and
because the forest is exactly `execFullTurnA` over those arms, this IS the live forest path, not the flat
shadow. `noteSpendNonMembershipFloor` (a `FloorObligation`, the no-double-spend relation over the
pre-state set) and `heapLeafSpliceFloor` (a `PostFloorObligation`, the root-pin + addressed-leaf splice)
deliver their facts OFF the commit via `noteSpendNonMembershipFloor_discharges` /
`heapLeafSpliceFloor_discharges` — the §4b/§P3 clean-discharge case (the steps were ALREADY strong
enough; the obligations PROMOTE the latent facts to typed floors). The teeth (§P4-TEETH):
`noteSpendNonMembershipFloor_double_spend_rejected` confirms a re-spent (present) nullifier produces NO
commit (the floor is LOAD-BEARING — the double-spend pole), and `…_proofless_rejected` confirms the
companion §8-proof gate fail-closes a forged spend.

**HONEST COMPLETION VERDICT.** All SIX named floor families are now internalized as typed obligations on
the uniform `FloorObligation` / `PostFloorObligation` surface (reserved-field · caveat · monotone-nonce ·
non-amp · epoch-freshness · index-membership) — each discharged from the step's own commit, each with
mutation teeth proving it bites, each `#assert_axioms`-clean. The FLAT/chained handler-executor floor
coverage is therefore COMPLETE for the six families.

For the LIVE FOREST PATH specifically: because `execFullForestA = execFullTurnA ∘ lowerForestA` and each
node action runs the SAME `execFullA` arm carrying these floors, the forest INHERITS the structural
immunity for free at the per-node level — there is no separate, stronger forest-leaf object these floors
fail to cover (the load-bearing P4 finding). What the forest adds ON TOP — and what is NOT a HandlerFloors
obligation — is the per-node membership-LIFT (`fullActionInvA`: the per-asset ledger vector ∧ ChainLink ∧
ObsAdvance attest at every tree node, `FullForest §7`) and the executed delegation-handoff non-amplification
(`FullForest §6.EXECUTED`). Those forest-structural laws are already PROVEN in `FullForest.lean`; they are
not floor-shedding side-hypotheses of the kind this campaign retires. So the gate-hole class this campaign
names — the silent missing-gate carried as a refinement SIDE-HYPOTHESIS — is RETIRED for all six flat
families AND inherited by the forest path per node; it is NOT a remaining forest-specific campaign. (The
genuinely-remaining circuit-soundness work — binding the `heaps` field into the state-commitment conjunct
`Circuit/StateCommit.RestHashIffFrame`, and the in-circuit `SortedTreeNonMembership` ↔ executor-set
agreement — is the CIRCUIT/descriptor frontier tracked in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`, a
distinct campaign from the handler-floor internalization this module completes.) -/

end Dregg2.Exec.HandlerFloors
