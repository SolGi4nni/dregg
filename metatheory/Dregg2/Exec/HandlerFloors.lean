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
  refreshDelegationChainA_restamps_epoch refreshDelegationChainA_fresh
  refreshDelegationChainA_noParent_rejects)
open Dregg2.Exec (delegationStale)

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

/-! ## §6 — Axiom-hygiene pins (the floor surface + all instances rest only on the kernel triple). -/

#assert_axioms FloorObligation.discharge
#assert_axioms PostFloorObligation.discharge
#assert_axioms reservedFieldFloor
#assert_axioms nonceMonotoneFloor
#assert_axioms authNonAmpFloor
#assert_axioms spawnFreshnessFloor
#assert_axioms refreshFreshnessFloor
#assert_axioms reservedFieldFloor_discharges
#assert_axioms nonceMonotoneFloor_discharges
#assert_axioms authNonAmpFloor_discharges
#assert_axioms spawnFreshnessFloor_discharges
#assert_axioms refreshFreshnessFloor_discharges
#assert_axioms reservedFieldFloor_bites
#assert_axioms nonceMonotoneFloor_bites
#assert_axioms authNonAmpFloor_overgrant_rejected
#assert_axioms spawnFreshnessFloor_not_stale
#assert_axioms refreshFreshnessFloor_not_stale
#assert_axioms freshnessFloor_unstamped_is_stale

/-! ## §P1/§P2/§P3 — DONE (field-write · authority-non-amp · lifecycle-freshness migrated). §P4 — NEXT.

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

**P4 — the next floor family: forest-path / index-membership** (the obligation table,
`docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`): the `noteSpend`/heap-membership floors — the spend's nullifier
NON-MEMBERSHIP (no double-spend) + the heap leaf-INDEX bound. ⚑ NOTE: unlike the §P1–§P3 floors (which
live over FLAT kernel/chained steps), these are FOREST-path floors — the LIVE executor routes spend +
heap-write through the FOREST handler (`FullForest` / the forest fold), so the membership/index floors must
be discharged on the FOREST step (the per-leaf path-membership the forest commitment binds), NOT the flat
`noteSpendStep`/`heapWriteStep` handler mirror. So P4 likely needs the forest-handler refinement, not the
flat-handler one — flag this before defining the floor (the flat mirror would discharge a WEAKER fact than
the forest commitment actually binds). -/

end Dregg2.Exec.HandlerFloors
