/-
# Dregg2.Apps.NameserviceGated — the nameservice as a VERIFIED USERSPACE APP on the ONE GATED executor.

`Dregg2.Apps.NameService` modelled dregg1's nameservice on the **credential-BLIND** per-asset executor
(`execFullForestA`) and anchored permanence in the grow-only `commitments` set. That is the registry
DISCIPLINE, but it never runs the production turn entry: the WHO (credential), the cap-authority, and
the per-slot WriteOnce/Monotonic CAVEATS the kernel checks on every `SetField`.

This module re-models the SAME nameservice through the ONE production turn entry —
`Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate:
credential ∧ cap-authority ∧ caveats-discharged ∧ not-revoked) — at the Demo carriers, so the
end-user theorems are about the EXECUTED, credential-gated, caveat-enforcing turn.

## The real ops (`starbridge-apps/nameservice/src/lib.rs`)

Each op is a single `SetField` on the registry cell, modelled as a GATED leaf node
`⟨ mkAuth cred [], .setFieldA actor cell field value, [] ⟩` run through `execFullForestG`:

  * **register**   — `SetField NAME_HASH` / `OWNER_HASH` / `EXPIRY` (anchors the binding);
  * **renew**      — `SetField EXPIRY` (extends the lease — `Monotonic`, can only grow);
  * **transfer**   — `SetField OWNER_HASH` (changes ownership);
  * **revoke**     — `SetField REVOKED` (writes the tombstone — `WriteOnce`, one-way);
  * **set-target** — `SetField RESOLVE_TARGET` (the resolve pointer).

## The registry cell's SLOT CAVEATS (the executor-enforced app invariants)

The registry cell carries (`s.kernel.slotCaveats registryCell`):
  * `WriteOnce NAME`     — the name binding, once set (≠0), can never be silently overwritten → **no name-squat**;
  * `Monotonic EXPIRY`   — the lease can only grow → **renew cannot SHORTEN rent**;
  * `WriteOnce REVOKED`  — the tombstone, once set, can never be lifted → **revocation is permanent**.

`stateStepGuarded` (the `setFieldA` arm of `execFullA`) reads exactly these and FAILS CLOSED on a
violating write — so the app invariants are enforced BY THE EXECUTOR, not merely carried.

## End-user theorems (general where possible; concrete `#guard` witnesses for non-vacuity)

  1. `ns_forged_credential_rejected` — a forged credential ⇒ the whole gated turn rejects (`none`);
  2. `ns_name_squat_impossible`      — a register over an already-set name slot ⇒ `none`;
  3. `ns_rent_cannot_shorten`        — a renew with `new < old` expiry ⇒ `none`;
  4. `ns_revoke_permanent`           — a second revoke (tombstone already set) ⇒ `none`;
  5. `ns_register_conserves`         — a committed register turn moves NO asset's supply (per-asset Δ = 0).

Plus a concrete registry-cell state (`reg0`) whose `#guard`s show a GOOD register COMMITS, a forged
credential gives `none`, and a squat gives `none` (the gate + the caveat are REAL, not vacuous).

Does NOT touch `NameService.lean`, `FullForestAuth.lean`,
nor `Dregg2.lean`. Reuses ONLY the proved gated-executor keystones + the proved `stateStepGuarded`
fail-closed teeth.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.NameserviceGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The nameservice DOMAIN at the Demo carriers (names, owners, the registry cell, the slots). -/

/-- The registry cell holding the name records (dregg1's `registry_cell`). We use cell `0` so the actor
can be `0` too — `stateAuthB` is then trivially satisfied (`actor == src`), letting the credential-gate
and the SLOT CAVEAT be the load-bearing admission conditions (not the cap-list). -/
abbrev registryCell : CellId := 0

/-- The registry actor (the owner key publishing records). Equal to `registryCell` so `stateAuthB`
holds by `actor == src` — the app's authority story rides on the §8 CREDENTIAL gate, not the c-list. -/
abbrev registryActor : CellId := 0

/-- The `NAME_HASH` slot (dregg1 `NAME_HASH_SLOT`) — `WriteOnce`: once a name is bound it is permanent. -/
abbrev nameSlot : FieldName := "name"
/-- The `OWNER_HASH` slot (dregg1 `OWNER_HASH_SLOT`) — transfer rewrites this (no caveat: ownership moves). -/
abbrev ownerSlot : FieldName := "owner"
/-- The `EXPIRY` slot (dregg1 `EXPIRY_SLOT`) — `Monotonic`: a renew can only EXTEND the lease, never shorten. -/
abbrev expirySlot : FieldName := "expiry"
/-- The `REVOKED` slot (dregg1 `REVOKED_SLOT`) — `WriteOnce`: a tombstone is one-way (permanent revocation). -/
abbrev revokedSlot : FieldName := "revoked"
/-- The `RESOLVE_TARGET` slot (dregg1 `RESOLVE_TARGET_SLOT`) — the resolve pointer (no caveat: free to update). -/
abbrev targetSlot : FieldName := "target"

/-- The registry cell's factory-installed SLOT CAVEATS — exactly the dregg1 nameservice program:
`WriteOnce { name }`, `Monotonic { expiry }`, `WriteOnce { revoked }`. The executor reads these on
EVERY `SetField` to the registry cell (`stateStepGuarded`). -/
def registryCaveats : List SlotCaveat :=
  [ .writeOnce nameSlot, .monotonic expirySlot, .writeOnce revokedSlot ]

/-! ## §2 — Each op as a GATED LEAF NODE through the production turn entry `execFullForestG`.

A nameservice op is a single `SetField` on the registry cell, decorated with a credential (the WHO)
and run through the 4-leg gate. `mkAuth cred []` (from `FullForestAuth.Demo`) supplies an admitting
cap-mode (`.unchecked (Guard.all [])`), an empty within-cell caveat list (so the GATE's caveat leg is
vacuously discharged — the SLOT caveats are enforced separately by `stateStepGuarded` inside
`execFullA`), no chain, and a non-revoked nullifier. So `gateOK` reduces to the CREDENTIAL leg. -/

/-- A gated nameservice node: credential `cred`, a `SetField slot value` on the registry cell, no
children. The production-entry shape `⟨ mkAuth cred [], action, [] ⟩`. -/
def nsNode (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA registryActor registryCell slot value, [] ⟩

/-- **register** — bind the name (the load-bearing `SetField NAME_HASH`; dregg1 also writes owner+expiry,
modelled by the sibling nodes). A genuine credential ⇒ the gate passes; the `WriteOnce name` slot caveat
then permits the FIRST write (`old = 0`) and forbids any later overwrite. -/
def registerNode (cred : Authorization Dg Pf) (nameVal : Int) : DForest :=
  nsNode cred nameSlot nameVal
/-- **renew** — extend the lease (`SetField EXPIRY`). `Monotonic` ⇒ admitted iff `new ≥ old`. -/
def renewNode (cred : Authorization Dg Pf) (newExpiry : Int) : DForest :=
  nsNode cred expirySlot newExpiry
/-- **transfer** — change ownership (`SetField OWNER_HASH`). No slot caveat ⇒ ownership is freely moved
(authority/credential alone gate it). -/
def transferNode (cred : Authorization Dg Pf) (newOwner : Int) : DForest :=
  nsNode cred ownerSlot newOwner
/-- **revoke** — write the tombstone (`SetField REVOKED`). `WriteOnce` ⇒ the first revoke commits, a
second (different) write is rejected (permanence). -/
def revokeNode (cred : Authorization Dg Pf) (tombstone : Int) : DForest :=
  nsNode cred revokedSlot tombstone
/-- **set-target** — update the resolve pointer (`SetField RESOLVE_TARGET`). No caveat ⇒ free to update. -/
def setTargetNode (cred : Authorization Dg Pf) (newTarget : Int) : DForest :=
  nsNode cred targetSlot newTarget

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` — PROVED (the load-bearing collapse).** A gated forest with NO children
runs EXACTLY its root gated node step: `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`. (Both
branches of `execFullForestG`'s match collapse because `execFullChildrenG _ s' [] = some s'`.) This is
the bridge through which every nameservice op's `none`/`some` is read off `execFullAGated` directly. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_nsNode` — the nameservice-op collapse.** A childless nameservice op runs
`if gateOK then execFullA (.setFieldA …) else none`, and `execFullA (.setFieldA …) = stateStepGuarded`.
The unfolding every theorem below rests on. -/
theorem execFullForestG_nsNode (s : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) :
    execFullForestG s (nsNode cred slot value)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s slot registryActor registryCell value
         else none) := by
  rw [nsNode, execFullForestG_leaf, execFullAGated]
  rfl

/-! ## §4 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` (and any forged cred) fail-closed.

`gateOK (mkAuth cred []) s = credentialValidG (mkAuth cred []) && capAuthorityG (mkAuth cred []) &&
caveatsDischarged (mkAuth cred []) s && revocationGate (mkAuth cred []) s`. For `mkAuth`: the cap mode
is `.unchecked (Guard.all [])` (admits), the within-cell caveat list is `[]` (vacuously discharged, no
chain), the nullifier is `0` (not in `reg0.kernel.revoked = []`). So `gateOK` is exactly the credential
leg `credentialValidG (mkAuth cred [])` — `portalVerify cred`. -/

/-- The forged credential's gate leg is FALSE (`portalVerify (.signature 7 8) = decide (7 = 8) = false`)
— independent of state, so the whole gate `gateOK (mkAuth forgedCred []) s = false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated turn REJECTS. -/

/-- **`ns_forged_credential_rejected` — PROVED.** A nameservice op (any slot/value) presented with a
FORGED credential is rejected by the production turn entry: `execFullForestG s (nsNode forgedCred …) =
none`, for EVERY pre-state `s`. The §8 credential leg fail-closes ⇒ the whole forest rolls back —
nobody can register/renew/transfer/revoke/retarget without a genuine credential. -/
theorem ns_forged_credential_rejected (s : RecChainedState) (slot : FieldName) (value : Int) :
    execFullForestG s (nsNode forgedCred slot value) = none := by
  rw [nsNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA registryActor registryCell slot value) [] (gateOK_forged_false s)

/-- Specialization to `registerNode` (the headline shape `registerNode forgedCred …`). -/
theorem ns_forged_register_rejected (s : RecChainedState) (nameVal : Int) :
    execFullForestG s (registerNode forgedCred nameVal) = none :=
  ns_forged_credential_rejected s nameSlot nameVal

/-! ## §6 — END-USER THEOREMS 2–4: the SLOT CAVEATS bite (gate passes for `goodCred`, the WRITE fails).

These are the COMPOSITION: the gate passes (genuine credential, admitting cap, discharged caveats,
not revoked) so `execFullForestG s (nsNode goodCred …) = stateStepGuarded …`; then the SLOT caveat on
the written field makes `caveatsAdmit = false`, so `stateStepGuarded = none`
(`stateStepGuarded_caveat_violation_fails`). The whole turn rejects — enforced BY THE EXECUTOR. -/

/-- **`ns_good_node_runs_write` — the gate-passing collapse for `goodCred`.** When the genuine
credential admits, the nameservice op IS its caveat-gated `SetField` — `execFullForestG s (nsNode
goodCred slot value) = stateStepGuarded s slot registryActor registryCell value`. The hinge for
theorems 2–4: any later caveat-rejection of the WRITE rejects the whole turn. -/
theorem ns_good_node_runs_write (s : RecChainedState) (slot : FieldName) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (nsNode goodCred slot value)
      = stateStepGuarded s slot registryActor registryCell value := by
  rw [execFullForestG_nsNode, if_pos hgate]

/-- **`ns_name_squat_impossible` — PROVED (END-USER THEOREM 2).** If the registry's `name` slot already
holds a DIFFERENT non-zero binding (the name is taken: `WriteOnce`, `old ≠ 0`, `value ≠ old`), then a
register over it is rejected by the executor — `execFullForestG s (registerNode goodCred value) = none`
— EVEN with a genuine credential. No squatter can overwrite a registered name. NON-VACUOUS: the
hypothesis `caveatsAdmit … = false` is forced by the `WriteOnce name` caveat on a contested slot. -/
theorem ns_name_squat_impossible (s : RecChainedState) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hsquat : caveatsAdmit s.kernel nameSlot registryActor registryCell value = false) :
    execFullForestG s (registerNode goodCred value) = none := by
  rw [registerNode, ns_good_node_runs_write s nameSlot value hgate]
  exact stateStepGuarded_caveat_violation_fails s nameSlot registryActor registryCell value hsquat

/-- **`ns_rent_cannot_shorten` — PROVED (END-USER THEOREM 3).** If the `Monotonic expiry` caveat rejects
the new lease (`caveatsAdmit = false`, i.e. `newExpiry < old`), a renew is rejected —
`execFullForestG s (renewNode goodCred newExpiry) = none` — EVEN with a genuine credential. Rent can
only be EXTENDED, never silently clawed back. -/
theorem ns_rent_cannot_shorten (s : RecChainedState) (newExpiry : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hshort : caveatsAdmit s.kernel expirySlot registryActor registryCell newExpiry = false) :
    execFullForestG s (renewNode goodCred newExpiry) = none := by
  rw [renewNode, ns_good_node_runs_write s expirySlot newExpiry hgate]
  exact stateStepGuarded_caveat_violation_fails s expirySlot registryActor registryCell newExpiry hshort

/-- **`ns_revoke_permanent` — PROVED (END-USER THEOREM 4).** If the `revoked` tombstone is already set
(the `WriteOnce revoked` caveat rejects a second, different write: `caveatsAdmit = false`), a second
revoke is rejected — `execFullForestG s (revokeNode goodCred tombstone) = none`. Once revoked, a name
is revoked FOREVER; no one can lift or move the tombstone. -/
theorem ns_revoke_permanent (s : RecChainedState) (tombstone : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hset : caveatsAdmit s.kernel revokedSlot registryActor registryCell tombstone = false) :
    execFullForestG s (revokeNode goodCred tombstone) = none := by
  rw [revokeNode, ns_good_node_runs_write s revokedSlot tombstone hgate]
  exact stateStepGuarded_caveat_violation_fails s revokedSlot registryActor registryCell tombstone hset

/-! ## §5b — END-USER THEOREM 5: a committed nameservice turn CONSERVES every asset.

A nameservice op is a single `SetField`, which has `ledgerDeltaAsset = 0` for EVERY asset — so its
per-asset turn delta is `0`, and `execFullForestG_conserves_per_asset` gives supply-preservation for
free. The credential/caveat gate is balance-orthogonal: passing the gate does not move money, and
failing it commits nothing. -/

/-- The per-asset turn delta of any nameservice op is `0` (a `SetField` is balance-neutral) — for EVERY
asset `b`. The conservation hypothesis, discharged once and reused for every op. -/
theorem nsNode_delta_zero (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (nsNode cred slot value)).map Prod.snd) b = 0 := by
  simp [nsNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`ns_register_conserves` — PROVED (END-USER THEOREM 5).** A COMMITTED nameservice turn preserves
EVERY asset's total supply: `recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b`,
for every asset `b`. The registry write touches metadata, never balance — so a name registration moves
no money. A one-liner off `execFullForestG_conserves_per_asset` with the `SetField`-is-balance-neutral
hypothesis discharged by `nsNode_delta_zero`. Stated for `register`; identical for every op (same shape). -/
theorem ns_register_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (nameVal : Int)
    (b : AssetId) (h : execFullForestG s (registerNode cred nameVal) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (registerNode cred nameVal) b h
    (nsNode_delta_zero cred nameSlot nameVal b)

/-- The conservation theorem holds for EVERY op, not just register (the shape is uniform). -/
theorem ns_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestG s (nsNode cred slot value) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (nsNode cred slot value) b h
    (nsNode_delta_zero cred slot value b)

/-! ## §7 — NON-VACUITY: a concrete registry-cell state with the real slot caveats + `#guard` witnesses.

`reg0` is the registry cell `0`, born with the three nameservice slot caveats and a CONTESTED name
binding (`name = 42`, owner `7`, expiry `100`, no tombstone). Actor `0 == registryCell`, so `stateAuthB`
holds; the cell is Live (default lifecycle `0`); accounts `{0, 1}`; the revocation registry is empty.
On `reg0` we exhibit: (i) a GOOD register over a FRESH name slot COMMITS; (ii) a forged credential ⇒
`none`; (iii) a squat over the contested name ⇒ `none`; (iv) a rent-shorten ⇒ `none`; (v) a second
revoke ⇒ `none`; (vi) the committed register CONSERVES both assets — so every theorem above is
witnessed REAL, not vacuous. -/

/-- A registry-cell pre-state: cell `0` carries the three slot caveats; the `name` slot is ALREADY
bound to `42` (contested), `expiry = 100`, `owner = 7`, no tombstone (`revoked = 0`). -/
def reg0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (nameSlot, .int 42), (ownerSlot, .int 7),
                           (expirySlot, .int 100), (revokedSlot, .int 0), (targetSlot, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then registryCaveats else [] }
    log := [] }

/-- A registry-cell pre-state whose `name` slot is FRESH (`name = 0`) — a GOOD register here COMMITS
(the `WriteOnce name` caveat permits the first write). Everything else as `reg0`. -/
def regFresh : RecChainedState :=
  { reg0 with kernel := { reg0.kernel with
      cell := fun c => if c = 0 then
                .record [("balance", .int 0), (nameSlot, .int 0), (ownerSlot, .int 0),
                         (expirySlot, .int 100), (revokedSlot, .int 0), (targetSlot, .int 0)]
              else .record [("balance", .int 0)] } }

/-- The registry-cell state AFTER a first revoke (the `revoked` tombstone is now set to `1`). A second,
DIFFERENT revoke must be rejected (the `WriteOnce revoked` caveat: `old = 1 ≠ 0`, `new = 2 ≠ 1`). -/
def regRevoked : RecChainedState :=
  { reg0 with kernel := { reg0.kernel with
      cell := fun c => if c = 0 then
                .record [("balance", .int 0), (nameSlot, .int 42), (ownerSlot, .int 7),
                         (expirySlot, .int 100), (revokedSlot, .int 1), (targetSlot, .int 0)]
              else .record [("balance", .int 0)] } }

-- The gate passes for the genuine credential on these states (the credential leg is the only live leg):
#guard (gateOK (mkAuth goodCred []) reg0)        --  true  (genuine credential admits)
#guard (gateOK (mkAuth goodCred []) regFresh)    --  true
#guard (gateOK (mkAuth forgedCred []) reg0) == false  --  false (forged ⇒ fail-closed)

-- (i) a GOOD register over a FRESH name slot COMMITS (the WriteOnce caveat permits the genesis write):
#guard ((execFullForestG regFresh (registerNode goodCred 42)).isSome)  --  true (registered!)
-- ...and the committed name slot reads back `42`:
#guard ((execFullForestG regFresh (registerNode goodCred 42)).map
        (fun s => fieldOf nameSlot (s.kernel.cell 0))) == some 42  --  some 42

-- (ii) a FORGED credential ⇒ none (credential gate fail-closes), even on the fresh state:
#guard ((execFullForestG regFresh (registerNode forgedCred 42)).isSome) == false  --  false

-- (iii) NAME-SQUAT: registering a DIFFERENT value over the contested `name = 42` slot ⇒ none
--       (WriteOnce: old = 42 ≠ 0 and new = 99 ≠ 42 ⇒ caveatsAdmit = false):
#guard (caveatsAdmit reg0.kernel nameSlot registryActor registryCell 99) == false  --  false (taken)
#guard ((execFullForestG reg0 (registerNode goodCred 99)).isSome) == false  --  false (squat rejected)
-- ...rewriting the SAME value (42) is a WriteOnce no-op and is admitted (the binding is idempotent):
#guard (caveatsAdmit reg0.kernel nameSlot registryActor registryCell 42)  --  true (no-op rewrite)

-- (iv) RENT CANNOT SHORTEN: expiry 100 → 50 is rejected (Monotonic: 50 < 100 ⇒ caveatsAdmit = false):
#guard (caveatsAdmit reg0.kernel expirySlot registryActor registryCell 50) == false  --  false (shorter)
#guard ((execFullForestG reg0 (renewNode goodCred 50)).isSome) == false  --  false (renew rejected)
-- ...extending the lease (100 → 200) is admitted and COMMITS:
#guard (caveatsAdmit reg0.kernel expirySlot registryActor registryCell 200)  --  true (longer)
#guard ((execFullForestG reg0 (renewNode goodCred 200)).isSome)  --  true (renew commits)

-- (v) REVOKE PERMANENT: first revoke (tombstone 0 → 1) commits; a SECOND, different write is rejected:
#guard ((execFullForestG reg0 (revokeNode goodCred 1)).isSome)  --  true (first revoke commits)
-- model the post-revoke state (tombstone now 1) and show a second (different) revoke is rejected:
#guard (caveatsAdmit regRevoked.kernel revokedSlot registryActor registryCell 2) == false  --  false (tombstone already set)
-- ...and the second revoke through the FULL gated turn is rejected (tombstone is permanent):
#guard ((execFullForestG regRevoked (revokeNode goodCred 2)).isSome) == false  --  false (revoke is forever)

-- (vi) a TRANSFER (no slot caveat on `owner`) COMMITS with a genuine credential:
#guard ((execFullForestG reg0 (transferNode goodCred 8)).isSome)  --  true (ownership moved)
-- (vii) set-target (no caveat) COMMITS:
#guard ((execFullForestG reg0 (setTargetNode goodCred 5)).isSome)  --  true (resolve pointer set)

-- (viii) CONSERVATION: a committed register moves NO asset's supply (per-asset Δ = 0):
#guard ((execFullForestG regFresh (registerNode goodCred 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (unchanged)

/-! ## §8 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. (The portal soundness
is a Prop carrier in `FullForestAuth`, never an axiom, so it does not appear.) -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_nsNode
#assert_axioms gateOK_forged_false
#assert_axioms ns_forged_credential_rejected
#assert_axioms ns_name_squat_impossible
#assert_axioms ns_rent_cannot_shorten
#assert_axioms ns_revoke_permanent
#assert_axioms ns_register_conserves
#assert_axioms ns_op_conserves

end Dregg2.Apps.NameserviceGated
