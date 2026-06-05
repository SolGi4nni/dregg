/-
# Dregg2.Apps.GovernedNamespaceGated — the GOVERNED NAMESPACE on the ONE gated executor.

`starbridge-apps/governed-namespace/src/lib.rs` is the fourth starbridge-app: a **governance-bound
atomic route-table swap** on a sovereign cell. A *governed-namespace cell* hosts a route table whose
root lives in slot 0; updates are GOVERNED — gated by a constitutional committee (a
`WitnessedPredicate { kind = Custom { vk_hash = GOVERNANCE_VK } }` threshold-signature carrier in an
`Authorization::Custom` action) plus per-slot caveats the executor enforces on every `SetField`.

This module re-models that app through the ONE production turn entry —
`Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate:
credential ∧ cap-authority ∧ caveats-discharged ∧ not-revoked) — at the Demo carriers, so every
end-user theorem is about the EXECUTED, credential-gated, caveat-enforcing turn the running system runs.

## The GOVERNANCE dimension = the §8 credential gate

The Rust app's authority story is the threshold-sig committee: only an authorized/attested caller's
`commit_table_update` (and propose/vote) commits; a forged or unauthorized carrier commits NOTHING.
We model the committee-threshold authorization as the §8 CREDENTIAL leg of `gateOK`: `goodCred` admits
(an attested/authorized caller), `forgedCred` fails-closed (a forged threshold-sig / unauthorized
caller). The revocation leg models a committee member whose key was rotated out of the constitution
(its nullifier in `s.kernel.revoked`) — it can never act again.

## The registry cell's SLOT CAVEATS (the constitutional invariants, executor-enforced)

The governed-namespace cell carries (`s.kernel.slotCaveats nsCell`) exactly the Rust app's slot layout
(`lib.rs` §"Slot layout" + `governance_program`'s `Always` / per-method cases):
  * `Immutable governance_committee_root` — the committee is CONSTITUTIONAL; it never changes →
    **no committee capture by silent rewrite**;
  * `Immutable threshold`                 — the threshold is CONSTITUTIONAL; never weakened →
    **no "lower the bar to 1 signer" attack**;
  * `MonotonicSeq version`                — `commit_table_update` bumps version by EXACTLY +1 →
    **no replay / no version skip on an atomic swap**;
  * `Monotonic dispute_window_height`     — the dispute window only pushes forward →
    **no shrinking the contestation window under voters**.

`stateStepGuarded` (the `setFieldA` arm of `execFullA`) reads exactly these and FAILS CLOSED on a
violating write — so the constitutional invariants are enforced BY THE EXECUTOR, not merely carried.

## End-user theorems (general; concrete `#guard` witnesses for non-vacuity)

  1. `gn_forged_credential_rejected` — a forged threshold-sig / unauthorized carrier ⇒ the whole gated
     turn rejects (`none`), ∀ state — only authorized/attested callers' ops commit;
  2. `gn_unauthorized_rejected`      — generic fail-closed: ANY gate-failing carrier ⇒ `none`, ∀ state;
  3. `gn_committee_immutable`        — a rewrite of the constitutional committee root ⇒ `none` (capture-proof);
  4. `gn_threshold_immutable`        — a rewrite of the constitutional threshold ⇒ `none` (bar cannot be lowered);
  5. `gn_version_monotonic_seq`      — a commit that does not bump version by exactly +1 ⇒ `none` (no replay/skip);
  6. `gn_dispute_window_cannot_shrink` — a dispute-window write that goes backwards ⇒ `none`;
  7. `gn_revoked_member_rejected`    — a committee member rotated out (revoked nullifier) ⇒ `none`, ∀ state;
  8. `gn_commit_conserves`           — a committed table swap moves NO asset's supply (per-asset Δ = 0).

Plus a concrete governed-namespace cell state (`gn0`) whose `#guard`s show a GOOD governed write
COMMITS, a forged credential gives `none`, and each constitutional caveat bites (committee/threshold
rewrite, version skip, window shrink) — the gate + the caveats are REAL, not vacuous.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Does NOT touch `FullForestAuth.lean` nor `Dregg2.lean`.
Reuses ONLY the proved gated-executor keystones + the proved `stateStepGuarded` fail-closed teeth.
-/
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Apps.GovernedNamespaceGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForestAuth.Demo

/-- The file-local `Verifiable` instance the `Gate`/`Gated` dispatcher signatures need at the Demo
carriers (`Stmt = Wit = Nat`), re-declared exactly as `FullForestAuth.Demo` does (its instance is
file-local, so it does not escape the import). Without it `gateOK`/`execFullForestG` cannot elaborate. -/
local instance demoVerifiableGN : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-! ## §1 — The governed-namespace DOMAIN at the Demo carriers (the cell, the slots, the caveats). -/

/-- The governed-namespace cell holding the route table + constitution (`lib.rs`'s sovereign cell).
We use cell `0` so the actor can be `0` too — `stateAuthB` is then trivially satisfied (`actor == src`),
letting the credential-gate and the SLOT CAVEAT be the load-bearing admission conditions (the
governance dimension), not the c-list. -/
abbrev nsCell : CellId := 0

/-- The carrier submitting a governed turn (a committee member / threshold-sig carrier). Equal to
`nsCell` so `stateAuthB` holds by `actor == src` — the app's authority story rides on the §8
CREDENTIAL gate (the committee threshold), not the c-list. -/
abbrev nsActor : CellId := 0

/-- Slot 0 — `route_table_root` (dregg1 `ROUTE_TABLE_ROOT_SLOT`). The BLAKE3 commitment of the live
route table; the atomic-swap target. No standing caveat here (the swap is the whole point; structural
well-formedness rides on the governance verifier out-of-band). -/
abbrev routeTableRootSlot : FieldName := "route_table_root"
/-- Slot 1 — `version` (dregg1 `VERSION_SLOT`) — `MonotonicSequence`: `commit_table_update` bumps it by
EXACTLY +1 (no replay, no skip on an atomic swap). -/
abbrev versionSlot : FieldName := "version"
/-- Slot 2 — `governance_committee_root` (dregg1 `GOVERNANCE_COMMITTEE_ROOT_SLOT`) — `Immutable`: the
committee is constitutional and never changes (no capture by silent rewrite). -/
abbrev committeeRootSlot : FieldName := "governance_committee_root"
/-- Slot 3 — `threshold` (dregg1 `THRESHOLD_SLOT`) — `Immutable`: the signature threshold is
constitutional and never weakened (no "lower the bar" attack). -/
abbrev thresholdSlot : FieldName := "threshold"
/-- Slot 4 — `dispute_window_height` (dregg1 `DISPUTE_WINDOW_HEIGHT_SLOT`) — `Monotonic`: the
contestation window only pushes forward (cannot be shrunk under voters). -/
abbrev disputeWindowSlot : FieldName := "dispute_window_height"
/-- Slot 5 — `pending_proposal_root` (dregg1 `PENDING_PROPOSAL_ROOT_SLOT`) — advances under
propose/vote, cleared by commit (no standing transition caveat — its discipline is in the program
cases, modelled by the credential gate). -/
abbrev pendingProposalSlot : FieldName := "pending_proposal_root"

/-- The governed-namespace cell's factory-installed SLOT CAVEATS — exactly the Rust app's constitutional
invariants (`governance_factory_descriptor`'s `state_constraints` + `governance_program`'s `Always`
case): `Immutable committee_root`, `Immutable threshold`, `MonotonicSeq version`,
`Monotonic dispute_window`. The executor reads these on EVERY `SetField` to the cell
(`stateStepGuarded`). -/
def nsCaveats : List SlotCaveat :=
  [ .immutable committeeRootSlot, .immutable thresholdSlot,
    .monotonicSeq versionSlot, .monotonic disputeWindowSlot ]

/-! ## §2 — A governed op as a GATED LEAF NODE through the production turn entry `execFullForestG`.

A governed-namespace write is a `SetField` on the namespace cell, decorated with a credential (the
committee threshold-sig — the WHO) and run through the 4-leg gate. `mkAuth cred []` (from
`FullForestAuth.Demo`) supplies an admitting cap-mode (`.unchecked (Guard.all [])`), an empty
within-cell caveat list (so the GATE's caveat leg is vacuously discharged — the constitutional SLOT
caveats are enforced separately by `stateStepGuarded` inside `execFullA`), no chain, and a non-revoked
nullifier. So `gateOK` reduces to the CREDENTIAL leg (the committee threshold) + the revocation leg. -/

/-- A gated governed-namespace node: credential `cred` (the committee threshold-sig carrier), a
`SetField slot value` on the namespace cell, no children. The production-entry shape
`⟨ mkAuth cred [], action, [] ⟩`. -/
def gnNode (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA nsActor nsCell slot value, [] ⟩

/-- **commit_table_update** — atomically swap the route-table root (`SetField route_table_root`). Gated
by the committee threshold-sig (the credential). The sibling `version`/`pending_proposal` writes are
modelled by their own nodes; the version bump is exercised by `versionBumpNode`. -/
def commitRootNode (cred : Authorization Dg Pf) (newRoot : Int) : DForest :=
  gnNode cred routeTableRootSlot newRoot
/-- **commit_table_update**'s version bump (`SetField version`). `MonotonicSeq` ⇒ admitted iff
`new = old + 1` — the atomic swap may not replay or skip a version. -/
def versionBumpNode (cred : Authorization Dg Pf) (newVersion : Int) : DForest :=
  gnNode cred versionSlot newVersion
/-- **propose_table_update**'s dispute-window push (`SetField dispute_window_height`). `Monotonic` ⇒
admitted iff `new ≥ old` — the contestation window cannot be shrunk. -/
def disputeWindowNode (cred : Authorization Dg Pf) (newHeight : Int) : DForest :=
  gnNode cred disputeWindowSlot newHeight
/-- An attempted constitutional amendment of the committee root (`SetField governance_committee_root`).
`Immutable` ⇒ rejected for any value ≠ old — the committee cannot be captured by rewrite. -/
def amendCommitteeNode (cred : Authorization Dg Pf) (newRoot : Int) : DForest :=
  gnNode cred committeeRootSlot newRoot
/-- An attempted weakening of the threshold (`SetField threshold`). `Immutable` ⇒ rejected for any
value ≠ old — the signature bar cannot be lowered. -/
def amendThresholdNode (cred : Authorization Dg Pf) (newThreshold : Int) : DForest :=
  gnNode cred thresholdSlot newThreshold

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` — PROVED (the load-bearing collapse).** A gated forest with NO children
runs EXACTLY its root gated node step: `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`. (Both
branches of `execFullForestG`'s match collapse because `execFullChildrenG _ s' [] = some s'`.) This is
the bridge through which every governed op's `none`/`some` is read off `execFullAGated` directly. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_gnNode` — the governed-op collapse.** A childless governed op runs
`if gateOK then stateStepGuarded … else none` (because `execFullA (.setFieldA …) = stateStepGuarded`).
The unfolding every theorem below rests on. -/
theorem execFullForestG_gnNode (s : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) :
    execFullForestG s (gnNode cred slot value)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s slot nsActor nsCell value
         else none) := by
  rw [gnNode, execFullForestG_leaf, execFullAGated]
  rfl

/-! ## §4 — The CREDENTIAL gate (the GOVERNANCE dimension): `goodCred` admits, `forgedCred` fails.

`gateOK (mkAuth cred []) s = credentialValidG (mkAuth cred []) && capAuthorityG (mkAuth cred []) &&
caveatsDischarged (mkAuth cred []) s && revocationGate (mkAuth cred []) s`. For `mkAuth`: the cap mode
admits, the within-cell caveat list is `[]` (vacuously discharged, no chain), the nullifier is `0`
(not revoked on `gn0`). So `gateOK` is exactly the credential leg `credentialValidG (mkAuth cred [])` —
`portalVerify cred` — modelling the committee threshold-signature check. -/

/-- The forged committee carrier's gate leg is FALSE (`portalVerify (.signature 7 8) =
decide (7 = 8) = false`) — independent of state, so the whole gate
`gateOK (mkAuth forgedCred []) s = false`. A forged threshold-sig / unauthorized carrier admits no
governed write. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREMS 1–2: only authorized/attested callers commit; forged/unauthorized ⇒ none. -/

/-- **`gn_forged_credential_rejected` — PROVED (END-USER THEOREM 1).** A governed-namespace op (any
slot/value) presented with a FORGED threshold-sig / unauthorized carrier is rejected by the production
turn entry: `execFullForestG s (gnNode forgedCred …) = none`, for EVERY pre-state `s`. The §8 credential
leg (the committee threshold) fail-closes ⇒ the whole forest rolls back — only authorized/attested
callers can propose/vote/commit/register. -/
theorem gn_forged_credential_rejected (s : RecChainedState) (slot : FieldName) (value : Int) :
    execFullForestG s (gnNode forgedCred slot value) = none := by
  rw [gnNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA nsActor nsCell slot value) [] (gateOK_forged_false s)

/-- Specialization to `commitRootNode` (the headline shape: a forged carrier cannot swap the table). -/
theorem gn_forged_commit_rejected (s : RecChainedState) (newRoot : Int) :
    execFullForestG s (commitRootNode forgedCred newRoot) = none :=
  gn_forged_credential_rejected s routeTableRootSlot newRoot

/-- **`gn_unauthorized_rejected` — PROVED (END-USER THEOREM 2, generic fail-closed).** ANY governed op
whose gate fails on ANY leg (forged credential, unauthorized cap, undischarged caveat, OR a revoked
nullifier) rejects the whole turn — `execFullForestG s (gnNode cred …) = none`. The single fail-closed
root every authorization story rides on. -/
theorem gn_unauthorized_rejected (s : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) (hgate : gateOK (mkAuth cred []) s = false) :
    execFullForestG s (gnNode cred slot value) = none := by
  rw [gnNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.setFieldA nsActor nsCell slot value) [] hgate

/-! ## §6 — END-USER THEOREMS 3–6: the CONSTITUTIONAL caveats bite (gate passes, the WRITE fails).

These are the COMPOSITION: the gate passes (authorized carrier, admitting cap, discharged caveats, not
revoked) so `execFullForestG s (gnNode goodCred …) = stateStepGuarded …`; then the SLOT caveat on the
written field makes `caveatsAdmit = false`, so `stateStepGuarded = none`
(`stateStepGuarded_caveat_violation_fails`). The whole turn rejects — enforced BY THE EXECUTOR, even for
a fully-authorized committee carrier. The committee cannot vote ITSELF out of its own constitution. -/

/-- **`gn_good_node_runs_write` — the gate-passing collapse for `goodCred`.** When the authorized
committee carrier admits, the governed op IS its caveat-gated `SetField` — `execFullForestG s (gnNode
goodCred slot value) = stateStepGuarded s slot nsActor nsCell value`. The hinge for theorems 3–6: any
later caveat-rejection of the WRITE rejects the whole turn. -/
theorem gn_good_node_runs_write (s : RecChainedState) (slot : FieldName) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (gnNode goodCred slot value)
      = stateStepGuarded s slot nsActor nsCell value := by
  rw [execFullForestG_gnNode, if_pos hgate]

/-- **`gn_committee_immutable` — PROVED (END-USER THEOREM 3).** If the `Immutable committee_root` caveat
rejects the rewrite (`caveatsAdmit = false`, i.e. a value ≠ the constitutional committee root), the
amendment is rejected — `execFullForestG s (amendCommitteeNode goodCred newRoot) = none` — EVEN with a
genuine, fully-authorized committee credential. The committee is CONSTITUTIONAL: it cannot be captured
by a silent rewrite, not even by the committee itself. -/
theorem gn_committee_immutable (s : RecChainedState) (newRoot : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfix : caveatsAdmit s.kernel committeeRootSlot nsActor nsCell newRoot = false) :
    execFullForestG s (amendCommitteeNode goodCred newRoot) = none := by
  rw [amendCommitteeNode, gn_good_node_runs_write s committeeRootSlot newRoot hgate]
  exact stateStepGuarded_caveat_violation_fails s committeeRootSlot nsActor nsCell newRoot hfix

/-- **`gn_threshold_immutable` — PROVED (END-USER THEOREM 4).** If the `Immutable threshold` caveat
rejects the rewrite (`caveatsAdmit = false`, i.e. a value ≠ the constitutional threshold), the change
is rejected — `execFullForestG s (amendThresholdNode goodCred newThreshold) = none` — EVEN with a
genuine credential. The signature bar cannot be lowered: no "drop the threshold to 1 signer" attack. -/
theorem gn_threshold_immutable (s : RecChainedState) (newThreshold : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfix : caveatsAdmit s.kernel thresholdSlot nsActor nsCell newThreshold = false) :
    execFullForestG s (amendThresholdNode goodCred newThreshold) = none := by
  rw [amendThresholdNode, gn_good_node_runs_write s thresholdSlot newThreshold hgate]
  exact stateStepGuarded_caveat_violation_fails s thresholdSlot nsActor nsCell newThreshold hfix

/-- **`gn_version_monotonic_seq` — PROVED (END-USER THEOREM 5).** If the `MonotonicSequence version`
caveat rejects the bump (`caveatsAdmit = false`, i.e. `new ≠ old + 1` — a replay or a skip), the commit
is rejected — `execFullForestG s (versionBumpNode goodCred newVersion) = none` — EVEN with a genuine
credential. An atomic table swap advances the version by EXACTLY +1: no replaying an old version, no
skipping ahead to forge a future state. -/
theorem gn_version_monotonic_seq (s : RecChainedState) (newVersion : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hseq : caveatsAdmit s.kernel versionSlot nsActor nsCell newVersion = false) :
    execFullForestG s (versionBumpNode goodCred newVersion) = none := by
  rw [versionBumpNode, gn_good_node_runs_write s versionSlot newVersion hgate]
  exact stateStepGuarded_caveat_violation_fails s versionSlot nsActor nsCell newVersion hseq

/-- **`gn_dispute_window_cannot_shrink` — PROVED (END-USER THEOREM 6).** If the `Monotonic
dispute_window_height` caveat rejects the write (`caveatsAdmit = false`, i.e. `new < old`), the proposal
is rejected — `execFullForestG s (disputeWindowNode goodCred newHeight) = none` — EVEN with a genuine
credential. The contestation window can only push FORWARD: no shrinking the window out from under
voters mid-dispute. -/
theorem gn_dispute_window_cannot_shrink (s : RecChainedState) (newHeight : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hback : caveatsAdmit s.kernel disputeWindowSlot nsActor nsCell newHeight = false) :
    execFullForestG s (disputeWindowNode goodCred newHeight) = none := by
  rw [disputeWindowNode, gn_good_node_runs_write s disputeWindowSlot newHeight hgate]
  exact stateStepGuarded_caveat_violation_fails s disputeWindowSlot nsActor nsCell newHeight hback

/-! ## §7 — END-USER THEOREM 7: a committee member ROTATED OUT (revoked) can NEVER act.

The Rust app's committee root is the set of authorized member keys; a member rotated out of the
constitution must lose its vote/commit power forever. We model "rotated out" as the credential's
nullifier sitting in the COMMITTED revocation registry `s.kernel.revoked` — the gate's revocation leg
(`gateOK_revoked_fails`, reading adversary-uncontrollable kernel state) fail-closes. -/

/-- **`gn_revoked_member_rejected` — PROVED (END-USER THEOREM 7).** If `goodCred`'s nullifier is in the
COMMITTED revocation registry `s.kernel.revoked` (the member was rotated out of the committee), then
EVERY governed op presented with it is rejected — `execFullForestG s (gnNode goodCred …) = none` — at
EVERY reachable state `s`. NON-VACUOUS: a GENUINE (`portalVerify`-passing) credential is still rejected
purely because it is revoked — credential-validity and revocation are orthogonal legs. -/
theorem gn_revoked_member_rejected (s : RecChainedState) (slot : FieldName) (value : Int)
    (hrev : s.kernel.revoked.contains (mkAuth goodCred []).credNul = true) :
    execFullForestG s (gnNode goodCred slot value) = none := by
  rw [gnNode]
  exact execFullForestG_unauthorized_fails s (mkAuth goodCred [])
    (.setFieldA nsActor nsCell slot value) [] (gateOK_revoked_fails (mkAuth goodCred []) s hrev)

/-! ## §8 — END-USER THEOREM 8: a committed governed turn CONSERVES every asset.

A governed-namespace op is a single `SetField`, which has `ledgerDeltaAsset = 0` for EVERY asset — so
its per-asset turn delta is `0`, and `execFullForestG_conserves_per_asset` gives supply-preservation
for free. Governance is balance-orthogonal: a route-table swap (or committee/threshold/version write)
touches metadata, never money — passing the threshold-sig gate does not move funds, and failing it
commits nothing. -/

/-- The per-asset turn delta of any governed op is `0` (a `SetField` is balance-neutral) — for EVERY
asset `b`. The conservation hypothesis, discharged once and reused for every op. -/
theorem gnNode_delta_zero (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (gnNode cred slot value)).map Prod.snd) b = 0 := by
  simp [gnNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`gn_commit_conserves` — PROVED (END-USER THEOREM 8).** A COMMITTED governed table swap preserves
EVERY asset's total supply: `recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b`,
for every asset `b`. The route-table commitment write touches metadata, never balance — so a governance
swap moves no money. A one-liner off `execFullForestG_conserves_per_asset` with the
`SetField`-is-balance-neutral hypothesis discharged by `gnNode_delta_zero`. Stated for the commit
(root) swap; identical for every op (same shape). -/
theorem gn_commit_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (newRoot : Int)
    (b : AssetId) (h : execFullForestG s (commitRootNode cred newRoot) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (commitRootNode cred newRoot) b h
    (gnNode_delta_zero cred routeTableRootSlot newRoot b)

/-- The conservation theorem holds for EVERY governed op, not just the root swap (uniform shape). -/
theorem gn_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestG s (gnNode cred slot value) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (gnNode cred slot value) b h
    (gnNode_delta_zero cred slot value b)

/-! ## §9 — NON-VACUITY: a concrete governed-namespace state with the real caveats + `#guard` witnesses.

`gn0` is the namespace cell `0`, born with the four constitutional slot caveats and a live constitution:
committee root `committee = 555`, threshold `3`, version `7`, dispute window `1000`, route-table root
`111`. Actor `0 == nsCell`, so `stateAuthB` holds; the cell is Live (default lifecycle `0`); accounts
`{0, 1}`; the revocation registry is empty. On `gn0` we exhibit: (i) a GOOD route-table swap COMMITS;
(ii) a forged carrier ⇒ `none`; (iii) a committee-amendment ⇒ `none`; (iv) a threshold-weaken ⇒ `none`;
(v) a version replay/skip ⇒ `none` (and the exact +1 bump COMMITS); (vi) a window-shrink ⇒ `none`;
(vii) a revoked member ⇒ `none`; (viii) the committed swap CONSERVES both assets — so every theorem
above is witnessed REAL, not vacuous. -/

/-- A governed-namespace pre-state: cell `0` carries the four constitutional caveats; committee root
`555`, threshold `3`, version `7`, dispute window `1000`, route-table root `111`, pending `0`. -/
def gn0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (routeTableRootSlot, .int 111),
                           (versionSlot, .int 7), (committeeRootSlot, .int 555),
                           (thresholdSlot, .int 3), (disputeWindowSlot, .int 1000),
                           (pendingProposalSlot, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then nsCaveats else [] }
    log := [] }

/-- The SAME state but with `goodCred`'s nullifier in the committed revocation registry — the committee
member is ROTATED OUT. Every op presented with it must now fail-closed (permanent revocation). -/
def gnRevoked : RecChainedState :=
  { gn0 with kernel := { gn0.kernel with revoked := [(mkAuth goodCred []).credNul] } }

-- The gate passes for the genuine committee carrier, fails for the forged one, fails when revoked:
#guard (gateOK (mkAuth goodCred []) gn0)                              --  true  (authorized carrier)
#guard (gateOK (mkAuth forgedCred []) gn0) == false                   --  false (forged ⇒ fail-closed)
#guard (gateOK (mkAuth goodCred []) gnRevoked) == false               --  false (rotated out ⇒ fail)

-- (i) a GOOD route-table swap (route_table_root: 111 → 222) COMMITS (no standing caveat on slot 0):
#guard ((execFullForestG gn0 (commitRootNode goodCred 222)).isSome)               --  true (table swapped!)
-- ...and the committed route-table root reads back `222`:
#guard ((execFullForestG gn0 (commitRootNode goodCred 222)).map
        (fun s => fieldOf routeTableRootSlot (s.kernel.cell 0))) == some 222       --  some 222

-- (ii) a FORGED carrier ⇒ none (credential/threshold gate fail-closes):
#guard ((execFullForestG gn0 (commitRootNode forgedCred 222)).isSome) == false    --  false

-- (iii) COMMITTEE CAPTURE IMPOSSIBLE: rewriting committee root 555 → 999 ⇒ none (Immutable bites):
#guard (caveatsAdmit gn0.kernel committeeRootSlot nsActor nsCell 999) == false     --  false (constitutional)
#guard ((execFullForestG gn0 (amendCommitteeNode goodCred 999)).isSome) == false   --  false (capture rejected)

-- (iv) THRESHOLD CANNOT BE LOWERED: rewriting threshold 3 → 1 ⇒ none (Immutable bites):
#guard (caveatsAdmit gn0.kernel thresholdSlot nsActor nsCell 1) == false           --  false (bar fixed)
#guard ((execFullForestG gn0 (amendThresholdNode goodCred 1)).isSome) == false     --  false (weaken rejected)

-- (v) VERSION REPLAY/SKIP REJECTED: version 7 → 7 (replay) and 7 → 9 (skip) are both rejected;
--     only the exact +1 bump (7 → 8) commits (MonotonicSequence):
#guard (caveatsAdmit gn0.kernel versionSlot nsActor nsCell 7) == false             --  false (replay)
#guard (caveatsAdmit gn0.kernel versionSlot nsActor nsCell 9) == false             --  false (skip)
#guard (caveatsAdmit gn0.kernel versionSlot nsActor nsCell 8)                      --  true  (exactly +1)
#guard ((execFullForestG gn0 (versionBumpNode goodCred 7)).isSome) == false        --  false (replay rejected)
#guard ((execFullForestG gn0 (versionBumpNode goodCred 9)).isSome) == false        --  false (skip rejected)
#guard ((execFullForestG gn0 (versionBumpNode goodCred 8)).isSome)                 --  true  (atomic +1 commits)

-- (vi) DISPUTE WINDOW CANNOT SHRINK: 1000 → 500 rejected (Monotonic); 1000 → 2000 commits:
#guard (caveatsAdmit gn0.kernel disputeWindowSlot nsActor nsCell 500) == false     --  false (backwards)
#guard ((execFullForestG gn0 (disputeWindowNode goodCred 500)).isSome) == false    --  false (shrink rejected)
#guard (caveatsAdmit gn0.kernel disputeWindowSlot nsActor nsCell 2000)             --  true  (forward)
#guard ((execFullForestG gn0 (disputeWindowNode goodCred 2000)).isSome)            --  true  (window extended)

-- (vii) ROTATED-OUT MEMBER: the SAME good carrier, once revoked, can NEVER act:
#guard ((execFullForestG gnRevoked (commitRootNode goodCred 222)).isSome) == false --  false (rotated out forever)

-- (viii) CONSERVATION: a committed table swap moves NO asset's supply (per-asset Δ = 0):
#guard ((execFullForestG gn0 (commitRootNode goodCred 222)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. (The portal soundness
is a Prop carrier in `FullForestAuth`, never an axiom, so it does not appear.) -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_gnNode
#assert_axioms gateOK_forged_false
#assert_axioms gn_forged_credential_rejected
#assert_axioms gn_unauthorized_rejected
#assert_axioms gn_committee_immutable
#assert_axioms gn_threshold_immutable
#assert_axioms gn_version_monotonic_seq
#assert_axioms gn_dispute_window_cannot_shrink
#assert_axioms gn_revoked_member_rejected
#assert_axioms gnNode_delta_zero
#assert_axioms gn_commit_conserves
#assert_axioms gn_op_conserves

end Dregg2.Apps.GovernedNamespaceGated
