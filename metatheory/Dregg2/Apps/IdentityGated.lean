/-
# Dregg2.Apps.IdentityGated — the identity app on the ONE gated executor: REVOKED STAYS REVOKED, forever.

`Dregg2.Apps.Identity` carried permanent-revocation on the credential-BLIND living cell. This module
re-models the SAME headline on the ONE production turn entry — `FullForestAuth.execFullForestG`
(`dregg_exec_full_forest_auth`, the 4-leg gate credential ∧ cap-authority ∧ caveats ∧ NOT-revoked) —
so the end-user theorems are about the EXECUTED, credential-gated turn the running system runs.

The identity protocol (credentials/src, starbridge-apps/identity): issue / present / verify / REVOKE.
The headline safety is PERMANENT REVOCATION: once a credential's nullifier is in the committed
revocation registry `s.kernel.revoked`, that credential can NEVER act again — at ANY reachable state.
This is EXACTLY the gate's revocation leg `revocationGate na s = !(s.kernel.revoked.contains na.credNul)`,
with the PROVED teeth `FullForestAuth.gateOK_revoked_fails`. An identity "use" (present/verify) is a
credential-gated op; a revoked credential's op fails-closed (`execFullForestG_unauthorized_fails`).

## End-user theorems (general; concrete `#guard` witnesses for non-vacuity)
  1. `id_forged_rejected`   — a forged credential ⇒ the whole gated turn rejects (`none`), ∀ state.
  2. `id_revoked_rejected`  — THE HEADLINE: a credential whose nullifier is in `s.kernel.revoked`
                              is rejected, ∀ state — a revoked credential can never act.
  3. `id_op_conserves`      — a committed identity op moves NO asset's supply (per-asset Δ = 0).

Zero `sorry`/`admit`/`native_decide`/`axiom`. Does NOT touch `Identity.lean`, `FullForestAuth.lean`,
nor `Dregg2.lean`. Reuses ONLY the proved gated-executor keystones (`gateOK_revoked_fails`,
`execFullForestG_unauthorized_fails`, `execFullForestG_conserves_per_asset`).
-/
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Apps.IdentityGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForestAuth.Demo

/-- The file-local `Verifiable` instance the `Gate`/`Gated` dispatcher signatures need at the Demo
carriers (`Stmt = Wit = Nat`), re-declared exactly as `FullForestAuth.Demo` does (its instance is
file-local). Without it `gateOK`/`execFullForestG` cannot elaborate at the Demo carriers. -/
local instance demoVerifiableId : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-! ## §1 — The identity DOMAIN at the Demo carriers. -/

/-- The identity cell (holds a credential's published status). Cell `0` so `actor = 0` self-authorizes
(`stateAuthB` by `actor == src`) — the load-bearing admission is the §8 CREDENTIAL gate, not the c-list. -/
abbrev idCell : CellId := 0
/-- The identity actor (the credential holder). Equal to `idCell` so `stateAuthB` holds. -/
abbrev idActor : CellId := 0
/-- The status slot a present/verify writes (no slot caveat — the gate is the credential, not a caveat). -/
abbrev statusSlot : FieldName := "status"

/-- An identity op (present/verify/update status) = a credential-gated leaf node: the credential `cred`
(the WHO), a `SetField` on the identity cell, no children. The production-entry shape. -/
def idNode (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA idActor idCell slot value, [] ⟩

/-! ## §2 — The leaf-collapse bridge (a childless gated forest runs EXACTLY its single gated node). -/

/-- **`execFullForestG_leaf` — PROVED.** `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`
(both match branches collapse: `execFullChildrenG _ s' [] = some s'`). -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-! ## §3 — The credential gate: a FORGED credential fails-closed (state-independent). -/

/-- **`gateOK_forged_false` — PROVED.** `portalVerify (.signature 7 8) = decide (7 = 8) = false`, so the
credential leg fails ⇒ the whole 4-leg gate is `false`, for EVERY pre-state. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §4 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated turn REJECTS. -/

/-- **`id_forged_rejected` — PROVED.** No identity op (any slot/value) commits with a forged credential:
`execFullForestG s (idNode forgedCred …) = none`, for EVERY pre-state `s`. -/
theorem id_forged_rejected (s : RecChainedState) (slot : FieldName) (value : Int) :
    execFullForestG s (idNode forgedCred slot value) = none := by
  rw [idNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA idActor idCell slot value) [] (gateOK_forged_false s)

/-! ## §5 — END-USER THEOREM 2 (THE HEADLINE): a REVOKED credential can NEVER act. -/

/-- **`id_revoked_rejected` — PROVED (permanent revocation).** If `goodCred`'s nullifier is in the
COMMITTED revocation registry `s.kernel.revoked`, then EVERY identity op presented with it is rejected
by the production turn entry — `execFullForestG s (idNode goodCred …) = none` — at EVERY reachable
state `s`. The revocation leg (`gateOK_revoked_fails`, reading adversary-uncontrollable kernel state)
fail-closes ⇒ the whole forest rolls back. Once revoked, a credential can never be re-validated.
NON-VACUOUS: a GENUINE (`portalVerify`-passing) credential is still rejected purely because it is
revoked — credential-validity and revocation are orthogonal legs. -/
theorem id_revoked_rejected (s : RecChainedState) (slot : FieldName) (value : Int)
    (hrev : s.kernel.revoked.contains (mkAuth goodCred []).credNul = true) :
    execFullForestG s (idNode goodCred slot value) = none := by
  rw [idNode]
  exact execFullForestG_unauthorized_fails s (mkAuth goodCred [])
    (.setFieldA idActor idCell slot value) [] (gateOK_revoked_fails (mkAuth goodCred []) s hrev)

/-! ## §6 — END-USER THEOREM 3: a committed identity op CONSERVES every asset. -/

/-- The per-asset turn delta of any identity op is `0` (a `SetField` is balance-neutral), every asset. -/
theorem idNode_delta_zero (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (idNode cred slot value)).map Prod.snd) b = 0 := by
  simp [idNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`id_op_conserves` — PROVED.** A committed identity op preserves every asset's total supply
(metadata write, no money). One-liner off `execFullForestG_conserves_per_asset`. -/
theorem id_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestG s (idNode cred slot value) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (idNode cred slot value) b h
    (idNode_delta_zero cred slot value b)

/-! ## §7 — NON-VACUITY: concrete states + `#guard` witnesses (the revocation teeth are REAL). -/

/-- A non-revoked identity state (cell 0 live, empty revocation registry; supply asset0 = 105, asset1 = 7). -/
def id0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

/-- The SAME state but with `goodCred`'s nullifier in the committed revocation registry — the credential
is REVOKED. Every op presented with it must now fail-closed (permanent revocation). -/
def idRevoked : RecChainedState :=
  { id0 with kernel := { id0.kernel with revoked := [(mkAuth goodCred []).credNul] } }

-- The gate admits the genuine credential when NOT revoked, and fail-closes once it IS revoked:
#guard (gateOK (mkAuth goodCred []) id0)                              --  true  (genuine + not revoked)
#guard (gateOK (mkAuth goodCred []) idRevoked) == false               --  false (revoked ⇒ gate fails)
#guard (gateOK (mkAuth forgedCred []) id0) == false                   --  false (forged ⇒ gate fails)

-- (i) a genuine, non-revoked credential op COMMITS:
#guard ((execFullForestG id0 (idNode goodCred statusSlot 1)).isSome)              --  true (presented)
-- (ii) the SAME op with a REVOKED credential ⇒ none (THE HEADLINE, witnessed):
#guard ((execFullForestG idRevoked (idNode goodCred statusSlot 1)).isSome) == false  --  false (revoked forever)
-- (iii) a FORGED credential ⇒ none:
#guard ((execFullForestG id0 (idNode forgedCred statusSlot 1)).isSome) == false      --  false
-- (iv) the committed op CONSERVES both assets (metadata, no money moved):
#guard ((execFullForestG id0 (idNode goodCred statusSlot 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §8 — Axiom-hygiene tripwires (the honesty pins; kernel-clean, no `sorryAx`). -/

#assert_axioms execFullForestG_leaf
#assert_axioms gateOK_forged_false
#assert_axioms id_forged_rejected
#assert_axioms id_revoked_rejected
#assert_axioms idNode_delta_zero
#assert_axioms id_op_conserves

end Dregg2.Apps.IdentityGated
