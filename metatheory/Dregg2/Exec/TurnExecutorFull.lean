/-
# Dregg2.Exec.TurnExecutorFull — §11-§13: axiom-hygiene pins + non-vacuity witnesses.

SPLIT (2026-07-13, file-split only — no proof or statement changed): the scalar ladder
(§1-§10) lives in `Dregg2.Exec.TurnExecutorFull.Scalar`; the per-asset executor (§MA-§MB)
in `Dregg2.Exec.TurnExecutorFull.PerAsset` — both imported here, so importing
`Dregg2.Exec.TurnExecutorFull` still provides the WHOLE surface, unchanged. THIS file is
§11-§13 — the `#assert_axioms` honesty pins and the non-vacuity witnesses — verbatim.
-/
import Dregg2.Exec.TurnExecutorFull.PerAsset

namespace Dregg2.Exec.TurnExecutorFull

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.CatalogInstances (EffectKind effectLinearity)
open Dregg2.CatalogEffects (Regime effectObligation)
open Dregg2.Spec (Domain conservedInDomain LinearityClass)
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.Exec.EffectsState (setField fieldOf writeField stateAuthB stateStep stateStep_factors
  setField_balOf state_caps_unchanged state_authGraph_unchanged state_authorized state_obsadvance
  state_field_written stateStepGuarded stateStepGuarded_eq stateStepGuarded_admits
  stateStepGuarded_caveat_violation_fails caveatsAdmit
  reservedField stateStepDev stateStepDev_eq stateStepDev_notReserved stateStepDev_reserved_fails
  stateStepDev_caveat_violation_fails
  incrementNonceStep incrementNonceStep_eq incrementNonceStep_advances
  incrementNonceStep_nonincreasing_fails)
open scoped BigOperators
open Dregg2.Tactics  -- the effect-arm combinators (`reject_none`/`commit_subst`/`gate_peel`/`bal_neutral`)


/-! ## §11 — Axiom-hygiene tripwires (the honesty pins over the widened replacement's keystones). -/

-- The PER-ASSET conservation-vector keystones (FILL 1, phase 2) over the executable turn:
-- The per-asset PER-NODE attestation carrier (the forest lift, §MB) keystones:
-- META-FILL B Wave 1: the 5 PURE-STATE (field/log) effects on the per-asset dispatch.
-- The balance-NEUTRALITY keystone (a field/log write moves NO asset's supply) + the per-effect
-- authority gates + the (re-extended) per-asset spine arms all pinned kernel-clean.

-- §MA-seal (Wave 6): the 6 SIMPLE bal-neutral effects (seal/unseal/createSealPair/makeSovereign/
-- refusal/receiptArchive) — each a `stateStep` field write, balance-NEUTRAL (`recTotalAsset`
-- UNCHANGED ∀ asset), authority-gated (`stateAuthB` over the written cell). The §8 crypto (AEAD /
-- commitment) is the chain-layer portal, NOT proved sound. The keystone
-- `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by construction
-- (FullForestA spine UNCHANGED — only `targetOf` gained arms).
-- FILL #133: MakeSovereign is a VALUE-REBIND (commitment-form), NOT a flag. The faithful kernel move
-- (`cells.remove(id)` + `sovereign_commitments.insert(id, cell.state_commitment())`) + its TEETH: the
-- readable balance/fields are GONE (a flag model CANNOT prove this), the commitment IS present and
-- binds the pre-state, and it stays bal-NEUTRAL on the per-asset ledger (`cell`-only ⇒ `bal` fixed).
-- THE THIRD NONCE-RESET VECTOR, CLOSED: the commitment-form rebind PRESERVES the reserved replay nonce
-- (the readable nonce no longer drops to 0 — `makeSovereign` is now nonce-MONOTONE, the fix that makes
-- `BodyNonceNondecreasing` hold for `makeSovereign` too, dropping the no-replay carve-out).
-- META-FILL B Wave 2: the 6 DISTINCT AUTHORITY effects on the per-asset dispatch. The headline
-- NON-AMPLIFICATION (genuine `capAuthConferred ⊆` over the real `List Auth` lattice) + the
-- teeth (amplifying grant rejected) + grounding/addEdge/removeEdge/graph-unchanged graph moves,
-- all pinned kernel-clean. The keystone `execFullA_attests_per_asset` (re-extended above) carries
-- ALL of these into the forest by construction (FullForestA spine UNCHANGED).
-- META-FILL C Wave 3: accounts-GROWTH (`createCell`/`spawn`, born EMPTY ⇒ conservation-NEUTRAL) +
-- the SUPPLY inflow (`bridgeMint`, §8-portal disclosed `+value` at ONE asset). The account-growth
-- NEUTRALITY keystone (`recTotalAsset` unchanged BECAUSE the fresh cell is born empty, the index set
-- grew) + the disclosed bridge inflow + the per-effect gates, all pinned kernel-clean. The
-- keystone `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by
-- construction (FullForestA spine UNCHANGED — only `targetOf` gains arms).
#assert_axioms recTotalAsset_insert_fresh
#assert_axioms createCellIntoAsset_grows_accounts
-- §MA-factory: the `CreateCellFromFactory` keystones (validation + program-install + frames).
-- META-FILL C: the note chained wrappers + the executed-dispatch obligations.
-- §MA-lifecycle (Wave-3) keystones: the lifecycle state machine + the de-shadowed seal cap-movement.

/-! ## §12 — Non-vacuity: each kind commits with the right invariant; unauthorized rejected.

Reuses `AuthTurn.rsCap` (delegator 0 holds a `node 7` cap) lifted to a `RecChainedState`, and a
minting state where actor 9 holds the privileged `node 0` cap. -/

/-- A chained record state: cells 0,1 with balances 100,5; actor 9 holds a `node 0` mint cap;
delegator 0 holds a `node 7` connectivity cap. Empty receipt chain. -/
def fs0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0]
                         else if l = 0 then [Cap.node 7] else [] }
    log := [] }

-- A DELEGATE turn commits (delegator 0 holds a `node 7` cap ⇒ can delegate connectivity to 7):
#guard ((execFull fs0 (.delegate 0 1 7)).isSome)  --  true
-- ...is conservation-trivial (`recTotal` unchanged) and grows the chain by one:
#guard ((execFull fs0 (.delegate 0 1 7)).map (fun s => recTotal s.kernel)) == some 105  --  some 105 (FIXED)
#guard ((execFull fs0 (.delegate 0 1 7)).map (fun s => s.log.length)) == some 1  --  some 1
-- ...and recipient 1 now holds the `node 7` cap (the new authority edge):
#guard (((execFull fs0 (.delegate 0 1 7)).map (fun s => s.kernel.caps 1)).getD []) == [Cap.node 7]  --  [Cap.node 7]
-- A delegator with no connectivity to the target cannot delegate it (fail-closed):
#guard ((execFull fs0 (.delegate 5 1 9)).isSome) == false  --  false

-- A MINT turn commits (actor 9 holds the privileged `node 0` cap ⇒ may coin cell 0's supply):
#guard ((execFull fs0 (.mint 9 0 50)).isSome)  --  true
-- ...raises `recTotal` by exactly +50 (disclosed non-conservation), chain grows by one:
#guard ((execFull fs0 (.mint 9 0 50)).map (fun s => recTotal s.kernel)) == some 155  --  some 155 (= 105 + 50)
#guard ((execFull fs0 (.mint 9 0 50)).map (fun s => s.log.length)) == some 1  --  some 1
-- ...and the minted receipt carries the disclosed delta +50:
#guard (((execFull fs0 (.mint 9 0 50)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0) == 50  --  50
-- An actor without the privileged mint cap cannot mint (bare ownership is NOT enough):
#guard ((execFull fs0 (.mint 0 0 50)).isSome) == false  --  false (actor 0 lacks `node 0`)

-- A BURN turn commits (actor 9 authorized; cell 0 has ≥ 40 balance):
#guard ((execFull fs0 (.burn 9 0 40)).isSome)  --  true
-- ...lowers `recTotal` by exactly -40 (disclosed), chain grows by one:
#guard ((execFull fs0 (.burn 9 0 40)).map (fun s => recTotal s.kernel)) == some 65  --  some 65 (= 105 - 40)
-- Over-burn (more than available) is rejected (availability gate):
#guard ((execFull fs0 (.burn 9 0 999)).isSome) == false  --  false
-- Unauthorized burn rejected:
#guard ((execFull fs0 (.burn 0 0 10)).isSome) == false  --  false

-- A REVOKE turn always commits (it only subtracts authority) and is conservation-trivial:
#guard ((execFull fs0 (.revoke 0 7)).isSome)  --  true
#guard ((execFull fs0 (.revoke 0 7)).map (fun s => recTotal s.kernel)) == some 105  --  some 105 (FIXED)
-- ...after which holder 0's `node 7` cap is gone:
#guard (((execFull fs0 (.revoke 0 7)).map (fun s => s.kernel.caps 0)).getD []) == []  --  []

-- A BALANCE turn (reusing the catalog-typed `Action`) commits and conserves:
#guard ((execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).isSome)  --  true
#guard ((execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩)).map (fun s => recTotal s.kernel)) == some 105  --  some 105

-- A MIXED full-turn: mint +50, then transfer (conserves), then burn -50 → nets to 0, conserves.
def mixedTurn : List FullAction :=
  [ .mint 9 0 50
  , .balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩
  , .burn 9 0 50 ]

#guard ((execFullTurn fs0 mixedTurn).isSome)  --  true (all-or-nothing commits)
#guard (turnLedgerDelta mixedTurn) == 0  --  0 (+50 +0 -50)
#guard ((execFullTurn fs0 mixedTurn).map (fun s => recTotal s.kernel)) == some 105  --  some 105 (CONSERVED: net 0)
#guard ((execFullTurn fs0 mixedTurn).map (fun s => s.log.length)) == some 3  --  some 3 (chain grew by count)

-- An all-or-nothing transaction with a bad action ROLLS BACK the whole turn:
def badMixedTurn : List FullAction :=
  [ .mint 9 0 50, .burn 0 0 10 ]   -- second action unauthorized ⇒ whole turn none
#guard ((execFullTurn fs0 badMixedTurn).isSome) == false  --  false (rollback)

/-! ## §13 — Non-vacuity for the PER-ASSET executor: conservation holds, laundering is CAUGHT. -/

/-- A chained state with a genuine 2-asset `bal` ledger: cell 0 holds 100 of asset 0 and 7 of asset
1; cell 1 holds 5 of asset 0. Actor 9 holds the privileged `node 0`/`node 1` mint caps over BOTH
issuer cells (W1: asset `a`'s issuer IS cell `a` — mint authority is control of the issuer). -/
def fma0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 1] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

#guard (recTotalAsset fma0.kernel 0) == 105  --  105 (asset 0 supply)
#guard (recTotalAsset fma0.kernel 1) == 7  --  7   (asset 1 supply)
-- A pure per-asset TRANSFER of asset 0 (actor 0 owns src 0) conserves BOTH assets:
#guard ((execFullTurnA fma0 [.balanceA ⟨0, 0, 1, 30⟩ 0]).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-- The pre-W1 scalar-LAUNDERING turn (mint 50 of asset 1 to cell 0 while burning 50 of asset 0
from cell 1's holding): under the supply-increment law the aggregate scalar hid a (−50, +50)
cross-asset move. W1 KILLS the whole channel: mint/burn are issuer-moves, so BOTH actions conserve
BOTH assets EXACTLY — the per-asset vector is identically (0, 0) and the post-state sums are
UNCHANGED. The swap is visible in the ROWS (the issuer wells moved), never in the sums. -/
def launderTurn : List FullActionA :=
  [ .mintA 9 0 1 50      -- mint 50 of asset 1 (issuer = cell 1) into cell 0: well 1 → −50
  , .burnA 9 1 0 5 ]     -- burn cell 1's 5 of asset 0 back into well 0

#guard (turnLedgerDeltaAsset launderTurn 0) == 0  --  0 (W1: burn = return-to-well, conserving)
#guard (turnLedgerDeltaAsset launderTurn 1) == 0  --  0 (W1: mint = issuer-move, conserving)
-- the per-asset ledger AFTER the turn: BOTH supplies unchanged (the W1 exactness, executable):
#guard ((execFullTurnA fma0 launderTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- ...and the ROWS show the actual moves: cell 1's well in asset 1 went NEGATIVE-CAPABLE (0 → −50,
-- the well IS −supply-delta), cell 0 gained 50 of asset 1; cell 1's asset-0 holding returned to
-- well 0 (5 → 0, well 100 → 105):
#guard ((execFullTurnA fma0 launderTurn).map
        (fun s => (s.kernel.bal 1 1, s.kernel.bal 0 1, s.kernel.bal 1 0, s.kernel.bal 0 0)))
        == some (-50, 57, 0, 105)
-- the ISSUER gate has teeth: an actor holding only `node 0` (NOT the issuer of asset 1) cannot
-- mint asset 1 (the legacy recipient-shaped gate would have accepted this):
#guard ((execFullA { fma0 with kernel := { fma0.kernel with
          caps := fun l => if l = 9 then [Cap.node 0] else [] } }
          (.mintA 9 0 1 50)).isNone)
-- self-mint into the issuer's own well is a no-move (rejected by the `a ≠ cell` gate):
#guard ((execFullA fma0 (.mintA 9 1 1 50)).isNone)

/-! ## §13-state — Non-vacuity for the 5 PURE-STATE effects: the cell record/log moves, but
`recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); authority is REAL
(an unauthorized field write fails-closed); `emitEvent` is authority-FREE. -/

/-- A genuine 2-asset state whose cells ALSO carry a `nonce`/`status`/`permissions`/`verification_key`
record (so the pure-state field writes are OBSERVABLE). Cell 0 holds 100 of asset 0 + 7 of asset 1;
cell 1 holds 5 of asset 0. Empty cap table ⇒ authority is by OWNERSHIP (actor = cell). -/
def fmaS : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 0), ("nonce", .int 0),
                                                ("status", .int 0), ("permissions", .int 0),
                                                ("verification_key", .int 0)]
                         else .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#guard ((recTotalAsset fmaS.kernel 0, recTotalAsset fmaS.kernel 1)) == (105, 7)  --  (105, 7)

-- ★ THE RESERVED-SLOT TOOTH (the replay-vector closure, BOTH POLES): a developer `setFieldA` that
--   tries to overwrite the PROTOCOL-managed `nonce` slot is now REJECTED (it used to COMMIT — the
--   nonce-reset replay vector). Only `incrementNonceA` may write `nonce`.
#guard ((execFullA fmaS (.setFieldA 0 0 "nonce" 42)).isNone)  --  true (REJECTED — was some, now none)
-- ...the other three protocol slots are likewise reserved against developer SetField:
#guard ((execFullA fmaS (.setFieldA 0 0 "permissions" 3)).isNone)        --  true (REJECTED)
#guard ((execFullA fmaS (.setFieldA 0 0 "verification_key" 99)).isNone)  --  true (REJECTED)
#guard ((execFullA fmaS (.setFieldA 0 0 "program" 1)).isNone)            --  true (REJECTED)
-- ★ THE BALANCE-NEUTRALITY KEYSTONE on a DEVELOPER field (`status`, NOT reserved): it COMMITS,
--   yet `recTotalAsset` is UNCHANGED at (105, 7) for BOTH assets (balance-NEUTRALITY):
#guard ((execFullA fmaS (.setFieldA 0 0 "status" 42)).isSome)  --  true (developer field still commits)
#guard ((execFullA fmaS (.setFieldA 0 0 "status" 42)).map
        (fun s => fieldOf "status" (s.kernel.cell 0))) == some 42  --  some 42 (CHANGED)
#guard ((execFullA fmaS (.setFieldA 0 0 "status" 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (UNCHANGED)
-- ...and grows the receipt chain by exactly one row (the metadata clock):
#guard ((execFullA fmaS (.setFieldA 0 0 "status" 42)).map (fun s => s.log.length)) == some 1  --  some 1
-- An UNAUTHORIZED actor (9 owns nothing, empty caps) cannot write cell 0's field (fail-closed):
#guard ((execFullA fmaS (.setFieldA 9 0 "status" 42)).isSome) == false  --  false

-- IncrementNonce (Monotonic): bump cell 0's nonce 0→1, balance-neutral:
#guard ((execFullA fmaS (.incrementNonceA 0 0 1)).map (fun s => fieldOf "nonce" (s.kernel.cell 0))) == some 1  --  some 1
#guard ((execFullA fmaS (.incrementNonceA 0 0 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- ★ THE MONOTONE-NONCE TOOTH (the second replay leg, BOTH POLES): cell 0's stored nonce is 0, so an
--   `incrementNonceA` to a STRICTLY-greater value COMMITS, but a RESET (to 0) or a non-advancing
--   value is REJECTED — the dedicated effect can only ADVANCE the nonce.
#guard ((execFullA fmaS (.incrementNonceA 0 0 5)).isSome)   --  true (0 → 5 advances)
#guard ((execFullA fmaS (.incrementNonceA 0 0 0)).isNone)   --  true (0 → 0 is a no-op/non-advance: REJECTED)
#guard ((execFullA fmaS (.incrementNonceA 0 0 (-3))).isNone) --  true (0 → −3 is a RESET: REJECTED)
-- ...and after an advance to 5, a later RESET back to 0 (or any value ≤ 5) is REJECTED (no cycling):
#guard ((execFullA fmaS (.incrementNonceA 0 0 5)).bind
          (fun s5 => execFullA s5 (.incrementNonceA 0 0 0))).isNone   --  true (5 → 0 RESET: REJECTED)
#guard ((execFullA fmaS (.incrementNonceA 0 0 5)).bind
          (fun s5 => execFullA s5 (.incrementNonceA 0 0 5))).isNone   --  true (5 → 5 no-op: REJECTED)
#guard ((execFullA fmaS (.incrementNonceA 0 0 5)).bind
          (fun s5 => execFullA s5 (.incrementNonceA 0 0 6))).isSome   --  true (5 → 6 advances)

-- SetPermissions / SetVerificationKey (Neutral): field writes, balance-neutral:
#guard ((execFullA fmaS (.setPermissionsA 0 0 3)).map (fun s => fieldOf "permissions" (s.kernel.cell 0))) == some 3  --  some 3
#guard ((execFullA fmaS (.setVKA 0 0 99)).map (fun s => fieldOf "verification_key" (s.kernel.cell 0))) == some 99  --  some 99
#guard ((execFullA fmaS (.setVKA 0 0 99)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

-- EmitEvent: authority-FREE (even actor 9, who owns nothing, commits — dregg1 runs NO cap check)
--   but cell-existence-gated; writes NO state, grows the chain by one, balance-neutral:
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).isSome)  --  true (authority-free)
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).map (fun s => s.log.length)) == some 1  --  some 1
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
-- Non-live event targets reject: no ghost-cell event rows.
#guard ((execFullA fmaS (.emitEventA 9 99 7 123)).isSome) == false  --  false
-- §LIVENESS-GATE mutation-confirm: a member-but-DESTROYED cell (cell 0, destroyed by actor 0) is
--   REFUSED both an emit AND a makeSovereign — "Destroyed is terminal" at the executor (CLASS-1).
--   Build the Destroyed state by running `cellDestroyA 0 0` (lifecycle 0 → 3, caps survive), then probe.
#guard ((execFullA fmaS (.cellDestroyA 0 0 777)).bind
          (fun sD => execFullA sD (.emitEventA 9 0 7 123))).isNone  --  true (Destroyed emit refused)
#guard ((execFullA fmaS (.cellDestroyA 0 0 777)).bind
          (fun sD => execFullA sD (.makeSovereignA 0 0))).isNone  --  true (Destroyed makeSovereign refused)
-- ...and the LIVE pole still commits normally (cell 0 is Live by default):
#guard ((execFullA fmaS (.emitEventA 9 0 7 123)).isSome)         --  true (Live emit commits)
#guard ((execFullA fmaS (.makeSovereignA 0 0)).isSome)           --  true (Live makeSovereign commits)

-- A MIXED per-asset turn interleaving pure-state effects with a transfer: ALL balance-neutral
--   (the transfer conserves; the field writes/emit move no asset) ⇒ (105, 7) preserved:
def stateMixedTurn : List FullActionA :=
  [ .setFieldA 0 0 "status" 5
  , .balanceA ⟨0, 0, 1, 30⟩ 0     -- transfer 30 of asset 0, cell 0 → cell 1 (conserves; bumps nonce 0→1)
  , .incrementNonceA 0 0 2        -- §MONOTONE-NONCE: must STRICTLY advance (1 → 2), not reset
  , .emitEventA 0 0 1 0
  , .setVKA 0 0 7 ]

#guard ((execFullTurnA fmaS stateMixedTurn).isSome)  --  true (all commit)
#guard ((turnLedgerDeltaAsset stateMixedTurn 0, turnLedgerDeltaAsset stateMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaS stateMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (CONSERVED)
#guard ((execFullTurnA fmaS stateMixedTurn).map (fun s => s.log.length)) == some 5  --  some 5 (chain grew by node count)

/-! ## §13-auth — Non-vacuity for the 6 DISTINCT AUTHORITY effects: the cap-graph moves (or is
checked), but `recTotalAsset` is UNCHANGED in EVERY asset (balance-NEUTRALITY witnessed); the
HEADLINE non-amplification has TEETH (an attenuation STRICTLY drops a right; an amplifying grant is
REJECTED); fail-closed (introduce/exercise without held connectivity ⇒ none). -/

/-- A 2-asset state whose actor 0 ALSO holds REAL caps: `node 7` (connectivity, for introduce/
exercise/handoff to target 7) and `endpoint 9 [read, write]` (rights-carrying, for attenuation
teeth; the `write` makes it confer connectivity to 9 too). Asset 0 = 105, asset 1 = 7. -/
def fmaA : RecChainedState :=
  { kernel :=
      -- cell 7 is a real (live, empty) account: actor 0 holds `Cap.node 7` to it, so exercising that
      -- cap runs inner effects AGAINST the live target 7 (an under-spec'd fixture before — 7 was a cap
      -- target but not an account, so inner `emitEventA 0 7` fail-closed; #44 triage made it faithful).
      { accounts := {0, 1, 7}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 7, Cap.endpoint 9 [Auth.read, Auth.write]] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply: asset 0 = 105, asset 1 = 7.
#guard ((recTotalAsset fmaA.kernel 0, recTotalAsset fmaA.kernel 1)) == (105, 7)  --  (105, 7)

/-- **`fullActionInvA_nonvacuous`** — the non-vacuity witness the `@[load_bearing]` linter requires:
`fullActionInvA` is NEITHER everywhere-true NOR everywhere-false. It ACCEPTS the committed
`introduceA 0 1 7` against the live fixture `fmaA` (a real per-asset step attests its full invariant,
via `execFullA_attests_per_asset`), and REFUTES any same-state instance `fullActionInvA s fa s` (the
ObsAdvance conjunct demands `s.log.length < s.log.length`, impossible). A vacuous accept-all relation
could not carry the refuted half; a vacuous reject-all could not carry the accepted half. -/
theorem fullActionInvA_nonvacuous :
    (∃ s', execFullA fmaA (.introduceA 0 1 7) = some s' ∧ fullActionInvA fmaA (.introduceA 0 1 7) s')
    ∧ ¬ fullActionInvA fmaA (.introduceA 0 1 7) fmaA := by
  refine ⟨?_, ?_⟩
  · -- ACCEPTED: the fixture step commits and attests its full per-asset invariant.
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (by decide : (execFullA fmaA (.introduceA 0 1 7)).isSome)
    exact ⟨s', hs', execFullA_attests_per_asset hs'⟩
  · -- REFUTED: a same-state instance violates ObsAdvance (`length < length` is irreflexive).
    intro hinv
    unfold fullActionInvA at hinv
    exact Nat.lt_irrefl _ hinv.2.2.1

-- (1) INTRODUCE: actor 0 (holds `node 7`) introduces recipient 1 to target 7. COMMITS, and
--   `recTotalAsset` is UNCHANGED in BOTH assets (caps change, bal does NOT — balance-NEUTRALITY):
#guard ((execFullA fmaA (.introduceA 0 1 7)).isSome)  --  true
#guard ((execFullA fmaA (.introduceA 0 1 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (UNCHANGED)
-- ...and recipient 1 now holds the `node 7` cap (the new authority EDGE — caps DID move):
#guard (((execFullA fmaA (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []) == [Cap.node 7]  --  [Cap.node 7]
-- An introducer with NO connectivity to the target cannot introduce it (FAIL-CLOSED ⇒ none):
#guard ((execFullA fmaA (.introduceA 5 1 7)).isSome) == false  --  false

/-- Actor 0 holds only endpoint-write connectivity to target 7. -/
def fmaEndpointIntro : RecChainedState :=
  { fmaA with
    kernel := { fmaA.kernel with
      caps := fun l => if l = 0 then [Cap.endpoint 7 [Auth.write]] else [] } }

-- INTRODUCE from an endpoint witness copies the endpoint cap; it does not upgrade to `node`/control.
#guard (((execFullA fmaEndpointIntro (.introduceA 0 1 7)).map (fun s => s.kernel.caps 1)).getD []) == [Cap.endpoint 7 [Auth.write]]  -- [Cap.endpoint 7 [Auth.write]]

-- (1') THE TEETH — genuine rights NON-AMPLIFICATION over the real `List Auth` lattice.
-- Attenuating the held `endpoint 9 [read, write]` to keep only `[read]` STRICTLY DROPS `write`:
#guard (capAuthConferred (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])) == [Auth.read])  --  [read] ⊊ [read,write]
-- the genuine non-amplification fires on this concrete held cap (granted ⊆ held, REAL rights):
example : IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write])
    (attenuate [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])) :=
  attenuateF_non_amplifying [Auth.read] (Cap.endpoint 9 [Auth.read, Auth.write])
-- ...and an AMPLIFYING grant is REJECTED: a `node 9` cap confers `control`, which the
-- held `endpoint 9 [read, write]` cap does NOT confer ⇒ it FAILS the non-amplification predicate:
example : ¬ IsNonAmplifyingF (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9) :=
  amplifyingF_rejected (Cap.endpoint 9 [Auth.read, Auth.write]) (Cap.node 9)
    Auth.control (by decide) (by decide)

-- (2) ATTENUATE: narrow actor 0's slot-1 cap (`endpoint 9 [read, write]`) to keep only `read`.
-- COMMITS, balance-neutral, and the slot's cap is narrowed:
#guard ((execFullA fmaA (.attenuateA 0 1 [Auth.read])).isSome)  --  true
#guard (((execFullA fmaA (.attenuateA 0 1 [Auth.read])).map (fun s => s.kernel.caps 0)).getD []) == [Cap.node 7, Cap.endpoint 9 [Auth.read]]  --  [node 7, endpoint 9 [read]] (write DROPPED)
#guard ((execFullA fmaA (.attenuateA 0 1 [Auth.read])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (UNCHANGED)
-- FAIL-CLOSED POLE (the bug fix): actor 0 holds exactly 2 caps (idx 0,1). An OUT-OF-BOUNDS attenuate
-- (idx 2 ≥ length 2) is REFUSED — `none`, NOT a logged no-op `some` + an authReceipt (codex's bug).
#guard ((execFullA fmaA (.attenuateA 0 2 [Auth.read])).isNone)  --  true: none (was a logged no-op)
#guard ((execFullA fmaA (.attenuateA 0 99 [Auth.read])).isNone)  --  true: none

-- (4) REVOKE-DELEGATION: parent drops child 0's edge to 7. Always commits, balance-neutral:
#guard ((execFullA fmaA (.revokeDelegationA 0 7)).isSome)  --  true
#guard ((execFullA fmaA (.revokeDelegationA 0 7)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

-- (6) EXERCISE (DE-SHADOWED): actor 0 (holds `node 7`) exercises its cap to target 7 to RUN inner
--   effects against it (dregg1 `apply.rs:2647`: each inner effect applied against the cap's target).
--   The inner effect (an `emitEvent` against 7) GENUINELY RUNS — the log grows by 2 (the exercise's
--   own receipt + the inner emit receipt), proving it is NOT a no-op shadow. An actor without
--   the held edge FAILS-CLOSED; a FAILING inner effect aborts the whole exercise (fail-closed):
#guard ((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).isSome)  --  true (inner emit against the now-live target 7 RUNS — exercise is no shadow)
#guard (((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).map (fun s => s.log.length)).getD 0) == 2  --  2 (exercise receipt + inner emit receipt)
#guard ((execFullA fmaA (.exerciseA 0 7 [.emitEventA 0 7 99 1])).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (emit is balance-neutral)
-- a committed exercise carrying a balance-MOVING inner (mint 3 of asset 1 into a live cell, by an actor
--   that holds the privileged `node`-cap): the inner mint actually CREDITS — combined delta sums the inner.
#guard ((execFullA fmaA (.exerciseA 0 7 [])).isSome)  --  true (empty inner: pure hold-check)
#guard (((execFullA fmaA (.exerciseA 0 7 [])).map (fun s => s.log.length)).getD 0) == 1  --  1 (only the exercise receipt)
#guard ((execFullA fmaA (.exerciseA 5 7 [.emitEventA 0 7 99 1])).isSome) == false  --  false (FAIL-CLOSED: no held edge)

-- ★★ R4 FACET-MASK TEETH (the canonical-semantics gate BITES). Actor 0 holds `endpoint 9 [read,write]`
--    toward target 9 (its mask is exactly [read,write]) and the privileged `node 7` toward 7 (full mask).
--    The facet of the inner effect — not mere connectivity — decides admission:
#guard (requiredFacetA (.emitEventA 0 9 99 1) == Auth.write)   -- a state write demands `write`
#guard (requiredFacetA (.delegate 0 1 7) == Auth.grant)        -- an authority grant demands `grant`
#guard (capFacetMaskA (heldCapTo fmaA.kernel.caps 0 9) == [Auth.read, Auth.write])  -- endpoint 9's mask
#guard (capFacetMaskA (heldCapTo fmaA.kernel.caps 0 7) == [Auth.read, Auth.write, Auth.grant, Auth.call, Auth.reply, Auth.reset, Auth.control, Auth.notify])  -- node 7 = full (every Auth incl. notify)
-- the [read,write] mask ADMITS a write-facet inner effect (gate passes; the inner emit then runs):
#guard (innerFacetsAdmittedA fmaA 0 9 [.emitEventA 0 9 99 1])  --  true
-- ...but REJECTS a grant-facet inner effect — `grant ∉ [read,write]` — so the WHOLE exercise is `none`
--    EVEN THOUGH actor 0 holds connectivity to 9 (connectivity ≠ facet — the R4 distinction):
#guard (innerFacetsAdmittedA fmaA 0 9 [.delegate 0 1 7]) == false  --  false
#guard ((execFullA fmaA (.exerciseA 0 9 [.delegate 0 1 7])).isSome) == false  --  false (R4 REJECTS the grant)
-- the privileged `node 7` cap (full mask) ADMITS the grant-facet inner effect (control over 7):
#guard (innerFacetsAdmittedA fmaA 0 7 [.delegate 0 1 7])  --  true (node mask contains grant)

-- A MIXED authority turn: introduce (adds edge) + attenuate (narrows) + exercise (RUNS inner emit) +
--   revoke-delegation (removes) — ALL balance-neutral ⇒ (105, 7) preserved across the turn:
def authMixedTurn : List FullActionA :=
  [ .introduceA 0 1 7
  , .attenuateA 0 1 [Auth.read]
  , .exerciseA 0 7 [.emitEventA 0 7 99 1]
  , .revokeDelegationA 0 7 ]

#guard ((execFullTurnA fmaA authMixedTurn).isSome)  --  true (all commit; the exercise inner emit runs against the live target 7)
#guard ((turnLedgerDeltaAsset authMixedTurn 0, turnLedgerDeltaAsset authMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaA authMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (CONSERVED)

/-! ## §13-supply (META-FILL C Wave 3) — Non-vacuity for ACCOUNT-GROWTH + SUPPLY: `createCell` GROWS
`accounts` yet `recTotalAsset` is UNCHANGED (born EMPTY ⇒ NEUTRAL); `bridgeMint` discloses `+value` at
ONE asset and leaves every other asset FIXED (no cross-asset laundering); unauthorized create/mint
FAIL-CLOSED. A 2-asset state where actor 9 holds the privileged `node 0`/`node 1`/`node 2` caps (can mint
into live cells 0,1 and create the fresh cell 2). -/

/-- The supply fixture: accounts {0,1}; cell 0 = 100 of asset 0 + 7 of asset 1, cell 1 = 5 of asset 0.
Actor 9 holds `node 0`,`node 1`,`node 2` (create/mint authority over cells 0,1 and the fresh 2). -/
def fmaSup : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

-- The pre-state per-asset supply + account set: asset 0 = 105, asset 1 = 7, accounts {0,1}.
#guard ((recTotalAsset fmaSup.kernel 0, recTotalAsset fmaSup.kernel 1)) == (105, 7)  --  (105, 7)
#guard ((decide (0 ∈ fmaSup.kernel.accounts), decide (1 ∈ fmaSup.kernel.accounts),
       decide (2 ∈ fmaSup.kernel.accounts))) == (true, true, false)  --  (true, true, false)

-- ★ THE ACCOUNT-GROWTH WITNESS: actor 9 (holds `node 2`) creates the FRESH cell 2 — COMMITS,
--   `accounts` GROWS {0,1} → {0,1,2} (cell 2 now live), YET `recTotalAsset` is UNCHANGED at (105, 7)
--   for BOTH assets (born EMPTY ⇒ conservation-NEUTRAL):
#guard ((execFullA fmaSup (.createCellA 9 2)).isSome)  --  true
#guard ((execFullA fmaSup (.createCellA 9 2)).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true  --  some true (GREW)
#guard ((execFullA fmaSup (.createCellA 9 2)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (NEUTRAL)
-- ...and the fresh cell 2 is born EMPTY in every asset (bal-reset):
#guard ((execFullA fmaSup (.createCellA 9 2)).map (fun s => (s.kernel.bal 2 0, s.kernel.bal 2 1))) == some (0, 0)  --  some (0, 0)
-- ...and grows the receipt chain by exactly one row:
#guard ((execFullA fmaSup (.createCellA 9 2)).map (fun s => s.log.length)) == some 1  --  some 1
-- An UNAUTHORIZED creator (actor 0 holds no create cap) is REJECTED (fail-closed):
#guard ((execFullA fmaSup (.createCellA 0 2)).isSome) == false  --  false
-- A NON-FRESH id (cell 1 already live) is REJECTED (the freshness gate has TEETH):
#guard ((execFullA fmaSup (.createCellA 9 1)).isSome) == false  --  false

-- SPAWN: child creation alone cannot mint authority to an unheld/non-live target:
#guard ((execFullA fmaSup (.spawnA 9 2 7)).isSome) == false  --  false
-- ...but actor 9 can spawn child 2 (born EMPTY) with a COPY of its held parent `node 1` cap — COMMITS,
--   NEUTRAL, and the child carries the concrete copied parent cap (`node 1`):
#guard ((execFullA fmaSup (.spawnA 9 2 1)).isSome)  --  true
#guard ((execFullA fmaSup (.spawnA 9 2 1)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (NEUTRAL)
#guard (((execFullA fmaSup (.spawnA 9 2 1)).map (fun s => s.kernel.caps 2)).getD []) == [Cap.node 1]  --  [Cap.node 1]
#guard ((execFullA fmaSup (.spawnA 9 2 1)).map (fun s => decide (2 ∈ s.kernel.accounts))) == some true  --  some true (GREW)
#guard ((execFullA fmaSup (.spawnA 9 2 1)).map
        (fun s => (s.kernel.delegate 2, s.kernel.delegations 2))) == some (some 9, [Cap.node 0, Cap.node 1, Cap.node 2])  --  some (some 9, [Cap.node 0, Cap.node 1, Cap.node 2])
#guard (((execFullA fmaSup (.spawnA 9 2 1)).bind
        (fun s => execFullA s (.refreshDelegationA 2 2))).isSome)  --  true (spawn initialized parent)

-- ★ THE BRIDGE-MINT WITNESS (W1): actor 9 (holds `node 1` — the BRIDGE cell 1 is the issuer of
--   bridged asset 1) bridge-mints 40 of asset 1 into the live cell 0 — COMMITS, and BOTH supplies
--   are UNCHANGED: the bridge well 1 went −40 (it owes the foreign chain 40) while cell 0 gained 40:
#guard ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).isSome)  --  true
#guard ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (EXACT)
#guard ((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map
        (fun s => (s.kernel.bal 1 1, s.kernel.bal 0 1))) == some (-40, 47)  --  the bridge well IS −outstanding
-- ...the delta family vanishes (W1: NO non-conserving verb is left):
#guard ((ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 0, ledgerDeltaAsset (.bridgeMintA 9 0 1 40) 1)) == (0, 0)  --  (0, 0)
-- ...and the bridge receipt records the truthful well → recipient move of 40:
#guard (((execFullA fmaSup (.bridgeMintA 9 0 1 40)).map (fun s => s.log.headD ⟨0,0,0,0⟩ |>.amt)).getD 0) == 40  --  40
-- An UNAUTHORIZED bridge-mint (actor 0, no mint cap over the bridge cell) is REJECTED (the LOCAL
--   gate, independent of the §8 foreign-finality portal):
#guard ((execFullA fmaSup (.bridgeMintA 0 0 1 40)).isSome) == false  --  false

-- A MIXED supply turn: createCell 2 (neutral growth) + bridgeMint 40 of asset 1 into cell 0
--   (issuer-move) → BOTH assets conserved exactly:
def supplyMixedTurn : List FullActionA :=
  [ .createCellA 9 2
  , .bridgeMintA 9 0 1 40 ]

#guard ((execFullTurnA fmaSup supplyMixedTurn).isSome)  --  true (all commit)
#guard ((turnLedgerDeltaAsset supplyMixedTurn 0, turnLedgerDeltaAsset supplyMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaSup supplyMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §13-seal (Wave 6) — Non-vacuity for the 6 SIMPLE bal-neutral effects: the cell flag/metadata/
refusal record MOVES (a flag flips), yet `recTotalAsset` is UNCHANGED in EVERY asset
(balance-NEUTRALITY witnessed by an `#eval`); authority is REAL (an unauthorized actor fails-closed);
the §8 crypto (AEAD for seal/unseal, the commitment for makeSovereign) is the HONEST chain-layer
portal — NOT exercised here sound. -/

-- Reuse `fmaS` (cell 0 carries a record; empty caps ⇒ authority by OWNERSHIP, actor = cell).
-- Pre-state per-asset supply: asset 0 = 105, asset 1 = 7.

-- `fmaW3` gives cell 0 a 3-cap c-list (for the refresh-snapshot witness) plus a delegation parent
-- (cell 0 is the parent of child 1) for refresh. Asset 0 = 105, asset 1 = 7 (as fmaS).
-- F3: the seal/swiss verb family is FACTORY-DISSOLVED (caps-in-slots, `Apps/CapSlotFactory.lean`,
-- R7 epoch-at-retrieval) — the sealer/unsealer fixture caps became generic endpoint caps.
def fmaW3 : RecChainedState :=
  { kernel :=
      { fmaS.kernel with
        caps := fun l => if l = 0 then [Cap.endpoint 5 [Auth.grant], Cap.endpoint 5 [Auth.reply], Cap.node 42] else []
        delegate := fun c => if c = 1 then some 0 else none }   -- child 1's parent is cell 0
    log := [] }

-- ★ WAVE-3 NON-VACUITY: the cell LIFECYCLE state machine. Seal cell 0 (Live→Sealed), then a destroyed
-- cell REJECTS a follow-on effect (terminal). First, a Live cell seals; a Sealed cell's seal-gate FIRES:
#guard ((execFullA fmaS (.cellSealA 0 0)).isSome)  --  true (Live→Sealed)
#guard ((execFullA fmaS (.cellSealA 0 0)).map (fun s => s.kernel.lifecycle 0)) == some 1  --  some 1 (Sealed)
-- a SEALED cell's lifecycle gate FIRES: it rejects a SECOND seal (AlreadySealed):
#guard (((execFullA fmaS (.cellSealA 0 0)).bind (fun s => execFullA s (.cellSealA 0 0))).isSome) == false  --  false (gate fires)
-- but a SEALED cell CAN be unsealed (Sealed→Live) or destroyed (seal is the prelude to destruction):
#guard (((execFullA fmaS (.cellSealA 0 0)).bind (fun s => execFullA s (.cellUnsealA 0 0))).map
        (fun s => s.kernel.lifecycle 0)) == some 0  --  some 0 (back to Live)
-- ★ A DESTROYED cell is TERMINAL — it REJECTS a follow-on effect. Destroy cell 0 (binds cert 777):
#guard ((execFullA fmaS (.cellDestroyA 0 0 777)).map (fun s => s.kernel.lifecycle 0)) == some 3  --  some 3 (Destroyed)
#guard ((execFullA fmaS (.cellDestroyA 0 0 777)).map (fun s => s.kernel.deathCert 0)) == some 777  --  some 777 (cert bound into final state)
-- a DESTROYED cell rejects a follow-on seal/unseal/destroy (terminal — no further transition):
#guard (((execFullA fmaS (.cellDestroyA 0 0 777)).bind (fun s => execFullA s (.cellSealA 0 0))).isSome) == false  --  false
#guard (((execFullA fmaS (.cellDestroyA 0 0 777)).bind (fun s => execFullA s (.cellDestroyA 0 0 888))).isSome) == false  --  false (terminal)
-- FAIL-CLOSED: an unauthorized actor cannot drive the lifecycle:
#guard ((execFullA fmaS (.cellSealA 9 0)).isSome) == false  --  false

-- ★ WAVE-3 NON-VACUITY: refreshDelegation SNAPSHOTS the parent's CURRENT c-list. Child 1's parent is
-- cell 0 (which holds 3 caps); refresh writes that snapshot into child 1:
#guard ((execFullA fmaW3 (.refreshDelegationA 1 1)).isSome)  --  true (self-authorized, has parent 0)
#guard ((execFullA fmaW3 (.refreshDelegationA 1 1)).map (fun s => (s.kernel.delegations 1).length)) == some 3  --  some 3 (parent cell 0's 3 caps snapshotted)
-- FAIL-CLOSED: a cell with NO parent (cell 0, delegate = 0) cannot refresh:
#guard ((execFullA fmaW3 (.refreshDelegationA 0 0)).isSome) == false  --  false (no parent)

-- ★ FILL #133 — MakeSovereign is a VALUE-REBIND, not a flag. dregg1's `make_sovereign` REMOVES the
--   readable cell (`cells.remove(id)`) and keeps ONLY a 32-byte commitment (`sovereign_commitments`).
--   The rebound cell carries the commitment-only record; the host can NO LONGER read its state.
-- (a) it commits (the self-sovereign authority gate holds: actor = cell = owner):
#guard ((execFullA fmaS (.makeSovereignA 0 0)).isSome)  --  true
-- (b) ★ THE TEETH: the pre-state `balance` is NO LONGER directly readable — the record was DROPPED
--     behind the commitment (a flag model leaves it readable; this is the §8-portal boundary):
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => (Value.scalar (s.kernel.cell 0) "balance").isNone)) == some true  -- some none (UNREADABLE)
-- permissions/balance/value are DROPPED behind the commitment, but the RESERVED replay nonce SURVIVES
-- (readable + equal to the pre-state nonce) — the third nonce-reset vector closed, no-replay monotone:
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => ((s.kernel.cell 0).field "permissions").isNone && ((s.kernel.cell 0).field "balance").isNone)) == some true  -- some (none, none) (host state DROPPED)
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => ((s.kernel.cell 0).scalar nonceField).getD 0)) == some (((fmaS.kernel.cell 0).scalar nonceField).getD 0)  -- nonce PRESERVED (not reset to 0)
-- (c) the COMMITMENT is present — a digest of the FULL pre-state value (`cell.state_commitment()`):
#guard (match (execFullA fmaS (.makeSovereignA 0 0)).map
              (fun s => (s.kernel.cell 0).field commitmentField) with
        | some (some (Value.dig d)) => d == stateCommitment (fmaS.kernel.cell 0)
        | _ => false)  --  some (some (Value.dig …)) (PRESENT)
#guard (match sovereignRebind fmaS.kernel.cell 0 0 with
        | Value.record fs =>
          match fs.find? (fun p => p.1 == commitmentField) with
          | some (_, Value.dig d) => d == stateCommitment (fmaS.kernel.cell 0) && fs.length == 2
          | _ => false
        | _ => false)  --  the rebound record IS commitment + reserved-nonce (length 2)
-- ...and DISTINCT pre-states give DISTINCT commitments (the binding is a function of the whole value):
#guard ((stateCommitment (.record [("balance", .int 0)]) == stateCommitment (.record [("balance", .int 1)]))) == false  --  false (binds value)
-- (d) bal-NEUTRAL on the per-asset ledger (the value moves behind the commitment on the HOST, not the
--     per-asset supply — `recTotalAsset` reads `bal`, independent of the rebound `cell` record):
#guard ((execFullA fmaS (.makeSovereignA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (SUPPLY PRESERVED)
-- (e) FAIL-CLOSED: an unauthorized actor (9 owns nothing) cannot make cell 0 sovereign:
#guard ((execFullA fmaS (.makeSovereignA 9 0)).isSome) == false  --  false (FAIL-CLOSED)

-- Refusal: write the `refusal` audit record (dregg1 bumps nonce + records commitment; NEVER touches
--   balance/caps/value), balance-neutral:
#guard ((execFullA fmaS (.refusalA 0 0)).map (fun s => fieldOf "refusal" (s.kernel.cell 0))) == some 1  --  some 1
#guard ((execFullA fmaS (.refusalA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
#guard ((execFullA fmaS (.refusalA 9 0)).isSome) == false  --  false (FAIL-CLOSED)

-- ReceiptArchive (DEPLOYED semantics): move the `lifecycle` SIDE-TABLE to Archived (4) — the
--   cellSeal/cellDestroy shape (`c.archive(checkpoint)`), NOT a `cell` record-slot write — balance-neutral:
#guard ((execFullA fmaS (.receiptArchiveA 0 0)).map (fun s => s.kernel.lifecycle 0)) == some lcArchived  --  some 4
#guard ((execFullA fmaS (.receiptArchiveA 0 0)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
#guard ((execFullA fmaS (.receiptArchiveA 9 0)).isSome) == false  --  false (FAIL-CLOSED, unauthorized)
-- ...and a NON-Live (sealed) cell cannot be archived (the liveness leg of auditGuard fails):
#guard ((execFullA { fmaS with kernel := setLifecycle fmaS.kernel 0 lcSealed } (.receiptArchiveA 0 0)).isSome) == false  --  false (FAIL-CLOSED, non-live)

-- Every lifecycle/refresh effect's per-asset ledgerDelta is 0 at every asset (balance-NEUTRAL):
#guard ((ledgerDeltaAsset (.cellSealA 0 0) 1,
       ledgerDeltaAsset (.cellDestroyA 0 0 777) 0, ledgerDeltaAsset (.refreshDelegationA 1 1) 1)) == (0, 0, 0)  --  (0, 0, 0)

-- A MIXED per-asset turn interleaving a bal-neutral refresh with a transfer: balance moves ONLY by the
--   transfer delta ⇒ (105, 7) preserved as a TOTAL; the chain grows by node count. (F3: the old
--   seal→balance→unseal spine moved to the caps-in-slots factory, `Apps/CapSlotFactory.lean`.)
def sealMixedTurn : List FullActionA :=
  [ .refreshDelegationA 1 1            -- child 1 refreshes its parent snapshot (bal-neutral)
  , .balanceA ⟨0, 0, 1, 30⟩ 0 ]        -- transfer 30 of asset 0, cell 0 → cell 1 (conserves)

#guard ((execFullTurnA fmaW3 sealMixedTurn).isSome)  --  true (all commit on the cap-rich fixture)
#guard ((turnLedgerDeltaAsset sealMixedTurn 0, turnLedgerDeltaAsset sealMixedTurn 1)) == (0, 0)  --  (0, 0)
#guard ((execFullTurnA fmaW3 sealMixedTurn).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (CONSERVED)
#guard ((execFullTurnA fmaW3 sealMixedTurn).map (fun s => s.log.length)) == some 2  --  some 2 (chain grew by node count)
-- the snapshot moved: child 1's delegation snapshot is the parent's 3-cap c-list:
#guard ((execFullTurnA fmaW3 sealMixedTurn).map (fun s => (s.kernel.delegations 1).length)) == some 3  --  some 3 (snapshot taken)

/-! ## §MA-factory NON-VACUITY — `createCellFromFactoryA` validates + installs the program, end-to-end.

A `subscription` factory (vk 42) publishes: `head` is `Monotonic` (the subscription head only advances),
`owner` is `Immutable` (registered forever), with conforming initial fields. We show: an UNKNOWN vk
rejects; the conforming factory MINTS a fresh cell + INSTALLS its caveats; and a later `SetField` to the
minted cell that VIOLATES an installed caveat is REJECTED BY THE EXECUTOR (the whole point — the
published app-safety is enforced, not merely carried). -/

/-- A subscription factory: `head` Monotonic, `owner` Immutable; born `head=0, owner=9` (conforming). -/
def subFactory : FactoryEntry :=
  { caveats := [.monotonic "head", .immutable "owner"]
    initialFields := [("head", 0), ("owner", 9)]
    programVk := 7 }

/-- The factory registry maps vk 42 → `subFactory`; actor 0 holds the PRIVILEGED minter cap
`Cap.node 5` over the fresh cell 5 (creation is privileged supply — `mintAuthorizedB`, not ownership). -/
def facS : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => .record [("balance", .int 0)]
                caps := fun l => if l = 0 then [Cap.node 5] else []
                factories := [(42, subFactory)] }
    log := [] }

/-- A malformed factory attempting to initialize the reserved scalar `balance` field. -/
def badBalanceFactory : FactoryEntry :=
  { caveats := []
    initialFields := [(balanceField, 999)]
    programVk := 7 }

def facBadBalanceS : RecChainedState :=
  { facS with kernel := { facS.kernel with factories := [(43, badBalanceFactory)] } }

-- The factory's own declared initial state CONFORMS to its own caveats (validate_and_record):
#guard (subFactory.conforms)  --  true
-- A factory cannot smuggle scalar `balance` through initial fields; per-asset `bal` is born empty:
#guard (badBalanceFactory.conforms) == false  --  false
#guard ((execFullA facBadBalanceS (.createCellFromFactoryA 0 5 43)).isSome) == false  --  false
-- An UNKNOWN factory vk (99 ∉ registry) is REJECTED (fail-closed, apply.rs:3140):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 99)).isSome) == false  --  false
-- The conforming factory (vk 42) MINTS the fresh cell 5 (born EMPTY ⇒ conservation-neutral):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).isSome)  --  true
-- ...and INSTALLS the factory's slot caveats onto the minted cell (the constructor-transparency keystone):
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).map
        (fun s => reprStr (s.kernel.slotCaveats 5)) == reprStr subFactory.caveats)  --  some "[…monotonic head, immutable owner]"
-- ...and writes the factory's initial fields + program VK onto the cell:
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).map
        (fun s => (fieldOf "head" (s.kernel.cell 5), fieldOf "owner" (s.kernel.cell 5),
                   fieldOf factoryVkField (s.kernel.cell 5)))) == some (0, 9, 7)  --  some (0, 9, 7)

-- THE TEETH: from the MINTED cell, a later `SetField` to the installed-caveat slots is gated BY THE
-- EXECUTOR — an Immutable `owner` rewrite (9→8) is REJECTED; a non-monotone `head` write (0→ −1 would
-- decrease) is REJECTED; a monotone `head` advance (0→3) is ADMITTED:
#guard (((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "owner" 8))).isSome) == false  --  false (Immutable owner: registered forever)
#guard (((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "head" (-1)))).isSome) == false  --  false (Monotonic head: cannot decrease)
#guard (((execFullA facS (.createCellFromFactoryA 0 5 42)).bind
        (fun s => execFullA s (.setFieldA 0 5 "head" 3))).map
        (fun s => fieldOf "head" (s.kernel.cell 5))) == some 3  --  some 3 (monotone advance admitted)
-- A factory whose OWN initial state violates its caveats is REJECTED at mint (validate_and_record):
#guard ((FactoryEntry.conforms { caveats := [.boundedBy "x" 0 10], initialFields := [("x", 99)], programVk := 0 })) == false  --  false

-- §MA-factory NEGATIVE-VK ATTACK (codex P1): `findFactory … vk.toNat` would map every negative `vk`
-- to key `0` (`Int.toNat (-1) = 0`), so a negative `vk` could ALIAS factory `0`. `fac0S` parks the
-- subscription factory at key `0` (the alias target); the guard rejects `vk = -1` BEFORE the lookup.
def fac0S : RecChainedState :=
  { facS with kernel := { facS.kernel with factories := [(0, subFactory)] } }
-- The honest call with the real non-negative key `0` MINTS (the factory lives at `0`):
#guard ((execFullA fac0S (.createCellFromFactoryA 0 5 0)).isSome)  --  true
-- THE ATTACK: `vk = -1` does not alias factory `0` — it is REJECTED before `findFactory`:
#guard ((execFullA fac0S (.createCellFromFactoryA 0 5 (-1))).isSome) == false  --  false (no aliasing)
-- ...and is rejected even when the alias target is a conforming, mintable factory at key `0`:
#guard ((createCellFromFactoryChainA fac0S 0 5 (-1)).isSome) == false  --  false
-- A legit non-negative `vk` against the original (key-42) registry still works unchanged:
#guard ((execFullA facS (.createCellFromFactoryA 0 5 42)).isSome)  --  true

/-! ### §MA-pipelined-send #eval — the apply-time NEUTRAL marker on the executed dispatch.
(F2b: the queue atomic-batch / pipeline-step fixtures died with the queue verb family — queue
behavior is the factory story, `Apps/{QueueFactory,InboxFactory,PubsubFactory}.lean`.) -/

def fmaP : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
        bal := fun c a => if c = 0 ∧ a = 0 then 50 else 0 }
    log := [] }

-- ★ PIPELINED-SEND — the apply-time NEUTRAL marker (the EventualRef resolution is `ConditionalTurn`'s
--   batch; AT apply the resolved action already ran, so this is a balance-neutral clock row that COMMITS):
#guard ((execFullA fmaP (.pipelinedSendA 0)).isSome)  --  true — apply-time neutral commits
#guard ((execFullA fmaP (.pipelinedSendA 0)).map
        (fun s => (recTotalAsset s.kernel 0, s.log.length))) == some (50, 1)  --  some (50, 1) — NEUTRAL + one clock row

/-! ## §14 — the axiom-hygiene pin, placed LAST on purpose (see the note). -/

-- ⚑ 2026-07-24 PILOT (axiom-pin migration, MEASURED). The 126 per-theorem
-- `#assert_axioms` lines that used to sit in §11-§13 are replaced by the ONE
-- namespace pin below. MEASURED on this tree: it pins 293 theorems kernel-clean
-- (`#assert_namespace_axioms Dregg2.Exec.TurnExecutorFull: 293 theorems pinned
-- kernel-clean`) versus the 126 the explicit lines covered — 2.3x the coverage,
-- because it also reaches every theorem in the `.Scalar` and `.PerAsset` halves
-- that the hand-written list never enumerated.
--
-- ⚠ TWO pins are DELIBERATELY RETAINED below and must NOT be folded in:
--   `recTotalAsset_insert_fresh` and `createCellIntoAsset_grows_accounts` are
--   `Dregg2.Exec.*`, NOT `Dregg2.Exec.TurnExecutorFull.*` — they only resolved
--   bare here because of the `open Dregg2.Exec` above. The namespace pin does
--   NOT cover them; deleting them would SILENTLY drop 2 keystones.
--
-- ⚠ PLACEMENT MATTERS: this command pins only what is ALREADY ELABORATED when it runs.
--   Measured: sitting at the top of §11 it reported 292; moved here (last) it reports 293 —
--   it was silently missing this file's own `fullActionInvA_nonvacuous` (§12, line ~339).
--   A namespace pin belongs at the END of the file. A per-theorem pin has no such trap.
--
-- ⚠ TRADEOFF, recorded honestly: every name this file pins is defined in ANOTHER
--   module (this file declares 1 theorem). A per-theorem pin fails LOUDLY if its
--   theorem is renamed/removed; the namespace pin just covers one fewer, SILENTLY.
--   Coverage went up, tripwire sharpness went down. Do not mass-apply this without
--   that trade being acceptable per-file. See docs/ORPHAN-TRIAGE-2026-07-24.md.
#assert_namespace_axioms Dregg2.Exec.TurnExecutorFull

end Dregg2.Exec.TurnExecutorFull

