/-
# Dregg2.Apps.PrivacyVoting — private voting as a verified cell-program (vote-as-nullifier WriteOnce slots).

`apps/privacy-voting/` and `starbridge-apps/privacy-voting/` model a privacy-preserving ballot: each
enfranchised voter casts EXACTLY ONE vote, with double-vote prevention keyed by a per-voter nullifier
mark kept disjoint from the commitment queue. This module is the **ungated cell-program dual** of
`PrivacyVotingGated` — the SAME ballot discipline runs through the shipped credential-blind executor
`execFullForestA`, with load-bearing guarantees enforced by `stateStepGuarded` reading the ballot cell's
factory-installed `WriteOnce` per-voter nullifier slots.

Headline guarantees (kernel-native, no §8 credential leg):

  * **NO DOUBLE-VOTE** — a second cast over an already-recorded nullifier slot is rejected by the
    executor's `WriteOnce` caveat (`pv_no_double_vote`).
  * **CONSERVATION** — every committed cast is balance-neutral (`SetField` Δ = 0).
  * **NON-VACUITY** — concrete `ballot0` state with `#guard` witnesses mirroring the gated app.

The executed dual of `MultisigVote`'s nullifier-set discipline is the SLOT caveat: the ballot cell's
per-voter `WriteOnce` field IS the on-chain spent-mark. Templates: `Apps/PrivacyVotingGated.lean`
(domain + caveats), `Apps/GovernedNamespace.lean` (ungated `setFieldA` shape).
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest

namespace Dregg2.Apps.PrivacyVoting

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState (stateStepGuarded caveatsAdmit fieldOf
  stateStepGuarded_caveat_violation_fails)

/-! ## §1 — The ballot DOMAIN (cell, per-voter nullifier slots, WriteOnce caveats). -/

abbrev ballotCell : CellId := 0
abbrev ballotActor : CellId := 0

abbrev voterNullA : FieldName := "null_A"
abbrev voterNullB : FieldName := "null_B"

def ballotCaveats : List SlotCaveat :=
  [ .writeOnce voterNullA, .writeOnce voterNullB ]

/-! ## §2 — Cast-vote as a REAL executor turn (`setFieldA` through `execFullForestA`). -/

def castVote (voterSlot : FieldName) (mark : Int) : FullForestA :=
  ⟨ .setFieldA ballotActor ballotCell voterSlot mark, [] ⟩

/-! ## §3 — No-double-vote teeth (executor-enforced WriteOnce, credential-blind). -/

theorem pv_no_double_vote (s : RecChainedState) (voterSlot : FieldName) (mark : Int)
    (hvoted : caveatsAdmit s.kernel voterSlot ballotActor ballotCell mark = false) :
    execFullForestA s (castVote voterSlot mark) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s voterSlot ballotActor ballotCell mark hvoted
  rw [execFullForestA_eq_execFullTurnA]
  simp only [castVote, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

/-! ## §4 — Conservation (ballot metadata is balance-orthogonal). -/

theorem castVote_delta_zero (voterSlot : FieldName) (mark : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (castVote voterSlot mark)) b = 0 := by
  simp [castVote, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem pv_cast_conserves (s s' : RecChainedState) (voterSlot : FieldName) (mark : Int) (b : AssetId)
    (h : execFullForestA s (castVote voterSlot mark) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (castVote voterSlot mark) b h
    (castVote_delta_zero voterSlot mark b)

/-! ## §5 — NON-VACUITY: `ballot0` + `#guard` witnesses (mirrors `PrivacyVotingGated.ballot0`). -/

def ballot0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (voterNullA, .int 7), (voterNullB, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then ballotCaveats else [] }
    log := [] }

-- (i) voter B's FIRST cast over a FRESH nullifier slot COMMITS:
#guard ((execFullForestA ballot0 (castVote voterNullB 9)).isSome)  --  true
#guard ((execFullForestA ballot0 (castVote voterNullB 9)).map
        (fun s => fieldOf voterNullB (s.kernel.cell 0))) == some 9  --  some 9

-- (ii) NO DOUBLE-VOTE: voter A re-casting a DIFFERENT mark over recorded `null_A = 7` ⇒ none:
#guard (caveatsAdmit ballot0.kernel voterNullA ballotActor ballotCell 13) == false  --  false
#guard ((execFullForestA ballot0 (castVote voterNullA 13)).isSome) == false  --  false
-- ...re-writing the SAME recorded nullifier (7) is a WriteOnce no-op and is admitted:
#guard (caveatsAdmit ballot0.kernel voterNullA ballotActor ballotCell 7)  --  true

-- (iii) CONSERVATION: a committed cast moves NO asset's supply:
#guard ((execFullForestA ballot0 (castVote voterNullB 9)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §6 — Axiom-hygiene pins. -/

#assert_axioms pv_no_double_vote
#assert_axioms castVote_delta_zero
#assert_axioms pv_cast_conserves

end Dregg2.Apps.PrivacyVoting