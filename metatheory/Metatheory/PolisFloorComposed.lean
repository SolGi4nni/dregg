/-
# Metatheory.PolisFloorComposed — the FIRST composed politician floor over DEPLOYED real bars.

Every prior composed floor (`PolisTrace.multiAgentExitFloor` / `politicianFloor`) folds the
*candidate* per-shape bars (`rExitForeclosureBar` over a toy `RState`, `flowCaptureBar` over a toy
`Proc`). This file folds the **DEPLOYED** recovery bar — `PolisRecoveryFloor.recoveryFloorBar`, the
bounded recovery game bound to the live KERI pre-rotation verb (`Dregg2.Apps.PreRotation.rotateStep`)
— over a common public trace, via the exact deployed composition primitives (`CaptureBar.pullback`,
`CaptureBar.or`). This is the first politician floor whose constituent bars are bound to the real,
green, deployed substrate.

## The common trace

A `CouncilTrace` is one interleaved run of PUBLIC recovery events: each event names which council
(`Bool` — two identity-as-council cells sharing a polis) presented its recovery view at that step.
NO interior — a `RecoveryView Nat` is the published recovery constitution (live `KeyState` + public
roster + recovery target), exactly the `Config` of the deployed `recoveryArena`. The trace is a list
of these public presentations.

PUBLIC projections `projView true / projView false` extract each council's LATEST presented recovery
view (its current public recovery posture). `CaptureBar.pullback` carries the deployed
`recoveryFloorBar tinyHash k` to the common trace for each council; `CaptureBar.or` folds the two —
the multi-agent recovery floor: NO council in the polis is driven into bounded recovery-foreclosure
along the shared interleaved run.

## Honest framing (the headline)

This stays **BOUNDED, PUBLIC, DECIDABLE**. The bar fires iff, reading only the published recovery
views in the trace, some council's bounded `k`-rotation recovery game (over the deployed
`rotateStep`) is `Foreclosed`. It does NOT solve politics — it captures one decidable trace-shape
(bounded recovery-foreclosure) over the live recovery verb, composed across the two councils.
`captureBar_exactly_floor_violation` gives that the composed bar bars EXACTLY the union floor
violation (no astrology, no forgotten case). Non-vacuity is EXECUTED both polarities below.

l4v bar: no `sorry`, no load-bearing `:= True`; the floor is decidable and bites both ways (a trace
where both councils stay recoverable clears; a trace where one council locks itself out is caught).
-/
import Metatheory.PolisRecoveryFloor
import Metatheory.PolisViability
import Metatheory.Polis

namespace Metatheory.PolisFloorComposed

open Metatheory.Polis
open Metatheory.PolisViability
open Metatheory.PolisRecoveryFloor
open Dregg2.Apps.PreRotation

/-- A PUBLIC recovery event: which council acted, and the `RecoveryView` it presented (the
published recovery posture — live key state + public roster + recovery target). NO interior. -/
structure CouncilEvent where
  actor : Bool
  view  : RecoveryView Nat

/-- The common trace: one interleaved run of two councils' public recovery presentations. -/
abbrev CouncilTrace := List CouncilEvent

/-- A neutral default recovery view (recoverable, trivial roster) for a council that never acted —
its committed next is on its own roster, so the bounded game is trivially viable: a council that has
made NO public move cannot be said to be foreclosed. -/
def defaultView : RecoveryView Nat :=
  { state := { current := [], nextDigest := tinyHash [] }, roster := [[]], target := tinyHash [] }

/-- **Public projection** — council `B`'s LATEST presented recovery view (its current public recovery
posture). If `B` never acted, the neutral recoverable `defaultView`. Interior-free, computable. -/
def projView (B : Bool) (τ : CouncilTrace) : RecoveryView Nat :=
  match (τ.filter (fun e => e.actor == B)).getLast? with
  | some e => e.view
  | none   => defaultView

/-- Council `B`'s DEPLOYED recovery-foreclosure bar (`recoveryFloorBar tinyHash k`), pulled back to
the common trace via the public latest-view projection. -/
def recoveryBarU (B : Bool) (k : Nat) :
    CaptureBar CouncilTrace (fun τ => Foreclosed (recoveryArena tinyHash) k (projView B τ)) :=
  (recoveryFloorBar tinyHash k).pullback (projView B)

/-- **`dreggPoliticianFloor` — the composed floor over the DEPLOYED bars.** No council in the polis
is driven into bounded recovery-foreclosure along the shared interleaved trace: the `or`-fold (over
the two councils) of the pulled-back deployed `recoveryFloorBar`. ONE `CaptureBar` over ONE common
trace, decidable and interior-free — the first composed politician floor whose constituents are the
green, deployed recovery bar bound to the live `rotateStep` verb. -/
def dreggPoliticianFloor (k : Nat) :
    CaptureBar CouncilTrace
      (fun τ => Foreclosed (recoveryArena tinyHash) k (projView true τ)
              ∨ Foreclosed (recoveryArena tinyHash) k (projView false τ)) :=
  (recoveryBarU true k).or (recoveryBarU false k)

/-- **The composition law transports.** The composed floor bars EXACTLY its union floor-violation:
some council's bounded recovery game is foreclosed along the trace. No astrology, no forgotten
council — the deployed `captureBar_exactly_floor_violation` applies verbatim to the
pullback/or-folded composition. -/
theorem dreggPoliticianFloor_exact (k : Nat) (τ : CouncilTrace) :
    (dreggPoliticianFloor k).badShape τ ↔
      (Foreclosed (recoveryArena tinyHash) k (projView true τ)
        ∨ Foreclosed (recoveryArena tinyHash) k (projView false τ)) :=
  captureBar_exactly_floor_violation (dreggPoliticianFloor k) τ

/-! ## Non-vacuity, both polarities, EXECUTED over the deployed recovery verb.

`recoverableView` and `lockedOutView` are the deployed module's witnesses: the former commits to a
roster-member next set (recoverable within budget); the latter commits to a next set on NOBODY's
roster (foreclosed at any budget). We build interleaved council traces from them and run the composed
floor's decidable `badShape` directly. -/

/-- A polis trace where BOTH councils present recoverable views — the composed floor CLEARS it. -/
def healthyTrace : CouncilTrace :=
  [ { actor := true,  view := recoverableView }
  , { actor := false, view := recoverableView } ]

/-- A polis trace where council `false` locks ITSELF out (commits to an off-roster next set) while
council `true` stays recoverable — the composed floor CATCHES it (on the `false` disjunct). -/
def captiveTrace : CouncilTrace :=
  [ { actor := true,  view := recoverableView }
  , { actor := false, view := lockedOutView } ]

-- The projections land the intended latest views (sanity, computable):
#guard (projView true  healthyTrace).state.nextDigest == recoverableView.state.nextDigest
#guard (projView false captiveTrace).state.nextDigest == lockedOutView.state.nextDigest

-- The composed floor CLEARS the healthy trace (neither council foreclosed at budget 3):
example : ¬ (dreggPoliticianFloor 3).badShape healthyTrace := by
  rw [dreggPoliticianFloor_exact]
  show ¬ (Foreclosed (recoveryArena tinyHash) 3 (projView true healthyTrace)
        ∨ Foreclosed (recoveryArena tinyHash) 3 (projView false healthyTrace))
  decide

-- The composed floor CATCHES the captive trace (council `false` is recovery-foreclosed at budget 5):
example : (dreggPoliticianFloor 5).badShape captiveTrace := by
  rw [dreggPoliticianFloor_exact]
  exact Or.inr (by show Foreclosed (recoveryArena tinyHash) 5 (projView false captiveTrace); decide)

-- And the catch is genuinely on the LOCKED-OUT council, not the recoverable one:
example : ¬ Foreclosed (recoveryArena tinyHash) 5 (projView true captiveTrace) := by
  show ¬ Foreclosed (recoveryArena tinyHash) 5 (projView true captiveTrace); decide
example : Foreclosed (recoveryArena tinyHash) 5 (projView false captiveTrace) := by decide

/-! ## Axiom hygiene: the composition-exactness theorem is kernel-clean. -/

#assert_axioms dreggPoliticianFloor_exact

end Metatheory.PolisFloorComposed
