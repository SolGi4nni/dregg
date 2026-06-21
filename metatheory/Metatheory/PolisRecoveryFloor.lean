/-
# Metatheory.PolisRecoveryFloor — the non-lock-in viability floor, bound to the DEPLOYED rotate verb.

This binds the abstract `PolisViability` bounded game to the deployed KERI pre-rotation recovery
(`Dregg2.Apps.PreRotation`). The toy `dist ≤ B` floor of `PolisViability.demoArena` is REPLACED by
the real recovery predicate: **the identity can still rotate/recover** — there exists an admissible
rotation event (one exhibiting the committed next-set preimage, `rotateStep … = some _`) reaching a
state that holds the council's designated recovery key set.

The public option-space is exactly the deployed recovery surface:

* **a `Config`** = `RecoveryView Key` = the public `KeyState` (the exposed `current` set + the
  committed `nextDigest`) plus the council's PUBLIC recovery roster — the finite list of key sets
  the council may lawfully present (KERI's pre-committed next set, plus any friend-council fallbacks)
  and the digest of the recovery target it is trying to (re)gain control under. Nothing here is the
  controller's private intent; it is the published recovery constitution.
* **`floorOk`** = "control is recoverable right now": the current state already commits to a roster
  member as its next set, so a present-able rotation exists. DECIDABLE (a `List.any` of `DecidableEq`
  on `Int`), public — never an interior peek.
* **`enabledMoves`** = each roster key set is a public legal move (present it as a rotation event).
* **`advReact`** = the deployed `rotateStep` outcome: an admitted move advances to the installed
  state (carrying the roster forward); a refused move is the empty response — the move "wasn't a
  move", so it cannot help the subject (fail-closed, exactly as the deployed verb is).

Then `PolisViability.viableWithinB` over this arena IS the **real bounded recovery game**: the
council can GUARANTEE it still controls a recovery key set within `k` public rotations, against an
adversary scheduling among the council's own legal responses. `Foreclosed` = the deployed lock-in:
no bounded sequence of admissible rotations regains a designated set (the exit-foreclosure, as a
game over the live verb).

## Honest framing

This is a **BOUNDED, PUBLIC, DECIDABLE** binding. `floorOk` reads only the published roster + the
cell's committed digests (no private keys, no controller intent); viability is decided by a finite
`k`-bounded game. It does NOT model coercion economics, off-protocol key custody, or "is the council
honest" — those are not public-decidable and are out of scope by construction. What it captures
faithfully: under the deployed `rotateStep` semantics, whether a *committed* recovery path of length
`≤ k` to a designated set EXISTS. The crypto floor (`KeySetCR`) lives in the deployed module; here we
witness the GAME, not re-prove the hash.

l4v bar: no `sorry`, no load-bearing `:= True`; the floor is `Bool`-valued and non-vacuous both
polarities (a recoverable view passes; a locked-out view is foreclosed). `#guard`s execute both.
-/
import Metatheory.PolisViability
import Dregg2.Apps.PreRotation

namespace Metatheory.PolisRecoveryFloor

open Metatheory.PolisViability
open Dregg2.Apps.PreRotation

variable {Key : Type}

/-- **The public recovery view** — the `Config` of the recovery arena. It is the published recovery
surface of an identity-as-council cell: the live `KeyState` (exposed `current` + committed
`nextDigest`), the council's PUBLIC `roster` of key sets it may lawfully present (the pre-committed
next set and any friend-council fallbacks), and the digest of the recovery `target` it seeks to
(re)control. No private controller state; this is the recovery constitution, in the open. -/
structure RecoveryView (Key : Type) where
  /-- The live key state of the identity cell (the deployed `KeyState`). -/
  state  : KeyState Key
  /-- The council's PUBLIC recovery roster: the key sets it may lawfully present. -/
  roster : List (List Key)
  /-- The digest of the designated recovery key set the council seeks to control. -/
  target : Int

/-- **`recoverableNow` — the deployed non-lock-in floor (DECIDABLE, `Bool`).** Control is
recoverable *right now* iff some roster member can be presented as an admissible rotation: i.e. the
current committed `nextDigest` is the hash of a roster set (so `rotateStep` would admit it). This is
the real floor — "the identity can still rotate/recover" — replacing the toy `dist ≤ B`. Reads only
the published roster + the cell's committed digest; no interior. -/
def recoverableNow (hash : List Key → Int) (V : RecoveryView Key) : Bool :=
  V.roster.any (fun ks => hash ks == V.state.nextDigest)

/-- **`recoveryArena` — the deployed recovery as a `PolisViability.Arena`.**

* `floorOk`     = `recoverableNow`: a present-able admissible rotation exists.
* `enabledMoves`= the roster sets the deployed verb actually ADMITS from this state (the public
  legal move-set: you can only "move" by a rotation `rotateStep` accepts — a refused presentation
  is no move at all, so it cannot be a spurious vacuous win).
* `advReact`    = the deployed `rotateStep` outcome of presenting an (already-admitted) set with the
  recovery `target` as its fresh next-commitment: the rotation advances to the installed state
  (roster + target carried forward, so the game continues from the real post-state). A move offered
  by `enabledMoves` is always admitted, so `advReact` always has exactly the one real successor —
  no empty (vacuously-winning) response set.

Faithfulness note: gating `enabledMoves` on actual admission is the deployed semantics, NOT a cheat
— the public option-space IS "the rotations the live verb accepts". `recoverableNow_iff_present_admits`
ties `floorOk` to this exact admission set. -/
def recoveryArena (hash : List Key → Int) : Arena (RecoveryView Key) (List Key) where
  floorOk V := recoverableNow hash V
  enabledMoves V :=
    V.roster.filter (fun ks =>
      (rotateStep hash V.state { newKeys := ks, freshNext := V.target }).isSome)
  advReact V ks :=
    match rotateStep hash V.state { newKeys := ks, freshNext := V.target } with
    | some st => [{ V with state := st }]
    | none    => []

/-- **`RecoveryViable` — the REAL bounded recovery game.** The council can GUARANTEE it still
controls a designated recovery set within `k` public rotations, against adversarial scheduling among
its own legal responses. This is `PolisViability.viableWithinB` over the deployed verb — the
deployed non-lock-in property, decidable. -/
def RecoveryViable (hash : List Key → Int) (k : Nat) (V : RecoveryView Key) : Prop :=
  Viable (recoveryArena hash) k V

/-- **`RecoveryForeclosed` — deployed lock-in as a GAME.** No bounded sequence of admissible
rotations regains a designated set: the exit-foreclosure over the live recovery verb. -/
def RecoveryForeclosed (hash : List Key → Int) (k : Nat) (V : RecoveryView Key) : Prop :=
  Foreclosed (recoveryArena hash) k V

instance (hash : List Key → Int) (k : Nat) (V : RecoveryView Key) :
    Decidable (RecoveryViable hash k V) :=
  inferInstanceAs (Decidable (Viable (recoveryArena hash) k V))
instance (hash : List Key → Int) (k : Nat) (V : RecoveryView Key) :
    Decidable (RecoveryForeclosed hash k V) :=
  inferInstanceAs (Decidable (Foreclosed (recoveryArena hash) k V))

/-- **The recovery-floor CaptureBar**, on the deployed recovery view. The politician's lock-in —
driving the identity cell into a state with NO bounded admissible recovery — is barred EXACTLY when
the bounded recovery game is `Foreclosed`, decidable from the public recovery view alone. -/
def recoveryFloorBar (hash : List Key → Int) (k : Nat) :=
  viabilityBar (recoveryArena hash) k

/-! ### The bridge lemma: the floor `recoverableNow` IS the present-able admissible rotation.

This is the load-bearing tie between the abstract floor and the deployed `rotateStep`: the decidable
`floorOk` holds for a view iff some roster set is admitted by the live rotate verb from that view's
state. So the game's base case is literally "the deployed verb would commit". -/

/-- **`recoverableNow_iff_present_admits`.** The floor holds iff some roster key set, presented as a
rotation event (with the recovery target as its fresh next), is ADMITTED by the deployed
`rotateStep`. The abstract floor and the deployed verb agree on the base case. -/
theorem recoverableNow_iff_present_admits (hash : List Key → Int) (V : RecoveryView Key) :
    recoverableNow hash V = true ↔
      ∃ ks ∈ V.roster,
        rotateStep hash V.state { newKeys := ks, freshNext := V.target }
          = some { current := ks, nextDigest := V.target } := by
  unfold recoverableNow
  rw [List.any_eq_true]
  constructor
  · rintro ⟨ks, hmem, hbeq⟩
    refine ⟨ks, hmem, ?_⟩
    have hg : hash ks = V.state.nextDigest := by simpa using (beq_iff_eq).1 hbeq
    unfold rotateStep; rw [if_pos hg]
  · rintro ⟨ks, hmem, hstep⟩
    refine ⟨ks, hmem, ?_⟩
    have hg : hash ks = V.state.nextDigest := rotate_exhibits_preimage hstep
    simpa using (beq_iff_eq).2 hg

/-! ## Non-vacuity, both polarities, EXECUTED.

`tinyHash` is the deployed module's fast injective demo hash. We build a recoverable view (the
committed next-set is on the roster, within reach) and a locked-out view (the committed next-set is
on NOBODY's roster — no admissible rotation, so foreclosed at any budget). The `#guard`s run the
real bounded game over the deployed `rotateStep`. -/

/-- A RECOVERABLE view: current state commits to `[3,4]`, which IS on the council's roster, and the
recovery target is the digest of `[5,6]` (itself on the roster, so the next link is reachable too). -/
def recoverableView : RecoveryView Nat :=
  { state  := { current := [1, 2], nextDigest := tinyHash [3, 4] }
    roster := [[3, 4], [5, 6]]
    target := tinyHash [5, 6] }

/-- A LOCKED-OUT view: the state commits to `[7,8]`, which is on NOBODY's roster — no roster set
hashes to the committed next, so no admissible rotation exists. Lock-in, by the deployed verb. -/
def lockedOutView : RecoveryView Nat :=
  { state  := { current := [1, 2], nextDigest := tinyHash [7, 8] }
    roster := [[3, 4], [5, 6]]
    target := tinyHash [5, 6] }

-- The floor itself: recoverable view passes, locked-out view fails (non-vacuous, both polarities):
#guard recoverableNow tinyHash recoverableView == true
#guard recoverableNow tinyHash lockedOutView == false

-- The REAL bounded game over the deployed rotate verb:
-- recoverable within budget 3 (present [3,4] → state now commits [5,6] → floor already holds there):
#guard viableWithinB (recoveryArena tinyHash) 3 recoverableView == true
-- locked-out: foreclosed even at a generous budget — no admissible rotation, ever:
#guard viableWithinB (recoveryArena tinyHash) 5 lockedOutView == false

-- The bar fires EXACTLY on the locked-out view, and NOT on the recoverable one:
example : (recoveryFloorBar tinyHash 5).badShape lockedOutView := by
  show RecoveryForeclosed tinyHash 5 lockedOutView; decide
example : ¬ (recoveryFloorBar tinyHash 3).badShape recoverableView := by
  show ¬ RecoveryForeclosed tinyHash 3 recoverableView; decide

-- And the Prop-level wrappers decide:
example : RecoveryViable tinyHash 3 recoverableView := by decide
example : RecoveryForeclosed tinyHash 5 lockedOutView := by decide

/-! ## Axiom hygiene: the bridge lemma pins {propext, Classical.choice, Quot.sound}. -/

#assert_axioms recoverableNow_iff_present_admits

end Metatheory.PolisRecoveryFloor
