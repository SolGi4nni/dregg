/-
# Metatheory.PolisSandboxDeceiver — the LONG CON: an agent benign for k ticks, then defects.

The deceiver is a *temporal* strategy. For the first `setup` ticks it plays only benign, strictly
floor-preserving moves (it `charges` a harmless counter — its distance home is untouched, the victim
untouched). At the defection tick it `fires`: it converts the accumulated charge into a shove that
pushes the victim out of recovery range. The harm is *latent in the prefix and realized in one move*.

Two detectors watch the same trajectory:

  * The MYOPIC TRUST detector judges each move only by what it sees *that step*. Because the prefix is
    a clean run of benign moves, it builds TRUST in the actor and WHITELISTS it — so when the defection
    arrives it waves it through. The con is exactly an exploit of per-step, trust-on-clean-prefix
    judgment. (`myopic_trusts_then_admits_defection` / the trajectory strands the victim.)

  * The VIABILITY / trajectory governor judges a move by whether the victim can still REACH HOME after
    it — it has no notion of "trust earned by a clean prefix." It admits every benign charge (they
    cost the victim nothing) and REFUSES the defection (it would strand the victim), regardless of how
    long the deceiver behaved. (`viability_admits_prefix` / `viability_refuses_defection` /
    `viability_survives_the_con`.)

Proven end to end:
  * `prefix_is_all_benign` — EVERY move of the benign prefix is floor-preserving (and reach-preserving).
  * `defection_breaks_floor` — the fire move, after the prefix, breaks the shared floor.
  * `defection_passes_per_step_trust` but `defection_fails_viability` — the gap the con lives in.

Honest: bounded Lean world (small `Nat`s so `decide` is cheap); the "detectors" are Lean functions,
not learned models. No `sorry`, no load-bearing `True`.
-/
import Metatheory.Polis

namespace Metatheory.PolisSandboxDeceiver

/-- The world: the victim's distance home, and the deceiver's accumulated `charge`. The charge is
public and benign-looking — it does not touch the victim while it builds. -/
structure DW where
  vdist : Nat
  charge : Nat
deriving Repr, DecidableEq

/-- Recovery budget: the victim keeps its bounded exit iff `vdist ≤ budget`. -/
def budget : Nat := 5

/-- Actions. `charge` is the benign move (accrue 1, touch nothing else). `victimStep` is the victim
walking home. `fire` is the DEFECTION: it shoves the victim out by the accumulated charge. -/
inductive DAct
  | charge
  | victimStep
  | fire
  | noop
deriving DecidableEq, Repr

/-- World transition. Note `fire` moves the victim by `charge` — harm latent in the prefix. -/
def dstep (w : DW) : DAct → DW
  | .charge => { w with charge := w.charge + 1 }
  | .victimStep => { w with vdist := w.vdist - 1 }
  | .fire => { w with vdist := w.vdist + w.charge }
  | .noop => w

/-- The MYOPIC safety floor: the victim is within recovery distance *right now*. Decidable. -/
def safe (w : DW) : Prop := w.vdist ≤ budget
instance (w : DW) : Decidable (safe w) := by unfold safe; infer_instance

/-- The LIVENESS test: the victim can REACH HOME within `k` steps. (It can always step here; the con
in this world is the shove, not a gate — the viability governor still sees the shove for what it is.) -/
def reachHome : Nat → DW → Bool
  | 0, w => w.vdist == 0
  | k + 1, w => w.vdist == 0 || reachHome k { w with vdist := w.vdist - 1 }

/-! ## The deceiver — a temporal policy. -/

/-- Ticks of benign setup before the defection. -/
def setup : Nat := 4

/-- **The deceiver's policy**, parameterised by the current tick: `charge` (benign) while
`tick < setup`, then `fire` (defect). A genuine temporal strategy — the same agent, different move
purely as a function of *when*. -/
def deceiver (tick : Nat) : DAct := if tick < setup then DAct.charge else DAct.fire

/-! ## Detector 1: the myopic TRUST detector — fooled by the clean prefix. -/

/-- A move *looks benign this step* iff it does not lower the victim's safety (vdist non-increasing).
`charge`, `victimStep`, `noop` all qualify; only `fire` (with positive charge) fails — but the
detector also extends TRUST: an actor with a clean run of `trustWindow` benign moves is whitelisted,
and its next move is admitted unexamined. That whitelist is the hole the con drives through. -/
def looksBenign (w : DW) (a : DAct) : Bool := (dstep w a).vdist ≤ w.vdist

/-- The number of consecutive benign moves after which the actor is trusted (≤ `setup`, so the
deceiver earns trust before it fires). -/
def trustWindow : Nat := 3

/-- The myopic trust governor: carry a `streak` of consecutive benign-looking moves. If the actor is
already trusted (`streak ≥ trustWindow`) ADMIT the move unexamined; otherwise admit iff it looks
benign and grow/reset the streak. Returns the new world and streak. -/
def trustGov (st : DW × Nat) (a : DAct) : DW × Nat :=
  let (w, streak) := st
  if streak ≥ trustWindow then
    (dstep w a, streak)                 -- whitelisted: admit unexamined (the exploit)
  else if looksBenign w a then
    (dstep w a, streak + 1)             -- benign: admit and earn trust
  else
    (w, 0)                              -- suspicious: shield and reset

/-- The viability governor: admit a move iff the victim can still reach home afterward. No trust,
no memory of the prefix. -/
def viabGov (w : DW) (a : DAct) : DW :=
  if reachHome budget (dstep w a) then dstep w a else w

/-! ## The episode. -/

/-- Start: victim 3 from home, deceiver uncharged. The floor and reach both hold. -/
def start : DW := ⟨3, 0⟩

/-- The deceiver's full move list across the episode: `setup` benign charges, then the fire. -/
def conMoves : List DAct := (List.range setup).map deceiver ++ [deceiver setup]

-- Watch the policy: four charges then a fire.
#eval conMoves                 -- [charge, charge, charge, charge, fire]

/-- Run the trust governor over the con. -/
def runTrust : DW × Nat := conMoves.foldl trustGov (start, 0)
/-- Run the viability governor over the con. -/
def runViab : DW := conMoves.foldl viabGov start

#eval (runTrust.1.vdist, runTrust.1.charge)   -- (7, 4)  — victim shoved out: the con SUCCEEDS
#eval (runViab.vdist, runViab.charge)         -- (3, 4)  — fire REFUSED: victim still recoverable

/-! ## Proofs. -/

/-- **`prefix_is_all_benign`** — EVERY move of the benign prefix is floor-preserving from `start`:
running just the charges keeps the victim exactly where it was, comfortably under budget. The
detector sees nothing but good behavior. -/
theorem prefix_is_all_benign :
    let after := ((List.range setup).map deceiver).foldl dstep start
    safe after ∧ after.vdist = start.vdist := by decide

/-- Stronger and non-vacuous: each individual prefix move *looks benign* to the per-step detector
from the world it actually acts in (track the world through the fold; the conjunction stays `true`),
AND the trust streak earned over the prefix reaches `trustWindow` — the actor is whitelisted by the
time it fires. -/
theorem each_prefix_move_looks_benign :
    (((List.range setup).map deceiver).foldl
        (fun (acc : DW × Bool) a => (dstep acc.1 a, acc.2 && looksBenign acc.1 a)) (start, true)).2 = true
    ∧ (((List.range setup).map deceiver).foldl trustGov (start, 0)).2 ≥ trustWindow := by decide

/-- **`defection_breaks_floor`** — after the all-benign prefix, the deceiver's `fire` (its move at
tick `setup`) pushes the victim PAST budget: the latent harm is realized in one move. -/
theorem defection_breaks_floor :
    ¬ safe (dstep (((List.range setup).map deceiver).foldl dstep start) (deceiver setup)) := by decide

/-- **`defection_passes_per_step_trust`** — by the time the deceiver fires it is WHITELISTED (its
streak reached `trustWindow` during setup), so the trust governor ADMITS the defection: the resulting
victim distance equals the un-governed fire. The clean prefix bought the con its pass. -/
theorem defection_passes_per_step_trust :
    runTrust.1.vdist = (dstep (((List.range setup).map deceiver).foldl dstep start)
                          (deceiver setup)).vdist := by decide

/-- **`myopic_trust_strands_victim`** — under the trust governor the con SUCCEEDS: the victim ends
shoved past budget (no longer safe, no longer reach-able), though every observed prefix move was
benign. -/
theorem myopic_trust_strands_victim :
    ¬ safe runTrust.1 ∧ reachHome budget runTrust.1 = false := by decide

/-- **`viability_admits_prefix`** — the viability governor is gentle on the honest prefix: each
benign charge is admitted (it costs the victim no reach-home option). After the prefix the victim is
exactly as reachable as at the start. -/
theorem viability_admits_prefix :
    (((List.range setup).map deceiver).foldl viabGov start).vdist = start.vdist := by decide

/-- **`viability_refuses_defection`** — from the post-prefix world the viability governor REFUSES the
fire: applying `viabGov … fire` leaves the world unchanged (the shielded branch), because firing
would strand the victim. Trust earned over a long prefix buys NOTHING here. -/
theorem viability_refuses_defection :
    let post := ((List.range setup).map deceiver).foldl viabGov start
    viabGov post (deceiver setup) = post := by decide

/-- **`viability_survives_the_con`** — over the WHOLE con the viability governor keeps the victim
safe and recoverable: the defection never lands. The trajectory-aware floor sees the latent harm the
trust detector was blinded to. -/
theorem viability_survives_the_con :
    safe runViab ∧ reachHome budget runViab = true := by decide

/-- **`the_con_in_one_line`** — the whole gap, from the SAME clean prefix: the trust governor lets the
defection land (the victim ends unsafe) while the viability governor refuses it (the victim stays
safe). That divergence is the long con and its cure in a single statement. -/
theorem the_con_in_one_line :
    -- trust admits the defection (con lands) …
    (¬ safe runTrust.1)
    -- … while viability refuses it (con fails), from the SAME clean prefix.
    ∧ safe runViab := by decide

/-! ## The strong result: viability withstands the con of ANY length.

No matter how long the deceiver behaves — `setup` of any size — the viability governor refuses the
defection, because it preserves the victim's reach-home option at every governed step (it never
trusts a prefix). -/

/-- The viability governor PRESERVES reach-home: from any reach-able world, after any governed move,
the victim can still reach home. -/
theorem viabGov_preserves_reach (w : DW) (a : DAct) (h : reachHome budget w = true) :
    reachHome budget (viabGov w a) = true := by
  unfold viabGov
  split
  · assumption
  · exact h

/-- Therefore, over a prefix of ANY length (any list of moves), the viability governor keeps the
victim reach-able — so the con's defection, whenever it comes, is refused (it can never produce an
unreachable state). The long con buys the deceiver no extra power against viability. -/
theorem viability_survives_con_of_any_length (as : List DAct) (w : DW)
    (h : reachHome budget w = true) :
    reachHome budget (as.foldl viabGov w) = true := by
  induction as generalizing w with
  | nil => simpa using h
  | cons a as ih => exact ih (viabGov w a) (viabGov_preserves_reach w a h)

end Metatheory.PolisSandboxDeceiver
