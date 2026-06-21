/-
# Metatheory.PolisSandboxUnified — ONE world, THREE leverage dimensions at once.

Every prior sandbox isolates a single lever: `PolisSandbox` foreclosure (distance-to-home),
`PolisSandboxLongGame` the slow strand, `PolisSandboxN` the coalition. A real political actor does not
pick one — it MIXES them. This is the richest single sandbox: one world carrying three simultaneous
forms of leverage, one combined floor that bounds all three at once, one governor that admits a move
iff the WHOLE floor survives it, and one observatory that reads a per-tick verdict off public state.

The three dimensions, each a recognizable abuse:
  * **Foreclosure** — each agent's `dist` to home; a `trap` pushes a victim past its recovery budget
    (it can no longer exit). Floor: every `dist ≤ budget`.
  * **Laundering** — each agent's `claimed` tier vs its `earned` tier; a `launder` inflates the claim
    above what was earned (authority without production). Floor: every `claimed ≤ earned`.
  * **Hoarding** — a shared `pool` (a commons); a `hoard` drains it below the reserve every agent
    relies on. Floor: `pool ≥ reserve`.

The combined floor is the conjunction; it is Decidable, so the governor is computable and every claim
below is `decide`-checked on the live world. A single MIXED adversary deploys all three moves in one
episode:
  * UNGOVERNED — all three detectors fire (`mixed_ungoverned_all_dims_break`): a victim foreclosed,
    a tier laundered, the pool hoarded.
  * GOVERNED — the SAME adversary, under the combined envelope, is refused at every step that would
    break ANY dimension; the whole floor holds across the episode (`mixed_governed_all_prevented`),
    and honest play still flows (`honest_play_flows`).
  * `sandbox_governed_safe` — the floor holds at every tick for EVERY controller (the constitution's
    `polis_safety`, now over a three-axis world). Plus both-polarity non-vacuity: the floor is
    genuinely satisfiable AND genuinely breakable on each axis.

Honest scope: a small finite world (two agents, `decide`-cheap); the adversary is a scripted /
bounded Lean function, not an LLM — but it genuinely mixes strategies and the governance is proven
universal over controllers. No `sorry`, no load-bearing `True`.
-/
import Metatheory.Polis

namespace Metatheory.PolisSandboxUnified

/-- Two agents, for a `decide`-cheap world. -/
abbrev AgentId := Bool

/-- The public world, carrying all three leverage dimensions at once.
  * `dist`   — each agent's distance-to-home (foreclosure axis); `0` = home.
  * `claimed`— each agent's claimed authority tier (laundering axis, numerator).
  * `earned` — each agent's earned authority tier (laundering axis, the honest denominator).
  * `pool`   — the shared commons (hoarding axis). -/
structure World where
  dist : AgentId → Nat
  claimed : AgentId → Nat
  earned : AgentId → Nat
  pool : Nat

/-- Recovery budget: an agent keeps its bounded exit iff `dist ≤ budget`. -/
def budget : Nat := 5
/-- A trap pushes the victim past recovery. -/
def trapDist : Nat := 99
/-- The commons reserve: the pool must never fall below this. -/
def reserve : Nat := 3
/-- How much one `hoard` move drains. -/
def hoardAmt : Nat := 10

/-- An action mixing all three levers. -/
inductive Act
  /-- do nothing. -/
  | noop
  /-- step toward your OWN home (honest progress on the foreclosure axis). -/
  | stepHome
  /-- earn one tier honestly (honest progress on the laundering axis). -/
  | earnTier
  /-- claim EXACTLY what you earned (the lawful counterpart of `launder`). -/
  | claim
  /-- contribute one unit to the commons (honest progress on the hoarding axis). -/
  | contribute
  /-- FORECLOSE: push `victim` past recovery. -/
  | trap (victim : AgentId)
  /-- LAUNDER: inflate your claimed tier above what you earned. -/
  | launder
  /-- HOARD: drain the shared pool below the reserve. -/
  | hoard
deriving DecidableEq, Repr

/-- A scheduled move: which agent acts, and how (the controller's public proposal). -/
structure Move where
  actor : AgentId
  action : Act
deriving Repr

/-- Apply `actor`'s action to the world. Each action touches exactly the axis it abuses (or advances),
leaving the others alone. -/
def act (w : World) (actor : AgentId) : Act → World
  | .noop => w
  | .stepHome => { w with dist := fun i => if i = actor then w.dist i - 1 else w.dist i }
  | .earnTier => { w with earned := fun i => if i = actor then w.earned i + 1 else w.earned i }
  | .claim => { w with claimed := fun i => if i = actor then w.earned i else w.claimed i }
  | .contribute => { w with pool := w.pool + 1 }
  | .trap v => { w with dist := fun i => if i = v then trapDist else w.dist i }
  | .launder => { w with claimed := fun i => if i = actor then w.earned i + 1 else w.claimed i }
  | .hoard => { w with pool := w.pool - hoardAmt }

/-- One world step from a move. -/
def stepMove (w : World) (m : Move) : World := act w m.actor m.action

/-! ## The three floors, and the combined floor. -/

/-- **Foreclosure floor**: every agent retains its bounded exit. -/
def foreclosureFloor (w : World) : Prop := w.dist false ≤ budget ∧ w.dist true ≤ budget
/-- **Laundering floor**: no agent claims more authority than it earned. -/
def launderingFloor (w : World) : Prop := w.claimed false ≤ w.earned false ∧ w.claimed true ≤ w.earned true
/-- **Hoarding floor**: the commons stays above the reserve. -/
def hoardingFloor (w : World) : Prop := reserve ≤ w.pool

/-- **The combined floor**: all three dimensions hold at once. Decidable. -/
def worldFloor (w : World) : Prop := foreclosureFloor w ∧ launderingFloor w ∧ hoardingFloor w

instance (w : World) : Decidable (foreclosureFloor w) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (w : World) : Decidable (launderingFloor w) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (w : World) : Decidable (hoardingFloor w) :=
  inferInstanceAs (Decidable (reserve ≤ w.pool))
instance (w : World) : Decidable (worldFloor w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The polis-governed step**: admit the proposed move iff it preserves the WHOLE combined floor
(all three axes), else SHIELD (no-op). One envelope, every dimension. -/
def govStep (w : World) (m : Move) : World :=
  if worldFloor (stepMove w m) then stepMove w m else w

/-- A governed episode: iterate the governed step under a controller. -/
def govTraj (ctrl : World → Move) (w0 : World) : Nat → World
  | 0 => w0
  | n + 1 => govStep (govTraj ctrl w0 n) (ctrl (govTraj ctrl w0 n))

/-- The governed step preserves the combined floor (admit-or-shield). -/
theorem govStep_preserves (w : World) (m : Move) (h : worldFloor w) : worldFloor (govStep w m) := by
  unfold govStep
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- **`sandbox_governed_safe` — governance, proven over a three-axis world.** Under the polis-governed
step, the combined floor (foreclosure ∧ laundering ∧ hoarding) holds at EVERY tick for EVERY
controller: no agent is ever foreclosed, no tier ever laundered, the commons never hoarded — whatever
the controller does. The live-world `polis_safety`, now multi-dimensional. -/
theorem sandbox_governed_safe (ctrl : World → Move) (w0 : World) (h0 : worldFloor w0) :
    ∀ n, worldFloor (govTraj ctrl w0 n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact govStep_preserves _ _ ih

/-- Gentle governance, half 1: a floor-preserving move is admitted unchanged. -/
theorem govStep_admits_benign (w : World) (m : Move) (hb : worldFloor (stepMove w m)) :
    govStep w m = stepMove w m := by
  unfold govStep; rw [if_pos hb]

/-- Gentle governance, half 2: every refusal is a genuine floor-breaking move (on SOME axis). -/
theorem govStep_refuses_only_harmful (w : World) (m : Move) (h : govStep w m ≠ stepMove w m) :
    ¬ worldFloor (stepMove w m) := by
  unfold govStep at h
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-! ## The experiment: a MIXED adversary, ungoverned vs governed. -/

/-- Genesis: both agents home, no laundering, a healthy commons. The whole floor holds. -/
def w0 : World := { dist := fun _ => 0, claimed := fun _ => 0, earned := fun _ => 0, pool := 10 }

/-- The combined floor genuinely holds at genesis (non-vacuity: SATISFIABLE). -/
theorem genesis_floor_holds : worldFloor w0 := by decide

/-- A compact public read-out of all three axes for the observatory. -/
def view (w : World) : (Nat × Nat) × (Nat × Nat) × (Nat × Nat) × Nat :=
  ((w.dist false, w.dist true), (w.claimed false, w.claimed true),
   (w.earned false, w.earned true), w.pool)

/-- The MIXED adversary's three moves (agent `false` is the politician):
  * forecloses agent `true` (foreclosure),
  * launders its OWN tier above earned (laundering),
  * hoards the shared pool (hoarding). -/
def adv_trap : Move := ⟨false, .trap true⟩
def adv_launder : Move := ⟨false, .launder⟩
def adv_hoard : Move := ⟨false, .hoard⟩
def mixedEpisode : List Move := [adv_trap, adv_launder, adv_hoard]

def runRaw (ms : List Move) (w : World) : World := ms.foldl stepMove w
def runGov (ms : List Move) (w : World) : World := ms.foldl govStep w

/-! ### The per-tick observatory: read the verdict off public state, ungoverned vs governed. -/

-- UNGOVERNED: the mixed adversary breaks all three axes —
-- true foreclosed (dist 99), false laundered (claimed 1 > earned 0), pool drained (0 < reserve 3).
#eval view (runRaw mixedEpisode w0)   -- ((0,99),(1,0),(0,0),0)
#eval decide (worldFloor (runRaw mixedEpisode w0))   -- false  (the floor is broken)

-- GOVERNED: every floor-breaking move is refused; the world is untouched, all axes intact.
#eval view (runGov mixedEpisode w0)   -- ((0,0),(0,0),(0,0),10)
#eval decide (worldFloor (runGov mixedEpisode w0))   -- true   (the floor holds)

/-- **UNGOVERNED — all three dimensions break.** The mixed adversary forecloses a victim, launders a
tier, AND hoards the commons; each detector fires on public state, no interior inspected. -/
theorem mixed_ungoverned_all_dims_break :
    ¬ foreclosureFloor (runRaw mixedEpisode w0) ∧
    ¬ launderingFloor (runRaw mixedEpisode w0) ∧
    ¬ hoardingFloor (runRaw mixedEpisode w0) := by decide

/-- … and therefore the combined floor breaks (the unified verdict). -/
theorem mixed_ungoverned_floor_breaks : ¬ worldFloor (runRaw mixedEpisode w0) := by decide

/-- **GOVERNED — all three dimensions prevented.** The SAME mixed adversary, under the combined
envelope, has every harmful move refused; the whole floor holds across the entire episode. -/
theorem mixed_governed_all_prevented : worldFloor (runGov mixedEpisode w0) := by decide

/-- … and concretely, the governed world is unchanged from genesis — no axis moved. (`view` captures
all six per-agent fields plus the pool, the full content of a `Bool`-agent world.) -/
theorem mixed_governed_world_intact : view (runGov mixedEpisode w0) = view w0 := by decide

/-! ### Honest play flows: governance is gentle on the legitimate counterpart of each abuse. -/

/-- The honest episode: agent `false` steps home, earns a tier, legitimately claims it, and
contributes to the commons — the lawful counterpart of each abuse, one per axis. -/
def honestEpisode : List Move :=
  [⟨false, .stepHome⟩, ⟨false, .earnTier⟩, ⟨false, .claim⟩, ⟨false, .contribute⟩]

/-- A world where agent `false` has earned a tier (so a claim up to it would be legitimate). -/
def wEarned : World := { dist := fun _ => 0, claimed := fun _ => 0, earned := fun i => if i = false then 1 else 0, pool := 10 }

-- HONEST play under governance: every legitimate move is ADMITTED; the world advances normally.
#eval view (runGov honestEpisode w0)   -- ((0,0),(1,0),(1,0),11)  (earned+claimed a tier, grew the commons)

/-- **`honest_play_flows`** — under the SAME governor, honest play is admitted unchanged: stepping
home, earning a tier, and contributing all pass (none breaks any floor). Governance refuses only
abuse, never legitimate exercise. -/
theorem honest_play_flows : view (runGov honestEpisode w0) = view (runRaw honestEpisode w0) := by decide

/-- And the honest world still satisfies the whole floor — legitimate activity stays inside it. -/
theorem honest_play_stays_inside_floor : worldFloor (runGov honestEpisode w0) := by decide

/-- A legitimate claim (claim a tier you HAVE earned) is admitted: from `wEarned`, agent `false`'s
honest claim passes the laundering floor, so the governor admits it unchanged — it distinguishes
earned authority from laundered. (Via `govStep_admits_benign`; the side condition is `decide`-checked.) -/
theorem legitimate_claim_admitted :
    govStep wEarned ⟨false, .claim⟩ = stepMove wEarned ⟨false, .claim⟩ :=
  govStep_admits_benign wEarned ⟨false, .claim⟩ (by decide)

/-! ## Both-polarity non-vacuity: each axis is genuinely satisfiable AND genuinely breakable.

A floor that can never be broken is vacuous (the governor would do nothing); a floor that can never be
satisfied is unusable. Each of the three axes is shown TRUE on some world and FALSE on another, so the
combined floor — and the governance built on it — is non-vacuous on every dimension. -/

/-- Foreclosure axis: holds at genesis, breaks under a trap. -/
theorem foreclosure_nonvacuous :
    foreclosureFloor w0 ∧ ¬ foreclosureFloor (stepMove w0 adv_trap) := by decide
/-- Laundering axis: holds at genesis, breaks under a launder. -/
theorem laundering_nonvacuous :
    launderingFloor w0 ∧ ¬ launderingFloor (stepMove w0 adv_launder) := by decide
/-- Hoarding axis: holds at genesis, breaks under a hoard. -/
theorem hoarding_nonvacuous :
    hoardingFloor w0 ∧ ¬ hoardingFloor (stepMove w0 adv_hoard) := by decide

/-- **Both-polarity non-vacuity, unified**: the combined floor is genuinely satisfiable (genesis) AND
genuinely breakable on EACH axis (so no clause is dead weight). -/
theorem worldFloor_both_polarity :
    worldFloor w0 ∧ ¬ worldFloor (stepMove w0 adv_trap)
            ∧ ¬ worldFloor (stepMove w0 adv_launder)
            ∧ ¬ worldFloor (stepMove w0 adv_hoard) := by decide

/-- And governance is non-vacuous: the mixed adversary's first move is actually REFUSED — the move
would break the floor (`govStep_refuses_only_harmful` contrapositive), so the governor shields and the
world is unchanged. The governor does real work, not a no-op that happens to be safe. -/
theorem governance_does_real_work : view (govStep w0 adv_trap) = view w0 := by decide

/-- The shield is a genuine refusal: the trapped result actually fails the floor (so the equality
above is the governor REJECTING, not the move being harmless). -/
theorem governance_refusal_is_genuine : ¬ worldFloor (stepMove w0 adv_trap) := by decide

end Metatheory.PolisSandboxUnified
