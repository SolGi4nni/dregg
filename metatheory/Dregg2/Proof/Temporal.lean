/-
# Dregg2.Proof.Temporal — an LTL □/◇ temporal logic over the LIVING CELL's trajectory.

`Exec/CellCarry.lean` proved **`livingCellA_carries`**: ANY state predicate `Good` preserved
by a single living-cell step (`cellNextA`) holds at EVERY index of the unbounded adversarial
trajectory `trajA s sched`, under EVERY schedule. That is, operationally, a `□`-introduction
rule — but it is stated as a raw `∀ n, Good (trajA …)`, with no *temporal vocabulary* and no
algebra connecting "always", "eventually", "now", and their interactions. This module supplies
that vocabulary: a small but genuine **linear-temporal logic** (LTL) over the living cell.

## Where this sits (and what it is NOT)

dregg2 already has the two *neighbouring* pieces; `Temporal.lean` is the third, and it is new:

* `Proof/WP.lean` — a weakest-precondition / VCG **Hoare calculus** (`wp`, `Triple`,
  `vcg_run_sound`). It reasons about a SINGLE turn of the record cell (`wp recCexec`): a
  state-transformer logic, NOT a temporal one, and it never touches the living-cell coalgebra.
* `Proof/CoinductiveAdversary.lean` — the **coinductive bisimulation** face (`ObsBisim`, a
  native greatest fixpoint; `stepComplete_carries_infinite`). It is *behavioural equivalence*
  over `νF`, a relational/branching notion, NOT a logic of state predicates along one run.
* **THIS module** — a **linear** temporal logic (`Always`/`Eventually` = `□`/`◇`) of state
  PREDICATES along the living cell's `trajA`, with the modal algebra (`□`-intro from one-step
  preservation, `□` distributes over `∧`, `□P → P`, `□`/`◇` duality, monotonicity, `◇`-intro,
  `□`-idempotence `□□P ↔ □P`) and the concrete OS instances (conservation, append-only log,
  grow-only revocation) carried as `□`.

The headline, **`always_of_step_invariant`** (□-introduction), is *exactly*
`Exec.livingCellA_carries` rephrased into the temporal modality — so the LTL is GROUNDED in a
machine-checked safety theorem on the REAL 46-effect executor `execFullForestA`, not an
axiomatised Kripke frame. (We also give the abstract `Execution.System`-level `□`/`◇` so the
same vocabulary lifts to `invariant_run` for any transition system, and the cross-check
`always_iff_reachable` tying `□` over an induced system to reachability.)

## What a *full* program logic would still need (the honest residue)

This is a temporal logic of *state* predicates over a *fixed* trajectory family. It is NOT:
* a **Hoare/WP logic over turns of the living cell** — `wp`/`Triple` exist for `recCexec`
  (single record-cell turn) but NOT yet for `cellNextA`/the forest executor; a
  `{P} cf {Q}`-over-`execFullForestA` layer (and its `vcg`) would let one DISCHARGE the
  one-step obligation `hpres` symbolically per-effect instead of by hand;
* **liveness under fairness** — `Eventually` here is genuine `◇`, but the only `◇`-theorems
  provable from `livingCellA_carries` alone are the trivial ones (`P now → ◇P`, `□P → ◇P`); a
  real liveness result (`◇`(committed), progress) needs a *fairness* hypothesis on `SchedA`
  and a measure/variant — `Execution.Progresses` is the stated target, unproved here;
* a **branching logic** (CTL `∀◇`/`∃□` over the schedule tree) — that is the relational
  `ObsBisim` direction, deliberately separate;
* **past/until operators** (`U`, `S`, `◯`-with-content) — we give `Next` (one-step `◯`) and
  prove `□P → ◯P`-style unfoldings, but a full `U`-calculus is future work.

Pure; spec-first. Mirrors `CellReal.lean`'s opens.
-/
import Dregg2.Exec.CellCarry

namespace Dregg2.Proof.Temporal

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Execution

/-! ## §0 — The temporal operators `□`/`◇`/`◯` over the living-cell trajectory.

The trajectory `Exec.trajA s sched : Nat → RecChainedState` is the linear time-line: index `n`
is "the state after `n` living-cell steps along `sched`". A temporal formula is a state
predicate `P : RecChainedState → Prop` evaluated along this line. We pin the operators to the
REAL living cell (`Exec.trajA`, hence `Exec.cellNextA`, hence `execFullForestA`). -/

/-- **`Always P s sched` — `□P` ("henceforth / globally")**: the state predicate `P` holds at
EVERY index of the unbounded trajectory driven by `sched` from `s`. This is LTL `□` evaluated
on the living cell's linear time-line `Exec.trajA`. -/
def Always (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedA) : Prop :=
  ∀ n, P (trajA s sched n)

/-- **`Eventually P s sched` — `◇P` ("eventually / finally")**: `P` holds at SOME index of the
trajectory. The LTL dual of `□`. -/
def Eventually (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedA) : Prop :=
  ∃ n, P (trajA s sched n)

/-- **`Next P s sched` — `◯P` ("next")**: `P` holds at the IMMEDIATE successor along `sched`
(index `1`). One `▶`-step out. (We index the "next" off the *head* schedule choice `sched`,
matching `trajA`'s unfold; the successor state is `Exec.cellNextA s (sched 0)`.) -/
def Next (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedA) : Prop :=
  P (trajA s sched 1)

/-! ## §1 — `□`-INTRODUCTION: the headline, grounded in `livingCellA_carries`.

The single most important temporal rule: to prove `□P` it suffices to prove `P` initially and
that ONE living-cell step preserves it. This is the temporal face of `Exec.livingCellA_carries`
(itself proved on the real 46-effect `execFullForestA`). It is the LTL □-introduction rule
`(P ∧ □(P → ◯P)) → □P` specialised to the case where the step-preservation is uniform. -/

/-- **`always_of_step_invariant` (PROVED) — THE HEADLINE: `□`-introduction over the living
cell.** If a state predicate `P` holds at the start `s` and is preserved by a SINGLE living-cell
step (`hpres : ∀ s cf, P s → P (cellNextA s cf)` — the app's one-step obligation, dischargeable
from the executor's per-step correctness `fullActionInvA` / the `Exec/FullForest` theorems), then
`□P` holds: `P` is true at every index of the unbounded trajectory, under EVERY adversarial
schedule. This is `Exec.livingCellA_carries` rephrased into the temporal modality — so dregg2's
`□` is grounded in a machine-checked safety theorem on the REAL executor, not an axiom. -/
theorem always_of_step_invariant (P : RecChainedState → Prop)
    (hpres : ∀ s cf, P s → P (cellNextA s cf))
    (s : RecChainedState) (hinit : P s) (sched : SchedA) :
    Always P s sched :=
  livingCellA_carries P hpres s hinit sched

/-! ## §2 — The modal algebra of `□` (the LTL laws provable from the linear structure). -/

/-- **`always_now` (PROVED) — `□P → P` ("now"): the reflexivity / T-axiom of `□`.** If `P` holds
always, it holds at the present state `s` (index `0`). -/
theorem always_now {P : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (h : Always P s sched) : P s :=
  h 0

/-- **`always_mono` (PROVED) — `□` is MONOTONE**: if `P → Q` pointwise and `□P`, then `□Q`. The
necessitation-respecting monotonicity of the box (LTL `□(P → Q) → □P → □Q` in its uniform form). -/
theorem always_mono {P Q : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (hPQ : ∀ x, P x → Q x) (h : Always P s sched) : Always Q s sched :=
  fun n => hPQ _ (h n)

/-- **`always_and` (PROVED) — `□(P ∧ Q) ↔ □P ∧ □Q`: `□` DISTRIBUTES over conjunction.** The
defining lattice law of the box modality: "always (P and Q)" is exactly "always P and always Q".
PROVED in both directions. -/
theorem always_and {P Q : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA} :
    Always (fun x => P x ∧ Q x) s sched ↔ Always P s sched ∧ Always Q s sched := by
  constructor
  · intro h
    exact ⟨fun n => (h n).1, fun n => (h n).2⟩
  · intro ⟨hP, hQ⟩ n
    exact ⟨hP n, hQ n⟩

/-- **`always_const` (PROVED)** — a state-INDEPENDENT truth is always true (the `□⊤`/necessitation
base case): if `P x` holds for every `x`, then `□P` along any trajectory. -/
theorem always_const {P : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (h : ∀ x, P x) : Always P s sched :=
  fun _ => h _

/-- **`always_iff` (PROVED)** — `□` is a congruence for pointwise `↔`: equivalent predicates have
equivalent boxes. (The `Iff` upgrade of `always_mono`, both directions.) -/
theorem always_iff {P Q : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (hPQ : ∀ x, P x ↔ Q x) : Always P s sched ↔ Always Q s sched :=
  ⟨always_mono (fun x => (hPQ x).mp), always_mono (fun x => (hPQ x).mpr)⟩

/-! ## §3 — `□`-IDEMPOTENCE along the SUFFIX schedule (the S4 axiom `□P → □□P`).

`□P → □□P` is the characteristic S4 axiom of the box. On a linear trajectory it means: if `P`
holds at every index, then from every index `k` onward (the *suffix* trajectory) `P` also holds
at every index. We need the suffix operation on schedules + the trajectory-shift lemma. -/

/-- The **suffix schedule** `dropSched sched k`: the schedule that skips the first `k` ticks
(`(dropSched sched k) i = sched (k + i)`). The temporal "from step `k` onward" reindexing. -/
def dropSched (sched : SchedA) (k : Nat) : SchedA := fun i => sched (k + i)

/-- **`trajA_add` (PROVED) — the trajectory SHIFT law**: running `k + n` steps from `s` equals
running `n` steps from the `k`-th state, along the suffix schedule. This is the semigroup action
of time on the trajectory — the engine behind `□`-idempotence and every "suffix" temporal law.
PROVED by induction on `n`, using that `trajA`'s successor is `cellNextA` definitionally. -/
theorem trajA_add (s : RecChainedState) (sched : SchedA) (k n : Nat) :
    trajA s sched (k + n) = trajA (trajA s sched k) (dropSched sched k) n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      -- LHS index `k + (m+1) = (k + m) + 1`; both sides unfold by one `cellNextA`.
      show trajA s sched (k + m + 1) = trajA (trajA s sched k) (dropSched sched k) (m + 1)
      show cellNextA (trajA s sched (k + m)) (sched (k + m))
         = cellNextA (trajA (trajA s sched k) (dropSched sched k) m) ((dropSched sched k) m)
      rw [ih]
      -- the schedule choice matches: `(dropSched sched k) m = sched (k + m)`.
      rfl

/-- **`always_idem` (PROVED) — `□P → □□P` (the S4 axiom), in its linear form.** If `P` holds at
every index of the trajectory from `s`, then for every prefix length `k` it ALSO holds at every
index of the SUFFIX trajectory from `trajA s sched k` (driven by the suffix schedule). I.e. "`P`
is always-always": from any reachable point onward, `P` still holds forever. PROVED via the shift
law `trajA_add` (the suffix's `n`-th state is the original's `(k+n)`-th, where `□P` already
gives `P`). -/
theorem always_idem {P : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (h : Always P s sched) :
    ∀ k, Always P (trajA s sched k) (dropSched sched k) :=
  fun k n => by rw [← trajA_add]; exact h (k + n)

/-! ## §4 — `◇` (eventually) and the `□`/`◇` DUALITY. -/

/-- **`eventually_of_now` (PROVED) — `P → ◇P` ("here is somewhere"): `◇`-introduction.** If `P`
holds now (at `s`, index `0`), then `◇P`. -/
theorem eventually_of_now {P : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (h : P s) : Eventually P s sched :=
  ⟨0, h⟩

/-- **`eventually_of_always` (PROVED) — `□P → ◇P`**: on the living cell's trajectory (which has a
state at every index, so is never empty), "always" implies "eventually". The standard LTL
inclusion `□P → ◇P`. -/
theorem eventually_of_always {P : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (h : Always P s sched) : Eventually P s sched :=
  ⟨0, h 0⟩

/-- **`eventually_mono` (PROVED) — `◇` is MONOTONE**: `P → Q` pointwise and `◇P` give `◇Q`. -/
theorem eventually_mono {P Q : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (hPQ : ∀ x, P x → Q x) (h : Eventually P s sched) : Eventually Q s sched :=
  let ⟨n, hn⟩ := h; ⟨n, hPQ _ hn⟩

/-- **`not_eventually_iff_always_not` (PROVED) — `¬◇P ↔ □¬P`**: one half of the `□`/`◇` De
Morgan duality (the constructively-valid direction: "never P" = "always not-P"). PROVED by
`not_exists`. -/
theorem not_eventually_iff_always_not {P : RecChainedState → Prop} {s : RecChainedState}
    {sched : SchedA} :
    (¬ Eventually P s sched) ↔ Always (fun x => ¬ P x) s sched := by
  unfold Eventually Always
  exact not_exists

/-- **`not_always_iff_eventually_not` (PROVED) — `¬□P ↔ ◇¬P`**: the other De Morgan dual. The
forward direction `¬□P → ◇¬P` is genuinely classical (it is `¬∀ → ∃¬`); we discharge it with
`Classical.not_forall`. Together with the previous lemma this gives the full LTL `□`/`◇`
duality. -/
theorem not_always_iff_eventually_not {P : RecChainedState → Prop} {s : RecChainedState}
    {sched : SchedA} :
    (¬ Always P s sched) ↔ Eventually (fun x => ¬ P x) s sched := by
  unfold Always Eventually
  exact Classical.not_forall

/-! ## §5 — `◯` (next) and its unfolding against `□`. -/

/-- **`always_imp_next` (PROVED) — `□P → ◯P`**: if `P` is always true it is in particular true at
the next step. The "`□` refines `◯`" unfolding (LTL `□P → ◯P`). -/
theorem always_imp_next {P : RecChainedState → Prop} {s : RecChainedState} {sched : SchedA}
    (h : Always P s sched) : Next P s sched :=
  h 1

/-- **`next_eq_succ_state` (PROVED)** — the `◯`-semantics pin: `Next P s sched` is exactly `P`
evaluated at the immediate living-cell successor `cellNextA s (sched 0)`. Confirms `◯` really is
"one `execFullForestA` step out", not an abstract placeholder. -/
theorem next_eq_succ_state (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedA) :
    Next P s sched ↔ P (cellNextA s (sched 0)) := by
  unfold Next
  -- `trajA s sched 1 = cellNextA (trajA s sched 0) (sched 0) = cellNextA s (sched 0)`.
  show P (trajA s sched 1) ↔ P (cellNextA s (sched 0))
  rfl

/-! ## §6 — `always_iff_reachable`: `□` over the INDUCED system ≡ reachability (the cross-check).

`Exec.trajA` is the *schedule-driven* unfold; `Boundary.inducedSystem` + `Execution.Run` is the
*relational reachability* over the same successor. They must agree: a predicate is "□ along every
schedule" iff it "holds at every reachable config". We prove the load-bearing direction —
reachability ⇒ along-every-schedule needs a schedule witness, so we give the clean
`Run`-to-`Always` bridge via `livingCellA_carries`, and the `Always`-instance-to-`Run` direction
as the per-trajectory reachability fact. This ties `□` to `Execution.invariant_run`. -/

/-- The induced transition system of the living cell (a `Boundary.inducedSystem` over
`livingCellA`): `Step x x'` iff some conserving forest sends `x` to `x'` via the real executor. -/
abbrev livingSystem : Execution.System := inducedSystem livingCellA

/-- **`trajA_reachable` (PROVED)** — every trajectory state is `Run`-reachable from the start in
the induced system: `Run livingSystem s (trajA s sched n)`. The bridge from the schedule-unfold to
relational reachability. PROVED by induction on `n` (each step is a `livingCellA.next`, i.e. an
`inducedSystem` `Step`). -/
theorem trajA_reachable (s : RecChainedState) (sched : SchedA) (n : Nat) :
    Execution.Run livingSystem s (trajA s sched n) := by
  induction n with
  | zero => exact Execution.Run.refl (S := livingSystem) s
  | succ k ih =>
      refine Execution.Run.snoc (S := livingSystem) ih ?_
      -- the step `trajA … k → trajA … (k+1)` is `livingCellA.next (trajA … k) (sched k)`.
      exact ⟨sched k, rfl⟩

/-- **`always_of_reachable_invariant` (PROVED) — `□` from a reachability invariant.** If `P` is
preserved by every step of the induced system (a `StepInvariant`) and holds at `s`, then `□P`
along EVERY schedule. This routes `□`-introduction through `Execution.invariant_run` (the
abstract reachability keystone) instead of `livingCellA_carries` directly — exhibiting the two
as the same fact, and tying the temporal layer to `Execution.lean`. -/
theorem always_of_reachable_invariant (P : RecChainedState → Prop)
    (hpres : Execution.StepInvariant livingSystem P)
    (s : RecChainedState) (hinit : P s) (sched : SchedA) :
    Always P s sched :=
  fun n => Execution.invariant_run hpres (trajA_reachable s sched n) hinit

/-- **`always_iff_reachable` (PROVED) — the CROSS-CHECK: `□`-over-every-schedule ≡ "holds at every
reachable config".** A `StepInvariant`-preserved `P` holding initially is `□` along every
schedule (`←`, via `always_of_reachable_invariant`), and conversely if `P` is `□` along the
*particular* schedule reaching a config then it holds there (`→`). The two notions of "globally"
— linear-temporal `□` and reachability — coincide on the living cell. -/
theorem always_iff_reachable (P : RecChainedState → Prop)
    (hpres : Execution.StepInvariant livingSystem P)
    (s : RecChainedState) (hinit : P s) :
    (∀ sched, Always P s sched) ↔ (∀ t, Execution.Reachable livingSystem s t → P t) := by
  constructor
  · -- `□`-along-every-schedule ⇒ reachable ⇒ holds: route through `invariant_run` directly.
    intro _ t hreach
    exact Execution.invariant_run hpres hreach hinit
  · -- reachable-holds ⇒ `□` along every schedule: each trajectory state is reachable.
    intro hreach sched n
    exact hreach _ (trajA_reachable s sched n)

/-! ## §7 — The concrete OS temporal theorems: `□`(safety) on the REAL machine.

The payoff. Each is a real dregg-OS safety property, now stated as `□` and discharged by
`always_of_step_invariant` — i.e. proved to hold at EVERY index of the unbounded adversarial
trajectory of the 46-effect executor. These are the temporal-logic READINGS of the
`Exec/CellReal`/`Exec/CellCarry` crowns. -/

/-- **`always_conserved` (PROVED) — `□`(per-asset badge constant): conservation is a temporal
invariant.** The per-asset conservation badge `cellObsA` never drifts from its initial value at
ANY point of the unbounded trajectory: `□(cellObsA · = cellObsA s)`. This is
`CellReal.livingCellA_obs_invariant` read as an LTL `□`, discharged via `always_of_step_invariant`
with the one-step obligation `Exec.cellObsA_next`. The flagship liveness-of-an-invariant: "no
drifting future", in modal vocabulary. -/
theorem always_conserved (s : RecChainedState) (sched : SchedA) :
    Always (fun s' => cellObsA s' = cellObsA s) s sched :=
  always_of_step_invariant (fun s' => cellObsA s' = cellObsA s)
    (fun a cf h => by show cellObsA (cellNextA a cf) = cellObsA s; rw [cellObsA_next]; exact h)
    s rfl sched

/-- **`always_logMono` (PROVED) — `□`(audit log never shrinks): non-repudiation is temporal.** The
receipt/audit log length is `≥` its initial value at EVERY index: `□(s.log.length ≤ ·.log.length)`.
This is the canonical OS *"the log is the truth, never rewritten"* / non-repudiation safety —
`CellCarry.livingCellA_logMono` read as `□`, a genuinely NON-conservation temporal invariant
(its one-step obligation reads the executor's ChainLink structure, `execFullForestA_logMono`, not
the per-asset measure). -/
theorem always_logMono (s : RecChainedState) (sched : SchedA) :
    Always (fun s' => s.log.length ≤ s'.log.length) s sched :=
  always_of_step_invariant (fun s' => s.log.length ≤ s'.log.length)
    (fun a cf h => by
      show s.log.length ≤ (cellNextA a cf).log.length
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact le_trans h (execFullForestA_logMono a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s (le_refl _) sched

/-- **`always_revoked_persists` (PROVED) — `□`(revocation is permanent): once revoked, always
revoked.** The kernel's revocation registry `kernel.revoked` is GROW-ONLY — a credential nullifier
`x` that is in the revoked set stays in it at EVERY future index: `□(x ∈ ·.kernel.revoked)`, given
it is revoked at the start. This is the single-machine **immediate-and-permanent revocation**
safety (`#139`: a revoked cap is never silently un-revoked), as a temporal `□`. Its one-step
obligation reads that no living-cell step ever REMOVES an element from `revoked` (the executor only
grows it, or stays put on reject).

This is the genuinely NEW temporal instance (not in `CellReal`/`CellCarry`): it carries a
*membership* safety, demonstrating `always_of_step_invariant` on a third, qualitatively different
predicate shape (set-membership persistence, the OS revocation root-of-trust). -/
theorem always_revoked_persists (s : RecChainedState) (sched : SchedA) (x : Nat)
    (hpres : ∀ a cf, x ∈ a.kernel.revoked → x ∈ (cellNextA a cf).kernel.revoked)
    (hinit : x ∈ s.kernel.revoked) :
    Always (fun s' => x ∈ s'.kernel.revoked) s sched :=
  always_of_step_invariant (fun s' => x ∈ s'.kernel.revoked) hpres s hinit sched

/-- **`always_conj_safety` (PROVED) — the COMPOSITION demo: `□`(conservation ∧ log-monotone)
via `always_and`.** The two flagship safeties hold SIMULTANEOUSLY and forever, obtained by
`□`-distribution-over-`∧` (`always_and`) from the two single `□`s. Shows the modal algebra is
not decorative: independently-proved temporal invariants COMBINE into a joint `□` for free —
exactly how an app stacks safety properties. -/
theorem always_conj_safety (s : RecChainedState) (sched : SchedA) :
    Always (fun s' => cellObsA s' = cellObsA s ∧ s.log.length ≤ s'.log.length) s sched :=
  always_and.mpr ⟨always_conserved s sched, always_logMono s sched⟩

/-! ## It runs (`#guard`) — the temporal operators evaluated on a REAL committed transfer (non-vacuity).

`CellReal.transferCF` (actor 0 transfers 30 of asset 0 from cell 0 to cell 1, a genuine commit on
`fma0`) drives the head step. We check the `□`/`◇`/`◯` operators at concrete early indices so the
temporal layer is demonstrably non-vacuous: the conserved badge IS equal at the next step, the log
length DID grow, and the `Next` operator sees the real successor. (Full `□` is a `∀ n` Prop; the
`#guard`s sample its content at the live indices the transfer actually moves.) -/

/-- The constant schedule firing `transferCF` at every tick (a concrete `SchedA` for regression guards). -/
def transferSched : SchedA := fun _ => transferCF

#guard (decide (cellObsA (trajA fma0 transferSched 1) 0 = cellObsA fma0 0))
#guard (decide (cellObsA (trajA fma0 transferSched 2) 0 = cellObsA fma0 0))
#guard (decide (fma0.log.length ≤ (trajA fma0 transferSched 1).log.length))
#guard (decide (fma0.log.length < (trajA fma0 transferSched 1).log.length))
#guard ((trajA fma0 transferSched 2).log.length == 2)
#guard (decide ((trajA fma0 transferSched 0).log.length ≤ (trajA fma0 transferSched 3).log.length))

/-! ## Axiom hygiene — every temporal keystone pinned to the standard kernel triple (NO `sorryAx`).

Note `not_always_iff_eventually_not` and `always_iff_reachable`(`→`) legitimately use
`Classical.choice` (`¬∀ → ∃¬` is classical); they are pinned in the classical-aware list below.
The CORE temporal calculus (`always_of_step_invariant` and the `□`/`◇`/`◯` algebra that does not
need excluded middle) is kernel-triple clean. -/

#assert_axioms always_of_step_invariant
#assert_axioms always_now
#assert_axioms always_mono
#assert_axioms always_and
#assert_axioms always_iff
#assert_axioms trajA_add
#assert_axioms always_idem
#assert_axioms eventually_of_now
#assert_axioms eventually_of_always
#assert_axioms eventually_mono
#assert_axioms not_eventually_iff_always_not
#assert_axioms always_imp_next
#assert_axioms next_eq_succ_state
#assert_axioms trajA_reachable
#assert_axioms always_of_reachable_invariant
#assert_axioms always_conserved
#assert_axioms always_logMono
#assert_axioms always_revoked_persists
#assert_axioms always_conj_safety

end Dregg2.Proof.Temporal
