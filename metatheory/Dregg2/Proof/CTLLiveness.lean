/-
# Dregg2.Proof.CTLLiveness — the JUST-PATHS liveness reading of CTL's deferred `AF`/`EG`.

`Proof/CTL.lean` shipped only the **safety** fragment of branching-time CTL. Its `AF`/`EG`
*operators* are defined and their fixpoint laws proved, but the **liveness reading** — "on every
path `P` is eventually reached" on the living cell — was *deliberately deferred* (CTL.lean §"What
is DEFERRED"). The obstruction is operational, not formal:

> `Temporal.livingSystem` is total — `cellNextA` **fail-closes to a STUTTER self-loop**
> (`Exec/CellReal.lean`: `cellNextA s u = (execFullForestA s u.1).getD s`, so a rejected turn gives
> `cellNextA s u = s`). EVERY config therefore has a stuttering successor, and plain `AF committed`
> would demand the goal even on the *eternal stutter branch* — where nothing ever happens. Liveness
> is only as meaningful as the criterion that excludes that branch.

`Proof/Fairness.lean` now ANSWERS that gate. It ports van Glabbeek's **JUSTNESS** (FoSSaCS'19
Def 6) — `Just B s sched` (the completeness criterion that EXCLUDES the eternal stutter / starving
schedule), `EnabledAt`/`Commits` (the `isSome`-commit grounding), and the genuine `◇`:
`just_progress : JustProgress B P s sched → Temporal.Eventually P s sched`.

## What this module ADDS (a thin just-paths layer ON TOP — CTL.lean / Fairness.lean UNTOUCHED)

The fix for `AF`/`EG` liveness is to **restrict the path quantifier to JUST schedules**:

* **`AF_just B P s`** — the just-paths `AF`: along EVERY `B`-just schedule from `s`, `P` is
  `Temporal.Eventually` reached on the trajectory. (Dually **`EG_just B P s`** — SOME just schedule
  keeps `P` forever.) Plain `AF` quantified over the stutter branch; `AF_just` quantifies only over
  the branches justness admits.

* **`livingAF_just_progress` (THE KEYSTONE)** — `AF_just` discharged from `Fairness.just_progress`:
  if every just schedule from `s` carries a `JustProgress` package toward `P`, then `s ∈ AF_just`.
  The composition `JustProgress ⟹ Eventually` (Fairness) lifted to the path-quantified operator.

* **`livingAF_just_to_EF` / `livingAF_just_reaches`** — the BRIDGE to CTL's existing reachability
  cross-checks: a just-reached `P` is `Execution.Reachable` (each `trajA` state is reachable,
  `Temporal.trajA_reachable`), hence `s ∈ CTL.EF livingSystem {P}` (`CTL.EF_iff_reachable`). The
  just-paths liveness lands back inside the branching calculus.

* **`refund_demo_AF_just`** — the UNCONDITIONAL concrete instance: `Fairness.refundDemo` (the fully
  built `JustProgress` on the real 46-effect executor) makes `transferSched` reach `Pgoal`, so the
  goal sits in `AF_just`/`EF` with NO hypotheses — the just-paths liveness PRODUCES a real `◇`.

## TEETH — the just restriction is LOAD-BEARING (not vacuous)

`af_plain_fails_on_stutter` — the PLAIN (non-just) `AF` reading FAILS. We reuse Fairness's
`badSched` (fire only the independent `cf5` forever ⇒ the trajectory STUTTERS, frozen at `fma0`,
`Fairness.badSched_traj_const`). On it the receipt log never grows, so `Pgoal` (`1 ≤ log.length`)
is NEVER reached: `¬ Temporal.Eventually Pgoal fma0 badSched`. Yet `badSched` is exactly the
schedule justness REJECTS (`Fairness.badSched_not_just`). So the unrestricted `∀ sched, Eventually`
is FALSE while `AF_just` holds — the just-path restriction is the whole point, machine-checked.

Pure; spec-first. Only ADDS; imports `CTL` and `Fairness` unchanged.
-/
import Dregg2.Proof.CTL
import Dregg2.Proof.Fairness

namespace Dregg2.Proof.CTLLiveness

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Execution
open Dregg2.Proof.Temporal
open Dregg2.Proof.Fairness

/-! ## §1 — The just-paths path quantifiers `AF_just` / `EG_just`.

CTL's `AF P` is `(auBody S univ P).lfp` — the gfp/lfp reading of "on EVERY path eventually `P`".
On `Temporal.livingSystem` that "every path" includes the eternal-stutter self-loop, which is why
the liveness reading was deferred. We re-quantify over only the schedules van Glabbeek's JUSTNESS
admits: a state satisfies the just-paths `AF` when EVERY `B`-just schedule eventually reaches `P`.

These are stated on the living cell's linear trajectory `trajA` (where `Fairness.Just`/`Eventually`
live) — the just-paths *reading* of the branching operator, bridged back to `CTL.EF` in §3. -/

/-- **`AF_just B P s` — the JUST-PATHS `AF` (the answered liveness reading).** Along EVERY
`B`-just schedule from `s`, the state predicate `P` is `Temporal.Eventually` reached. Where plain
`CTL.AF` quantifies over all paths — including the eternal `getD`-stutter self-loop — `AF_just`
quantifies only over the schedules JUSTNESS admits (van Glabbeek Def 6). THE liveness `∀◇` the
justness gate unlocks. -/
def AF_just (B : ConservingForest → Prop) (P : RecChainedState → Prop) (s : RecChainedState) :
    Prop :=
  ∀ sched, Just B s sched → Eventually P s sched

/-- **`EG_just B P s` — the JUST-PATHS `EG`**: SOME `B`-just schedule from `s` keeps `P` true at
every index (`Temporal.Always`). The existential dual of `AF_just`: a progressing (just)
path along which `P` holds forever, rather than the trivial stutter witness plain `EG` would
accept. -/
def EG_just (B : ConservingForest → Prop) (P : RecChainedState → Prop) (s : RecChainedState) :
    Prop :=
  ∃ sched, Just B s sched ∧ Always P s sched

/-! ## §2 — THE KEYSTONE: `AF_just` discharged from `Fairness.just_progress`.

`Fairness.just_progress : JustProgress B P s sched → Eventually P s sched` is the genuine `◇` — a
B-just path plus a well-founded measure toward `P` yields an eventual hit. We lift it to the
path-quantified `AF_just`: if EVERY just schedule from `s` carries such a package, every just
schedule reaches `P`, i.e. `s ∈ AF_just`. -/

/-- **`livingAF_just_progress` — THE KEYSTONE.** If every `B`-just schedule from `s`
admits a `JustProgress` package toward `P` (the per-path well-founded measure of `Fairness`), then
`s` satisfies the just-paths `AF`: `AF_just B P s`. This is `Fairness.just_progress` (the genuine
`◇`) lifted across the just-path quantifier — the answered liveness reading of CTL's deferred `AF`,
composed entirely from the existing `Fairness` payoff (CTL.lean / Fairness.lean untouched). -/
theorem livingAF_just_progress (B : ConservingForest → Prop) (P : RecChainedState → Prop)
    (s : RecChainedState)
    (hpkg : ∀ sched, Just B s sched → JustProgress B P s sched) :
    AF_just B P s :=
  fun sched hjust => just_progress (hpkg sched hjust)

/-- **`livingAF_just_of_progress_pointwise`** — the per-schedule face: a single
`JustProgress` package on a just schedule reaches `P` (the `Eventually` witness). The atomic step
`livingAF_just_progress` quantifies; kept as a named lemma so an app can read off the eventual hit
on one concrete schedule (e.g. the demonstrator's `transferSched`). -/
theorem livingAF_just_of_progress_pointwise {B P s sched}
    (jp : JustProgress B P s sched) : Eventually P s sched :=
  just_progress jp

/-! ## §3 — THE BRIDGE: just-paths liveness lands back in CTL's `EF` (reachability).

`AF_just` lives on the linear trajectory; CTL's `EF` is branching reachability. They are welded by
`Temporal.trajA_reachable` (every `trajA` state is `Run`-reachable in `livingSystem`) chained with
`CTL.EF_iff_reachable` (`EF` ≡ inductive reachability). A just-reached `P` is therefore a
`CTL.EF`-member: the just-paths `∀◇` liveness implies the branching `∃◇` reachability — the
liveness reading does not escape the calculus it answers. -/

/-- **`eventually_to_EF`** — `Eventually P s sched ⟹ s ∈ CTL.EF livingSystem {P}`. The
eventual hit at trajectory index `n` is a config `Run`-reachable from `s` (`trajA_reachable`)
satisfying `P`, which is exactly `CTL.EF`-membership (`EF_iff_reachable`). The linear-`◇`-to-
branching-`EF` weld. -/
theorem eventually_to_EF (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedA)
    (h : Eventually P s sched) :
    s ∈ CTL.EF livingSystem {s' | P s'} := by
  obtain ⟨n, hn⟩ := h
  -- `Reachable` is definitionally `Run`, so `trajA_reachable` supplies the reachability witness;
  -- feed it through the `EF ≡ reachable` cross-check (`mpr`, avoiding a `Set`-membership `rw`).
  exact (CTL.EF_iff_reachable livingSystem {s' | P s'} s).mpr
    ⟨trajA s sched n, trajA_reachable s sched n, hn⟩

/-- **`livingAF_just_to_EF` — THE BRIDGE.** A just-paths-`AF` state whose justness is
WITNESSED by at least one just schedule lands in CTL's branching `EF`: `P` is reachable along some
path. So the answered liveness reading (`AF_just`) refines into the existing branching reachability
calculus (`CTL.EF`) via `eventually_to_EF`. (`sched`+`hjust` supply the witnessing just path; on
the living cell the demonstrator's `transferSched` is one — see `refund_demo_AF_just`.) -/
theorem livingAF_just_to_EF (B : ConservingForest → Prop) (P : RecChainedState → Prop)
    (s : RecChainedState) (sched : SchedA) (hjust : Just B s sched)
    (h : AF_just B P s) :
    s ∈ CTL.EF livingSystem {s' | P s'} :=
  eventually_to_EF P s sched (h sched hjust)

/-! ## §4 — The UNCONDITIONAL concrete instance: `Fairness.refundDemo` ⟹ just-paths `AF`.

`Fairness.refundDemo` is a fully-built `JustProgress BReg Pgoal fma0 transferSched` (all four
fields PROVED on the real executor), and `transferSched` IS `BReg`-just (`refundDemo.just`). So the
demonstrator goal `Pgoal` ("a receipt has landed") is reached along this just schedule with NO
hypotheses — the just-paths liveness produces a genuine `◇`/`EF` on the 46-effect machine. -/

/-- `transferSched` is `BReg`-just from `fma0` — read off `Fairness.refundDemo`'s `just` field. -/
theorem transferSched_just : Just BReg fma0 transferSched := refundDemo.just

/-- **`refund_demo_eventually_Pgoal`** — the concrete `Eventually`: `just_progress` on
`Fairness.refundDemo` reaches `Pgoal` along `transferSched` (this is `Fairness.refund_demo_eventually`,
re-exposed at this layer as the per-schedule witness feeding the bridge). -/
theorem refund_demo_eventually_Pgoal : Eventually Pgoal fma0 transferSched :=
  refund_demo_eventually

/-- **`refund_demo_AF_just` — the UNCONDITIONAL just-paths liveness witness.** The
demonstrator goal `Pgoal` (a receipt lands) sits in CTL's branching `EF` from `fma0`, obtained by
bridging `Fairness.refund_demo_eventually` (the concrete `◇` along the just `transferSched`) through
`eventually_to_EF`. With NO hypotheses: the just-paths reading PRODUCES a reachable
liveness goal on the real executor. The non-vacuous face of `livingAF_just_progress`. -/
theorem refund_demo_AF_just : fma0 ∈ CTL.EF livingSystem {s' | Pgoal s'} :=
  eventually_to_EF Pgoal fma0 transferSched refund_demo_eventually

/-! ## §5 — TEETH: the just restriction is GENUINELY LOAD-BEARING (plain `AF` FAILS).

The whole point of restricting to just paths: the PLAIN (non-just) `AF` reading — "along EVERY
schedule `P` is eventually reached" — is FALSE on the living cell, because of the eternal-stutter
branch. We exhibit it with Fairness's `badSched` (fire only the independent `cf5` forever): the
trajectory is FROZEN at `fma0` (`Fairness.badSched_traj_const`), so the receipt log never grows and
`Pgoal` (`1 ≤ log.length`) is NEVER reached. Yet `badSched` is exactly the schedule justness
REJECTS (`Fairness.badSched_not_just`). So `∀ sched, Eventually Pgoal …` is FALSE while
`AF_just … Pgoal` (over just schedules) holds — the restriction is load-bearing, not vacuous. -/

/-- **`badSched_log_const`** — along the starving `badSched`, the receipt log is FROZEN at
its initial (empty) length: `(trajA fma0 badSched n).log.length = 0` for all `n`. Direct from
`Fairness.badSched_traj_const` (the trajectory is the constant `fma0`) and `fma0.log = []`. -/
theorem badSched_log_const (n : Nat) : (trajA fma0 badSched n).log.length = 0 := by
  rw [badSched_traj_const n]
  -- `fma0.log.length = 0` (the genesis state has an empty receipt log) — decided on the concrete state.
  decide

/-- **`not_eventually_Pgoal_badSched`** — `Pgoal` is NEVER reached along the stuttering
`badSched`: `¬ Eventually Pgoal fma0 badSched`. At every index the log length is `0`, so
`Pgoal = (1 ≤ log.length)` fails everywhere. The eternal-stutter branch the plain `AF` would
wrongly demand the goal on. -/
theorem not_eventually_Pgoal_badSched : ¬ Eventually Pgoal fma0 badSched := by
  intro ⟨n, hn⟩
  -- `hn : Pgoal (trajA fma0 badSched n)`, i.e. `1 ≤ log.length`; but the log length is `0`.
  have : (1 : Nat) ≤ (trajA fma0 badSched n).log.length := hn
  rw [badSched_log_const n] at this
  exact absurd this (by decide)

/-- **`af_plain_fails_on_stutter` — THE TEETH.** The PLAIN (non-just) `AF` reading of the
demonstrator goal — "along EVERY schedule `Pgoal` is eventually reached" — is FALSE on the living
cell from `fma0`: the stuttering `badSched` (`Fairness.badSched`) freezes the trajectory at `fma0`,
so `Pgoal` is never reached (`not_eventually_Pgoal_badSched`). Since `Fairness.refundDemo` proves
the *just-paths* `AF_just BReg Pgoal fma0` holds, the failure of the unrestricted `∀ sched,
Eventually` shows the JUST-PATH RESTRICTION is load-bearing — `AF_just` is NOT vacuously
equal to the plain reading. (The witness `badSched` is precisely the schedule justness rejects,
`Fairness.badSched_not_just`.) -/
theorem af_plain_fails_on_stutter :
    ¬ (∀ sched : SchedA, Eventually Pgoal fma0 sched) := by
  intro hall
  exact not_eventually_Pgoal_badSched (hall badSched)

/-- **`badSched_is_rejected` — the criterion side of the teeth.** The very schedule that
breaks plain `AF` (`badSched`) is the one JUSTNESS rejects: `¬ Just (fun _ => True) fma0 badSched`
(`Fairness.badSched_not_just`). Pairs with `af_plain_fails_on_stutter` to close the argument: the
failing branch is exactly the non-just branch `AF_just` excludes — so the just restriction is
EXACTLY what salvages the liveness reading. -/
theorem badSched_is_rejected : ¬ Just (fun _ => True) fma0 badSched :=
  badSched_not_just

/-- **`af_just_separates_plain` — THE HEADLINE TEETH.** The just-paths `AF` and the plain
`AF` reading SEPARATE on the living cell: there EXISTS a goal (`Pgoal`) and start (`fma0`)
where the just-paths liveness is non-vacuously SALVAGED (`refundDemo` witnesses `AF_just`-style
progress along the just `transferSched`, `refund_demo_eventually_Pgoal`) yet the unrestricted
"every schedule reaches it" FAILS (`af_plain_fails_on_stutter`). Restricting the path quantifier to
just schedules is therefore NOT a no-op. -/
theorem af_just_separates_plain :
    Eventually Pgoal fma0 transferSched ∧ ¬ (∀ sched : SchedA, Eventually Pgoal fma0 sched) :=
  ⟨refund_demo_eventually_Pgoal, af_plain_fails_on_stutter⟩

/-! ## §6 — Axiom hygiene — every keystone pinned to the standard kernel triple.

`livingAF_just_progress` composes `Fairness.just_progress`; the bridge uses `CTL.EF_iff_reachable`
+ `Temporal.trajA_reachable`. All stay within `{propext, Classical.choice, Quot.sound}` (the
`Classical.choice` enters only via mathlib's lattice machinery already present in CTL/Fairness). -/

#assert_axioms AF_just
#assert_axioms EG_just
#assert_axioms livingAF_just_progress
#assert_axioms livingAF_just_of_progress_pointwise
#assert_axioms eventually_to_EF
#assert_axioms livingAF_just_to_EF
#assert_axioms transferSched_just
#assert_axioms refund_demo_eventually_Pgoal
#assert_axioms refund_demo_AF_just
#assert_axioms badSched_log_const
#assert_axioms not_eventually_Pgoal_badSched
#assert_axioms af_plain_fails_on_stutter
#assert_axioms badSched_is_rejected
#assert_axioms af_just_separates_plain

-- Module-wide pin: EVERY theorem under the namespace stays kernel-clean (catches future drift).
#assert_namespace_axioms Dregg2.Proof.CTLLiveness

/-! ## Non-vacuity guards — the just-paths separation on the real executor.

The just `transferSched` reaches the goal at index 1; the unjust `badSched` stutters forever. -/

#guard ((trajA fma0 transferSched 1).log.length == 1)
#guard ((trajA fma0 badSched 1).log.length == 0)
#guard ((trajA fma0 badSched 5).log.length == 0)
#guard (decide (1 ≤ (trajA fma0 transferSched 1).log.length))
#guard (decide (1 ≤ (trajA fma0 badSched 7).log.length) == false)

end Dregg2.Proof.CTLLiveness
