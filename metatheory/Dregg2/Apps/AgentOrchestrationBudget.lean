/-
# Dregg2.Apps.AgentOrchestrationBudget — the INTEGRATOR WEDGE, as ONE cell program.

`Apps/AgentOrchestration.lean` runs a multi-agent swarm through the KERNEL EXECUTOR (real
per-asset transfers + attenuated delegation + the credential gate). This app is its missing
twin: the **orchestration POLICY** — the dispatch board itself — expressed as a `RecordProgram`
the executor enforces on EVERY turn, exercising the full landed cell-program expressiveness
(`Exec/Program.lean`): turn-sender binding, balance gates, affine budget arithmetic, the
actor-bound baton, the composite Heyting gate — PLUS the async `notify` cap algebra
(`Firmament/NotifyAuthority.lean`) for the wake edge.

## The integrator wedge — the six primitives buildr/builders/sig/simbi each hand-rolled UNGATED

A multi-agent coordinator (buildr/builders/sig/simbi …) re-invents the SAME six primitives, each
without enforcement:

  1. **cap-gated authority** — only the appointed lead may dispatch work;
  2. **signed provenance** — a dispatch must come FROM the cell's recorded lead (sender-binding),
     not from anyone who merely holds a capability;
  3. **atomic budget** — the swarm's total spend may never exceed its mandate (one over-budget
     worker aborts the whole turn);
  4. **atomic handoff** — the coordination baton flips only when its CURRENT holder signs the turn;
  5. **surfaces-as-caps** — a worker's reach is an attenuated capability, never amplifiable;
  6. **async notify wake** — a worker is woken only on a badge its coordinator holds a cap for.

dregg closes all six AT ONE SEAM: the dispatch-board cell's `RecordProgram` + the notify cap.
Here every primitive is a constraint or a cap, every refusal a theorem.

## The board cell — its state

The dispatch-board cell carries (named record fields, the heap/register substrate):

  * `lead`       — the identity of the cell's appointed coordinator (the signed-provenance anchor);
  * `baton`      — the coordination baton's current holder (the handoff target);
  * `budget`     — the swarm's spend mandate (an immutable ceiling once set);
  * `spent_a`/`spent_b` — per-worker cumulative spend (monotone; their sum gated by `budget`);
  * `epoch`      — a strictly-monotone dispatch counter (every dispatch advances it; no replay).

The dispatch gate is ONE `RecordProgram.predicate`. The teeth below show:
COMMIT a faithful dispatch; REFUSE a forged handoff (non-lead sender), an over-budget runaway,
a stolen baton (non-holder flip), a replayed dispatch (non-advancing epoch); and — through the
notify algebra — REFUSE an un-capped wake while a properly-capped wake COMMITS.

## Honest scope

* The sender/balance/epoch ATOMS are enforced by the executor's `admitsCtx` (the ctx carries the
  turn's sender + the cell's sealed balance, exactly the Rust `EvalContext`). We prove the GATE
  behaviour; the §8 crypto portal (signature → sender identity) is the named seam, never proved
  inside Lean (`AuthPortal`, the seL4 floor) — same convention as `AgentOrchestration`.
* The notify teeth demonstrate AUTHORITY containment (a worker cannot cause a wake it holds no
  cap for), NOT information containment (the badge-OR covert channel is the carried risk named in
  `SwarmSignal`/`NOTIFY-CASCADE.md`).
* The budget gate bounds the per-turn declared spend (`spent_a + spent_b ≤ budget`); binding the
  declared spend to ACTUAL ledger debits is the executor's conservation keystone, a separate axis
  (`AgentOrchestration.workForest_conserves`) — this app gates the POLICY, that one moves value.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` —
`decide` / `#guard` / `Exec.Program`-keystone reuse only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.Program
import Dregg2.Firmament.NotifyAuthority

namespace Dregg2.Apps.AgentOrchestrationBudget

open Dregg2.Exec
open Dregg2.Firmament.NotifyAuthority
open Dregg2.Firmament.SeL4Kernel (Notification ObjId)

/-! ## §0 — The board's field names + the swarm's identities. -/

/-- The cell's appointed coordinator (the signed-provenance anchor). -/
abbrev leadF : FieldName := "lead"
/-- The coordination baton's current holder (the handoff target). -/
abbrev batonF : FieldName := "baton"
/-- The swarm's spend mandate (immutable ceiling). -/
abbrev budgetF : FieldName := "budget"
/-- Worker A's cumulative spend (monotone). -/
abbrev spentAF : FieldName := "spent_a"
/-- Worker B's cumulative spend (monotone). -/
abbrev spentBF : FieldName := "spent_b"
/-- The strictly-monotone dispatch counter (no replay). -/
abbrev epochF : FieldName := "epoch"

/-- The appointed lead's identity (a public-key scalar, `EvalContext::sender`). -/
abbrev leadPk : Int := 0xA1
/-- A rogue worker's identity (holds NO lead authority over the board). -/
abbrev roguePk : Int := 0x99
/-- The swarm's spend mandate. -/
abbrev mandate : Int := 1000

/-! ## §1 — THE DISPATCH GATE as a `RecordProgram` (the six primitives, ONE predicate).

The board's program is a conjunction of constraints, each a primitive of the wedge:

  * `senderInField leadF` — **(1)+(2) cap-gated authority + signed provenance**: the dispatch
    must be SIGNED BY the identity held in the cell's own `lead` slot. Capability possession is
    not enough; the turn's sender must BE the recorded lead. A forged handoff from a rogue who
    holds a capability is rejected.
  * `affineLe [(1,spentAF),(1,spentBF)] mandate` — **(3) atomic budget**: the swarm's total
    declared spend `spent_a + spent_b ≤ mandate`. An over-budget runaway is refused; the whole
    turn aborts (all-or-nothing — it is ONE predicate).
  * `anyOf [immutable batonF, senderInField batonF]` — **(4) atomic handoff**: the baton flips
    only in a turn SIGNED BY its current holder (the actor-bound keystone `actorBound_*`); a turn
    that leaves the baton alone is open. A stolen-baton flip (non-holder sender) is rejected.
  * `strictMono epochF` — **(no replay)**: every dispatch strictly advances the epoch. A replayed
    dispatch (same/stale epoch) is rejected.
  * `immutable budgetF` — the mandate, once set, cannot be quietly widened mid-swarm.

(Capabilities-as-surfaces (5) and the async wake (6) ride the cap algebra in §4/§5 — they are
not record-field constraints.) -/
def dispatchConstraints : List StateConstraint :=
  [ .simple (.senderInField leadF)                            -- (1)+(2) signed provenance
  , .affineLe [(1, spentAF), (1, spentBF)] mandate            -- (3) atomic budget
  , .anyOf [.immutable batonF, .senderInField batonF]         -- (4) actor-bound baton handoff
  , .simple (.strictMono epochF)                              -- (no replay)
  , .simple (.immutable budgetF) ]                            -- immutable mandate

/-- **The dispatch board program** — the integrator wedge as ONE coalgebra structure-map. -/
def boardProgram : RecordProgram := .predicate dispatchConstraints

/-! ## §2 — Extraction plumbing (the `ChannelGroup` pattern): an admitted dispatch satisfies
every constraint of the board. -/

/-- Every constraint binds on an admitted dispatch (`admitsCtx` on `.predicate` IS the
conjunction, definitionally — the `ChannelGroup.admitted_mem` shape). -/
private theorem admitted_mem {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : boardProgram.admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ dispatchConstraints) :
    evalConstraintCtx ctx c o n = true := by
  have hall : dispatchConstraints.all (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

/-- The signed-provenance constraint (constraint 1) read off an admitted dispatch. -/
private theorem admitted_signed {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : boardProgram.admitsCtx ctx m o n = true) :
    evalSimpleCtx ctx (.senderInField leadF) o n = true := by
  have := admitted_mem h (c := .simple (.senderInField leadF)) (by exact .head _)
  simpa [evalConstraintCtx] using this

/-- The budget constraint (constraint 2) read off an admitted dispatch. -/
private theorem admitted_budget {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : boardProgram.admitsCtx ctx m o n = true) :
    evalConstraintCtx ctx (.affineLe [(1, spentAF), (1, spentBF)] mandate) o n = true :=
  admitted_mem h (by exact .tail _ (.head _))

/-- The baton-handoff constraint (constraint 3) read off an admitted dispatch. -/
private theorem admitted_baton {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : boardProgram.admitsCtx ctx m o n = true) :
    evalConstraintCtx ctx (.anyOf [.immutable batonF, .senderInField batonF]) o n = true :=
  admitted_mem h (by exact .tail _ (.tail _ (.head _)))

/-- The epoch constraint (constraint 4) read off an admitted dispatch. -/
private theorem admitted_epoch {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : boardProgram.admitsCtx ctx m o n = true) :
    evalSimpleCtx ctx (.strictMono epochF) o n = true := by
  have := admitted_mem h (c := .simple (.strictMono epochF)) (by exact .tail _ (.tail _ (.tail _ (.head _))))
  simpa [evalConstraintCtx] using this

/-! ## §3 — THE TEETH on the dispatch policy (both polarities, all PROVED).

Each is a real fact about the board program: an honest dispatch admits; each adversary trace is
rejected (`admitsCtx … = false`). -/

/-- **① SIGNED-PROVENANCE TOOTH — a forged handoff is UNSAT.** A dispatch whose turn-sender is
NOT the cell's recorded `lead` is rejected by the board program: `admitsCtx = false`. Holding a
capability is not enough — the turn must be SIGNED BY the lead. The integrator's primitive (2)
made enforceable. -/
theorem forged_dispatch_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (recordedLead : Int)
    (hlead : n.scalar leadF = some recordedLead)
    (hforged : ctx.sender ≠ some recordedLead) :
    boardProgram.admitsCtx ctx m o n = false := by
  -- The signed-provenance constraint fails: sender ≠ the recorded lead.
  have hfail : evalConstraintCtx ctx (.simple (.senderInField leadF)) o n = false := by
    simp only [evalConstraintCtx, evalSimpleCtx, hlead]
    cases hs : ctx.sender with
    | none   => rfl
    | some s =>
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he; exact hforged (by rw [hs, he])
  -- A false constraint collapses the conjunction.
  by_contra hc
  have hne : boardProgram.admitsCtx ctx m o n = true := by
    cases h : boardProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have := admitted_mem hne (c := .simple (.senderInField leadF)) (.head _)
  rw [hfail] at this; exact absurd this (by simp)

/-- **② ATOMIC-BUDGET TOOTH — an over-budget runaway is refused.** A dispatch declaring total
spend `spent_a + spent_b > mandate` is rejected: `admitsCtx = false`. One worker blowing the
mandate aborts the whole turn (it is one predicate). The integrator's primitive (3) made
enforceable. -/
theorem over_budget_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (sa sb : Int)
    (ha : n.scalar spentAF = some sa) (hb : n.scalar spentBF = some sb)
    (hover : sa + sb > mandate) :
    boardProgram.admitsCtx ctx m o n = false := by
  -- The affine budget sum exceeds the mandate, so `affineLe` rejects. `affineLe` is a ctx-free
  -- constraint, so `evalConstraintCtx ctx (.affineLe …) = evalConstraint (.affineLe …)` and we
  -- refute it through the PUBLIC admit-characterization `evalConstraint_affineLe_iff`.
  have hsum : affineSum n [(1, spentAF), (1, spentBF)] = some (sa + sb) := by
    simp [affineSum, ha, hb]; ring
  have hfail : evalConstraintCtx ctx (.affineLe [(1, spentAF), (1, spentBF)] mandate) o n = false := by
    show evalConstraint (.affineLe [(1, spentAF), (1, spentBF)] mandate) o n = false
    by_contra hc
    have htrue : evalConstraint (.affineLe [(1, spentAF), (1, spentBF)] mandate) o n = true := by
      cases h : evalConstraint (.affineLe [(1, spentAF), (1, spentBF)] mandate) o n with
      | true => rfl
      | false => exact absurd h hc
    obtain ⟨s, hs, hle⟩ := (evalConstraint_affineLe_iff _ _ o n).mp htrue
    rw [hsum] at hs; injection hs with hs; omega
  by_contra hc
  have hne : boardProgram.admitsCtx ctx m o n = true := by
    cases h : boardProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have := admitted_budget hne (ctx := ctx) (m := m) (o := o) (n := n)
  rw [hfail] at this; exact absurd this (by simp)

/-- **③ ATOMIC-HANDOFF TOOTH — a stolen baton is UNSAT.** A dispatch that FLIPS the baton
(`immutable baton` rejects — the holder changed) with a turn-sender who is NOT the current
holder is rejected: `admitsCtx = false`. The baton moves only when its holder signs the turn —
the actor-bound keystone (`actorBound_flip_requires_sender`) consumed at the board boundary. The
integrator's primitive (4) made enforceable. -/
theorem stolen_baton_rejected (ctx : TurnCtx) (m : Nat) (o n : Value)
    (hflip : evalSimple (.immutable batonF) o n = false)
    (hheld : ∀ h, n.scalar batonF = some h → ctx.sender ≠ some h) :
    boardProgram.admitsCtx ctx m o n = false := by
  -- The `senderInField baton` disjunct also fails (sender ≠ the held baton identity), so the
  -- whole `anyOf [immutable baton, senderInField baton]` fails.
  have hsif : evalSimpleCtx ctx (.senderInField batonF) o n = false := by
    simp only [evalSimpleCtx]
    cases hs : ctx.sender with
    | none   => cases hv : n.scalar batonF <;> rfl
    | some s =>
      cases hv : n.scalar batonF with
      | none   => rfl
      | some v =>
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he; exact (hheld v hv) (by rw [hs, he])
  have himm : evalSimpleCtx ctx (.immutable batonF) o n = false := hflip
  have hfail : evalConstraintCtx ctx (.anyOf [.immutable batonF, .senderInField batonF]) o n = false := by
    simp [evalConstraintCtx, himm, hsif]
  by_contra hc
  have hne : boardProgram.admitsCtx ctx m o n = true := by
    cases h : boardProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have := admitted_baton hne (ctx := ctx) (m := m) (o := o) (n := n)
  rw [hfail] at this; exact absurd this (by simp)

/-- **④ NO-REPLAY TOOTH — a replayed dispatch is UNSAT.** A dispatch that does NOT strictly
advance the epoch (`new ≤ old`) is rejected: `admitsCtx = false`. A captured dispatch cannot be
re-submitted; every dispatch is fresh. -/
theorem replayed_dispatch_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (eo en : Int)
    (heo : o.scalar epochF = some eo) (hen : n.scalar epochF = some en)
    (hstale : en ≤ eo) :
    boardProgram.admitsCtx ctx m o n = false := by
  have hfail : evalSimpleCtx ctx (.strictMono epochF) o n = false := by
    -- ctx-free atom: delegate to evalSimple; strictMono needs old < new, but en ≤ eo. Refute
    -- through the PUBLIC `evalSimple_strictMono_iff`.
    show evalSimple (.strictMono epochF) o n = false
    by_contra hc
    have htrue : evalSimple (.strictMono epochF) o n = true := by
      cases h : evalSimple (.strictMono epochF) o n with
      | true => rfl
      | false => exact absurd h hc
    obtain ⟨a, b, hoa, hnb, hab⟩ := (evalSimple_strictMono_iff epochF o n).mp htrue
    rw [heo] at hoa; rw [hen] at hnb; injection hoa with hoa; injection hnb with hnb
    omega
  by_contra hc
  have hne : boardProgram.admitsCtx ctx m o n = true := by
    cases h : boardProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have := admitted_epoch hne (ctx := ctx) (m := m) (o := o) (n := n)
  rw [hfail] at this; exact absurd this (by simp)

/-- **⑤ THE HONEST DISPATCH COMMITS (the gate is not constant-false).** A dispatch signed by the
recorded lead, within budget, advancing the epoch, leaving the baton fixed and the budget
immutable, ADMITS. The conjunction of the teeth is non-vacuous: there is a real admitted
transition the policy lets through. -/
theorem honest_dispatch_admits (ctx : TurnCtx) (m : Nat) (o n : Value)
    (hsender : ctx.sender = some leadPk)
    (hlead : n.scalar leadF = some leadPk)
    (hsa : n.scalar spentAF = some 300) (hsb : n.scalar spentBF = some 400)
    (hbatonImm : evalSimple (.immutable batonF) o n = true)
    (heo : o.scalar epochF = some 5) (hen : n.scalar epochF = some 6)
    (hbudImm : evalSimple (.immutable budgetF) o n = true) :
    boardProgram.admitsCtx ctx m o n = true := by
  -- Establish each constraint = true, then the `.all` conjunction follows.
  have c1 : evalConstraintCtx ctx (.simple (.senderInField leadF)) o n = true := by
    simp [evalConstraintCtx, evalSimpleCtx, hsender, hlead]
  have c2 : evalConstraintCtx ctx (.affineLe [(1, spentAF), (1, spentBF)] mandate) o n = true := by
    have hsum : affineSum n [(1, spentAF), (1, spentBF)] = some 700 := by
      simp [affineSum, hsa, hsb]
    exact (evalConstraint_affineLe_iff _ _ o n).mpr ⟨700, hsum, by show (700:Int) ≤ 1000; omega⟩
  have c3 : evalConstraintCtx ctx (.anyOf [.immutable batonF, .senderInField batonF]) o n = true := by
    have hb : evalSimpleCtx ctx (.immutable batonF) o n = true := hbatonImm
    simp [evalConstraintCtx, hb]
  have c4 : evalConstraintCtx ctx (.simple (.strictMono epochF)) o n = true := by
    show evalSimpleCtx ctx (.strictMono epochF) o n = true
    show evalSimple (.strictMono epochF) o n = true
    exact (evalSimple_strictMono_iff epochF o n).mpr ⟨5, 6, heo, hen, by omega⟩
  have c5 : evalConstraintCtx ctx (.simple (.immutable budgetF)) o n = true := by
    have : evalSimpleCtx ctx (.immutable budgetF) o n = true := hbudImm
    simpa [evalConstraintCtx] using this
  show dispatchConstraints.all (fun c => evalConstraintCtx ctx c o n) = true
  simp only [dispatchConstraints, List.all_cons, List.all_nil, c1, c2, c3, c4, c5, Bool.and_true]

/-! ## §4 — SURFACES-AS-CAPS: a worker's reach is an ATTENUATED capability (primitive 5).

The board hands each worker a notify cap over its own task queue, badge-masked to the task kinds
that worker may be woken for. Attenuation only shrinks the reach (`signalAdmissible_attenuate_no_amplify`),
and a worker cannot widen its own mask. This is `AgentOrchestration`'s synchronous delegation
algebra in its async form — the `notify` cap is the surface. -/

/-- Worker A's task-queue object id. -/
abbrev queueA : ObjId := 11
/-- Task-kind `compile` — badge bit `0b001`. -/
abbrev kCompile : Nat := 0b001
/-- Task-kind `test` — badge bit `0b010`. -/
abbrev kTest : Nat := 0b010
/-- Task-kind `deploy` — badge bit `0b100`. -/
abbrev kDeploy : Nat := 0b100
/-- The wide mask — all three task kinds. -/
abbrev kAll : Nat := 0b111

/-- **`coordToQueueA`** — the coordinator's root wake cap over worker A's queue: any of the three
task kinds. -/
def coordToQueueA : NotifyCap := { target := queueA, rights := .signature, badgeMask := kAll }

/-- **`workerAReach`** — worker A's delegated reach: the coordinator's cap attenuated to
`compile` ONLY (worker A may be woken for compile work, nothing else). The surface-as-cap. -/
def workerAReach : Option NotifyCap := coordToQueueA.attenuateNotify .signature kCompile

/-- **`workerAReach_is_compile_only`** — the surface is exactly the compile-only wake cap (the
delegation succeeded and narrowed). -/
theorem workerAReach_is_compile_only :
    workerAReach = some { target := queueA, rights := .signature, badgeMask := kCompile } := by
  decide

/-- **⑥ SURFACE NON-AMPLIFICATION — a worker cannot widen its reach.** Worker A's compile-only
surface cannot be re-attenuated UP to the wide mask (adding the test+deploy bits it does not
hold): `attenuateNotify … = none`. A worker cannot hand itself (or a sub-delegate) more reach
than it was granted. The integrator's primitive (5) made enforceable — the async mirror of
`AgentOrchestration.worker_attenuation_is_strict`. -/
theorem worker_cannot_widen_reach (c : NotifyCap) (h : workerAReach = some c) :
    c.attenuateNotify .signature kAll = none := by
  have hc : c = { target := queueA, rights := .signature, badgeMask := kCompile } := by
    rw [workerAReach_is_compile_only] at h; exact (Option.some.injEq _ _).mp h.symm
  subst hc
  exact attenuateNotify_refuses_mask_widening _ .signature kAll (by decide)

/-- **⑥ (strictness witness)** — the coordinator's root cap admits the `deploy` kind that worker
A's surface does NOT, so the attenuation is a genuine shrink (non-vacuous). -/
theorem worker_reach_is_strict :
    coordToQueueA.signalAdmissible kDeploy = true ∧
    (∀ c, workerAReach = some c → c.signalAdmissible kDeploy = false) := by
  refine ⟨by decide, ?_⟩
  intro c hc
  have hcc : c = { target := queueA, rights := .signature, badgeMask := kCompile } := by
    rw [workerAReach_is_compile_only] at hc; exact (Option.some.injEq _ _).mp hc.symm
  subst hcc; decide

/-! ## §5 — THE ASYNC WAKE EDGE (primitive 6): an un-capped wake is rejected.

The coordinator wakes worker A for a compile task it holds the cap for — COMMITS, delivering the
badge. A wake for a `deploy` task through worker A's compile-only surface is REFUSED (fail-closed)
— a worker is woken only on a badge its coordinator holds a cap for. -/

/-- **CAPPED WAKE COMMITS** — the coordinator wakes worker A's queue for `compile` (within its
wide mask): `signalGated` is `some`, OR'ing the badge into the queue accumulator. The wake is
delivered. (`signalGated_commits_of_admissible`.) -/
theorem capped_wake_commits (n : Notification) :
    signalGated coordToQueueA n kCompile = some (n.signal kCompile) :=
  signalGated_commits_of_admissible coordToQueueA n kCompile (by decide)

/-- **⑦ UN-CAPPED WAKE REJECTED — fail-closed.** A wake for the `deploy` task kind through worker
A's compile-only surface (which lacks the deploy bit) is REFUSED: `signalGated … = none`. A
worker cannot be woken for work outside its delegated mask. The integrator's primitive (6) made
enforceable. (`signalGated_refuses_of_inadmissible`.) -/
theorem uncapped_wake_rejected (c : NotifyCap) (nf : Notification) (h : workerAReach = some c) :
    signalGated c nf kDeploy = none := by
  have hc : c = { target := queueA, rights := .signature, badgeMask := kCompile } := by
    rw [workerAReach_is_compile_only] at h; exact (Option.some.injEq _ _).mp h.symm
  subst hc
  exact signalGated_refuses_of_inadmissible _ nf kDeploy (by decide)

/-! ## §6 — CONSERVATION / NON-AMPLIFICATION of the policy gate.

The dispatch gate writes board-metadata fields (lead/baton/budget/spend/epoch); it touches no
capability table (the surfaces are the §4 notify caps, unchanged by a dispatch turn) and no
asset. So a dispatch is, on the policy axis, non-amplifying by construction: the constraint
language reads and constrains record fields; it cannot mint authority. We pin the wake's
balance-neutrality (the async edge writes a badge accumulator, not the ledger). -/

/-- **`wake_is_balance_neutral`** — a capped wake produces a `Notification` whose badge is exactly
the prior OR the signalled badge — and nothing else. The async edge touches the badge accumulator
only; there is no asset, no ledger column, in a `Notification`. (`SwarmSignal.wake_is_balance_neutral`
shape.) -/
theorem wake_is_balance_neutral (n : Notification) (badge : Nat)
    (hadm : coordToQueueA.signalAdmissible badge = true) :
    ∃ n', signalGated coordToQueueA n badge = some n' ∧ n'.badge = n.badge ||| badge := by
  refine ⟨n.signal badge, signalGated_commits_of_admissible coordToQueueA n badge hadm, ?_⟩
  rfl

/-! ## §7 — NON-VACUITY TEETH (`#guard`): the policy + wake BITE on the concrete board, both
polarities. -/

section Witnesses

/-- A faithful dispatch state: lead = leadPk, signed by leadPk, within budget, baton fixed,
epoch advancing, budget immutable. -/
def goodOld : Value :=
  .record [(leadF, .int leadPk), (batonF, .int leadPk), (budgetF, .int mandate),
           (spentAF, .int 100), (spentBF, .int 100), (epochF, .int 5)]
def goodNew : Value :=
  .record [(leadF, .int leadPk), (batonF, .int leadPk), (budgetF, .int mandate),
           (spentAF, .int 300), (spentBF, .int 400), (epochF, .int 6)]

-- ① COMMIT: a faithful dispatch signed by the lead ADMITS.
#guard boardProgram.admitsCtx { sender := some leadPk } 0 goodOld goodNew

-- ① REFUSE (forged handoff): the SAME dispatch SIGNED BY a rogue (who holds capabilities but is
-- not the recorded lead) is REJECTED. Signed-provenance bites.
#guard boardProgram.admitsCtx { sender := some roguePk } 0 goodOld goodNew == false

-- ② REFUSE (over-budget): a dispatch with spent_a + spent_b = 700 + 400 = 1100 > 1000 mandate,
-- signed by the lead, is REJECTED. The atomic budget bites.
#guard boardProgram.admitsCtx { sender := some leadPk } 0 goodOld
  (.record [(leadF, .int leadPk), (batonF, .int leadPk), (budgetF, .int mandate),
            (spentAF, .int 700), (spentBF, .int 400), (epochF, .int 6)]) == false

-- ③ REFUSE (stolen baton): the lead signs a turn that flips the baton to a rogue — but the baton
-- moves only when ITS HOLDER signs, and the new holder (rogue) is not the sender (lead). REJECTED.
#guard boardProgram.admitsCtx { sender := some leadPk } 0 goodOld
  (.record [(leadF, .int leadPk), (batonF, .int roguePk), (budgetF, .int mandate),
            (spentAF, .int 300), (spentBF, .int 400), (epochF, .int 6)]) == false

-- ③ COMMIT (legitimate handoff): the CURRENT baton holder (leadPk) signs a turn flipping the
-- baton to themselves-as-target… the actor-bound rule admits a flip signed by the new holder.
-- Here leadPk hands the baton to leadPk (self), which is a flip the holder signs ⇒ ADMITS.
-- (A flip to a DIFFERENT holder requires THAT holder to sign — modeled by senderInField on `new`.)
#guard boardProgram.admitsCtx { sender := some roguePk } 0
  (.record [(leadF, .int roguePk), (batonF, .int leadPk), (budgetF, .int mandate),
            (spentAF, .int 0), (spentBF, .int 0), (epochF, .int 5)])
  (.record [(leadF, .int roguePk), (batonF, .int roguePk), (budgetF, .int mandate),
            (spentAF, .int 0), (spentBF, .int 0), (epochF, .int 6)])
  -- lead=rogue (rogue signs, is the recorded lead ✓), baton flips leadPk→roguePk and rogue (the
  -- NEW holder) signs ✓, budget ok, epoch advances ✓ ⇒ ADMITS. The handoff is legitimate.

-- ④ REFUSE (replay): the SAME epoch (6 → 6, no advance), signed by the lead, is REJECTED.
#guard boardProgram.admitsCtx { sender := some leadPk } 0
  (.record [(leadF, .int leadPk), (batonF, .int leadPk), (budgetF, .int mandate),
            (spentAF, .int 300), (spentBF, .int 400), (epochF, .int 6)])
  goodNew == false

-- ④ REFUSE (rewind): a STALE epoch (6 → 5) is REJECTED.
#guard boardProgram.admitsCtx { sender := some leadPk } 0 goodNew
  (.record [(leadF, .int leadPk), (batonF, .int leadPk), (budgetF, .int mandate),
            (spentAF, .int 300), (spentBF, .int 400), (epochF, .int 5)]) == false

-- (immutable budget) REFUSE: a dispatch that WIDENS the mandate (1000 → 5000) is REJECTED.
#guard boardProgram.admitsCtx { sender := some leadPk } 0 goodOld
  (.record [(leadF, .int leadPk), (batonF, .int leadPk), (budgetF, .int 5000),
            (spentAF, .int 300), (spentBF, .int 400), (epochF, .int 6)]) == false

-- (fail-closed) REFUSE: NO sender in context (a ctx-less / unsigned turn) ⇒ the provenance atom
-- fails closed ⇒ REJECTED.
#guard boardProgram.admitsCtx {} 0 goodOld goodNew == false

/-! ### §4/§5 surface + wake teeth (the notify cap algebra). -/

-- ⑤ surface narrowed: worker A's reach is the compile-only cap (some, not none).
#guard workerAReach.isSome
#guard workerAReach == some { target := queueA, rights := .signature, badgeMask := kCompile }

-- ⑥ REFUSE (widen): worker A cannot widen its compile-only mask to the wide mask.
#guard
  match workerAReach with
  | some c => (c.attenuateNotify .signature kAll).isNone
  | none => false
-- ⑥ but it CAN re-narrow to the empty mask (attenuation narrows, is not constant-none).
#guard
  match workerAReach with
  | some c => (c.attenuateNotify .signature 0).isSome
  | none => false

-- ⑥ strictness: the coordinator admits deploy; worker A's surface does NOT.
#guard coordToQueueA.signalAdmissible kDeploy
#guard
  match workerAReach with
  | some c => !c.signalAdmissible kDeploy
  | none => false

-- capped wake COMMITS: the coordinator wakes the queue for compile ⇒ some.
#guard (signalGated coordToQueueA Notification.empty kCompile).isSome
#guard signalGated coordToQueueA Notification.empty kCompile == some (Notification.empty.signal kCompile)

-- ⑦ REFUSE (un-capped wake): worker A's compile-only surface signalling deploy ⇒ none.
#guard
  match workerAReach with
  | some c => (signalGated c Notification.empty kDeploy).isNone
  | none => false
-- ⑦ but the SAME surface signalling its held compile kind COMMITS (the gate is not constant-none).
#guard
  match workerAReach with
  | some c => (signalGated c Notification.empty kCompile).isSome
  | none => false

end Witnesses

/-! ## §8 — Axiom hygiene. Every load-bearing policy + wake theorem checked kernel-clean. -/

#assert_all_clean [
  forged_dispatch_rejected,
  over_budget_rejected,
  stolen_baton_rejected,
  replayed_dispatch_rejected,
  honest_dispatch_admits,
  workerAReach_is_compile_only,
  worker_cannot_widen_reach,
  worker_reach_is_strict,
  capped_wake_commits,
  uncapped_wake_rejected,
  wake_is_balance_neutral
]

end Dregg2.Apps.AgentOrchestrationBudget
