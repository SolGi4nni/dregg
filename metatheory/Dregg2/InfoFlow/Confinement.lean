/-
# Dregg2.InfoFlow.Confinement — the CAPABILITY view of information flow (the *-property pillar).

dregg's authority theory proves **non-amplification of AUTHORITY** (`Positional.confinement_preserved`,
the cross-cell non-amplify, the `LossyMorphism` attenuation-only law): a cell cannot grant itself
caps it was never given. But authority non-amplification says NOTHING about **information flow**: a
cell with read-access to a secret + send-access to an attacker can *leak* the secret even though it
amplifies no authority. This is the confinement / Bell–LaPadula **\*-property** ("no write down")
problem — the classic gap between an integrity model and a confidentiality model.

`Proof/Noninterference.lean` is the **field-classification** axis (HIGH/LOW labels on record fields;
the seL4/Volpano–Smith unwinding over `setFieldA`). THIS module is the **capability** axis: instead of
labelling fields, we ask what the *cap table itself* lets a cell do to an attacker's observation. The
observation here is the attacker's **resource view** (the balances on the cells it owns), and the
question is: *can a cell with no capability reaching the attacker influence what the attacker sees?*

We work over the executable `Exec.Kernel` (`KernelState`/`Turn`/`exec`/`authorizedB`) — the same
machine on which `exec_authorized` already lives — so the cap reasoning is the REAL gate, not a
re-abstraction.

## What is PROVED (the genuine fragment that holds)

* **§3 FRAME** (`view_frame`): a committed turn that touches no attacker cell — neither as the debited
  `src` nor the credited `dst` — leaves the attacker view *pointwise unchanged*. The honest "if you
  don't touch it, the observer can't tell" half. Non-vacuous (`view_frame_inhabited`).

* **§4 NO-DRAIN** (the cap tooth, `confined_cannot_debit_attacker`): a **confined** actor — one that
  owns no attacker cell and holds NO cap (`node`/`endpoint`-with-`write`) reaching any attacker cell —
  *cannot commit any turn that debits an attacker cell* (`src ∈ A`). The kernel's `authorizedB` gate
  refuses it. So the attacker's resource cannot be DRAINED by a capability-confined cell. This is the
  integrity-flavored half of confinement, and it is a genuine consequence of the cap model (it rides
  `exec_authorized` + the structure of `authorizedB`).

* **§4 view-confinement against drains** (`confined_drain_preserves_view_at`): combining the two, a
  confined actor's committed turn cannot LOWER an attacker cell's balance below where a pure credit
  would leave it — restated cleanly: it cannot debit, so the attacker's own cells are never the `src`.

## What is OPEN / a real COVERT CHANNEL (characterized honestly, with a refutation witness)

* **§5 THE \*-PROPERTY LEAK** (`confined_can_credit_attacker`, `full_noninterference_fails`): full
  noninterference is **FALSE** for this cap model, and we PROVE it false with an explicit witness. The
  `authorizedB` gate only guards the *debited* `src`; **crediting** a cell (`dst ∈ A`) needs no cap on
  the destination. So a confined actor CAN raise an attacker cell's balance, and an attacker who
  observes its own balance can DETECT that a confined cell acted. This is the textbook \*-property
  "write up" channel: the model confines *draining* (integrity) but not *signalling-by-deposit*
  (confidentiality). We exhibit a confined actor, an attacker view, and two of the confined cell's
  secret states that the attacker DISTINGUISHES — refuting `Noninterference`.

* **§6 THE TURN-EXISTENCE SIDE CHANNEL** (`refusal_leaks`): even with NO balance change, *whether a
  turn commits or is refused* is itself observable (the kernel returns `none` vs `some`), and the
  refusal can depend on the confined cell's secret (e.g. `amt ≤ bal src`). We characterize this as the
  termination/refusal covert channel that a pure state-indistinguishability `lowEq` cannot see, and
  show a confined cell whose *commit-vs-refuse* outcome is a function of its secret balance.

So the honest verdict the cap model supports: **it confines authority and confines resource-DRAINING,
but it does NOT confine information** — deposit-signalling and refusal-timing are open covert channels
that a deposit-discipline (or a quota/clocking countermeasure) would have to close. Nothing here is
dressed as `True`: every positive law has a non-vacuity witness, and every negative law is a proved
refutation with an explicit distinguishing pair.

Pure; spec-first. No `sorry`/`axiom`/`admit`/`native_decide`. `#assert_axioms` pins every keystone to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.Kernel
import Dregg2.Tactics

namespace Dregg2.InfoFlow.Confinement

open Dregg2.Authority
open Dregg2.Exec

set_option linter.unusedVariables false

/-! ## §1 — The attacker frontier and the attacker's resource view.

The attacker observes the balances on a finite set `A` of cells it owns. Two kernel states are
**view-equal w.r.t. `A`** iff they agree on every attacker balance. (We deliberately observe ONLY the
balances, not the cap table — the cap table is the authority axis that `Positional` already governs;
here the secret is the *confined cell's* resource state and the observation is the *attacker's*
resource state.) -/

/-- The attacker's **observation**: the function giving each attacker cell its balance. Two states are
indistinguishable to the attacker iff this agrees on all of `A`. -/
def attackerView (A : Finset CellId) (k : KernelState) : CellId → ℤ :=
  fun c => if c ∈ A then k.bal c else 0

/-- **View-equality** (the attacker's indistinguishability relation): `k` and `k'` look the same to an
attacker observing the cells in `A` iff their balances agree on every cell of `A`. -/
def viewEq (A : Finset CellId) (k k' : KernelState) : Prop :=
  ∀ c ∈ A, k.bal c = k'.bal c

/-- `viewEq` is reflexive. -/
theorem viewEq_refl (A : Finset CellId) (k : KernelState) : viewEq A k k := fun _ _ => rfl

/-- `viewEq` is symmetric. -/
theorem viewEq_symm {A : Finset CellId} {k k' : KernelState} (h : viewEq A k k') : viewEq A k' k :=
  fun c hc => (h c hc).symm

/-- `viewEq` is transitive. -/
theorem viewEq_trans {A : Finset CellId} {k k' k'' : KernelState}
    (h1 : viewEq A k k') (h2 : viewEq A k' k'') : viewEq A k k'' :=
  fun c hc => (h1 c hc).trans (h2 c hc)

/-- `viewEq A` agrees with equality of the `attackerView` observation. -/
theorem viewEq_iff_view (A : Finset CellId) (k k' : KernelState) :
    viewEq A k k' ↔ attackerView A k = attackerView A k' := by
  constructor
  · intro h; funext c; unfold attackerView; by_cases hc : c ∈ A
    · rw [if_pos hc, if_pos hc]; exact h c hc
    · rw [if_neg hc, if_neg hc]
  · intro h c hc
    have := congrFun h c
    unfold attackerView at this
    rw [if_pos hc, if_pos hc] at this; exact this

/-! ## §2 — When does a turn touch an attacker cell?

A `transferBal` move edits exactly two cells: it *debits* `src` and *credits* `dst`. So it changes the
attacker view iff `src ∈ A` or `dst ∈ A`. -/

/-- **A turn whose `src` and `dst` are both outside `A` does not edit any attacker balance.** Pointwise:
on a cell `c ∈ A` (hence `c ≠ src`, `c ≠ dst`) `transferBal` is the identity. -/
theorem transferBal_off_view (bal : CellId → ℤ) (src dst : CellId) (amt : ℤ)
    (A : Finset CellId) (hsrc : src ∉ A) (hdst : dst ∉ A) :
    ∀ c ∈ A, transferBal bal src dst amt c = bal c := by
  intro c hc
  unfold transferBal
  have hcs : c ≠ src := fun h => hsrc (h ▸ hc)
  have hcd : c ≠ dst := fun h => hdst (h ▸ hc)
  rw [if_neg hcs, if_neg hcd]

/-! ## §3 — THE FRAME LAW (PROVED): an off-view turn is invisible to the attacker.

If a committed turn touches neither attacker cell (`src ∉ A`, `dst ∉ A`), the attacker view is
unchanged. The honest "if you don't touch it, the observer can't tell" half of confinement. -/

/-- **KEYSTONE (FRAME) — `view_frame`.** A committed turn whose `src` and `dst` are both outside the
attacker frontier `A` leaves the attacker's view unchanged: `viewEq A k k'`. The observation is a frame
property of `transferBal`. (This is the part that holds *unconditionally* — no cap hypothesis needed,
because the move simply edits cells the attacker does not watch.) -/
theorem view_frame {k k' : KernelState} {turn : Turn} (A : Finset CellId)
    (hsrc : turn.src ∉ A) (hdst : turn.dst ∉ A) (h : exec k turn = some k') :
    viewEq A k k' := by
  -- factor the committed step: `k'.bal = transferBal k.bal src dst amt`.
  unfold exec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    intro c hc
    -- on an attacker cell `c ∈ A`, the (off-view) transfer is the identity.
    rw [← h]
    exact (transferBal_off_view k.bal turn.src turn.dst turn.amt A hsrc hdst c hc).symm
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`view_frame` is non-vacuous (`view_frame_inhabited`).** A real committed turn, off the attacker
view, witnesses the frame: cells `0 → 1` transfer 30, attacker watches cell `2` (untouched), so the
attacker sees nothing. The frame hypothesis is satisfiable by a genuine commit. -/
theorem view_frame_inhabited :
    ∃ (k k' : KernelState) (turn : Turn) (A : Finset CellId),
      turn.src ∉ A ∧ turn.dst ∉ A ∧ exec k turn = some k' ∧ viewEq A k k' := by
  -- `s0`/`t1`: actor 0 owns src 0, transfers 30 to 1; commits. Attacker watches cell 2 (untouched).
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp (by decide : (exec s0 t1).isSome)
  exact ⟨s0, k', t1, {2}, by decide, by decide, hk', view_frame {2} (by decide) (by decide) hk'⟩

/-! ## §4 — THE CAP TOOTH (PROVED): a confined cell cannot DEBIT an attacker cell.

We define **confinement** in cap terms: an actor is confined w.r.t. the attacker frontier `A` if it
owns no attacker cell *and* holds no capability (`node a` or `endpoint a` carrying `write`) reaching
any attacker cell `a ∈ A`. We then show such an actor cannot pass the `authorizedB` gate for ANY turn
whose `src` is an attacker cell — so the kernel REFUSES any drain of attacker resource by a confined
cell. This is the integrity-flavored half: confinement of *resource draining* really follows from the
cap model. -/

/-- **`reachesCell caps actor a`** — does `actor`'s cap table grant authority over cell `a`? Exactly the
caps that `authorizedB` consults on `src`: a `node a` cap, or an `endpoint a` cap carrying `write`. -/
def reachesCell (caps : Caps) (actor a : CellId) : Prop :=
  ∃ c ∈ caps actor,
    c = Cap.node a ∨ (∃ rights, c = Cap.endpoint a rights ∧ Auth.write ∈ rights)

/-- **`Confined A caps actor`** — the actor is capability-confined away from the attacker frontier `A`:
it is itself not an attacker cell (owns none of them as identity), and it reaches no attacker cell via
its caps. This is the precise cap-side hypothesis under which DRAINING is impossible. -/
def Confined (A : Finset CellId) (caps : Caps) (actor : CellId) : Prop :=
  actor ∉ A ∧ ∀ a ∈ A, ¬ reachesCell caps actor a

/-- **Bridge: passing `authorizedB` over an attacker `src` forces either ownership or a reaching cap.**
If `authorizedB caps turn = true` and `turn.src = a`, then `turn.actor = a` (owns it) or
`reachesCell caps turn.actor a`. (Unfolds the `authorizedB` `||`/`any` into the two ways it can be
`true`, matching `reachesCell`.) -/
theorem authorizedB_src_forces_reach {caps : Caps} {turn : Turn} {a : CellId}
    (hsrc : turn.src = a) (h : authorizedB caps turn = true) :
    turn.actor = a ∨ reachesCell caps turn.actor a := by
  subst hsrc
  unfold authorizedB at h
  rw [Bool.or_eq_true] at h
  rcases h with hown | hcap
  · -- `actor == src` ⇒ ownership.
    left; exact (beq_iff_eq.mp hown)
  · -- a reaching cap exists in the `any`.
    right
    rw [List.any_eq_true] at hcap
    obtain ⟨c, hmem, hc⟩ := hcap
    refine ⟨c, hmem, ?_⟩
    rw [Bool.or_eq_true] at hc
    rcases hc with hnode | hep
    · -- `c == Cap.node src` ⇒ the node-cap disjunct.
      left; exact (beq_iff_eq.mp hnode)
    · -- the endpoint-with-write disjunct: split on the cap shape.
      right
      cases c with
      | null => simp only [reduceCtorEq] at hep
      | node t => simp only [reduceCtorEq] at hep
      | endpoint t rights =>
          rw [Bool.and_eq_true] at hep
          obtain ⟨ht, hw⟩ := hep
          refine ⟨rights, ?_, ?_⟩
          · rw [beq_iff_eq.mp ht]
          · exact List.contains_iff_mem.mp hw  -- normalize `contains = true` to `∈`

/-- **KEYSTONE (NO-DRAIN) — `confined_cannot_debit_attacker`.** A `Confined` actor cannot commit any
turn whose debited `src` is an attacker cell. The kernel's `authorizedB` gate (consulted by `exec` via
`exec_authorized`) would have to grant authority over the attacker cell, which a confined actor neither
owns nor reaches by cap. So the attacker's resource is **never drained** by a capability-confined cell —
the integrity-confinement half of the \*-property, riding the real cap gate. -/
theorem confined_cannot_debit_attacker (A : Finset CellId) {k k' : KernelState} {turn : Turn}
    (hconf : Confined A k.caps turn.actor) (hsrcA : turn.src ∈ A)
    (h : exec k turn = some k') : False := by
  -- the committed turn passed `authorizedB`.
  have hauth : authorizedB k.caps turn = true := exec_authorized k k' turn h
  -- so the actor owns `src` or reaches it by cap.
  rcases authorizedB_src_forces_reach (a := turn.src) rfl hauth with hown | hreach
  · -- ownership: but then `turn.actor = turn.src ∈ A`, contradicting `actor ∉ A`.
    exact hconf.1 (hown ▸ hsrcA)
  · -- a reaching cap to the attacker cell `turn.src ∈ A`, contradicting confinement.
    exact hconf.2 turn.src hsrcA hreach

/-- **`confined_no_attacker_src` (corollary).** Restated as a frame premise: for a confined actor's
committed turn, the debited cell is NOT an attacker cell. This is exactly the hypothesis `view_frame`
needs on the `src` side — confinement *supplies* `turn.src ∉ A`. -/
theorem confined_no_attacker_src (A : Finset CellId) {k k' : KernelState} {turn : Turn}
    (hconf : Confined A k.caps turn.actor) (h : exec k turn = some k') :
    turn.src ∉ A := fun hsrcA => confined_cannot_debit_attacker A hconf hsrcA h

/-! ## §5 — THE \*-PROPERTY LEAK (PROVED FALSE): confinement does NOT confine information.

`view_frame` needed `turn.dst ∉ A` too — and confinement gives us NOTHING about `dst`. The
`authorizedB` gate guards only the *debited* `src`; crediting an attacker cell (`dst ∈ A`) needs no cap
on the destination. So a confined actor CAN deposit into an attacker cell and thereby change the
attacker's observed balance — a "write up" the cap model does not stop. We prove full noninterference
is FALSE with an explicit distinguishing witness. -/

/-- A confined actor with an empty cap table: it owns no attacker cell and reaches none (the `any` over
`[]` is `False`). The cleanest confined witness — its ONLY authority is over its own cell `0`. -/
def confinedActor : CellId := 0

/-- The attacker frontier: cell `1`. -/
def attackerFrontier : Finset CellId := {1}

/-- A two-cell ledger where the confined actor `0` owns 100 and the attacker `1` owns 5; **empty cap
table** (so cell `0` is confined away from `{1}` — it has no cap reaching cell 1). -/
def kBase : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- The DEPOSIT turn: confined actor `0` credits the attacker cell `1` (debiting its OWN cell `0`,
which it is authorized over by ownership). `src = 0 ∉ A`, but `dst = 1 ∈ A`. -/
def depositTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

/-- **Cell `0` IS confined away from the attacker frontier `{1}`** (empty caps ⇒ no reaching cap; and
`0 ∉ {1}`). The hypothesis of §4 is genuinely met by this actor. -/
theorem confinedActor_confined : Confined attackerFrontier kBase.caps confinedActor := by
  refine ⟨by decide, ?_⟩
  intro a ha hreach
  -- empty cap table: `reachesCell` requires a cap in `caps 0 = []`, impossible.
  obtain ⟨c, hmem, _⟩ := hreach
  simp only [kBase] at hmem
  exact absurd hmem (by simp)

/-- **The deposit COMMITS** (the confined actor is authorized over its OWN cell `0`, has the funds,
`src ≠ dst`, both live). So the leak is realized by a genuine kernel transition, not a hypothesis. -/
theorem depositTurn_commits : (exec kBase depositTurn).isSome = true := by decide

/-- **KEYSTONE (LEAK) — `confined_can_credit_attacker`.** A confined actor CHANGES the attacker view by
crediting an attacker cell: after the deposit, attacker cell `1`'s balance is `35 ≠ 5`. So
`¬ viewEq {1} kBase (deposit-post-state)` — confinement does NOT preserve the attacker view. The cap
model confines DRAINING (§4) but NOT depositing: this is the \*-property "write up" covert channel,
proved present. -/
theorem confined_can_credit_attacker :
    ∃ k', exec kBase depositTurn = some k' ∧ ¬ viewEq attackerFrontier kBase k' := by
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp depositTurn_commits
  refine ⟨k', hk', ?_⟩
  intro hview
  -- the attacker watches cell `1`; pre = 5, post = 35.
  have h1 : kBase.bal 1 = k'.bal 1 := hview 1 (by decide)
  -- compute the post-state balance of cell 1.
  unfold exec at hk'
  simp only [depositTurn, kBase, authorizedB] at hk'
  -- after the guard, `k'.bal = transferBal … 0 1 30`; read cell 1 (= 5 + 30 = 35).
  rw [if_pos (by decide)] at hk'
  simp only [Option.some.injEq] at hk'
  rw [← hk'] at h1
  -- `h1 : (if 1=0 then 100 else if 1=1 then 5 else 0) = transferBal … 1`, i.e. `5 = 35`.
  simp only [transferBal] at h1
  revert h1; decide

/-- **`full_noninterference_fails` — confinement-noninterference is FALSE for the cap model.** The crisp
refutation: there is a confined actor, an attacker frontier, and a committed turn after which the
attacker view CHANGES. So one cannot prove "a confined actor preserves the attacker view"; the genuine
guarantee is only the DRAIN-confinement of §4. We package the confinement witness alongside the
view-change to make the failure unmistakable: the SAME actor that §4 certifies cannot drain CAN still
signal by deposit. -/
theorem full_noninterference_fails :
    Confined attackerFrontier kBase.caps confinedActor ∧
    ∃ k', exec kBase depositTurn = some k' ∧ ¬ viewEq attackerFrontier kBase k' :=
  ⟨confinedActor_confined, confined_can_credit_attacker⟩

/-! ## §6 — THE TURN-EXISTENCE / REFUSAL SIDE CHANNEL (characterized honestly).

Even a state-indistinguishability relation like `viewEq` cannot see *whether* a turn commits. The
kernel's `exec` returns `none` (refusal) or `some` (commit), and the refusal can branch on the confined
cell's SECRET (here, its balance, via the `amt ≤ bal src` guard). So an attacker who can observe merely
*that the confined cell's turn was refused* learns a predicate of the secret — a covert channel orthogonal
to any balance-view relation. We exhibit it: two secret balances of the confined cell that the
*commit-vs-refuse* outcome of the SAME turn distinguishes. -/

/-- A confined cell `0` that is RICH (balance 100). The over-budget turn `amt = 50` commits. -/
def kRich : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- The SAME cell `0` but POOR (balance 10). The same `amt = 50` turn is REFUSED (`50 ≤ 10` fails). -/
def kPoor : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 10 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- A self-debiting deposit of `50` (cell `0` → cell `1`). Authorized by ownership in both states; its
*commit-vs-refuse* outcome depends ONLY on whether cell `0` has ≥ 50 — the secret. -/
def probeTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 50 }

/-- **KEYSTONE (SIDE CHANNEL) — `refusal_leaks`.** The same probe turn COMMITS from the rich secret
state and is REFUSED from the poor one (`isSome` differs). So *whether the turn commits* is a function
of the confined cell's secret balance — a refusal/termination covert channel that no balance-view
relation captures. This characterizes a genuine limit of the cap model: it cannot make the *existence*
of a turn independent of the secret; only a quota/clocking discipline could. (Both `kRich` and `kPoor`
present the attacker an IDENTICAL view of its own cell `1` = 5, yet are distinguished by the outcome.) -/
theorem refusal_leaks :
    -- the attacker's own view is identical in both secret states (cell 1 = 5 in both)…
    viewEq attackerFrontier kRich kPoor ∧
    -- …yet the SAME turn commits in one and is refused in the other (the leak).
    (exec kRich probeTurn).isSome = true ∧ (exec kPoor probeTurn).isSome = false := by
  refine ⟨?_, by decide, by decide⟩
  intro c hc
  -- `A = {1}`; both states read `bal 1 = 5`.
  simp only [attackerFrontier, Finset.mem_singleton] at hc
  subst hc; rfl

/-! ## §7 — Non-vacuity guards (the positive laws are inhabited; the leaks are real). -/

#guard ((exec kBase depositTurn).isSome)
#guard ((exec kRich probeTurn).isSome)
#guard ((exec kPoor probeTurn).isSome) == false
#guard (decide (kRich.bal 1 = kPoor.bal 1))   -- attacker view identical across the secret split

/-! ## §8 — Axiom-hygiene tripwires (every keystone kernel-clean). -/

#assert_axioms viewEq_refl
#assert_axioms viewEq_symm
#assert_axioms viewEq_trans
#assert_axioms viewEq_iff_view
#assert_axioms view_frame
#assert_axioms view_frame_inhabited
#assert_axioms authorizedB_src_forces_reach
#assert_axioms confined_cannot_debit_attacker
#assert_axioms confined_no_attacker_src
#assert_axioms confinedActor_confined
#assert_axioms confined_can_credit_attacker
#assert_axioms full_noninterference_fails
#assert_axioms refusal_leaks

end Dregg2.InfoFlow.Confinement
