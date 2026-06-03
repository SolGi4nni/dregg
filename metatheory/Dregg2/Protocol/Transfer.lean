/-
# Dregg2.Protocol.Transfer — an executable two-cell atomic token transfer.

A concrete instantiation of the abstract stack (`Core.Conservation`, `Boundary.TurnCoalg`,
and the `JointTurn` cross-cell `⊗`) as computable Lean. Two sovereign account-cells; a
transfer is the canonical cross-cell atomic turn — a debit on the sender ⊗ a credit on the
receiver, all-or-nothing (atomicity = the `will_succeed` cumulative AND), with the amount
debited exactly equal to the amount credited (CG-5, the conservation aggregate). The
protocol-level theorems are proved by `omega` for the concrete state.
-/
import Dregg2.Core
import Dregg2.Boundary
import Dregg2.Execution

namespace Dregg2.Protocol.Transfer

open Dregg2.Boundary Dregg2.Execution

/-- A fungible amount of the one asset. -/
abbrev Amount := Nat

/-- A sovereign account-cell's state: a single balance. -/
structure Acct where
  bal : Amount
deriving Repr, DecidableEq, Inhabited

/-- A cell's local move within a turn (its half of a joint turn, or a solo op). -/
inductive LocalOp where
  | debit (amt : Amount)
  | credit (amt : Amount)
  | noop
deriving Repr, DecidableEq

/-- **Fail-closed** local application: a lone debit beyond balance is a no-op (the cell
never goes negative — `Nat` has no debt; cf. `Core` conservation needing a group for
signed deltas). -/
def applyLocal (a : Acct) : LocalOp → Acct
  | .debit amt  => if amt ≤ a.bal then ⟨a.bal - amt⟩ else a
  | .credit amt => ⟨a.bal + amt⟩
  | .noop       => a

/-- **A cell as live codata** — the concrete `Boundary.TurnCoalg`: the observation is the
public balance; the transition applies a `LocalOp`, landing in another live `Acct` (never
a "final state"). This is `νF` made executable for one account-cell. -/
def acctCoalg : TurnCoalg Amount LocalOp where
  Carrier := Acct
  step a := (a.bal, fun op => applyLocal a op)

/-- The atomic two-cell transfer: debit sender ⊗ credit receiver, all-or-nothing.
`none` = the turn does NOT commit (the cumulative-AND prophecy failed); crucially there
is then no partial credit. -/
def transfer (sender receiver : Acct) (amt : Amount) : Option (Acct × Acct) :=
  if amt ≤ sender.bal then
    some (⟨sender.bal - amt⟩, ⟨receiver.bal + amt⟩)
  else
    none

/-- `will_succeed` prophecy = the cumulative AND over participants (here the single debit
guard). Atomicity is this PROOF property, not a live coordinator. -/
def willSucceed (sender : Acct) (amt : Amount) : Bool := decide (amt ≤ sender.bal)

/-! ## It runs (`#eval`). -/

/-- Alice starts with 100. -/
def alice : Acct := ⟨100⟩
/-- Bob starts with 5. -/
def bob : Acct := ⟨5⟩

#eval transfer alice bob 30    -- some ({ bal := 70 }, { bal := 35 })
#eval transfer alice bob 200   -- none   (atomic reject — Bob is NOT credited)
#eval willSucceed alice 30     -- true
#eval (acctCoalg.next alice (.credit 7)).bal   -- 107  (the coalgebra steps as codata)
#eval (acctCoalg.next alice (.debit 40)).bal   -- 60

/-! ## And it is PROVED (no `sorry`). -/

/-- **Conservation — Law 1, proved by computation:** total supply is invariant across any
committed transfer (the concrete instance of `Core.conservation_ordinary` / the JointTurn
CG-5 aggregate). -/
theorem transfer_conserves (sender receiver : Acct) (amt : Amount) {s' r' : Acct}
    (h : transfer sender receiver amt = some (s', r')) :
    s'.bal + r'.bal = sender.bal + receiver.bal := by
  obtain ⟨sb⟩ := sender; obtain ⟨rb⟩ := receiver
  unfold transfer at h
  by_cases hb : amt ≤ sb
  · rw [if_pos hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    change (sb - amt) + (rb + amt) = sb + rb
    simp only [Amount] at *
    omega
  · rw [if_neg hb] at h
    simp at h

/-- **CG-5 (the cross-cell conservation aggregate), proved:** the amount the sender loses
exactly equals the amount the receiver gains — the signed half-edges cancel (`-amt + +amt
= 0`), here as the bilateral `out = in` equality over `Nat`. -/
theorem transfer_cg5 (sender receiver : Acct) (amt : Amount) {s' r' : Acct}
    (h : transfer sender receiver amt = some (s', r')) :
    sender.bal - s'.bal = r'.bal - receiver.bal := by
  obtain ⟨sb⟩ := sender; obtain ⟨rb⟩ := receiver
  unfold transfer at h
  by_cases hb : amt ≤ sb
  · rw [if_pos hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    change sb - (sb - amt) = (rb + amt) - rb
    simp only [Amount] at *
    omega
  · rw [if_neg hb] at h
    simp at h

/-- **Atomicity — proved:** the transfer commits iff `willSucceed` (the cumulative AND);
on failure it returns `none`, so NEITHER cell moves (all-or-nothing, no partial credit). -/
theorem transfer_atomic (sender receiver : Acct) (amt : Amount) :
    (transfer sender receiver amt).isSome = willSucceed sender amt := by
  unfold transfer willSucceed
  by_cases hb : amt ≤ sender.bal <;> simp [hb]

/-- **No value created from a failed turn:** a non-committing transfer leaves both cells
exactly as they were (there is no state to read back — `none` — so the cells are
untouched). Stated as: failure ⇒ `willSucceed = false`. -/
theorem transfer_fail_no_credit (sender receiver : Acct) (amt : Amount)
    (h : transfer sender receiver amt = none) :
    willSucceed sender amt = false := by
  unfold transfer at h
  unfold willSucceed
  by_cases hb : amt ≤ sender.bal
  · rw [if_pos hb] at h; simp at h
  · simp [hb]

/-! ## A userspace program: the two-party payment channel, conserved over its WHOLE run. -/

/-- The two-party payment **channel** as a transition system (`Execution.System`): a
configuration is the pair of account-cells; a step is a committed transfer in EITHER
direction. This is a "userspace program" built from the Transfer protocol. -/
def channel : System where
  Config := Acct × Acct
  Step s t := ∃ amt : Amount,
    transfer s.1 s.2 amt = some t ∨ transfer s.2 s.1 amt = some (t.2, t.1)

/-- Total supply held across the channel. -/
def total (s : Acct × Acct) : Nat := s.1.bal + s.2.bal

/-- **Every channel step conserves total supply — PROVED** (both directions, from
`transfer_conserves`). -/
theorem channel_step_conserves {s t : Acct × Acct} (h : channel.Step s t) :
    total t = total s := by
  obtain ⟨amt, hd⟩ := h
  rcases hd with h1 | h2
  · have hc := transfer_conserves s.1 s.2 amt h1
    simp only [total, Amount] at *; omega
  · have hc := transfer_conserves s.2 s.1 amt h2
    simp only [total, Amount] at *; omega

/-- **Conservation over an entire channel execution.** For any run of arbitrarily many
transfers in either direction, total supply equals its initial value.
`Execution.invariant_run` lifts the per-step `channel_step_conserves` to the trace. -/
theorem channel_run_conserves {s t : Acct × Acct} (hrun : Run channel s t) :
    total t = total s := by
  have hpres : StepInvariant channel (fun c => total c = total s) := by
    intro a b ha hstep
    rw [channel_step_conserves hstep]; exact ha
  exact invariant_run hpres hrun rfl

/-- An executable batch runner over the channel (`(direction, amount)` list). -/
def runBatch : Acct × Acct → List (Bool × Amount) → Option (Acct × Acct)
  | s, [] => some s
  | s, (dir, amt) :: rest =>
      let stepped := if dir then transfer s.1 s.2 amt
                     else (transfer s.2 s.1 amt).map (fun p => (p.2, p.1))
      match stepped with
      | some s' => runBatch s' rest
      | none    => none

#eval runBatch (alice, bob) [(true, 30), (false, 10), (true, 5)]
  -- some ({ bal := 75 }, { bal := 30 })   — total 105 preserved throughout

end Dregg2.Protocol.Transfer
