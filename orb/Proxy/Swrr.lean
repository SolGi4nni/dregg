/-
Swrr — SMOOTH weighted round-robin (the burst-free schedule).

Interval WRR (`Proxy.Wrr`) is exactly fair over a full cycle but BURSTY under
skew: weights `{5,1,1}` produce `a a a a a b c` — backend `a` takes five
consecutive requests. The smooth variant spreads each backend's share evenly
through the cycle: the same weights produce `a a b a c a a` — the skewed
backend's hits are interleaved with the others'.

The algorithm (the reference one, as shipped by mainstream proxies): each
backend carries a signed `current` counter, initially 0. Per selection round

  1. every backend's `current` increases by its configured weight;
  2. the backend with the GREATEST `current` is selected (earliest wins ties);
  3. the selected backend's `current` decreases by the pool's total weight.

Theorems (the algorithm-spec conformance for each step of the round):

  * `swrrStep_argmax`  — **the selection rule**: the emitted backend attained
    the maximal post-bump `current` over the whole pool (steps 1–2 exactly);
  * `swrrStep_mem` / `swrrStep_total` — soundness and totality of a round;
  * `swrrStep_sum` / `swrrRun_sum_zero` — **the balance invariant**: a round
    conserves the summed `current` (step 1 adds the total weight, step 3
    removes exactly it), so from the all-zero start the summed counter is 0
    forever — selection debt neither accumulates nor leaks;
  * `bump_ids` / `deduct_ids` / `swrrStep_entIds` — a round moves counters
    only: the backend snapshots (ids, weights, health) are never touched.

Exact PER-CYCLE fairness (each backend selected weight-many times per
`totalWeight` rounds) and the burst-spread itself are exercised over concrete
pools in `Proxy.LbChecks` by full evaluation; the general per-cycle theorem
for the smooth variant is future depth — the interval variant's
`wrr_window_weight` remains the proven fairness anchor.
-/

import Proxy.Balance

namespace Proxy

/-- One smooth-WRR pool entry: the backend snapshot plus its signed running
`current` counter. -/
abbrev SwrrEntry := Backend × Int

/-- The smooth-WRR state for a pool: one counter per backend, initially 0. -/
def swrrInit (bs : List Backend) : List SwrrEntry :=
  bs.map (fun b => (b, (0 : Int)))

/-- The pool's total weight, as the signed decrement of step 3. -/
def totalWeightZ (s : List SwrrEntry) : Int :=
  (totalWeight (s.map Prod.fst) : Int)

/-- Step 1: every backend's counter grows by its configured weight. -/
def bump (s : List SwrrEntry) : List SwrrEntry :=
  s.map (fun e => (e.1, e.2 + (e.1.weight : Int)))

/-- Step 2's argmax: the entry with the greatest counter, earliest wins ties. -/
def pickMax : List SwrrEntry → Option SwrrEntry
  | [] => none
  | e :: es =>
    match pickMax es with
    | none => some e
    | some m => if m.2 ≤ e.2 then some e else some m

/-- Step 3: the selected backend (by id) pays back the total weight. -/
def deduct (bid : Nat) (d : Int) (s : List SwrrEntry) : List SwrrEntry :=
  s.map (fun e => if e.1.id = bid then (e.1, e.2 - d) else e)

/-- One smooth-WRR round: bump, pick the maximal counter, deduct the total
weight from the winner. Emits the chosen backend and the successor state. -/
def swrrStep (s : List SwrrEntry) : Option Backend × List SwrrEntry :=
  match pickMax (bump s) with
  | none => (none, bump s)
  | some e => (some e.1, deduct e.1.id (totalWeightZ s) (bump s))

/-- Run `n` rounds, collecting the emitted backend ids oldest-first. -/
def swrrRun : Nat → List SwrrEntry → List (Option Nat) × List SwrrEntry
  | 0, s => ([], s)
  | n + 1, s =>
    let r := swrrStep s
    let rest := swrrRun n r.2
    (r.1.map Backend.id :: rest.1, rest.2)

/-! ### Argmax soundness -/

theorem pickMax_total {s : List SwrrEntry} (h : s ≠ []) :
    (pickMax s).isSome := by
  cases s with
  | nil => exact absurd rfl h
  | cons e rest =>
    cases hr : pickMax rest with
    | none => simp [pickMax, hr]
    | some m => by_cases hb : m.2 ≤ e.2 <;> simp [pickMax, hr, hb]

theorem pickMax_mem {s : List SwrrEntry} {e : SwrrEntry}
    (h : pickMax s = some e) : e ∈ s := by
  induction s generalizing e with
  | nil => cases h
  | cons f rest ih =>
    cases hr : pickMax rest with
    | none =>
      simp only [pickMax, hr] at h
      cases h
      exact List.mem_cons_self f rest
    | some m =>
      simp only [pickMax, hr] at h
      split at h
      · cases h; exact List.mem_cons_self f rest
      · cases h; exact List.mem_cons_of_mem _ (ih hr)

/-- **The selection rule, verbatim.** The picked entry's counter is maximal
over the whole pool: no other backend had a strictly greater `current`. -/
theorem pickMax_max {s : List SwrrEntry} {e : SwrrEntry}
    (h : pickMax s = some e) : ∀ f ∈ s, f.2 ≤ e.2 := by
  induction s generalizing e with
  | nil => cases h
  | cons g rest ih =>
    intro f hf
    cases hr : pickMax rest with
    | none =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons x xs =>
          have := pickMax_total (s := x :: xs) (by intro hx; cases hx)
          rw [hr] at this
          cases this
      simp only [pickMax, hr] at h
      cases h
      rcases List.mem_cons.mp hf with hf' | hf'
      · rw [hf']; exact Int.le_refl _
      · rw [hrest] at hf'; cases hf'
    | some m =>
      simp only [pickMax, hr] at h
      split at h
      · rename_i hle
        cases h
        rcases List.mem_cons.mp hf with hf' | hf'
        · rw [hf']; exact Int.le_refl _
        · exact Int.le_trans (ih hr f hf') hle
      · rename_i hgt
        cases h
        rcases List.mem_cons.mp hf with hf' | hf'
        · rw [hf']; omega
        · exact ih hr f hf'

/-! ### Round soundness -/

/-- Bumping moves counters only: the backend row is untouched. -/
theorem bump_ids (s : List SwrrEntry) :
    (bump s).map Prod.fst = s.map Prod.fst := by
  induction s with
  | nil => rfl
  | cons e rest ih => simp only [bump, List.map_cons] at ih ⊢; rw [ih]

/-- Deducting moves counters only: the backend row is untouched. -/
theorem deduct_ids (bid : Nat) (d : Int) (s : List SwrrEntry) :
    (deduct bid d s).map Prod.fst = s.map Prod.fst := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    simp only [deduct, List.map_cons] at ih ⊢
    rw [ih]
    by_cases h : e.1.id = bid <;> simp [h]

/-- A round's verdict is drawn from the pool. -/
theorem swrrStep_mem {s : List SwrrEntry} {b : Backend}
    (h : (swrrStep s).1 = some b) : b ∈ s.map Prod.fst := by
  unfold swrrStep at h
  cases hp : pickMax (bump s) with
  | none => rw [hp] at h; cases h
  | some e =>
    rw [hp] at h
    cases h
    have hmem : e.1 ∈ (bump s).map Prod.fst :=
      List.mem_map_of_mem Prod.fst (pickMax_mem hp)
    rwa [bump_ids] at hmem

/-- A round over a nonempty pool always selects. -/
theorem swrrStep_total {s : List SwrrEntry} (h : s ≠ []) :
    ((swrrStep s).1).isSome := by
  have hbne : bump s ≠ [] := by
    intro hb
    apply h
    cases s with
    | nil => rfl
    | cons e rest => simp [bump] at hb
  unfold swrrStep
  cases hp : pickMax (bump s) with
  | none =>
    have := pickMax_total hbne
    rw [hp] at this
    cases this
  | some e => simp [hp]

/-- **Argmax conformance.** The backend a round emits attained the maximal
post-bump counter — steps 1–2 of the algorithm, as one statement. -/
theorem swrrStep_argmax {s : List SwrrEntry} {b : Backend}
    (h : (swrrStep s).1 = some b) :
    ∃ c : Int, (b, c) ∈ bump s ∧ ∀ f ∈ bump s, f.2 ≤ c := by
  unfold swrrStep at h
  cases hp : pickMax (bump s) with
  | none => rw [hp] at h; cases h
  | some e =>
    rw [hp] at h
    cases h
    exact ⟨e.2, pickMax_mem hp, pickMax_max hp⟩

/-! ### The balance invariant -/

/-- Summed counters. -/
def sumCw : List SwrrEntry → Int
  | [] => 0
  | e :: es => e.2 + sumCw es

@[simp] theorem sumCw_nil : sumCw [] = 0 := rfl

@[simp] theorem sumCw_cons (e : SwrrEntry) (s : List SwrrEntry) :
    sumCw (e :: s) = e.2 + sumCw s := rfl

/-- Step 1 adds exactly the total weight to the summed counter. -/
theorem sumCw_bump (s : List SwrrEntry) :
    sumCw (bump s) = sumCw s + totalWeightZ s := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    simp only [bump, List.map_cons, sumCw_cons, totalWeightZ,
      totalWeight_cons] at ih ⊢
    omega

/-- The entry identities of a state. -/
def entIds (s : List SwrrEntry) : List Nat :=
  s.map (fun e => e.1.id)

/-- Deducting an absent identity is the identity. -/
theorem deduct_absent {bid : Nat} {d : Int} {s : List SwrrEntry}
    (h : bid ∉ entIds s) : deduct bid d s = s := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    have hne : e.1.id ≠ bid := by
      intro heq
      exact h (by simp [entIds, heq])
    have hrest : bid ∉ entIds rest := by
      intro hmem
      apply h
      simp only [entIds, List.map_cons, List.mem_cons]
      exact Or.inr hmem
    simp only [deduct, List.map_cons, if_neg hne]
    rw [show rest.map (fun e => if e.1.id = bid then (e.1, e.2 - d) else e)
        = rest from ih hrest]

/-- Step 3 removes exactly `d` from the summed counter, provided the debited
identity occurs once (the `idsNodup` config invariant, in entry form). -/
theorem sumCw_deduct {bid : Nat} {d : Int} {s : List SwrrEntry}
    (hnd : (entIds s).Nodup) (hmem : bid ∈ entIds s) :
    sumCw (deduct bid d s) = sumCw s - d := by
  induction s with
  | nil => cases hmem
  | cons e rest ih =>
    have hnd' : e.1.id ∉ entIds rest ∧ (entIds rest).Nodup := by
      simpa [entIds] using hnd
    by_cases he : e.1.id = bid
    · have habs : bid ∉ entIds rest := he ▸ hnd'.1
      simp only [deduct, List.map_cons, if_pos he, sumCw_cons]
      rw [show rest.map (fun e => if e.1.id = bid then (e.1, e.2 - d) else e)
          = rest from deduct_absent habs]
      omega
    · have hmem' : bid ∈ entIds rest := by
        have : bid = e.1.id ∨ bid ∈ entIds rest := by
          simpa [entIds] using hmem
        rcases this with h | h
        · exact absurd h.symm he
        · exact h
      simp only [deduct, List.map_cons, if_neg he, sumCw_cons]
      have htail := ih hnd'.2 hmem'
      rw [show rest.map (fun e => if e.1.id = bid then (e.1, e.2 - d) else e)
          = deduct bid d rest from rfl, htail]
      omega

/-- Identities are stable across bump. -/
theorem entIds_bump (s : List SwrrEntry) : entIds (bump s) = entIds s := by
  induction s with
  | nil => rfl
  | cons e rest ih => simp only [entIds, bump, List.map_cons] at ih ⊢; rw [ih]

/-- Identities are stable across deduct. -/
theorem entIds_deduct (bid : Nat) (d : Int) (s : List SwrrEntry) :
    entIds (deduct bid d s) = entIds s := by
  induction s with
  | nil => rfl
  | cons e rest ih =>
    simp only [entIds, deduct, List.map_cons] at ih ⊢
    rw [ih]
    by_cases h : e.1.id = bid <;> simp [h]

/-- Identities are stable across a round: smooth WRR moves counters only. -/
theorem swrrStep_entIds (s : List SwrrEntry) :
    entIds (swrrStep s).2 = entIds s := by
  unfold swrrStep
  cases hp : pickMax (bump s) with
  | none => simp [entIds_bump]
  | some e => simp [entIds_deduct, entIds_bump]

/-- **The balance invariant, one round.** With distinct identities and a
nonempty pool, a round conserves the summed counter: step 1's total-weight
credit is exactly repaid by step 3's debit on the winner. -/
theorem swrrStep_sum {s : List SwrrEntry} (hnd : (entIds s).Nodup)
    (hne : s ≠ []) : sumCw (swrrStep s).2 = sumCw s := by
  have hbne : bump s ≠ [] := by
    intro hb
    apply hne
    cases s with
    | nil => rfl
    | cons e rest => simp [bump] at hb
  unfold swrrStep
  cases hp : pickMax (bump s) with
  | none =>
    have := pickMax_total hbne
    rw [hp] at this
    cases this
  | some e =>
    have hnd_b : (entIds (bump s)).Nodup := by rw [entIds_bump]; exact hnd
    have hmem : e.1.id ∈ entIds (bump s) :=
      List.mem_map_of_mem (fun e => e.1.id) (pickMax_mem hp)
    simp only
    rw [sumCw_deduct hnd_b hmem, sumCw_bump]
    omega

/-- **The balance invariant, any horizon.** From the all-zero start the summed
counter is 0 after every number of rounds: the schedule's selection debt
neither accumulates nor leaks, ever. -/
theorem swrrRun_sum_zero {bs : List Backend} (hnd : idsNodup bs)
    (hne : bs ≠ []) (n : Nat) :
    sumCw (swrrRun n (swrrInit bs)).2 = 0 := by
  have hinit_sum : sumCw (swrrInit bs) = 0 := by
    clear hnd hne
    induction bs with
    | nil => rfl
    | cons b rest ih => simp only [swrrInit, List.map_cons, sumCw_cons] at ih ⊢; omega
  have hinit_ids : entIds (swrrInit bs) = bs.map Backend.id := by
    clear hnd hne hinit_sum
    induction bs with
    | nil => rfl
    | cons b rest ih =>
      simp only [swrrInit, entIds, List.map_cons] at ih ⊢; rw [ih]
  have hinit_ne : swrrInit bs ≠ [] := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b rest => simp [swrrInit]
  -- generalize: any state with zero sum, nodup ids, nonempty stays at zero
  suffices h : ∀ (n : Nat) (s : List SwrrEntry), (entIds s).Nodup → s ≠ [] →
      sumCw s = 0 → sumCw (swrrRun n s).2 = 0 by
    exact h n (swrrInit bs) (by rw [hinit_ids]; exact hnd) hinit_ne hinit_sum
  intro n
  induction n with
  | zero => intro s _ _ hsum; exact hsum
  | succ n ih =>
    intro s hnd' hne' hsum
    show sumCw (swrrRun n (swrrStep s).2).2 = 0
    have hne'' : (swrrStep s).2 ≠ [] := by
      intro hnil
      have := swrrStep_entIds s
      rw [hnil] at this
      cases s with
      | nil => exact absurd rfl hne'
      | cons e rest => simp [entIds] at this
    exact ih (swrrStep s).2
      (by rw [swrrStep_entIds]; exact hnd')
      hne''
      (by rw [swrrStep_sum hnd' hne']; exact hsum)

end Proxy
