/-
# Market.FhEggClearing — the fhEgg uniform-price aggregation-clearing core (T = 1).

**The base case of the private convex engine.** `docs/deos/FHEGG-KERNEL.md` states the fhEgg kernel:
*a clearing is the fold of order-increments into an aggregate curve, crossed once.* This module
formalizes exactly that — the histogram fold `→` monotone crossing `→` cleared allocation — and proves
its three soundness faces, composing with the already-proved algebra (`Market/Clearing.lean`'s fold
homomorphism, `Market/Aggregation.lean`'s order-independence, `Market/{Priced,Optimality}.lean`'s priced
conservation + uniform-price optimality). `PRIVATE-CONVEX-ENGINE.md` calls this the `T = 1` degenerate
case of the T-step engine (the crossing is the prox at `T = 1`; the certificate is Σ-balance).

## The object — a price-indexed aggregate, folded from order-increments

A limit order is one **curve increment**: a bid `(qty q, limit ℓ)` adds `q` to cumulative demand at
every bucket `p ≤ ℓ` (you trade at any price at or below your limit); an ask adds `q` to cumulative
supply at every bucket `p ≥ ℓ`. `demand`/`supply` are the commutative-monoid **folds** of these
increments — order-independent (CRDT, `demand_perm`), homomorphic (`demand_cons`), and monotone in the
price index (`demand_antitone`/`supply_monotone`).

## What is proved (honest scope)

  * **(b) THE CLEARING PRICE MAXIMIZES EXECUTED VOLUME — `crossing`, the volume-argmax.** The executed
    volume at bucket `p` is `V(p) = min(demand p, supply p)` (`execVol`); the uniform clearing price is
    `p* = argmax_p V(p)` over the buckets `0..K-1`, ties broken to the LOWEST bucket (`crossing`). This is
    the textbook opening/closing-auction rule. `clearedVolume_optimal` proves the GENUINE optimality:
    `V(q) ≤ V*` for every bucket `q < K` — the clearing price maximizes matched volume. This is exactly
    the property the two old heuristics (Lean least-`{demand ≤ supply}`, Rust largest-`{demand ≥ supply}`)
    VIOLATED: they clear at a balance point that can sit strictly below the volume peak (witnessed on the
    worked book — the old least-crossing bucket 2 executes only `6 < 8`, `workBook_old_crossing_suboptimal`).
  * **(a) CONSERVATION — the cleared allocation Σ-balances.** At the clearing price the matched volume is
    `V* = min(demand p*, supply p*)` (`clearedVolume_eq` — the short side, NOT generally the demand); the
    aggregate cleared batch (the buy leg and sell leg at the uniform price) neither mints nor burns —
    `netFlow = 0` on every asset (`clearedBatch_conserves`), the priced lift of
    `clearing_conserves_per_asset`. Built on the fold homomorphism and discharged through
    `Market/Priced.lean`'s `Conserves`.
  * **(c) UNIFORM-PRICE OPTIMALITY — at the level `Optimality.lean` already proves.** The cleared batch
    `ClearsAtUniformPrice` and is therefore no-arbitrage / value-neutral and individually rational
    (`clearedBatch_optimal`, discharged through `uniform_price_optimal`). **Scope, stated plainly:** this
    is MODEL-LEVEL optimality (over the `Fill` substrate) — the same guarantee `Market/Optimality.lean`
    proves. LEDGER-REALIZATION (binding the histogram fold to the on-chain fills in-circuit) is the NAMED
    circuit step (`FHEGG-KERNEL.md §2.4`), NOT proved here.

## Emittability (§7)

The conservation and crossing checks are LINEAR circuit `Constraint`s (`Dregg2.Circuit`): the crossing
gate `supply(p*) = demand(p*) + slack` (`slack ≥ 0` is the range side — the crossing holds iff the
imbalance is non-positive) and the conservation gate `baseOut = baseIn`. Demonstrated on the worked book:
`satisfied` of the emitted system ↔ the semantic check.

Pure.
-/
import Market.Priced
import Market.Optimality
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.IntervalCases
import Dregg2.Circuit
import Dregg2.Tactics

namespace Market

open Dregg2.Exec (AssetId)
open List

/-! ## 1. Orders, the book, and the histogram fold. -/

/-- A market side — a `bid` buys the base asset, an `ask` sells it. -/
inductive Side | bid | ask
  deriving DecidableEq, Repr

/-- **A limit order** — one curve increment: a `qty` at a `limit` price bucket. A bid trades at any
bucket `≤ limit`; an ask at any bucket `≥ limit`. -/
structure LimitOrder where
  /-- Buy (`bid`) or sell (`ask`) the base asset. -/
  side  : Side
  /-- The order quantity (nonnegative in a valid book). -/
  qty   : ℤ
  /-- The limit price bucket index. -/
  limit : ℕ
  deriving DecidableEq, Repr

/-- **A book** — the standing limit orders the batch clears together. -/
abbrev OrderBook := List LimitOrder

/-- **A valid book** — every order has nonnegative quantity (a real order puts value on the table).
(Named `OrdersValid` to avoid clashing with `Market/Priced.lean`'s `BookValid` for `Fill` books.) -/
def OrdersValid (bk : OrderBook) : Prop := ∀ o ∈ bk, 0 ≤ o.qty

/-- The demand increment of one order at price bucket `p`: a bid contributes its `qty` to every bucket
at or below its limit; everything else contributes `0`. -/
def demandIncr (o : LimitOrder) (p : ℕ) : ℤ :=
  if o.side = Side.bid ∧ p ≤ o.limit then o.qty else 0

/-- The supply increment of one order at price bucket `p`: an ask contributes its `qty` to every bucket
at or above its limit. -/
def supplyIncr (o : LimitOrder) (p : ℕ) : ℤ :=
  if o.side = Side.ask ∧ o.limit ≤ p then o.qty else 0

/-- **Cumulative demand at bucket `p`** — the commutative-monoid FOLD of the bids' increments (the
aggregate curve; there is no per-order object). -/
def demand (bk : OrderBook) (p : ℕ) : ℤ := (bk.map (fun o => demandIncr o p)).sum

/-- **Cumulative supply at bucket `p`** — the fold of the asks' increments. -/
def supply (bk : OrderBook) (p : ℕ) : ℤ := (bk.map (fun o => supplyIncr o p)).sum

@[simp] theorem demand_nil (p : ℕ) : demand [] p = 0 := rfl
@[simp] theorem supply_nil (p : ℕ) : supply [] p = 0 := rfl

/-- **The fold homomorphism (demand)** — `demand` distributes over `cons`: the additive `toBal_mul`
analog of `Market/Clearing.lean`, at the histogram grain. -/
@[simp] theorem demand_cons (o : LimitOrder) (bk : OrderBook) (p : ℕ) :
    demand (o :: bk) p = demandIncr o p + demand bk p := by
  simp [demand]

/-- **The fold homomorphism (supply).** -/
@[simp] theorem supply_cons (o : LimitOrder) (bk : OrderBook) (p : ℕ) :
    supply (o :: bk) p = supplyIncr o p + supply bk p := by
  simp [supply]

/-- **Order-independence (CRDT / `pool_as_perm` analog)** — reordering the book leaves `demand`
unchanged: the fold is commutative, so arrival order is irrelevant (coordination-lite aggregation). -/
theorem demand_perm {bk bk' : OrderBook} (h : bk ~ bk') (p : ℕ) : demand bk p = demand bk' p :=
  (h.map _).sum_eq

/-- **Order-independence (supply).** -/
theorem supply_perm {bk bk' : OrderBook} (h : bk ~ bk') (p : ℕ) : supply bk p = supply bk' p :=
  (h.map _).sum_eq

/-! ## 2. Monotonicity of the aggregate curves (the crossing's precondition). -/

/-- A bid's demand increment is NON-INCREASING in the price bucket (given nonnegative qty): once the
price rises past the limit, the bid drops out. -/
theorem demandIncr_antitone {o : LimitOrder} (hq : 0 ≤ o.qty) {p p' : ℕ} (h : p ≤ p') :
    demandIncr o p' ≤ demandIncr o p := by
  by_cases hp' : o.side = Side.bid ∧ p' ≤ o.limit
  · have hp : o.side = Side.bid ∧ p ≤ o.limit := ⟨hp'.1, le_trans h hp'.2⟩
    simp [demandIncr, hp', hp]
  · simp only [demandIncr, if_neg hp']
    split_ifs
    · exact hq
    · exact le_refl _

/-- An ask's supply increment is NON-DECREASING in the price bucket. -/
theorem supplyIncr_monotone {o : LimitOrder} (hq : 0 ≤ o.qty) {p p' : ℕ} (h : p ≤ p') :
    supplyIncr o p ≤ supplyIncr o p' := by
  by_cases hp : o.side = Side.ask ∧ o.limit ≤ p
  · have hp' : o.side = Side.ask ∧ o.limit ≤ p' := ⟨hp.1, le_trans hp.2 h⟩
    simp [supplyIncr, hp, hp']
  · simp only [supplyIncr, if_neg hp]
    split_ifs
    · exact hq
    · exact le_refl _

/-- **Cumulative demand is NON-INCREASING in price** — the fold of non-increasing increments. -/
theorem demand_antitone {bk : OrderBook} (hb : OrdersValid bk) {p p' : ℕ} (h : p ≤ p') :
    demand bk p' ≤ demand bk p := by
  induction bk with
  | nil => simp
  | cons o os ih =>
    simp only [demand_cons]
    exact add_le_add (demandIncr_antitone (hb o (by simp)) h)
      (ih (fun x hx => hb x (by simp [hx])))

/-- **Cumulative supply is NON-DECREASING in price.** -/
theorem supply_monotone {bk : OrderBook} (hb : OrdersValid bk) {p p' : ℕ} (h : p ≤ p') :
    supply bk p ≤ supply bk p' := by
  induction bk with
  | nil => simp
  | cons o os ih =>
    simp only [supply_cons]
    exact add_le_add (supplyIncr_monotone (hb o (by simp)) h)
      (ih (fun x hx => hb x (by simp [hx])))

/-- **The imbalance `demand − supply` is NON-INCREASING in price** — demand falls, supply rises, so the
excess demand is monotone. This is what makes the crossing operator `F` monotone (§4). -/
def imbalance (bk : OrderBook) (p : ℕ) : ℤ := demand bk p - supply bk p

theorem imbalance_antitone {bk : OrderBook} (hb : OrdersValid bk) {p p' : ℕ} (h : p ≤ p') :
    imbalance bk p' ≤ imbalance bk p := by
  have hd := demand_antitone hb h
  have hs := supply_monotone hb h
  unfold imbalance; omega

/-! ## 3. The balance predicate `Clears` (demand ≤ supply) — an auxiliary notion (NOT the clearing rule). -/

/-- **`Clears bk j`** — the market clears at bucket `j`: cumulative demand has fallen to at or below
cumulative supply (the imbalance is non-positive). -/
def Clears (bk : OrderBook) (j : ℕ) : Prop := demand bk j ≤ supply bk j

instance (bk : OrderBook) : DecidablePred (Clears bk) :=
  fun j => inferInstanceAs (Decidable (demand bk j ≤ supply bk j))

/-! ### The balance-threshold index (NOT the clearing price).

`balanceCrossing` is the LEAST balanced bucket (`Nat.find` on `Clears`). It is emphatically NOT the
clearing price — the clearing price is the volume-argmax `crossing` (§4). `balanceCrossing` is the
THRESHOLD of the monotone balance sign vector `[Clears bk j]` — the object the output-boundary MPC opens
(`Market/MpcClearingSecurity.lean`) and the fixed point of the monotone feedback operator `Fstep`
(`Market/ZKOpenRel.lean`). It is kept as a distinct, honestly-named auxiliary; it is what the OLD
least-`{demand ≤ supply}` heuristic mistook for the clearing price. -/

/-- **A crossing exists** — some bucket is balanced. The honest existence hypothesis for the
balance-threshold index: monotone curves make the imbalance non-increasing but do NOT force it to reach
zero (a book in permanent excess demand never balances). -/
abbrev CrossingExists (bk : OrderBook) : Prop := ∃ j, Clears bk j

/-- **`balanceCrossing`** — the LEAST balanced bucket (`Nat.find` on the decidable `Clears`, given one
exists). The threshold of the balance sign vector; NOT the clearing price (`crossing`, §4). -/
def balanceCrossing (bk : OrderBook) (h : CrossingExists bk) : ℕ := Nat.find h

/-- The balance-threshold bucket is genuinely balanced. -/
theorem balanceCrossing_clears (bk : OrderBook) (h : CrossingExists bk) :
    Clears bk (balanceCrossing bk h) := Nat.find_spec h

/-- The balance threshold is `≤` any balanced bucket. -/
theorem balanceCrossing_least (bk : OrderBook) (h : CrossingExists bk) {j : ℕ} (hj : Clears bk j) :
    balanceCrossing bk h ≤ j := Nat.find_min' h hj

/-- **The balance threshold is the LEAST balanced bucket** — `IsLeast` of the balanced set. -/
theorem balanceCrossing_is_least (bk : OrderBook) (h : CrossingExists bk) :
    IsLeast {j | Clears bk j} (balanceCrossing bk h) :=
  ⟨balanceCrossing_clears bk h, fun _ hj => balanceCrossing_least bk h hj⟩

/-- **Below the balance threshold the market is NOT balanced** — every bucket before it has strictly
positive imbalance. -/
theorem below_balanceCrossing_not_clears (bk : OrderBook) (h : CrossingExists bk) {j : ℕ}
    (hj : j < balanceCrossing bk h) : ¬ Clears bk j := Nat.find_min h hj

/-- **The balance-threshold operator** `F(j) = j if Clears j, else min(j+1, K)` — the explicit monotone
update whose least fixed point is `balanceCrossing`. The feedback map for `Market/ZKOpenRel.lean`'s
guarded trace. `K` is the top price bucket. -/
def Fstep (bk : OrderBook) (K : ℕ) (j : ℕ) : ℕ :=
  if Clears bk j then j else min (j + 1) K

theorem Fstep_fixed_of_clears {bk : OrderBook} {K j : ℕ} (hc : Clears bk j) :
    Fstep bk K j = j := by unfold Fstep; rw [if_pos hc]

theorem Fstep_succ_of_not_clears {bk : OrderBook} {K j : ℕ} (hc : ¬ Clears bk j) :
    Fstep bk K j = min (j + 1) K := by unfold Fstep; rw [if_neg hc]

/-- **The balance threshold is a FIXED POINT of `F`.** `balanceCrossing` is balanced, so `F` holds
still — the least fixed point of the monotone operator (Knaster–Tarski with `Fstep_monotone`). -/
theorem balanceCrossing_fixed (bk : OrderBook) (h : CrossingExists bk) (K : ℕ) :
    Fstep bk K (balanceCrossing bk h) = balanceCrossing bk h :=
  Fstep_fixed_of_clears (balanceCrossing_clears bk h)

/-- **`F` IS THE MONOTONE OPERATOR.** `Fstep` is monotone on the price-index chain (the fact that makes
Knaster–Tarski apply). The proof leans on `imbalance_antitone`: the balance guard is upward-closed (once
balanced it stays balanced as price rises), so `F` never steps back. -/
theorem Fstep_monotone {bk : OrderBook} (hb : OrdersValid bk) (K : ℕ) : Monotone (Fstep bk K) := by
  intro a b hab
  by_cases hca : Clears bk a
  · have hcb : Clears bk b := by
      have himb := imbalance_antitone hb hab
      unfold Clears imbalance at *; omega
    rw [Fstep_fixed_of_clears hca, Fstep_fixed_of_clears hcb]; exact hab
  · rw [Fstep_succ_of_not_clears hca]
    by_cases hcb : Clears bk b
    · rw [Fstep_fixed_of_clears hcb]
      have hne : a ≠ b := fun he => hca (he ▸ hcb)
      exact le_trans (min_le_left _ _) (by omega)
    · rw [Fstep_succ_of_not_clears hcb]
      exact min_le_min (by omega) (le_refl K)

/-- **The balance-threshold volume** — `min(demand, supply)` at `balanceCrossing`; since the book is
balanced there, this equals cumulative demand (`balanceVolume_eq_demand`). The MPC's revealed `V*`
(`Market/MpcClearingSecurity.lean`), NOT the (generally larger) volume-maximizing `clearedVolume`. -/
def balanceVolume (bk : OrderBook) (h : CrossingExists bk) : ℤ :=
  min (demand bk (balanceCrossing bk h)) (supply bk (balanceCrossing bk h))

theorem balanceVolume_eq_demand (bk : OrderBook) (h : CrossingExists bk) :
    balanceVolume bk h = demand bk (balanceCrossing bk h) :=
  min_eq_left (balanceCrossing_clears bk h)

/-! ## 4. The clearing price — the volume-maximizing bucket (the uniform-price auction rule). -/

/-- **The executed (matched) volume at bucket `p`** — the short side of the two curves,
`V(p) = min(demand p, supply p)`: a bid trades only against available supply, an ask only against
available demand. -/
def execVol (bk : OrderBook) (p : ℕ) : ℤ := min (demand bk p) (supply bk p)

/-- **The volume-argmax over buckets `0..n`** — the LOWEST bucket maximizing `execVol`. The strict `<` in
the guard keeps the incumbent (earlier) bucket on ties, realizing the lowest-`p` tie-break. -/
def argmaxUpto (bk : OrderBook) : ℕ → ℕ
  | 0     => 0
  | n + 1 => if execVol bk (argmaxUpto bk n) < execVol bk (n + 1) then n + 1 else argmaxUpto bk n

/-- The argmax bucket lies in range `0..n`. -/
theorem argmaxUpto_le (bk : OrderBook) : ∀ n, argmaxUpto bk n ≤ n
  | 0     => le_refl 0
  | n + 1 => by
      simp only [argmaxUpto]
      split
      · exact le_refl _
      · exact le_trans (argmaxUpto_le bk n) (Nat.le_succ n)

/-- **THE OPTIMALITY CORE — the argmax bucket MAXIMIZES executed volume over `0..n`.** Every bucket
`q ≤ n` executes no more than the argmax bucket: `execVol q ≤ execVol (argmaxUpto n)`. This is the genuine
volume-maximization the least-`{demand ≤ supply}` heuristic LACKED (it stops at the first balance point,
which can sit strictly below the volume peak). Proved by induction on the scan: each step keeps the
incumbent unless a strictly larger bucket appears. -/
theorem argmaxUpto_max (bk : OrderBook) :
    ∀ n q, q ≤ n → execVol bk q ≤ execVol bk (argmaxUpto bk n) := by
  intro n
  induction n with
  | zero =>
    intro q hq
    interval_cases q
    exact le_refl _
  | succ n ih =>
    intro q hq
    by_cases h : execVol bk (argmaxUpto bk n) < execVol bk (n + 1)
    · have hred : argmaxUpto bk (n + 1) = n + 1 := by simp only [argmaxUpto, if_pos h]
      rw [hred]
      rcases (by omega : q ≤ n ∨ q = n + 1) with hqn | hqn
      · exact le_trans (ih q hqn) (le_of_lt h)
      · subst hqn; exact le_refl _
    · have hred : argmaxUpto bk (n + 1) = argmaxUpto bk n := by simp only [argmaxUpto, if_neg h]
      rw [hred]
      rcases (by omega : q ≤ n ∨ q = n + 1) with hqn | hqn
      · exact ih q hqn
      · subst hqn; exact not_lt.mp h

/-- **`crossing`** — the uniform clearing price bucket over the `K` price buckets `0..K-1`: the LOWEST
bucket maximizing executed volume `V(p) = min(demand p, supply p)` (`argmax_p V(p)`, lowest-`p`
tie-break). The textbook opening/closing-auction rule — it maximizes matched volume (`clearedVolume_optimal`)
and is individually rational (a bid trades at `p ≤ limit`, an ask at `p ≥ limit`, by the increments'
construction). -/
def crossing (bk : OrderBook) (K : ℕ) : ℕ := argmaxUpto bk (K - 1)

/-- The clearing price is a genuine in-range bucket whenever the book has at least one price bucket. -/
theorem crossing_lt (bk : OrderBook) {K : ℕ} (hK : 0 < K) : crossing bk K < K := by
  have := argmaxUpto_le bk (K - 1)
  unfold crossing
  omega

/-! ## 5. The cleared volume and the aggregate cleared batch — optimality + conservation.

The cleared (executed) volume is `V* = min(demand p*, supply p*)` at the clearing price `p* = crossing`.
By `clearedVolume_optimal` this `V*` is the MAXIMUM executed volume over all buckets — genuine
volume-maximization. The cleared allocation is the aggregate BUY leg and SELL leg at the uniform price `ρ`,
matched at volume `V*`, discharged through `Market/{Priced,Optimality}.lean`: it conserves every asset
(`netFlow = 0`) and is uniform-price-optimal (no-arbitrage / value-neutral / individually rational). -/

/-- **The cleared (executed) volume at the clearing price** — `V* = min(demand p*, supply p*)`. -/
def clearedVolume (bk : OrderBook) (K : ℕ) : ℤ := execVol bk (crossing bk K)

/-- **The cleared-volume characterization** (the volume-argmax analogue of the balance-threshold's
`balanceVolume_eq_demand`: at the volume-argmax bucket the matched volume is the short side
`min(demand, supply)`, which is NOT generally the demand — the least-crossing `V = demand` identity is a
property of the balance threshold, not the clearing price). -/
theorem clearedVolume_eq (bk : OrderBook) (K : ℕ) :
    clearedVolume bk K = min (demand bk (crossing bk K)) (supply bk (crossing bk K)) := rfl

/-- **OPTIMALITY (c) — the clearing price MAXIMIZES executed volume.** For every bucket `q < K`, the
executed volume `min(demand q, supply q)` is at most the cleared volume `V*`. GENUINE, non-vacuous
optimality: `p*` maximizes the matched volume — precisely the property the two old heuristics (Lean
least-`{demand ≤ supply}`, Rust largest-`{demand ≥ supply}`) VIOLATE, mis-clearing when the volume peak
sits on their blind side. -/
theorem clearedVolume_optimal (bk : OrderBook) (K : ℕ) {q : ℕ} (hq : q < K) :
    min (demand bk q) (supply bk q) ≤ clearedVolume bk K := by
  unfold clearedVolume crossing
  exact argmaxUpto_max bk (K - 1) q (by omega)

/-- The aggregate BUY leg — base buyers collectively spend `V·ρ` numéraire (asset `1`) and receive `V`
of the base asset (asset `0`) at the uniform rate `ρ` (`execPrice = ρ⁻¹`, base per numéraire). -/
def buyLeg (V ρ : ℚ) : Fill :=
  { orderId := 0,
    order := { creator := 0, offerAsset := 1, wantAsset := 0, offerAmount := V * ρ, limitPrice := ρ⁻¹ },
    filledIn := V * ρ, execPrice := ρ⁻¹ }

/-- The aggregate SELL leg — base sellers offer `V` of the base asset (asset `0`) and receive `V·ρ`
numéraire (asset `1`) at the uniform rate `ρ` (`execPrice = ρ`, numéraire per base). -/
def sellLeg (V ρ : ℚ) : Fill :=
  { orderId := 1,
    order := { creator := 1, offerAsset := 0, wantAsset := 1, offerAmount := V, limitPrice := ρ },
    filledIn := V, execPrice := ρ }

/-- **The cleared batch** — the two aggregate legs at the uniform price. -/
def clearedBatch (V ρ : ℚ) : List Fill := [buyLeg V ρ, sellLeg V ρ]

/-- **CONSERVATION (a) — the cleared batch Σ-balances.** `netFlow = 0` on every asset: the base asset
(`0`) nets `V − V = 0` (buyers receive what sellers provide), the numéraire (`1`) nets `V·ρ − V·ρ = 0`,
every other asset is untouched. The priced lift of `clearing_conserves_per_asset`, over the aggregate
cleared allocation. Needs `ρ ≠ 0` (a real rate). -/
theorem clearedBatch_conserves (V ρ : ℚ) (hρ : ρ ≠ 0) : Conserves (clearedBatch V ρ) := by
  intro a
  by_cases h0 : a = 0
  · subst h0
    simp only [netFlow, clearedBatch, buyLeg, sellLeg, legDelta, Fill.filledOut, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    norm_num
    field_simp
    ring
  · by_cases h1 : a = 1
    · subst h1
      simp only [netFlow, clearedBatch, buyLeg, sellLeg, legDelta, Fill.filledOut, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      norm_num
    · refine netFlow_untouched _ a ?_
      intro f hf
      fin_cases hf
      · exact ⟨Ne.symm h1, Ne.symm h0⟩
      · exact ⟨Ne.symm h0, Ne.symm h1⟩

/-- The cleared batch is a valid priced book (both legs `FillValid`, neither order over-filled) — needs a
nonnegative volume and a positive rate. -/
theorem clearedBatch_valid (V ρ : ℚ) (hV : 0 ≤ V) (hρ : 0 < ρ) : BookValid (clearedBatch V ρ) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    fin_cases hf
    · exact ⟨mul_nonneg hV (le_of_lt hρ), le_of_lt (inv_pos.mpr hρ), le_refl _⟩
    · exact ⟨hV, le_of_lt hρ, le_refl _⟩
  · intro f hf
    fin_cases hf <;> simp [orderFilledIn, clearedBatch, buyLeg, sellLeg]

/-- The cleared batch clears at the uniform price `ρ` on the base/numéraire pair `(0, 1)`: the sell leg
(`0 → 1`) executes at `ρ`, the buy leg (`1 → 0`) at `ρ⁻¹`. -/
theorem clearedBatch_uniform (V ρ : ℚ) : ClearsAtUniformPrice (clearedBatch V ρ) 0 1 ρ := by
  intro f hf
  fin_cases hf <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp_all [buyLeg, sellLeg]

/-- Both legs trade on the base/numéraire pair `(0, 1)`. -/
theorem clearedBatch_onPair (V ρ : ℚ) : ∀ f ∈ clearedBatch V ρ, OnPair 0 1 f := by
  intro f hf
  fin_cases hf
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- **OPTIMALITY (c) — the cleared batch is uniform-price optimal, at the level `Optimality.lean` proves.**
Discharged through `uniform_price_optimal`: the cleared batch conserves per asset, respects every order's
declared limit (individually rational), and is no-arbitrage / value-neutral (every leg's numéraire value
received equals value spent). **Scope:** this is MODEL-LEVEL (over the `Fill` substrate) — the same
guarantee `Market/Optimality.lean` proves. Ledger-realization (binding this batch to the histogram fold
in-circuit) is the named circuit step, NOT proved here. -/
theorem clearedBatch_optimal (V ρ : ℚ) (hV : 0 ≤ V) (hρ : 0 < ρ) :
    (∀ a, netFlow (clearedBatch V ρ) a = 0) ∧
    (∀ f ∈ clearedBatch V ρ, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ clearedBatch V ρ, recvValue 0 1 ρ f = spentValue 0 1 ρ f) :=
  uniform_price_optimal (by decide) (ne_of_gt hρ) (clearedBatch_valid V ρ hV hρ)
    (clearedBatch_conserves V ρ (ne_of_gt hρ)) (clearedBatch_uniform V ρ) (clearedBatch_onPair V ρ)

/-! ## 6. NON-VACUITY — a worked book crosses cleanly (positive), a non-clearing book has no crossing
(negative), and a non-conserving batch is refused (negative). -/

/-- The worked book: two bids (`6 @ limit 2`, `4 @ limit 1`) and two asks (`3 @ limit 0`, `5 @ limit 1`).
Cumulative demand `(10, 10, 6)` and supply `(3, 8, 8)` cross at bucket **2** (imbalance `7, 2, −2`). -/
def workBook : OrderBook :=
  [ { side := Side.bid, qty := 6, limit := 2 },
    { side := Side.bid, qty := 4, limit := 1 },
    { side := Side.ask, qty := 3, limit := 0 },
    { side := Side.ask, qty := 5, limit := 1 } ]

theorem workBook_valid : OrdersValid workBook := by
  unfold OrdersValid workBook; decide

/-- The worked book has a balanced bucket — bucket 2 (`demand 6 ≤ supply 8`). -/
theorem workBook_crosses : CrossingExists workBook := ⟨2, by decide⟩

/-- **The BALANCE THRESHOLD of the worked book is bucket 2** (the least balanced bucket; buckets 0, 1 have
imbalance `7, 2 > 0`). This is what the OLD least-crossing heuristic returned — and what the MPC sign
vector's threshold is — NOT the clearing price (bucket 1, the volume argmax). -/
theorem workBook_balanceCrossing : balanceCrossing workBook workBook_crosses = 2 := by
  unfold balanceCrossing
  rw [Nat.find_eq_iff]
  refine ⟨by decide, ?_⟩
  intro n hn
  interval_cases n <;> decide

/-- The worked book's balance-threshold volume is 6 (`min(demand 2, supply 2) = min(6, 8)`). -/
theorem workBook_balanceVolume : balanceVolume workBook workBook_crosses = 6 := by
  rw [balanceVolume_eq_demand, workBook_balanceCrossing]; decide

/-- **THE CLEARING PRICE, COMPUTED — the worked book clears at bucket 1** (executed volume
`min(10, 8) = 8`, the argmax of `min = (3, 8, 6)`). Non-vacuous: the OLD least-`{demand ≤ supply}`
crossing was bucket 2 (volume only 6); the argmax genuinely moves to the volume peak at bucket 1. -/
theorem workBook_crossing : crossing workBook 3 = 1 := by decide

/-- **The matched volume at the clearing price is 8** (`min(demand 1, supply 1) = min(10, 8)`). -/
theorem workBook_clearedVolume : clearedVolume workBook 3 = 8 := by decide

/-- **THE CORRECTION, WITNESSED — the old least-crossing bucket 2 was SUBOPTIMAL.** Bucket 2 executes only
`min(6, 8) = 6`, strictly below the argmax's `8`: the least-`{demand ≤ supply}` heuristic mis-cleared,
leaving 2 units of matchable volume on the table. -/
theorem workBook_old_crossing_suboptimal :
    min (demand workBook 2) (supply workBook 2) < clearedVolume workBook 3 := by decide

/-- **THE CLEARING PRICE MAXIMIZES VOLUME on the worked book** — every bucket `q < 3` executes at most the
cleared volume `8`. The general `clearedVolume_optimal`, instantiated on the worked book. -/
theorem workBook_optimal {q : ℕ} (hq : q < 3) :
    min (demand workBook q) (supply workBook q) ≤ clearedVolume workBook 3 :=
  clearedVolume_optimal workBook 3 hq

/-- **THE CLEARED BATCH IS CONSERVING AND OPTIMAL** — the clearing's matched volume `8` at a uniform rate
`2` yields a batch that conserves every asset and is no-arbitrage / individually rational. The full
pipeline: book `→` fold `→` argmax clearing price `→` cleared allocation `→` conserving, optimal clearing. -/
theorem workBook_cleared_optimal :
    (∀ a, netFlow (clearedBatch 8 2) a = 0) ∧
    (∀ f ∈ clearedBatch 8 2, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ clearedBatch 8 2, recvValue 0 1 2 f = spentValue 0 1 2 f) :=
  clearedBatch_optimal 8 2 (by norm_num) (by norm_num)

/-- **THE COUNTER-WITNESS** `D = (10, 9)`, `S = (5, 20)` — two bids (`9 @ limit 1`, `1 @ limit 0`) and two
asks (`5 @ limit 0`, `15 @ limit 1`). Executed volume `min = (5, 9)` peaks at bucket 1, so the auction
clears at `(p* = 1, V* = 9)`; the argmax lands on the true volume peak. -/
def counterBook : OrderBook :=
  [ { side := Side.bid, qty := 9, limit := 1 },
    { side := Side.bid, qty := 1, limit := 0 },
    { side := Side.ask, qty := 5, limit := 0 },
    { side := Side.ask, qty := 15, limit := 1 } ]

theorem counterBook_valid : OrdersValid counterBook := by
  unfold OrdersValid counterBook; decide

/-- The counter-witness clears at bucket 1 (`crossing counterBook 2 = 1`). -/
theorem counterBook_crossing : crossing counterBook 2 = 1 := by decide

/-- The counter-witness's matched volume is `9` (`min(demand 1, supply 1) = min(9, 20)`). -/
theorem counterBook_clearedVolume : clearedVolume counterBook 2 = 9 := by decide

/-- A book that NEVER clears — demand strictly exceeds supply at every bucket (a lone bid, no asks). Its
imbalance is `6 > 0` everywhere, so `CrossingExists` fails: the market has no clearing price. -/
def noCrossBook : OrderBook := [ { side := Side.bid, qty := 6, limit := 100 } ]

/-- **TOOTH (crossing existence): a book with no crossing does NOT clear.** `noCrossBook`'s demand is `6`
at every bucket `≤ 100` and supply is `0`, so no bucket clears in `[0, 100]` — the honest content of the
crossing-existence hypothesis: without a crossing there is no clearing price (only the spurious top). -/
theorem noCrossBook_no_crossing : ∀ j ≤ 100, ¬ Clears noCrossBook j := by
  intro j hj hcl
  have hd : demand noCrossBook j = 6 := by
    simp [demand, noCrossBook, demandIncr, hj]
  have hs : supply noCrossBook j = 0 := by
    simp [supply, noCrossBook, supplyIncr]
  rw [Clears, hd, hs] at hcl
  norm_num at hcl

/-- A NON-CONSERVING "cleared batch" — the buy leg alone, spending numéraire with no seller returning the
base asset. Value leaks out of the pair. -/
def leakBatch : List Fill := [buyLeg 6 2]

/-- **TOOTH (conservation): a non-conserving batch is REFUSED.** `leakBatch` credits `6` base to buyers
with no sell leg debiting it — asset `0` nets `+6 ≠ 0`. Not `Conserves`: the market cannot mint the base
asset out of nothing. Mirrors `Market/Priced.lean`'s `pairLeak_refused`. -/
theorem leakBatch_refused : ¬ Conserves leakBatch := by
  intro hc
  have h0 := hc 0
  simp [netFlow, leakBatch, buyLeg, legDelta, Fill.filledOut] at h0

/-! ## 7. EMITTABILITY — the conservation + balance checks as AIR `Constraint`s (`Dregg2.Circuit`).

SCOPE (honest): these gates encode the per-bucket *balance* decomposition `supply = demand + slack` and
the *conservation* `vout = vin`. They are NOT yet a circuit for the volume-argmax *selection*
(`crossing`); emitting the argmax — a witness that no other bucket executes strictly more — is a separate
AIR obligation, not modeled here. The sample values below are a balanced witness, not the worked book's
argmax clearing (which is bucket 1, where `demand 10 > supply 8`). -/

open Dregg2.Circuit

/-- Lay the crossing + conservation witness out: wire 0 = `demand(p*)`, wire 1 = `supply(p*)`,
wire 2 = `slack = supply − demand ≥ 0` (the crossing's range side), wire 3 = matched volume in,
wire 4 = matched volume out. -/
def encodeClearing (dem sup slack vin vout : ℤ) : Assignment
  | 0 => dem | 1 => sup | 2 => slack | 3 => vin | 4 => vout
  | _ => 0

/-- **The crossing gate** `supply(p*) = demand(p*) + slack` — the market clears at `p*` iff the slack
(`= supply − demand`) is nonnegative (`slack ≥ 0` is the standard AIR range side, named). Plus the
**conservation gate** `vout = vin` — matched volume in equals matched volume out. Two linear gates. -/
def clearingCircuit : ConstraintSystem :=
  [ { lhs := .var 1, rhs := .add (.var 0) (.var 2) },   -- supply = demand + slack  (crossing)
    { lhs := .var 4, rhs := .var 3 } ]                  -- vout = vin               (conservation)

/-- **THE EMIT BRIDGE — the AIR system is `satisfied` ⇔ the crossing + conservation arithmetic holds.**
`satisfied clearingCircuit (encodeClearing …)` iff `supply = demand + slack` (the crossing decomposition)
AND `vout = vin` (conservation). Checking the circuit IS checking the clearing. -/
theorem clearingCircuit_sound (dem sup slack vin vout : ℤ) :
    satisfied clearingCircuit (encodeClearing dem sup slack vin vout)
      ↔ sup = dem + slack ∧ vout = vin := by
  simp only [satisfied, clearingCircuit, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, Constraint.holds, Expr.eval, encodeClearing]
  tauto

/-- **A BALANCED, CONSERVING WITNESS IS ACCEPTED by the emitted circuit** — a sample bucket with
`demand 6`, `supply 8`, `slack 2 ≥ 0`, matched volume `6` in and out satisfies `clearingCircuit`. The
positive emit polarity: a balanced, conserving bucket passes the gates. (This is a balance witness, not
the worked book's argmax clearing — see the §7 scope note.) -/
theorem clearingCircuit_accepts : satisfied clearingCircuit (encodeClearing 6 8 2 6 6) := by
  rw [clearingCircuit_sound]; exact ⟨by norm_num, rfl⟩

/-- **A non-conserving clearing is REJECTED by the emitted circuit** — matched volume `6` in but `5` out
fails the conservation gate. The circuit's gate has the same refusing power as `leakBatch_refused`. -/
theorem clearingCircuit_rejects : ¬ satisfied clearingCircuit (encodeClearing 6 8 2 6 5) := by
  rw [clearingCircuit_sound]; rintro ⟨-, h⟩; norm_num at h

/-! ### `#guard` smoke — the fold, the argmax clearing price, and cleared volume are COMPUTED. -/

-- cumulative demand (10, 10, 6) and supply (3, 8, 8) over the three price buckets:
#guard (demand workBook 0, demand workBook 1, demand workBook 2) == (10, 10, 6)
#guard (supply workBook 0, supply workBook 1, supply workBook 2) == (3, 8, 8)
-- the executed volume V(p) = min(demand, supply) = (3, 8, 6) — the argmax is bucket 1:
#guard (execVol workBook 0, execVol workBook 1, execVol workBook 2) == (3, 8, 6)
-- the imbalance (7, 2, −2) turns non-positive at bucket 2 (the OLD least-crossing) — NOT the argmax:
#guard (imbalance workBook 0, imbalance workBook 1, imbalance workBook 2) == (7, 2, -2)
-- demand ≤ supply only at bucket 2 — the least-crossing heuristic's (blind) clear:
#guard (decide (Clears workBook 0), decide (Clears workBook 1), decide (Clears workBook 2))
        == (false, false, true)
-- the clearing price is the volume-argmax bucket 1, matched volume min(10, 8) = 8:
#guard crossing workBook 3 == 1
#guard clearedVolume workBook 3 == 8
-- the counter-witness D=(10,9), S=(5,20) clears at (p*, V*) = (1, 9):
#guard (demand counterBook 0, demand counterBook 1) == (10, 9)
#guard (supply counterBook 0, supply counterBook 1) == (5, 20)
#guard (crossing counterBook 2, clearedVolume counterBook 2) == (1, 9)
-- the cleared batch's per-asset net flow is zero on base (0) and numéraire (1):
#guard netFlow (clearedBatch 8 2) 0 == (0 : ℚ)
#guard netFlow (clearedBatch 8 2) 1 == (0 : ℚ)

/-! ### Axiom hygiene — the fhEgg clearing keystones pinned kernel-clean. -/

#assert_all_clean [Market.demand_cons, Market.demand_perm, Market.demand_antitone,
  Market.supply_monotone, Market.imbalance_antitone, Market.balanceCrossing_is_least,
  Market.below_balanceCrossing_not_clears, Market.balanceCrossing_fixed, Market.Fstep_monotone,
  Market.balanceVolume_eq_demand, Market.workBook_balanceCrossing, Market.workBook_balanceVolume,
  Market.argmaxUpto_max, Market.crossing_lt,
  Market.clearedVolume_eq, Market.clearedVolume_optimal, Market.clearedBatch_conserves,
  Market.clearedBatch_optimal, Market.workBook_crossing, Market.workBook_clearedVolume,
  Market.workBook_old_crossing_suboptimal, Market.workBook_optimal, Market.workBook_cleared_optimal,
  Market.counterBook_crossing, Market.counterBook_clearedVolume, Market.noCrossBook_no_crossing,
  Market.leakBatch_refused, Market.clearingCircuit_sound, Market.clearingCircuit_accepts,
  Market.clearingCircuit_rejects]

end Market
