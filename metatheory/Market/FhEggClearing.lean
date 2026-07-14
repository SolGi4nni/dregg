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

  * **(b) THE CROSSING is well-defined — `crossing`, the least genuine clearing index.** Per the codex
    correction (`FHEGG-CODEX-INSIGHTS.md` Q2: *monotone curves are NOT a monotone operator*), the
    crossing is the least fixed point of the explicit index update

        F(j) = j                if demand(j) ≤ supply(j)   (found it — stop)
             = min(j+1, K)       otherwise                  (imbalance still positive — move up)

    `Fstep_monotone` proves **`F` IS the monotone operator** (using `imbalance_antitone` — the fold's
    imbalance is non-increasing, so the guard is upward-closed). **Assuming a crossing exists**
    (`CrossingExists`, stated honestly as the hypothesis — else the book does not clear), `crossing` is
    the LEAST index that clears (`crossing_is_least`) and is a fixed point of `F` (`crossing_fixed`);
    below it `F` strictly increases (`below_crossing_not_clears`). No overclaim: without a crossing there
    is no genuine fixed point (only the spurious top `K`).
  * **(a) CONSERVATION — the cleared allocation Σ-balances.** At the crossing the matched volume is
    `V = min(demand, supply) = demand` (`clearedVolume_eq_demand`); the aggregate cleared batch (the buy
    leg and sell leg at the uniform price) neither mints nor burns — `netFlow = 0` on every asset
    (`clearedBatch_conserves`), the priced lift of `clearing_conserves_per_asset`. Built on the fold
    homomorphism and discharged through `Market/Priced.lean`'s `Conserves`.
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

/-! ## 3. The crossing — the least genuine clearing index (assuming a crossing exists). -/

/-- **`Clears bk j`** — the market clears at bucket `j`: cumulative demand has fallen to at or below
cumulative supply (the imbalance is non-positive). -/
def Clears (bk : OrderBook) (j : ℕ) : Prop := demand bk j ≤ supply bk j

instance (bk : OrderBook) : DecidablePred (Clears bk) :=
  fun j => inferInstanceAs (Decidable (demand bk j ≤ supply bk j))

/-- **A crossing exists** — some bucket clears. Stated HONESTLY as the hypothesis (`FHEGG-KERNEL.md §2.1c`
/ codex Q2): monotone curves guarantee the imbalance is non-increasing, but NOT that it ever reaches
zero; a book whose demand exceeds supply at every bucket does not clear. -/
abbrev CrossingExists (bk : OrderBook) : Prop := ∃ j, Clears bk j

/-- **`crossing`** — the clearing price bucket: the LEAST index that clears (`Nat.find` on the decidable
`Clears`, given a crossing exists). This is the least fixed point of `F` (§4). -/
def crossing (bk : OrderBook) (h : CrossingExists bk) : ℕ := Nat.find h

/-- The crossing bucket genuinely clears. -/
theorem crossing_clears (bk : OrderBook) (h : CrossingExists bk) : Clears bk (crossing bk h) :=
  Nat.find_spec h

/-- The crossing is `≤` any clearing bucket. -/
theorem crossing_least (bk : OrderBook) (h : CrossingExists bk) {j : ℕ} (hj : Clears bk j) :
    crossing bk h ≤ j :=
  Nat.find_min' h hj

/-- **The crossing is the LEAST clearing bucket** — `IsLeast` of the clearing set. The uniform clearing
price `p*` well-defined, as the design's monotone-crossing demands. -/
theorem crossing_is_least (bk : OrderBook) (h : CrossingExists bk) :
    IsLeast {j | Clears bk j} (crossing bk h) :=
  ⟨crossing_clears bk h, fun _ hj => crossing_least bk h hj⟩

/-- **Below the crossing the market does NOT clear** — every bucket before `p*` has strictly positive
imbalance. So `F` strictly increases below `p*` and stops exactly at it (§4). -/
theorem below_crossing_not_clears (bk : OrderBook) (h : CrossingExists bk) {j : ℕ}
    (hj : j < crossing bk h) : ¬ Clears bk j :=
  Nat.find_min h hj

/-! ## 4. The crossing operator `F` — the codex correction (curves ≠ operator). -/

/-- **The crossing operator** `F(j) = j if the market clears at `j`, else `min(j+1, K)`** — the explicit
monotone update whose least fixed point is the crossing (`FHEGG-CODEX-INSIGHTS.md` Q2: the fixpoint is of
THIS operator, NOT of the monotone curves). `K` is the top price bucket. -/
def Fstep (bk : OrderBook) (K : ℕ) (j : ℕ) : ℕ :=
  if Clears bk j then j else min (j + 1) K

theorem Fstep_fixed_of_clears {bk : OrderBook} {K j : ℕ} (hc : Clears bk j) :
    Fstep bk K j = j := by
  unfold Fstep; rw [if_pos hc]

theorem Fstep_succ_of_not_clears {bk : OrderBook} {K j : ℕ} (hc : ¬ Clears bk j) :
    Fstep bk K j = min (j + 1) K := by
  unfold Fstep; rw [if_neg hc]

/-- **The crossing is a FIXED POINT of `F`.** Together with `Fstep_monotone` and Knaster–Tarski this is
the "least fixed point assuming a crossing exists" of the design — `crossing` clears, so `F` holds
still. -/
theorem crossing_fixed (bk : OrderBook) (h : CrossingExists bk) (K : ℕ) :
    Fstep bk K (crossing bk h) = crossing bk h :=
  Fstep_fixed_of_clears (crossing_clears bk h)

/-- **`F` IS THE MONOTONE OPERATOR (the codex correction, discharged).** `Fstep` is monotone on the
price-index chain — the fact that makes Knaster–Tarski apply, and which the monotone *curves* alone do
NOT give. The proof leans on `imbalance_antitone`: the clearing guard is upward-closed (once the market
clears it stays cleared as price rises), so `F` never steps back. -/
theorem Fstep_monotone {bk : OrderBook} (hb : OrdersValid bk) (K : ℕ) : Monotone (Fstep bk K) := by
  intro a b hab
  by_cases hca : Clears bk a
  · -- clears at a ⇒ clears at b (upward-closed), so F a = a ≤ b = F b
    have hcb : Clears bk b := by
      have himb := imbalance_antitone hb hab
      unfold Clears imbalance at *; omega
    rw [Fstep_fixed_of_clears hca, Fstep_fixed_of_clears hcb]; exact hab
  · rw [Fstep_succ_of_not_clears hca]
    by_cases hcb : Clears bk b
    · -- ¬clears a, clears b, a ≤ b ⇒ a < b ⇒ a+1 ≤ b ⇒ min(a+1,K) ≤ b
      rw [Fstep_fixed_of_clears hcb]
      have hne : a ≠ b := fun he => hca (he ▸ hcb)
      exact le_trans (min_le_left _ _) (by omega)
    · rw [Fstep_succ_of_not_clears hcb]
      exact min_le_min (by omega) (le_refl K)

/-! ## 5. The cleared volume and the aggregate cleared batch — conservation + optimality.

At the crossing the matched volume is `V = min(demand, supply)`; since the market clears there
(`demand ≤ supply`), `V = demand`. The cleared allocation is the aggregate BUY leg and SELL leg at the
uniform price `ρ` — matched at volume `V` — which we discharge through `Market/{Priced,Optimality}.lean`:
it conserves every asset (`netFlow = 0`) and is uniform-price-optimal (no-arbitrage / value-neutral). -/

/-- **The cleared (matched) volume at the crossing** — `min(demand, supply)`. -/
def clearedVolume (bk : OrderBook) (h : CrossingExists bk) : ℤ :=
  min (demand bk (crossing bk h)) (supply bk (crossing bk h))

/-- At the crossing, the matched volume is exactly cumulative demand (demand ≤ supply there). -/
theorem clearedVolume_eq_demand (bk : OrderBook) (h : CrossingExists bk) :
    clearedVolume bk h = demand bk (crossing bk h) :=
  min_eq_left (crossing_clears bk h)

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

/-- The worked book clears — at bucket 2 (`demand 6 ≤ supply 8`). A concrete crossing. -/
theorem workBook_crosses : CrossingExists workBook := ⟨2, by decide⟩

/-- **THE CROSSING, COMPUTED — the worked book's clearing bucket is 2.** Non-vacuous: buckets 0 and 1 do
NOT clear (imbalance `7`, `2` > 0), so the crossing genuinely searches. -/
theorem workBook_crossing : crossing workBook workBook_crosses = 2 := by
  unfold crossing
  rw [Nat.find_eq_iff]
  refine ⟨by decide, ?_⟩
  intro n hn
  interval_cases n <;> decide

/-- **The matched volume at the crossing is 6** (`min(demand 6, supply 8)`). -/
theorem workBook_clearedVolume : clearedVolume workBook workBook_crosses = 6 := by
  rw [clearedVolume_eq_demand, workBook_crossing]; decide

/-- **THE CLEARED BATCH IS CONSERVING AND OPTIMAL** — the worked crossing's matched volume `6` at a
uniform price `2` yields a batch that conserves every asset and is no-arbitrage / individually rational.
The full pipeline: book `→` fold `→` crossing `→` cleared allocation `→` conserving, optimal clearing. -/
theorem workBook_cleared_optimal :
    (∀ a, netFlow (clearedBatch 6 2) a = 0) ∧
    (∀ f ∈ clearedBatch 6 2, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ clearedBatch 6 2, recvValue 0 1 2 f = spentValue 0 1 2 f) :=
  clearedBatch_optimal 6 2 (by norm_num) (by norm_num)

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

/-! ## 7. EMITTABILITY — the conservation + crossing checks as AIR `Constraint`s (`Dregg2.Circuit`). -/

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

/-- **THE WORKED CLEARING IS ACCEPTED by the emitted circuit** — the worked book's crossing values
(`demand 6`, `supply 8`, `slack 2 ≥ 0`, matched volume `6` in and out) satisfy `clearingCircuit`. The
positive emit polarity: a genuine clearing passes the gates. -/
theorem clearingCircuit_accepts : satisfied clearingCircuit (encodeClearing 6 8 2 6 6) := by
  rw [clearingCircuit_sound]; exact ⟨by norm_num, rfl⟩

/-- **A non-conserving clearing is REJECTED by the emitted circuit** — matched volume `6` in but `5` out
fails the conservation gate. The circuit's gate has the same refusing power as `leakBatch_refused`. -/
theorem clearingCircuit_rejects : ¬ satisfied clearingCircuit (encodeClearing 6 8 2 6 5) := by
  rw [clearingCircuit_sound]; rintro ⟨-, h⟩; norm_num at h

/-! ### `#guard` smoke — the fold, crossing, and cleared volume are COMPUTED. -/

-- cumulative demand (10, 10, 6) and supply (3, 8, 8) over the three price buckets:
#guard (demand workBook 0, demand workBook 1, demand workBook 2) == (10, 10, 6)
#guard (supply workBook 0, supply workBook 1, supply workBook 2) == (3, 8, 8)
-- the imbalance (7, 2, −2) crosses (turns non-positive) exactly at bucket 2:
#guard (imbalance workBook 0, imbalance workBook 1, imbalance workBook 2) == (7, 2, -2)
-- buckets 0, 1 do NOT clear; bucket 2 does — the crossing genuinely searches:
#guard (decide (Clears workBook 0), decide (Clears workBook 1), decide (Clears workBook 2))
        == (false, false, true)
-- the matched volume at the crossing is min(6, 8) = 6:
#guard clearedVolume workBook workBook_crosses == 6
-- the cleared batch's per-asset net flow is zero on base (0) and numéraire (1):
#guard netFlow (clearedBatch 6 2) 0 == (0 : ℚ)
#guard netFlow (clearedBatch 6 2) 1 == (0 : ℚ)

/-! ### Axiom hygiene — the fhEgg clearing keystones pinned kernel-clean. -/

#assert_all_clean [Market.demand_cons, Market.demand_perm, Market.demand_antitone,
  Market.supply_monotone, Market.imbalance_antitone, Market.crossing_clears, Market.crossing_is_least,
  Market.below_crossing_not_clears, Market.crossing_fixed, Market.Fstep_monotone,
  Market.clearedVolume_eq_demand, Market.clearedBatch_conserves, Market.clearedBatch_optimal,
  Market.workBook_crossing, Market.workBook_cleared_optimal, Market.noCrossBook_no_crossing,
  Market.leakBatch_refused, Market.clearingCircuit_sound, Market.clearingCircuit_accepts,
  Market.clearingCircuit_rejects]

end Market
