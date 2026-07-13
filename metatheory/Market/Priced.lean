/-
# Market.Priced — DrEX rung 5: PRICED · PARTIAL-FILL · MULTI-PAIR clearing (the substrate lift).

**The dependency-unblocker.** `docs/deos/DREX-DESIGN.md` §3-#3/§4/§5 states rung 5 plainly: the
proven conservation + fairness of rungs 1-2 (`Market/{Clearing,Fairness}.lean`) live over the
discrete two-asset exact `DemoRes` book — *no prices, no partial fills, all-or-nothing*. That is a
provably-fair *exact-swap demo*, not a real exchange. And it is a **hard dependency floor**: the
design's §5 dependency-inversion finding is that **rung 4 (uniform-price optimality) CANNOT be
STATED before rung 5 exists** — envy-freeness / one-price optimality are theorems *about prices and
partial allocations the module does not yet have*. This file builds that substrate.

The lift is genuinely NEAR (the tower's proven mode): the quantity columns already exist in
`Dregg2/Intent/Ring.lean`'s `MatchNode` (`offerAmount`/`wantMin`), and the settled leg amount is
already `≤` the offer (`Market/Fairness.lean`'s `clearing_respects_limits`). What was missing —
supplied here, ADDITIVELY (rungs 1-2 untouched, still green):

  * **PRICES.** A `PricedOrder` carries a `limitPrice : ℚ` (minimum `wantAsset` units received per
    `offerAsset` unit spent — a REAL rational rate, not a discrete bundle). A `Fill` clears at a
    stated `execPrice : ℚ`; the received amount is `filledIn · execPrice` (priced exchange, not the
    exact-swap `Converts`). Computable/decidable throughout (ℚ has `DecidableEq`/`DecidableLE`).
  * **PARTIAL FILLS.** A `Fill` carries `filledIn ≤` the order's `offerAmount`; the un-filled
    `remainder = offerAmount − filledIn` is TRACKED (`no_value_lost`: `filledIn + remainder =
    offerAmount`, nothing lost). An order may be filled by SEVERAL fills; the consistency law is
    `Σ fills of an order ≤ the order` (`orderFilledIn ≤ offerAmount`, the `BookValid` clause).
  * **MULTI-PAIR.** Orders/fills range over many `(offerAsset, wantAsset)` pairs. Conservation is a
    per-asset net-flow reading (`netFlow`), and it COMPOSES across pairs by additivity
    (`Conserves_append`) — the per-pair conservations sum to a global one — while a pair that does
    not touch an asset contributes `0` to it (`netFlow_untouched`, the `multi_domain_independent`
    shape: pairs do not leak into each other).

**Composition, not duplication.** This module lifts the *shape* of rungs 1-2:
`clearing_conserves_per_asset`'s Σ-in = Σ-out becomes `netFlow = 0` over ℚ; `clearing_respects_limits`'s
"debited ≤ offered, received ≥ min" becomes "`filledIn ≤ offerAmount`, `filledIn·limitPrice ≤
filledOut`" at the cleared price. And it CONNECTS BACK: `ofMatchNode` embeds a rung-1/2 `MatchNode`
as a `PricedOrder`, and `ofMatchNode_full_fill_meets_wantMin` proves a full fill at the limit price
recovers rung-1's `received = wantMin` exactly — the priced law degenerates to the exact-book law.

**Unblocks rung 4.** The predicate `ClearsAtUniformPrice` — one exchange rate for every leg of a
one-pair batch — is now WELL-FORMED (it references `execPrice`, which did not exist pre-rung-5), and
non-vacuously satisfied by the worked book (`posBook_uniform_price`). That is the substrate the
rung-4 keystone `uniform_price_optimal` (all legs clear at one price ⇒ no coalition strictly improves)
rests on; it could not be typed before this file. See §7.

NON-VACUITY both polarities (§5/§6): a concrete two-order priced book with a **partial** fill clears
and satisfies the keystone (`posBook_keystone`; the filled amounts + prices are `#guard`-pinned); and
the teeth — an over-fill (`Σ > offer`, `overfill_refused`), a below-limit price (`badPrice_refused`),
and a cross-pair value leak (`pairLeak_refused`) are REFUSED — mirroring rung-1/2's
`mint_refused`/`overdebit_refused`.

Pure.
-/
import Dregg2.Intent.Ring
import Dregg2.Tactics
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Market

open Dregg2.Exec (AssetId CellId)

/-! ## 1. Priced orders and fills — the ℚ substrate. -/

/-- **A priced limit order.** Generalizes rung-1/2's `MatchNode`: same `creator`/`offerAsset`/
`wantAsset` identity columns, but `offerAmount` and the limit are now REAL rationals — `limitPrice`
is the minimum `wantAsset` units the order accepts per unit of `offerAsset` spent (rung-1's `wantMin`
is the special case `limitPrice · offerAmount` at a full fill). -/
structure PricedOrder where
  /-- The intent creator's cell (`MatchNode.creator`). -/
  creator     : CellId
  /-- The asset this order OFFERS (`MatchNode.offerAsset`). -/
  offerAsset  : AssetId
  /-- The asset this order WANTS (`MatchNode.wantAsset`). -/
  wantAsset   : AssetId
  /-- How much of `offerAsset` is on the table (`MatchNode.offerAmount`, now `ℚ`). -/
  offerAmount : ℚ
  /-- Minimum `wantAsset` received per `offerAsset` spent — the order's rational LIMIT PRICE. -/
  limitPrice  : ℚ
  deriving Inhabited, DecidableEq

/-- **A (partial) fill of a priced order** — a fractional leg settlement. `filledIn` of the order's
`offerAsset` is spent at realized rate `execPrice`, yielding `filledOut = filledIn · execPrice` of
`wantAsset`. `orderId` names the order so several fills of ONE order can be summed
(`orderFilledIn`). -/
structure Fill where
  /-- The order this fill settles (index into the book — several fills may share it). -/
  orderId   : ℕ
  /-- The order's declared terms (carried for a self-contained limit check). -/
  order     : PricedOrder
  /-- Amount of `order.offerAsset` actually spent by this fill (`≤ offerAmount` in aggregate). -/
  filledIn  : ℚ
  /-- The realized `wantAsset`-per-`offerAsset` execution rate (`≥ order.limitPrice`). -/
  execPrice : ℚ
  deriving Inhabited, DecidableEq

/-- What the fill DELIVERS: `filledIn · execPrice` of the order's `wantAsset`. -/
def Fill.filledOut (f : Fill) : ℚ := f.filledIn * f.execPrice

/-- The un-filled remainder of the order's offer — TRACKED, never lost (`no_value_lost`). -/
def Fill.remainder (f : Fill) : ℚ := f.order.offerAmount - f.filledIn

/-- **A single fill respects the order's terms** — nonnegative spend, a nonnegative limit price, and
execution AT OR ABOVE the limit (`limitPrice ≤ execPrice`: the order never receives worse than the
rate it declared). The aggregate `filledIn ≤ offerAmount` bound is a BOOK-level law (`BookValid`),
since one order may be split across fills. -/
def FillValid (f : Fill) : Prop :=
  0 ≤ f.filledIn ∧ 0 ≤ f.order.limitPrice ∧ f.order.limitPrice ≤ f.execPrice

/-! ## 2. The book — per-order aggregate fill and validity. -/

/-- **`orderFilledIn fills id`** — the TOTAL of the order `id`'s `filledIn` across every fill of it in
the book. The Σ that the partial-fill consistency law (`Σ fills of an order ≤ the order`) bounds. -/
def orderFilledIn (fills : List Fill) (id : ℕ) : ℚ :=
  ((fills.filter (fun f => f.orderId == id)).map Fill.filledIn).sum

/-- **A valid priced book**: every fill respects its order's terms (`FillValid`), AND for every order,
the SUM of its fills' `filledIn` stays within its `offerAmount` (partial-fill consistency — no order
is over-filled, even across multiple fills). -/
def BookValid (fills : List Fill) : Prop :=
  (∀ f ∈ fills, FillValid f) ∧
  (∀ f ∈ fills, orderFilledIn fills f.orderId ≤ f.order.offerAmount)

/-! ## 3. Per-asset conservation — the priced lift of `clearing_conserves_per_asset`. -/

/-- **`legDelta f a`** — the net change fill `f` makes to asset `a`'s total: `+filledOut` if `a` is
what the order WANTS (credited), `−filledIn` if `a` is what it OFFERS (debited), `0` otherwise. The
priced/continuous analogue of `toBal`'s per-asset reading. -/
def legDelta (f : Fill) (a : AssetId) : ℚ :=
  (if f.order.wantAsset = a then f.filledOut else 0)
    - (if f.order.offerAsset = a then f.filledIn else 0)

/-- **`netFlow fills a`** — Σ over the book of the per-asset net change to asset `a`. Conservation is
`netFlow = 0`: the market moves value between participants but neither mints nor burns any asset — the
ℚ-priced generalization of rung-1's `Σ in = Σ out` (`clearing_conserves_per_asset`). -/
def netFlow (fills : List Fill) (a : AssetId) : ℚ :=
  (fills.map (fun f => legDelta f a)).sum

/-- **The clearing CONSERVES per asset** — no asset is minted or burned by the whole book. -/
def Conserves (fills : List Fill) : Prop := ∀ a, netFlow fills a = 0

@[simp] theorem netFlow_nil (a : AssetId) : netFlow [] a = 0 := rfl

@[simp] theorem netFlow_cons (f : Fill) (fs : List Fill) (a : AssetId) :
    netFlow (f :: fs) a = legDelta f a + netFlow fs a := by
  simp [netFlow]

/-- **`netFlow` is ADDITIVE over book concatenation** — the bridge that lets per-pair conservations
compose into a global one (`Conserves_append`). -/
theorem netFlow_append (f1 f2 : List Fill) (a : AssetId) :
    netFlow (f1 ++ f2) a = netFlow f1 a + netFlow f2 a := by
  simp [netFlow, List.map_append, List.sum_append]

/-- **MULTI-PAIR COMPOSITION — two conserving sub-books compose to one conserving book.** The
per-pair conservations SUM: if `f1` conserves every asset and `f2` conserves every asset, so does
`f1 ++ f2`. This is how a multi-pair clearing (one sub-book per trading pair) conserves globally from
its per-pair pieces — the lift of "the per-pair conservations compose to a global conservation." -/
theorem Conserves_append {f1 f2 : List Fill} (h1 : Conserves f1) (h2 : Conserves f2) :
    Conserves (f1 ++ f2) := by
  intro a; rw [netFlow_append, h1 a, h2 a, add_zero]

/-- **NO CROSS-PAIR LEAK — a sub-book that never touches asset `a` contributes `0` to it.** If no fill
in the book offers or wants `a`, then `netFlow · a = 0`: a trading pair that does not involve `a`
cannot move `a`. The `multi_domain_independent` shape — pairs are isolated; value in one pair's assets
does not leak into another's. -/
theorem netFlow_untouched (fills : List Fill) (a : AssetId)
    (h : ∀ f ∈ fills, f.order.offerAsset ≠ a ∧ f.order.wantAsset ≠ a) :
    netFlow fills a = 0 := by
  induction fills with
  | nil => rfl
  | cons f fs ih =>
    rw [netFlow_cons]
    have hf := h f (by simp)
    rw [legDelta, if_neg hf.2, if_neg hf.1,
        ih (fun g hg => h g (by simp [hg]))]
    ring

/-! ## 4. Partial fills respect the order's limits (the priced `clearing_respects_limits`). -/

/-- **Each fill's spend is ≤ the order's per-order aggregate** — a single fill never exceeds the sum
of the order's fills (given all spends nonnegative). The bridge to the `offerAmount` bound. -/
theorem filledIn_le_orderFilledIn {fills : List Fill}
    (hpos : ∀ g ∈ fills, 0 ≤ g.filledIn) (f : Fill) (hf : f ∈ fills) :
    f.filledIn ≤ orderFilledIn fills f.orderId := by
  unfold orderFilledIn
  apply List.single_le_sum
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hpos g (List.mem_of_mem_filter hg)
  · rw [List.mem_map]
    exact ⟨f, List.mem_filter.2 ⟨hf, by simp⟩, rfl⟩

/-- **PARTIAL FILL WITHIN OFFER (the give-side limit)** — in a valid book, every fill spends `≤` its
order's `offerAmount`, even when the order is split across several fills. The priced lift of rung-1's
"debited ≤ offered" (`settlement_from_sender_within_offer`). -/
theorem partial_fill_within_offer {fills : List Fill} (h : BookValid fills)
    (f : Fill) (hf : f ∈ fills) : f.filledIn ≤ f.order.offerAmount :=
  le_trans (filledIn_le_orderFilledIn (fun g hg => (h.1 g hg).1) f hf) (h.2 f hf)

/-- **PARTIAL FILL MEETS THE PRO-RATA MINIMUM (the receive-side limit)** — a valid fill delivers at
least `filledIn · limitPrice` of `wantAsset`: it receives no worse than the order's declared rate on
the portion filled. The priced lift of rung-1's "received ≥ `wantMin`"
(`cycle_individuallyRational`) — at a full fill (`filledIn = offerAmount`) this is
`offerAmount · limitPrice`, exactly `wantMin` for the embedded order (`ofMatchNode`). -/
theorem partial_fill_meets_min {f : Fill} (h : FillValid f) :
    f.filledIn * f.order.limitPrice ≤ f.filledOut :=
  mul_le_mul_of_nonneg_left h.2.2 h.1

/-- **NO VALUE LOST** — the filled amount plus the tracked remainder is exactly the order's offer;
the un-filled part is accounted, never dropped. -/
theorem no_value_lost (f : Fill) : f.filledIn + f.remainder = f.order.offerAmount := by
  unfold Fill.remainder; ring

/-- The remainder is nonnegative in a valid book (`filledIn ≤ offerAmount`) — a real leftover, not an
over-fill. -/
theorem remainder_nonneg {fills : List Fill} (h : BookValid fills)
    (f : Fill) (hf : f ∈ fills) : 0 ≤ f.remainder := by
  have := partial_fill_within_offer h f hf
  unfold Fill.remainder; linarith

/-! ## 5. THE KEYSTONE — priced · partial-fill · multi-pair clearing is sound. -/

/-- **`priced_clearing_keystone` — a valid, conserving priced book satisfies all three DrEX rung-5
guarantees at once.** For a `BookValid` book that `Conserves`:

  * **(a) conserves per-asset globally** — `netFlow = 0` on EVERY asset (no mint, no burn), across
    all pairs (`clearing_conserves_per_asset` lifted to ℚ);
  * **(b) respects every order's declared limits at the cleared price** — each fill spends `≤` its
    `offerAmount` (give side), executes AT OR ABOVE its `limitPrice`, and thereby delivers `≥` its
    pro-rata minimum `filledIn · limitPrice` (receive side) — `clearing_respects_limits` lifted to
    priced partial fills;
  * **(c) partial fills are consistent** — the Σ of an order's fills is `≤` the order
    (`orderFilledIn ≤ offerAmount`), and each fill's `filledIn + remainder = offerAmount` with
    `remainder ≥ 0` (the un-filled part tracked, no value lost).

This is DrEX's matching engine as a real exchange — priced, partial-fillable, multi-pair — as one
theorem. Its refusing power is the teeth of §6 (`overfill_refused` / `badPrice_refused` /
`pairLeak_refused`): an over-fill, an under-limit price, or a leak is not a valid conserving book. -/
theorem priced_clearing_keystone (fills : List Fill)
    (hbook : BookValid fills) (hcons : Conserves fills) :
    (∀ a, netFlow fills a = 0) ∧
    (∀ f ∈ fills, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ fills, orderFilledIn fills f.orderId ≤ f.order.offerAmount ∧
      f.filledIn + f.remainder = f.order.offerAmount ∧ 0 ≤ f.remainder) :=
  ⟨hcons,
   fun f hf =>
     ⟨partial_fill_within_offer hbook f hf,
      (hbook.1 f hf).2.2,
      partial_fill_meets_min (hbook.1 f hf)⟩,
   fun f hf =>
     ⟨hbook.2 f hf, no_value_lost f, remainder_nonneg hbook f hf⟩⟩

/-! ## 6. Composition BACK to rungs 1-2 — the priced law degenerates to the exact-book law. -/

open Dregg2.Intent.Ring (MatchNode)

/-- **Embed a rung-1/2 `MatchNode` as a `PricedOrder`.** The exact-book order (`offerAmount` of
`offerAsset`, wanting `≥ wantMin` of `wantAsset`) becomes the priced order with `limitPrice =
wantMin / offerAmount` — the implicit rate the exact book already carried. -/
def PricedOrder.ofMatchNode (n : MatchNode) : PricedOrder where
  creator     := n.creator
  offerAsset  := n.offerAsset
  wantAsset   := n.wantAsset
  offerAmount := (n.offerAmount : ℚ)
  limitPrice  := (n.wantMin : ℚ) / (n.offerAmount : ℚ)

/-- **The priced fill law RECOVERS rung-1's `received = wantMin` exactly.** A FULL fill
(`filledIn = offerAmount`) at the limit price of an embedded `MatchNode` delivers precisely
`wantMin` of `wantAsset` — the exact amount rung-1's `cycle_individuallyRational` guarantees. So the
priced substrate is a conservative generalization: on an exact, full, unit-priced book it is rung 1.
(Requires `offerAmount ≠ 0`, as any real order has.) -/
theorem ofMatchNode_full_fill_meets_wantMin (n : MatchNode) (hne : (n.offerAmount : ℚ) ≠ 0) :
    (Fill.filledOut
      { orderId := 0, order := PricedOrder.ofMatchNode n,
        filledIn := (n.offerAmount : ℚ),
        execPrice := (PricedOrder.ofMatchNode n).limitPrice }) = (n.wantMin : ℚ) := by
  simp only [Fill.filledOut, PricedOrder.ofMatchNode]
  field_simp

/-! ## 7. UNBLOCKING RUNG 4 — uniform-price is now STATABLE. -/

/-- **`ClearsAtUniformPrice fills x y p` — one exchange rate for a one-pair batch.** Every leg trading
pair `(x, y)` clears at the SAME rate: an `x → y` order executes at `p` (`y` per `x`), a `y → x` order
at `p⁻¹`. THIS PREDICATE COULD NOT BE WRITTEN before rung 5 — it references `execPrice`, which the
exact `DemoRes` book (rungs 1-2) does not have. It is the substrate the rung-4 keystone
**`uniform_price_optimal`** (all legs of a two-sided one-pair batch clear at one price ⇒ no coalition
re-trades to strictly improve — Budish FBA / Shapley–Scarf core) is stated over. Rung 4 is now
well-typed; the design's §5 dependency inversion (rung 4 blocked on rung 5) is discharged at the
substrate. -/
def ClearsAtUniformPrice (fills : List Fill) (x y : AssetId) (p : ℚ) : Prop :=
  ∀ f ∈ fills,
    (f.order.offerAsset = x ∧ f.order.wantAsset = y → f.execPrice = p) ∧
    (f.order.offerAsset = y ∧ f.order.wantAsset = x → f.execPrice = p⁻¹)

/-! ## 8. NON-VACUITY, positive polarity — a priced book with a PARTIAL fill clears. -/

/-- Order 0: creator 1 offers 10 of asset 0 (gold), wants ≥ ½ art per gold (i.e. ≥ 5 art). -/
def o0 : PricedOrder :=
  { creator := 1, offerAsset := 0, wantAsset := 1, offerAmount := 10, limitPrice := 1/2 }

/-- Order 1: creator 2 offers 5 of asset 1 (art), wants ≥ 2 gold per art (i.e. ≥ 10 gold). -/
def o1 : PricedOrder :=
  { creator := 2, offerAsset := 1, wantAsset := 0, offerAmount := 5, limitPrice := 2 }

/-- Fill of order 0: spends **8** of 10 gold (PARTIAL) at ½ art/gold → receives 4 art. -/
def pf0 : Fill := { orderId := 0, order := o0, filledIn := 8, execPrice := 1/2 }

/-- Fill of order 1: spends **4** of 5 art (PARTIAL) at 2 gold/art → receives 8 gold. -/
def pf1 : Fill := { orderId := 1, order := o1, filledIn := 4, execPrice := 2 }

/-- **The worked priced book**: a two-sided gold/art clearing where BOTH sides are partially filled
(8 < 10 gold, 4 < 5 art). Gold moved: order 0 out 8 = order 1 in 8. Art moved: order 1 out 4 =
order 0 in 4. It clears at the uniform rate ½ (art per gold). -/
def posFills : List Fill := [pf0, pf1]

/-- The worked book is valid — both fills respect their orders' terms and neither order is over-filled
(`orderFilledIn` 8 ≤ 10, 4 ≤ 5). -/
theorem posFills_valid : BookValid posFills := by
  constructor
  · intro f hf; fin_cases hf <;> norm_num [FillValid, pf0, pf1, o0, o1]
  · intro f hf
    fin_cases hf <;> norm_num [orderFilledIn, posFills, pf0, pf1, o0, o1]

/-- The worked book conserves EVERY asset: gold (asset 0) and art (asset 1) net to zero, and every
other asset is untouched. A real priced/partial-fill clearing that neither mints nor burns. -/
theorem posFills_conserves : Conserves posFills := by
  intro a
  by_cases h0 : a = 0
  · subst h0
    norm_num [netFlow, posFills, pf0, pf1, o0, o1, legDelta, Fill.filledOut]
  · by_cases h1 : a = 1
    · subst h1
      norm_num [netFlow, posFills, pf0, pf1, o0, o1, legDelta, Fill.filledOut]
    · refine netFlow_untouched posFills a ?_
      intro f hf
      fin_cases hf <;> refine ⟨?_, ?_⟩ <;> first | exact Ne.symm h0 | exact Ne.symm h1

/-- **THE KEYSTONE, INSTANTIATED — the worked priced/partial-fill book satisfies all of rung 5.**
Conserving, limit-respecting at the cleared prices, and partial-fill-consistent. A non-vacuous
witness that the substrate does real work. -/
theorem posBook_keystone :
    (∀ a, netFlow posFills a = 0) ∧
    (∀ f ∈ posFills, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ posFills, orderFilledIn posFills f.orderId ≤ f.order.offerAmount ∧
      f.filledIn + f.remainder = f.order.offerAmount ∧ 0 ≤ f.remainder) :=
  priced_clearing_keystone posFills posFills_valid posFills_conserves

/-- **The worked book clears at a UNIFORM PRICE ½** (art per gold): the gold→art leg executes at ½,
the art→gold leg at 2 = (½)⁻¹. The rung-4 substrate `ClearsAtUniformPrice`, non-vacuously satisfied —
concrete proof that uniform-price optimality is now statable over a real cleared book. -/
theorem posBook_uniform_price : ClearsAtUniformPrice posFills 0 1 (1/2) := by
  intro f hf
  fin_cases hf <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simp_all [pf0, pf1, o0, o1]

/-! ### `#guard` smoke — the cleared amounts and prices are COMPUTED, not asserted. -/

-- order 0: spends 8 gold (partial of 10), receives 4 art, at execPrice ½; remainder 2 gold TRACKED:
#guard pf0.filledIn == (8 : ℚ)
#guard pf0.filledOut == (4 : ℚ)
#guard pf0.execPrice == (1/2 : ℚ)
#guard pf0.remainder == (2 : ℚ)
-- order 1: spends 4 art (partial of 5), receives 8 gold, at execPrice 2; remainder 1 art TRACKED:
#guard pf1.filledIn == (4 : ℚ)
#guard pf1.filledOut == (8 : ℚ)
#guard pf1.remainder == (1 : ℚ)
-- Σ per order ≤ offer (partial-fill consistency), both strictly inside:
#guard orderFilledIn posFills 0 == (8 : ℚ)   -- ≤ 10
#guard orderFilledIn posFills 1 == (4 : ℚ)   -- ≤ 5
-- per-asset net flow is zero on both traded assets (conservation, computed):
#guard netFlow posFills 0 == (0 : ℚ)          -- gold
#guard netFlow posFills 1 == (0 : ℚ)          -- art

/-! ## 9. NON-VACUITY, MULTI-PAIR — a second pair composes without leaking. -/

/-- A DISJOINT second pair (assets 2 ↔ 3): order 2 offers 6 of asset 2 wanting ≥ 6 of asset 3; order 3
the mirror. Both fully filled at rate 1. -/
def o2 : PricedOrder :=
  { creator := 3, offerAsset := 2, wantAsset := 3, offerAmount := 6, limitPrice := 1 }
def o3 : PricedOrder :=
  { creator := 4, offerAsset := 3, wantAsset := 2, offerAmount := 6, limitPrice := 1 }
def pf2 : Fill := { orderId := 2, order := o2, filledIn := 6, execPrice := 1 }
def pf3 : Fill := { orderId := 3, order := o3, filledIn := 6, execPrice := 1 }

/-- The second pair's book (assets 2/3). -/
def pair2Fills : List Fill := [pf2, pf3]

/-- **The multi-pair book** — the gold/art pair and the asset-2/3 pair cleared TOGETHER. -/
def multiPairFills : List Fill := posFills ++ pair2Fills

theorem pair2Fills_conserves : Conserves pair2Fills := by
  intro a
  by_cases h2 : a = 2
  · subst h2
    norm_num [netFlow, pair2Fills, pf2, pf3, o2, o3, legDelta, Fill.filledOut]
  · by_cases h3 : a = 3
    · subst h3
      norm_num [netFlow, pair2Fills, pf2, pf3, o2, o3, legDelta, Fill.filledOut]
    · refine netFlow_untouched pair2Fills a ?_
      intro f hf
      fin_cases hf <;> refine ⟨?_, ?_⟩ <;> first | exact Ne.symm h2 | exact Ne.symm h3

/-- **MULTI-PAIR CONSERVATION COMPOSES** — the two per-pair conservations sum to a global one, by
`Conserves_append`. Clearing many pairs together conserves every asset globally. -/
theorem multiPairFills_conserves : Conserves multiPairFills :=
  Conserves_append posFills_conserves pair2Fills_conserves

/-- **NO CROSS-PAIR LEAK** — the asset-2/3 pair contributes nothing to gold or art: pairs are
isolated (`netFlow_untouched`), the `multi_domain_independent` shape at the priced substrate. -/
theorem pair2_no_leak_into_pair1 :
    netFlow pair2Fills 0 = 0 ∧ netFlow pair2Fills 1 = 0 := by
  refine ⟨netFlow_untouched _ _ ?_, netFlow_untouched _ _ ?_⟩ <;>
    (intro f hf; fin_cases hf <;> decide)

#guard netFlow multiPairFills 2 == (0 : ℚ)
#guard netFlow multiPairFills 3 == (0 : ℚ)
#guard netFlow pair2Fills 0 == (0 : ℚ)   -- pair-2 does not move gold

/-! ## 10. NON-VACUITY, negative polarity — the teeth (an unsound clearing is REFUSED). -/

/-- Two fills of order 0 spending 8 + 5 = 13 > its `offerAmount` 10 — an OVER-FILL. -/
def ov0 : Fill := { orderId := 0, order := o0, filledIn := 8, execPrice := 1/2 }
def ov1 : Fill := { orderId := 0, order := o0, filledIn := 5, execPrice := 1/2 }
def overFills : List Fill := [ov0, ov1]

/-- **TOOTH (partial-fill consistency): an OVER-FILLED order is REFUSED.** The book fills order 0 for
13 (8 + 5) against its offer of 10 — filling BEYOND the order. It is not `BookValid`: the
`orderFilledIn ≤ offerAmount` clause fails (`13 ≤ 10` is false). Mirrors rung-1's `mint_refused`. -/
theorem overfill_refused : ¬ BookValid overFills := by
  rintro ⟨-, hw⟩
  have h := hw ov0 (by simp [overFills])
  norm_num [orderFilledIn, overFills, ov0, ov1, o0] at h

/-- A fill of order 0 at execPrice ¼ — BELOW its declared limit ½ (an inconsistent price: the order
would receive worse than its stated rate). -/
def badFill : Fill := { orderId := 0, order := o0, filledIn := 8, execPrice := 1/4 }
def badFills : List Fill := [badFill]

/-- **TOOTH (price): a leg CLEARED BELOW the order's limit price is REFUSED.** The fill executes at ¼
against a declared minimum of ½ — the order receives less than the rate it declared acceptable. Not
`FillValid` (`limitPrice ≤ execPrice` fails: `½ ≤ ¼` is false), so the book is not `BookValid`.
Mirrors rung-2's `substitution_refused`. -/
theorem badPrice_refused : ¬ BookValid badFills := by
  rintro ⟨hv, -⟩
  have h := hv badFill (by simp [badFills])
  norm_num [FillValid, badFill, o0] at h

/-- A one-sided book: gold spent OUT (via `pf0`) with no counterparty returning gold — value would
LEAK out of the gold/art pair. -/
def leakFills : List Fill := [pf0]

/-- **TOOTH (conservation / cross-pair leak): a leaking clearing is REFUSED.** `pf0` alone spends 8
gold with nothing crediting gold back — asset 0 nets `−8 ≠ 0`. The book does NOT `Conserves`: value
cannot silently leave a pair (nor cross into another). The conservation half of the keystone has real
refusing power — mirrors rung-1's mint/burn refusal. -/
theorem pairLeak_refused : ¬ Conserves leakFills := by
  intro h
  have h0 := h 0
  norm_num [netFlow, leakFills, pf0, o0, legDelta, Fill.filledOut] at h0

/-! ### Axiom hygiene — the rung-5 keystones pinned kernel-clean. -/

#assert_all_clean [Market.netFlow_append, Market.Conserves_append, Market.netFlow_untouched,
  Market.filledIn_le_orderFilledIn, Market.partial_fill_within_offer, Market.partial_fill_meets_min,
  Market.no_value_lost, Market.remainder_nonneg, Market.priced_clearing_keystone,
  Market.ofMatchNode_full_fill_meets_wantMin, Market.posFills_valid, Market.posFills_conserves,
  Market.posBook_keystone, Market.posBook_uniform_price, Market.pair2Fills_conserves,
  Market.multiPairFills_conserves, Market.pair2_no_leak_into_pair1, Market.overfill_refused,
  Market.badPrice_refused, Market.pairLeak_refused]

end Market
