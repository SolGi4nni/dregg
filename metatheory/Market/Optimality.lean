/-
# Market.Optimality — DrEX rung 4: UNIFORM-PRICE NO-ARBITRAGE / envy-freeness (the fairness apex).

**The marquee fairness result, now STATABLE.** `docs/deos/DREX-DESIGN.md` §#4 states rung 4: all legs
of a two-sided one-pair batch clear at **one price** (the Budish FBA discipline), and no participant
can strictly improve by an alternative feasible trade at that same price — the *no-arbitrage* /
envy-free core of a uniform-price call auction. §5 records the *dependency inversion finding*: rung 4
**could not be stated before rung 5** (`Market/Priced.lean`), because uniform-price optimality is a
theorem *about prices and partial allocations* the exact `DemoRes` book (rungs 1-2) does not have.
Rung 5 supplied the substrate — `execPrice`, `Fill`, `ClearsAtUniformPrice` — and confirmed the worked
book satisfies it (`posBook_uniform_price`). This file discharges rung 4 over that substrate.

**What is proved (the strongest tractable optimality property, named honestly):**

  * **NO-ARBITRAGE / value-neutrality (`uniform_price_no_arbitrage`, the marquee).** Measured in a
    common numéraire (asset `x`, priced by the uniform rate `p` = `y` per `x`), EVERY leg of a
    uniform-price clearing is **value-neutral**: the numéraire value received equals the value spent
    (`recvValue = spentValue`). Nobody extracts surplus; there is no free value to be had. This is the
    Budish-FBA / "arbitrage-free ⇔ single price" property (arXiv 2310.09782's *strictly-increasing-
    invariant ⇔ no-arb* shape, here specialized to a one-price batch): a uniform price is *exactly* the
    condition under which no participant can strictly improve their value position.
  * **No strictly-improving deviation (`no_improving_deviation`).** The numéraire value net of ANY
    feasible alternative quantity a participant could trade at the uniform price is `0` — never
    strictly positive. So the uniform-price allocation admits no strictly-improving unilateral
    deviation (the FBA optimality reading of no-arbitrage).
  * **Envy-freeness (`uniform_price_envy_free`).** Any two same-direction participants clear at the
    IDENTICAL rate `p`. Nobody faces a worse price than anyone else on their side — the envy-free
    reading of "one price for all."
  * **The capstone (`uniform_price_optimal`).** Composes rung 5's `priced_clearing_keystone`
    (conserves per-asset + respects every declared limit — the individual-rationality floor rung 1
    established, lifted to priced partial fills) WITH the new no-arbitrage guarantee. A uniform-price
    clearing is FIRST individually rational (rung 5 / rung 1) and THEN admits no improving deviation
    (rung 4): sound *and* optimal, as one theorem. This is `uniform_price_optimal` of the design's §7.

**Composition, not duplication.** Conservation, the limit/IR bounds, and `ClearsAtUniformPrice` come
verbatim from `Market/Priced.lean` (rung 5); `Market/Fairness.lean`'s `clearing_respects_limits` /
`Dregg2/Intent/Ring.lean`'s `cycle_individuallyRational` are the rung-1 IR lineage this optimality
result *builds on* (IR first, no-improving-deviation second). Nothing below rung 4 is re-proved.

NON-VACUITY, both polarities (the discipline):
  * **positive** — the worked uniform-price book (`posFills` / `posBook_uniform_price`, rung 5) IS
    no-arbitrage and value-neutral: both legs value exactly `8` in the numéraire, spent = received
    (`posBook_uniform_price_optimal`; `#guard`-pinned). A concrete optimal, core-neutral clearing.
  * **the refuse tooth** — a SPLIT-price book (two same-direction legs at DIFFERENT rates, `½` vs `1`)
    is NOT `ClearsAtUniformPrice` (`splitFills_not_uniform`) AND admits a strictly-improving deviation:
    the off-rate leg extracts strict numéraire surplus (`splitFills_admits_arbitrage`, value `16` for
    an `8` spend — an arbitrage), and its participant is strictly better off than the fair-rate leg on
    the same offer (`splitFills_has_envy` — envy exists). Uniform pricing is *what* buys optimality;
    drop it and arbitrage/envy return. Mirrors rung 5's `badPrice_refused` / rung 1's `overdebit_refused`.

NEXT SUB-RUNG (named, not claimed): **full coalition TTC-core stability** — no *coalition* (not just a
single participant) can re-trade among themselves to make every member weakly and some strictly better
than the uniform-price clearing gives them (the Shapley-Scarf core over multi-party `CycleValid`). The
single-participant no-improving-deviation + envy-freeness proved here is the coalition-of-one / pairwise
core; the general k-coalition argument (a Scarf-balancedness / no-blocking-coalition proof) is the open
sub-rung above this file.

Pure.
-/
import Market.Priced

namespace Market

open Dregg2.Exec (AssetId CellId)

/-! ## 1. The numéraire — value in a common unit at the uniform price. -/

/-- **Numéraire value of holding `amt` of asset `a`**, priced in units of `x` at the uniform rate `p`
(`y` per `x`): one `x` is worth `1`; one `y` is worth `p⁻¹` (since `p` units of `y` buy one `x`); any
off-pair asset is worth `0` here. The common yardstick against which "did anyone extract surplus?" is
asked — the FBA no-arbitrage question is whether value-in = value-out in THIS unit. -/
def numeraireValue (x y : AssetId) (p : ℚ) (a : AssetId) (amt : ℚ) : ℚ :=
  if a = x then amt else if a = y then amt * p⁻¹ else 0

/-- The numéraire value a fill SPENDS: its `filledIn` of the order's `offerAsset`. -/
def spentValue (x y : AssetId) (p : ℚ) (f : Fill) : ℚ :=
  numeraireValue x y p f.order.offerAsset f.filledIn

/-- The numéraire value a fill RECEIVES: its `filledOut` of the order's `wantAsset`. -/
def recvValue (x y : AssetId) (p : ℚ) (f : Fill) : ℚ :=
  numeraireValue x y p f.order.wantAsset f.filledOut

/-- **A fill trades ON the `(x, y)` pair** — it either offers `x` for `y` or offers `y` for `x`. The
domain on which uniform pricing and the numéraire are meaningful. -/
def OnPair (x y : AssetId) (f : Fill) : Prop :=
  (f.order.offerAsset = x ∧ f.order.wantAsset = y) ∨
  (f.order.offerAsset = y ∧ f.order.wantAsset = x)

/-! ## 2. The core lemma — a leg at the uniform price is VALUE-NEUTRAL. -/

/-- **A single on-pair fill executed at the uniform price extracts no surplus** — the numéraire value
it receives EQUALS the value it spends. Both directions:

  * an `x → y` leg spends `filledIn` of `x` (value `filledIn`) and receives `filledIn·p` of `y` (value
    `filledIn·p·p⁻¹ = filledIn`) — neutral;
  * a `y → x` leg spends `filledIn` of `y` (value `filledIn·p⁻¹`) and receives `filledIn·p⁻¹` of `x`
    (value `filledIn·p⁻¹`) — neutral.

This is the atom of no-arbitrage: at ONE price, every feasible trade is a fair swap of equal value.
Needs `x ≠ y` (the pair is genuine) and `p ≠ 0` (a real rate). -/
theorem fill_value_neutral {x y : AssetId} {p : ℚ} (hxy : x ≠ y) (hp : p ≠ 0)
    {f : Fill} (hpair : OnPair x y f)
    (hf1 : f.order.offerAsset = x ∧ f.order.wantAsset = y → f.execPrice = p)
    (hf2 : f.order.offerAsset = y ∧ f.order.wantAsset = x → f.execPrice = p⁻¹) :
    recvValue x y p f = spentValue x y p f := by
  rcases hpair with ⟨ho, hw⟩ | ⟨ho, hw⟩
  · -- x → y leg: executes at p.
    have hep := hf1 ⟨ho, hw⟩
    have hs : spentValue x y p f = f.filledIn := by
      unfold spentValue numeraireValue; rw [ho, if_pos rfl]
    have hr : recvValue x y p f = f.filledIn := by
      unfold recvValue numeraireValue Fill.filledOut
      rw [hw, if_neg (Ne.symm hxy), if_pos rfl, hep, mul_assoc, mul_inv_cancel₀ hp, mul_one]
    rw [hr, hs]
  · -- y → x leg: executes at p⁻¹.
    have hep := hf2 ⟨ho, hw⟩
    have hs : spentValue x y p f = f.filledIn * p⁻¹ := by
      unfold spentValue numeraireValue; rw [ho, if_neg (Ne.symm hxy), if_pos rfl]
    have hr : recvValue x y p f = f.filledIn * p⁻¹ := by
      unfold recvValue numeraireValue Fill.filledOut; rw [hw, if_pos rfl, hep]
    rw [hr, hs]

/-! ## 3. THE MARQUEE — a uniform-price clearing is NO-ARBITRAGE. -/

/-- **`uniform_price_no_arbitrage` — every leg of a uniform-price clearing is value-neutral.** Over a
book whose every on-pair leg clears at the single rate `p` (`ClearsAtUniformPrice`, rung 5), NO
participant extracts numéraire surplus: `recvValue = spentValue` for every fill. The machine-checked
Budish-FBA / "single price ⇔ arbitrage-free" property over the deployed priced substrate — the exact
condition under which no unilateral trade can strictly improve a participant's value position. -/
theorem uniform_price_no_arbitrage {fills : List Fill} {x y : AssetId} {p : ℚ}
    (hxy : x ≠ y) (hp : p ≠ 0) (hu : ClearsAtUniformPrice fills x y p)
    (hpair : ∀ f ∈ fills, OnPair x y f) :
    ∀ f ∈ fills, recvValue x y p f = spentValue x y p f :=
  fun f hf => fill_value_neutral hxy hp (hpair f hf) (hu f hf).1 (hu f hf).2

/-- **`no_improving_deviation` — no feasible deviation at the uniform price strictly improves.** The
numéraire value net of spending any amount `a` at the uniform price `p` (receive `a·p` of the wanted
asset, valued `a·p·p⁻¹ = a`, against the `a` spent) is exactly `0` — for EVERY `a`. So a participant
cannot, by choosing a different feasible quantity at the one price, obtain positive surplus: the
uniform-price allocation admits no strictly-improving unilateral deviation. The FBA optimality reading
of no-arbitrage. -/
def xyDeviationNet (p a : ℚ) : ℚ := a * p * p⁻¹ - a

theorem no_improving_deviation (p : ℚ) (hp : p ≠ 0) (a : ℚ) : xyDeviationNet p a = 0 := by
  unfold xyDeviationNet; rw [mul_assoc, mul_inv_cancel₀ hp, mul_one, sub_self]

/-- **`uniform_price_envy_free` — same-direction participants clear at the IDENTICAL rate.** Any two
`x → y` legs of a uniform-price book execute at the same `p`. Nobody on a side faces a worse price than
a peer — the envy-free reading of "one price for all." (The give/receive limits are already respected
per rung 5, so equal price ⇒ no participant strictly prefers another's terms.) -/
theorem uniform_price_envy_free {fills : List Fill} {x y : AssetId} {p : ℚ}
    (hu : ClearsAtUniformPrice fills x y p) {f g : Fill} (hf : f ∈ fills) (hg : g ∈ fills)
    (hfp : f.order.offerAsset = x ∧ f.order.wantAsset = y)
    (hgp : g.order.offerAsset = x ∧ g.order.wantAsset = y) :
    f.execPrice = g.execPrice := by
  rw [(hu f hf).1 hfp, (hu g hg).1 hgp]

/-! ## 4. THE CAPSTONE — sound (rung 5 / IR) AND optimal (rung 4 / no-arb), composed. -/

/-- **`uniform_price_optimal` — the DrEX fairness capstone.** A `BookValid`, `Conserves`ing clearing
that `ClearsAtUniformPrice` on the `(x, y)` pair is, all at once:

  * **(sound, rung 5 — composed from `priced_clearing_keystone`)** conserving per-asset (`netFlow = 0`
    on every asset) and limit-respecting / individually rational — each fill spends `≤` its
    `offerAmount`, executes at or above its `limitPrice`, and thereby delivers `≥` its pro-rata minimum
    (the rung-1 `cycle_individuallyRational` floor, lifted to priced partial fills);
  * **(optimal, rung 4 — NEW)** no-arbitrage / value-neutral — every leg's numéraire value received
    equals value spent (`uniform_price_no_arbitrage`), so no participant can strictly improve by a
    feasible deviation at the uniform price (`no_improving_deviation`).

Individual rationality FIRST (nobody worse than their declaration), then NO IMPROVING DEVIATION at the
uniform price (nobody can do strictly better) — a uniform-price clearing is sound and optimal as one
theorem. The design's §7 `uniform_price_optimal`, discharged. -/
theorem uniform_price_optimal {fills : List Fill} {x y : AssetId} {p : ℚ}
    (hxy : x ≠ y) (hp : p ≠ 0)
    (hbook : BookValid fills) (hcons : Conserves fills)
    (hu : ClearsAtUniformPrice fills x y p) (hpair : ∀ f ∈ fills, OnPair x y f) :
    (∀ a, netFlow fills a = 0) ∧
    (∀ f ∈ fills, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ fills, recvValue x y p f = spentValue x y p f) := by
  obtain ⟨hc, hl, _⟩ := priced_clearing_keystone fills hbook hcons
  exact ⟨hc, hl, uniform_price_no_arbitrage hxy hp hu hpair⟩

/-! ## 5. NON-VACUITY, positive polarity — the worked book is no-arbitrage / optimal. -/

/-- Both legs of the worked rung-5 book trade on the gold/art pair `(0, 1)`. -/
theorem posFills_onPair : ∀ f ∈ posFills, OnPair 0 1 f := by
  intro f hf; fin_cases hf
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **THE CAPSTONE, INSTANTIATED — the worked uniform-price book is sound AND no-arbitrage.** The
rung-5 witness (`posFills`, clearing at the uniform rate `½`) is conserving, limit-respecting, and
value-neutral on every leg: a concrete individually-rational, arbitrage-free, envy-free clearing. A
non-vacuous witness that rung-4 optimality does real work over a real cleared book. -/
theorem posBook_uniform_price_optimal :
    (∀ a, netFlow posFills a = 0) ∧
    (∀ f ∈ posFills, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ posFills, recvValue 0 1 (1/2) f = spentValue 0 1 (1/2) f) :=
  uniform_price_optimal (by decide) (by norm_num) posFills_valid posFills_conserves
    posBook_uniform_price posFills_onPair

/-! ### `#guard` smoke — value-neutrality is COMPUTED (both legs value exactly 8, spent = received). -/

-- gold→art leg (pf0): spends 8 gold (value 8), receives 4 art (value 4·(½)⁻¹ = 8) — NEUTRAL:
#guard spentValue 0 1 (1/2) pf0 == (8 : ℚ)
#guard recvValue  0 1 (1/2) pf0 == (8 : ℚ)
-- art→gold leg (pf1): spends 4 art (value 4·(½)⁻¹ = 8), receives 8 gold (value 8) — NEUTRAL:
#guard spentValue 0 1 (1/2) pf1 == (8 : ℚ)
#guard recvValue  0 1 (1/2) pf1 == (8 : ℚ)
-- any feasible deviation at the uniform price nets zero value (spend 100 of x → recv 100·p worth 100):
#guard xyDeviationNet (1/2) 100 == (0 : ℚ)

/-! ## 6. NON-VACUITY, negative polarity — the teeth (split price ⇒ arbitrage + envy). -/

/-- A second gold-offering order (a DISTINCT participant, creator 5) with the same terms as `o0`. -/
def o0b : PricedOrder :=
  { creator := 5, offerAsset := 0, wantAsset := 1, offerAmount := 10, limitPrice := 1/2 }

/-- The FAIR leg: creator 1 spends 8 gold for art at the uniform rate ½ → receives 4 art. -/
def fairLeg : Fill := { orderId := 0, order := o0, filledIn := 8, execPrice := 1/2 }

/-- The ARBITRAGE leg: creator 5, SAME direction (gold→art), SAME 8-gold spend, but at rate `1` (≠ the
uniform ½) → receives 8 art. Both fills are individually `FillValid` (`½ ≤ 1`); what fails is UNIFORMITY. -/
def arbLeg : Fill := { orderId := 1, order := o0b, filledIn := 8, execPrice := 1 }

/-- **A SPLIT-price book** — two same-direction gold→art legs at DIFFERENT rates (½ and 1). Exactly the
"legs at different prices" a uniform-price clearing forbids. -/
def splitFills : List Fill := [fairLeg, arbLeg]

/-- **TOOTH (uniformity): the split-price book is NOT a uniform-price clearing.** `arbLeg` is a gold→art
leg (offers `0`, wants `1`) yet executes at `1`, not the batch rate `½` — `ClearsAtUniformPrice … ½`
demands `execPrice = ½` for it, which is false. A split-price clearing is refused as non-uniform. -/
theorem splitFills_not_uniform : ¬ ClearsAtUniformPrice splitFills 0 1 (1/2) := by
  intro h
  have hp := (h arbLeg (by simp [splitFills])).1 ⟨rfl, rfl⟩
  norm_num [arbLeg] at hp

/-- **TOOTH (no-arbitrage FAILS): the off-rate leg extracts strict surplus.** Valued in the numéraire at
the fair rate `½`, `arbLeg` spends `8` gold (value `8`) but receives `8` art worth `8·(½)⁻¹ = 16` — a
STRICT arbitrage gain of `8`. The value-neutrality of §3 fails precisely because the leg is off the
uniform price: `spentValue < recvValue`. Uniform pricing is *what* kills the arbitrage. -/
theorem splitFills_admits_arbitrage :
    spentValue 0 1 (1/2) arbLeg < recvValue 0 1 (1/2) arbLeg := by
  norm_num [spentValue, recvValue, numeraireValue, arbLeg, o0b, Fill.filledOut]

/-- **TOOTH (envy): the split price makes one participant strictly envy the other.** `fairLeg` and
`arbLeg` put the SAME 8 gold on the table, but the off-rate leg receives `8` art against the fair leg's
`4` — the fair participant strictly prefers the arb participant's terms. Envy-freeness fails; a single
uniform price is exactly what removes it. -/
theorem splitFills_has_envy : fairLeg.filledIn = arbLeg.filledIn ∧ fairLeg.filledOut < arbLeg.filledOut := by
  refine ⟨by norm_num [fairLeg, arbLeg], ?_⟩
  norm_num [fairLeg, arbLeg, Fill.filledOut]

/-! ### Axiom hygiene — the rung-4 keystones pinned kernel-clean. -/

#assert_all_clean [Market.fill_value_neutral, Market.uniform_price_no_arbitrage,
  Market.no_improving_deviation, Market.uniform_price_envy_free, Market.uniform_price_optimal,
  Market.posFills_onPair, Market.posBook_uniform_price_optimal, Market.splitFills_not_uniform,
  Market.splitFills_admits_arbitrage, Market.splitFills_has_envy]

end Market
