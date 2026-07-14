/-
# Market.QuantizedConservation — Weld A: quantized per-asset conservation is no-wrap-sound.

The STARK checks per-vertex flow conservation as a **field** (`ZMod p`) equality — the AIR asserts, for
each vertex of the fhEgg circulation, that the modular sum of the inflow edge-flows equals the modular
sum of the outflow edge-flows. A field equality is *not* an integer equality: it admits a discrepancy of
exactly `p` — a **value-minting wraparound**, where an output is committed to `p − k` and the modular gate
still balances. This file welds the modular gate to EXACT integer per-vertex conservation using the
deployed **no-wrap discipline** (`Dregg2.Bignum.legs_noWrap_conservation`): each edge flow is
range-bounded below `2 ^ VALUE_BITS`, and the vertex degree obeys `#edges · 2 ^ VALUE_BITS ≤ p`, so every
per-vertex sum lives in `[0, p)`. Two range-bounded integers below `p` that agree mod `p` are EQUAL, so
the wraparound mint is refused.

## What is proved (honest scope)

  * `perVertexConservation_noWrap` — the per-vertex gate: field-checked congruence + no-wrap range bounds
    ⇒ exact integer `inflow.sum = outflow.sum`. A direct instance of `legs_noWrap_conservation`.
  * `perVertexConservation_field` — the same, phrased on the ACTUAL `ZMod p` equality the AIR asserts
    (the field congruence is the AIR's native form), reduced to the `%`-form via `ZMod.natCast_…`.
  * `noWrap_range_load_bearing` / `mintWraparound_at_babyBear` — the range bound is LOAD-BEARING: drop it
    and the modular gate mints `p` (an output committed to the wraparound of the modulus). Concrete.
  * `balanced_vertex_conserves` — a worked balanced vertex at deployed-ish params (`VALUE_BITS = 26`,
    `p = babyBearP`) passes the gate and the theorem yields exact conservation. Non-vacuous positive.
  * `wholeCirculation_conserves` / `wholeCirculation_total_conserves` — whole-circulation conservation as
    the conjunction of the per-vertex gate across a `List` of vertices, and the total-flow corollary.

**Honest scope.** The content is the per-vertex ℕ statement `inflow.sum = outflow.sum` and its
`List`-indexed conjunction; this is the honest shape of no-wrap circulation conservation. It is
deliberately NOT forced onto the abstract `Matrix` incidence form (`A f = 0`) — the per-vertex inflow /
outflow leg sums ARE the incidence rows, and the ℕ-list statement is the faithful, non-vacuous content of
the gate the AIR actually checks. Pure.
-/
import Market.MintSafeQuantization
import Dregg2.Bignum
import Mathlib.Data.ZMod.Basic

namespace Market

/-- The deployed value range: each edge flow is committed as a `VALUE_BITS`-bit non-negative integer. The
shielded ring-clearing AIR range-checks every flow limb to `< 2 ^ VALUE_BITS` (`shielded_ring_clearing_air`
`::VALUE_BITS`). Fixed at 26 bits here. -/
def VALUE_BITS : ℕ := 26

/-- The deployed field modulus — BabyBear, `p = 15 · 2^27 + 1 = 2013265921`. The no-wrap bound the AIR
enforces is `#edges · 2 ^ VALUE_BITS ≤ p`; at 26-bit flows this admits up to `⌊p / 2^26⌋ = 29` edges per
vertex leg before the modular sum could wrap. -/
def babyBearP : ℕ := 2013265921

/-! ## 1. The per-vertex no-wrap conservation gate. -/

/-- **`perVertexConservation_noWrap` — the per-vertex gate (Weld A keystone).** For a single vertex of the
fhEgg circulation, given its inflow edge-flows `inflow` and outflow edge-flows `outflow` (each a `List ℕ`
of committed flow values), with:

  * every flow range-bounded below `2 ^ VALUE_BITS` (`hin` / `hout`, the AIR's per-limb range check);
  * each leg's degree obeying the no-wrap bound `#edges · 2 ^ VALUE_BITS ≤ p` (`hlenIn` / `hlenOut`);
  * the FIELD-checked congruence `inflow.sum % p = outflow.sum % p` (`hcong`, what the STARK verifies);

the exact integer conservation `inflow.sum = outflow.sum` follows. A range-bounded sum below `p` that
agrees mod `p` is EQUAL — the wraparound mint is refused. Direct instance of
`Dregg2.Bignum.legs_noWrap_conservation` with `n := VALUE_BITS`. -/
theorem perVertexConservation_noWrap {p : ℕ} {inflow outflow : List ℕ}
    (hp : 0 < p)
    (hin  : ∀ x ∈ inflow,  x < 2 ^ VALUE_BITS)
    (hout : ∀ x ∈ outflow, x < 2 ^ VALUE_BITS)
    (hlenIn  : inflow.length  * 2 ^ VALUE_BITS ≤ p)
    (hlenOut : outflow.length * 2 ^ VALUE_BITS ≤ p)
    (hcong : inflow.sum % p = outflow.sum % p) :
    inflow.sum = outflow.sum :=
  Dregg2.Bignum.legs_noWrap_conservation hp hin hout hlenIn hlenOut hcong

/-- **`perVertexConservation_field` — the gate on the AIR's native field equality.** The STARK asserts the
conservation clause as an equality in `ZMod p` (`hfield`), not a `%`-equality. This is the same keystone
reading the field form directly: `((inflow.sum : ℕ) : ZMod p) = ((outflow.sum : ℕ) : ZMod p)` together
with the no-wrap range bounds refines to exact `inflow.sum = outflow.sum`. -/
theorem perVertexConservation_field {p : ℕ} {inflow outflow : List ℕ}
    (hp : 0 < p)
    (hin  : ∀ x ∈ inflow,  x < 2 ^ VALUE_BITS)
    (hout : ∀ x ∈ outflow, x < 2 ^ VALUE_BITS)
    (hlenIn  : inflow.length  * 2 ^ VALUE_BITS ≤ p)
    (hlenOut : outflow.length * 2 ^ VALUE_BITS ≤ p)
    (hfield : ((inflow.sum : ℕ) : ZMod p) = ((outflow.sum : ℕ) : ZMod p)) :
    inflow.sum = outflow.sum :=
  perVertexConservation_noWrap hp hin hout hlenIn hlenOut
    ((ZMod.natCast_eq_natCast_iff' _ _ _).mp hfield)

/-! ## 2. The range bound is LOAD-BEARING — drop it and the modular gate MINTS.

Without the range discipline, a field-balanced vertex can mint the full modulus: an output committed to
the wraparound of `p` (equivalently, a flow whose true integer value is `k` but is committed as `p + k`,
or here `p` itself committed against nothing in) satisfies the modular gate `outflow.sum ≡ inflow.sum`
while the true integers differ by `p`. This is exactly the "output committed to `p − k`" mint the no-wrap
bound refuses. -/

/-- **`noWrap_range_load_bearing` — the mint when the range bound is dropped.** There is a vertex with
NOTHING flowing in and a single outflow edge committed to the modulus `p`, whose modular sums agree
(`p ≡ 0`) yet whose true integer sums differ by `p` — a mint of the entire modulus. The single flow value
`p` is NOT `< 2 ^ VALUE_BITS`, so `perVertexConservation_noWrap`'s range hypothesis is precisely what
forbids it. -/
theorem noWrap_range_load_bearing :
    ∃ (p : ℕ) (inflow outflow : List ℕ),
      0 < p ∧
      inflow.sum % p = outflow.sum % p ∧
      inflow.sum ≠ outflow.sum :=
  ⟨babyBearP, [], [babyBearP], by decide, by decide, by decide⟩

-- The mint is concrete at the DEPLOYED modulus: empty inflow vs. one outflow committed to `p = babyBearP`.
-- Modular gate balances (`p % p = 0 = [].sum % p`) but the true integers differ by the whole modulus.
#guard (([babyBearP] : List ℕ).sum % babyBearP == ([] : List ℕ).sum % babyBearP)
#guard !decide (([babyBearP] : List ℕ).sum = ([] : List ℕ).sum)

/-- **`mintWraparound_at_babyBear` — the "output committed to `p − k`" mint, concretely.** An honest
inflow of `1000` against an outflow committed to `p − 1000 + 1000 ≡ 1000`… stated at its sharpest: an
inflow summing to `k` and an outflow whose committed integer is `k + p` are field-equal but mint `p`.
Here `k = 1000`, `outflow = [1000 + babyBearP]`. Both agree mod `p`; the true sums differ by `p`. The
outflow flow value `1000 + p` exceeds `2 ^ VALUE_BITS`, so the range bound rejects it. -/
theorem mintWraparound_at_babyBear :
    ([1000] : List ℕ).sum % babyBearP = ([1000 + babyBearP] : List ℕ).sum % babyBearP ∧
    ([1000] : List ℕ).sum ≠ ([1000 + babyBearP] : List ℕ).sum := by
  refine ⟨by decide, by decide⟩

/-! ## 3. Non-vacuity POSITIVE — a worked balanced vertex at deployed-ish params. -/

/-- Balanced vertex: two inflow edges of `100` and `200` (sum `300`) against one outflow edge of `300`.
Every flow is a 26-bit value (`< 2^26 = 67108864`); each leg's degree bound holds
(`2 · 2^26 = 134217728 ≤ babyBearP`). -/
def exInflow : List ℕ := [100, 200]
/-- Balanced vertex: the single outflow edge. -/
def exOutflow : List ℕ := [300]

/-- **`balanced_vertex_conserves` — the honest vertex PASSES and yields exact conservation.** Routed
through `perVertexConservation_noWrap` at the deployed params (`VALUE_BITS = 26`, `p = babyBearP`): all
hypotheses (range bounds, degree bounds, field congruence) are satisfiable, and the theorem concludes the
exact integer conservation `exInflow.sum = exOutflow.sum` (both `300`). Non-vacuous positive polarity. -/
theorem balanced_vertex_conserves : exInflow.sum = exOutflow.sum :=
  perVertexConservation_noWrap (p := babyBearP) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- The balanced vertex's leg sums are equal (300 = 300), computed:
#guard exInflow.sum == 300
#guard exOutflow.sum == 300
#guard exInflow.sum == exOutflow.sum
-- Every flow is a genuine 26-bit value and the degree bounds hold at BabyBear:
#guard decide (∀ x ∈ exInflow, x < 2 ^ VALUE_BITS)
#guard decide (exInflow.length * 2 ^ VALUE_BITS ≤ babyBearP)

/-- The field-form gate also accepts the honest vertex: the `ZMod babyBearP` congruence holds and
`perVertexConservation_field` yields the same exact conservation. -/
theorem balanced_vertex_conserves_field : exInflow.sum = exOutflow.sum :=
  perVertexConservation_field (p := babyBearP) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## 4. Whole-circulation conservation — the per-vertex gate, conjoined across a finite vertex set. -/

/-- A vertex of the circulation carries its inflow and outflow edge-flows. -/
structure Vertex where
  inflow  : List ℕ
  outflow : List ℕ

/-- **`wholeCirculation_conserves` — whole-circulation conservation.** Given a `List` of vertices, each
satisfying the per-vertex range bounds, degree bounds, and the field-checked congruence, EVERY vertex
conserves exactly: `inflow.sum = outflow.sum`. The whole circulation is the conjunction of the per-vertex
gate `perVertexConservation_noWrap`, applied pointwise. -/
theorem wholeCirculation_conserves {p : ℕ} (hp : 0 < p) (vertices : List Vertex)
    (hin  : ∀ v ∈ vertices, ∀ x ∈ v.inflow,  x < 2 ^ VALUE_BITS)
    (hout : ∀ v ∈ vertices, ∀ x ∈ v.outflow, x < 2 ^ VALUE_BITS)
    (hlenIn  : ∀ v ∈ vertices, v.inflow.length  * 2 ^ VALUE_BITS ≤ p)
    (hlenOut : ∀ v ∈ vertices, v.outflow.length * 2 ^ VALUE_BITS ≤ p)
    (hcong : ∀ v ∈ vertices, v.inflow.sum % p = v.outflow.sum % p) :
    ∀ v ∈ vertices, v.inflow.sum = v.outflow.sum := by
  intro v hv
  exact perVertexConservation_noWrap hp (hin v hv) (hout v hv)
    (hlenIn v hv) (hlenOut v hv) (hcong v hv)

/-- **`wholeCirculation_total_conserves` — total inflow equals total outflow.** With every vertex
conserving exactly (the conclusion of `wholeCirculation_conserves`), the total of all inflow leg-sums
equals the total of all outflow leg-sums across the whole circulation. This is the aggregate no-mint
statement: the circulation neither creates nor destroys value. -/
theorem wholeCirculation_total_conserves {p : ℕ} (hp : 0 < p) (vertices : List Vertex)
    (hin  : ∀ v ∈ vertices, ∀ x ∈ v.inflow,  x < 2 ^ VALUE_BITS)
    (hout : ∀ v ∈ vertices, ∀ x ∈ v.outflow, x < 2 ^ VALUE_BITS)
    (hlenIn  : ∀ v ∈ vertices, v.inflow.length  * 2 ^ VALUE_BITS ≤ p)
    (hlenOut : ∀ v ∈ vertices, v.outflow.length * 2 ^ VALUE_BITS ≤ p)
    (hcong : ∀ v ∈ vertices, v.inflow.sum % p = v.outflow.sum % p) :
    (vertices.map (fun v => v.inflow.sum)).sum = (vertices.map (fun v => v.outflow.sum)).sum := by
  have hbal := wholeCirculation_conserves hp vertices hin hout hlenIn hlenOut hcong
  have : vertices.map (fun v => v.inflow.sum) = vertices.map (fun v => v.outflow.sum) :=
    List.map_congr_left (fun v hv => hbal v hv)
  rw [this]

/-! ### Non-vacuity — a worked two-vertex circulation. -/

/-- A concrete circulation: vertex A (`[100,200] → [300]`) and vertex B (`[50] → [20,30]`), both
balanced, both within the deployed 26-bit / BabyBear no-wrap discipline. -/
def exCirculation : List Vertex :=
  [ { inflow := [100, 200], outflow := [300] },
    { inflow := [50],        outflow := [20, 30] } ]

/-- **`worked_circulation_conserves` — the whole worked circulation conserves.** Both vertices pass the
per-vertex gate at `p = babyBearP`, so every vertex conserves exactly. Non-vacuous whole-circulation
positive polarity. -/
theorem worked_circulation_conserves :
    ∀ v ∈ exCirculation, v.inflow.sum = v.outflow.sum :=
  wholeCirculation_conserves (p := babyBearP) (by decide) exCirculation
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **`worked_circulation_total` — the worked circulation's totals match.** Total inflow `= 100+200+50 =
350` equals total outflow `= 300+20+30 = 350`. The aggregate no-mint fact on a concrete instance. -/
theorem worked_circulation_total :
    (exCirculation.map (fun v => v.inflow.sum)).sum
      = (exCirculation.map (fun v => v.outflow.sum)).sum :=
  wholeCirculation_total_conserves (p := babyBearP) (by decide) exCirculation
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- The worked circulation's totals are both 350:
#guard (exCirculation.map (fun v => v.inflow.sum)).sum == 350
#guard (exCirculation.map (fun v => v.outflow.sum)).sum == 350

/-! ## Axiom hygiene — the Weld-A conservation keystones pinned kernel-clean. -/

#assert_all_clean [Market.perVertexConservation_noWrap, Market.perVertexConservation_field,
  Market.noWrap_range_load_bearing, Market.mintWraparound_at_babyBear,
  Market.balanced_vertex_conserves, Market.balanced_vertex_conserves_field,
  Market.wholeCirculation_conserves, Market.wholeCirculation_total_conserves,
  Market.worked_circulation_conserves, Market.worked_circulation_total]

end Market
