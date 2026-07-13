/-
# Market.Aggregation — DrEX rung 2: ORDER-BOOK AGGREGATION SOUNDNESS.

Between the raw SUBMITTED orders and the multilateral clearing (`Market/Clearing.lean`, rung 1)
sits the AGGREGATOR: it takes the stream of submitted orders and produces the ordered `Book` the
clearing consumes. This module proves that aggregation is FAITHFUL — the aggregated book neither
DROPS a submitted order, INSERTS an order nobody submitted, nor REORDERS against the declared
priority. It then COMPOSES with rung 1: because the book is a faithful (permutation) image of the
submissions, a clearing of the aggregated book conserves EXACTLY the submitted orders' per-asset
totals — independent of the order the stream happened to arrive in.

## What is reused (not re-proved)

  * **Rung 1's book + clearing** (`Market/Clearing.lean`) — `Book`, `pool`, `offersOf`, `toBal`,
    `MarketClearing`, `clearing_conserves_per_asset`, `clearing_fair`, `ExactBook`,
    `exact_clears_iff`, and the concrete `crossBid`/`artSeller`/`dealer` ring. Aggregation feeds
    INTO these; this module adds NO new clearing law. `bookOfOrders` lands in exactly rung 1's
    `Book`, so every rung-1 theorem applies to the aggregated book verbatim.
  * **The kernel intent** (`Dregg2/Intent/Kernel.lean`) — an order's payload is a `KernelIntent`
    (four faces and all); `Order` wraps it with the two market-microstructure fields aggregation
    needs: a `priority` key (price-time / batch rank) and a `nonce` (the unique submission id).
  * **The no-drop/insert/reorder SHAPE** — Dregg2's `ChainBound`
    (`Dregg2/Distributed/HistoryAggregation.lean`) enforces "no drop/insert/reorder" over the
    TURN stream as a per-adjacent-pair root tooth (`Continues`: `new_root[i] = old_root[i+1]`).
    We reuse that SHAPE over the ORDER stream, at the grain aggregation actually has: whole-list
    faithfulness = a permutation (`Perm`, the "aggregate attests exactly the submissions"), and
    the per-adjacent-pair discipline = `Pairwise (· priority ≤ ·)` (the order-stream analog of
    `ChainBound`'s adjacent `Continues`). When DrEX commits the order stream as a root-chain, the
    two unify into one tooth; here the discipline is proven directly over the list, as rung 1 is.

## The theorems

  * **`aggregate_sound` (THE KEYSTONE)** — the real aggregator (`aggregate = mergeSort` by
    priority) produces an `AggregationSound` book: `faithful` (a permutation of the submissions —
    no drop, no insert) AND `prioritized` (sorted by the declared priority — no reorder). Non-
    vacuous: `aggregate` genuinely reorders (the positive example submits out of priority order).
  * **`no_drop` / `no_insert`** — every submitted order appears in the aggregate, and every
    aggregate entry was submitted (membership, from `faithful`); `faithful_preserves_count`
    pins the true MULTISET (nonce-sum + length preserved — no silent duplicate/substitution).
  * **`aggregated_clearing_conserves_submissions` (THE rung-2→rung-1 COMPOSITION)** — for any
    clearing of the aggregated book, the SUBMITTED orders' per-asset offered total equals the
    allocated total. Composes `clearing_conserves_per_asset` (rung 1) with the permutation-
    invariance of the per-asset Σ: aggregation cannot change what conservation sees.
  * **`aggregated_ring_clears`** — the aggregated ring book (submitted out of order) is exact and
    pool-balanced, so it CLEARS (`exact_clears_iff`): aggregation delivers a clearable book.

NON-VACUITY, both polarities (mirroring rung 1's `validTriangle` / `overdebit_refused`):
positive — `ringSubmissions` submitted in the order dealer, crossBid, artSeller aggregates to the
priority order crossBid, artSeller, dealer, and that book is `AggregationSound` (the `#guard`s pin
the reordered priorities and the preserved nonce multiset). Teeth — a DROPPED book
(`droppedBook`), an INSERTED book (`insertedBook`), and a fabricated-substitution
(`substitutedBook`) are all NOT `faithful` (`drop_refused` / `insert_refused` /
`substitution_refused`); a REORDERED book (`reorderedBook`, a genuine permutation) is NOT
`prioritized` (`reorder_refused`). A book that fails any one tooth is not aggregation-sound.

Pure.
-/
import Market.Clearing
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Market

open Dregg2.Intent
open Dregg2.Exec (AssetId)
open Dregg2.Authority.Blocklace (Lace)
open Dregg2.Authority.Predicate (Registry)
open Dregg2.Time.Frame (FrameStatement)
open List

universe u

variable {R : Type u} {Stmt Wit : Type} {B : Lace} {reg : Registry Stmt Wit}
  {stmtOf : FrameStatement → Stmt}

/-! ## 1. Orders and the aggregator. -/

/-- **A submitted order** — the aggregator's input unit: a kernel `Intent` (the thing that will
clear, four faces and all — reused verbatim), tagged with the two microstructure fields
aggregation reasons about:

  * `priority` — the declared price-time key (or the batch's uniform rank): LOWER is matched
    FIRST. This is the "declared priority" the aggregated book must respect.
  * `nonce` — the unique submission id. A faithful aggregate preserves the multiset of nonces,
    so no order is silently dropped, duplicated, or swapped for a fabricated one. -/
structure Order (R : Type u) {Stmt Wit : Type} (B : Lace) (reg : Registry Stmt Wit)
    (stmtOf : FrameStatement → Stmt) where
  /-- The order's payload — the kernel intent that clears. -/
  intent : Intent R B reg stmtOf
  /-- The declared priority key (price-time / batch rank); lower = matched first. -/
  priority : ℕ
  /-- The unique submission id. -/
  nonce : ℕ

/-- The Bool comparator the aggregator sorts by: order `a` is not-later than `b` when its declared
priority is `≤`. Total and transitive (proven inline in `aggregate_prioritized`). -/
def leOrder (a b : Order R B reg stmtOf) : Bool := a.priority ≤ b.priority

/-- **THE AGGREGATOR** — the submitted stream, sorted by declared priority. `mergeSort` is the
faithful sort: its output is a PERMUTATION of the input (no order added or lost) that is SORTED by
the comparator (priority respected). This is exactly the price-time-priority book build. -/
def aggregate (orders : List (Order R B reg stmtOf)) : List (Order R B reg stmtOf) :=
  orders.mergeSort leOrder

/-- The `Book` (rung 1's clearing input) underlying a list of orders — forget the microstructure
tags, keep the intents in stream order. Lands in exactly `Market/Clearing.lean`'s `Book`. -/
def bookOfOrders (orders : List (Order R B reg stmtOf)) : Book R B reg stmtOf :=
  orders.map (·.intent)

/-- **The aggregated book** — the `Book` the clearing consumes, built by aggregating then
projecting to intents. -/
def aggregatedBook (orders : List (Order R B reg stmtOf)) : Book R B reg stmtOf :=
  bookOfOrders (aggregate orders)

/-! ## 2. Aggregation soundness — faithful AND prioritized. -/

/-- **`AggregationSound submissions book`** — the aggregated `book` faithfully represents the
`submissions`:

  * `faithful` — `book` is a PERMUTATION of `submissions`: every submitted order appears (no
    DROP) and every book entry was submitted (no INSERT), with multiplicity (`Perm`, the
    order-stream analog of `ChainBound`'s "attests exactly the history");
  * `prioritized` — `book` is `Pairwise (· priority ≤ ·)`: sorted by declared priority, no
    REORDER (the analog of `ChainBound`'s per-adjacent-pair `Continues` tooth). -/
structure AggregationSound (submissions book : List (Order R B reg stmtOf)) : Prop where
  /-- No drop, no insert: the book is a permutation of the submissions. -/
  faithful : book ~ submissions
  /-- No reorder: the book is sorted by declared priority. -/
  prioritized : book.Pairwise (fun a b => a.priority ≤ b.priority)

/-- The aggregate is a permutation of the submissions — no drop, no insert. -/
theorem aggregate_faithful (orders : List (Order R B reg stmtOf)) :
    aggregate orders ~ orders :=
  mergeSort_perm orders leOrder

/-- The aggregate is sorted by declared priority — no reorder. -/
theorem aggregate_prioritized (orders : List (Order R B reg stmtOf)) :
    (aggregate orders).Pairwise (fun a b => a.priority ≤ b.priority) := by
  have h := pairwise_mergeSort (le := leOrder)
    (by intro a b c hab hbc; simp only [leOrder, decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [leOrder, Bool.or_eq_true, decide_eq_true_eq]; omega) orders
  exact h.imp (by intro a b hab; simpa [leOrder] using hab)

/-- **THE KEYSTONE — the aggregator is SOUND.** For any submitted stream, `aggregate` produces a
book that (a) contains EXACTLY the submitted orders (permutation: no drop, no insert) and (b)
respects the declared priority (sorted). The two faces are independent teeth (see §5). -/
theorem aggregate_sound (orders : List (Order R B reg stmtOf)) :
    AggregationSound orders (aggregate orders) :=
  ⟨aggregate_faithful orders, aggregate_prioritized orders⟩

/-! ## 3. What faithfulness gives — no drop, no insert, multiset preserved. -/

/-- **NO DROP** — every submitted order appears in a faithful book. -/
theorem no_drop {submissions book : List (Order R B reg stmtOf)}
    (H : AggregationSound submissions book) {o : Order R B reg stmtOf}
    (ho : o ∈ submissions) : o ∈ book :=
  H.faithful.mem_iff.mpr ho

/-- **NO INSERT** — every entry of a faithful book was submitted. -/
theorem no_insert {submissions book : List (Order R B reg stmtOf)}
    (H : AggregationSound submissions book) {o : Order R B reg stmtOf}
    (ho : o ∈ book) : o ∈ submissions :=
  H.faithful.mem_iff.mp ho

/-- **THE MULTISET IS PRESERVED** — a faithful book has the same number of orders and the same
nonce-multiset total as the submissions: no silent duplicate, drop, or fabricated substitution
can hide behind equal membership. (The nonce-sum is the decidable projection of the full
multiset equality that `faithful` — a `Perm` — carries.) -/
theorem faithful_preserves_count {submissions book : List (Order R B reg stmtOf)}
    (H : AggregationSound submissions book) :
    book.length = submissions.length ∧
      (book.map (·.nonce)).sum = (submissions.map (·.nonce)).sum :=
  ⟨H.faithful.length_eq, (H.faithful.map _).sum_eq⟩

/-! ## 4. Composition with rung 1 — aggregation preserves what conservation sees.

The bridge to `Market/Clearing.lean`: because the aggregated book is a permutation of the
submission book, the per-asset offered Σ is identical (a permutation-invariant sum), so a clearing
of the aggregated book conserves exactly the SUBMITTED orders' per-asset totals. Aggregation
cannot change what `clearing_conserves_per_asset` sees. -/

/-- The aggregated book is a permutation of the submission book (as `Book`s of intents) — the
projection of `aggregate_faithful` through `bookOfOrders`. -/
theorem aggregatedBook_perm (orders : List (Order R B reg stmtOf)) :
    aggregatedBook orders ~ bookOfOrders orders := by
  unfold aggregatedBook bookOfOrders
  exact (aggregate_faithful orders).map (·.intent)

/-- **The pool's underlying bundle is the ⊗-product of the members' bundles** — the multiplicative
mirror of `pool_toBal`. Lets the pool's `.as` be read off as a `List.prod` in the commutative
monoid `Bundle`, hence made permutation-invariant. -/
theorem pool_as_prod (rs : List DemoRes) : (pool rs).as = (rs.map (·.as)).prod := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    have hx : (pool (x :: xs)).as = x.as * (pool xs).as := rfl
    rw [hx, ih, List.map_cons, List.prod_cons]

/-- **The pool's bundle is PERMUTATION-INVARIANT** — reordering the members leaves `(pool rs).as`
unchanged (`Bundle` is a commutative monoid, so the ⊗-product does not depend on order). This is
what makes aggregation transparent to conservation: the sorted book and the submission book carry
the same pool bundle. -/
theorem pool_as_perm {rs rs' : List DemoRes} (h : rs ~ rs') :
    (pool rs).as = (pool rs').as := by
  rw [pool_as_prod, pool_as_prod]
  exact (h.map (·.as)).prod_eq

/-- **THE rung-2 → rung-1 COMPOSITION — a clearing of the aggregated book conserves the SUBMITTED
orders per asset.** For orders over the demo resource theory and any `MarketClearing` of the
aggregated book: the sum over the SUBMITTED orders of what they offered (in the ledger measure
`toBal`) equals the sum over the allocation. Composes `clearing_conserves_per_asset` (rung 1, over
the aggregated book) with the permutation-invariance of the Σ (`aggregatedBook_perm`) — the order
the stream arrived in is irrelevant to conservation. -/
theorem aggregated_clearing_conserves_submissions
    {orders : List (Order DemoRes B reg stmtOf)}
    (C : MarketClearing (aggregatedBook orders)) (a : AssetId) :
    ((bookOfOrders orders).map (fun i => toBal i.offered.as a)).sum
      = (C.alloc.map (fun r => toBal r.as a)).sum := by
  rw [← clearing_conserves_per_asset C a]
  exact ((aggregatedBook_perm orders).map (fun i => toBal i.offered.as a)).sum_eq.symm

/-! ## 5. NON-VACUITY, positive polarity — the ring, submitted OUT of order, aggregates clean. -/

/-- The submitted ring stream — the `crossBid`/`artSeller`/`dealer` ring of `Market/Clearing.lean`,
submitted OUT of priority order (dealer 30, crossBid 10, artSeller 20). Aggregation must reorder
it to the price-time order crossBid, artSeller, dealer. -/
def ringSubmissions :
    List (Order DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf) :=
  [ { intent := dealer,    priority := 30, nonce := 3 },
    { intent := crossBid,  priority := 10, nonce := 1 },
    { intent := artSeller, priority := 20, nonce := 2 } ]

/-- **AGGREGATION SOUNDNESS, INSTANTIATED** — the ring submissions aggregate to a faithful,
priority-sorted book. Non-vacuous: the input is out of order, so `faithful` is a genuine
non-identity permutation and `prioritized` genuinely constrains (the `#guard`s pin the reordered
priorities 10, 20, 30 and the preserved nonce multiset). -/
theorem ringSubmissions_sound : AggregationSound ringSubmissions (aggregate ringSubmissions) :=
  aggregate_sound ringSubmissions

/-- The aggregated ring book is exact — every entry's predicate is `= wanted`. Transported across
the aggregation permutation: every entry of the aggregate is one of the three ring orders, each of
which has that predicate shape (so exactness holds regardless of the sorted position). -/
theorem aggregatedRing_exact : ExactBook (aggregatedBook ringSubmissions) := by
  intro i hi r
  have hmem : (aggregatedBook ringSubmissions)[i] ∈ aggregatedBook ringSubmissions :=
    getElem_mem hi
  have hsub : (aggregatedBook ringSubmissions)[i] ∈ bookOfOrders ringSubmissions :=
    (aggregatedBook_perm ringSubmissions).mem_iff.mp hmem
  have key : ∀ x ∈ bookOfOrders ringSubmissions, x.predicate r ↔ r = x.wanted := by
    intro x hx
    simp only [bookOfOrders, ringSubmissions, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact Iff.rfl
  exact key _ hsub

/-- **AGGREGATION DELIVERS A CLEARABLE BOOK** — the aggregated ring book CLEARS. It is exact and
its offered/wanted pools balance (both carry the bundle (7 gold, 1 art), permutation-invariant
from the ring), so `exact_clears_iff` (rung 1) inhabits a `MarketClearing`. Aggregation hands the
clearing a book it can settle. -/
theorem aggregated_ring_clears : Nonempty (MarketClearing (aggregatedBook ringSubmissions)) := by
  rw [exact_clears_iff _ aggregatedRing_exact]
  have ho : (pool (offersOf (aggregatedBook ringSubmissions))).as
      = (pool (offersOf (bookOfOrders ringSubmissions))).as :=
    pool_as_perm (by unfold offersOf; exact (aggregatedBook_perm ringSubmissions).map (·.offered))
  have hw : (pool (wantsOf (aggregatedBook ringSubmissions))).as
      = (pool (wantsOf (bookOfOrders ringSubmissions))).as :=
    pool_as_perm (by unfold wantsOf; exact (aggregatedBook_perm ringSubmissions).map (·.wanted))
  rw [ho, hw]
  decide

/-! ## 6. NON-VACUITY, negative polarity — the teeth (a tampered book is refused). -/

/-- A DROPPED book — the aggregate with `crossBid`'s order removed. One fewer order than
submitted. -/
def droppedBook :
    List (Order DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf) :=
  [ { intent := artSeller, priority := 20, nonce := 2 },
    { intent := dealer,    priority := 30, nonce := 3 } ]

/-- **TOOTH (no drop): a book missing a submitted order is REFUSED.** `droppedBook` drops
`crossBid` — two orders against three submitted — so it cannot be a permutation of the
submissions: `faithful` fails on length. -/
theorem drop_refused : ¬ AggregationSound ringSubmissions droppedBook := by
  intro H
  have := H.faithful.length_eq
  simp [droppedBook, ringSubmissions] at this

/-- An INSERTED book — the aggregate with a fabricated fourth order (nonce 99, never submitted). -/
def insertedBook :
    List (Order DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf) :=
  [ { intent := crossBid,  priority := 10, nonce := 1 },
    { intent := artSeller, priority := 20, nonce := 2 },
    { intent := dealer,    priority := 30, nonce := 3 },
    { intent := dealer,    priority := 40, nonce := 99 } ]

/-- **TOOTH (no insert): a book with a fabricated order is REFUSED.** `insertedBook` adds a
never-submitted fourth order — four against three — so it cannot be a permutation of the
submissions: `faithful` fails on length. -/
theorem insert_refused : ¬ AggregationSound ringSubmissions insertedBook := by
  intro H
  have := H.faithful.length_eq
  simp [insertedBook, ringSubmissions] at this

/-- A SUBSTITUTED book — same length as the submissions, but `dealer`'s order (nonce 3) is swapped
for a fabricated order (nonce 99). Membership/length alone would not catch it; the nonce multiset
does. -/
def substitutedBook :
    List (Order DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf) :=
  [ { intent := crossBid,  priority := 10, nonce := 1 },
    { intent := artSeller, priority := 20, nonce := 2 },
    { intent := dealer,    priority := 30, nonce := 99 } ]

/-- **TOOTH (no fabricated substitution): a same-length book that swaps a submitted order for a
fabricated one is REFUSED.** `substitutedBook` replaces nonce 3 with nonce 99 — same length, but
the nonce-multiset total differs (98 vs 6), which a permutation preserves. `faithful` fails. -/
theorem substitution_refused : ¬ AggregationSound ringSubmissions substitutedBook := by
  intro H
  have := (H.faithful.map (·.nonce)).sum_eq
  simp [substitutedBook, ringSubmissions] at this

/-- A REORDERED book — a genuine permutation of the submissions (so `faithful` holds), but NOT in
priority order: dealer (30) placed before crossBid (10). -/
def reorderedBook :
    List (Order DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf) :=
  [ { intent := dealer,    priority := 30, nonce := 3 },
    { intent := crossBid,  priority := 10, nonce := 1 },
    { intent := artSeller, priority := 20, nonce := 2 } ]

/-- **TOOTH (no reorder): a priority-violating book is REFUSED — even though it is a faithful
permutation.** `reorderedBook` IS a permutation of the submissions (no drop, no insert — it is in
fact `ringSubmissions` itself), but places priority-30 `dealer` ahead of priority-10 `crossBid`,
so it is not `Pairwise (· priority ≤ ·)`: `prioritized` fails. Faithfulness and priority are
INDEPENDENT teeth — a faithful book can still violate priority. -/
theorem reorder_refused : ¬ AggregationSound ringSubmissions reorderedBook := by
  intro H
  have := H.prioritized
  simp [reorderedBook, List.pairwise_cons] at this

/-! ### `#guard` smoke — the aggregation is computed, not asserted. -/

-- submitted out of priority order (30, 10, 20):
#guard (ringSubmissions.map (·.priority)) == [30, 10, 20]
-- aggregation SORTS to priority order (10, 20, 30):
#guard ((aggregate ringSubmissions).map (·.priority)) == [10, 20, 30]
-- the nonce multiset is preserved (submitted 3,1,2 ↦ aggregated 1,2,3 — same set, reordered):
#guard ((aggregate ringSubmissions).map (·.nonce)) == [1, 2, 3]
#guard (ringSubmissions.map (·.nonce)).sum == (aggregate ringSubmissions |>.map (·.nonce)).sum
-- the aggregated book's offered pool carries the ring bundle (7 gold, 1 art) — clearable:
#guard (pool (offersOf (aggregatedBook ringSubmissions))).as.toAdd == (7, 1)
#guard (pool (wantsOf (aggregatedBook ringSubmissions))).as.toAdd == (7, 1)
-- the tampered books, by the numbers the teeth turn on:
#guard droppedBook.length == 2          -- < 3 submitted (drop)
#guard insertedBook.length == 4         -- > 3 submitted (insert)
#guard (substitutedBook.map (·.nonce)).sum == 102   -- ≠ 6 submitted (substitution)
#guard (ringSubmissions.map (·.nonce)).sum == 6

/-! ### Axiom hygiene — the aggregation keystones pinned to the three kernel axioms. -/

#assert_all_clean [Market.aggregate_faithful, Market.aggregate_prioritized, Market.aggregate_sound,
  Market.no_drop, Market.no_insert, Market.faithful_preserves_count,
  Market.aggregatedBook_perm, Market.aggregated_clearing_conserves_submissions,
  Market.ringSubmissions_sound, Market.aggregatedRing_exact, Market.aggregated_ring_clears,
  Market.drop_refused, Market.insert_refused, Market.substitution_refused, Market.reorder_refused]

end Market
