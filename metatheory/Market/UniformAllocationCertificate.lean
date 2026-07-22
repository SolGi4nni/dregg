/-
# Market.UniformAllocationCertificate — executable exact allocation authority.

`fhegg-solver::uniform_allocation_cert::verify_uniform_allocation` is the authority boundary after
an untrusted optimizer proposes a uniform clearing.  The older `Allocation.validate` predicate only
checks conservation, caps, and activity; it therefore accepts a conserving move of one unit between
two active orders.  This file gives the corresponding Lean semantic checker teeth: acceptance fixes
the price to the lowest-index volume argmax, fixes the volume, requires every inactive full-book slot
to be zero, and fixes each active side to `FhEggAllocation.ration` exactly.  Thus a long side uses the
largest remainder order (remainder descending, active-order rank ascending on ties; filtering
preserves original book-index order), rather than merely landing within a loose fairness interval.

The Rust wire carrier's `RationWitness` cutoff is deliberately absent here.  It is a compact way for
the Rust checker to validate the same exact relation; it is not part of the allocation semantics.  The
Lean checker recomputes the complete canonical relation directly.  The price-grid size `K` is an
external checker argument, never worker-selected certificate data.  Lean quantities are `Int`, so
this checker explicitly admits `OrdersValid`; Rust gets that premise from its `u64` order type.

Pure. No axioms.
-/
import Market.FhEggAllocation
import Market.FhEggRustDenotation
import Dregg2.Tactics

namespace Market.UniformAllocationCertificate

open Market
open Market.FhEggAllocation

set_option autoImplicit false

/-! ## Certificate carrier and finite executable predicates. -/

/-- The semantic fields carried by one proposed exact uniform allocation.  Unlike the Rust wire
type, naturals here are unbounded and there are no transport/work-limit fields. -/
structure Certificate where
  clearingPrice : Nat
  clearedVolume : Nat
  /-- One fill per source order, in original book order. -/
  fills : List Nat
  deriving DecidableEq, Repr

/-- Whether an order participates at the proposed uniform price. -/
def ActiveAt (price : Nat) (o : LimitOrder) : Prop :=
  match o.side with
  | Side.bid => price ≤ o.limit
  | Side.ask => o.limit ≤ price

instance (price : Nat) (o : LimitOrder) : Decidable (ActiveAt price o) := by
  unfold ActiveAt
  cases o.side <;> infer_instance

/-- Whether `o` participates on the named side. -/
def ActiveOn (side : Side) (price : Nat) (o : LimitOrder) : Prop :=
  o.side = side ∧ ActiveAt price o

instance (side : Side) (price : Nat) (o : LimitOrder) : Decidable (ActiveOn side price o) :=
  by
    by_cases hside : o.side = side
    · by_cases hactive : ActiveAt price o
      · exact isTrue ⟨hside, hactive⟩
      · exact isFalse (fun h => hactive h.2)
    · exact isFalse (fun h => hside h.1)

/-- Select fills for active orders on one side, preserving original book order.  A shape mismatch
returns the empty tail; the checker separately requires exact full-book shape. -/
def activeSideFills (side : Side) (price : Nat) : OrderBook → List Nat → List Nat
  | o :: orders, fill :: fills =>
      if ActiveOn side price o then
        fill :: activeSideFills side price orders fills
      else
        activeSideFills side price orders fills
  | _, _ => []

/-- A shape-sensitive recursive inactivity predicate.  On matching lists it says exactly that each
order inactive at `price` has fill zero; mismatched lists are rejected. -/
def InactiveZero (price : Nat) : OrderBook → List Nat → Prop
  | [], [] => True
  | o :: orders, fill :: fills =>
      (ActiveAt price o ∨ fill = 0) ∧ InactiveZero price orders fills
  | _, _ => False

instance (price : Nat) (orders : OrderBook) (fills : List Nat) :
    Decidable (InactiveZero price orders fills) := by
  induction orders generalizing fills with
  | nil =>
      cases fills with
      | nil => exact isTrue trivial
      | cons _ _ => exact isFalse (by simp [InactiveZero])
  | cons o orders ih =>
      cases fills with
      | nil => exact isFalse (by simp [InactiveZero])
      | cons fill fills =>
          change Decidable ((ActiveAt price o ∨ fill = 0) ∧ InactiveZero price orders fills)
          infer_instance

/-- Executable admission of the `Int`-modeled book.  Rust's `u64` source type makes this check
structural; Lean must state it. -/
def ordersValidCheck (book : OrderBook) : Bool :=
  book.all fun o => decide (0 ≤ o.qty)

theorem ordersValidCheck_eq_true_iff (book : OrderBook) :
    ordersValidCheck book = true ↔ OrdersValid book := by
  simp [ordersValidCheck, OrdersValid]

/-- The executable authority check.  It does not trust a finder or the weaker allocation validator:
all semantic fields and both complete active-side vectors are recomputed. -/
def check (book : OrderBook) (priceLevels : Nat) (cert : Certificate) : Bool :=
  decide (0 < priceLevels) &&
  ordersValidCheck book &&
  decide (cert.fills.length = book.length) &&
  decide (cert.clearingPrice = crossing book priceLevels) &&
  decide (cert.clearedVolume = (clearedVolume book priceLevels).toNat) &&
  decide (InactiveZero cert.clearingPrice book cert.fills) &&
  decide (activeSideFills Side.bid cert.clearingPrice book cert.fills =
    ration (activeBidQtys book cert.clearingPrice) cert.clearedVolume) &&
  decide (activeSideFills Side.ask cert.clearingPrice book cert.fills =
    ration (activeAskQtys book cert.clearingPrice) cert.clearedVolume)

/-! ## Semantic lemmas used by checker soundness. -/

/-- Earlier buckets are strictly worse than the selected `argmaxUpto`, which is the content of the
lowest-index tie convention (not merely maximality). -/
theorem argmaxUpto_strict_before (book : OrderBook) :
    ∀ n q, q < argmaxUpto book n → execVol book q < execVol book (argmaxUpto book n) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simp [argmaxUpto] at hq
  | succ n ih =>
      intro q hq
      by_cases h : execVol book (argmaxUpto book n) < execVol book (n + 1)
      · have harg : argmaxUpto book (n + 1) = n + 1 := by
          simp [argmaxUpto, h]
        rw [harg] at hq ⊢
        exact lt_of_le_of_lt (argmaxUpto_max book n q (by omega)) h
      · have harg : argmaxUpto book (n + 1) = argmaxUpto book n := by
          simp [argmaxUpto, h]
        rw [harg] at hq ⊢
        exact ih q hq

theorem crossing_strict_before (book : OrderBook) (K q : Nat)
    (hq : q < crossing book K) :
    execVol book q < clearedVolume book K := by
  exact argmaxUpto_strict_before book (K - 1) q hq

/-- The recursive inactivity predicate has the promised per-index meaning. -/
theorem inactiveZero_getD {price : Nat} {book : OrderBook} {fills : List Nat}
    (hzero : InactiveZero price book fills) :
    ∀ i, i < book.length → ¬ ActiveAt price (book.getD i ⟨Side.bid, 0, 0⟩) →
      fills.getD i 0 = 0 := by
  induction book generalizing fills with
  | nil => simp
  | cons o book ih =>
      cases fills with
      | nil => simp [InactiveZero] at hzero
      | cons fill fills =>
          rcases hzero with ⟨hhead, htail⟩
          intro i hi hinactive
          cases i with
          | zero =>
              simp only [List.getD_cons_zero] at hinactive ⊢
              exact hhead.resolve_left hinactive
          | succ i =>
              simp only [List.getD_cons_succ] at hinactive ⊢
              exact ih htail i (by simp at hi; omega) hinactive

/-! ## Checker soundness. -/

/-- **Exact checker soundness.** Acceptance materially yields the public optimization result, the
full-book inactivity guarantee, and exact active-side allocations.  In particular:

* every bucket has volume at most `clearedVolume`;
* every lower bucket is strictly worse, hence equal-volume ties cannot displace the lowest index;
* every inactive full-book slot is zero;
* active bids and asks equal the exact `ration` vectors; and
* each side sums exactly to the cleared volume.

The two exact-vector equalities are stronger than the older one-unit fairness interval: because
`ration` uses `bonusIdxs`/`remOrder`, they fix the largest-remainder winners and index tie-break. -/
theorem check_sound {book : OrderBook} {priceLevels : Nat} {cert : Certificate}
    (hcheck : check book priceLevels cert = true) :
    0 < priceLevels ∧
    OrdersValid book ∧
    cert.fills.length = book.length ∧
    cert.clearingPrice < priceLevels ∧
    cert.clearedVolume = (clearedVolume book priceLevels).toNat ∧
    (∀ q < priceLevels, execVol book q ≤ (cert.clearedVolume : Int)) ∧
    (∀ q < cert.clearingPrice, execVol book q < (cert.clearedVolume : Int)) ∧
    (∀ i, i < book.length →
      ¬ ActiveAt cert.clearingPrice (book.getD i ⟨Side.bid, 0, 0⟩) →
      cert.fills.getD i 0 = 0) ∧
    activeSideFills Side.bid cert.clearingPrice book cert.fills =
      ration (activeBidQtys book cert.clearingPrice) cert.clearedVolume ∧
    activeSideFills Side.ask cert.clearingPrice book cert.fills =
      ration (activeAskQtys book cert.clearingPrice) cert.clearedVolume ∧
    (activeSideFills Side.bid cert.clearingPrice book cert.fills).sum = cert.clearedVolume ∧
    (activeSideFills Side.ask cert.clearingPrice book cert.fills).sum = cert.clearedVolume := by
  simp only [check, Bool.and_eq_true] at hcheck
  have hK' := hcheck.1.1.1.1.1.1.1
  have hvalid' := hcheck.1.1.1.1.1.1.2
  have hlen' := hcheck.1.1.1.1.1.2
  have hprice' := hcheck.1.1.1.1.2
  have hvolume' := hcheck.1.1.1.2
  have hzero' := hcheck.1.1.2
  have hbid' := hcheck.1.2
  have hask' := hcheck.2
  have hK : 0 < priceLevels := of_decide_eq_true hK'
  have hvalid : OrdersValid book :=
    (ordersValidCheck_eq_true_iff book).mp hvalid'
  have hlen : cert.fills.length = book.length := of_decide_eq_true hlen'
  have hprice : cert.clearingPrice = crossing book priceLevels :=
    of_decide_eq_true hprice'
  have hvolume : cert.clearedVolume = (clearedVolume book priceLevels).toNat :=
    of_decide_eq_true hvolume'
  have hzero : InactiveZero cert.clearingPrice book cert.fills :=
    of_decide_eq_true hzero'
  have hbid : activeSideFills Side.bid cert.clearingPrice book cert.fills =
      ration (activeBidQtys book cert.clearingPrice) cert.clearedVolume :=
    of_decide_eq_true hbid'
  have hask : activeSideFills Side.ask cert.clearingPrice book cert.fills =
      ration (activeAskQtys book cert.clearingPrice) cert.clearedVolume :=
    of_decide_eq_true hask'
  have hpRange : cert.clearingPrice < priceLevels := by
    rw [hprice]
    exact crossing_lt book hK
  have hvolumeInt : (cert.clearedVolume : Int) = clearedVolume book priceLevels := by
    rw [hvolume]
    exact Int.toNat_of_nonneg
      (Market.MpcClearingSecurity.clearedVolume_nonneg hvalid _)
  have hmax : ∀ q < priceLevels,
      execVol book q ≤ (cert.clearedVolume : Int) := by
    intro q hq
    rw [hvolumeInt]
    exact clearedVolume_optimal book priceLevels hq
  have hlowest : ∀ q < cert.clearingPrice,
      execVol book q < (cert.clearedVolume : Int) := by
    intro q hq
    rw [hprice] at hq
    rw [hvolumeInt]
    exact crossing_strict_before book priceLevels q hq
  have hinactive := inactiveZero_getD hzero
  have hbidSum :
      (activeSideFills Side.bid cert.clearingPrice book cert.fills).sum =
        cert.clearedVolume := by
    calc
      (activeSideFills Side.bid cert.clearingPrice book cert.fills).sum =
          (ration (activeBidQtys book cert.clearingPrice) cert.clearedVolume).sum :=
        congrArg List.sum hbid
      _ = cert.clearedVolume := by
        simpa [hprice, hvolume, buyFills] using buyFills_sum book priceLevels hvalid
  have haskSum :
      (activeSideFills Side.ask cert.clearingPrice book cert.fills).sum =
        cert.clearedVolume := by
    calc
      (activeSideFills Side.ask cert.clearingPrice book cert.fills).sum =
          (ration (activeAskQtys book cert.clearingPrice) cert.clearedVolume).sum :=
        congrArg List.sum hask
      _ = cert.clearedVolume := by
        simpa [hprice, hvolume, sellFills] using sellFills_sum book priceLevels hvalid
  exact ⟨hK, hvalid, hlen, hpRange, hvolume, hmax, hlowest, hinactive,
    hbid, hask, hbidSum, haskSum⟩

/-- On a rationed bid side, accepted active fills are literally floor share plus the one-bit award to
the largest-remainder winners. -/
theorem accepted_bid_long_side_exact {book : OrderBook} {priceLevels : Nat} {cert : Certificate}
    (hcheck : check book priceLevels cert = true)
    (hlong : cert.clearedVolume < (activeBidQtys book cert.clearingPrice).sum)
    (i : Nat) (hi : i < (activeBidQtys book cert.clearingPrice).length) :
    (activeSideFills Side.bid cert.clearingPrice book cert.fills).getD i 0 =
      (activeBidQtys book cert.clearingPrice).getD i 0 * cert.clearedVolume /
          (activeBidQtys book cert.clearingPrice).sum +
        (if i ∈ bonusIdxs (activeBidQtys book cert.clearingPrice) cert.clearedVolume then 1 else 0) := by
  have h := check_sound hcheck
  rw [h.2.2.2.2.2.2.2.2.1]
  exact ration_getD _ _ hlong i hi

/-- Ask-side counterpart of `accepted_bid_long_side_exact`. -/
theorem accepted_ask_long_side_exact {book : OrderBook} {priceLevels : Nat} {cert : Certificate}
    (hcheck : check book priceLevels cert = true)
    (hlong : cert.clearedVolume < (activeAskQtys book cert.clearingPrice).sum)
    (i : Nat) (hi : i < (activeAskQtys book cert.clearingPrice).length) :
    (activeSideFills Side.ask cert.clearingPrice book cert.fills).getD i 0 =
      (activeAskQtys book cert.clearingPrice).getD i 0 * cert.clearedVolume /
          (activeAskQtys book cert.clearingPrice).sum +
        (if i ∈ bonusIdxs (activeAskQtys book cert.clearingPrice) cert.clearedVolume then 1 else 0) := by
  have h := check_sound hcheck
  rw [h.2.2.2.2.2.2.2.2.2.1]
  exact ration_getD _ _ hlong i hi

/-- On a strictly positive-quantity book, every accepted active-bid fill is capped by that active
order's quantity.  (The full-book checker separately proves every inactive slot is zero.) -/
theorem accepted_bid_active_cap {book : OrderBook} {priceLevels : Nat} {cert : Certificate}
    (hcheck : check book priceLevels cert = true)
    (hpositive : ∀ o ∈ book, 0 < o.qty) (i : Nat) :
    (activeSideFills Side.bid cert.clearingPrice book cert.fills).getD i 0 ≤
      (activeBidQtys book cert.clearingPrice).getD i 0 := by
  have h := check_sound hcheck
  rw [h.2.2.2.2.2.2.2.2.1]
  exact ration_getD_le _ _ (activeBidQtys_pos book hpositive _) i

/-- Ask-side active-order cap. -/
theorem accepted_ask_active_cap {book : OrderBook} {priceLevels : Nat} {cert : Certificate}
    (hcheck : check book priceLevels cert = true)
    (hpositive : ∀ o ∈ book, 0 < o.qty) (i : Nat) :
    (activeSideFills Side.ask cert.clearingPrice book cert.fills).getD i 0 ≤
      (activeAskQtys book cert.clearingPrice).getD i 0 := by
  have h := check_sound hcheck
  rw [h.2.2.2.2.2.2.2.2.2.1]
  exact ration_getD_le _ _ (activeAskQtys_pos book hpositive _) i

/-! ## Executable positive and adversarial teeth. -/

def workCertificate : Certificate :=
  ⟨1, 8, [5, 3, 3, 5]⟩

#guard check workBook 3 workCertificate
-- The worker cannot reinterpret this result over a one-bucket grid: `K` comes from the caller.
#guard !check workBook 1 workCertificate

/-- The workbook attack accepted by conservation/caps/activity alone: move one unit from active bid
1 to active bid 0.  Both side sums remain eight, but the exact checker refuses `[6,2] ≠ [5,3]`. -/
def workMovedUnitAttack : Certificate :=
  ⟨1, 8, [6, 2, 3, 5]⟩

#guard workMovedUnitAttack.fills.sum == workCertificate.fills.sum
#guard (activeSideFills Side.bid 1 workBook workMovedUnitAttack.fills).sum == 8
#guard (activeSideFills Side.ask 1 workBook workMovedUnitAttack.fills).sum == 8
#guard !check workBook 3 workMovedUnitAttack

/-- At the counter-book clearing price, bid index 1 is inactive.  Moving one unit into that slot keeps
the full bid-order fill total at nine but lowers the active-side total, and is refused. -/
def counterCertificate : Certificate :=
  ⟨1, 9, [9, 0, 2, 7]⟩

def counterInactiveAttack : Certificate :=
  ⟨1, 9, [8, 1, 2, 7]⟩

#guard check counterBook 2 counterCertificate
#guard (activeSideFills Side.bid 1 counterBook counterInactiveAttack.fills).sum == 8
#guard !check counterBook 2 counterInactiveAttack

/-- Equal remainders award the final unit to the lower original active-order index. -/
def remainderTieBook : OrderBook :=
  [⟨Side.bid, 1, 0⟩, ⟨Side.bid, 1, 0⟩, ⟨Side.bid, 1, 0⟩, ⟨Side.ask, 2, 0⟩]

def remainderTieCertificate : Certificate :=
  ⟨0, 2, [1, 1, 0, 2]⟩

def remainderLaterIndexAttack : Certificate :=
  ⟨0, 2, [1, 0, 1, 2]⟩

#guard check remainderTieBook 1 remainderTieCertificate
#guard !check remainderTieBook 1 remainderLaterIndexAttack

/-- Both price buckets execute one unit, so the lowest-price tie convention fixes bucket zero. -/
def priceTieBook : OrderBook := [⟨Side.bid, 1, 1⟩, ⟨Side.ask, 1, 0⟩]
def priceTieCertificate : Certificate := ⟨0, 1, [1, 1]⟩
def laterPriceAttack : Certificate := ⟨1, 1, [1, 1]⟩

#guard execVol priceTieBook 0 == execVol priceTieBook 1
#guard check priceTieBook 2 priceTieCertificate
#guard !check priceTieBook 2 laterPriceAttack

/-! ### Kernel hygiene. -/

#assert_all_clean [Market.UniformAllocationCertificate.argmaxUpto_strict_before,
  Market.UniformAllocationCertificate.crossing_strict_before,
  Market.UniformAllocationCertificate.inactiveZero_getD,
  Market.UniformAllocationCertificate.check_sound,
  Market.UniformAllocationCertificate.accepted_bid_long_side_exact,
  Market.UniformAllocationCertificate.accepted_ask_long_side_exact,
  Market.UniformAllocationCertificate.accepted_bid_active_cap,
  Market.UniformAllocationCertificate.accepted_ask_active_cap]

end Market.UniformAllocationCertificate
