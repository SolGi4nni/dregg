/-
# Market.GraduationPool — the LAUNCHPAD GRADUATION tie: the on-chain solvent pool ↔ `pool_solvent_forever`.

When a fair-launch raise clears (`chain/contracts/launchpad/DreggLaunchpad.sol`: commit → reveal →
uniform-price clear → settle), the token GRADUATES into a standing liquid market — a
`DreggSolventPool` seeded with a DISCLOSED fraction of the raise proceeds (the quote reserve) and a
reserved token allocation (the token reserve). Unlike a pump.fun bonding curve (drainable) or a
Raydium pool (no solvency theorem), the graduated pool is the DrEX **rung-6** never-insolvent pool of
`Market/Liquidity.lean`: a trade that would drive a reserve below its disclosed floor REVERTS
(`DreggSolventPool.PoolFloorBreached`).

This file is the **tie**: the on-chain floor guard `require(reserveOut - output ≥ floor)` is exactly a
`PoolFillValidFloor` discipline, and — because the floor is nonnegative — it REFINES rung-6's
`PoolFillValid`, so the deployed pool realizes `pool_solvent_forever` (`Market/Liquidity.lean:145`,
REUSED here, not re-proved). rung-6's guarantee is the **floor-0 special case** (never negative); the
launchpad graduates with a positive disclosed floor and this file proves the reserve stays **at or
above that floor forever**, which is strictly stronger and implies solvency.

Honest scope: this proves the **floor discipline realizes the solvency keystone** (both polarities: a
floor-respecting schedule stays above floor forever + stays solvent; a floor-breaching fill is REFUSED
and provably drives a reserve below the floor). The on-chain constant-product `x·y=k` PRICING is BUILT
in `DreggSolventPool.sol` (a swap keeps `x·y` non-decreasing under the fee); it is the pricing policy
ABOVE this solvency floor — the load-bearing guarantee tied here is the never-insolvent floor, exactly
as `Market/Liquidity.lean` frames it.
-/
import Market.Liquidity

namespace Market

open Dregg2.Exec (AssetId)

/-! ## 1. The disclosed reserve FLOOR — the graduation pool's `PoolFloorBreached` guard. -/

/-- A per-asset reserve **floor**: the disclosed minimum each reserve may never drop below. The
on-chain `DreggSolventPool` sets `floorQuote`/`floorToken` at graduation (a disclosed fraction of the
seed) and reverts any swap whose output would push a reserve under it. rung-6's `pool_solvent_forever`
is the `floor = 0` case (never negative). -/
abbrev Floor := AssetId → ℚ

/-- A floor is **well-formed** when it is nonnegative — you cannot disclose a "negative reserve floor".
This is what makes the floor discipline REFINE (strengthen) rung-6's never-negative guarantee. -/
def Floor.wf (fl : Floor) : Prop := ∀ a, 0 ≤ fl a

/-- The pool is **above its floor** when every per-asset reserve is ≥ the disclosed floor. With
`fl = 0` this is exactly `Pool.solvent`. -/
def Pool.aboveFloor (fl : Floor) (p : Pool) : Prop := ∀ a, fl a ≤ p a

/-- With a well-formed (nonnegative) floor, being above the floor IMPLIES solvent — the floor
discipline is a strengthening of never-negative. -/
theorem aboveFloor_solvent (fl : Floor) (hfl : Floor.wf fl) {p : Pool}
    (h : Pool.aboveFloor fl p) : Pool.solvent p :=
  fun a => le_trans (hfl a) (h a)

/-! ## 2. The on-chain swap discipline — `PoolFillValidFloor` = `require(reserveOut - out ≥ floor)`. -/

/-- **A fill is FLOOR-VALID** against a pool when it respects the order terms (`FillValid`, rung 5) AND
leaves the paid-out reserve at or above the floor: `filledOut ≤ reserve − floor`. This is EXACTLY the
`DreggSolventPool` swap guard `require(reserveOut - output ≥ floor)` — the `PoolFloorBreached` refusal.
With `floor = 0` it is rung-6's `PoolFillValid` (`filledOut ≤ reserve`). -/
def PoolFillValidFloor (fl : Floor) (p : Pool) (f : Fill) : Prop :=
  FillValid f ∧ f.filledOut ≤ p f.order.wantAsset - fl f.order.wantAsset

/-- **THE REFINEMENT (the tie):** a floor-valid fill against a well-formed (nonnegative) floor is a
`PoolFillValid` fill — the on-chain floor guard REFINES rung-6's solvency discipline. Everything the
deployed pool admits, rung-6 admits; so rung-6's keystone governs the deployed pool. -/
theorem poolFillValidFloor_refines
    (fl : Floor) (hfl : Floor.wf fl) {p : Pool} {f : Fill}
    (h : PoolFillValidFloor fl p f) : PoolFillValid p f := by
  obtain ⟨hv, hle⟩ := h
  refine ⟨hv, ?_⟩
  have := hfl f.order.wantAsset
  linarith

/-! ## 3. The floor invariant STEP — a floor-valid fill leaves the pool above the floor. -/

/-- **`poolStep_aboveFloor`:** clearing a floor-valid fill against an above-floor pool leaves it
above the floor. The pool gains the offered asset (grows) and pays the wanted asset only down to the
floor (`filledOut ≤ reserve − floor`). This is the single-step core the graduation invariant folds —
the exact analogue of `poolStep_solvent`, one floor per asset. -/
theorem poolStep_aboveFloor (fl : Floor) {p : Pool} {f : Fill}
    (hp : Pool.aboveFloor fl p) (hf : PoolFillValidFloor fl p f) :
    Pool.aboveFloor fl (poolStep p f) := by
  intro a
  obtain ⟨hfill, hdraw⟩ := hf
  have hin : 0 ≤ f.filledIn := hfill.1
  have hout : 0 ≤ f.filledOut := Fill.filledOut_nonneg hfill
  have hpa : fl a ≤ p a := hp a
  simp only [poolStep, poolDelta]
  by_cases hw : f.order.wantAsset = a
  · rw [hw] at hdraw
    by_cases ho : f.order.offerAsset = a
    · rw [if_pos ho, if_pos hw]; linarith
    · rw [if_neg ho, if_pos hw]; linarith
  · by_cases ho : f.order.offerAsset = a
    · rw [if_pos ho, if_neg hw]; linarith
    · rw [if_neg ho, if_neg hw]; linarith

/-! ## 4. THE GRADUATION KEYSTONE — above the floor forever, hence solvent forever. -/

/-- A schedule is **floor-valid** for a starting pool when every fill respects the floor at the state
it actually hits — the on-chain guard, on every trade, forever. -/
def FloorScheduleValid (fl : Floor) (p₀ : Pool) (s : PoolSched) : Prop :=
  ∀ n, PoolFillValidFloor fl (poolTraj p₀ s n) (s n)

/-- **`pool_above_floor_forever`:** starting above the floor, under any floor-valid schedule, the pool
is above the floor at EVERY reachable state — the `DreggSolventPool` reserve never drops below its
disclosed floor along any stream of trades. The fold of `poolStep_aboveFloor`. -/
theorem pool_above_floor_forever (fl : Floor) (p₀ : Pool)
    (hinit : Pool.aboveFloor fl p₀) (s : PoolSched) (hs : FloorScheduleValid fl p₀ s) :
    ∀ n, Pool.aboveFloor fl (poolTraj p₀ s n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih => exact poolStep_aboveFloor fl ih (hs k)

/-- **`graduated_pool_solvent_forever` (THE TIE):** the graduated pool — governed by the on-chain floor
guard (`FloorScheduleValid`, a well-formed floor) — is SOLVENT at every reachable state, by rung-6's
`pool_solvent_forever` REUSED. The deployed `DreggSolventPool.PoolFloorBreached` refusal is exactly the
hypothesis that discharges the keystone: what the pool admits refines `PoolFillValid`, so the pool can
never be driven insolvent. This is the launchpad graduation realizing `Market/Liquidity.lean`. -/
theorem graduated_pool_solvent_forever
    (fl : Floor) (hfl : Floor.wf fl) (p₀ : Pool) (hinit : Pool.solvent p₀)
    (s : PoolSched) (hs : FloorScheduleValid fl p₀ s) :
    ∀ n, Pool.solvent (poolTraj p₀ s n) :=
  pool_solvent_forever p₀ hinit s (fun n => poolFillValidFloor_refines fl hfl (hs n))

/-! ## 5. Non-vacuity, polarity ⊕ — a disclosed floor, a real trade stream stays above it + solvent.

We reuse `Market/Liquidity.lean`'s `demoPool` (gold 100, art 100) and `demoSched` (draw 5 art, draw
40 gold, then idle: reserves stabilize at gold 70, art 115). The graduation discloses a floor of 20
per asset — every reachable reserve (min gold 70, min art 95) stays above it. -/

/-- The graduated pool's disclosed floor: 20 of each asset (a positive fraction of the seed). -/
def gradFloor : Floor := fun a => if a = 0 then (20 : ℚ) else if a = 1 then 20 else 0

theorem gradFloor_wf : Floor.wf gradFloor := by
  intro a; simp only [gradFloor]; split_ifs <;> norm_num

/-- The demo pool (gold 100, art 100) is above the disclosed floor at graduation. -/
theorem demoPool_aboveFloor : Pool.aboveFloor gradFloor demoPool := by
  intro a; simp only [gradFloor, demoPool]; split_ifs <;> norm_num

/-- The demo trade stream respects the floor at every state (min reserves 70/95 ≥ floor 20; each
draw pays out well within `reserve − floor`). The on-chain guard would admit every one of these. -/
theorem demoSched_floorValid : FloorScheduleValid gradFloor demoPool demoSched := by
  intro n
  rcases n with _ | _ | k
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoSched, poolTraj, rfill0, o0, Fill.filledOut, demoPool, gradFloor]
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoSched, poolTraj, poolStep, poolDelta, rfill0, rfill1, oR1, o0,
        Fill.filledOut, demoPool, gradFloor]
  · rw [show demoSched (k + 2) = noopFill from rfl, demoTraj_stable k]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [noopFill, noopOrder, Fill.filledOut, poolTraj, poolStep, poolDelta,
        demoSched, rfill0, rfill1, oR1, o0, demoPool, gradFloor]

/-- **The graduation invariant fires on a real stream (polarity TRUE):** the graduated pool stays
above its disclosed floor at every state — `pool_above_floor_forever` instantiated. -/
theorem demo_above_floor_forever :
    ∀ n, Pool.aboveFloor gradFloor (poolTraj demoPool demoSched n) :=
  pool_above_floor_forever gradFloor demoPool demoPool_aboveFloor demoSched demoSched_floorValid

/-- **…and therefore SOLVENT forever (the tie fires):** the graduated pool realizes rung-6's
`pool_solvent_forever` under the floor discipline. -/
theorem demo_graduated_solvent_forever :
    ∀ n, Pool.solvent (poolTraj demoPool demoSched n) :=
  graduated_pool_solvent_forever gradFloor gradFloor_wf demoPool demoPool_solvent
    demoSched demoSched_floorValid

/-! ## 6. Non-vacuity, polarity FALSE — the tooth: a floor-breaching trade is REFUSED. -/

/-- A pool holding only 25 art (asset 1), with the disclosed floor of 20. -/
def floorDrainPool : Pool := fun a => if a = 1 then (25 : ℚ) else 100

/-- A trade wanting 10 art out — which would leave 15 < the disclosed floor 20. -/
def floorDrawFill : Fill := { orderId := 0, order := o0, filledIn := 20, execPrice := 1 / 2 }

/-- **`floor_breach_refused` (TOOTH):** a trade that would push a reserve below the disclosed floor is
NOT `PoolFillValidFloor` — it never reaches settlement. This is the `DreggSolventPool.PoolFloorBreached`
revert as a Lean refusal: the graduated pool cannot be drained below its floor because such a fill is
not admissible. -/
theorem floor_breach_refused : ¬ PoolFillValidFloor gradFloor floorDrainPool floorDrawFill := by
  rintro ⟨_, hd⟩
  simp only [floorDrawFill, o0, Fill.filledOut, floorDrainPool, gradFloor] at hd
  norm_num at hd

/-- **`floor_breach_drives_below` (TOOTH, the other face):** and were such a trade applied anyway, it
provably drives the reserve below the disclosed floor — the floor guard is exactly what forbids it. -/
theorem floor_breach_drives_below : (poolStep floorDrainPool floorDrawFill) 1 < gradFloor 1 := by
  simp only [poolStep, poolDelta, floorDrawFill, o0, Fill.filledOut, floorDrainPool, gradFloor]
  norm_num

/-! ## 7. Axiom hygiene — the graduation keystones self-guard against an axiom leak. -/

#assert_axioms graduated_pool_solvent_forever
#assert_axioms pool_above_floor_forever
#assert_axioms poolFillValidFloor_refines

end Market
