/-
# `Dregg2.Circuit.CrossCellConserveRefine` — the REFINEMENT of the runtime conservation DECISION
against the COMMITTED cross-cell `Σδ = 0` AIR (House Law #1).

`CrossCellConserveDecision.conservesFFI` is the `@[export]`-ed decision the deployed executor CALLS.
This module proves it is not a re-authored peer of the AIR the prover commits to, but its faithful
runtime image: the decision's per-asset boundary `Σδ = 0` is **exactly** the committed AIR's
`creditSum = debitSum` (`balance[last] == 0`) boundary — the SAME quantity
`CrossCellConservation.ccc_conserves` proves for every satisfying trace.

## The teeth (all machine-checked below, `#assert_axioms`-clean, NO `sorry`)

* `balanceList_deltasOfTrace` — the decision's `sumInts` over a trace's realized signed deltas
  (`ccv i − dcv i` per row) EQUALS the committed `creditSum t (len−1) − debitSum t (len−1)`. This is
  the definitional bridge between the runtime decision and the committed accumulators — it reads the
  ACTUAL `creditSum`/`debitSum` from `CrossCellConservation`, not a copy.
* `decision_conserves_iff_air_boundary` — **THE REFINEMENT IFF**: the decision ADMITS a trace's
  realized deltas IFF the committed AIR's credit/debit boundary balances
  (`creditSum t (len−1) = debitSum t (len−1)`). Both directions; no vacuous premise.
* `satisfied_imp_decision_conserves` — **the soundness corollary**, instantiating the committed
  `ccc_conserves`: every trace the AIR ACCEPTS, the runtime decision ADMITS. So routing the executor
  through `conservesFFI` can never disagree with the proof the prover commits to.
* `conservesRows_iff` — the multi-asset export decomposes into the per-asset boundary conjunction
  (one boundary per asset, exactly `BlockConservation`'s "one per-asset AIR run per asset").
* `psum_forgery_refused` — the `p`-sum forgery (`ccc_psum_forgery_unsat`'s witness) is REFUSED by the
  decision over ℤ.
-/
import Dregg2.Circuit.CrossCellConservation
import Dregg2.Circuit.CrossCellConserveDecision

namespace Dregg2.Circuit.CrossCellConserveRefine

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt EffectVmDescriptor2 Satisfied2)
open Dregg2.Circuit.CrossCellConservation
  (ccv dcv creditSum debitSum crossCellConservationDescriptor ccc_conserves)
open Dregg2.Circuit.CrossCellConserveDecision
  (sumInts conservesSingle conservesRows firstImbalanced keysAsc sumForAsset)

set_option autoImplicit false

/-! ## §1 — the trace's realized signed deltas (`ccv − dcv` per row). -/

/-- The signed cross-cell delta the trace realizes at row `i`: its credit contribution minus its debit
contribution, exactly the `(NET_DELTA_MAG, NET_DELTA_SIGN)` the off-AIR verifier fills `ccv`/`dcv`
from. -/
def deltaAt (t : VmTrace) (i : Nat) : Int := ccv t i - dcv t i

/-- The list of signed deltas over the trace's data rows `[0, len−1)` (row `len−1` is the inert wrap
row the AIR pins to zero, so it contributes nothing). -/
def deltasOfTrace (t : VmTrace) : List Int :=
  (List.range (t.rows.length - 1)).map (deltaAt t)

/-! ## §2 — `sumInts` is an additive fold (elementary). -/

theorem sumInts_append (a b : List Int) : sumInts (a ++ b) = sumInts a + sumInts b := by
  induction a with
  | nil => simp [sumInts]
  | cons x xs ih => simp [sumInts, ih]; ring

/-! ## §3 — the definitional bridge: the decision's balance = the committed AIR's `creditSum − debitSum`. -/

/-- The prefix identity: `sumInts` of the realized deltas over `[0, n)` equals the committed
accumulator reconstruction `creditSum t n − debitSum t n` (both are prefix sums; `deltaAt = ccv − dcv`
and `creditSum`/`debitSum` fold `ccv`/`dcv`). -/
theorem balance_prefix (t : VmTrace) (n : Nat) :
    sumInts ((List.range n).map (deltaAt t)) = creditSum t n - debitSum t n := by
  induction n with
  | zero => simp [sumInts, creditSum, debitSum]
  | succ n ih =>
    rw [List.range_succ, List.map_append, sumInts_append, ih]
    simp only [List.map_cons, List.map_nil, sumInts, deltaAt, creditSum, debitSum]
    ring

/-- **The definitional bridge.** The decision's `sumInts` over the trace's realized deltas EQUALS the
committed AIR's `creditSum t (len−1) − debitSum t (len−1)`. -/
theorem balanceList_deltasOfTrace (t : VmTrace) :
    sumInts (deltasOfTrace t)
      = creditSum t (t.rows.length - 1) - debitSum t (t.rows.length - 1) :=
  balance_prefix t (t.rows.length - 1)

/-! ## §4 — the decision's single-asset spec. -/

theorem conservesSingle_iff (ds : List Int) : conservesSingle ds = true ↔ sumInts ds = 0 := by
  unfold conservesSingle
  exact beq_iff_eq

/-! ## §5 — THE REFINEMENT IFF (decision output ⟺ committed AIR boundary). -/

/-- **THE REFINEMENT.** The runtime decision ADMITS a trace's realized deltas IFF the committed AIR's
credit/debit accumulator boundary balances — i.e. iff `creditSum t (len−1) = debitSum t (len−1)`, the
`balance[last] == 0` the AIR pins. The decision is thus the faithful runtime image of the committed
boundary, not a re-authored peer: both sides reduce to the SAME `creditSum − debitSum`. -/
theorem decision_conserves_iff_air_boundary (t : VmTrace) :
    conservesSingle (deltasOfTrace t) = true
      ↔ creditSum t (t.rows.length - 1) = debitSum t (t.rows.length - 1) := by
  rw [conservesSingle_iff, balanceList_deltasOfTrace]
  omega

/-- **The soundness corollary** — the committed `ccc_conserves` instantiated at the runtime decision:
every trace the AIR ACCEPTS (satisfies `crossCellConservationDescriptor`), the runtime decision ADMITS.
Routing the executor's conservation gate through `conservesFFI` therefore never disagrees with the
proof the prover commits to. -/
theorem satisfied_imp_decision_conserves
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash crossCellConservationDescriptor minit mfin maddrs t)
    (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (hlen : 2 ≤ t.rows.length) :
    conservesSingle (deltasOfTrace t) = true :=
  (decision_conserves_iff_air_boundary t).mpr (ccc_conserves hsat hcanon hlen)

/-! ## §6 — the multi-asset export decomposes into the per-asset boundary conjunction. -/

/-- `findSome?` is `none` on the whole list iff the probe is `none` at every element. -/
theorem findSome?_isNone_iff {α β : Type} (l : List α) (g : α → Option β) :
    (l.findSome? g).isNone = true ↔ ∀ a ∈ l, g a = none := by
  rw [Option.isNone_iff_eq_none, List.findSome?_eq_none_iff]

/-- **The multi-asset decision decomposes into per-asset boundaries.** The export ADMITS the whole
`(asset, δ)` block iff EVERY asset's signed delta sum is `0` — one independent boundary per asset,
exactly `BlockConservation`'s "one per-asset AIR run per asset" (cross-asset borrowing impossible). -/
theorem conservesRows_iff (rows : List (Nat × Int)) :
    conservesRows rows = true ↔ ∀ a ∈ keysAsc rows, sumForAsset rows a = 0 := by
  unfold conservesRows firstImbalanced
  rw [findSome?_isNone_iff]
  constructor
  · intro h a ha
    have := h a ha
    by_cases hb : sumForAsset rows a = 0
    · exact hb
    · simp [hb] at this
  · intro h a ha
    simp [h a ha]

/-! ## §7 — non-vacuity: the `p`-sum forgery is REFUSED (the ℤ decision kills the wrap). -/

/-- The concrete forgery `CrossCellConservation.ccc_psum_forgery_unsat` names — two credit rows whose
TRUE integer sum is exactly `p = 2013265921` with no debit — is REFUSED by the decision. The
single-felt design accepted it (`p ≡ 0 [ZMOD p]`); the ℤ decision does not. -/
theorem psum_forgery_refused : conservesSingle [1006632961, 1006632960] = false := by decide

/-- A matched transfer conserves (the decision is not the trivial `false`). -/
theorem honest_transfer_conserves : conservesSingle [-10, 10] = true := by decide

#assert_axioms balanceList_deltasOfTrace
#assert_axioms decision_conserves_iff_air_boundary
#assert_axioms satisfied_imp_decision_conserves
#assert_axioms conservesRows_iff

end Dregg2.Circuit.CrossCellConserveRefine
