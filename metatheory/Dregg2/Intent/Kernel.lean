/-
# Dregg2.Intent.Kernel — the concrete `KernelIntent` (the auction proves on this).

Phase 2, layer 4 (`docs/rebuild/PHASE-2-INTENT-SPEC.md`). The concrete instance of the four-faced
`Intent` (`Intent/Core.lean`) over the kernel's resources. The abstract laws — `fulfill_discharges`
(the receipt⊣intent keystone), `fulfill_conserves`, `no_double_fulfill` — are polymorphic over the
resource theory `R` and the time-world `(B, reg, stmtOf)`, so they **transfer to `KernelIntent` by
instantiation** (no re-proof). This is the layered-option-(c) payoff: prove once over `Intent R`, reuse
on the concrete model.

**Resource choice (ember-approved, 2026-06-03):** for the gallery auction DEMO, `DreggResources` =
asset bundles (`Resource.DemoRes`). This is the right grain for the auction; the *real* kernel resources
(assets ⊗ caps ⊗ cells, with the market's standing offers as non-identity conversions) sharpen in
Phase 4 — the abstract layer does not change when they do. In the discrete demo, convertibility is
EXACT, so a true cross-asset bid (offer gold, want art) is NOT directly fillable: it needs the market's
offer-generated conversions (Phase 4). Here we exhibit (a) a well-formed bid intent, (b) the keystone
transferred to a same-allocation settle, (c) the cross-asset bid's boundary teeth (needs the market).

Pure; no `axiom`/`sorry`/`admit`/`native_decide`.
-/
import Dregg2.Intent.Core
import Dregg2.Intent.Match

namespace Dregg2.Intent

open CategoryTheory
open Dregg2.Time.Deadline (Deadline)
open Dregg2.Authority.Blocklace (Lace)
open Dregg2.Authority.Predicate (Registry)
open Dregg2.Time.Frame (FrameStatement)

/-! ## 1. The concrete resource theory + the concrete intent. -/

/-- **`DreggResources`** — the kernel's resource objects for the auction demo: asset bundles
(`Resource.DemoRes`, the discrete symmetric monoidal category on `(gold, art)` count bundles). Phase 4
sharpens this to assets ⊗ caps ⊗ cells with market offers. -/
abbrev DreggResources := DemoRes

/-- **`KernelIntent`** — the four-faced intent over the kernel resources and a time-world. The abstract
`Intent R`-laws specialize here by instantiation. -/
abbrev KernelIntent {Stmt Wit : Type} (B : Lace) (reg : Registry Stmt Wit)
    (stmtOf : FrameStatement → Stmt) := Intent DreggResources B reg stmtOf

/-! ## 2. A concrete auction intent + the keystone, transferred. -/

/-- A **sealed-bid settle intent** over the kernel resources: the winning allocation is "3 art"
(`res 0 3`) — offered and demanded (a settled allocation), accepted exactly, escrow funded, with a
**causal** validity window (`causalAfter g0`): the fill may not happen before the reveal event `g0` — a
lightcone fact, so reveal-ordering excludes frontrunning *structurally* (the Phase-4 headline). -/
def settleIntent : KernelIntent Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 0 3
  wanted := res 0 3
  predicate := fun r => r = res 0 3
  resource := EscrowWitness.fund (res 0 3)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- The settle is fulfilled by the identity conversion (allocation = allocation); the escrow is locked.
-/
def settleReceipt : FillReceipt settleIntent :=
  fulfill settleIntent (𝟙 (res 0 3)) rfl rfl

/-- **The discharge keystone, TRANSFERRED to `KernelIntent`** — proved by *instantiating* the abstract
`fulfill_discharges` (`Intent/Core.lean`) at the concrete settle, with NO re-proof. The kernel receipt
witnesses exactly the demanded allocation, the predicate holds, and the escrow is consumed. -/
theorem settle_discharges :
    settleReceipt.outcome = res 0 3 ∧
      settleIntent.predicate settleReceipt.outcome ∧
      settleReceipt.spentEscrow.locked = false :=
  fulfill_discharges settleIntent (𝟙 (res 0 3)) rfl rfl

/-- **Conservation across the settle, TRANSFERRED** — the receipt carries a conversion
`offered ⟶ outcome`, so the allocation conserves (the Phase-3 per-asset `Σ in = Σ out` invariant
refines this). By instantiating the abstract `fulfill_conserves`. -/
theorem settle_conserves : Converts settleIntent.offered settleReceipt.outcome :=
  fulfill_conserves settleIntent (𝟙 (res 0 3)) rfl rfl

/-- **One-shot, TRANSFERRED** — the settle's escrow cannot fund a second fill (the abstract
`no_double_fulfill`, instantiated). No double-settle from one escrow. -/
theorem settle_no_double : settleReceipt.spentEscrow.locked ≠ true :=
  no_double_fulfill settleIntent (𝟙 (res 0 3)) rfl rfl

/-! ## 3. The cross-asset bid — boundary teeth (needs the market = Phase 4). -/

/-- A **cross-asset bid**: offer "5 gold" (`res 5 0`, escrowed), want "1 art" (`res 0 1`). A genuine
exchange intent. Its causal validity excludes pre-reveal fills. -/
def crossBid : KernelIntent Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 5 0
  wanted := res 0 1
  predicate := fun r => r = res 0 1
  resource := EscrowWitness.fund (res 5 0)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- **The cross-asset bid is NOT directly fillable:** no conversion `5 gold ⟶ 1 art` exists in the
discrete resource theory — the hole is unpluggable WITHOUT the market's standing offers (Phase 4's
offer-generated conversions / the `Match` coend's multi-hop routing). This is the honest boundary: the
intent is well-formed, but its fill is a *market* fact, not a resource fact. -/
theorem crossBid_needs_market : ¬ Converts crossBid.offered crossBid.wanted :=
  res_no_convert (by decide)

/-! ## 4. The solver embedding — the settle as a route in the coend `Match`. -/

/-- The settle fill, as a one-hop route in the kernel's solver (`Match`). The cross-asset bid would
populate `Match (res 5 0) (res 0 1)` only once the market supplies an offer — the multi-hop case. -/
def settleRoute : Match settleIntent.offered settleReceipt.outcome :=
  settleReceipt.lensFill.toMatch

/-! ### `#eval` smoke. -/

#guard (settleReceipt.outcome.as |>.toAdd) == (0, 3)   -- the settled allocation (3 art)
#guard settleReceipt.spentEscrow.locked == false       -- escrow consumed
#guard settleIntent.validity.kind                      -- causal reveal-ordering — anti-frontrunning

/-! ### Axiom hygiene — pin EVERY Phase-2 intent theorem to the three kernel axioms.

One line, run at the end of the `Intent.*` stack: walks every theorem under `Dregg2.Intent` (Resource,
Core, Match, Kernel) and errors if any escapes `{propext, Classical.choice, Quot.sound}` — a `sorryAx`
anywhere would fail the build. No `sorry`/`admit`/`native_decide` leaked into any keystone. -/
#assert_namespace_axioms Dregg2.Intent

end Dregg2.Intent
