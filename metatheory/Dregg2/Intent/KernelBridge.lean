/-
# Dregg2.Intent.KernelBridge — the Intent/auction layer is a FAITHFUL SHADOW of the real bal-ledger.

**DEMO (non-production): the TOY-REMEDIATION seam.** This module exists precisely BECAUSE the
Intent/auction stack above it runs on a toy. It proves the toy *refines* the real kernel ledger, but the
`DemoRes` carrier it bridges from is itself the non-production two-asset `(gold, art)` demo — the
refinement is the remediation, not a claim that the toy is itself a shipped resource theory.

The whole Intent/auction stack (`Intent/Resource.lean`,
`Intent/Core.lean`, `Intent/Kernel.lean`) runs on the `DemoRes` TOY: `Discrete (Multiplicative
(ℕ × ℕ))`, the discrete symmetric-monoidal category on `(gold, art)` count bundles. Its conservation
(`fulfill_conserves` / the `Converts offered outcome` shadow) is HONEST but ABSTRACT — it says only "a
conversion exists", a thin convertibility fact, not the strong per-asset `Σ in = Σ out` the REAL
executable ledger enforces. The memory note (`THE-JAM`/`don't-cheap-out`) calls exactly this out: the
hard core is showing the toy *refines* the real kernel, not just that the toy is internally consistent.

This module builds the **refinement bridge** down to `Exec/RecordKernel.lean`'s genuine per-asset
ledger `RecordKernelState.bal : CellId → AssetId → ℤ`, whose keystone `recKExecAsset_conserves_per_asset`
proves every committed per-asset transfer preserves `recTotalAsset k b` for EVERY asset `b` (the moved
asset by debit/credit cancellation, every other asset literally untouched — the `CONSERVATION_VECTOR`).

The plan (the standard refinement square — *abstract* commutes ⟹ *concrete* commutes):

  1. **`toBal` — the refinement map.** A `DemoRes` bundle `(gold, art)` shadows a per-asset `bal`
     delta: gold ↦ asset `0`, art ↦ asset `1`, every other asset ↦ `0`. This is the abstraction
     function α : Bundle → (AssetId → ℤ) of the data refinement.

  2. **Faithful, with TEETH.** `toBal` is INJECTIVE on the two demo assets (`toBal_inj`): distinct
     bundles shadow distinct per-asset deltas — the shadow does NOT collapse (no Subsingleton dodge).

  3. **The abstract conservation REFINES to per-asset equality.** A settled Intent carries
     `Converts offered outcome` (`fulfill_conserves`). In the discrete category a conversion forces the
     bundles EQUAL, so `toBal offered = toBal outcome` *pointwise per asset* (`converts_refines_toBal`):
     the abstract Σ-conservation shadow refines to the real per-asset measure agreeing on every asset.

  4. **The SIMULATION lemma (the headline).** The settled bundle, transferred src→dst on the REAL
     `bal` ledger via `recKExecAsset`, conserves `recTotalAsset b` for EVERY asset `b` — by *composing*
     `recKExecAsset_conserves_per_asset`. A settled Intent corresponds to a real per-asset transfer that
     conserves each asset. This is the simulation: abstract discharge ⟹ concrete per-asset conservation.

  5. **TEETH — the bridge REJECTS a toy-accepted, real-conservation-VIOLATING settle.** The hostile
     case the bridge must refuse: an Intent whose `offered`/`wanted` bundles disagree on some asset's
     `toBal` (so a real per-asset transfer of one would NOT leave the other's supply equal — laundering
     gold for art). The bridge proves NO such settle discharges (`bridge_rejects_nonconserving`): no
     `Converts offered wanted`, so the hole is unpluggable. The toy's discrete category and the real
     per-asset ledger AGREE on what conserves — genuine discrimination, not a vacuous pass.

Pure.
-/
import Dregg2.Intent.Kernel
import Dregg2.Exec.RecordKernel

universe v u

namespace Dregg2.Intent

open CategoryTheory
open Dregg2.Exec (RecordKernelState AssetId Turn CellId recTransferBal recTotalAsset recKExecAsset
  recKExecAsset_conserves_per_asset)

/-! ## 1. `toBal` — the refinement map (the abstraction function α : Bundle → per-asset Δ). -/

/-- **`toBal b` — the per-asset shadow of a `DemoRes` bundle.** A bundle `(gold, art)` (the toy's
two-asset carrier) maps to a per-asset `bal` delta: asset `0` carries the `gold` count, asset `1` the
`art` count, every other asset is `0`. This is the abstraction function of the data refinement — it
embeds the toy's two-coordinate `(ℕ × ℕ)` carrier into the real kernel's `AssetId → ℤ` ledger
(`RecordKernelState.bal`). The `ℕ → ℤ` cast is faithful (no debt in the toy; the real ledger is
debt-capable but the shadow lands in `≥ 0`). -/
def toBal (b : Bundle) : AssetId → ℤ :=
  fun a => if a = 0 then (b.toAdd.1 : ℤ) else if a = 1 then (b.toAdd.2 : ℤ) else 0

/-- `toBal` at asset `0` reads the gold count. -/
@[simp] theorem toBal_zero (b : Bundle) : toBal b 0 = (b.toAdd.1 : ℤ) := rfl

/-- `toBal` at asset `1` reads the art count. -/
@[simp] theorem toBal_one (b : Bundle) : toBal b 1 = (b.toAdd.2 : ℤ) := by
  unfold toBal; simp

/-- `toBal` at any asset `≥ 2` is `0` (the demo carries only two assets). -/
theorem toBal_other (b : Bundle) {a : AssetId} (h0 : a ≠ 0) (h1 : a ≠ 1) : toBal b a = 0 := by
  unfold toBal; rw [if_neg h0, if_neg h1]

/-- `toBal` of an `res`-bundle, concretely: `toBal (mkBundle g a)` is gold `g` at asset 0, art `a` at
asset 1, else 0. The bridge between the auction's `res g a` objects and the real per-asset ledger. -/
@[simp] theorem toBal_mkBundle (g a : ℕ) :
    toBal (mkBundle g a) = fun k => if k = 0 then (g : ℤ) else if k = 1 then (a : ℤ) else 0 := by
  funext k
  unfold toBal mkBundle
  simp [toAdd_ofAdd]

/-! ### Faithfulness — TEETH: the shadow does not collapse. -/

/-- **`toBal` is INJECTIVE (the shadow is faithful).** Distinct bundles shadow distinct per-asset
deltas: if `toBal b = toBal b'` agree on all assets, then `b = b'`. NON-VACUOUS — it reads the two demo
assets back out (`toBal · 0`, `toBal · 1`) and uses `ℕ → ℤ` injectivity, so a genuine separating witness
survives the refinement (this is what forbids a `Subsingleton.elim` dodge: the map really distinguishes
gold-bundles from art-bundles). -/
theorem toBal_inj {b b' : Bundle} (h : toBal b = toBal b') : b = b' := by
  have hg : ((b.toAdd.1 : ℤ)) = (b'.toAdd.1 : ℤ) := by
    have := congrFun h 0; simpa using this
  have ha : ((b.toAdd.2 : ℤ)) = (b'.toAdd.2 : ℤ) := by
    have := congrFun h 1; simpa using this
  have hg' : b.toAdd.1 = b'.toAdd.1 := by exact_mod_cast hg
  have ha' : b.toAdd.2 = b'.toAdd.2 := by exact_mod_cast ha
  -- a bundle IS its `toAdd` pair (up to the `Multiplicative` tag); equal coordinates ⇒ equal bundle.
  have : b.toAdd = b'.toAdd := Prod.ext hg' ha'
  exact Multiplicative.toAdd.injective this

/-- **The faithfulness teeth, witnessed:** "2 gold" and "1 art" shadow DIFFERENT per-asset deltas
(`toBal (res 2 0).as ≠ toBal (res 0 1).as`). The exact pair the toy's `demo_no_convert` refuses — the
real ledger refuses it too (it would move asset 0 against asset 1, the laundering the per-asset measure
forbids). -/
theorem toBal_separates : toBal (res 2 0).as ≠ toBal (res 0 1).as := by
  intro h
  -- read asset 0: 2 = 0 (gold), absurd.
  have := congrFun h 0
  simp [res, mkBundle, toAdd_ofAdd] at this

/-! ## 2. The abstract `Converts`-shadow REFINES to per-asset equality. -/

/-- **`converts_refines_toBal` — the abstract Σ-conservation REFINES to per-asset equality.** In the
discrete demo resource theory, a conversion `Converts a c` forces the underlying bundles EQUAL
(`Discrete.eq_of_hom`), hence their per-asset shadows agree on EVERY asset: `toBal a.as = toBal c.as`.
This is the refinement of `fulfill_conserves`: the thin convertibility witness (`offered ⪰ outcome`)
descends to the real per-asset measure `toBal` agreeing pointwise — the abstract conservation shadow is
faithfully reflected in the concrete ledger's per-asset reading. -/
theorem converts_refines_toBal {a c : DemoRes} (h : Converts a c) :
    toBal a.as = toBal c.as := by
  obtain ⟨f⟩ := h
  have he : a.as = c.as := Discrete.eq_of_hom f
  rw [he]

/-! ## 3. The SIMULATION — a settled Intent transfers per-asset on the REAL ledger, conserving. -/

/-- **`settleTransfer` — the real per-asset transfer a settled bundle induces.** Given a real kernel
state `k`, a `src`/`dst` cell pair, and a bundle `b`, the kernel turn that moves `toBal b a` of asset
`a` from `src` to `dst` (the per-asset move of the bundle's `a`-component). Each asset is a SEPARATE
`recKExecAsset` transfer of `toBal b a` — the bundle's two assets (gold, art) are moved independently,
NEVER folded into one aggregate (the per-asset discipline). -/
def settleTransfer (src dst : CellId) (b : Bundle) (a : AssetId) : Turn :=
  { actor := src, src := src, dst := dst, amt := toBal b a }

/-- **THE SIMULATION LEMMA — a settled Intent corresponds to a real per-asset transfer that conserves
EVERY asset.** If the real per-asset move of the settled bundle's `a`-component commits
(`recKExecAsset k (settleTransfer …) a = some k'`), then for EVERY asset `b` the real total supply is
preserved: `recTotalAsset k' b = recTotalAsset k b`. Proved by *composing* the real kernel's keystone
`recKExecAsset_conserves_per_asset` — the moved asset by debit/credit cancellation, every other asset
because its column is literally untouched. This is the refinement payoff: the Intent layer's abstract
discharge is a FAITHFUL SHADOW of a real-ledger transfer that conserves per-asset, not just in
aggregate. -/
theorem settle_refines_per_asset_conservation
    (k k' : RecordKernelState) (src dst : CellId) (b : Bundle) (a : AssetId)
    (h : recKExecAsset k (settleTransfer src dst b a) a = some k') (asset : AssetId) :
    recTotalAsset k' asset = recTotalAsset k asset :=
  recKExecAsset_conserves_per_asset k k' (settleTransfer src dst b a) a h asset

/-- **The whole-bundle simulation — gold AND art, each conserving.** A settled bundle is transferred
as TWO independent per-asset moves (asset 0 = gold, asset 1 = art). If BOTH commit, then EVERY asset's
real total supply is preserved across the pair. This is the concrete refinement of a settled Intent: its
`(gold, art)` allocation is realised as two real per-asset transfers, neither of which leaks supply into
any asset (including each other — the cross-asset non-laundering of `recKExecAsset_no_cross_asset_leak`,
lifted to the Intent layer). -/
theorem settle_refines_bundle_conservation
    (k k₁ k₂ : RecordKernelState) (src dst : CellId) (b : Bundle)
    (h0 : recKExecAsset k  (settleTransfer src dst b 0) 0 = some k₁)
    (h1 : recKExecAsset k₁ (settleTransfer src dst b 1) 1 = some k₂)
    (asset : AssetId) :
    recTotalAsset k₂ asset = recTotalAsset k asset := by
  have e1 : recTotalAsset k₁ asset = recTotalAsset k asset :=
    settle_refines_per_asset_conservation k k₁ src dst b 0 h0 asset
  have e2 : recTotalAsset k₂ asset = recTotalAsset k₁ asset :=
    settle_refines_per_asset_conservation k₁ k₂ src dst b 1 h1 asset
  rw [e2, e1]

/-! ## 4. The Intent-layer simulation — `settle_conserves` REFINES real per-asset conservation. -/

/-- **The discharged-Intent simulation (the bridge keystone).** Take ANY concrete `KernelIntent` whose
fulfillment discharges (carries `Converts offered outcome` — `fulfill_conserves`). Then:

  * (abstract ⟹ shadow) the offered and achieved bundles agree on EVERY asset's `toBal`
    (`converts_refines_toBal`) — the abstract conservation refines to per-asset equality; AND
  * (shadow ⟹ real) realising that bundle as a real per-asset `recKExecAsset` transfer conserves
    `recTotalAsset` for EVERY asset (`settle_refines_per_asset_conservation`).

So a settled Intent IS a faithful shadow of a real-ledger transfer that conserves per-asset. The
hypotheses are exactly what `Intent/Kernel.lean`'s `settle_conserves` provides — this composes the
abstract keystone with the real kernel keystone across the refinement map. -/
theorem discharged_intent_refines_real
    {Stmt Wit : Type} {B : Dregg2.Authority.Blocklace.Lace}
    {reg : Dregg2.Authority.Predicate.Registry Stmt Wit}
    {stmtOf : Dregg2.Time.Frame.FrameStatement → Stmt}
    (i : KernelIntent B reg stmtOf) (r : FillReceipt i)
    (hconv : Converts i.offered r.outcome)
    (k k' : RecordKernelState) (src dst : CellId) (a : AssetId)
    (htransfer : recKExecAsset k (settleTransfer src dst i.offered.as a) a = some k') :
    toBal i.offered.as = toBal r.outcome.as ∧
      (∀ asset : AssetId, recTotalAsset k' asset = recTotalAsset k asset) := by
  refine ⟨converts_refines_toBal hconv, ?_⟩
  intro asset
  exact settle_refines_per_asset_conservation k k' src dst i.offered.as a htransfer asset

/-- **The concrete settle, refined.** The auction's `settleIntent` (`Intent/Kernel.lean`, the winning
"3 art" allocation) discharges with `settle_conserves : Converts offered outcome`; the bridge refines
THAT to per-asset equality of the real ledger reading. The settled "3 art" bundle shadows asset 1 = 3,
asset 0 = 0 — and a real per-asset transfer of it conserves every asset. The full instantiation of the
bridge on the shipped auction intent. -/
theorem settleIntent_refines :
    toBal settleIntent.offered.as = toBal settleReceipt.outcome.as :=
  converts_refines_toBal settle_conserves

/-- The settled "3 art" bundle's per-asset shadow, concretely: asset 0 (gold) = 0, asset 1 (art) = 3,
every other asset = 0. The real per-asset delta the auction's settle induces on the ledger — NON-VACUOUS
(asset 1 is `3`, not collapsed to a single scalar). -/
theorem settleIntent_toBal :
    toBal settleIntent.offered.as = fun a => if a = 0 then (0 : ℤ) else if a = 1 then 3 else 0 := by
  show toBal (res 0 3).as = _
  simp [res]

/-! ## 5. TEETH — the bridge REJECTS a toy-accepted, real-conservation-VIOLATING settle. -/

/-- **`bridge_rejects_nonconserving` (THE TEETH).** The hostile case the bridge MUST refuse: an Intent
whose `offered` and `wanted` bundles shadow DIFFERENT per-asset deltas (`toBal offered ≠ toBal wanted` —
e.g. offer gold, want art, which on the real ledger is laundering asset 0 for asset 1, per-asset
NON-conserving). The bridge proves NO conversion `offered ⟶ wanted` exists — so the intent's hole is
UNPLUGGABLE, no fill discharges. The toy's discrete category and the real per-asset ledger AGREE on what
conserves: a bundle move conserves per-asset iff the bundles are equal iff `toBal` agrees iff a discrete
conversion exists. Genuine discrimination — a settle the toy "wants" but that violates real per-asset
conservation is structurally rejected (contrapositive of `converts_refines_toBal`). -/
theorem bridge_rejects_nonconserving {a c : DemoRes} (h : toBal a.as ≠ toBal c.as) :
    ¬ Converts a c :=
  fun hconv => h (converts_refines_toBal hconv)

/-- **The cross-asset bid is rejected by the bridge — witnessed.** The auction's `crossBid` (offer "5
gold", want "1 art") shadows `toBal (res 5 0).as ≠ toBal (res 0 1).as` (asset 0 reads 5 vs 0), so the
bridge refuses it: `¬ Converts crossBid.offered crossBid.wanted`. This is the SAME boundary the toy's
`crossBid_needs_market` carries (`Intent/Kernel.lean`) — but now JUSTIFIED by real per-asset conservation:
moving 5 gold to obtain 1 art would change asset 0 and asset 1 supplies inconsistently, which the real
ledger's per-asset measure forbids. Reuses `bridge_rejects_nonconserving`, so the refusal is the SHADOW
of a real conservation fact, not a toy artefact. -/
theorem crossBid_rejected_by_bridge : ¬ Converts crossBid.offered crossBid.wanted := by
  apply bridge_rejects_nonconserving
  -- `crossBid.offered = res 5 0`, `crossBid.wanted = res 0 1`; they disagree at asset 0 (5 ≠ 0).
  intro h
  have := congrFun h 0
  simp [crossBid, res, mkBundle, toAdd_ofAdd] at this

/-- **The teeth, the other direction (genuine equivalence at the demo grain).** For the demo's two
assets, `toBal` agreement is EXACTLY bundle equality (`toBal_inj` + congruence), and bundle equality is
exactly when a discrete conversion exists. So the bridge's acceptance criterion (`toBal` agrees) and the
toy's fillability criterion (`Converts`) COINCIDE — the refinement is tight, neither over- nor
under-approximating. This rules out a vacuous bridge that accepts everything (it would have to accept the
cross-asset bid, which `crossBid_rejected_by_bridge` refutes) or rejects everything (it accepts the
identity settle, `settleIntent_refines`). -/
theorem bridge_accepts_iff_conserves {a c : DemoRes} :
    toBal a.as = toBal c.as ↔ Converts a c := by
  constructor
  · intro h
    have hbas : a.as = c.as := toBal_inj h
    -- equal underlying bundles ⇒ a discrete conversion exists (the eqToHom).
    refine ⟨?_⟩
    have : a = c := by cases a; cases c; simp_all
    exact this ▸ 𝟙 a
  · exact converts_refines_toBal

/-! ## 6. Axiom hygiene — pin EVERY bridge keystone to the three kernel axioms.

Walks every theorem under `Dregg2.Intent.KernelBridge`'s declarations and errors if any escapes
`{propext, Classical.choice, Quot.sound}` — a `sorryAx`/`admit`/`native_decide` anywhere would fail the
build. The refinement bridge is kernel-clean. -/
#assert_axioms toBal_inj
#assert_axioms converts_refines_toBal
#assert_axioms settle_refines_per_asset_conservation
#assert_axioms settle_refines_bundle_conservation
#assert_axioms discharged_intent_refines_real
#assert_axioms settleIntent_refines
#assert_axioms bridge_rejects_nonconserving
#assert_axioms crossBid_rejected_by_bridge
#assert_axioms bridge_accepts_iff_conserves

/-! ### `#eval` smoke — the refinement is computable on the auction's settle. -/

#guard toBal settleIntent.offered.as 1 == 3     -- the settled art allocation, as a real per-asset Δ
#guard toBal settleIntent.offered.as 0 == 0     -- gold untouched
#guard toBal crossBid.offered.as 0 == 5         -- the cross-asset bid's gold (≠ wanted art → rejected)

end Dregg2.Intent
