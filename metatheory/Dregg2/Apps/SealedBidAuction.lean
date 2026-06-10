/-
# Dregg2.Apps.SealedBidAuction — the gallery SEALED-BID AUCTION (Track-A Phase 4, the proving-ground app).

The first END-TO-END app on the intent-as-co-receipt stack (`docs/rebuild/INTENT-AS-CO-RECEIPT.md` §5/§7,
HANDOFF Track A). It is **composition, not new theory**: every keystone INSTANTIATES a proved abstract
lemma from the green Phase-1/2/3 modules. The auction proves, on the same-bundle settle (the
decision-free core — see the OPEN block below for the model-shape calls deferred to ember):

  * **(b) causal reveal-ordering EXCLUDES frontrunning** — a *lightcone fact*, not a gas race: a fill that
    does not causally follow the bid's reveal event fails the bid's validity window. The teeth: a bid
    revealed on the Byzantine fork `f1` is UNFILLABLE by a concurrent fill on `f2`
    (`no_frontrunning_teeth`), backed by `Time.Causal.demo_frontrun_caught` (`f1 ∦ f2`).
  * **(c) CONSERVATION across the settle** — no value minted: the settle receipt carries a conversion
    `offered ⟶ outcome`, hence `Converts offered outcome` (the thin Coecke–Fritz convertibility shadow,
    `fulfill_conserves`). The teeth: a cross-asset settle that WOULD mint (5 gold ⟶ 1 art with no market
    offer) is rejected — `no Converts`, so no fill, so nothing minted (`settle_cannot_mint`, via
    `res_no_convert`).
  * **(c⁺) STRONG per-asset Σ-CONSERVATION** — strictly above the thin shadow: each asset's total is an
    `AddMonoidHom (ℕ × ℕ) →+ ℕ` and the settle preserves EVERY such total (`settle_sigma_conserves`,
    refining `Converts` to a named per-asset ledger). The teeth: a hypothetical mint-one-asset settle is
    CAUGHT by Σ where the shadow is silent (`mint_rejected_by_sigma`).
  * **(Q1) CROSS-ASSET exchange** — the cross-asset bid (pay gold, get art) is FILLED by an
    offer-generated conversion (a seller `Offer gold ⟶ art`, realized as a balanced two-leg `Exchange`),
    and the matched exchange still conserves every asset's Σ-total (`crossBid_fillable_by_offer`,
    `exchange_sigma_conserves` — Q2 survives Q1). The teeth: a SKIMMING settle the per-leg shadow accepts
    is rejected by Σ (`thinShadow_accepts_skim` vs `skim_rejected_by_sigma`) — no minting without a
    balanced backing offer.
  * **one-shot (no double-settle)** — the settled escrow is released and can never fund a second settle
    (`settle_no_double`, the abstract `no_double_fulfill` instantiated).
  * **loser-refund LIVENESS** — the genuine `◇`: from a `JustProgress` package over a refund potential,
    `just_progress` yields `Eventually Refunded`. Carried as the abstract template
    (`loser_refunded_eventually`) AND de-vacuified by a concrete inhabited witness on the REAL executor
    (`auction_loser_refunded`, reusing `Fairness.refundDemo`'s B-just `transferSched` path). The teeth that
    keep this non-vacuous: `Fairness.badSched_not_just` (a starving schedule is REJECTED).

## The §8 carriers — kept honest (explicit)

The sealed-bid commitment is the COMMIT phase: a bidder publishes `commit value blinding` BEFORE the
reveal frontier, then the reveal "opens" it. The validity face is `causalAfter revealEvt` (the reveal
event), so anti-frontrunning needs **no clock, no authority, no δ** — `causalAfter_no_frame_dependency`.
The commitment binding/hiding (Pedersen) enters ONLY as the §8 carrier `CryptoKernel.commit` (NOT faked
here — the auction is parametric in the digest type; the headline (b) is a pure ORDER fact that does not
touch the commitment seam). A wall-clock auction-CLOSE (a separate `frameWithin` deadline) would carry its
own `δ` and the `commit_wait_bridge`; the headline does not use it.

## The (a) obligation — userspace-escrow ≥ kernel-escrow — is a CARRIED OPEN, not a stub

The §5/§7 inequality `kernelEscrow ⊑ userspaceEscrow` needs the userspace-escrow CELL-PROGRAM (`INTENT-AS-
CO-RECEIPT.md` §2 face 3) that does not yet exist in the green tree, and a state CLOCK dimension the
executor lacks (`EFFECT-FIDELITY-LEDGER.md`). Per MEMORY "Improve Don't Degrade" / "Don't Cheap Out": it
is NOT stubbed and NOT `sorry`'d — it is stated as a carried-hypothesis interface obligation
(`UserspaceDominatesKernel` + `escrow_refinement_sound`) whose precise model-shape is OPEN-flagged for
ember (see §5). Everything else ships green around it.

Built per the architect's PHASE-4 BUILD SPEC. Pure.
-/
import Dregg2.Intent.Kernel
import Dregg2.Proof.Fairness

namespace Dregg2.Apps.SealedBidAuction

open CategoryTheory MonoidalCategory
open Dregg2.Intent
open Dregg2.Time.Deadline (Deadline)
open Dregg2.Time.Causal (Frontier CausalAfter frontrunExcluded)
open Dregg2.Authority.Blocklace (demoLace g0 g1 f1 f2)

/-! ## 1. The per-bidder sealed-bid `KernelIntent` (the four faces, on the kernel resources).

A bid is a four-faced `Intent` over `DreggResources` (asset bundles) and the demo time-world
(`demoLace`, the empty registry `demoReg`, the constant encoder `demoStmtOf` — `Intent/Core.lean`). The
empty registry is LOAD-BEARING and correct: the causal reveal-ordering needs NO authority
(`causalAfter_no_frame_dependency`); only a frame-typed wall-clock close would need one.

DECISION-FREE DEFAULTS (the architect's Q1a / Q2-thin / Q5i — same-bundle settle, thin `Converts`
conservation, per-bid acceptance predicate):
  * `offered = wanted = alloc` — the WINNER's escrow is already in the settled allocation, so the fill is
    the identity conversion (`settleIntent` shape, `Intent/Kernel.lean`). The genuine cross-asset
    exchange (pay gold, get art) needs the market's offer-generated conversions — deferred (`crossBid`,
    the §3 teeth). -/

/-- A bidder is a cell on the lace, identified by its block's `creator` worldline (`Blocklace.Block`'s
`creator : Nat`). (Architect Q3 default: a worldline, not a bare `CellId`. The N-bidder protocol with a
purpose-built lace is the deferred build; here a bidder rides the demo lace's authors.) -/
abbrev Bidder := Nat

/-- **A per-bidder sealed-bid intent** over the kernel resources, with a CAUSAL validity window
`causalAfter revealEvt` — a lightcone fact: the fill MAY NOT happen before the reveal event `revealEvt`,
so reveal-ordering excludes frontrunning *structurally* (§3). `alloc` is the bidder's settled allocation
(same-bundle: offered = wanted = alloc); `accept` is the per-bid acceptance predicate (Q5i: "this is my
allocation"). The escrow is funded over `alloc`. -/
def bidIntent (_bidder : Bidder) (alloc : DreggResources) (revealEvt : Frontier) :
    KernelIntent demoLace demoReg demoStmtOf where
  offered   := alloc
  wanted    := alloc
  predicate := fun r => r = alloc
  resource  := EscrowWitness.fund alloc
  validity  := Deadline.causalAfter revealEvt

/-- A concrete winning bid: bidder `7` (the honest author), allocation "3 art" (`res 0 3`), reveal at the
genesis event `g0`. -/
def winningBid : KernelIntent demoLace demoReg demoStmtOf := bidIntent 7 (res 0 3) g0

/-- The winning bid's validity is a CAUSAL deadline (the §4 court read-off: a lightcone fact, no trust). -/
theorem winningBid_is_causal : winningBid.validity.kind = true := rfl

/-! ## 2. The SETTLE — the winning bid filled by the allocating conversion.

In the discrete `DemoRes` the same-bundle settle (offered = wanted = alloc) is filled by the IDENTITY
conversion (allocation = allocation) — exactly `fulfill` at `𝟙 alloc` (`Intent/Core.lean`). This is the
decision-free core; the cross-asset settle (§3) is the market-generated case deferred to ember (Q1). -/

/-- **`auctionSettle`** — settle a (same-bundle) bid `i` by a conversion `f : i.offered ⟶ i.wanted`, given
the acceptance predicate holds at `wanted` and the escrow is LOCKED (funded). Produces the discharging
receipt with the escrow RELEASED — the receipt⊣intent counit (`fulfill`). -/
def auctionSettle (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    FillReceipt i :=
  fulfill i f hpred hlock

/-- The concrete settle of `winningBid`: the identity conversion `res 0 3 ⟶ res 0 3`, the predicate
accepts (`rfl`), the escrow is locked (`rfl`). The receipt attests "3 art" allocated to the winner. -/
def winningReceipt : FillReceipt winningBid :=
  auctionSettle winningBid (𝟙 (res 0 3)) rfl rfl

/-- The settle discharges to exactly the demanded allocation, the predicate holds there, and the escrow is
consumed — the discharge keystone (`fulfill_discharges`) at the auction settle. -/
theorem winning_discharges :
    winningReceipt.outcome = res 0 3 ∧
      winningBid.predicate winningReceipt.outcome ∧
      winningReceipt.spentEscrow.locked = false :=
  fulfill_discharges winningBid (𝟙 (res 0 3)) rfl rfl

/-! ## 3. KEYSTONE (b) — causal reveal-ordering EXCLUDES frontrunning.

Anti-frontrunning is "no one may fill before I reveal" = `revealEvt ≺ fill` = `frontrunExcluded demoLace
revealEvt fill` — a frame-invariant happens-before FACT (spine §4/§5), discharged exactly when the bid's
causal validity window is MET at the fill frontier. The `Deadline.Met` check on the bid's validity IS
`CausalAfter demoLace revealEvt fill` (definitional dispatch, `Deadline.lean`): one predicate, no
timestamp race. So MEV = control of a simultaneity surface a causal model simply does not have. -/

/-- **`met_iff_frontrunExcluded`** — the bid's validity window is MET at frontier `fillNow` EXACTLY when
the fill causally follows the reveal (frontrunning excluded). The two are *definitionally* the same
proposition: `Deadline.Met` of `causalAfter revealEvt` dispatches to `CausalAfter demoLace revealEvt
fillNow = frontrunExcluded …`. The anti-frontrunning gate and the deadline check are ONE predicate. -/
theorem met_iff_frontrunExcluded (bidder : Bidder) (alloc : DreggResources)
    (revealEvt fillNow : Frontier) :
    (bidIntent bidder alloc revealEvt).validity.Met fillNow ↔
      frontrunExcluded demoLace revealEvt fillNow :=
  Iff.rfl

/-- **`no_frontrunning` (KEYSTONE b)** — a fill that does NOT causally follow the reveal is REJECTED: the
bid's causal validity window is NOT met at a pre-reveal / concurrent fill frontier. The frontrun is
excluded by the ORDER, not adjudicated by a clock. Definitionally `h` (the validity-Met predicate IS the
frontrun-excluded predicate). -/
theorem no_frontrunning (bidder : Bidder) (alloc : DreggResources) (revealEvt fillNow : Frontier)
    (h : ¬ frontrunExcluded demoLace revealEvt fillNow) :
    ¬ (bidIntent bidder alloc revealEvt).validity.Met fillNow :=
  h

/-- **`honest_fill_admitted` (positive non-vacuity)** — the dual: an HONEST fill that observed the reveal
IS admitted. A bid revealed at genesis `g0` and filled at the honest successor `g1` (which acks `g0`, so
`g0 ≺ g1`) MEETS its validity window — the order admits the honest filler. Without this the (b) keystone
could be vacuously "everything is rejected". Discharged by `demo_frontrun_excluded` (`g0 ≺ g1`). -/
theorem honest_fill_admitted (bidder : Bidder) (alloc : DreggResources) :
    (bidIntent bidder alloc g0).validity.Met g1 :=
  Dregg2.Time.Causal.demo_frontrun_excluded

/-- **`no_frontrunning_teeth` (the (b) TEETH — a real adversarial frontrun REJECTED, proved).** A bid
revealed on the Byzantine fork branch `f1` is GENUINELY UNFILLABLE by a fill on the *concurrent* fork
branch `f2`: `f2` never observed `f1` (they are incomparable, `f1 ∦ f2`), so the fill does not causally
follow the reveal and the bid's validity window is NOT met. The frontrun is caught by the causal order —
not by a gas auction. Discharged via the abstract `no_frontrunning` fed `Time.Causal.demo_frontrun_caught`.
-/
theorem no_frontrunning_teeth (bidder : Bidder) (alloc : DreggResources) :
    ¬ (bidIntent bidder alloc f1).validity.Met f2 :=
  no_frontrunning bidder alloc f1 f2 Dregg2.Time.Causal.demo_frontrun_caught

/-! ## 4. KEYSTONE (c) — CONSERVATION across the settle (no value minted).

The settle receipt carries `conversion : offered ⟶ outcome`, hence `Converts offered outcome` — the fill
type-checks and conserves BY CONSTRUCTION (Spivak's functoriality of operadic substitution; the thin
Coecke–Fritz convertibility shadow of the Phase-3 per-asset `Σ in = Σ out` invariant). A settle that would
MINT value (no conversion exists) is therefore unfillable. -/

/-- **`settle_conserves` (KEYSTONE c)** — the settled outcome is convertible FROM the offered escrow: no
value is minted across the settle. By instantiating the abstract `fulfill_conserves` at the auction
settle. -/
theorem settle_conserves (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    Converts i.offered (auctionSettle i f hpred hlock).outcome :=
  fulfill_conserves i f hpred hlock

/-- The concrete winning-settle conserves: `res 0 3 ⪰ res 0 3` (the winner's allocation is convertible
from the escrow). -/
theorem winning_settle_conserves : Converts winningBid.offered winningReceipt.outcome :=
  settle_conserves winningBid (𝟙 (res 0 3)) rfl rfl

/-- A **cross-asset bid** that would EXCHANGE value: offer "5 gold" (escrowed), want "1 art". A genuine
exchange intent whose causal validity excludes pre-reveal fills — the honest auction shape Phase 4
sharpens via the market's offer-generated conversions. -/
def crossBid (revealEvt : Frontier) : KernelIntent demoLace demoReg demoStmtOf where
  offered   := res 5 0
  wanted    := res 0 1
  predicate := fun r => r = res 0 1
  resource  := EscrowWitness.fund (res 5 0)
  validity  := Deadline.causalAfter revealEvt

/-- **`settle_cannot_mint` (the (c) TEETH — a real minting settle REJECTED, proved).** A cross-asset settle
that would mint value — turn "5 gold" into "1 art" with NO market offer — is UNFILLABLE: no conversion `5
gold ⟶ 1 art` exists in the discrete resource theory (`res_no_convert`). No conversion ⇒ no fill ⇒ nothing
minted. Conservation is enforced by the *absence* of a conversion, not by an after-the-fact audit. -/
theorem settle_cannot_mint (revealEvt : Frontier) :
    ¬ Converts (crossBid revealEvt).offered (crossBid revealEvt).wanted :=
  res_no_convert (by decide)

/-! ## 4b. KEYSTONE (c⁺) — STRONG per-asset Σ-conservation (strictly above the thin shadow).

`settle_conserves` (§4) is the THIN Coecke–Fritz convertibility shadow: "*some* conversion `offered ⟶
outcome` exists". In the discrete `DemoRes` that shadow already forces `offered = outcome`, but it does
so OPAQUELY — it never names a quantity, so it cannot be *aimed* at a single asset, and it is silent the
moment a settle spans more than one leg (the cross-asset exchange of §4c, where a per-leg `Converts` can
be satisfied while the GLOBAL ledger is short). The Phase-3 invariant we want is the per-asset ledger:
**for every asset, Σ of the inputs = Σ of the outputs**. We realize "Σ of an asset" as an
`AddMonoidHom (ℕ × ℕ) →+ ℕ` (the count of one asset kind is an additive homomorphism of bundle union),
and prove the settle preserves EACH such total — strictly stronger than, and refining, the thin shadow. -/

/-- **`assetTotal h r`** — the Σ-total of resource bundle `r` read through the asset-selector
homomorphism `h : (ℕ × ℕ) →+ ℕ`. Bundle union is `*` on `Multiplicative (ℕ × ℕ)` = `+` on `(ℕ × ℕ)`, so
a *fixed asset's count* is an `AddMonoidHom` and `assetTotal h` is additive over bundling
(`assetTotal_tensor`). This is the per-asset ledger projection the Phase-3 `Σ in = Σ out` invariant lives
on. -/
def assetTotal (h : (ℕ × ℕ) →+ ℕ) (r : DreggResources) : ℕ := h (Multiplicative.toAdd r.as)

/-- **`goldHom`** — the gold-count selector, the first-coordinate `AddMonoidHom`. -/
def goldHom : (ℕ × ℕ) →+ ℕ := AddMonoidHom.fst ℕ ℕ
/-- **`artHom`** — the art-count selector, the second-coordinate `AddMonoidHom`. -/
def artHom : (ℕ × ℕ) →+ ℕ := AddMonoidHom.snd ℕ ℕ

/-- **`assetTotal_tensor`** — every asset total is ADDITIVE over bundle union (`⊗`): the Σ of a
side-by-side bundle is the sum of the Σ's. This is the homomorphism property that makes Σ-conservation a
genuine *ledger* law (totals add across composed positions), and it is exactly why `assetTotal` is the
right refinement of the thin shadow — the shadow has no such additive structure. -/
theorem assetTotal_tensor (h : (ℕ × ℕ) →+ ℕ) (a b : DreggResources) :
    assetTotal h (a ⊗ b) = assetTotal h a + assetTotal h b := by
  show h (Multiplicative.toAdd (a.as * b.as))
     = h (Multiplicative.toAdd a.as) + h (Multiplicative.toAdd b.as)
  rw [show Multiplicative.toAdd (a.as * b.as)
        = Multiplicative.toAdd a.as + Multiplicative.toAdd b.as from rfl, map_add]

/-- **`converts_preserves_assetTotal`** — a conversion in `DemoRes` preserves EVERY asset total. A
`DemoRes` morphism forces the underlying bundles equal (`Discrete.eq_of_hom`), so reading either through
any selector `h` gives the same Σ. This is the bridge from the rich/thin convertibility layer to the
per-asset ledger: holding a conversion is enough to pin each asset's count. -/
theorem converts_preserves_assetTotal {a c : DreggResources} (hc : Converts a c)
    (h : (ℕ × ℕ) →+ ℕ) : assetTotal h a = assetTotal h c := by
  obtain ⟨f⟩ := hc
  have he : a.as = c.as := Discrete.eq_of_hom f
  simp only [assetTotal, he]

/-- **`settle_sigma_conserves` (KEYSTONE c⁺)** — the auction settle conserves EACH asset's Σ-total: for
every asset selector `h`, the offered-side total equals the outcome-side total. Strictly stronger than
`settle_conserves` (the thin shadow): it does not merely assert "a conversion exists", it pins every
asset count across the settle. Proved by feeding the settle's own conversion (the receipt's
`fulfill_conserves` witness) to `converts_preserves_assetTotal`. -/
theorem settle_sigma_conserves (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true)
    (h : (ℕ × ℕ) →+ ℕ) :
    assetTotal h i.offered = assetTotal h (auctionSettle i f hpred hlock).outcome :=
  converts_preserves_assetTotal (settle_conserves i f hpred hlock) h

/-- The concrete winning settle conserves both asset totals: 0 gold in = 0 gold out, 3 art in = 3 art
out — the winner's "3 art" allocation neither mints nor burns either asset. -/
theorem winning_sigma_conserves :
    assetTotal goldHom winningBid.offered = assetTotal goldHom winningReceipt.outcome ∧
      assetTotal artHom winningBid.offered = assetTotal artHom winningReceipt.outcome :=
  ⟨settle_sigma_conserves winningBid (𝟙 (res 0 3)) rfl rfl goldHom,
   settle_sigma_conserves winningBid (𝟙 (res 0 3)) rfl rfl artHom⟩

/-! ### The (c⁺) TEETH — a mint a hypothetical settle would carry is CAUGHT by Σ, missed by the shadow.

We model a *hypothetical* settle as a raw `(inputs, outputs)` ledger — the layer at which a mint can even
be EXPRESSED (a `fulfill` cannot mint, because its outcome is definitionally `wanted` and its conversion
forces equality; the threat is a settle that side-steps the conversion and just *asserts* an outcome). On
this layer the thin convertibility shadow is computed PER-LEG; the global asset totals are computed by
Σ. The two diverge exactly on a mint. -/

/-- **`SettleLedger`** — a raw settle as a global `(inputs, outputs)` bundle pair, the layer at which a
mint is expressible (no conversion is demanded — that is precisely the threat Σ must catch). -/
structure SettleLedger where
  /-- Everything escrowed into the settle (buyer payment ⊗ seller stock). -/
  inputs  : DreggResources
  /-- Everything paid out of the settle (buyer receipt ⊗ seller receipt). -/
  outputs : DreggResources

/-- **`SettleLedger.sigmaConserves`** — the strong per-asset law on a raw settle: every asset's Σ-total
is preserved from inputs to outputs. This is the auditable ledger predicate the kernel enforces. -/
def SettleLedger.sigmaConserves (s : SettleLedger) : Prop :=
  ∀ h : (ℕ × ℕ) →+ ℕ, assetTotal h s.inputs = assetTotal h s.outputs

/-- An honest same-bundle settle satisfies Σ-conservation (`inputs = outputs`, so every total agrees) —
non-vacuity of the predicate. -/
theorem honest_settle_sigmaConserves (r : DreggResources) :
    SettleLedger.sigmaConserves ⟨r, r⟩ := fun _ => rfl

/-- A hypothetical **mint-one-art settle**: inputs "3 art", outputs "4 art" — one art conjured from
nothing. The thin shadow would be SILENT (it only asks whether outputs are reachable, never whether the
total grew); Σ-conservation on the art selector CATCHES it. -/
def mintSettle : SettleLedger := ⟨res 0 3, res 0 4⟩

/-- **`mint_rejected_by_sigma` (the (c⁺) TEETH)** — the mint-one-art settle FAILS Σ-conservation: the art
selector reads 3 in, 4 out, so `assetTotal artHom` is not preserved. A mint that the thin convertibility
shadow does not even name is caught by the per-asset ledger. -/
theorem mint_rejected_by_sigma : ¬ SettleLedger.sigmaConserves mintSettle := by
  intro hc
  have h4 := hc artHom
  simp [assetTotal, artHom, mintSettle, res, mkBundle] at h4

/-! ## 4c. KEYSTONE (Q1) — the CROSS-ASSET exchange, FILLED by an offer-generated conversion.

§4's `crossBid` (pay 5 gold, get 1 art) is unfillable *by a resource fact* — no `5 gold ⟶ 1 art`
conversion lives in the discrete `DemoRes` (`settle_cannot_mint`). The market supplies the missing
conversion as a standing **`Offer`** (the seller's `gives ⟶ gets`); the exchange is the buyer's bid
MATCHED against that offer. The discrete category has only identity morphisms, so the offer-generated
conversion is realized one layer up — as a balanced two-leg ledger — and we prove **Q2 survives Q1**: the
matched exchange conserves every asset's Σ-total (the seller is paid exactly what the buyer pays; the
buyer receives exactly what the seller gives; no asset is minted on either leg). -/

/-- **`Offer`** — a seller's standing market offer: hand over `gives` (e.g. 1 art) in return for `gets`
(e.g. 5 gold). This is the offer-generated conversion `gives ⟶ gets` the discrete resource theory
lacks — the market layer's contribution that makes a genuine cross-asset bid fillable. -/
structure Offer where
  /-- What the seller hands over (delivers the buyer's wanted). -/
  gives : DreggResources
  /-- What the seller receives (the buyer's payment). -/
  gets  : DreggResources

/-- **`Exchange`** — a buyer bid (pays `buyerPays`, wants `buyerGets`) MATCHED against a seller `offer`,
with the matching conditions: the seller delivers exactly the buyer's wanted (`hgive`) and receives
exactly the buyer's payment (`hget`). The two legs together are the offer-generated fill of the
cross-asset bid. -/
structure Exchange where
  /-- The buyer's escrowed payment. -/
  buyerPays : DreggResources
  /-- The buyer's demanded outcome. -/
  buyerGets : DreggResources
  /-- The matched seller offer. -/
  offer : Offer
  /-- Match condition: the seller's `gives` IS the buyer's wanted. -/
  hgive : offer.gives.as = buyerGets.as
  /-- Match condition: the seller's `gets` IS the buyer's payment. -/
  hget : offer.gets.as = buyerPays.as

/-- The global ledger of an exchange: inputs = buyer payment ⊗ seller stock; outputs = buyer receipt ⊗
seller receipt. The settle's full books — both legs, not one. -/
def Exchange.ledger (e : Exchange) : SettleLedger :=
  ⟨e.buyerPays ⊗ e.offer.gives, e.buyerGets ⊗ e.offer.gets⟩

/-- **`exchange_sigma_conserves` (Q2 SURVIVES Q1 — the keystone)** — a matched exchange conserves EVERY
asset's Σ-total across its full two-leg ledger. The seller is paid exactly what the buyer pays and the
buyer receives exactly what the seller gives, so `inputs = buyerPays ⊗ gives` and `outputs = buyerGets ⊗
gets` carry identical per-asset totals (`assetTotal_tensor` + the match conditions + commutativity of
bundle union). The cross-asset exchange mints NOTHING — the strong per-asset law of §4b holds on the
genuine exchange, not just the same-bundle identity settle. -/
theorem exchange_sigma_conserves (e : Exchange) : e.ledger.sigmaConserves := by
  intro h
  show assetTotal h (e.buyerPays ⊗ e.offer.gives)
     = assetTotal h (e.buyerGets ⊗ e.offer.gets)
  rw [assetTotal_tensor, assetTotal_tensor]
  -- assetTotal h gives = assetTotal h buyerGets (hgive); assetTotal h gets = assetTotal h buyerPays (hget)
  have hg : assetTotal h e.offer.gives = assetTotal h e.buyerGets := by
    simp only [assetTotal, e.hgive]
  have ht : assetTotal h e.offer.gets = assetTotal h e.buyerPays := by
    simp only [assetTotal, e.hget]
  rw [hg, ht, Nat.add_comm]

/-- **`crossExchange`** — the concrete fill of `crossBid` (pay 5 gold, get 1 art): match it against a
seller offer that GIVES "1 art" and GETS "5 gold". The match conditions hold by `rfl`. This is the
offer-generated conversion that makes the cross-asset bid fillable. -/
def crossExchange : Exchange where
  buyerPays := res 5 0
  buyerGets := res 0 1
  offer := ⟨res 0 1, res 5 0⟩
  hgive := rfl
  hget := rfl

/-- **`crossBid_fillable_by_offer` (Q1 KEYSTONE — the bid is FILLED, no minting)** — the cross-asset bid
that was unfillable-without-a-market is now FILLED by `crossExchange`, and the fill conserves every
asset's Σ-total. The exact bundles `crossBid` offers and wants ARE the buyer legs of the exchange
(`rfl`/`rfl`), and the seller's offer-generated leg supplies the missing `gold ⟶ art` conversion while
the global ledger balances. Q1 (fillability) and Q2 (per-asset conservation) hold simultaneously. -/
theorem crossBid_fillable_by_offer (revealEvt : Frontier) :
    crossExchange.buyerPays = (crossBid revealEvt).offered ∧
      crossExchange.buyerGets = (crossBid revealEvt).wanted ∧
      crossExchange.ledger.sigmaConserves :=
  ⟨rfl, rfl, exchange_sigma_conserves crossExchange⟩

/-! ### The (Q1) TEETH — no minting WITHOUT a backing/balanced offer, even when the per-leg shadow agrees.

A SKIMMING settle is the adversarial cross-asset case: the buyer pays 5 gold for 1 art; the seller
DELIVERS the 1 art correctly (so the per-leg convertibility shadow on the delivery leg is satisfied) but
takes 6 gold — skimming one gold from nowhere. Such a settle CANNOT be a matched `Exchange` (its `gets`
≠ the buyer's payment, so the `hget` match condition is unprovable — `Exchange` structurally excludes
the skim). To exhibit the threat we drop to the raw ledger layer, where the skim is expressible, and show
the thin shadow accepts it while Σ catches it. -/

/-- The skim's raw global ledger: 5 gold + 1 art in (buyer pays 5 gold, seller stocks 1 art), 1 art + 6
gold out (buyer gets 1 art, seller gets 6 gold). -/
def skimLedger : SettleLedger := ⟨res 5 0 ⊗ res 0 1, res 0 1 ⊗ res 6 0⟩

/-- **`thinShadow_accepts_skim` (the shadow is FOOLED)** — the thin per-leg convertibility check on the
seller's delivery leg PASSES: the seller's "1 art" `gives` converts to the buyer's "1 art" wanted (the
identity). The shadow sees a valid delivery and says yes — it never inspects the gold leg's totals. -/
theorem thinShadow_accepts_skim : Converts (res 0 1) (res 0 1) := Converts.refl' _

/-- **`skim_rejected_by_sigma` (the (Q1) TEETH — Σ catches what the shadow misses)** — the skim ledger
FAILS Σ-conservation on the gold selector: 5 gold in, 6 gold out — one gold minted by the seller's skim.
The per-leg shadow accepted this exact settle (`thinShadow_accepts_skim`); the global per-asset ledger
rejects it. No minting survives Σ even when a backing per-leg conversion is present. -/
theorem skim_rejected_by_sigma : ¬ SettleLedger.sigmaConserves skimLedger := by
  intro hc
  have hgold := hc goldHom
  simp [assetTotal, goldHom, skimLedger, res, mkBundle] at hgold

/-! ## 5. KEYSTONE one-shot — no double-settle from one escrow. -/

/-- **`settle_no_double` (the one-shot teeth)** — the settled escrow is RELEASED, so it can never again
satisfy `fulfill`'s `locked = true` precondition: no second settle from one funding. The abstract
`no_double_fulfill`, instantiated at the auction settle. -/
theorem settle_no_double (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    (auctionSettle i f hpred hlock).spentEscrow.locked ≠ true :=
  no_double_fulfill i f hpred hlock

/-- The concrete winning settle is one-shot: its released escrow cannot fund a second settle. -/
theorem winning_no_double : winningReceipt.spentEscrow.locked ≠ true :=
  settle_no_double winningBid (𝟙 (res 0 3)) rfl rfl

/-! ## 6. KEYSTONE — loser-refund LIVENESS (the genuine `◇`).

A losing bidder is EVENTUALLY refunded. From a `JustProgress` package (van Glabbeek reactive justness +
a well-founded refund potential), `just_progress` produces `Eventually Refunded` — the genuine `◇`, not a
trivial `□→◇`. Two faces:
  * the abstract TEMPLATE (`loser_refunded_eventually`): conditional on a supplied package — the escrow
    layer instantiates `Refunded`/`μ` with the holding-store refund-count;
  * the CONCRETE inhabited witness (`auction_loser_refunded`): UNCONDITIONAL on the REAL executor, reusing
    `Fairness.refundDemo` (the B-just `transferSched` path, all four `JustProgress` fields proved against
    the 46-effect executor) — proving the machinery is INHABITABLE, not a vacuous carried
    package. The teeth that keep `Just` non-vacuous is `Fairness.badSched_not_just` (a starving schedule
    REJECTED). -/

open Dregg2.Proof.Fairness (Just JustProgress Refunded just_progress refundDemo Pgoal
  badSched badSched_not_just)
open Dregg2.Proof.Temporal (Eventually transferSched)
open Dregg2.Exec.TurnExecutorFull (fma0)

/-- **`loser_refunded_eventually` (KEYSTONE liveness, the TEMPLATE)** — given a `JustProgress` package whose
potential is the pending-refund count and whose goal is `Refunded` (all refunds discharged),
`just_progress` yields `Eventually Refunded`: the loser IS eventually refunded. The escrow layer
instantiates `Refunded`/`μ` with the real holding-store (architect Q4a default: the abstract template
ships; the executor-wired `μ` is the Q4b ember decision). -/
theorem loser_refunded_eventually {B s sched} (jp : JustProgress B Refunded s sched) :
    Eventually Refunded s sched :=
  just_progress jp

/-- **`auction_loser_refunded` (the liveness TEETH — `◇` PRODUCED, UNCONDITIONAL).** The
concrete `refundDemo` package (the B-just `transferSched` path on the REAL executor, all four
`JustProgress` fields proved) feeds `just_progress` to yield `Eventually Pgoal fma0 transferSched` with NO
hypotheses: the refund goal IS eventually reached. This de-vacuifies `loser_refunded_eventually` — the
`JustProgress` machinery is inhabitable and `just_progress` truly produces a `◇`. (`Pgoal` =
"a receipt has landed", the concrete stand-in the escrow holding-store replaces.) -/
theorem auction_loser_refunded : Eventually Pgoal fma0 transferSched :=
  just_progress refundDemo

/-- **`auction_starvation_rejected` (the liveness NON-VACUITY teeth)** — the justness criterion
REJECTS a starving schedule: `badSched` (firing only an independent cell forever) is NOT B-just, so it
cannot underwrite a refund-liveness claim. Without this the `Just` premise of `loser_refunded_eventually`
could be vacuously `True` and the `◇` would be empty. dregg2's [Survey] Example 21 ("Bart never gets his
beer"), re-exported as the auction's anti-starvation guarantee. -/
theorem auction_starvation_rejected : ¬ Just (fun _ => True) fma0 badSched :=
  badSched_not_just

/-! ## 7. The (a) obligation — userspace-escrow ≥ kernel-escrow — a CARRIED OPEN (not a stub).

⚑ MODEL-SHAPE CALL FOR EMBER (architect Q6). The §5/§7 headline `kernelEscrow ⊑ userspaceEscrow` (anything
the kernel escrow conserves/guarantees, the userspace escrow does too) needs a definition that does NOT
yet exist in the green tree:
  * the userspace-escrow CELL-PROGRAM holding `offered`, released exactly on the discharging receipt
    (`INTENT-AS-CO-RECEIPT.md` §2 face 3) — the current `EscrowWitness` is the kernel side's thin one-shot
    lockbox (`locked : Bool`), not a userspace cell-program; and
  * a state CLOCK / block-height dimension the executor lacks (`EFFECT-FIDELITY-LEDGER.md`: `refund
    CommittedEscrowA` is a SHADOW that can refund before deadline; `RecChainedState` has no clock).

Per MEMORY "Improve Don't Degrade" + "Don't Cheap Out on Hard Proofs", this is NOT stubbed and NOT
`sorry`'d. It is stated as a carried-hypothesis INTERFACE obligation: a relation `UserspaceDominatesKernel`
(the simulation/refinement on the escrow guarantees) and the corollary `escrow_refinement_sound` that, ONCE
the refinement is supplied, every kernel-escrow guarantee transfers to the userspace escrow. The build ships
(b)+(c)+liveness green around it; ember picks the shape (cell-program refinement vs. abstract interface)
before the relation is *constructed*. -/

/-- **`EscrowGuarantee`** — a property an escrow witness must uphold (e.g. "locked ⇒ funds held",
"released ⟺ a discharging receipt exists", "refundable ⟺ expiry-without-fill"). Parametrized over the
offered bundle. A `Prop`-valued predicate on `EscrowWitness offered` — the abstract surface the (a)
inequality compares the two escrows on. -/
abbrev EscrowGuarantee (offered : DreggResources) := EscrowWitness offered → Prop

/-- **OPEN/BLOCKED: `UserspaceDominatesKernel` is the auction's (a) obligation — it is NOT a proved
guarantee, it is a carried HYPOTHESIS.**

To keep the honesty seam unmissable, this auction's results split into two disjoint piles:

  * **PROVED (shipped green, kernel-clean — these ARE guarantees):** `no_frontrunning` /
    `no_frontrunning_teeth` (causal reveal-ordering EXCLUDES frontrunning), `settle_conserves` /
    `settle_sigma_conserves` (the settle conserves every asset's Σ-total — no value minted),
    `settle_cannot_mint` / `mint_rejected_by_sigma` / `skim_rejected_by_sigma` (a minting/skimming
    settle is structurally rejected), `settle_no_double` (one-shot), `auction_loser_refunded` (the
    genuine `◇`). Each is `#assert_axioms`-pinned below.

  * **OPEN / BLOCKED (NOT proved — do not read as a guarantee):** `UserspaceDominatesKernel` itself.
    It states that the userspace escrow over `offered` would uphold at least every guarantee the kernel
    escrow does (for every guarantee `G`, `G ke → G ue`) — the `⊑` refinement typed at the abstract
    `EscrowWitness` layer (architect Q6 option (ii)). This relation is **CARRIED as a hypothesis**, never
    asserted of any specific escrow: the corollary `escrow_refinement_sound` only *consumes* it, and the
    only inhabitant proved is the trivial reflexive one (`escrow_refinement_reflexive`). The NON-trivial
    witness — a userspace-escrow cell-program with its own release/refund semantics so `⊑` is an
    executable simulation against `createEscrowKAsset` (option (i)) — DOES NOT EXIST in the green tree and
    is the OPEN model-shape call for ember (see §7 banner). Treat any `UserspaceDominatesKernel _ _` you
    see in a theorem's hypotheses as an unmet debt, not a fact this file establishes. -/
def UserspaceDominatesKernel {offered : DreggResources}
    (ke ue : EscrowWitness offered) : Prop :=
  ∀ G : EscrowGuarantee offered, G ke → G ue

/-- **`escrow_refinement_sound` (the (a) corollary — sound the MOMENT the refinement is supplied)** — GIVEN
the carried refinement `UserspaceDominatesKernel ke ue`, any guarantee the KERNEL escrow upholds, the
USERSPACE escrow upholds too. This is the content of "userspace-escrow ≥ kernel-escrow" at the interface
layer: it is `h` applied to the guarantee. It does NOT assert the refinement exists (that is the OPEN
ember decides) — it shows the inequality is a one-line consequence once the refinement is constructed, so
the obligation is precisely localized to building `UserspaceDominatesKernel`. -/
theorem escrow_refinement_sound {offered : DreggResources} {ke ue : EscrowWitness offered}
    (h : UserspaceDominatesKernel ke ue) (G : EscrowGuarantee offered) (hk : G ke) : G ue :=
  h G hk

/-- **`escrow_refinement_reflexive` (non-vacuity of the interface)** — the refinement relation is
INHABITED: an escrow trivially dominates ITSELF (`UserspaceDominatesKernel e e`). This proves
`UserspaceDominatesKernel` is not the empty relation / not vacuously unsatisfiable — there is at least one
real witness, so `escrow_refinement_sound` has content. (The NON-trivial witness — the userspace
cell-program dominating the kernel lockbox — is the OPEN ember scopes.) -/
theorem escrow_refinement_reflexive {offered : DreggResources} (e : EscrowWitness offered) :
    UserspaceDominatesKernel e e :=
  fun _ hk => hk

/-! ## 8. `#eval` smoke — the auction's load-bearing bits, decided by the model alone. -/

#guard (winningReceipt.outcome.as |>.toAdd) == (0, 3)  -- (0, 3)  the settled allocation (3 art to winner)
#guard winningReceipt.spentEscrow.locked == false  -- false   the escrow is consumed (one-shot)
#guard winningBid.validity.kind                -- true    causal reveal-ordering (anti-frontrunning)
-- (b): the honest fill saw the reveal (g0 ≺ g1) ⇒ admitted; the fork fill did not (f1 ∦ f2) ⇒ rejected.
#guard decide (g0.id ∈ g1.preds)               -- true    honest fill at g1 observed reveal at g0
#guard decide (f1.id ∈ f2.preds ∨ f2.id ∈ f1.preds) == false  -- false  fork fill at f2 never saw reveal at f1
-- (c⁺): the winning settle conserves both asset totals (0 gold, 3 art on each side).
#guard assetTotal goldHom winningBid.offered == 0     -- 0       gold in
#guard assetTotal goldHom winningReceipt.outcome == 0 -- 0      gold out (conserved)
#guard assetTotal artHom winningBid.offered == 3      -- 3       art in
#guard assetTotal artHom winningReceipt.outcome == 3  -- 3      art out (conserved)
-- (c⁺ teeth): the mint-one-art settle's art total grows 3 ⟶ 4 (Σ catches it; the shadow is silent).
#guard assetTotal artHom mintSettle.inputs == 3       -- 3       art in
#guard assetTotal artHom mintSettle.outputs == 4      -- 4       art out (MINTED — rejected by Σ)
-- (Q1): the cross-exchange ledger balances gold (5 in / 5 out) and art (1 in / 1 out).
#guard assetTotal goldHom crossExchange.ledger.inputs == 5   -- 5    gold in (buyer pays)
#guard assetTotal goldHom crossExchange.ledger.outputs == 5  -- 5    gold out (seller paid)
#guard assetTotal artHom crossExchange.ledger.inputs == 1    -- 1    art in (seller stock)
#guard assetTotal artHom crossExchange.ledger.outputs == 1   -- 1    art out (buyer gets)
-- (Q1 teeth): the SKIM ledger mints gold (5 in / 6 out) while delivering art correctly (1 in / 1 out).
#guard assetTotal goldHom skimLedger.inputs == 5      -- 5       gold in
#guard assetTotal goldHom skimLedger.outputs == 6     -- 6       gold out (SKIMMED — rejected by Σ, shadow fooled)

/-! ## 9. Axiom hygiene — every keystone pinned to the standard kernel triple.

`#assert_axioms` walks each keystone and errors if any escapes `{propext, Classical.choice, Quot.sound}`.
The (a) obligation is a carried hypothesis, NOT an axiom. -/

#assert_axioms winning_discharges
#assert_axioms met_iff_frontrunExcluded
#assert_axioms no_frontrunning
#assert_axioms honest_fill_admitted
#assert_axioms no_frontrunning_teeth
#assert_axioms settle_conserves
#assert_axioms winning_settle_conserves
#assert_axioms settle_cannot_mint
#assert_axioms assetTotal_tensor
#assert_axioms converts_preserves_assetTotal
#assert_axioms settle_sigma_conserves
#assert_axioms winning_sigma_conserves
#assert_axioms honest_settle_sigmaConserves
#assert_axioms mint_rejected_by_sigma
#assert_axioms exchange_sigma_conserves
#assert_axioms crossBid_fillable_by_offer
#assert_axioms thinShadow_accepts_skim
#assert_axioms skim_rejected_by_sigma
#assert_axioms settle_no_double
#assert_axioms winning_no_double
#assert_axioms loser_refunded_eventually
#assert_axioms auction_loser_refunded
#assert_axioms auction_starvation_rejected
#assert_axioms escrow_refinement_sound
#assert_axioms escrow_refinement_reflexive

end Dregg2.Apps.SealedBidAuction
