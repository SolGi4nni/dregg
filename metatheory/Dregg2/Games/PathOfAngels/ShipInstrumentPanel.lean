/-
# ShipInstrumentPanel — the one ship state an ordinary day can move

PLATFORM-ROADMAP §7.3 pairs two rows.  *Salvage crate* — "open a precommitted
daily table" — is the ritual, and it already exists as `SalvageCrate`.  *Ship
instrument panel* — "see contribution-driven states in-world", authority output
**none**, technical exercise **exact aggregate projection** — is what the ritual
is supposed to move, and until now it did not exist, so an accepted opening's
`Contribution` was computed, proved exact, and then dropped on the floor.

This module is that panel.  It is **communal**: one face for the whole
Khovokhi, not a career page.  You come back and the bins are fuller than you
left them, and you did not fill them yourself.

## Where the authority actually lives

Not here.  The only thing that can move this panel is a
`SalvageCrate.OpenReceipt`, whose constructor is private to `SalvageCrate` and
whose only producer is `OpenResult.receipt` — and an `OpenResult` can only be
minted by the crate's own transition core under a `CurrentStateCapability`.
This module owns no balance, no custody, no eligibility and no draw.  It has
exactly two state producers, `initial` and `observe`, `State.mk` is private, and
`observe` cannot be called without a receipt.  Every displayed number is a
projection of one `Contribution` that some authority already proved.

`observe` adds *exactly* the receipt's contribution (`observe_adds_exactly_the_receipt`),
using `Contribution.merge`, which refuses on overflow rather than saturating.
A bound reached is a refusal, never a silently clipped meter.

## The design law, as theorems rather than as a comment

The roadmap says the crate's "scarcity and rewards should remain low enough that
missing a day is uninteresting".  Two theorems here are that sentence:

* `an_ordinary_day_moves_no_gauge` — the overwhelmingly common outcome (packing
  foam, a sticker, warm air: `Contribution.zero`) provably leaves every gauge and
  the recovered-salvage set bit-identical.  Showing up on an ordinary day and
  not showing up at all are the same ship.
* `the_face_does_not_record_who_opened` — two different crew members drawing the
  same ticket leave identical faces.  The panel has no per-player field, so no
  leaderboard, streak, or attendance record can be read off it.  Its companion
  `the_same_crew_member_cannot_be_counted_twice` shows this is not achieved by
  dropping people: the replay key keeps crew apart, it just never displays them.
* `the_order_the_crew_arrives_does_not_change_the_face` — whoever reached the
  reclamation desk first, the ship reads the same.

## Say plainly what the draw is

`SalvageCrate`'s own docblock is explicit and this module does not soften it:
the mixer is **additive and is not an unpredictability source**, and the beacon
schedule is **curator-authored and visible**, so a player may precompute their
whole rotation (`SalvageCrate.generatedRotation` hands it to them deliberately).
This is a **visible rotation, not a hidden instance** — unlike the three arcade
games, which use `HiddenInstance`/`SlotDeriveRuntime`.  That is fine here only
because the panel is communal and unattributed: knowing which day you would draw
salvage buys you nothing, because there is nothing personal to buy.  If anything
attributable is ever hung off this panel, the visible rotation stops being fine.

## What this module does NOT prove

`the_order_the_crew_arrives_does_not_change_the_face` assumes **both** orders
were accepted and concludes they agree.  That both orders always succeed or
always fail together is true (`Nat` addition is monotone, so an outer bound
implies the inner one) but is **not proved here**.
-/
import Dregg2.Games.PathOfAngels.SalvageCrate
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ShipInstrumentPanel

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev MAX_GAUGES : Nat := 16
abbrev MAX_OBSERVED : Nat := 4096

/-! ## The authored panel -/

/-- The five shared meters `Contribution` already carries.  This module adds no
sixth meter, because adding one would mean inventing a resource. -/
inductive Meter where
  | intel
  | supplies
  | cohesion
  | influence
  | score
deriving Repr, DecidableEq

def Meter.valueIn : Meter → Contribution → Nat
  | .intel, c => c.intel.val
  | .supplies, c => c.supplies.val
  | .cohesion, c => c.cohesion.val
  | .influence, c => c.influence.val
  | .score, c => c.score.val

structure GaugeId where
  value : Nat
deriving Repr, DecidableEq

/-- One dial. `fullAt` is an authored *display* scale only: it is where the
needle stops moving on screen, never where the arithmetic stops. -/
structure Gauge where
  id : GaugeId
  meter : Meter
  fullAt : Nat
deriving Repr, DecidableEq

/-- Fiction (which dial is "reclamation bins" and which is "deck plating") lives
in content, not in Lean.  This layer authors ids, meters and scales. -/
structure RawPanel where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  gauges : List Gauge
  capacity : Nat
deriving DecidableEq

def panelValidB (raw : RawPanel) : Bool :=
  decide (0 < raw.gauges.length) &&
  decide (raw.gauges.length ≤ MAX_GAUGES) &&
  decide (raw.gauges.map Gauge.id).Nodup &&
  raw.gauges.all (fun gauge =>
    decide (0 < gauge.fullAt) && decide (gauge.fullAt ≤ METRIC_LIMIT)) &&
  decide (0 < raw.capacity) &&
  decide (raw.capacity ≤ MAX_OBSERVED)

structure Panel where
  raw : RawPanel
  valid : panelValidB raw = true

/-! ## Receipts — the only thing that can move the panel -/

/-- Which authority produced the receipt.  The crate is the first; Shipworks and
the Galley daily are the obvious next two, and each must publish its own sealed
receipt type before it appears here. -/
inductive Source where
  | salvageCrate
deriving Repr, DecidableEq

/-- The replay key.  `subject` is carried so two crew members on the same day are
kept apart — and it is deliberately absent from everything the panel displays. -/
structure ReceiptKey where
  source : Source
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  period : EpochId
  subject : Digest32
deriving DecidableEq

def ReceiptKey.deploymentMatchesB (key : ReceiptKey) (raw : RawPanel) : Bool :=
  decide (key.federationId = raw.federationId) &&
  decide (key.contentSession = raw.contentSession) &&
  decide (key.contentEpoch = raw.contentEpoch)

/-- Private constructor: the panel cannot mint its own input.  The only public
producer is `ofSalvageOpen`, which consumes a `SalvageCrate.OpenReceipt`. -/
structure Receipt where
  private mk ::
  key : ReceiptKey
  contribution : Contribution
deriving DecidableEq

/-- The weld.  Every field is copied from the crate's sealed receipt; the
theorems below cite the crate's own exactness proofs rather than this
definition. -/
def ofSalvageOpen (receipt : SalvageCrate.OpenReceipt) : Receipt where
  key :=
    { source := .salvageCrate
      federationId := receipt.federationId
      contentSession := receipt.contentSession
      contentEpoch := receipt.contentEpoch
      period := receipt.period
      subject := receipt.player }
  contribution := receipt.contribution

/-- The number the panel adds is the authored loot-table row's contribution. No
runtime, adapter or projection chose it. -/
theorem welded_contribution_is_the_authored_table_row {config : SalvageCrate.Config}
    {envelope : SalvageCrate.OpenEnvelope}
    (result : SalvageCrate.OpenResult config envelope) :
    (ofSalvageOpen result.receipt).contribution = result.entry.contribution :=
  result.contribution_exact

/-- The replay key's subject is the player the envelope was signed for. -/
theorem welded_subject_is_the_signed_player {config : SalvageCrate.Config}
    {envelope : SalvageCrate.OpenEnvelope}
    (result : SalvageCrate.OpenResult config envelope) :
    (ofSalvageOpen result.receipt).key.subject = envelope.player :=
  result.player_exact

/-- The replay key's period is the period the crate actually consumed, so
`alreadyObserved` defends the same day the crate closed. -/
theorem welded_period_is_the_consumed_period {config : SalvageCrate.Config}
    {envelope : SalvageCrate.OpenEnvelope}
    (result : SalvageCrate.OpenResult config envelope) :
    (ofSalvageOpen result.receipt).key.period = envelope.expectedPeriod :=
  result.period_exact

/-! ## State and its one transition -/

/-- Every field is either a replay index or the exact merged total.  There is no
per-player row, no streak, no last-seen epoch, and no decay. -/
structure State where
  private mk ::
  panelIdentity : RawPanel
  total : Contribution
  observed : Finset ReceiptKey
  admitted : Nat
deriving DecidableEq

def initial (panel : Panel) : State where
  panelIdentity := panel.raw
  total := Contribution.zero
  observed := ∅
  admitted := 0

/-- Five reasons, all of them fired by a fixture at the bottom of this file. -/
inductive Refusal where
  | panelIdentityMismatch
  | foreignDeployment
  | alreadyObserved
  | capacityReached
  | meterOverflow
deriving Repr, DecidableEq

/-- Everything decidable before any arithmetic happens.  Kept separate so the
refusal precedence is readable and so `observe`'s conservation proof does not
have to case over an if-chain. -/
def refusalBefore (panel : Panel) (state : State) (receipt : Receipt) :
    Option Refusal :=
  if state.panelIdentity ≠ panel.raw then some .panelIdentityMismatch
  else if receipt.key.deploymentMatchesB panel.raw ≠ true then some .foreignDeployment
  else if receipt.key ∈ state.observed then some .alreadyObserved
  else if panel.raw.capacity ≤ state.observed.card then some .capacityReached
  else none

def observe (panel : Panel) (state : State) (receipt : Receipt) :
    Except Refusal State :=
  match refusalBefore panel state receipt with
  | some refusal => .error refusal
  | none =>
      match Contribution.merge state.total receipt.contribution with
      | none => .error .meterOverflow
      | some total =>
          .ok { panelIdentity := state.panelIdentity
                total := total
                observed := insert receipt.key state.observed
                admitted := state.admitted + 1 }

/-! ## The face — a pure function of the total, and of nothing else -/

/-- `exactTotal` is the unclipped arithmetic.  `shown` is the needle. Keeping
both means the display scale can never quietly become the bound. -/
structure Reading where
  gauge : GaugeId
  meter : Meter
  exactTotal : Nat
  fullAt : Nat
  shown : Nat
  atFull : Bool
deriving Repr, DecidableEq

def readingOf (total : Contribution) (gauge : Gauge) : Reading where
  gauge := gauge.id
  meter := gauge.meter
  exactTotal := gauge.meter.valueIn total
  fullAt := gauge.fullAt
  shown := min (gauge.meter.valueIn total) gauge.fullAt
  atFull := decide (gauge.fullAt ≤ gauge.meter.valueIn total)

def readings (panel : Panel) (total : Contribution) : List Reading :=
  panel.raw.gauges.map (readingOf total)

/-- The whole visible ship. It reads `total` and nothing else — not `observed`,
not `admitted`, not the identity. -/
def State.face (state : State) (panel : Panel) : List Reading :=
  readings panel state.total

/-- Which kinds of salvage the crew has recovered, as a set: ten people
recovering the same kind is one entry, which is what "kinds" means. -/
def State.recovered (state : State) : Finset RelicId := state.total.relics

/-! ## Exact arithmetic -/

/-- Everything a successful merge determines, in one place.  Mirrors the proof
shape of `Contribution.merge_intel_exact`. -/
theorem mergeExact {a b c : Contribution} (merged : Contribution.merge a b = some c) :
    c.intel.val = a.intel.val + b.intel.val ∧
    c.supplies.val = a.supplies.val + b.supplies.val ∧
    c.cohesion.val = a.cohesion.val + b.cohesion.val ∧
    c.influence.val = a.influence.val + b.influence.val ∧
    c.score.val = a.score.val + b.score.val ∧
    c.relics = a.relics ∪ b.relics := by
  simp only [Contribution.merge, checkedAddMetric] at merged
  split_ifs at merged <;> try contradiction
  cases merged
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Conservation.  The panel's new total is EXACTLY the checked sum of its old
total and the receipt: nothing invented, nothing lost, nothing clipped. -/
theorem observe_adds_exactly_the_receipt {panel : Panel} {state : State}
    {receipt : Receipt} {after : State}
    (accepted : observe panel state receipt = .ok after) :
    Contribution.merge state.total receipt.contribution = some after.total := by
  unfold observe at accepted
  split at accepted
  · simp at accepted
  · split at accepted
    · simp at accepted
    · rename_i merged
      cases accepted
      exact merged

theorem readings_eq_of_meters (panel : Panel) {x y : Contribution}
    (agree : ∀ meter : Meter, meter.valueIn x = meter.valueIn y) :
    readings panel x = readings panel y := by
  simp only [readings]
  apply List.map_congr_left
  intro gauge _
  simp [readingOf, agree gauge.meter]

/-! ## The design law -/

/-- ⭐ An ordinary day moves nothing.  The common outcomes carry
`Contribution.zero`, so a crew member who opened the crate and got packing foam
leaves the ship bit-identical to one who never came.  This is the roadmap's
"missing a day is uninteresting" as a theorem rather than as a promise. -/
theorem an_ordinary_day_moves_no_gauge {panel : Panel} {state : State}
    {receipt : Receipt} {after : State}
    (ordinary : receipt.contribution = Contribution.zero)
    (accepted : observe panel state receipt = .ok after) :
    after.face panel = state.face panel ∧ after.recovered = state.recovered := by
  have merged := observe_adds_exactly_the_receipt accepted
  rw [ordinary] at merged
  obtain ⟨hintel, hsupplies, hcohesion, hinfluence, hscore, hrelics⟩ := mergeExact merged
  refine ⟨readings_eq_of_meters panel ?_, ?_⟩
  · intro meter
    cases meter <;>
      simp only [Meter.valueIn, hintel, hsupplies, hcohesion, hinfluence, hscore,
        Contribution.zero, Fin.val_zero, Nat.add_zero]
  · simp only [State.recovered, hrelics, Contribution.zero, Finset.union_empty]

/-- ⭐ The panel does not know who opened the crate.  Two different crew members
drawing the same ticket leave identical faces, so no attendance record, streak,
or leaderboard can be read off this state. -/
theorem the_face_does_not_record_who_opened {panel : Panel} {state : State}
    {alpha beta : Receipt} {a b : State}
    (sameDraw : alpha.contribution = beta.contribution)
    (acceptedAlpha : observe panel state alpha = .ok a)
    (acceptedBeta : observe panel state beta = .ok b) :
    a.face panel = b.face panel ∧ a.recovered = b.recovered := by
  have mergedAlpha := observe_adds_exactly_the_receipt acceptedAlpha
  have mergedBeta := observe_adds_exactly_the_receipt acceptedBeta
  rw [sameDraw] at mergedAlpha
  have same : a.total = b.total := Option.some.inj (mergedAlpha.symm.trans mergedBeta)
  exact ⟨by simp only [State.face, readings, same],
    by simp only [State.recovered, same]⟩

/-- ⭐ Whoever reached the reclamation desk first, the ship reads the same.
Assumes both orders were accepted; see the module docblock for what that does
not claim. -/
theorem the_order_the_crew_arrives_does_not_change_the_face {panel : Panel}
    {state : State} {alpha beta : Receipt} {alphaFirst betaFirst ab ba : State}
    (stepOne : observe panel state alpha = .ok alphaFirst)
    (stepTwo : observe panel alphaFirst beta = .ok ab)
    (stepOneSwapped : observe panel state beta = .ok betaFirst)
    (stepTwoSwapped : observe panel betaFirst alpha = .ok ba) :
    ab.face panel = ba.face panel ∧ ab.recovered = ba.recovered := by
  obtain ⟨a1, b1, c1, d1, e1, r1⟩ :=
    mergeExact (observe_adds_exactly_the_receipt stepOne)
  obtain ⟨a2, b2, c2, d2, e2, r2⟩ :=
    mergeExact (observe_adds_exactly_the_receipt stepTwo)
  obtain ⟨a3, b3, c3, d3, e3, r3⟩ :=
    mergeExact (observe_adds_exactly_the_receipt stepOneSwapped)
  obtain ⟨a4, b4, c4, d4, e4, r4⟩ :=
    mergeExact (observe_adds_exactly_the_receipt stepTwoSwapped)
  refine ⟨readings_eq_of_meters panel ?_, ?_⟩
  · intro meter
    cases meter <;> simp only [Meter.valueIn] <;> omega
  · simp only [State.recovered]
    rw [r2, r1, r4, r3]
    ext relic
    simp only [Finset.mem_union]
    tauto

/-! ## Private executable hostility laboratory

Two kinds of fixture live here and the difference matters.  The ones named
`lab_*` build a `Receipt` directly through the private constructor to reach
arithmetic corners (an almost-full meter) that the crate's authored table cannot
produce.  The ones named `welded_*` consume `SalvageCrate.fixtureOpenReceipt` —
a REAL accepted opening — so the seam this module actually ships is exercised
rather than a re-typed mirror of it.
-/

private def labDigest (tag : Nat) : Digest32 where
  bytes := List.replicate 32 (SalvageCrate.byte tag)
  length_eq := by simp

/-- Explicit rather than an anonymous constructor: inside a structure instance
the `Metric` bound is not elaborated when a tactic would run, and a tactic that
fails there produces a `sorryAx` that only surfaces as an `unreachable` inside
`native_decide`. -/
private def metricOf (value : Nat) (bounded : value ≤ METRIC_LIMIT) : Metric :=
  ⟨value, Nat.lt_succ_of_le bounded⟩

/-- `omega` treats `METRIC_LIMIT` as an opaque atom rather than unfolding the
abbreviation, so `1 ≤ atom` is not provable there.  `decide` reduces it. -/
private theorem one_le_metric_limit : 1 ≤ METRIC_LIMIT := by decide

/-- Deployed on the crate lab's federation, so the welded witnesses are in
scope.  Reading the fields off the witness avoids re-typing them wrongly. -/
private def labPanelRaw : RawPanel where
  federationId := SalvageCrate.fixtureOpenReceipt.federationId
  contentSession := SalvageCrate.fixtureOpenReceipt.contentSession
  contentEpoch := SalvageCrate.fixtureOpenReceipt.contentEpoch
  gauges :=
    [ { id := ⟨1⟩, meter := .supplies, fullAt := 50 }
    , { id := ⟨2⟩, meter := .cohesion, fullAt := 25 } ]
  capacity := 8

private theorem lab_panel_valid : panelValidB labPanelRaw = true := by native_decide
private def labPanel : Panel := ⟨labPanelRaw, lab_panel_valid⟩

/-- A different ship. -/
private def otherPanelRaw : RawPanel :=
  { labPanelRaw with federationId := labDigest 200 }

private theorem other_panel_valid : panelValidB otherPanelRaw = true := by native_decide
private def otherPanel : Panel := ⟨otherPanelRaw, other_panel_valid⟩

private def tinyPanelRaw : RawPanel := { labPanelRaw with capacity := 1 }
private theorem tiny_panel_valid : panelValidB tinyPanelRaw = true := by native_decide
private def tinyPanel : Panel := ⟨tinyPanelRaw, tiny_panel_valid⟩

private def isOkB {α : Type} (result : Except Refusal α) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

private def refusedWithB {α : Type} (expected : Refusal) (result : Except Refusal α) :
    Bool :=
  match result with
  | .error refusal => decide (refusal = expected)
  | .ok _ => false

private def observeChain (panel : Panel) (state : State) :
    List Receipt → Except Refusal State
  | [] => .ok state
  | receipt :: rest =>
      (match observe panel state receipt with
       | .error refusal => .error refusal
       | .ok next => observeChain panel next rest)

private def labReceipt (crew : Digest32) (day : EpochId) (draw : Contribution) :
    Receipt where
  key :=
    { source := .salvageCrate
      federationId := labPanelRaw.federationId
      contentSession := labPanelRaw.contentSession
      contentEpoch := labPanelRaw.contentEpoch
      period := day
      subject := crew }
  contribution := draw

private def brimming : Contribution where
  intel := 0
  supplies := metricOf METRIC_LIMIT (Nat.le_refl _)
  cohesion := 0
  influence := 0
  score := 0
  relics := ∅
  relics_bounded := by simp

private def oneSupply : Contribution where
  intel := 0
  supplies := metricOf 1 one_le_metric_limit
  cohesion := 0
  influence := 0
  score := 0
  relics := ∅
  relics_bounded := by simp

private def brimmingState : State where
  panelIdentity := labPanelRaw
  total := brimming
  observed := ∅
  admitted := 0

private def foreignState : State where
  panelIdentity := otherPanelRaw
  total := Contribution.zero
  observed := ∅
  admitted := 0

private def alphaWelded : Receipt := ofSalvageOpen SalvageCrate.fixtureOpenReceipt
private def betaWelded : Receipt :=
  ofSalvageOpen SalvageCrate.fixtureOpenReceiptSecondCrew

/-! ### The five declared refusals, each fired -/

theorem lab_state_from_another_panel_refuses :
    refusedWithB .panelIdentityMismatch
      (observe labPanel foreignState alphaWelded) = true := by native_decide

/-- The deliberately public crate lab witness is contained: a panel on any other
federation refuses it, so exposing it cannot move a real ship. -/
theorem welded_lab_witness_is_refused_by_another_deployment :
    refusedWithB .foreignDeployment
      (observe otherPanel (initial otherPanel) alphaWelded) = true := by native_decide

theorem welded_same_crew_member_cannot_be_counted_twice :
    refusedWithB .alreadyObserved
      (observeChain labPanel (initial labPanel) [alphaWelded, alphaWelded]) = true := by
  native_decide

theorem lab_capacity_refuses_rather_than_forgetting_a_receipt :
    refusedWithB .capacityReached
      (observeChain tinyPanel (initial tinyPanel) [alphaWelded, betaWelded]) = true := by
  native_decide

/-- An almost-full meter refuses the next receipt instead of saturating. -/
theorem lab_meter_overflow_refuses_instead_of_clipping :
    refusedWithB .meterOverflow
      (observe labPanel brimmingState (labReceipt (labDigest 7) ⟨12⟩ oneSupply)) = true := by
  native_decide

/-! ### The weld, end to end -/

theorem welded_lab_witness_is_admitted_by_its_own_deployment :
    isOkB (observe labPanel (initial labPanel) alphaWelded) = true := by native_decide

/-- Two crew members opening on the SAME period are both counted.  Together with
`the_face_does_not_record_who_opened` this is the whole social shape: the panel
keeps people apart well enough to count them, and never well enough to rank
them. -/
theorem welded_two_crew_members_of_one_day_are_both_counted :
    isOkB (observeChain labPanel (initial labPanel) [alphaWelded, betaWelded]) = true ∧
    alphaWelded.key ≠ betaWelded.key ∧
    alphaWelded.key.period = betaWelded.key.period := by native_decide

#assert_axioms mergeExact
#assert_axioms observe_adds_exactly_the_receipt
#assert_axioms readings_eq_of_meters
#assert_axioms an_ordinary_day_moves_no_gauge
#assert_axioms the_face_does_not_record_who_opened
#assert_axioms the_order_the_crew_arrives_does_not_change_the_face
#assert_axioms welded_contribution_is_the_authored_table_row
#assert_axioms welded_subject_is_the_signed_player
#assert_axioms welded_period_is_the_consumed_period
#assert_compiled lab_state_from_another_panel_refuses
#assert_compiled welded_lab_witness_is_refused_by_another_deployment
#assert_compiled welded_same_crew_member_cannot_be_counted_twice
#assert_compiled lab_capacity_refuses_rather_than_forgetting_a_receipt
#assert_compiled lab_meter_overflow_refuses_instead_of_clipping
#assert_compiled welded_lab_witness_is_admitted_by_its_own_deployment
#assert_compiled welded_two_crew_members_of_one_day_are_both_counted

end Dregg2.Games.PathOfAngels.ShipInstrumentPanel
