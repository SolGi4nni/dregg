/-
# StationCrateOpen — the daily ritual that finally MOVES the ship

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget; it composes two already-proved state machines.

PLATFORM-ROADMAP §7.3 pairs *salvage crate* (the ritual) with *ship instrument
panel* (what the ritual moves).  Until now the write half was **unreachable by
type**: `SalvageCrate.openCrate` demanded a `CurrentStateCapability` that had no
producer anywhere in the tree, so `StationDailyRuntime` served
`ShipInstrumentPanel.initial` and every gauge read zero — `the_served_ship_has_not
_been_moved`.  `SalvageCrate` now roots that capability in a `genesis` install and
hands the successor capability back from each accepted open, so the ceremony is
**reachable-through-authorization**.  This module is the composition: open the
crate under that chain and fold the accepted `OpenReceipt` into the panel through
the panel's *own* communal `observe`.

## The write is not a second authority

`observeDay` moves the panel ONLY by calling `ShipInstrumentPanel.observe` on a
real `SalvageCrate.OpenReceipt` — the sealed receipt whose only producer is an
accepted opening.  It mints no contribution, chooses no draw, and owns no gauge.
Every number the ship shows is one `Contribution` the crate already proved exact.

## Two poles, on ACTUAL crate output

* `an_honest_salvage_open_moves_the_supplies_gauge` — on the authored deployment,
  crew `digest 41` opening the genesis period draws the communal-salvage row and
  the supplies gauge advances by exactly its contribution (1), the recovered set
  gains the thread spool.  The ritual moves the ship.
* `an_ordinary_open_moves_no_gauge` — crew `digest 40` draws a bound record whose
  contribution is zero; they opened (observed and admitted both count) and the
  ship is bit-identical.  Showing up on an ordinary day and not showing up are the
  same ship — the roadmap's "missing a day is uninteresting", on real output.
* `the_replay_open_is_refused_and_never_reaches_the_panel` and
  `a_wrong_period_open_is_refused_and_never_reaches_the_panel` — a second open of
  the same period by the same crew, and an open of a period that is not the
  current one, are refused by the crate and never reach the fold.  The hostile
  envelopes are constructed explicitly and asserted refused; the honest pole above
  witnesses that the refusal is not vacuous.

## Communal and unattributed

`the_communal_gauge_accumulates_only_the_salvage_draw` folds the whole eligible
crew and the gauge carries only the one salvage draw, with three arrivals counted;
`the_face_is_the_same_whatever_order_the_crew_arrives` reorders them and the ship
reads identically.  There is no per-player field on the panel, so no streak,
leaderboard, or attendance record can be read off the moved ship — exactly the
laws `ShipInstrumentPanel` proves, here on the composed write path.
-/
import Dregg2.Games.PathOfAngels.ShipInstrumentPanel
import Dregg2.Games.PathOfAngels.SalvageCrateExamples
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.StationCrateOpen

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## The deployment: the authored crate and a panel that is its one ship -/

/-- The already-authored, already-valid crate rotation. -/
abbrev crate : SalvageCrate.Config := SalvageCrateExamples.config

/-- The panel identity is read off the crate's mission so a receipt this crate
produces can never be refused by this panel as foreign.  One supplies dial,
because every authored row moves only supplies (the read runtime proves the same
of its own panel). -/
def panelRaw : ShipInstrumentPanel.RawPanel where
  federationId := crate.raw.mission.federationId
  contentSession := crate.raw.mission.contentSession
  contentEpoch := crate.raw.mission.epoch
  gauges := [{ id := ⟨1⟩, meter := .supplies, fullAt := 64 }]
  capacity := ShipInstrumentPanel.MAX_OBSERVED

theorem panel_valid : ShipInstrumentPanel.panelValidB panelRaw = true := by native_decide

def panel : ShipInstrumentPanel.Panel := ⟨panelRaw, panel_valid⟩

/-- ⭐ The panel and the crate are ONE deployment, so no accepted opening is ever
refused as `foreignDeployment`. -/
theorem panel_and_crate_are_one_deployment :
    panelRaw.federationId = crate.raw.mission.federationId ∧
    panelRaw.contentSession = crate.raw.mission.contentSession ∧
    panelRaw.contentEpoch = crate.raw.mission.epoch := ⟨rfl, rfl, rfl⟩

/-! ## The ceremony: open, then fold the receipt into the panel -/

/-- Open the crate under the threaded capability and, on an accepted opening, fold
its receipt into the panel; then continue with the successor state and its
successor capability.  Refuses (returns `none`) at the first crate refusal OR the
first panel refusal, so the panel is never left holding a receipt the crate
declined.  Returns the final panel. -/
def observeDay : (state : SalvageCrate.State crate) →
    SalvageCrate.CurrentStateCapability state → ShipInstrumentPanel.State →
    List SalvageCrate.OpenEnvelope → Option ShipInstrumentPanel.State
  | _, _, panelState, [] => some panelState
  | state, cap, panelState, envelope :: rest =>
      match SalvageCrate.openCrate crate state cap envelope with
      | none => none
      | some result =>
          match ShipInstrumentPanel.observe panel panelState
                  (ShipInstrumentPanel.ofSalvageOpen result.receipt) with
          | .error _ => none
          | .ok nextPanel =>
              observeDay result.after result.nextCapability nextPanel rest

/-- One open from the installed ship, the common shape below. -/
def observeOne (envelope : SalvageCrate.OpenEnvelope) : Option ShipInstrumentPanel.State :=
  observeDay (SalvageCrate.genesis crate) (SalvageCrate.genesisCapability crate)
    (ShipInstrumentPanel.initial panel) [envelope]

/-! ## The crew and their authored envelopes

The genesis period is the first authored beacon (31).  Each envelope carries the
running sequence position and the opener's advancing counter; the eligible crew
are `digest 40/41/42`. -/

def actorRoot : Digest32 := SalvageCrateExamples.digest 90

def envFor (player : Digest32) (period : EpochId) (previous next sequence : Nat) :
    SalvageCrate.OpenEnvelope where
  configIdentity := crate.raw
  expectedPeriod := period
  expectedSequence := sequence
  actorRoot := actorRoot
  player := player
  previousPlayerCounter := previous
  playerCounter := next

def crew40 : Digest32 := SalvageCrateExamples.digest 40
def crew41 : Digest32 := SalvageCrateExamples.digest 41
def crew42 : Digest32 := SalvageCrateExamples.digest 42

/-- Crew 41, opening the genesis period from the installed ship: draws the
communal salvage. -/
def env41 : SalvageCrate.OpenEnvelope := envFor crew41 ⟨31⟩ 0 1 0

/-- Crew 40, opening the genesis period: draws a bound record (zero contribution). -/
def env40 : SalvageCrate.OpenEnvelope := envFor crew40 ⟨31⟩ 0 1 0

/-! ## The two poles -/

/-- ⭐ THE RITUAL MOVES THE SHIP.  The supplies gauge advances by exactly the drawn
contribution (1), the recovered set gains one kind, and the open is counted —
observed and admitted both 1.  A refusal is `none`, so this cannot be met by
declining. -/
theorem an_honest_salvage_open_moves_the_supplies_gauge :
    (observeOne env41).map (fun s =>
        (s.face panel, s.recovered.card, s.observed.card, s.admitted)) =
      some ([{ gauge := ⟨1⟩, meter := .supplies, exactTotal := 1, fullAt := 64,
               shown := 1, atFull := false }], 1, 1, 1) := by native_decide

/-- ⭐ AN ORDINARY DAY MOVES NO GAUGE, on real crate output.  Crew 40 opened — it
is observed and admitted — and the ship is bit-identical to the installed one:
supplies zero, no salvage recovered.  Missing a day is uninteresting. -/
theorem an_ordinary_open_moves_no_gauge :
    (observeOne env40).map (fun s =>
        (s.face panel, s.recovered.card, s.observed.card, s.admitted)) =
      some ([{ gauge := ⟨1⟩, meter := .supplies, exactTotal := 0, fullAt := 64,
               shown := 0, atFull := false }], 0, 1, 1) := by native_decide

/-! ## The hostile openings, constructed and refused

`firstResult` is the ACCEPTED first open of crew 41 — its existence witnesses that
the refusals below are not vacuous (there really was a ship-moving open to
replay). -/

private def firstResult : SalvageCrate.OpenResult crate env41 :=
  (SalvageCrate.openCrate crate (SalvageCrate.genesis crate)
    (SalvageCrate.genesisCapability crate) env41).get (by native_decide)

private def afterFirst : SalvageCrate.State crate := firstResult.after
private def afterFirstCap : SalvageCrate.CurrentStateCapability afterFirst :=
  firstResult.nextCapability

/-- The mutation: the SAME crew member opening the SAME period again, on the
successor state, with the correctly advanced counter — so the only check left to
refuse it is the append-only consumed-period guard. -/
def replayEnv41 : SalvageCrate.OpenEnvelope := envFor crew41 ⟨31⟩ 1 2 1

/-- The mutation is present: crew 41 already consumed the genesis period. -/
theorem the_first_period_is_consumed_by_crew_41 :
    SalvageCrate.openKey crate ⟨31⟩ crew41 ∈ afterFirst.consumed := by
  have := firstResult.consumes_exact_period
  simpa using this

/-- ⭐ REPLAY REFUSED, and it never reaches the panel.  Holding a perfectly valid
successor capability does not let crew 41 open the genesis period twice. -/
theorem the_replay_open_is_refused_and_never_reaches_the_panel :
    observeDay afterFirst afterFirstCap (ShipInstrumentPanel.initial panel) [replayEnv41]
      = none := by native_decide

/-- The mutation: crew 41 asking for period 32 while the ship is still at the
genesis period 31. -/
def wrongPeriodEnv41 : SalvageCrate.OpenEnvelope := envFor crew41 ⟨32⟩ 0 1 0

/-- ⭐ WRONG-PERIOD REFUSED, and it never reaches the panel.  A capability for the
installed state authorizes opening the CURRENT finalized period, not a future one.
The honest pole above shows this same crew, same genesis, DOES open period 31. -/
theorem a_wrong_period_open_is_refused_and_never_reaches_the_panel :
    observeOne wrongPeriodEnv41 = none := by native_decide

/-! ## Communal and unattributed, on the composed write path -/

def env40Seq1 : SalvageCrate.OpenEnvelope := envFor crew40 ⟨31⟩ 0 1 1
def env42Seq2 : SalvageCrate.OpenEnvelope := envFor crew42 ⟨31⟩ 0 1 2

/-- The whole eligible crew opening the genesis period, in arrival order 41,40,42. -/
def theWholeCrewOpens : Option ShipInstrumentPanel.State :=
  observeDay (SalvageCrate.genesis crate) (SalvageCrate.genesisCapability crate)
    (ShipInstrumentPanel.initial panel) [env41, env40Seq1, env42Seq2]

/-- ⭐ The communal gauge carries only the one salvage draw though THREE crew
opened: supplies 1, one recovered kind, three observed, three admitted.  The panel
counts arrivals well enough to keep them apart (observed = 3) and never well enough
to rank them (the face is one supplies number). -/
theorem the_communal_gauge_accumulates_only_the_salvage_draw :
    theWholeCrewOpens.map (fun s =>
        (s.face panel, s.recovered.card, s.observed.card, s.admitted)) =
      some ([{ gauge := ⟨1⟩, meter := .supplies, exactTotal := 1, fullAt := 64,
               shown := 1, atFull := false }], 1, 3, 3) := by native_decide

def env42Seq0 : SalvageCrate.OpenEnvelope := envFor crew42 ⟨31⟩ 0 1 0
def env41Seq2 : SalvageCrate.OpenEnvelope := envFor crew41 ⟨31⟩ 0 1 2

/-- The same crew, arriving in a different order 42,40,41. -/
def theWholeCrewOpensReordered : Option ShipInstrumentPanel.State :=
  observeDay (SalvageCrate.genesis crate) (SalvageCrate.genesisCapability crate)
    (ShipInstrumentPanel.initial panel) [env42Seq0, env40Seq1, env41Seq2]

/-- ⭐ Whoever reached the reclamation desk first, the ship reads the same — the
communal face does not depend on arrival order, on the composed write path. -/
theorem the_face_is_the_same_whatever_order_the_crew_arrives :
    theWholeCrewOpens.map (fun s => s.face panel) =
      theWholeCrewOpensReordered.map (fun s => s.face panel) := by native_decide

#assert_compiled panel_valid
#assert_compiled panel_and_crate_are_one_deployment
#assert_compiled an_honest_salvage_open_moves_the_supplies_gauge
#assert_compiled an_ordinary_open_moves_no_gauge
#assert_compiled the_first_period_is_consumed_by_crew_41
#assert_compiled the_replay_open_is_refused_and_never_reaches_the_panel
#assert_compiled a_wrong_period_open_is_refused_and_never_reaches_the_panel
#assert_compiled the_communal_gauge_accumulates_only_the_salvage_draw
#assert_compiled the_face_is_the_same_whatever_order_the_crew_arrives

end Dregg2.Games.PathOfAngels.StationCrateOpen
