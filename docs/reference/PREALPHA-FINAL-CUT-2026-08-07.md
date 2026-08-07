# Prealpha Final Cut — what the next re-genesis can actually contain

**Measured 2026-08-07 at `7497a9dcb166cdbffcbbef068f810dd797f0bab4`.**

⚠ The tree moved twice while this was being written (`5f216e915` → `65c8eaa96` →
`7497a9dcb`); three PoA commits landed mid-census, including the crew organ's first
`@[export]`. Every claim below is read at the pinned SHA. Where the working tree
differs it is called out, never merged in.

The question this answers: ember and Sentyr sit down after the next ceremony. What
can they *do*, and what would they have to *imagine*? Reachability is judged by **the
surface** — a signed descriptor a client renders, or an export a route serves and a
page shows. A green theorem is not a surface. An absent `@[export]` is not death: the
four bundle games have none and are the most playable things here.

---

## Headline

| class | count | what it is |
|---|---|---|
| **A — playable now** | **11** surfaces (4 games, 4 organs, 3 labs) | a player reaches it today |
| **B — one ceremony away** | **0** | **nothing.** See "B is empty" below |
| **C — kernel only, N hops** | **9 organs/games** | real game logic, no surface |
| **D — supporting machinery** | **~66 modules** | codecs, wires, boundaries, examples |
| **E — dead / superseded** | **2 candidates** | ~1.7k lines, both argued below |

**B is empty, and that is the most important sentence in this document.** The natural
assumption going into the ceremony — "Deck Descent is authored, so a re-emit lands a
fifth game" — is false. Deck Descent has no client, its checked-in descriptor is
*stale enough that the design gate refuses it*, and enrolling it in the signed catalog
without a controller makes its rack card **worse**, not better (see §3).

---

## 1. The classification

### A — PLAYABLE NOW (11 surfaces)

| thing | surface (measured) | evidence |
|---|---|---|
| **Signal Triangulation** | signed bundle + authored surface in `index.html` (`#signal-game`), `signal-runtime.js` | `poa/artifacts/poag1/games/signal-triangulation.json` (52,260 B, pinned in `manifest.json`); catalog mission 1; `poa-web/src/mission-launcher.js:27` |
| **Relay Repair** | signed bundle + `relay-controller.js` via `mountFiniteTableController` | `poa/artifacts/poag1/games/relay-repair.json` (122,003 B); `mission-launcher.js:21` |
| **Salvage Lock** | signed bundle + `salvage-controller.js` | `.../salvage-lock.json` (635,203 B); `mission-launcher.js:22` |
| **Black Box Reconstruction** | signed bundle + `blackbox-controller.js` | `.../black-box-reconstruction.json` (8,107 B); `mission-launcher.js:23` |
| **The Galley** | `#galley` view + `galley-controller.js`; `GET /api/poa/galley/v1/session`, `/status`, `POST /command` (all public) | routes `node/src/poa_galley_api.rs:513-515`, merged `node/src/api.rs:2228`; Lean `dregg_poa_galley_daily_judge` reached via `persist/src/poa_galley_authority.rs:1292` |
| **Field Records** | `#records` view, `#records-live` panel; `GET /api/poa/records/{authority}` | `node/src/poa_records_api.rs:427`; Lean `dregg_poa_records_project` at `poa_records_api.rs:372` |
| **Ship instrument panel (read)** | `#station-panel`; `GET /api/poa/station/{authority}/panel` | `node/src/poa_station_api.rs:434`; Lean `dregg_poa_station_daily_read` at `poa_station_api.rs:392` |
| **Today board / slot opening** | `#today-board`; `GET /api/poa/signal/{authority}/slot`, curator Ed25519 re-verified client-side | `node/src/poa_signal_slot_api.rs:127`; `poa-web/src/today-board.js:56` rebuilds the signed statement bytes rather than trusting the wire |
| **Archive Evidence Lab** | standalone `poa-web/labs/archive-lab.html`, linked from `#records` | fixture + provenance checked in (`archive-lab-demonstrator.provenance.json`, generator = `ArchiveLabDemonstratorEmit.lean`) |
| **Expedition Lab** | standalone `poa-web/labs/expedition-lab.html`, linked from `#crew` and `#records` | `expedition-demonstrator.provenance.json`, generator = `ExpeditionDemonstratorEmit.lean` |
| **Flight Recorder** | standalone `poa-web/labs/flight-recorder.html`, linked from `#records` | ⚠ `flight-recorder.config.json` is `"mode": "demo"`, `"api_base_url": null` — it replays a checked-in fixture, it does not follow a live wake |

⚠ **All four rack games are PRACTICE ONLY in the browser.** `poa-web/src/app.js:113`
pins `STATUS_BY_MODE = { practice: "practice" }` and every controller is handed
`practiceSession(...)` at `app.js:677`. Nothing a player does on the rack reaches a
chain. The judged path exists but does not run — §2.

### B — AUTHORED, ONE CEREMONY AWAY: **none**

There is no module in this tree that becomes playable by re-emitting, re-signing or
installing alone. Every candidate needs code as well:

- **Deck Descent** is enrolled in the emitter (`Emit.lean:1439`, mission 5) *and* in
  the reproduction script (`scripts/check-poag1-artifacts.sh:94,181,250` all name
  `games/deck-descent.json`), so the ceremony would land it in the signed bundle. But
  `poa-web` has no Deck Descent controller, no runtime, and no `descriptorShape`
  presentation record with a shape. It is **C**, not B.
- **Vent Crawl** and **Artificer Logic** have complete browser clients on disk and are
  in neither the emitter's catalog nor the reproduction script. **C**.
- **The Night Watch world** has emitted, gate-checked content
  (`poa/artifacts/night-watch/epoch-1/`) and an installer shape, but nothing serves
  it and no page reads it. **C**.

⚑ **The ceremony's most likely own-goal.** `poa-web/src/game-rack.js:56` renders an
enrolled-but-uncontrolled game as:

> "The signed catalog enrols this drill and this terminal has no controller for it.
> Nothing opens: a browser must never approximate a game it was not given."

Today Deck Descent renders as `reserved` — *"A route down. Not yet cut."* If the
ceremony enrols it and the controller is not shipped in the same cut, the card
**downgrades** from an honest berth to a refusal. Enrol Deck Descent only in the same
cut as its client.

### C — KERNEL ONLY, N HOPS

Ranked cheapest-first in §3. Listed here with the hop that is actually missing.

| organ / game | modules | what exists | what is missing |
|---|---|---|---|
| **Artificer Logic** | `ArtificerLogic` (1671), `ArtificerLogicEmit` (593), `ArtificerLogicEmitMain` (57) | kernel + emitter; design-gate rule model `_artificer_differential` registered (`scripts/poa-design-gate.py:2299`); **`poa-web/src/artificer-controller.js` (103) + `artificer-runtime.js` (372) fully written**; routes as `parametric` in BOTH routers, tested (`poa-web/tests/artificer-router.test.mjs`) | catalog enrolment; descriptor never committed; **`artificer-controller.js` is imported by nothing** |
| **Vent Crawl** | `VentCrawl` (1422), `VentCrawlEmit` (529), `VentCrawlEmitMain` (50) | kernel + emitter; design-gate backend `PushYourLuckGame` (`poa-design-gate.py:4357`, dispatched on `"vent" in doc` at `:5229`); **`ventcrawl-controller.js` (268) + `ventcrawl-runtime.js` (482) fully written**; descriptor publishes all four veins so a local practice oracle is a *lookup*, not a reconstruction | catalog enrolment; a **fifth shape** taught to `descriptor-shape.js:34` and `run-summary.js:145`; **`ventcrawl-controller.js` is imported by nothing** |
| **Deck Descent** | `DeckDescent` (1879), `DeckDescentEmit` (529), `DeckDescentEmitMain` (49) | kernel (8-board family, `boardAt_injective` by `decide`, `DeckDescent.lean:332`); emitter; **already in `Emit.lean` and `check-poag1-artifacts.sh`**; design-gate rule model `DescentRules` (`poa-design-gate.py:1408`) | **the committed descriptor is STALE** — the gate FAILs it (measured, §2); **no client at all**; descriptor emits **no practice board family**, so a practice oracle is impossible without an emitter change |
| **Salvage Crate open** | `SalvageCrate` (911), `SalvageCrateExamples`, `StationCrateOpen` (290), `StationCrateOpenRuntime` (791) | full chain: Lean `dregg_poa_crate_open` → `node/src/poa_crate_api.rs:444` → `POST /api/poa/station/{authority}/crate/open`; client fn `openSalvageCrate` (`station-panel.js:424`) and the button (`app.js:425`) | **no crew identity in the browser** (`app.js:95` — `crew: null`, and the file refuses to invent one), and the route is **bearer-protected** (`api.rs:2540`, layer at `:2542`) while the page holds no bearer. The control renders DISABLED, with the reason |
| **Crew field mission** | `CrewFieldMission` (2875), `CrewFieldMissionAdmission` (**new at `ca986ccfd`**, 1901), `CrewFieldMissionRuntime` (1729), `+Boundary`, `CrewExpeditionAuthority` (1244), `CrewRelayExpedition`, `CrewSigningVectors`, `PoaCrewPreferenceDrExExercise` | admission module landed **today**, carrying the organ's first export `@[export dregg_poa_crew_field_step]` (`CrewFieldMissionAdmission.lean:1448`) and a C shim (`dregg-lean-ffi/src/lean_init.c:1842`) | **no safe Rust wrapper caller, no node route, no client.** The `#crew` view is a static roster plus a link to the expedition lab; `GET /api/poa/station/{authority}/crew/{crew}` exists but `station-panel.js:38-42` states plainly the terminal binds no crew key, and `tests/station-panel.test.mjs:630` asserts the route is never called |
| **Night Watch campaign** | `NightWatchCampaign` (1136), `+Admission` (899), `+Content` (620), `+ContentEmitMain` (220), `+Examples` (1148), `+Wire` (771) | content emitted and gate-checked into `poa/artifacts/night-watch/epoch-1/` by `scripts/test-poa.sh:79-83`; `@[export dregg_poa_night_watch_campaign_judge` + FFI wrapper `judge_poa_night_watch_campaign` (`dregg-lean-ffi/src/poa_night_watch_ffi.rs:83`) | **the export is an ORPHAN.** Zero callers outside `dregg-lean-ffi/`; only 5 in-file `#[cfg(test)]` uses and a `build.rs` presence probe. No route, no persist consumer, no client |
| **Dark Bazaar / Bazaar** | `BazaarGame` (2603), `BazaarGameRuntime` (1134, 15 exports), `BazaarGameExamples` (1016), `DarkBazaar` (1860), `DarkBazaarJudge` (280), `DarkBazaarJudgeWire` (813) | 16 exports, Lean↔C CAS/journal machinery, a Rust portal | **every one of the 16 is TEST-ONLY.** `dregg_poa_dark_bazaar_judge`'s only entry is `LeanJudgedSettlement::judge` (`circuit-prove/src/dark_bazaar_private_poa_settlement.rs:549`), called only from that file's `#[cfg(test)]`. The `#bazaar` view is a hand-written locked-organ card. Market routes exist at `/market/dark-clearing/…` but are bearer-gated operator surface, not a player path |
| **Private Recon Choir** | `PrivateReconChoir` (760), `+Examples` (267) | kernel | no export, no route, no client. `#choir` is a static historical panel: *"Historical display only. This terminal does not synthesize or replay the YouTube poll."* |
| **Ordinary Salvage Exchange** | `OrdinarySalvageExchange` (597) + `Boundary` + `Examples`, `OrdinarySalvageFinalizedTransaction` (565) + `Boundary` + `Examples` | kernels + boundary statements | no export, no route, no client |

### D — SUPPORTING MACHINERY (~66 modules)

Named as such; none is a game.

- **Emission / wire**: `Emit` (1968), `EmitJson`, `EmitMain`, `NetworkGenesis`,
  `NetworkGenesisWire`, `NetworkJudge`, `NetworkJudgeWire`, `SignalFeedbackRuntime`,
  `SlotDeriveRuntime`, `RecordsRuntime`, `StationDailyRuntime`,
  `GalleyMaintenanceDailyRuntime`, `EventBatchRuntime`, `ActivatedContentRuntime`,
  `WorldActivation`, `NightWatchCampaignWire`, `DarkBazaarJudgeWire`,
  `BazaarGameRuntime`.
- **Instance derivation**: `SeedDraw` (159), `HiddenInstance` (502), `FiniteTables`
  (551), `DeckGenerator` (684), `PlayerCounters` (254).
- **Content authority**: `Core` (543, fan-in 21), `Canon`, `CanonicalCodec`,
  `CanonicalCodecFalsifier`, `CanonicalCodecHealthWire`, `ContentContract`,
  `ActivatedContent`, `EditorialRegistry`, `EventSourcing`, `EventBatch`, `Judged`,
  `ActivityOutcome`, `DailyMission`, `FieldArchive`, `FinalizedRunEventAggregate`,
  `HolderMechanics`, `AssistProfile`, `ContainmentInspection`, `FheggPrivacyTopology`,
  `Cartography`, `OfficerLogbook`, `AttendantKernel`, `AttendantContinuityAggregate`,
  `ShipExpeditionSeason`, `ShipLifeProgression`, `Shipworks`, `ShipInstrumentPanel`,
  `DeckExpedition`, `DeckGraph`.
- **Boundary modules** (statement-only, zero importers by design):
  `CrewFieldMissionRuntimeBoundary`, `EditorialRegistryBoundary`,
  `GalleyMaintenanceDailyRuntimeBoundary`, `HolderMechanicsBoundary`,
  `OrdinarySalvageExchangeBoundary`, `OrdinarySalvageFinalizedTransactionBoundary`,
  `ShipExpeditionSeasonBoundary`, `ShipLifeProgressionBoundary`.
- **Examples / fixtures**: `ActivatedContentExamples`, `BazaarGameExamples`,
  `NightWatchCampaignExamples`, `OrdinarySalvage*Examples`, `PrivateReconChoirExamples`,
  `SalvageCrateExamples`, `CrewSigningVectors`.

⚠ **Structural note worth carrying forward.** No PoA module is reached by an import
edge from `Dregg2.lean`. `Dregg2/FFI.lean` imports exactly the 15 modules that carry an
`@[export]` (14 until `CrewFieldMissionAdmission` joined at `FFI.lean:104` today);
every other module is held alive only by the 68-entry `globs` list of the
`PathOfAngelsGuards` `lean_lib` (`metatheory/lakefile.toml:281`, list at `:282-497`).
**A new PoA module that is not added to that list is elaborated by nothing** — the
list's own comments record a 46-orphan sweep whose modules carried 378 `#assert_axioms`
and 439 `#assert_compiled` that ran in no `lake build` at all. There is also no
`lean_exe` rooting any of the 7 `def main` emitters (`metatheory/lakefile.toml` has
four, all Polis/Mina) — they run only under `lake env lean --run`.

### E — DEAD / SUPERSEDED (2 candidates, ~1.7k lines)

Precedent: `NightWatchLoop` was 741 measured unreachable states and 4,717 lines, cut
2026-08-07. Both candidates below are **argued, not asserted** — neither is as clean.

1. **`PoaCrewPreferenceDrExExercise` (1239 lines)** — zero importers, zero exports, not
   named by any Rust, script, or web file outside the lakefile glob. It is a
   preference-regime exercise attached to a crew organ that has since grown its own
   admission module. **Recommend: read once against `CrewFieldMissionAdmission`, and
   cut if it is the superseded draft.** I could not determine that from the outside.
2. **`persist::poa_world_activation::prepare_poa_world_activation_v1`
   (`persist/src/poa_world_activation.rs:560`)** — not a PoA Lean module, but dead code
   on this surface: **zero callers repo-wide**, while its sibling
   `install_poa_world_activation_v1` is the live path. A retained no-op the next reader
   will trust. **Cut it.**

Also worth a decision, though I am not calling it dead: the **16 Bazaar exports** and
their C shim layer are the largest test-only surface in the tree (~7.7k Lean lines +
`lean_init.c` machinery + two Rust portal files) with no player path and no roadmap
entry I found that schedules one.

---

## 2. What the design gate can actually measure

`scripts/poa-design-gate.py` (5,339 lines) has **six** backends, not five —
`pick_backend` at `:5229`:

| # | backend | dispatch key | games |
|---|---|---|---|
| 1 | `DeductionGame` `:276` | `"rules" in doc` | Signal |
| 2 | `MachineGame` `:700` | (used by 4) | — |
| 3 | `ParametricMachineGame` `:1055` | a `resolve` row | Salvage, **Deck Descent**, **Artificer** |
| 4 | `MachineFamilyGame` `:3052` | `"machines" in state_machine` | Relay |
| 5 | `ProbeOracleGame` `:3171` | `"oracle" in doc` | Black Box |
| 6 | `PushYourLuckGame` `:4357` | `"vent" in doc` | **Vent Crawl** |

Backend 3 will not analyse a parametric table it cannot independently rebuild
(`:1139`). `PARAMETRIC_RULE_MODELS` (`:2299`) registers exactly three rulesets:

```python
"salvage-v2":   ParametricMachineGame._salvage_differential,
"descent-v1":   ParametricMachineGame._descent_differential,
"artificer-v1": ParametricMachineGame._artificer_differential,
```

**Answer to the question: every C game already has a fitting backend. No new gate work
is needed to enrol any of them.** That is the surprise — the gate is *ahead* of the
client, not behind it.

Measured, not read:

- **Shipped bundle** — `python3 scripts/poa-design-gate.py --games-dir poa/artifacts/poag1/games`
  → exit 0, 4 games, 0 FAIL, 4 baseline WARNs
  (`scripts/poa-design-gate.baseline.json`: salvage budget-slack + three signal
  entries). Signal's budget binds exactly (worst case 5 = `action_limit` 5, slack 0);
  Salvage's hidden-board floor is 10 exposures against a 12 budget.
- **Deck Descent, the committed pending descriptor** —
  `poa/artifacts/poag1-pending/games/deck-descent.json` (2,758,692 B) →
  **1 FAIL, `deck-descent/analyser-refusal`**:

  > the shaft declares `relics_per_chamber`, the pre-second-relic shape. The kernel
  > counts relics PER CHAMBER now (the east spur holds two); re-emit the descriptor
  > from `DeckDescentEmitMain` rather than reinterpreting a scalar

  The committed artifact is one kernel commit stale (`d49ea5494`, "the east spur now
  holds a second relic"). **The Final Cut must re-emit it, not ship it.**

⚠ **The client's shape taxonomy is behind the gate's.** `descriptor-shape.js:8-12`
says the two files mirror `pick_backend` "name-for-name" and that "if a fifth shape
appears, BOTH refuse until somebody teaches them". The gate has been taught the
`vent` shape; `descriptor-shape.js:34` still holds four. Vent Crawl's rows carry only
`accept`/`refuse` and no `resolve` (`VentCrawlEmit.lean:115-119`), so
`descriptorShape` would refuse it with `shape-no-hidden-information` — the invariant
held, and the debt is now one-sided.

I did **not** run the gate on Vent Crawl or Artificer descriptors: neither is
committed anywhere, and emitting them needs a Lean build I did not run.

---

## 3. Ranked: cheapest to make playable

Hop counting is over *code and ceremony steps*, not lines. All three share a common
ceremony tail, written once at the end.

### 1st — **Artificer Logic**. Zero new web modules.

| # | hop | where |
|---|---|---|
| A1 | Lean: enrol as a catalog mission — `ArtifactHashes` field, `canonicalArtifacts` entry, `missionCatalogJson` row, schema paths. This is exactly the shape of the Deck Descent enrolment already in the file | `metatheory/Dregg2/Games/PathOfAngels/Emit.lean:1439-1904` is the worked example |
| A2 | `source_files` + `content_paths` + `expected` + a `artificer_sha` var. ⚠ `source_files` is checked against the *derived* transitive closure of `EmitMain`'s imports (`check-poag1-artifacts.sh:130-160`) — it will go red if you forget a module | `scripts/check-poag1-artifacts.sh:94,181,250` |
| A3 | `POAG1_EXPECTED_ARTIFACTS` += `games/artificer-logic.json`, path-ascending | `poa-web/src/poag1.js:20` |
| A4 | fill the presentation record: `session`, `shape: SHAPES.parametric`, `columns` | `poa-web/src/game-rack.js:125` |
| A5 | one dispatch line: `"artificer-logic": mountArtificerLogic` | `poa-web/src/mission-launcher.js:20` |
| A6 | one `practiceSession` branch using `artificerPracticeOracle` | `poa-web/src/app.js:634` |

Nothing new is written. `mountArtificerLogic` (`artificer-controller.js:30`) already
delegates to the shared `mountFiniteTableController`, and both routers already agree
it is `parametric` — with a *test* that asserts it (`tests/artificer-router.test.mjs`).
⚠ It has **no controller test**; the router test runs on a synthetic descriptor
because "the emitted artifact has no tracked home yet".

### 2nd — **Vent Crawl**. Zero new web modules, one new shared shape.

A1–A6 as above, plus:

| # | hop | where |
|---|---|---|
| V7 | teach `descriptor-shape.js` a fifth shape keyed on `"vent" in doc`, mirroring `pick_backend` | `poa-web/src/descriptor-shape.js:34,45` |
| V8 | add an `OUTCOME_BY_SHAPE` reading for it, or the end screen refuses `no end-of-run reading exists for the … shape` | `poa-web/src/run-summary.js:145,163` |

`mountVentCrawl` (`ventcrawl-controller.js:74`) deliberately does **not** use the
shared finite-table controller — two verbs of different shape — so V7/V8 are real
work, not renames. Also **no tests exist for either vent file**.

### 3rd — **Deck Descent**. Two new web modules and a Lean emitter change.

Already half-enrolled (A1, A2 done), so the ceremony is a script run. But:

| # | hop | where |
|---|---|---|
| D1 | **re-emit** — the committed pending descriptor is refused by the gate (§2) | `DeckDescentEmitMain.lean`, driven by `check-poag1-artifacts.sh --update` |
| D2 | Lean: emit a **practice board family** (the 8 boards of `DeckDescent.boardTable`). Today `instance` carries no `boards` and there is no top-level `practice.boards`, so `app.js:634` cannot build a local oracle — and deriving the 8 boards from `shaft` in JavaScript would be the client inventing the game | `DeckDescentEmit.lean`; compare `salvage-lock.json`'s top-level `practice` block |
| D3 | new `poa-web/src/deckdescent-runtime.js` — loader spec + practice oracle (~450 lines, on the salvage/relay pattern) | new file |
| D4 | new `poa-web/src/deckdescent-controller.js` — presentation (~100 lines) | new file |
| D5–D8 | `poag1.js` list, `game-rack.js:105` record, `mission-launcher.js:20` line, `app.js:634` branch | as above |

Its shape is *already* right: 14,382 transitions with 282 `resolve` rows and the exact
key set salvage uses (`state, action, verdict, reason, next, on_match, on_mismatch`),
so `mountFiniteTableController` handles the mechanics unchanged.

### The shared ceremony tail (all three)

1. `POA_ROOT=<live devnet> scripts/check-poag1-artifacts.sh --update` — re-derives the
   federation id from genesis bytes, re-emits every descriptor + catalog + schema +
   manifest, and **deletes `manifest.sig.json`** with the message *"curator re-sign
   required"*.
2. Curator ceremony re-signs `manifest.json` → new `manifest.sig.json` at a bumped
   counter (currently `content_epoch 1, counter 8`, key `3c757baf…`).
3. `poa-web/src/trust-config.js:4` — bump `POA_EXPECTED_CURATOR_COUNTER`.
4. `node poa-web/scripts/sync-artifacts.mjs` — re-verifies every SHA-256 and FNV pin
   and the curator signature before copying into `poa-web/public/artifacts/`.
5. `scripts/test-poa.sh` — includes the design gate against the ratcheted baseline. A
   new game's findings must be *earned into* `poa-design-gate.baseline.json`, not
   dropped in.

---

## 4. The player's arc, after the ceremony

What ember and Sentyr can actually do, in order:

1. **Open the terminal.** The bundle authenticates against the pinned curator key
   before anything renders; a failed authentication seals every card rather than
   showing a placeholder. Good.
2. **Read today's board.** Four tiles: rack state, whether a judged slot is open (with
   the curator Ed25519 **re-verified in the browser against re-derived statement
   bytes**), what the salvage crate holds, the ship's headline figure. Each is either
   fetched-and-checked or a sealed tile that says why. This is the strongest surface
   in the product.
3. **Play four games on the rack.** Signal, Relay, Salvage, Black Box. Full runs, real
   Lean-emitted rules, honest refusals, a per-run local transcript, an end screen.
4. **Open the Galley.** Live session/status/command against the node; the Lean judge
   runs on every read.
5. **Read the ship's instrument panel and the field records.** Both live from the node.
6. **Enter three labs.** Archive evidence triage, the authored expedition descent,
   the flight recorder replay.
7. **Look at the crew muster, the Dark Bazaar and the Choir** — and read that nothing
   is there.

### The gaps that force them to imagine

| # | gap | what they see instead |
|---|---|---|
| **G1** | **Nothing they do settles.** Every rack run is practice; the transcript header literally reads `PRACTICE TRANSCRIPT — NOT SCORED` (`app.js:759`). The judged path is built — `openJudgedSession`, `spendJudgedBurst`, `loadJudgedSession`, `settleJudgedRun` all exist in `judged-session.js` — but **`openJudgedSession` and `spendJudgedBurst` have no caller outside the test file**, so the page cannot start a judged run at all. And one wall further on, `claim-cell-underivable` (`judged-session.js:434`) stands: the extension derives the player cell through `wasm.cell_id_for_pubkey`, which **has never existed in any shipped bundle**. The binding is in `wasm/src/lib.rs` at HEAD; the artifact does not carry it, and the rebuild is blocked because the wasm32 workspace does not compile | a panel that names the wall by name |
| **G2** | **The salvage crate is a disabled button.** The whole chain works — Lean, node handler, protected route, client function, panel refresh — and `state.crew` is `null` because the terminal binds no crew identity and refuses to invent one. The route is also bearer-gated and the page holds no bearer | a control rendered disabled, with the reason |
| **G3** | **The crew organ renders a static roster.** ~10k Lean lines across eight crew modules, an admission module and its first `@[export]` landed *today*, and the `#crew` view is four locked-system rows and a link to the expedition lab. The `/crew/{crew}` route exists; a test asserts the page never calls it | *"Nothing yet"* |
| **G4** | The Night Watch is content-complete, gate-checked, and reaches nobody — its export is an orphan | nothing at all; there is no Night Watch surface |
| **G5** | The Dark Bazaar is a hand-written locked-organ card over 7.7k lines of test-only machinery | *"The market is present. Settlement is not yet linked to this federation."* |
| **G6** | The Choir is a static historical panel | *"No command decision is waiting"* |
| **G7** | The Flight Recorder is in `"mode": "demo"` against a checked-in fixture, not a live wake | a replay that looks live |
| **G8** | Deck Descent, Vent Crawl and Artificer Logic are three empty berths | *"Not yet cut" / "Not yet opened" / "A bench, waiting for its work."* |

**The three biggest gaps between built and playable**, by lines-behind-a-wall:

1. **The judged loop (G1)** — the difference between a demo and a game. Two orphan
   client functions and one wasm rebuild blocked by an unrelated lane's
   `Effect::Deshield`.
2. **Crew (G3)** — ~10k Lean lines, an export minted today, and a static card.
3. **Bazaar (G5)** — ~7.7k Lean lines, 16 exports, all test-only.

---

## 5. What I could not determine

Said plainly, because each is a real hole in this census:

- **Whether Vent Crawl's and Artificer Logic's descriptors emit cleanly at HEAD.**
  Neither is committed anywhere; both emitters write to `poa/artifacts/poag1-pending/`
  and only Deck Descent's output is tracked. Running them needs a Lean build I did not
  run. So my ranking assumes their emitters work; that assumption is untested.
- **Whether `deckdescent-runtime.js` is really ~450 lines of work.** I sized it off
  `salvage-runtime.js` (200) + `ventcrawl-runtime.js` (482). It is an estimate, not a
  measurement. ⚑ Per `CLAUDE.md`: do not let this estimate become a constraint.
- **Whether `PoaCrewPreferenceDrExExercise` is superseded.** It has zero importers and
  zero external references, which is *consistent* with dead and also consistent with
  every other boundary/example module in the cone. Someone who knows the crew design
  has to read it against `CrewFieldMissionAdmission`.
- **Whether the deployed beta actually serves this HEAD.** Infra lives in
  `~/dev/dregg-infra` and I did not touch it. Memory records a class where fresh web
  shipped against a 189-commit-stale node for 27h with `healthy: true`. **Before the
  Final Cut, check `latest_height` against `dag_height` on the live node**, not the
  health flag.
- **Whether the three labs' fixtures are fresh.** Their provenance files pin source
  commits `60d7e5221` and `9d4f597c7` (2026-08-04). I found no gate that re-derives
  them; `test-poa.sh` checks the Galley and Night Watch content roots but not the lab
  fixtures.

### In-flight, not at HEAD

The working tree carries another lane's untracked `poa/artifacts/angels-epoch-2/`
(`manifest.json`, `world.json`, `galley-policy.json`, `night-watch-config.json`) and
`metatheory/Dregg2/Games/PathOfAngels/AngelsEpoch2World{,EmitMain}.lean`. An **epoch-2
world** is being assembled right now, and it includes a night-watch config. That may
change G4's answer within a day. It is not at HEAD and is not classified above.
