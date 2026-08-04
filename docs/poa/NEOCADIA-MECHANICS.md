# Neocadia mechanics as Path of Angels platform depth

Status: build-facing design inventory, 2026-08-04.

This document treats `~/dev/neocadia` as raw mechanical research. It does not import
Neocadia's setting, generated characters, restoration economy, token arithmetic, or assumptions
about audience size. The transferable material is a collection of small player verbs, declarative
content shapes, onboarding patterns, and progression surfaces. Path of Angels supplies its own
fiction, authority, economy, privacy, and proof boundaries.

`docs/poa/ROADMAP.md` remains the broader dependency map. This document answers a narrower
question: how can PoA gain the depth of a long-lived game platform through many inexpensive,
interconnected activities without turning those activities into unverified JavaScript islands or
making Sentyr feed a content furnace?

## Source index and extraction rule

The useful Neocadia sources are specifications, not reusable production code. Its `src/main.ts`
is only a Phaser bootstrap; the algorithms below are sketches. Every transplant therefore begins
as a fresh PoA state machine and content schema, preferably in Lean.

| Key | Raw source | Useful material |
|---|---|---|
| N-MINI | `~/dev/neocadia/specs/minigames/README.md:1-167` | 30-second loops, common game shell, difficulty shapes, data-driven game format |
| N-GEAR | `~/dev/neocadia/specs/minigames/clockwork-quarter/gear-garden.md:13-84,159-173` | connection puzzle, inventory, BFS propagation |
| N-LOCK | `~/dev/neocadia/specs/minigames/pixel-beach/shell-shocked.md:13-115,237-281` | pair board, pressure budget, duplicate-and-shuffle generation |
| N-BLACKBOX | `~/dev/neocadia/specs/minigames/starlight-cinema/directors-cut.md:13-71,116-133` | ordering puzzle, accepted permutations, adjacency scoring |
| N-INSPECT | `~/dev/neocadia/specs/minigames/glitch-garden/debug.md:13-68,98-108` | authored anomaly regions, false-positive penalty, finite state machine |
| N-LOOP | `~/dev/neocadia/specs/minigames/glitch-garden/loop-garden.md:13-74,106-116` | room graph with changing movement/topology rules |
| N-PROBE | `~/dev/neocadia/specs/minigames/pixel-beach/reel-deal.md:13-73,231-259` | tune/wait/hook/recover phases, weighted encounter table |
| N-PIPE | `~/dev/neocadia/specs/minigames/sugar-rush/sugar-rush-kitchen.md:13-89,133-154` | recipe pipelines, concurrent stations, timing windows |
| N-TEND | `~/dev/neocadia/specs/minigames/glitch-garden/error-garden.md:13-98,132-147` | independent plots, delayed growth, mutation table |
| N-QTE | `~/dev/neocadia/specs/minigames/starlight-cinema/scene-stealer.md:13-78,125-143` | authored prompt tracks and timing judgments |
| N-QUIZ | `~/dev/neocadia/specs/minigames/starlight-cinema/reel-trivia.md:13-93,185-203` | fixed question packs, shared daily set, exact answer data |
| N-NAV | `~/dev/neocadia/specs/ui/navigation.md:1-58,62-87,122-141,224-259` | scene/hotspot graph, consistent back/home behavior, navigation stack |
| N-COLLECT | `~/dev/neocadia/specs/systems/collections.md:1-139,245-336` | collection records, silhouettes, hints, recent discoveries, micro-stories |
| N-DAILY | `~/dev/neocadia/specs/systems/daily-weekly.md:1-75,103-150,205-270` | featured activity, deterministic rotation, non-punitive recurrence |
| N-ONBOARD | `~/dev/neocadia/specs/systems/onboarding.md:1-12,90-169,169-270,274-340` | learn by doing, contextual help, tutorial queue, accessibility preflight |
| N-SAVE | `~/dev/neocadia/specs/systems/save-system.md:15-47,155-167,240-367` | versioned local projection, best runs, backups, ordered migrations |
| N-ACCESS | `~/dev/neocadia/specs/systems/accessibility.md:15-65,104-119,170-247,250-305` | semantic assist profiles, redundant cues, keyboard/screen-reader contract |
| N-CRITIQUE | `~/dev/neocadia/ANALYSIS.md:96-195` and `~/dev/neocadia/gemini-critique.md:17-76` | what not to copy: genre reskins, broken economy, false accessibility claims |

The extraction rule is: take the verb and the finite structure, then re-derive the semantics under
PoA's contracts. Names, prose, values, characters, lore, rewards, and economy do not cross the
boundary.

## Subsystem map

```text
curator-authored source pack
  -> content compiler and preview
  -> signed activation + POAG1 emitted bundle
  -> deck map / Officer / daily board / game config
  -> Lean-defined actions, replay and game-specific judge
  -> closed JudgedRun registry
  -> RunReceipt + bounded Contribution
       -> WorldState meters
       -> Field Archive beta record
       -> personal locker / score / crew record
       -> exact salvage claim -> DrEX ingress
  -> curator console
       -> remain beta | promote exact artifact | supersede exact artifact
```

| Subsystem | Player-facing organ | Semantic owner | Inputs | Durable outputs |
|---|---|---|---|---|
| Content epochs | changing ship, mission catalog | Lean schema plus curator signature verifier | authored source, epoch, activation counter | content root, activation digest, catalog |
| Navigation | deck map and compartments | declarative signed scene graph | active content epoch, archive state | selected mission or inspected record |
| Briefing | Expedition Officer | signed content plus local presentation state | mission, first-encounter flags, assist profile | no world mutation |
| Games | arcade, expeditions, maintenance | one Lean module per ruleset | mission config, seed, action transcript | game-specific judged run |
| Settlement | field record terminal | `Core.lean` and `Judged.lean` | authenticated player/counter, judged run | exact `RunReceipt` |
| World | ship instruments | `WorldState` transition | bounded contribution | monotone public meters and discoveries |
| Archive | field records and collections | canon admission model | judged receipt, artifact reference | beta/alpha/superseded record |
| Personal | locker, patches, best runs | receipt-derived projection | player-keyed receipts | non-authoritative cache plus reproducible view |
| Social | crews, league, theory board | signed statements and deterministic folds | receipts, claims, attestations | standings, evidence graph, crew state |
| Economy | salvage custody and Bazaar | asset ledger plus DrEX | exact receipted salvage claim | custody change, clearing receipt |
| Governance | Choir | proposal-specific Lean ballot regime | eligible proofs and ballots | tally receipt, never an automatic story branch |
| Curation | Sentyr console | `Canon.lean` capability boundary | exact artifact and signed admission | promotion or supersession |

The browser may render all of these. It does not get an alternate implementation of any operation
whose result changes world state, custody, canon, eligibility, or score.

## Shared Lean contracts

### 1. Content and mission contract

Every semantic activity consumes a `MissionSpec` or a game-specific configuration containing one.
The existing contract binds:

- mission and artifact identity;
- content epoch, federation, content root, detached activation digest, and content session;
- a precommitted run seed;
- per-meter and relic-count budgets;
- an exact allowed-relic set;
- the privacy grade and ballot regime claimed for this mission.

The content compiler may make ergonomic author formats, but its output must refine this contract.
Missing, duplicate, oversized, stale, or self-inconsistent content refuses activation. A client may
not replace a missing field with a default that changes semantics.

### 2. Game contract

Each game owns these definitions in Lean:

```text
Config + State + Action + step/replay + terminal predicate
  + score/contribution extraction + judge
```

A new game is not admitted merely because it can construct a `RunReceipt`. It receives a constructor
in the closed `JudgedRun` registry only after carrying equality to its fixed executable judge and an
opaque activation for the exact authenticated configuration. Central registry edits belong to the
integration lane so independent game swarms do not race on `Judged.lean`.

Each game proves, where applicable:

- replay determinism;
- legal actions preserve state invariants;
- illegal, late, duplicate, or out-of-range actions refuse;
- terminality under the declared action budget;
- score and contribution bounds;
- returned relics are drawn from the mission allowlist;
- generated instances satisfy solvability or explicitly declare that failure is an intended result;
- presentation-only assists do not change semantic results;
- semantic assists are committed in the authenticated configuration.

Facts worth gating are named theorems with `#assert_axioms`. Closed executable examples are named
theorems as well; if they require compiled evaluation, they use `#assert_compiled` rather than an
anonymous `#guard`.

### 3. Receipt contract

`RunReceipt` is the common durable envelope. It binds federation, content root, activation,
session, epoch, actor root, player key, monotonic counter step, run seed, pre/post world states,
contribution, and transcript digest. Construction carries proof that `applyContribution` maps the
exact pre-world and contribution to the exact post-world.

That proves a checked world transition, not by itself that a particular game was played. The
`JudgedRun` witness supplies that missing fact. Consumers use the strongest type they need:

| Consumer | Minimum accepted evidence |
|---|---|
| Local replay viewer | raw transcript plus emitted program; explicitly non-settled |
| Personal unsynced field note | local replay record; cannot enter canon or custody |
| World-state update | authenticated game-specific `JudgedRun` |
| Field Archive beta record | `GameEffect.recordRun` over a `JudgedRun` |
| Score league | judged receipt plus league mission/epoch match |
| Salvage asset creation | judged receipt plus one-shot DrEX ingress policy |
| Alpha promotion | known beta artifact plus exact curator capability/admission |

Replay identity is not attacker-selected display JSON. It is derived from the committed domain and
canonical transcript bytes. The same receipt key or player counter step cannot settle twice.

### 4. Economy contract

PoA has several deliberately separate value layers. Collapsing them into one fungible number would
recreate the weakest part of the Neocadia design.

| Value layer | Meaning | Transferable? | Creation rule |
|---|---|---:|---|
| Run resources | health, charge, tools inside one run | No | initial config and legal game transitions |
| World meters | intel, supplies, cohesion, influence, score | No | bounded judged `Contribution` only |
| Reputation/best run | evidence of mastery or reliability | No | fold over matching judged receipts |
| Relic discovery | the fact an allowed `RelicId` was encountered | No by default | judged receipt and mission allowlist |
| Salvage claim | an exact custodiable object derived from a discovery | Policy-specific | one-shot crown/ingress from eligible receipt |
| Bazaar asset | a claim admitted to DrEX custody | Yes when its policy permits | conservation-preserving ledger transition |
| Choir voice | eligibility under one proposal regime | Never a saleable game balance | proposal-specific proof |
| `$DREGG` holding | fact about the main Dregg federation | Externally governed | pinned external state proof; never PoA minting |

Current `WorldState` meters are monotone. Repair, research, sacrifice, or other sinks therefore need
their own Lean-owned effect with explicit authorization and conservation; the UI must not simulate a
subtraction from the public meter. Score is not money. A relic appearing in `discoveredRelics` does
not automatically create a tradable asset. `$DREGG` does not buy stronger tools, better random
tables, safer expeditions, or alpha canon.

### 5. Canon contract

Play may register the mission's exact artifact as known beta canon. The game path preserves alpha
and superseded sets byte-for-byte. Promotion and supersession require:

- the exact four-part artifact reference;
- matching federation/content/activation/session/epoch;
- the pinned curator key;
- expected revision and monotonic curator counter;
- an opaque capability for that exact tagged action.

Collections and theory-board text are not automatically canon. They are views over artifacts,
receipts, and signed claims. Free-form player prose remains commentary until a curator deliberately
associates or promotes an exact object. A generated companion, room description, or name cannot
smuggle itself into alpha canon through popularity.

### 6. Accessibility contract

Every game declares which assists are presentation-only and which modify semantics.

- Presentation-only: high contrast, text scale, redundant symbols, reduced animation, captions,
  focus indicators, input remapping. These do not enter scoring.
- Semantic: extended action budget, preview, hint, undo, simplified input sequence, auto-fire. These
  must be in the authenticated configuration or a content-bound assist profile.
- No assist is silently penalized. If missions intentionally compare an identical challenge, they
  select compatible profiles before play rather than discounting a player afterward.
- All essential state has a non-color cue. All navigation and turn-based games have a keyboard path
  and meaningful screen-reader announcements.

The content pack describes assists as rule parameters. TypeScript and CSS implement presentation;
they do not decide whether an assisted run is valid.

## Adapted mechanics catalog

Engineering cost assumes the shared mission/receipt shell exists. Content burden is the recurring
authoring load after the code ships, which is often the more important number.

| # | PoA mechanic | Raw pattern | Player verb and PoA use | Receipt/world output | Eng. | Content |
|---:|---|---|---|---|---:|---:|
| 1 | Signal Triangulation | N-QUIZ plus Mastermind-like deduction | Probe a hidden transmission through bounded guesses and exact feedback | intel, score, possible signal artifact | S, present | Low |
| 2 | Relay Repair | N-GEAR | Place conduits to connect a source to required systems through obstacles | supplies/cohesion, repair record | S, present | Low |
| 3 | Salvage Lock | N-LOCK | Pair alien glyphs before a deterministic pressure budget expires | score, allowed salvage relic | S, present | Low |
| 4 | Black Box Reconstruction | N-BLACKBOX | Order 4-8 telemetry fragments into an accepted sequence | intel, beta field record | S | Medium |
| 5 | Containment Inspection | N-INSPECT | Mark declared anomalies between two sensor sweeps without false positives | intel/cohesion, inspection artifact | S/M | Medium |
| 6 | Drift Probe | N-PROBE | Tune range, distinguish false blips, hook a contact, and maintain lock | intel or allowed salvage claim | M | Low/Medium |
| 7 | Damage Control | N-PIPE | Route finite parts through concurrent repair stations in the correct order | supplies/cohesion | M | Low |
| 8 | Pressure Garden | N-TEND | Tend a reclamation culture across finalized ticks and respond to mutations | supplies, sample artifact | M | Medium |
| 9 | Impossible Deck | N-LOOP | Navigate rooms whose wrap, mirror, phase, or door relation changes by declared rule | intel, map fragment | M | Medium |
| 10 | Archive Restoration | N-BLACKBOX | Assemble damaged schematic pieces with positional and adjacency constraints | intel, schematic relic | M | Medium |
| 11 | Tool Calibration | N-GEAR/N-QTE | Tune a tool against a known trace using bounded adjustments | supplies, calibrated-loadout eligibility | S/M | Low |
| 12 | Episode Debrief | N-QUIZ | Answer Sentyr-authored observation questions tied to evidence in an episode | score/reputation, no canon mutation | S | Medium |
| 13 | Emergency Drill | N-QTE | Execute an authored prompt track against a training simulation or video cue | cohesion, drill record | M | Medium/High |
| 14 | Deck Cartography | N-NAV/N-LOOP | Traverse and annotate a signed compartment graph | map observations, beta report | M | High |
| 15 | Sensor Fusion | N-INSPECT | Combine separately signed partial observations into one declared classification | intel/cohesion, fused report | M | Low/Medium |
| 16 | Quarantine Desk | N-QUIZ/N-INSPECT | Classify arrivals or cargo from bounded evidence and policy rules | cohesion/influence, no automatic custody | M | Medium |
| 17 | Hull Choir | N-QTE | Coordinate several players' timed maintenance actions without popularity voting | cohesion, multi-party run receipt | M/L | Low |
| 18 | Crown Wreck Survey | N-PROBE/N-NAV | Allocate a finite team and probe budget among uncertain locations | intel/salvage, survey report | M | Medium |
| 19 | Sleeping Deck Retrieval | N-TEND/N-LOOP | Choose when to enter, take a bounded object, or withdraw before wake state advances | relic or bounded loss | M | High |
| 20 | Free Galley Ration | N-DAILY | Claim one deliberately mundane ration per finalized epoch | low-stakes personal claim, no market mint | S | Low |
| 21 | Salvage Crate | N-DAILY | Open a seed-committed daily table whose contents were fixed before activation | allowed relic or cosmetic record | S | Low/Medium |
| 22 | Daily Dispatch | N-DAILY | Attempt one shared mission selected from epoch and catalog | ordinary judged run plus daily badge | S | Low |
| 23 | Field Archive | N-COLLECT | Inspect discoveries, provenance, hints, status, and recent acquisitions | projection over receipts/canon | S/M | Medium |
| 24 | Personal Locker | N-COLLECT/N-SAVE | Arrange receipted objects, patches, and reports in a personal display | no new authority; portable projection | S/M | Low |
| 25 | Deck Map | N-NAV | Move among signed scenes, inspect hatches, and launch available missions | no mutation except explicit interactions | S/M | Medium |
| 26 | Expedition Officer | N-ONBOARD | Receive contextual, optional briefings and request help without leaving the fiction | local tutorial state only | S | Medium |
| 27 | Expedition League | N-MINI/N-DAILY | Submit best matching judged run to a rotating challenge | recomputable standing | M | Low |
| 28 | Crew Expeditions | N-NAV/N-PIPE | Plan loadouts and combine separately signed actions into one mission | multi-party contribution/report | L | Medium |
| 29 | Theory Board | N-COLLECT | Attach a signed claim to exact receipts, artifacts, and episode evidence | evidence graph; commentary by default | M | High |
| 30 | Prediction League | N-DAILY | Commit and later reveal a prediction about a declared event | non-transferable reputation | M | Medium |
| 31 | Research Commons | N-COLLECT | Contribute eligible custody objects toward a declared research threshold | custody sink plus bounded communal unlock | M/L | High |
| 32 | Sealed Salvage Auction | N-COLLECT, not its economy | Submit private bids for an exact salvage claim | DrEX clearing and custody receipts | L | Low |
| 33 | Batch Barter | N-COLLECT | Express private wants and clear compatible cycles atomically | conserved multi-asset custody change | L | Low |
| 34 | Relic Loan | N-COLLECT/N-SAVE | Grant time- or use-bounded custody without permanent sale | capability, expiry, return/recovery receipt | M/L | Medium |
| 35 | Choir Chambers | N-DAILY's rotating event shape | Compare public and eligible-holder preferences under declared regimes | tally receipt only | M/L | Low |

The first three have Lean semantic modules. “Present” does not imply that every runtime, node,
emitter, deployment, or browser boundary is already complete.

## Content burden and authoring economy

Platform depth works only if content is cheaper to add than code and if Sentyr can control reveals
without authoring every numeric detail by hand.

### Burden classes

| Burden | What one content unit requires | Good uses |
|---|---|---|
| Low | parameters, abstract glyphs, board seed, reward budget, short flavor line | Signal, Relay, Salvage Lock, calibration, daily selection |
| Medium | 4-10 authored fragments, item descriptions, a scene pair, a small map, or 5-10 evidence questions | Black Box, Inspection, Archive sets, debriefs |
| High | a coherent anomaly, multi-room expedition, new rule vocabulary, substantial art/audio, or lore with future implications | impossible decks, sleeping entities, theory arcs |
| Very high | new character intelligence, alpha-canon revelation, episode integration, or cross-product continuity | Aspects and major promotion events |

### Content unit templates

| Template | Minimum useful unit | Mechanical validation |
|---|---|---|
| Signal | target alphabet, length, attempt cap, reward | target in alphabet, finite feedback table, solvability smoke theorem |
| Relay | grid, source, targets, pieces, obstacles | coordinates in range, inventory bounded, declared solution reaches targets |
| Lock | pair IDs, board size, action budget, seed | even population, exact multiplicity two, deterministic permutation |
| Black Box | 4-8 fragments, accepted orders, optional adjacency hints | each accepted order is a full permutation; no undeclared fragment |
| Inspection | base asset, variant asset, hit regions, false-positive policy | regions in bounds, nonempty targets, overlap policy explicit |
| Probe | contact table, noise schedule, phase windows | weights/bounds valid, seed commits schedule, terminal result bounded |
| Pipeline | stations, recipes, durations, inventory | recipe steps name declared stations; conservation; finite completion budget |
| Deck graph | rooms, directed exits, modifiers, extraction nodes | identifiers unique, exits resolved, extraction reachable when promised |
| Debrief | questions, choices, answers, evidence references | answer index valid; evidence points to activated episode/content |
| Archive set | artifact IDs, silhouettes, hints, descriptions, reveal policy | IDs unique and mission-allowlisted; status text cannot assert alpha |

The curator tool should generate the mechanical boilerplate, preview every state/reward/canon delta,
and show exactly which facts become visible at activation. It must not generate new lore behind
Sentyr's back. High-burden units should be sparse; one strong anomaly can support several games,
archive entries, debriefs, and a later episode reference.

### Reuse without homogenization

Reuse state-machine families, not finished skins. A pair-board family can power an alien lock,
memory recovery, or sensor correlation, but each deployed game needs one fiction-specific decision
that changes how it is played. Conversely, one authored content unit should feed several surfaces:

```text
one deck anomaly
  -> map compartment
  -> expedition encounter
  -> Inspection sweep
  -> recovered Black Box fragments
  -> Archive entries
  -> debrief questions
  -> optional Bazaar object
  -> possible later alpha promotion
```

This is the preferred depth multiplier: richer connections per authored truth, not more generated
proper nouns.

## Swarm-sized implementation packets

Each packet has one primary file family and an objective completion gate. Workers add isolated files
and fixtures; the integration lane alone edits shared registries, umbrella imports, emitter routing,
and release manifests. This keeps the shared tree workable.

| Packet | Owned surface | Deliverable | Completion gate |
|---|---|---|---|
| P01 Black Box kernel | new `BlackBoxReconstruction.lean` | config/state/action/replay/judge; exact and enumerated accepted orders | permutation, bounds, deterministic replay, hostile submissions, axiom census |
| P02 Inspection kernel | new `ContainmentInspection.lean` | finite hit regions and false-positive policy | out-of-bounds/reflexive/duplicate clicks refuse as declared; score bound |
| P03 Daily selector | new `DailyMission.lean` | finalized-epoch catalog rotation | same epoch/catalog selects same mission; empty/stale catalogs refuse |
| P04 Deck graph | new `DeckGraph.lean` | signed scene/room/hotspot schema and validation | unique IDs, resolved exits, activation monotonicity, promised extraction reachable |
| P05 Archive model | new `FieldArchive.lean` | receipt-origin records, hints, projections, beta/alpha/superseded view | no acquisition without judged run; monotonic acquisition; canon status exact |
| P06 Assist profiles | new `AssistProfile.lean` | presentation/semantic distinction and config commitment | semantic assist cannot be introduced after activation; reward policy explicit |
| P07 Content schema | isolated POAG1 schema/fixtures | author JSON/YAML shapes for packets P01-P06 | malformed, duplicate, stale, oversized, and unknown IDs fail closed |
| P08 Emitter expansion | new game-specific emitter modules | deterministic descriptors/tables for selected kernels | byte-identical double emission; checked-in pins; no handwritten semantic fallback |
| P09 Runtime interpreter | one adapter module per game | load emitted artifact, replay transcript, call settlement boundary | differential corpus against Lean; artifact mismatch/absence refuses |
| P10 Shared game shell | isolated web components | briefing/start/play/result/receipt inspector shell | keyboard, reduced motion, closed shadow, local-vs-judged labeling |
| P11 Deck/archive UI | new declarative renderers | deck map, Field Archive, personal locker | spoofed status cannot render as alpha; provenance links exact receipt |
| P12 Officer/onboarding | local presentation module | first-encounter queue, contextual help, replay/skip controls | never interrupts active run; flags are presentation-only; accessibility E2E |
| P13 Debrief pack | new content fixture family | episode-linked question format and one non-canon test pack | invalid answer/evidence refs refuse; extension and site render same pack |
| P14 DrEX crown adapter | isolated ingress policy module/test | eligible salvage receipt to one exact asset claim | duplicate, wrong epoch/domain/relic/game/transcript tamper refuse |
| P15 Bazaar crown journey | integration test and isolated fixtures | expedition -> crown -> sealed bid -> threshold clear -> custody | conservation, n-1 refusal, declared privacy grade, crash/replay cases |
| P16 Projection cache | local IndexedDB/version module | receipt-derived saves, backups, ordered migration | deleting cache loses no authority; corrupt/newer schema fails recoverably |
| P17 Hostile browser suite | new Playwright specs/fixtures | route spoof, SPA remount, content swap, counter replay, status spoof | every attack visibly refuses without stale success UI |
| P18 Curator workbench | isolated preview surface | build/validate mission; show state, contribution, reveal, canon delta | signed bytes previewed are exact activated bytes; stale revision refuses |

Integration checklist for each semantic packet:

1. Narrow Lean build of the new module.
2. Named theorem and axiom/compiled census.
3. Emitter artifact with deterministic byte pin.
4. Runtime differential and refusal corpus.
5. Closed `JudgedRun` registry addition by the integration owner.
6. Game added to source/release PoA gates only after all preceding steps exist.

## Anti-patterns to reject

1. **Skin transfer.** Renaming fish as salvage or candy as circuitry without changing the decision
   structure creates generic arcade filler.
2. **One magic currency.** World contribution, mastery, canon, custody, governance voice, and
   `$DREGG` are not interchangeable balances.
3. **Client-clock truth.** Daily selection, growth, expiry, and pressure use finalized epochs,
   committed ticks, or transcript actions—not `Date.now()`.
4. **Unreceipted scoreboards.** A score posted by the browser is a local field record until the
   game-specific judge settles it.
5. **Second semantics in TypeScript or Rust.** Renderers interpret Lean-emitted rules and adapters
   invoke the verified boundary; they do not independently decide legality or rewards.
6. **AI as judge.** Creative ordering or prose may be fun, but an unbounded model response cannot
   determine receipts, custody, or canon. Accepted semantic alternatives are explicit.
7. **Generated canon.** Procedural text, room names, companions, and player theories remain beta
   artifacts or commentary until exact curator promotion.
8. **Tradable-by-default collectibles.** Discovery, possession, custody, exhibition, loan, and sale
   are separate policies.
9. **Daily punishment.** No essential progression, canon access, or competitive power depends on a
   login streak. Recurrence offers a shared occasion, not an attendance job.
10. **FOMO content deletion.** Old content roots and receipts remain verifiable. An event may stop
    accepting new runs without erasing prior records.
11. **Fake privacy.** Operator-visible hiding, process separation, and independent threshold
    operation are labeled distinctly and tested according to the deployed construction.
12. **Holder power creep.** `$DREGG` can prove membership or select a declared ballot chamber; it
    does not improve loot tables, damage, timing, or canon authority.
13. **Unbounded collective progress.** Aggregates retain per-mission ceilings, one-shot receipts,
    and explicit epoch scopes.
14. **Content before tooling.** Do not commission dozens of encounters before validators, preview,
    emission, signing, rollback, and provenance views work on one content unit.
15. **Premature Aspects.** A generic procedural pet would spend important fiction for a familiar
    retention mechanic. Keep the dormant schema until Sentyr activates their narrative debut.
16. **Anonymous executable checks.** Do not replace named Lean facts with `#guard` case tests that
    cannot be cited or audited.

## Six-epoch rollout

An epoch here is a signed, reproducible content activation, not a promised calendar interval. The
M1-M6 labels below are rollout labels, not literal values of the federation's `contentEpoch`; the
deployed bootstrapping epoch already precedes this sequence. Each mechanics epoch is independently
deployable and reversible by activating a later epoch. Old roots, programs, and receipts remain
reproducible.

### Mechanics epoch M1 — Complete the field terminal

Purpose: expand the live field terminal from one browser-playable game to the three proved finite
games while preserving its existing trust boundaries.

- Keep Signal Triangulation live and activate Relay Repair and Salvage Lock in one successor signed
  POAG1 bundle.
- Show a minimal deck map, Expedition Officer, daily-board placeholder, Field Archive hatch, and
  Bazaar hatch.
- Distinguish local replay, submitted run, judged receipt, and refused settlement in the UI.
- Settle one run into bounded world state and one beta artifact.
- Ship keyboard/reduced-motion/high-contrast behavior for all three games.

Gate: browser, runtime, node, and Lean replay agree on exact transcripts; content, signer, seed,
counter, or artifact tampering refuses.

Content burden: three abstract game packs and short briefing/archive copy. No deep lore required.

### Mechanics epoch M2 — Daily life

Purpose: make the ship feel like a place with recurring, non-punitive activity.

- Finalized-epoch Daily Dispatch selection.
- Field Archive provenance/status views and Personal Locker projection.
- Free Galley Ration or similarly mundane daily ritual with no market value.
- One Episode Debrief pack and contextual Officer teaching.
- Diegetic world instruments for bounded aggregate contributions.
- Content-bound assist profiles and accessibility preflight.

Gate: client time changes nothing; cache loss loses no authority; no daily action can settle twice;
archive status cannot be spoofed from presentation data.

Content burden: one small question pack, archive descriptions, hints, and station copy.

### Mechanics epoch M3 — Unknown decks

Purpose: connect short games to the micro-exploration premise and begin The Descent braid.

- Declarative deck/compartment graph with signed hotspots.
- Black Box Reconstruction and Containment Inspection.
- One Impossible Deck modifier pack integrated with Descent or a finite graph expedition.
- One anomaly expressed across map, encounter, inspection, fragments, archive, and debrief.
- Extraction decisions and beta field reports.

Gate: promised extraction is reachable, all discoveries are predeclared, free-form field prose has no
canon authority, and the same anomaly's cross-surface references are content-addressed.

Content burden: one carefully authored anomaly, 4-8 fragments, one sweep pair, and a small room map.

### Mechanics epoch M4 — Dark Bazaar

Purpose: exercise DrEX because private exchange and exact provenance improve the game, not as a
detached protocol demo.

- Crown one eligible expedition receipt into one exact salvage claim.
- Sealed-bid auction with atomic custody transfer.
- One batch-barter or wants-list demonstration if the same-opening and threshold path is wired.
- Public provenance from mission/content root through discovery, crown, offer, clearing, and custody.
- Explicit deployed privacy label and threshold roster.

Gate: duplicate crown, wrong domain/epoch/relic, tampered transcript, insufficient threshold, replay,
and conservation violations all refuse; no producer-only proof path remains unwired.

Content burden: a tiny catalog of abstract salvage policies; no speculative universal marketplace.

### Mechanics epoch M5 — Crews and research

Purpose: turn verified individual play into collaboration without making everything a vote.

- Crew rosters, shared archive, and rotating Expedition League.
- Sensor Fusion or Hull Choir as the first multi-party game.
- Theory Board claims linked to exact evidence.
- Prediction League with non-transferable reputation.
- Research Commons consuming explicitly eligible custody objects under a declared threshold.
- One Choir proposal showing a selected ballot regime without granting story authorship.

Gate: standings recompute from receipts; multi-party actions are separately signed and combined
deterministically; Sybil-sensitive eligibility is explicit; research sinks conserve custody.

Content burden: crew/league framing, one research question, and moderation—not a new setting bible.

### Mechanics epoch M6 — Curated living world

Purpose: close the loop from play to selective authorial adoption and sustainable content creation.

- Curator workbench for mission creation, semantic preview, activation, promotion, supersession, and
  rollback-safe next epoch.
- Promote one exact beta artifact into alpha canon only if Sentyr chooses it.
- Show its history in the Archive and, when appropriate, the series or an official dispatch.
- Add Drift Probe, Damage Control, or Pressure Garden from validated low/medium-burden templates.
- Publish the one-command follower/replay path for independent verification of every epoch.
- Keep Aspect content disabled unless its separate narrative activation is signed.

Gate: the reviewed bytes equal the activated bytes; stale revision/counter/key/content refuses;
promotion changes only the exact selected artifact; an independent follower can reproduce roots and
replay the promoted artifact's originating run.

Content burden: one promotion candidate, one additional mechanical pack, and sustainable author
templates. The system should now make the next unit cheaper rather than demanding a content sprint.

## Success condition

Platform depth is present when a player can move naturally among several distinct verbs—inspect a
deck, play a finite game, recover a record, understand its provenance, contribute to the ship,
display or trade an eligible object, collaborate with a crew, and watch selected discoveries gain
meaning—while every authoritative transition remains reproducible and Sentyr retains exact control
over canon. It is not measured by account counts, number of generated characters, raw minigame
count, or the nominal size of an item economy.
