# Path of Angels as a game platform

Status: long-horizon product architecture and implementation program, 2026-08-04.

This document answers a different question from `docs/poa/ROADMAP.md`. The current roadmap says
what the live beta has established and what the next content epochs can activate. This document
asks what Path of Angels should become if the repository is treated as raw material for a fresh
game platform rather than as a pile of crates that must all be snapped together.

The source material is unusually rich: Lean game kernels, receipt and capability systems, a daily
Descent, party and custody machinery, DrEX, threshold FHE and MPC experiments, a browser extension,
an isolated federation, and the unfinished Neocadia design corpus. None of those names is a product
requirement. The requirement is a coherent place aboard the Khovokhi where many small activities
feed one another, the games remain enjoyable without their rewards, discoveries can acquire
meaning, private play is genuinely private at the grade claimed, and Sentyr retains exact editorial
control.

The platform comparison is Neopets in **depth and connected surface area**, not audience size,
visual style, or economy. Path of Angels should eventually contain dozens of reasons to visit and
several ways for one action to matter. It should not require dozens of unrelated applications or a
content furnace.

## 1. Product thesis

The YouTube series concerns the Khovokhi at the macro scale: where the ship jumps, what its people
choose, and what happens in alpha canon. The platform concerns the micro scale: what exists inside
roughly a thousand mostly unexplored eight-metre decks of an Artificer-built God-Engine.

The core fantasy is not “vote with a token.” It is:

> I took an expedition officer into a place the crew did not understand, made choices under
> uncertainty, brought back an exact record, and changed what the people aboard the ship know.

That fantasy supports a whole platform:

- short games are instruments, drills, repairs, and forensic tasks;
- Descent expeditions connect those instruments into risky journeys;
- the Field Archive makes discoveries legible and worth collecting;
- crews turn individual evidence into shared investigations;
- the Dark Bazaar gives a few custody objects interesting private lives;
- the Choir gives declared questions several fair decision procedures;
- the series can selectively promote a beta discovery into alpha canon;
- independent nodes can reproduce the result rather than trusting the official page.

The Khovokhi is the world, not the pet. The Expedition Officer is initially the player's persistent
point of view. Aspects may later become precious personal companions, but only when the fiction
introduces them. A generic procedural pet launched early would spend one of the setting's strongest
ideas on a retention widget.

## 2. Lines that do not move

1. **Sentyr authors alpha canon.** No score, vote, market, model, or popularity threshold writes the
   show automatically.
2. **The mechanic must be worth playing.** A receipt can make a good decision more meaningful; it
   cannot make a dull interaction fun.
3. **Lean owns semantic authority wherever practical.** Legal state, transition, generation,
   scoring, contribution, custody admission, ballot rules, canon movement, and circuit descriptions
   belong in Lean. Rust and TypeScript do not receive quiet semantic twins.
4. **Content is signed data.** Rooms, dialogue, puzzles, relic policies, maps, and reveal schedules
   are versioned packs, not application releases.
5. **A receipt says exactly what it proves.** Local replay, operator-visible privacy, process
   separation, threshold privacy, and independently operated threshold privacy are different
   claims.
6. **Randomness is precommitted.** The operator, curator, signer, and player cannot reroll a target,
   route, loot table, jury, or spill after seeing the result.
7. **Value layers remain separate.** Run resources, ship contributions, reputation, discovery,
   custody, canon, Choir voice, and `$DREGG` are not one balance.
8. **Failure does not become attendance discipline.** Daily activity is a shared occasion, not a
   streak job. Old content and receipts remain inspectable.
9. **Accessibility is semantic when it changes the challenge.** Presentation aids are free;
   challenge-changing assists are declared in the signed mission rather than punished afterward.
10. **The implementation is public.** Spoilers may be sealed cryptographically, but fairness,
    security, or governance cannot depend on nobody reading the repository.

## 3. Treating the repository as raw material

Reuse a component only when it preserves the right object and the right authority boundary. Reuse
an idea when the implementation carries the wrong semantics. Rebuild freely when neither is true.

| Existing material | What it proves or teaches | PoA treatment |
|---|---|---|
| Signal Triangulation, Relay Repair, Salvage Lock | Lean can define a finite game and emit a browser-consumed table | Keep as the first arcade family and extend the emission discipline |
| Black Box, Inspection, deck and archive Lean modules | More content families fit the same judge/canon spine | Activate through signed packs after the runtime authority path is complete |
| native Descent and daily Descent | Seeded runs, executor-backed verbs, durable replay, sessions, and provenance exist | Redesign the expedition decision space and fiction; do not inherit the solved tightrope unchanged |
| Dungeon Lean laws and Campaign records | Extraction debt, attenuating capacity, absorbing banks, portable event chains, settlement phases, and consequence grants have precise forms | Carry the laws and event shapes into a new PoA Lean transition; do not make the Rust Campaign coordinator authoritative |
| `.dungeon` DSL/compiler | Bounded IR, unsupported-feature refusal, frozen variables, and phantom/dropped-tooth checks are good compiler discipline | Build a new Lean-owned deck/encounter IR; the current navigation/dialogue subset is not the PoA content language |
| party, quest, gear, craft, trade, guild, faction, cheevo, saga | Capabilities, completion identity, custody identity, and cross-system handoff are executable | Extract shared nouns and laws; do not expose every crate as a PoA feature |
| tavern/shared world | Several identities can inhabit one receipted place | Recast as crew rooms, mission control, or the inhabited decks if the operational weight is justified |
| Neocadia specifications | Good activity shapes, contextual onboarding, collections, deterministic rotation, and world-stage projections | Re-derive schemas and rules; import no Phaser app, balance constants, lore, or local-clock authority |
| DrEX and the Dark Bazaar | Private order intake, proof carriers, custody consequences, FHE/MPC paths, and exact gaps are concrete | Make salvage journeys the low-stakes integration ground for real DrEX, with honest privacy labels |
| PoA browser extension | Signed routing can add a verified companion surface to YouTube and social pages | Use for episode evidence, debriefs, polls, and field records; never make the host DOM authoritative |
| isolated PoA federation and operator kit | A distinct history can run and be followed independently | Make reproducibility and participation a platform feature, not merely an ops note |

The extraction rule is simple: **preserve identity, discard accidental packaging**. A completion
that becomes an archive entry and a salvage claim must remain the same run object. A relic traded in
the Bazaar must remain the same custody object. In contrast, a Rust module named `guild` does not
force PoA to have a guild system, and a Neocadia activity named fishing does not become “space
fishing” by changing its nouns.

## 4. The reinforcing loops

PoA needs connected loops at several time scales. Each one should work at small population and
become richer, rather than merely functional, when more people arrive.

### 4.1 Moment loop: read, choose, resolve, understand

A player reads a compact situation, chooses one consequential verb, sees the result, and can ask
why it happened. A good room or minigame turn lasts seconds; a complete finite game lasts roughly
one to five minutes. Exact explanation is part of the pleasure: the same terms used by the judge
become the readable post-action card.

This loop is served by Signal, Relay, Lock, Inspection, Black Box, calibration, and later room
encounters. It must be enjoyable in practice mode with no economy attached.

### 4.2 Expedition loop: prepare, descend, improvise, extract

An officer chooses a route hypothesis, finite tools, an assist profile, and possibly a crew. The
expedition traverses a signed deck graph. Encounters consume incomparable resources, alter future
options, and sometimes disclose incomplete information. At safe points the player chooses whether
to extract known findings or continue with more at risk.

The current Descent is evidence that the executor and replay spine work, not a final ruleset. Its
ranked game was exhaustively shown to have zero strategic forks across sixteen maps: one optimal
move multiset, a dead headline verb, and a scalar tightrope mistaken for choice. PoA Descent must be
rebuilt around at least two incomparable budgets, information value, route commitment, loadout
identity, and extraction. Difficulty without branch points is not strategy.

### 4.3 Home loop: debrief, archive, equip, display

After a run, the officer returns to a stable personal station:

- inspect the exact field record and its proof status;
- place discoveries in the Archive or personal locker;
- compare a current run with one's own earlier route or a public ghost;
- equip or loan eligible tools without turning every discovery into property;
- read new hints unlocked by evidence rather than by a universal level number;
- prepare a theory, prediction, or later expedition.

This is where a collection becomes more than inventory. Discovery, study, custody, display, loan,
sale, consumption, and canon status are distinct actions and policies.

### 4.4 Ship loop: many small acts make a visible state

Judged runs yield bounded `Contribution` values. Finalized contributions drive diegetic ship
instruments, deck-restoration stages, research thresholds, and predeclared conditional releases.
The current canonical vocabulary remains small: intel, supplies, cohesion, influence, score, and
allowlisted relic identifiers. Fictional displays such as propellant, hull integrity, or morale are
projections of an explicit versioned transition; they are not extra browser-owned balances.

One shared condition should open several pieces of content. For example, enough exact sensor work
might activate a new sweep image, add an Archive hypothesis, open a route in the deck graph, and
change an Officer briefing. This is the useful part of Neocadia's restoration model. There is no
single permanent “100% restored” ending and no ability to buy past the activity with currency.

### 4.5 Social loop: form a crew around evidence

Crews maintain rosters, roles, shared expeditions, an archive shelf, theories, and a rotating
challenge. The unit of social play is not always a vote:

- combine separately signed observations;
- assign distinct expedition tools and roles;
- attempt an asynchronous relay whose state persists between members;
- sponsor an Archive restoration or public exhibition;
- commit a prediction and reveal it later;
- review a disputed field report under a declared jury rule.

A solo player must remain able to play the core activities. Crews add composition, coordination,
and interpretation rather than gating basic access.

### 4.6 Economy loop: discover, crown, exchange, use

Most discoveries are records, not assets. An eligible exact discovery may be crowned once into a
custody claim. The claim can be displayed, loaned, researched, consumed by a declared sink, swapped,
or offered through an appropriate Bazaar hall. Provenance follows the same object through every
step.

The economy exists to create decisions and histories:

- keep a strange object because it completes an Archive set;
- loan it to a crew so they can attempt a study;
- place it into a sealed auction without publishing every valuation;
- consume it to repair or unlock something explicitly authored;
- trade compatible wants atomically without a public negotiation graph.

It is not a yield machine. `$DREGG` may buy services such as hosting, private computation, premium
narration, or entry to a bounded event. It never improves loot tables, expedition safety, timing,
or alpha-canon authority.

### 4.7 Editorial loop: discover beta, promote exactly

The game may reveal or compose beta material only inside a curator-authored possibility space. A
field record can contain an exact deck coordinate, artifact, reaction, route, and player report.
Free prose is commentary. A generated name is a player label. Neither is alpha canon.

Sentyr may later select one exact beta artifact, attach or revise official interpretation, and sign
an alpha promotion. The Archive retains the originating receipt and promotion history. A later
correction supersedes rather than erases it. Popularity, market price, or a Choir tally may inform
the editorial decision, but cannot exercise the curator capability.

This makes promotion rare and powerful. “The object our crew found on deck 447 appeared in an
episode” is a genuine reward without delegating the series to a procedural generator.

### 4.8 Episode loop: watch, inspect, act, return

The extension can place an authenticated companion beside an episode or social post:

- an evidence marker at an exact timestamp;
- an episode debrief or observation task;
- a macro poll with its declared eligibility regime;
- a relevant Archive record or ship instrument;
- a route into the beta site for a game whose content epoch is active.

The extension authenticates the PoA route and content root, and must remove stale panels on host SPA
navigation. YouTube, X, and their DOMs provide presentation context only. A poll result becomes
authoritative through its own signed/finalized path, never because the extension observed a number
on a page.

### 4.9 Federation loop: reproduce, follow, participate

A technically interested player can inspect a receipt, replay the judge, reproduce a content
bundle, follow the federation from genesis, and eventually operate a node. This is not required for
ordinary play. It is what turns “trust us” into a graduated set of verifiable claims.

Semi-trusted account signup, recovery, and moderation can live at the application edge. Consensus
admission remains a distinct Lean-owned rule. A convenient login does not silently become a
validator credential.

### 4.10 Aspect loop: bond, interpret, compose

This loop remains dormant until the story introduces Aspects. When activated, an Aspect is an
authored, finite Artificer intelligence with constrained communication, equipment bodies, persistent
identity, and rules for copying, custody, loss, and recovery. Players learn how a particular Aspect
communicates and bring it into several activities. It is not an unbounded chatbot or a universal
stat bonus.

The platform can prepare generic companion persistence, equipment capabilities, and finite
behavior semantics. It must not instantiate an “Aspect” or publish Aspect lore before the signed
narrative activation.

## 5. Shared state vocabulary

The platform should have a small, explicit language shared by every subsystem. The following is a
proposed conceptual vocabulary, not a demand to preserve current crate type names.

### 5.1 Immutable identity

| Concept | Bound fields and purpose |
|---|---|
| Deployment | federation domain, genesis root, protocol epoch, validator policy |
| Content epoch | curator key, monotonic counter, content root, activation digest, content session |
| Activity | ruleset identifier/version, content unit, proof profile, privacy grade, assist policy |
| Mission | activity, seed commitment, activation window, budgets, allowed contributions and relics |
| Run | deployment, mission, actor/player, counter step, party roster, canonical transcript digest |
| Artifact | content identity plus exact discovery/reaction/coordinate and origin run |
| Proof profile | executable judge/artifact version, circuit/VK epoch when used, public statement shape |

No subsystem substitutes display labels, URLs, host timestamps, or mutable JSON for these
identities. Full-width roots remain full-width through commitment, custody, and market paths.

### 5.2 Authoritative state

| Family | Minimum state |
|---|---|
| Player | stable signing/account relation, monotonic play counter, officer identity, declared session grants |
| Expedition | party roster, deck/room, route history, resources, tool custody, knowledge flags, provisional finds, terminal/extracted state |
| World | versioned meters, activated deck/research stages, aggregate replay keys |
| Archive | artifact reference, origin, acquired status, beta/alpha/superseded state, revision history |
| Social | crew roster/roles, signed claims and evidence edges, proposal, eligibility regime, ballot or prediction commitments |
| Custody | one exact note/claim, owner/custodian, version, policy, provenance, spent/escrow/loan state |
| Market | eligible claim, order commitment, roster/session, clearing statement, settlement and custody changes |
| Federation | finalized turns, content statements, admission evidence, operator manifests and state roots |

### 5.3 Derived projections

Deck maps, Officer summaries, galleries, best runs, badges, collection percentages, activity
recommendations, notifications, and most leaderboards are projections over receipts. They may be
cached in IndexedDB or a server database. Deleting a cache can make the UI slower or emptier; it
must not destroy authority. Corrupt or future-version projection data fails recoverably and is
recomputed from durable inputs.

### 5.4 Five deliberately separate object states

One evocative item may occupy several states over its life, but none implies the next:

```text
encountered discovery
    -> archived beta artifact
    -> one-shot eligible salvage claim
    -> custody object
    -> offered / loaned / exhibited / researched / consumed object
```

Alpha canon is orthogonal to custody. A non-tradable field report may become alpha canon; an
expensive custody object may remain beta forever. This separation prevents the market from becoming
a canon auction.

### 5.5 Canon state machine

```text
authored possibility in an activated content epoch
    -> exact beta artifact discovered by judged play
    -> [optional] curator-signed alpha promotion
    -> [optional] curator-signed supersession with an explicit successor or correction
```

Player theory and free-form reports live beside this machine as signed commentary/evidence. They
can be cited by a curator action but never construct its state.

### 5.6 Privacy grades are state, not copy

Every private activity binds a named grade, roster, session, public statement, and permitted reveal:

1. `public` — inputs and outputs may be public;
2. `operatorVisibleHidingFri` — public observers do not see the witness, but the producer/operator
   may;
3. `processSeparatedThreshold` — threshold operations exist across isolated processes under one
   administrative operator;
4. `independentOperatorThreshold` — shares and protocol roles are independently operated;
5. a future malicious-secure grade — only after authenticated distributed custody, malicious DKG
   and computation integrity are actually exercised.

A UI may say “sealed” for atmosphere only if its receipt inspector gives the exact technical grade.

### 5.7 Account, identity, and session boundary

The beta's shared HTTP Basic Auth password is a deployment perimeter, not a player identity system.
Platform persistence needs a stable pseudonymous player identity, device/session delegation,
recovery, moderation handles, and explicit links to any external Dregg identity.

The existing session-key material supplies the right authority pattern: a player or custodian opens
a narrowly scoped, expiring, turn-budgeted play grant; attenuation may only narrow it; refused game
turns are not charged. PoA should put passkey or similarly ordinary onboarding above this boundary
so playing does not require signing every move or understanding a wallet. Recovery must rotate or
revoke session authority without rewriting old receipts.

A `$DREGG` holding proof is a separately scoped external fact pinned to a main-federation state
root. It does not become the player ID, a PoA validator credential, or an all-purpose entitlement.
Public profile, crew membership, private notes, blocklists, and market identity each disclose only
what their activity requires.

## 6. Where semantics live

The preference for Lean is architectural, not ceremonial. A Lean model beside a Rust decision is a
specification; it is not the implementation.

### 6.1 Lean

Lean owns:

- content and mission schemas, validation, and versioned migrations that affect meaning;
- game `Config`, `State`, `Action`, transition/replay, terminality, scoring, and contribution;
- generators and validators for boards, maps, encounters, loot tables, and daily selection;
- session/counter admission and game-specific `JudgedRun` construction;
- archive acquisition, canon promotion/supersession, and world-state transition;
- capability attenuation and multi-party combination rules;
- custody admission, conservation, clearing, ballot, sortition, and reputation folds;
- descriptors for AIR/circuits and theorems connecting emitted artifacts to their denotation;
- canonical codecs/hashes whenever byte identity affects authority.

Large tables or circuit descriptions should be generated by Lean metaprograms and checked in as
content-addressed artifacts. Facts worth asserting are named theorems with an axiom census. Closed
compiled examples use the repository's compiled-assertion discipline; anonymous `#guard` checks do
not become release evidence.

### 6.2 Rust and the node

Rust owns transport, durable storage, networking, scheduling, proof orchestration, cryptographic
libraries, hardware acceleration, and narrow FFI adapters. It may propose candidate layouts,
routes, matches, or witnesses. Lean or a Lean-authored emitted verifier decides acceptance.

There is no “temporary” Rust judge that becomes authoritative when Lean is missing. An unavailable
Lean archive, unknown descriptor, stale VK epoch, absent private verifier, or mismatched content
root is a refusal with a specific error.

### 6.3 Browser and extension

TypeScript owns input capture, animation, audio, accessible rendering, local practice, network
requests, and projections. It can interpret a Lean-emitted finite table or descriptor and render
its result. It cannot independently score a settled run, select a daily seed, crown salvage,
compute canon status, or infer privacy from a successful request.

The browser is hostile by design: every settled action is canonicalized and checked again at the
authority boundary. Practice results are useful and clearly labelled, not passed off as receipts.

### 6.4 Content and generative tools

Content packs own prose, art, sound, characters, room templates, hints, accepted semantic
alternatives, reveal policy, and fiction-specific mappings. Generative tools can propose variants,
names, dialogue, encounter arrangements, or art. They do not sign activation, create alpha canon,
or define an unbounded judge.

An AI narrator may explain a landed state or choose prose within a confined set. The world resolves
the action. If authentic model provenance is claimed, the real attestation path must be live; a
self-signed fixture is not renamed production provenance.

### 6.5 Solver, FHE, MPC, and proofs

- A solver finds a route, match, clearing, or witness; the verifier checks it.
- FHE hides values during permitted computation; it does not prove that the computation was right.
- MPC limits what any participant learns; it does not supply public integrity by itself.
- A proof binds the declared relation and public statement; it does not imply that no operator ever
  saw the witness.
- Attestation identifies code or a service environment; it does not replace semantic verification.

PoA activities should be chosen to make these boundaries visible and testable, not to decorate the
site with cryptographic nouns.

## 7. Mechanics atlas

The catalog below is an option space for co-creation with Sentyr. It is deliberately larger than a
release plan. `Lean-table` means a finite emitted evaluator; `Lean-native` means a transition run
through the live Lean boundary; `VK` means a Lean-authored circuit/custom transition verifier;
`cap` means capability/cross-cell authority; `FHE`, `MPC`, and `DrEX` name the privacy/economy organ
the mechanic can honestly exercise.

### 7.1 Short instruments and arcade games

| Mechanic | Actual decision | Authority output | Technical exercise | Author load |
|---|---|---|---|---|
| Signal Triangulation | choose probes that maximize information under an attempt cap | signal record, intel, score | Lean-table, judge, extension prompt | Low |
| Relay Repair | place a finite inventory of conduits across obstacles and optional loads | repair record, supplies/cohesion | Lean-table graph reachability | Low |
| Salvage Lock | choose pair reveals and manage deterministic pressure | allowed discovery, score | Lean-table seeded multiplicity | Low |
| Black Box Reconstruction | order fragments where several sequences may be semantically accepted | telemetry artifact, intel | Lean-table permutations and adjacency | Medium |
| Containment Inspection | mark anomalies while pricing false positives | inspection artifact, intel | Lean-table hit regions; image content | Medium |
| Tool Calibration | spend limited adjustments to fit a noisy but committed trace | tool eligibility or repair record | Lean-native numeric bounds | Low |
| Drift Probe | decide when to scan, hold, hook, and recover a changing contact | contact record or provisional find | Lean-native finite phases and noise table | Low/medium |
| Damage Control | route finite parts through concurrent repair pipelines | supplies/cohesion | Lean-native conservation and schedules | Low |
| Pressure Garden | choose interventions across finalized growth ticks | sample artifact, supplies | Lean-native tick semantics; no client clock | Medium |
| Emergency Drill | choose or sequence responses against an authored prompt track | drill record, cohesion | emitted timing windows and assist profiles | Medium |
| Episode Debrief | answer evidence questions tied to exact episode references | observation reputation | signed content, extension, finite judge | Medium |
| Archive Restoration | fit fragments by shape, adjacency, and material clues | restored schematic | Lean-native assembly proof | Medium |
| Language Workbench | test a bounded grammar against paired signals and counterexamples | beta lexicon evidence | Lean-native grammar evaluator | High |
| Sensor Correlator | align two partial traces without seeing the full source | fused record | FHE or MPC input fusion at stronger tier | Medium |
| Fair Anomaly Deck | combine eight committed contributions into a fair selective-reveal deck | accepted draw attempts and opened cards | existing Lean HidingFRI fair-shuffle relation | Low/medium |

These games share a shell, not a scoring formula. Each needs one fiction-specific decision that
changes its play. A pair board with different art is not a new activity.

### 7.2 Expedition rooms and deck systems

| Mechanic | Actual decision | Authority output | Technical exercise | Author load |
|---|---|---|---|---|
| Route survey | choose which uncertain branch to spend time and sensors on | observations, map edges | Lean-native graph state | Medium |
| Push or extract | risk provisional finds against increasing cost/hazard | extracted run and spill | Lean-native multi-resource choice | Low per ruleset |
| Loadout pocket | arrange a few tools whose position/capabilities alter approaches | committed starting state | cap, custody, deterministic composition | Medium |
| Impossible Deck | navigate wrap, mirror, loop, phase, or nonlocal door rules | map fragment, intel | generator/validator, VK for rich topology | Medium/high |
| Containment approach | choose observe, communicate, bypass, stabilize, or retrieve | bounded reaction/artifact | content grammar plus Lean resolver | High |
| Crown wreck survey | allocate a finite party and probe budget among sites | survey record, salvage eligibility | private choices, multi-party combination | Medium |
| Sleeping-deck retrieval | decide entry timing, object choice, and withdrawal before wake advances | custody-eligible find or bounded loss | committed shared state, capability gates | High |
| Quarantine crossing | selectively disclose enough attributes to pass a policy | passage or refusal receipt | credentials, private predicates, VK | Medium |
| Shared-door room | two crews affect one space through different interfaces | joined state change | cross-cell observed fields, multi-signature | High |
| Recursive room | actions alter an earlier room or the interpretation of a route | versioned graph state | custom VK and replay | High |
| Drift rescue | choose fuel, contact confidence, and crew exposure under uncertainty | rescue result, cohesion | MPC sensor fusion; threshold output | High |
| Silent sector | coordinate without revealing chosen routes until rendezvous | combined expedition record | commit-reveal then MPC route intersection | Medium/high |
| Survey ghost | race or cooperate with a prior verified trajectory | comparative result | proof/replay, no trusted leaderboard | Low |
| Field extraction | choose which evidence, object, or injured tool occupies finite return capacity | exact retained set | conservation, provisional-to-custody boundary | Medium |

An anomaly is a reusable authored unit. One strong anomaly can supply rooms, sweep images, black-box
fragments, debrief questions, archive entries, a salvage policy, theories, and a possible later
episode reference.

### 7.3 Life aboard the ship

| Mechanic | Player verb | Authority output | Technical exercise | Author load |
|---|---|---|---|---|
| Free galley ration | take one mundane serving per finalized epoch | low-stakes personal record | monotonic counter and epoch selection | Low |
| Salvage crate | open a precommitted daily table | allowed object or cosmetic record | beacon/seed and table proof | Low |
| Maintenance dispatch | choose one of several bounded communal jobs | ship contribution | world fold and per-run ceiling | Low |
| Fabrication queue | commit materials and choose priority under finite capacity | tool/object or refund | custody escrow, scheduling | Medium |
| Research Commons | contribute, loan, or study eligible records/objects | research stage and provenance | threshold statement, custody sink/loan | High |
| Observation window | inspect a changing ship/external condition and leave evidence | observation record | finalized world projection | Low/medium |
| Personal locker | arrange field records, tools, patches, and display objects | no new authority | receipt-derived projection | Low |
| Archive gallery | curate a public view without changing canon or ownership | signed display manifest | capability-limited projection | Low |
| Officer notebook | pin routes, hypotheses, reminders, and later comparisons | private/local notes | encrypted projection; no canon authority | Low |
| Ship instrument panel | see contribution-driven states in-world | no new authority | exact aggregate projection | Medium art |
| Rotating station | activate a content pack for one place without deleting old history | content epoch transition | signed pack, rollback ratchet | Medium |
| Community threshold event | choose where bounded contributions go among authored goals | conditional activation | Lean world transition and exact dedupe | Medium/high |

The ration and crate are intentionally not economic engines. Ordinary rituals make the ship feel
inhabited; their scarcity and rewards should remain low enough that missing a day is uninteresting.

### 7.4 Archive, knowledge, and canon

| Mechanic | Player verb | Authority output | Technical exercise | Author load |
|---|---|---|---|---|
| Field Archive | inspect origins, hints, relations, and status | projection over receipts/canon | exact provenance graph | Medium |
| Theory Board | attach a claim to exact evidence | signed commentary/evidence edge | identity, revisions, moderation | High |
| Contradiction map | exhibit incompatible claims without selecting a winner | evidence graph view | deterministic graph queries | Medium |
| Lab assay | spend/loan an eligible sample to run a bounded test | new beta observation | custody + declared judge | Medium/high |
| Cartography commons | submit and reconcile deck observations | map candidate and disputes | signed observations, conflict protocol | High |
| First-discovery record | establish earliest finalized discovery, not earliest HTTP arrival | archive annotation | consensus ordering and replay | Low |
| Provenance trail | follow an object through run, crown, custody, loan, and settlement | no new authority | full-width identity across systems | Low UI/high integration |
| Curator promotion | select one exact beta artifact for alpha status | canon revision | Lean capability and signed counter | Very high editorial |
| Supersession | correct or reinterpret an exact record without erasure | new canon revision | revision chain and projection migration | High editorial |
| Episode concordance | link episode time/range to official archive evidence | signed concordance | extension routing/content authenticity | Medium |

### 7.5 Crews, reputation, and Choir

| Mechanic | Player verb | Authority output | Technical exercise | Author/moderation load |
|---|---|---|---|---|
| Crew roster | accept a role-scoped invitation | role capability | attenuation and expiry | Low |
| Asynchronous expedition | take one seat's turn and hand the run onward | joined run receipt | separately signed deterministic fold | Medium |
| Sensor Fusion | submit partial observations for a declared merge | fused report | MPC or public signed fold | Low/medium |
| Secret Council | privately score four predeclared actions and reveal only the aggregate winner | selected beta mission action | existing 4x4 Lean private-preference relation; Tier-1 initially | Low |
| Away-team muster | privately express role suitability/constraints and receive the optimal four-seat assignment | canonical role roster | existing Lean private-raid relation; authenticated roster binding required | Low/medium |
| Containment lock | prove codes agree or a team threshold is met without exposing each input | pass/refuse bit | PartyMPC equality/less-than; semi-honest grade initially | Low |
| Hull Choir | coordinate timed/ordered maintenance roles | cohesion and crew run | multiparty state machine | Low |
| Expedition League | submit matching judged runs to rotating predicates | recomputable standings | replay and dispute window | Low |
| Prediction League | commit then reveal a prediction about a declared event | non-transferable accuracy record | commit-reveal, epoch finality | Medium |
| Evidence jury | review a disputed report under sortition | review receipt | eligibility proof, sortition, sealed ballot | Medium/high |
| Delegated expedition voice | lend proposal voice for one scope and expiry | proposal ballot capability | attenuation and revocation | Medium |
| Choir chambers | compare public, crew, holder, or random-jury tallies | separate tally receipts | proposal-specific Lean regimes | Low |
| Conviction experiment | allocate bounded voice over time without purchase of story power | tally receipt | finalized time, cap, adversarial simulation | Low |
| Crew archive shelf | collectively curate copies/references, not seize custody | display manifest | capability limits and provenance | Medium |
| Mentorship contract | help a new officer and earn an acknowledgment if both complete | social record | consent, bounded one-shot link | Low/moderation |

`$DREGG` holding can prove membership in one declared chamber or eligibility for service discounts.
It does not become combat power or a multiplier on every vote. Market-reactive mechanics such as a
“martyr vote” are simulations or one-off events until adversarial analysis shows that a participant
cannot profitably cause the trigger.

### 7.6 Dark Bazaar and custody

| Mechanic | Player verb | Permitted reveal | DrEX exercise | Author load |
|---|---|---|---|---|
| Fixed-price stall | offer an eligible object under public terms | object and price | ordinary atomic escrow/custody | Low |
| Sealed salvage auction | submit a private bid and receive winner/price result | declared clearing result | private book, HidingFRI, same opening, settlement | Low |
| Batch barter | privately state wants and clear compatible cycles | matched transfers only | solver proposal, proof, atomic multi-asset custody | Low |
| Loan desk | grant use/custody until an epoch or use budget | loan terms | attenuated capability, expiry, recovery | Medium |
| Research escrow | commit an object to a study that may consume or return it | declared study result | exactly-once custody consequence | Medium |
| Blind allocation | crew submits private preferences for finite salvage | allocation only | FHE aggregation and output-boundary MPC | Medium |
| Netting vault | settle several crew obligations while revealing only nets | per-party net | additive threshold FHE, conservation | Low |
| Confidential matchmaking | reveal a compatible expedition roster, not all blocks/ratings | selected roster | private predicates and MPC selection | Low |
| Hidden-route rendezvous | reveal whether routes intersect under a safety rule | rendezvous/no-rendezvous | MPC predicate with authenticated inputs | Medium |
| Private prediction pool | aggregate declared non-monetary forecasts without exposing each one | aggregate distribution | FHE aggregation; no wagering needed | Medium |
| Shielded salvage note | transfer an eligible object without public value/attribute disclosure | exact public statement | committee-free shielded DrEX path if FRI floor closes | High technical |
| Dark-AMM expedition resource | later experimental exchange of bounded event resources | pinned aggregate result | full v4/FXC4 only; never an early economy default | High |

The current PoA Dark Bazaar exercise already binds signed expedition envelopes, a private BFV
book, HidingFRI, same-opening evidence, threshold shares, and an MPC output. It correctly stops
before minting because it lacks a real judged-transition verifier. The next milestone is not more
sample orders. It is one authentic journey from finalized game transition to salvage custody and
private settlement.

Three private game relations can be exercised before value exists: four-person private preference,
four-seat optimal private raid assignment, and an eight-seat commit/reveal fair shuffle with
recorded rejection sampling and selective opening. They are real Lean-authored HidingFRI relations,
but their current honest grade is Tier-1: one producer sees the complete secret input. The raid
proof also needs its session derived from the canonical authenticated roster rather than a host
assertion. These make excellent zero-value protocol games precisely because the UI can show what
each proof hides, what it reveals, and who still sees the witness.

### 7.7 Later Aspect mechanics

| Mechanic | Actual relationship | Required semantic work |
|---|---|---|
| Communication notebook | infer a particular Aspect's bounded signs over repeated encounters | authored finite behavior, private/local hypotheses, exact landed observations |
| Equipment body | select a specialized body/tool that changes available verbs, not raw universal power | capability-constrained loadout and custody policy |
| Joint approach | combine officer action with an Aspect's deterministic response | nonlinear/custom transition verifier when needed |
| Trust and refusal | an Aspect may withhold or reinterpret a command according to consistent finite state | persistent authored state; no chatbot authority |
| Cross-game memory | an exact earlier interaction changes a later available approach | portable identity and receipt witness |
| Recovery mission | locate or recover one precious Aspect under story-specific stakes | bespoke canon and custody rules, narrative activation |

## 8. What PoA should exercise in Dregg and DrEX

The platform should climb a technical ladder through complete player journeys. Each rung remains
useful after the next exists.

| Rung | Player-visible journey | Dregg/DrEX property exercised | Honest exit gate |
|---:|---|---|---|
| 1 | play three finite station games locally | Lean-emitted finite semantics | browser has no scoring twin; exact artifact pins |
| 2 | submit one run and receive a finalized field record | live Lean judge, counter, receipt, world transition | node-derived finalized carrier; replay and tamper refusal |
| 3 | acquire one Archive beta artifact | closed judged-run registry and canon admission | no issuer/client construction path; exact origin preserved |
| 4 | complete a small Descent and extract | native transition, capabilities, seeded graph, durable replay | multi-resource strategic forks; generator properties; restart |
| 5 | complete a crew expedition | party roles, attenuated caps, cross-cell/multi-signature transition | signer uniqueness/order, abort/restart, deterministic combined result |
| 6 | crown one eligible discovery | one-shot custody admission from the same run object | domain/epoch/relic/transcript/replay attacks refuse |
| 7 | settle a sealed auction | private book proof, same opening, conservation, custody consequence | exact declared privacy grade; crash/replay; no producer-only seam |
| 8 | run a real separated threshold ceremony | threshold FHE and MPC output boundary across processes | no process holds all shares; authenticated roster/session; n-1 refusal |
| 9 | run independently operated private clearing | distributed custody and maliciously robust protocol perimeter | DKG, complaints/QUAL, authenticated transport, computation integrity |
| 10 | reproduce it from a follower node | federation finality and portable state | fresh operator kit converges and verifies exact history |
| 11 | promote one exact discovery | canon capability and editorial revision | only the selected artifact changes; history remains replayable |

### 8.1 FHE/MPC fork, made useful by the game

The repository contains three materially different privacy directions:

- threshold decryption around hidden orders;
- FHE aggregation with an MPC output boundary that reveals only a declared result;
- shielded commitments that decrypt nothing, contingent on closing the proof-system soundness
  floor and wiring the full settlement relation.

PoA should not choose one by slogan. It can exercise them with low-stakes mechanics whose expected
outputs are simple:

- Netting Vault tests additive threshold FHE and conservation;
- blind salvage allocation tests FHE aggregation plus output-boundary selection;
- sealed auctions test same-opening, clearing, and custody consequence;
- shielded salvage tests the committee-free path only when the full proof and note mutation are
  live.

For the threshold paths, the biggest missing organ is operational: independently hosted custody,
authenticated transport, malicious DKG/complaint handling, real preprocessing, and computation
integrity. Several parties in one process are a valuable cryptographic test harness, not an
independent committee.

The source is ahead of some older summaries: separate-process threshold custody, hybrid
Ed25519/ML-DSA authentication, X25519/ML-KEM envelopes, distributed exact BFV input certificates,
and authenticated PartyMPC transport are materially implemented. They still do not establish a
house-blind Bazaar. One HidingFRI/root source process can see the complete private book; distributed
input proofs prevent substitution but do not remove that viewer. Share-proof/replay persistence,
malicious key-generation range proofs, availability, and malicious computation integrity also
remain explicit work.

The preprocessing boundary must stay honest. Authenticated trusted preprocessing is a useful rung,
but the current dealerless path correctly stops at `AwaitingCrossTermProvider` until a
malicious-secure PQ OT/VOLE or threshold-BFV cross-term provider exists. A consequential PoA path
must not quietly fall back to `trusted_dealer_triples` and call itself house-blind.

## 9. Content system and authoring economy

Platform depth fails if every mechanic demands a new episode's worth of writing. The unit of work
should be a reusable, validated content pack.

### 9.1 One authored truth, many surfaces

```text
one anomaly pack
  -> a compartment and hotspots on the deck map
  -> a route/encounter family in Descent
  -> an Inspection sweep and a Signal trace
  -> Black Box fragments and an assay
  -> Archive silhouettes, hints, and relations
  -> an Officer briefing and episode debrief
  -> one eligible salvage policy
  -> several player theories
  -> an optional exact alpha-promotion candidate
```

This is the main content multiplier. It creates connections, not merely quantity.

### 9.2 Pack layers

| Layer | Examples | Validator responsibility |
|---|---|---|
| Mechanical | board, graph, room coefficients, action budget, reward limits | totality, bounds, solvability/declared failure, exact IDs |
| Fiction | prose, art, audio, names, official interpretation | references resolve; disclosure policy explicit |
| Reveal | activation, sealed payload, hint stages, episode concordance | precommitment, counter, epoch, no early semantic default |
| Economy | discovery/custody eligibility, loan/trade/research/consume policy | allowlist, conservation, one-shot crown |
| Canon | beta identity, promotion target, supersession link | exact curator capability and revision |
| Accessibility | cues, alt text, captions, presentation and semantic assists | redundant essential cues; assist effects committed |

The curator workbench previews the exact signed bytes, all state/contribution/custody/canon deltas,
the fields revealed at activation, and the browser rendering. The previewed digest must equal the
activated digest.

### 9.3 Content burden tiers

- **Low:** abstract board parameters, trace, table, short briefing, reward budget.
- **Medium:** a small scene, several fragments, sweep assets, item descriptions, question pack.
- **High:** a coherent anomaly spanning rooms, rules, art/audio, and future implications.
- **Very high:** an Aspect, major alpha revelation, or cross-product continuity.

Low and medium packs create regular platform depth. High packs create seasons. Very-high packs are
narrative events, not an expected live-ops cadence.

## 10. Braided implementation program

This is not a waterfall and not a date promise. Several braids advance in parallel, but each has a
named join point. One integration lane owns the hot registries, umbrella imports, artifact manifest,
and release gate; semantic workers add isolated Lean modules, fixtures, emitters, adapters, and
tests without racing those files.

### Braid A — authority and receipts

**Purpose:** make one played action become one authoritative, finalized, reusable fact.

- Wire persisted node state and a finalized signed turn into the Lean network judge's carrier.
- Enforce the per-player counter and canonical transcript identity at the live caller.
- Construct world/archive effects only through the closed game-specific judged-run type.
- Complete F4 persisted vouch-row consumption without a bypass or pretend bond path.
- Preserve full-width content/run/artifact roots through every consumer.

**Join A:** one browser run settles into world state and a beta Archive record, survives restart,
replays identically on another node, and every signer/seed/counter/content/transcript mutation
refuses.

### Braid B — Lean game kernel and emitter

**Purpose:** make adding a game primarily a Lean/content task.

- Stabilize the common `Config/State/Action/step/replay/judge` family and closed admission contract.
- Activate the existing three finite tables, then Black Box and Inspection.
- Emit deterministic tables/descriptors/codecs and exact source maps for readable explanations.
- Add a content validator/generator framework and custom-VK path for state spaces too large for a
  finite table.
- Remove any Rust constant or mover mirror that can decide settled behavior.

**Join B:** a fresh game module reaches local play, network judgment, Archive, contribution, and the
receipt inspector through one documented path with no semantic fallback.

### Braid C — expedition and Descent

**Purpose:** make exploration the flagship play rather than a generic dungeon skin.

- Specify two or more incomparable expedition resources and prove their bounds/conservation.
- Build signed deck graphs, route knowledge, tools/loadout, provisional finds, extraction, and
  spill/retention rules.
- Start with a concrete state: position/phase; air, power or light; damage/contamination; exact
  carried-object custody; opened hotspots; deployed tools; knowledge flags; and extraction status.
  Candidate actions are traverse, inspect, stabilize, collect, deploy/recover tool, extract, and
  abort.
- Carry forward the strongest old laws: every step inward creates extraction debt; damage reduces
  future carrying capacity; an installed tool has one location; returning safely, not touching an
  object, creates the archiveable find; extracted/banked states are absorbing.
- Use exhaustive solvers as design instruments: measure strict strategic forks, dominated verbs,
  reachable dead states, route diversity, and score/board coherence.
- Author one small anomaly with several encounter modes rather than a long corridor of combat.
- Add durable resume, practice, ranked attempt policy if desired, and proof-derived ghosts.

**Join C:** a five-to-ten-room expedition offers materially different successful strategies, is
fun without rewards in human playtests, and produces one exact extractable discovery.

The current `DeckGraph` supplies bounded packs, hotspots, phases, replay, BFS extraction, and
validation. Its `wrap` and `mirror` modifiers are presently renderer metadata; only `phase` changes
semantics. They remain visual vocabulary until the new transition gives them rules and proof gates.

### Braid D — place, archive, and personal continuity

**Purpose:** turn isolated runs into a world worth revisiting.

- Build the declarative deck map, Officer, Field Archive, personal locker, and provenance viewer.
- Derive saves/projections from receipts with versioned migration, export, and recovery.
- Add finalized daily selection and one non-punitive ordinary ritual.
- Project bounded contributions into diegetic ship instruments and campaign stages.
- Build the theory/evidence graph without allowing commentary to mutate canon.

**Join D:** cache deletion loses no authority; the same discovery appears consistently in its run,
Archive, locker/custody status, ship effects, and optional extension surface.

### Braid E — custody, Bazaar, and DrEX

**Purpose:** make privacy and exact ownership produce interesting game choices.

- Finish the judged-transition verifier required by PoA DrEX ingress.
- Crown one eligible artifact once into the same custody object used by listing/loan/research.
- Wire the proven private producer into a real sealed-ingress queue and settlement worker.
- Preserve same-opening, conservation, roster/session, privacy grade, crash recovery, and exact
  consequence across the complete path.
- Separate process-hosted threshold operation, then independently operated custody; do not collapse
  the labels.
- Add batch barter or Netting Vault only after the first custody journey is real.

**Join E:** finalized expedition -> crown -> sealed order -> proved clear -> custody transfer ->
Archive provenance is one deployment-owned journey and still converges on an independent follower.

### Braid F — crews and Choir

**Purpose:** add social composition without turning the platform into governance UI.

- Define crew roster/role capabilities and separately signed combined actions.
- Ship one asynchronous crew expedition or Sensor Fusion game.
- Recompute leagues and reputation from matching receipts; add dispute/correction windows.
- Implement commit-reveal predictions and one proposal-specific Choir mechanism.
- Red-team Sybil, delegation, holder/public chamber, and market-reactive rule incentives.

**Join F:** a solo activity and a crew activity share exact underlying objects; the crew path cannot
forge a member, replay a seat, widen a role, or turn a tally into canon.

### Braid G — surfaces and episode bridge

**Purpose:** make the platform present where viewers already are without surrendering authority to
host sites.

- Build an accessible shared game/receipt shell for site and extension.
- Authenticate curator routes and content epochs for YouTube/X transclusion.
- Bind episode evidence/debrief content to exact timestamps and content roots.
- Handle SPA navigation, stale responses, closed-shadow mounting, host CSS, reduced motion,
  keyboard, screen reader, and panel removal under adversarial fixtures.
- Clearly distinguish practice, submitted, judged, finalized, private, and refused states.

**Join G:** the same pack renders on the beta site and beside an episode; navigation or delayed
responses cannot leave a stale authenticated panel or success state.

### Braid H — federation and reproducibility

**Purpose:** make independent verification and participation routine.

- Keep PoA genesis, keys, storage, ports, deployment domain, and economy isolated.
- Publish deterministic node/content builds and exact hashes.
- Make a follower start from an empty directory and converge from documented inputs.
- Persist and consume the N=2 rooted-vouch evidence before advertising open admission.
- Add state export, recovery, observability, resource limits, and bounded public endpoints.

**Join H:** a new operator can reproduce genesis, follow history, replay the Crown journey, and fail
closed on wrong binaries, roots, peers, or admission evidence.

### Braid I — Aspect incubation

**Purpose:** prepare technical primitives without pre-spending canon.

- General companion identity, finite behavior, equipment capability, cross-game witness, and local
  communication notebook may be built behind a disabled content type.
- No Aspect instance, personality, art, lore, or market policy activates before Sentyr signs the
  narrative epoch.
- Design copying, custody, loss, and recovery with Starfall's “one Aspect matters” premise.

**Join I:** a narrative activation can introduce one authored Aspect without a client rewrite, and
an inactive build reveals no sealed content or generic substitute pet.

## 11. Constellations of convergence

The braids meet in substantial constellations. A constellation is releaseable only as a whole; it
does not prohibit broad parallel work beyond it.

### Constellation 0 — trustworthy field station

Activate the three finite games, exact local-vs-judged UI, daily/content shell, Officer, Archive
hatch, and extension route. Complete Join A for one run and publish the reproducible federation
artifacts.

**Player result:** several small things to play and one incontrovertible field record.

### Constellation 1 — an inhabited ship

Add the deck map, locker, Archive collections, a mundane daily ritual, episode debrief, ship
instruments, contextual onboarding, and one cross-surface anomaly pack.

**Player result:** a place to return to rather than a catalog of demos.

### Constellation 2 — first real expedition

Ship the rebuilt small Descent, loadout, extraction, provisional finds, one impossible-deck rule,
durable resume, route ghosts, and one crown-eligible artifact. Complete human decision-space tests.

**Player result:** the show is where the ship goes; the game is where they discover what the ship is.

### Constellation 3 — the object has a life

Complete the Crown journey through exact archive provenance, one-shot salvage, custody, loan or
research, sealed auction, private clear, and settlement. Deploy at least process-separated roles
and show the privacy grade in the receipt inspector.

**Player result:** something found on an expedition can be kept, studied, lent, or privately
exchanged without becoming a generic fungible reward.

### Constellation 4 — crews investigate

Add crew roles, one asynchronous or synchronous multi-party expedition, Sensor Fusion/Hull Choir,
theory/evidence, a league, predictions, and one Choir chamber experiment.

**Player result:** other players are collaborators and interpreters, not merely leaderboard rows.

### Constellation 5 — unknown decks as a content engine

Deliver the curator workbench, anomaly/deck grammar, generator proofs, custom-VK game path, several
connected content packs, an independent follower journey, and one exact alpha promotion if Sentyr
wants it.

**Player result:** the world can deepen sustainably and a discovered thing can cross into the show
without surrendering authorship.

### Constellation 6 — independently dark

Move the chosen DrEX hall from in-process ceremony to authenticated, distributed, independently
operated custody with malicious-security gates appropriate to its claim. Exercise a second private
mechanic such as Netting Vault or blind allocation.

**Player result:** privacy no longer depends on the official operator choosing not to look.

### Constellation 7 — Aspects

Only after the narrative event, activate one authored Aspect, communication/bonding, equipment,
cross-game memory, and a bespoke recovery/custody rule. Resist mass procedural generation until
the first relationship is good.

**Player result:** a rare intelligence becomes personally meaningful because the platform already
has expeditions, records, tools, and shared history for it to inhabit.

## 12. Verification and red-team program

PoA needs tests for semantics, integration, privacy, economics, deployment, and fun. These are
different kinds of evidence.

### 12.1 Per-semantic-module gate

Every authoritative Lean module carries, where applicable:

- replay determinism and canonical encoding;
- invariant preservation for every legal action;
- explicit refusal for invalid, late, duplicate, stale, over-budget, and out-of-range actions;
- terminality or a declared nontermination bound;
- contribution, score, inventory, and arithmetic bounds with overflow refusal;
- generator properties such as exact multiplicity, reachability, extraction, and declared relics;
- replay/counter uniqueness and content/domain separation;
- presentation-assist noninterference and semantic-assist commitment;
- named positive and negative theorems with axiom/compiled census.

The release gate compiles the modules and emitted artifacts. It does not infer proof completeness
from a text search, a sample run, or `#guard`.

### 12.2 Artifact and runtime gate

- double emission is byte-identical;
- checked-in roots, descriptors, codecs, tables, and VK epochs match source;
- table/descriptor absence, unknown tag, wrong digest, stale content, or missing Lean FFI refuses;
- a browser interpreter corpus matches Lean output on every finite row and hostile boundary case;
- native/custom-VK games compare executable Lean judgment with the admitted proof statement;
- no Rust or TypeScript fallback can construct the accepted receipt type.

The first coverage repair is concrete. At the time of this roadmap, `scripts/test-poa.sh source`
uses `cargo nextest list` for `poa_dark_bazaar_protocol`: it discovers the binary but never executes
it. That test and `private_book_distributed_bfv_exact` are heavy-profile-only, while private web
operations and the distributed-threshold process test appear in the repository's explicit
never-run inventory. Add a deliberate PoA crypto release profile, run it in release mode on a
leased build lane, and retain its verdict/log/duration artifact. Source existence is not a green
privacy gate.

### 12.3 Game-design gate

Formal validity is not fun. Use exhaustive or property-guided solvers to find:

- zero strategic forks or one dominant move multiset;
- dead or dominated verbs;
- legal states from which the ranked goal is already impossible but play continues misleadingly;
- score displays that reward a run excluded from the board;
- seed families with impossible, trivial, or near-identical instances;
- loadouts or lineage combinations that dominate every context.

Then run human practice-only playtests. The exit condition is observed replay, argument over a
choice, and comprehension of consequences—not proof coverage or a large mechanic count.

### 12.4 Receipt and economy adversary corpus

For every journey, mutate independently:

- deployment, genesis, content root, activation, session, epoch, ruleset, and VK;
- actor, player key, party order, duplicate signer, counter, transcript encoding, and seed;
- pre/post world, contribution, relic allowlist, score, and artifact reference;
- crown eligibility, custody owner/version, offer, roster, clearing statement, and settlement;
- alpha/beta/superseded status, curator key, revision, and counter.

Each mutation must either yield a named refusal or be proved irrelevant. Red-proof mutation testing
runs on a copy or isolated build lane, never by disarming a shared-tree guard.

Economic property tests cover conservation, exactly-once sources/sinks, escrow recovery, loan
expiry/reclaim, wash/self-trade policy, circular barter, griefing through unfinishable offers,
seed-grinding, alt-account multiplication, and cross-season replay. Simulate proposed token/voice
mechanics before deploying them.

### 12.5 Privacy and MPC gate

- The receipt binds the exact privacy grade, roster, session, input commitments, permitted reveal,
  and output statement.
- FHE ciphertext evaluation has bit-exact oracle/differential vectors for the supported envelope.
- Threshold share sets reject missing, duplicate, wrong-session, under-smudged, or forged shares;
  n-1 learns/recovers no accepted output under the claimed scheme.
- Same-opening verification connects the private input representation to the proof and clearing
  representation actually used.
- Crash/restart cannot replay a reveal, reuse preprocessing, or apply a consequence twice.
- Process-separated and independent-operator deployments have different operational tests.
- Malicious-security claims require authenticated broadcast/transport, DKG complaints/QUAL,
  chosen-input defenses, real preprocessing, and computation integrity—not only semi-honest unit
  tests.
- A fair-shuffle or joint-entropy game persists every commitment and rejected attempt before the
  next attempt; restart cannot erase an unfavourable rejection, and missing-last-revealer/abort has
  a declared outcome.
- Private preference and raid sessions derive from the authenticated canonical participant roster;
  the proof cannot be stapled to host-invented seat identities.
- Distributed input/BFV certificates receive an explicit source-viewer test. They cannot promote a
  grade until no process reconstructs the complete book and the distributed clearing/root proof is
  the one actually consumed.

### 12.6 Surface gate

- keyboard-only and screen-reader paths complete every turn-based activity;
- essential state has redundant non-colour cues and reduced-motion behavior;
- semantic assists are visible before play and preserved in the receipt;
- site and extension render the same signed pack and proof labels;
- route spoof, content swap, host CSS, closed shadow DOM, SPA navigation, delayed response, stale
  counter, and mounted-panel removal have hostile tests;
- no stale success UI survives a refused or superseded request.

### 12.7 Deployment and follower gate

- beta auth, TLS, signed release, content root, binary hash, node genesis, data directory, ports,
  advertised addresses, peers, and Lean/full-turn requirements are checked at startup;
- the deployed bytes equal the tested bytes;
- secrets are absent from artifacts and logs;
- restart, rollback attempt, corrupted projection, stale epoch, validator loss, and bounded load have
  captured outcomes;
- a fresh follower reproduces content and state roots and replays at least the field-record and
  Crown journeys.

## 13. Public-source and non-secrecy law

Path of Angels remains a public-source system, including its game rules, content schemas,
generators, Lean semantics, circuit/AIR emitters, verifier artifacts, receipt codecs, federation
rules, and verification tools. Public source is part of the trust claim, not a later documentation
task.

Spoilers use cryptography and release discipline:

- publish a commitment or encrypted signed pack before activation;
- bind the decryption/reveal to a finalized epoch or threshold ceremony;
- retain the sealed bytes and reveal evidence for later audit;
- keep old activated roots and rules reproducible.

Repository obscurity is never accepted as:

- a fairness mechanism for daily seeds, puzzle targets, loot, jury selection, or market clearing;
- a security boundary for keys, admin authority, validator admission, custody, or canon;
- a privacy mechanism for bids, routes, inventories, votes, or identity;
- an excuse for a browser or server to carry unverified semantic code.

Competitive puzzle targets may remain sealed during their window, but the accepted solution space,
judge, commitment scheme, and post-window reveal are public. Server and participant keys are normal
deployment secrets; their existence does not make the rules secret.

## 14. Decisions for co-creation with Sentyr

The implementation can advance broadly while these product choices remain open, but each should be
made before its constellation joins:

1. What is the Expedition Officer: a named authored crew member, a player-created role, or an
   intentionally thin point of view?
2. What kinds of beta composition are allowed: only prewritten artifacts, authored atoms combined
   by verified rules, or bounded generated descriptions as commentary?
3. What are the first expedition's two or three incomparable resources, and what makes extraction
   emotionally legible in PoA rather than generically roguelike?
4. Which one anomaly can sustain the first cross-surface content pack without revealing future
   alpha canon?
5. Which discoveries remain records, which may be crowned into custody, and which are explicitly
   untradeable?
6. Which first private mechanic is most interesting as a game: sealed salvage auction, blind crew
   allocation, Netting Vault, or private route rendezvous?
7. What role may `$DREGG` play at launch: service payment, one separate Choir chamber, access to an
   experimental mechanism, or none yet?
8. How public should crew identity and field reports be, and what moderation/recovery boundary is
   acceptable for a small beta?
9. What exact story event unlocks Aspects, and what facts about them must remain sealed until then?

## 15. The success condition

PoA has platform depth when a player can naturally move among distinct pleasures—watch an episode,
inspect a signal, play a compact game, plan a route, extract from an unknown deck, study a field
record, arrange a locker, help a crew, form a theory, contribute to the ship, lend or privately
exchange one eligible object, and independently verify what happened—and when those pleasures share
exact objects without collapsing into one currency or one governance system.

The proof is not the number of crates connected, minigames listed, characters generated, or token
holders voting. The proof is that each activity is good at its own scale, each handoff preserves
identity and authority, one authored truth can deepen several surfaces, and Sentyr can still decide
exactly what becomes part of the show.
