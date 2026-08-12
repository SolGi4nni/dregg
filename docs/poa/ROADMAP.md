# Path of Angels: development map

Status: live epoch 1, curator **counter 12**, plus working design, header refreshed 2026-08-12. This is a
menu and dependency map for co-creation with Sentyr, not a promise that every row becomes canon or ships
in order. The counter is read from `poa/artifacts/poag1/manifest.sig.json` and pinned by
`POA_EXPECTED_CURATOR_COUNTER` in `poa-web/src/trust-config.js`; this line said 4 until 2026-08-09 and
10 until 2026-08-12, which is why the envelope—not this sentence—remains the authority.

## What epoch 1 actually establishes

This document began before the first release. The deployed beta now closes enough of the spine to
distinguish implemented substrate from the option space below:

- `beta.pathofangels.network` serves an authenticated, signed-content station with six connected
  organs: Field Drills, Expedition, Archive, Recorder, Crew, and Bazaar. **Seven** games are playable
  finite games — Signal Triangulation, Relay Repair, Salvage Lock, Black Box Reconstruction, Deck
  Descent, Artificer Logic and Vent Crawl; each consumes an exact Lean-emitted
  table and the browser does not score it. Counter 12 closes the three descriptor/kernel drifts that
  counter 10 still carried: Salvage now emits 18 actions, Black Box 11 actions with three answer
  classes, and Descent one shoring timber. The Expedition and Archive demonstrators also regenerate
  their complete Lean artifacts during the release gate. Curator counter 12 is live behind Basic
  Auth, with separate evidence grades so a healthy local instrument cannot launder an unavailable
  network authority path.
- The PoA chain is distinct from public Dregg: one workhorse validator in explicit `solo` mode,
  threshold one, separate keys/storage/ports/deployment domain, no demo economy, required Lean
  authority and full-turn proving. Federation id remains
  `70b7fa4c…d07c1b`; the epoch-3 successor deployment is `de8a785f…95866`.
  This is a twice-monthly development chain, not a fault-tolerant federation: hbox is build capacity
  and persvati is not a validator.
- Lean owns the emitted game state machines and their judged/canon boundaries. It also owns Black
  Box Reconstruction, Containment Inspection, deck validation, daily mission selection,
  accessibility commitments, the Field Archive, owner-wide Attendant continuity, authenticated
  crew field missions, an operator-visible Poseidon-bound preference exercise, deployment-rooted
  Galley Commons/Daily life, and an exact opening-aware Bazaar core. Those additional systems are
  not activated browser content merely because their semantics exist. Galley still needs concrete
  host codecs and atomic stores; Bazaar still needs its seven fixed native verifier/effect adapters
  and durable restart decoder.
- The curator, content-epoch rollback ratchet, extension route authentication, content-addressed web
  staging, and atomic content-only cutover are exercised rather than diagrammed. The active solo
  release receipt binds counter 12, committed browser source, epoch-3 genesis/runtime/config bytes,
  the height-1 Signal head and finalized receipt, while preserving the prior pointer and metadata as
  content-addressed rollback copies.
- DrEX ingress signs distinct exact Lean-judge input and output digests and still refuses to crown a
  claim because the finalized-state adapter is not wired. The curator likewise exports only a
  semantic Signal review. A bearer-only node-envelope diagnostic now reconstructs exact canonical
  `SignedTurn`, executor receipt, Lean replay, and durable commit projection from one node, but it
  explicitly leaves external deployment pinning, actor PQ enrollment, authenticated mission/config
  binding, and quorum hybrid finality false. Promotion therefore still hard-refuses. The preference
  exercise is explicitly not described as DrEX, FHE, MPC, or proof-backed: its Poseidon semantics are
  real, but its production portal and private/proved outer statement are not.
- The browser now supports Wallet Standard and an explicit classic-provider seam for Solana
  proof-of-holding admission against the exact `$DREGG` mint. Challenges and capabilities are
  wallet-bound, short-lived, and fail closed. Holder mechanics remain a separate, unexercised path;
  the fact that the current validator serves judged Signal does not turn that preview into live
  holder admission.
- Rooted transitive N=2 admission is proved and differentially tested, but the live node remains the
  fixed genesis committee until authenticated vouch rows are persisted and consumed.

Epoch 1 is therefore a trustworthy field terminal and solo development chain, not yet the whole
“sealed beta station” constellation. One judged Signal claim now reaches a finalized receipt,
durable world/archive state and byte-identical restart replay. The immediate expansion is to put the
real Cipherclerk provider—not an integration-only ephemeral signer—through that whole browser path,
then carry the same discipline into Descent, holder admission and an actually private Bazaar
clearing path without weakening the existing refusals.

## The opportunity

Path of Angels can have Neopets-like **platform depth**, not Neopets-like audience assumptions.
The useful comparison is a world with many small things worth doing: games, expeditions, archives,
shops, crews, rituals, curiosities, and recurring places. The games should be enjoyable before
their rewards matter. The surrounding economy and fiction give players reasons to return and
reasons to care.

The two scales divide cleanly:

- The YouTube series and its polls decide the macro story: where the Khovokhi jumps and what its
  inhabitants choose.
- The game explores the micro story: the thousand mostly uninhabited decks of a God-Engine that
  was not designed for humanoids and was never fully explained to its passengers.

Game discoveries begin as beta canon. Sentyr may promote selected discoveries into the series'
alpha canon. Promotion is editorial, explicit, signed, and much rarer than discovery. The best
reward is sometimes that an expedition, object, officer, or rumor becomes real in the show.

## Laws of the platform

1. Sentyr remains the author. A game may reveal only predeclared beta material; play alone cannot
   manufacture alpha canon.
2. The mechanic is the product. Currency, $DREGG, proofs, and rewards deepen a good game; they do
   not rescue a bad one.
3. Lean owns game truth. Legal states, transitions, scoring, contributions, replay, canon movement,
   and artifact emission live in Lean wherever practical. Browser and Rust code interpret emitted
   artifacts and carry verified decisions; they do not quietly rewrite the rules.
4. Content is data. Decks, encounters, relics, dialogue, tables, and maps are signed, versioned
   content bundles so new material does not require a new client.
5. A receipt says exactly what it proves. Client-side replay is a field record, not a verified
   network receipt. Privacy is named by the construction actually deployed, never by aspiration.
6. Seeds and randomness are committed before play. A player, signer, or client cannot grind a
   favorable target after seeing the result.
7. Contributions are bounded and exact. A mission can affect only predeclared resources and relics;
   overflow refuses rather than saturating or wrapping.
8. Scarcity serves fiction. Avoid compulsory streaks, engagement punishment, pay-to-win governance,
   and an economy that makes new players feel permanently late.
9. Accessibility is part of the ruleset. Declared assists may change timing or presentation without
   silently changing receipt validity or rewards.
10. Mechanics need not be secret. Signed content can keep a reveal sealed until activation, but
    security and fun cannot depend on nobody reading the source.

## The platform spine

Every activity consumes a signed mission specification and produces the same narrow result:

```text
signed content epoch + precommitted seed + player actions
        -> Lean-defined replay/judge
        -> judged run receipt
        -> bounded Contribution
        -> world state / archive / DrEX ingress
        -> optional curator promotion of beta material
```

The shared contribution vocabulary is intentionally small: intel, supplies, cohesion, influence,
declared relic identifiers, and score. A game does not invent a branch in the series. It moves
world state and returns discoveries the curator had already made possible.

## Release constellations

These are dependency-shaped constellations, not calendar quarters. Work can proceed across several
at once while each public boundary remains fail-closed.

### A. Sealed beta station

The first beta should demonstrate the trust spine and a small place worth visiting.

- Password-protected `beta.pathofangels.network`, with no indexable spoilers.
- A distinct PoA Dregg federation and deployment domain, three initial validators, no generic demo
  faucet/economy, and a reproducible operator/join kit.
- Curator-signed Lean-emitted content epochs with rollback protection.
- Expedition Officer, daily board, deck map, field archive, Bazaar hatch, and Choir hatch.
- Seven complete finite games: Signal Triangulation, Relay Repair, Salvage Lock, Black Box
  Reconstruction, Deck Descent, Artificer Logic, and Vent Crawl.
- Opt-in YouTube extension companion, activated only by a curator-signed routing statement.
- Local replay first; network submission is enabled only when the runtime verifier consumes the
  same emitted transition artifact and returns a judged receipt.

Exit condition: changing a browser rule, content file, signer, seed, counter, or artifact causes a
specific red test. The deployed beta must contain the exact bundle those tests approved.

### B. Daily life aboard the Khovokhi

Make the station feel inhabited before building a giant economy.

- A finalized-epoch daily mission shared by everyone, never selected from browser time.
- Field Archive entries with origin receipt, beta/alpha/superseded state, silhouettes, hints, and
  first-discovery history.
- Ship meters driven by bounded aggregate contributions, shown through diegetic instruments rather
  than administrative labels.
- Personal locker and gallery for recovered objects, reports, and expedition patches.
- Contextual, skippable Officer briefings and one-hint-at-a-time tutorials.
- Accessibility profiles whose game effects are explicit in the mission specification.
- Episode debriefs and observation drills using author-supplied questions and evidence.

### C. The Descent

The existing dungeon/descent engine becomes the flagship expedition game rather than a generic
dungeon pasted beside the series.

- Short seeded runs through alien deck graphs with extraction as a meaningful choice.
- Expedition loadouts, tools, damage, hazards, and incomplete information.
- Non-Euclidean modifiers: wrapped rooms, mirrored topology, loops, phase changes, rooms that share
  a door but not a coordinate system.
- SCP-shaped encounters whose declared mechanics can be replayed without prematurely revealing
  their narrative interpretation.
- Crew expeditions with separately signed actions and a deterministic combined transition.
- Field reports become beta canon; exceptional reports can be curated into later episodes.
- Proof-carrying generator properties: reachable extraction, bounded resources, declared relics,
  deterministic seed, and no impossible initial state.

### D. Dark Bazaar and DrEX

DrEX should do something that would be less interesting or less trustworthy as an ordinary web
database. The Bazaar is the natural exercise surface.

- Crown only a runtime-judged expedition receipt into an offerable salvage claim.
- Full 32-byte provenance from content epoch through run, discovery, offer, clearing, and custody.
- Sealed-bid salvage auctions with the existing private-clearing/DrEX machinery.
- Process-separated threshold decryption first; stronger MPC/FHE modes only when they are actually
  deployed and tested.
- Batch barter and wants-lists: clear compatible exchanges without publishing every reserve or
  preference.
- Dark Bazaar expeditions where private choices are revealed only at settlement or remain hidden
  when the protocol genuinely supports it.
- Curator-defined sinks: research, repair, exhibition, loan, or sacrifice. Avoid a universal item
  treadmill whose only purpose is price appreciation.
- A public audit trail proves conservation and valid clearing while keeping the promised fields
  private.

### E. Choir, crews, and $DREGG

Voting is one activity in the world, not the entire world.

- Episode polls remain broadly accessible; holding $DREGG may unlock additional game mechanisms or
  bounded voice, but should not make spectators narratively irrelevant.
- One-wallet-one-voice, capped/square-root voice, conviction, delegated voice, random juries, and
  holder/non-holder chambers are selectable proposal mechanisms rather than a single constitution.
- Prediction leagues use reputation or in-world standing by default, not financial wagering.
- Crews maintain shared archives, expedition rosters, specialties, and weekly challenges.
- Contribution proofs support leaderboards that can be recomputed, disputed, and corrected.
- A “martyr” or market-reactive rule is an event mechanic only after adversarial simulation; it
  must not reward a holder for causing the condition that grants more power.

### F. Aspects

Aspects are not generic procedural pets painted in PoA colors. They arrive when the fiction earns
them. Their platform debut should coincide with their narrative debut.

- Individual Artificer-crafted intelligences with constrained communication and specialized
  equipment bodies.
- Bonding, interpretation, equipment, teaching, and joint expedition mechanics.
- Personality is partly authored and partly expressed through consistent finite behavior, not an
  unbounded chatbot pretending to be canon.
- An Aspect may influence several games without becoming a universal stat bonus.
- Custody, loss, copying, and persistence receive story-specific rules because Starfall establishes
  that even one Aspect matters enormously.

### G. An open game federation

- Anyone can reproduce genesis, verify signed content, replay a run, and spool a node without
  receiving secret application logic.
- Admission uses the Lean-owned positive-N rooted transitive vouch closure. PoA starts with N=2,
  no pretend bond path, and no environment switch that bypasses the verified gate.
- Node/operator manifests bind deployment domain, genesis, binary digest, data directory, ports,
  advertised addresses, peers, and serving keys.
- Semi-trusted signup and recovery may exist at the application edge without being confused with
  consensus admission.
- Federation evolution follows explicit, versioned statements and portable state exports.

## Mechanics menu for Sentyr

Cost is relative after the platform spine exists. “Canon load” estimates how much new authored
truth a mechanic asks Sentyr to commit.

| Mechanic | Player verb | Dregg / Lean opportunity | Cost | Canon load |
|---|---|---|---:|---:|
| Signal Triangulation | deduce a hidden transmission | emitted finite feedback table; judged transcript | S | Low |
| Relay Repair | route power through a damaged grid | BFS reachability, inventory and power invariants | S | Low |
| Salvage Lock | pair alien glyphs under pressure | seeded board multiplicity and action budget | S | Low |
| Black Box Reconstruction | order telemetry fragments | permutation proof and enumerated accepted sequences | S | Medium |
| Containment Inspection | mark differences between sweeps | declared hit regions and false-positive bounds | S/M | Medium |
| Episode Debrief | answer evidence questions | signed question set; replayable scoring | S | Medium |
| Drift Probe | tune, hold, and recover a contact | finite state machine; committed noise table | M | Low |
| Damage Control | schedule repair pipelines | resource conservation and bounded concurrent timers | M | Low |
| Pressure Garden | tend a reclamation culture | finalized ticks; mutation table; no client-clock trust | M | Medium |
| Impossible Deck | navigate changing topology | graph invariants and deterministic phase transitions | M | Medium |
| Quarantine Desk | classify arrivals and cargo | private attributes; selective disclosure credentials | M | Medium |
| Sensor Fusion | combine partial crew observations | multi-party signed input and deterministic merge | M | Low |
| Hull Choir | coordinate timed maintenance actions | threshold/cohesion contribution without popularity vote | M | Low |
| Crown Wreck Survey | allocate a finite expedition team | private choice, shared budget, aggregate result | M | Medium |
| Archive Restoration | assemble damaged schematics | content-addressed fragments; proof of exact assembly | M | Medium |
| Tool Calibration | tune equipment against noisy traces | reproducible numeric bounds and challenge cases | M | Low |
| Language Workbench | infer meanings from paired signals | finite grammar/content packs; beta lexicon discoveries | M | High |
| Deck Cartography | collectively map connected rooms | signed observations and conflict/dispute handling | M | High |
| Field Archive | collect and contextualize discoveries | monotonic acquisition from judged receipts | M | Medium |
| Personal Locker | arrange/show recovered objects | provenance-preserving custody and galleries | S/M | Low |
| Free Galley Ration | one finalized-epoch daily claim | anti-replay counter; deliberately low stakes | S | Low |
| Salvage Crate | open a committed daily table | epoch randomness and verifiable draw | S | Low |
| Sleeping Deck Entity | choose when to risk retrieval | committed wake state; bounded loss; event timing | M | High |
| Crew Expeditions | plan and execute joint missions | multi-signature turns and deterministic combination | L | Medium |
| Expedition League | compare verified runs | recomputable scores and dispute windows | M | Low |
| Theory Board | attach claims to evidence | signed statements, provenance graph, curator status | M | High |
| Prediction League | predict votes/reveals/actions | commit-reveal and reputation accounting | M | Medium |
| Sealed Salvage Auction | bid without public reserves | DrEX private clearing and conservation audit | L | Low |
| Batch Barter | express private wants and clear cycles | MPC/solver proofs and atomic custody changes | L | Low |
| Relic Loans | lend instead of permanently trade | capabilities, expiry, custody and recovery | M/L | Medium |
| Research Commons | contribute objects to unlock study | threshold statement and bounded communal unlock | M | High |
| Random Expedition Jury | review disputed field reports | sortition, eligibility proof, commit-reveal | L | Medium |
| Choir Chambers | compare holder and public preference | multiple electorate proofs without collapsing them | M/L | Low |
| Aspect Bonding | learn to communicate with one Aspect | authored finite behavior and portable identity | L | Very high |
| Aspect Equipment | match bodies/tools to missions | capability constraints, custody and loadout proofs | L | High |
| Alpha Promotion | elevate a beta discovery into the show | exact curator capability, revision, epoch, counter | M | Very high |

`S` is a focused finite game or surface, `M` composes several platform services, and `L` requires a
new durable subsystem or serious content production. Art and writing can dominate engineering cost.

## What the current braid must prove

Before the first beta is called protocol-backed:

- The exact Lean files compile without `sorry`/`admit`, and their named security theorems have an
  explicit axiom census.
- Only a game-specific judge can construct the receipt accepted by canon/world state.
- Per-player counters are monotonic and replay identity does not depend on attacker-chosen transcript
  bytes.
- The mission's seed, federation, content session, epoch, artifact hashes, and allowed relics are
  committed before play.
- The emitted POAG1 bundle is deterministic, complete, content-addressed with SHA-256, and signed by
  a pinned curator key with rollback protection.
- The browser consumes the emitted transition table. No second JavaScript scoring implementation is
  shipped.
- DrEX ingress fails closed until it verifies a real judged run; it never mints from an issuer's
  unverified claim.
- The PoA node has a distinct deployment-domain genesis, no demo faucet/economy, N=2 admission,
  `DREGG_REQUIRE_LEAN=1`, isolated storage/keys/ports, and an operator manifest that is checked again
  at launch.
- The public bundle, authenticated beta deployment, node artifact, and documented hashes are the
  exact tested bytes.

The discoverable gate is `scripts/test-poa.sh source`. After genesis, emission, and the curator
ceremony, `scripts/test-poa.sh release` adds exact Lean reproduction, signature/rollback pins,
artifact staging, and the full browser hostile suite. A focused green that is absent from this gate
is not durable coverage.

## Near-term build order

1. **Closed in Lean:** judged runs, counters, Canon admission, world chaining, seeds, signed content,
   archive acquisition, declared assists, and transcript-independent replay identity.
2. **Frozen successor:** deterministic POAG1 epoch 1/counter 2 contains all three finite games and
   reproduces exactly under its curator signature.
3. **Promotion pending:** the browser consumes only authenticated emitted tables and distinguishes
   local transcripts from judged receipts; the counter-2 web successor still needs the v3
   content-only ceremony.
4. **Runtime deployed, admission residual explicit:** the isolated three-node federation has no
   demo economy and requires Lean/full-turn proving. N=2 admission is proved but not live because
   finalized typed vouch rows are not yet persisted and consumed by the node.
5. **Evaluator complete, authority adapter open:** Lean can judge and atomically compute the exact
   world/Canon/counter successor through native FFI. The node must still load persisted state and
   derive `FinalizedCarrier` from a finalized signed turn before that result is authoritative.
6. **Bazaar semantics complete, private verifier open:** the bounded Dark Bazaar core proves escrow,
   conservation, policy, and replay properties; DrEX v2 binds judge input/output digests and refuses
   minting until the real adapter and private authorization verifier exist.
7. **Deploy and inspect:** promote the signed three-game web successor without restarting validators,
   then exercise all three games through Basic Auth and the extension and record exact hashes.
8. **Broaden life aboard ship:** activate archive/deck systems and additional finite games; begin the
   Descent once the finalized receipt/content spine is boringly reliable.
