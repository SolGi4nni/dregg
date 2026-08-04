# Path of Angels: development map

Status: working design, 2026-08-03. This is a menu and dependency map for co-creation with
Sentyr, not a promise that every row becomes canon or ships in order.

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
- Three complete finite games: Signal Triangulation, Relay Repair, and Salvage Lock.
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

1. Close the judged-receipt, counter, canon-admission, seed, and signed-content contracts in Lean.
2. Emit and sign one deterministic POAG1 content epoch containing the three finite games.
3. Make the beta station consume only that epoch and visibly distinguish local field records from
   federation-judged receipts.
4. Cut the isolated node image and ceremony with the PoA deployment domain, verified N=2 admission,
   and no demo economy.
5. Wire one end-to-end judged run into world contribution and the Field Archive.
6. Wire that same receipt into one fail-closed Dark Bazaar salvage offer and private clearing demo.
7. Deploy behind Basic Auth, exercise it visually and from the extension, then publish exact operator
   reproduction steps.
8. Expand content through declarative deck maps and additional finite games; start The Descent work
   once the shared receipt/content spine is boringly reliable.
