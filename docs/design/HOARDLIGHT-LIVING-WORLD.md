# HOARDLIGHT: THE LIVING WORLD

## Extensibility architecture for stories, games, agents, society, and the decentralized MUD

> Hoardlight is not the game we keep making larger. It is the first warm window into a world that can keep becoming more things.

This is the architectural companion to `docs/design/DRAGON-DESCENT-VISION.md`. That document answers what the first beloved game is. This one asks the more dangerous question:

**Does building Hoardlight create the beginning of a living world, or merely a charming cul-de-sac?**

The answer after reading the engine with that question in mind is:

> **The substrate thesis is directionally true, materially instantiated, and not yet true as an integrated description of HEAD.**

Dregg really does have a remarkably general primitive: an authorized turn composes committed entity state with an action under installed law, then leaves a receipt. The executor, custom-verifier carrier, signed-turn node path, state recovery, asset lineage, multi-surface offering layer, collective decisions, authored worlds, and attested-agent work are not dragon-game tricks. They are pieces of a general world machine.

But those pieces are currently a **portfolio of real primitives and adjacent proofs**, not one versioned game-and-world protocol. Several flagship apps still own private executors. Several “shared” worlds are one-process object graphs. The playable custom games and their strongest proof paths are not yet the same path. The common federation adapter submits an app receipt **commitment**, not the app's full transition and world state. Identities are often opaque strings adapted between crates. There is no universal ruleset manifest, no general entity-parameter composition contract, and no durable multiplayer realm service.

So the thesis is not an excuse to proceed casually. It is a design constraint:

> **Stage 1 must be the first customer of the general substrate, not the place where Hoardlight-specific assumptions become the substrate.**

If we get that seam right, new stories, games, AI roles, markets, social institutions, and persistent federated places become additions: new content roots, schema versions, verifier keys, agent mandates, and surfaces. If we get it wrong, every future mode will require archaeology inside the dragon game.

---

## 1. The thesis, made precise

The useful claim is not “everything is already generic.” It is:

```text
Turn
  = resolve(
      realm + world@pre_root,
      actor@identity,
      entities@versioned_roots,
      scene@content_root,
      typed_action,
      ruleset@ruleset_root,
      optional agent attestations,
      finalized observations + witnesses
    )
  -> committed entity deltas + events + receipt@post_root
```

A **game** is then a family of entity schemas, typed actions, rulesets/verifiers, content, and projections over that turn. A **story** is content plus a permitted transition grammar over the same world. An **AI character** is an attested, capability-bounded proposer of typed actions. A **society** is persistent identity, assets, groups, places, and agreements expressed as mutually visible turns. A **MUD** is a durable realm in which many identities continually submit those turns and converge on the same finalized world.

The kernel does not need to know what a dragon, card, guild, room, romance, election, or shop is. It needs to know how to authenticate an actor, locate exact pre-state, resolve a named version of law, verify observations and custom proofs, authorize effects, commit the post-state, and issue a reconstructible receipt.

### Why the claim is credible

The core program model is already not genre-shaped. A cell can carry a predicate, default-deny transition cases, or a circuit-named law (`cell/src/program/types.rs:3`, `cell/src/program/types.rs:23`). The evaluator makes unmatched method-dispatching cases refuse rather than fall through (`cell/src/program/eval.rs:64`). Cross-cell equality is a real fail-closed predicate: without an executor-provided finalized-root authority or its bound witness it refuses, and the local post-state must equal the observed peer value (`cell/src/program/eval.rs:2049`).

The custom-verifier lane is also genuinely general. VK v2 binds program bytes, AIR shape, verifier implementation, and proving system rather than treating a human label as law (`cell/src/vk_v2.rs:1`, `cell/src/vk_v2.rs:161`). Executors hold a per-instance registry from VK hash to canonical bytes and verifier (`cell/src/custom_effect.rs:150`, `cell/src/custom_effect.rs:175`), and a proof-carrying turn fails closed if its VK is unregistered or the verifier rejects it (`turn/src/executor/proof_verify.rs:216`). That is the right cryptographic carrier for “add a new game without changing the kernel.”

The same generality appears above the executor. `Offering` defines one open/actions/advance/verify/render contract whose legal advance lands a receipt and whose illegal advance commits nothing (`dreggnet-offerings/src/lib.rs:439`, `dreggnet-offerings/src/lib.rs:459`). It renders a shared `ViewNode` affordance tree (`dreggnet-offerings/src/lib.rs:83`); `SurfaceBackend` projects that tree onto a channel and decodes an actuation back into the same `{turn, arg}` (`deos-view/src/backend.rs:18`). That is already a many-views architecture, not a Discord game bolted to a web game.

The node work proves two other essential statements. A headless node can host a userspace MUD in which a signed player turn changes real ledger cells while a more broadly capped GM changes different cells (`node/src/mud_e2e.rs:1`). Two distinct key-ceremony identities can co-inhabit one board, observe each other's attributed turns over SSE, and be refused when one reaches into the other's private cell (`node/src/shared_world.rs:1`, `node/src/shared_world.rs:17`). Those are small demonstrations, but they are exactly the multiplayer-MUD primitive.

### Where the claim is false at HEAD

The general pieces do not yet compose through one canonical protocol:

1. **There is no world-governed ruleset catalog.** A custom verifier is registered in a particular executor instance, and an executor that does not register it refuses it (`cell/src/custom_effect.rs:184`). That is safe, but it is host configuration—not yet a realm manifest saying which immutable ruleset roots are valid at which world height.
2. **There is no common game-module contract.** Automatafl, multiway-tug, spween, the node-hosted JavaScript MUD, and the RPG feature crates each hand-author different combinations of schema, host mover, `CellProgram`, custom AIR, proof wrapper, identity adapter, and offering.
3. **Playable and proven can be parallel lanes.** Automatafl has a real custom AIR and foldable proof tests (`dregg-automatafl/src/lib.rs:1`, `dregg-automatafl/tests/prove_fold.rs:36`), but its offering computes `apply_turn` on the host and commits the resulting state (`dregg-automatafl/src/surface.rs:805`, `dregg-automatafl/src/surface.rs:839`). Its own surface names the in-proof sealed move as a subsequent wiring lane (`dregg-automatafl/src/surface.rs:37`). Multiway-tug likewise advances its reference engine and commits a projection in the playable offering (`dregg-multiway-tug/src/surface.rs:345`, `dregg-multiway-tug/src/surface.rs:359`), while its fold helper constructs separate custom legs (`dregg-multiway-tug/src/fold.rs:148`).
4. **Most app federation is commitment routing, not shared state execution.** `SubmittedTurn` contains a domain, a 32-byte app commitment, and an optional predecessor—not the app turn body, entity deltas, content, witnesses, or ruleset (`node-target/src/lib.rs:91`). The HTTP path wraps that commitment in a node `EmitEvent` turn (`node-target/src/lib.rs:359`), and `NodeTarget::Federation` confirms the wrapper appears in the node log (`node-target/src/lib.rs:215`), but the app still owns its in-process ledger. The crate says so explicitly (`node-target/src/lib.rs:1`).
5. **Identity and ledgers remain fragmented.** The offering-wide identity is an opaque `String` wrapper (`dreggnet-offerings/src/lib.rs:302`). `dreggnet-adventure` derives custody, guild, run, and asset identities from one name through an adapter, but calls it a small adapter rather than a protocol redesign (`dreggnet-adventure/src/lib.rs:98`). The canonical asset crate says each holder currently runs a sovereign `EmbeddedExecutor` and names a shared federated ledger as unbuilt (`dreggnet-asset/src/lib.rs:76`).
6. **Persistence is not yet a persistent game realm.** Offering sessions can be reopened from a seed plus a landed-move log (`dreggnet-offerings/src/lib.rs:60`), and snapshots can reconstruct a finalized ledger against a trusted root (`persist/src/snapshot.rs:279`). Neither is yet the durable, queryable, many-player world service every game uses.

The thesis therefore passes as a **north-star architecture** and fails as a **status slogan**. Hoardlight is safe from becoming a cul-de-sac only if its first implementation closes the shared seams instead of building around them.

---

## 2. The architecture to grow into

The target is a small set of versioned, content-addressed contracts. Names here are architectural, not a demand for these exact Rust identifiers.

### 2.1 A world manifest

Every durable realm or instance should be born from a committed `WorldManifest` containing at least:

- a protocol/version identifier;
- a `RealmId` and `WorldId`, plus an optional parent world/instance;
- the genesis state root;
- allowed entity-schema roots;
- the ruleset-catalog root and resolver policy;
- content roots or a content-registry root;
- the identity namespace and cross-realm identity policy;
- asset/ledger domains the world may observe or mutate;
- lifecycle policy: persistent realm, daily instance, private party fork, tournament match, or disposable practice dream;
- governance and upgrade authority, including activation heights and rollback/refusal rules;
- data-availability commitments for the manifest, rulesets, content, genesis, and full turn bodies.

The manifest is the answer to “who owns the world?” A host may serve it, a federation may finalize it, authors may contribute to it, and governors may authorize future additive roots—but no one operator silently edits what its existing receipts meant.

### 2.2 A game-module manifest

A new game should plug in by publishing a versioned module, not by changing the turn kernel:

```text
GameModuleManifest
  module_id + semantic/wire version
  entity_schema_refs[]
  action_schema_ref
  ruleset_refs[]
  verifier_refs[]          # VK v2 roots and their public-input contracts
  parameter_projections[]  # which foreign entity facts this game understands
  receipt/event schema
  replay/verification recipe
  surface vocabulary/profile
  migration/compatibility policy
```

The existing VK v2 hash is a strong foundation because it binds all four soundness-relevant verifier components (`cell/src/vk_v2.rs:167`, `cell/src/vk_v2.rs:212`). What is missing is the world-level manifest and resolver that says, “for this turn at this height, this exact module and VK are law.”

### 2.3 The versioned resolver

The resolver is not “the current Rust function.” It is a committed selection rule:

```text
(world_version, action_type, subject_schema_versions, scene_type)
    -> exact ruleset root + verifier root + public-input layout
```

Every receipt must commit the selected ruleset root, not merely the resulting state. Old receipts continue to resolve under old roots. New rooms, games, balance rules, agent policies, or composition laws arrive as new roots with explicit activation—not as edits that change historical meaning.

Dregg already does this discipline in pieces. Randomness requests reserve a `game_binding` for a ruleset hash and bind sequence, pre-state root, action, purpose, and draw count (`dice/src/request.rs:15`). `attested-dm` hashes the objective and loot tables into a game binding but explicitly calls a full ruleset hash the production form (`attested-dm/src/game.rs:1417`). Stage 1 should finish the pattern rather than create another partial fingerprint.

### 2.4 Typed entities and typed projections

An entity is not “sixteen anonymous slots.” It is:

```text
EntityRef = (realm, entity_id, schema_root, state_root)
```

Its schema defines canonical field encodings, privacy classes, legal migrations, and named projections. A game does not receive arbitrary access to a dragon's entire state. It asks for a declared, verifier-readable projection such as:

- `Hoardlight.ResonanceBraid.v1`;
- `Common.Ownership.v1`;
- `Common.StageAndConsent.v1`;
- `Automatafl.ExhibitionWeather.v1`;
- `Trade.AssetTraits.v1`.

That is how a creature's parameters can feed **any game that chooses to understand them** without declaring that every game must use the same stat vector. A chess-like game may ignore dragons entirely. A normalized ranked game may accept only a symmetric cosmetic projection. A cooperative exploration game may consume the full resonance projection. The module declares the projection; the verifier proves the values came from the named entities at named finalized roots.

HEAD has the first real atom for this: `ObservedFieldEquals` binds a peer cell, field, root, witness index, and local value (`cell/src/program/types.rs:1528`), and the executor builds an authority from committed peer state (`turn/src/executor/execute_tree.rs:106`). It is not yet the general solution. The authority builder only scans `CellProgram::Predicate` and explicitly skips `Cases` (`turn/src/executor/execute_tree.rs:140`), while most authored games compile to `Cases`. The embedded-world witness is structurally required but is not cryptographically opened against the root; the host recomputes from its own ledger, and cross-node root/witness transport remains the named production add (`dungeon-on-dregg/src/multicell.rs:48`).

The general composition verifier must therefore accept an arbitrary bounded set of typed entity projections, bind their schema and state roots, verify finalized openings, canonicalize order, apply one exact ruleset, and expose an explanation commitment. It must not be “dragon A slots + dragon B slots + three pocket slots” frozen into a circuit forever.

### 2.5 Views are projections, not worlds

Discord, web, Telegram, WeChat, native, spectator, accessible-text, and future spatial clients must all render **one world/session**, not open look-alike sessions on separate ledgers.

The correct seam already exists. An offering returns a `Surface(ViewNode)` (`dreggnet-offerings/src/lib.rs:83`); `Offering::render_for` and `actions_for` provide per-viewer projections without changing the underlying session (`dreggnet-offerings/src/lib.rs:492`, `dreggnet-offerings/src/lib.rs:512`); the backend trait maps the shared tree to each transport (`deos-view/src/backend.rs:18`).

The N-surfaces claim should remain honest. The vocabulary is broad, but native text input is currently display-only (`deos-view/src/tree.rs:61`), and fixed-button chat transports cannot express value-dependent sliders and toggles (`deos-view/src/backend.rs:72`). The architectural promise is **one semantic view tree with channel-specific faithful degradation**, not pixel or interaction parity on every surface.

---

## 3. Axis one: more AI features — accountable agents everywhere

Storyflame should not become a privileged special case named “the AI feature.” It should establish the one boundary every machine participant uses:

> **An AI may observe what its mandate permits, produce an attested typed proposal, and explain it. It may never acquire more state-changing authority merely because it produced fluent text.**

### What exists

The provenance vocabulary is unusually honest. The default attestation carrier is explicitly a self-signed fixture that proves plumbing and nothing about model origin; live policy can require MPC-TLS and refuse fixtures (`attested-dm/src/lib.rs:15`, `zkoracle-prove/src/attestation.rs:142`, `zkoracle-prove/src/attestation.rs:306`). A real Bedrock path connects the prover/notary to the actual endpoint, discloses the returned body, pins the host and a separate notary key, and hides the authorization value (`zkoracle-prove/src/tlsn_bedrock.rs:1`, `zkoracle-prove/src/tlsn_bedrock.rs:299`).

The cap pattern is also correct in spirit. `DmCaps` enumerates scene, flag, and item-grant authority and recursively checks every effect in a batch (`attested-dm/src/lib.rs:1067`, `attested-dm/src/lib.rs:1102`). The prompt template hash, world binding, and player input can be committed into the turn (`attested-dm/src/lib.rs:1243`, `attested-dm/src/lib.rs:1299`).

### What is still prototype-shaped

The default `DungeonMaster::land_move` calls `attest_narration`, the fixture path (`attested-dm/src/lib.rs:1352`, `attested-dm/src/lib.rs:1371`). Its `WorldCell` is a local maps-and-vector model “reconciled against” the real world cell rather than the real turn executor (`attested-dm/src/lib.rs:695`). Its `DmCaps` is a host-side Rust object. Its federation route sends the local receipt commitment before mutating the local world (`attested-dm/src/lib.rs:1392`); it does not cause another node to execute the same typed world effect.

The injection proof is valuable but narrow. Proving that one template slot and one output avoid `{{` is not proof of truth, benevolence, policy compliance, absence of other injection languages, or good game judgment. Transport provenance proves where bytes came from, not that the bytes deserve power.

### The general attested-agent envelope

Every AI-authored turn should optionally carry a verifier-derived envelope like:

```text
AttestedAgentEnvelope
  agent_identity
  role + mandate/capability root
  model/provider provenance policy and verdict
  prompt/template root
  tool/code/container manifest root
  visible input state roots
  typed proposal + proposal commitment
  attestation/proof references
  resolver verdict
  effects actually admitted
```

The surface badge must be computed from the verified envelope. It must distinguish scripted, local/unattested, transport-attested, model-attested, tool-attested, and proof-constrained operation. A model cannot choose its own green badge.

The roles then become ordinary applications of one boundary:

| Agent role | Reads | May propose | May actually change |
|---|---|---|---|
| NPC | Its memory, room, visible visitors | Dialogue, reactions, its own bounded actions | Only effects under the NPC's installed caps and room rules |
| Dungeon master | Scene/world projections permitted by mandate | Encounters, pacing, typed world actions | Nothing until the versioned resolver and executor admit it |
| Room author | Authoring context and content schema | A signed content bundle or remix | The registry may append a new content root; existing history is untouched |
| Companion | Owner-approved private/public projections | Advice, consent-scoped assist, personality action | Its own entity state or explicitly delegated assist only |
| Agent-player | The same player-visible state a human client receives | Ordinary typed game actions | Exactly the seat/session capabilities it holds, with bot attribution and rate policy |
| Society agent | Market, guild, or civic public state | Listings, votes, services, moderation proposals | Only escrow, treasury, ballot, or moderation caps explicitly delegated to it |

“Accountable AI everywhere” becomes real only when five conditions hold together:

1. provenance policy is explicit and fail-closed;
2. inputs and code/prompt/tool manifests are committed;
3. the proposal is typed and bound to exact pre-state;
4. capability and ruleset verification—not the model—decide effects;
5. durable indexes let a player query every turn, model/path badge, mandate, refusal, and consequence attributable to an agent.

HEAD has strong examples of conditions 1–4 in separate places. It does not have the general envelope or the durable provenance index. That index is not merely an explorer convenience: reputation, agent hiring, appeals, safety audits, and provenance-gated mechanics all depend on it.

---

## 4. Axis two: other kinds of stories — content over law

The story substrate should support at least four distinct modes without changing the kernel:

1. **Authored interactive stories.** A signed content bundle provides rooms/scenes, prose, typed choices, stimuli, and references to allowed rulesets.
2. **Committed procedural worlds.** A published seed and generator version reproduce the identical content bundle.
3. **Collective fiction.** A crowd certifies which legal branch becomes history.
4. **Agent-augmented stories.** Attested agents propose prose or typed branches under the same content and capability boundary.

### The room/scene grammar is general; the room library is authored

`spween-dregg` already demonstrates the right split: parsed scenes become content over a real world-cell executor, with deterministic passage/variable layout and one method case per choice (`spween-dregg/src/compiler.rs:181`, `spween-dregg/src/compiler.rs:231`). `ugc-dregg` content-addresses an authored or procgen universe, supports signed author identity and parent/remix lineage, and verifies completions by replay (`ugc-dregg/src/lib.rs:1`, `ugc-dregg/src/lib.rs:83`, `ugc-dregg/src/lib.rs:270`). `procgen-dregg` makes the whole room graph a pure function of a committed seed and a fixed indexed draw stream (`procgen-dregg/src/lib.rs:15`, `procgen-dregg/src/lib.rs:30`).

The general grammar should define:

- room and scene identity;
- typed stimuli, tags, exits, clocks, occupants, affordances, and visibility;
- typed conditions and effects, each labeled by whether it is executor-enforced, custom-verifier-enforced, or presentation-only;
- content imports and ruleset references by root;
- localized prose and art/audio references;
- author/procgen/agent provenance;
- migration and compatibility behavior;
- safety/resource bounds for content compilation.

Hoardlight contributes six exquisite room families, cozy vocabulary, the Downbelow, named reactions, and resonance-oriented approaches. A mystery contributes clues, suspicions, testimony, and revelation rules. A political drama contributes constituencies and promises. A romance contributes consent and relationship-memory schemas. A survival story contributes scarcity and weather. None should require editing the executor; each adds content schemas and, only where necessary, a new ruleset/VK.

### Collective fiction is a second mode, not a UI option

The collective path is already more than a poll pasted onto a story. `spween-dregg` puts only available typed choices on the ballot, resolves a winner, commits the winner/tally binding into the same world turn, and can verify that the operator did not apply another branch (`spween-dregg/src/collective.rs:86`, `spween-dregg/src/collective.rs:140`, `spween-dregg/src/collective.rs:210`). `dungeon-on-dregg` goes further on ballot identity and quorum: signed seated ballots drive a real vote engine, while the game executor can still refuse a quorum-certified but illegal command (`dungeon-on-dregg/src/collective.rs:40`, `dungeon-on-dregg/src/collective.rs:30`).

That already gives an un-retconnable **branch-authorship** mode: the crowd authors which allowed future becomes history. It does not yet give arbitrary crowd-authored scenes. The spween harness still receives ballots from a caller while naming production ballot turns (`spween-dregg/src/collective.rs:93`), and a proposal is a coordinate in a closed move set rather than a free-form mutation (`dungeon-on-dregg/src/collective.rs:245`).

The next additive step is a content-governance turn:

```text
signed proposals -> schema validation -> optional agent/editor attestations
                 -> electorate/quorum decision -> append content root
                 -> later scene turn references that immutable root
```

The crowd may extend the canon, but it cannot rewrite old receipts. An AI may help draft a room, but its authorship/provenance stays visible. A host may refuse to serve unsafe content, but it cannot claim a different bundle under the same root.

### HEAD warning: the current compiler cannot be mistaken for the permanent grammar

The compiler is explicitly v0. String/float comparisons and a choice that overwrites its own precondition remain handler-only (`spween-dregg/src/compiler.rs:20`). It has a fixed sixteen-register allocation and rejects scenes that exceed it (`spween-dregg/src/compiler.rs:211`). More seriously, it installs a permissive `genesis` method (`spween-dregg/src/compiler.rs:231`), while `WorldCell::apply_raw` publicly drives arbitrary method/effect pairs (`spween-dregg/src/world.rs:412`). A test proves that the same heap write can be invoked under `genesis` after deployment and commit (`spween-dregg/tests/heap_hatch.rs:114`).

That write-hatch is acceptable only as setup machinery in a prototype. In a living world, genesis must be factory-only or lifecycle-gated exactly once. Leaving it callable would let future content, admin tools, or compromised hosts rewrite fields without passing the authored move law. This is a Stage 1 stop-ship substrate issue.

---

## 5. Axis three: other kinds of games — additive Custom-VK modules

The promise is not that every game compiles into today's `StateConstraint` vocabulary. The promise is that every game can use the same turn, identity, entity, asset, receipt, persistence, and surface substrate while bringing the law it needs.

Simple invariants should remain stock teeth: write-once identity, monotone progression, exact deltas, default-deny method dispatch, bounds, ownership, and finalized peer observations. Complex transitions—Automatafl's board evolution, Hoardlight's nonlinear resonance, a physics game, an auction-clearing rule, a card game's hidden-hand transition—arrive as Custom VKs whose public-input contract is declared in the game module.

### What a new game must implement

Under the target architecture, a game author supplies:

1. **Versioned state schemas.** Canonical encoding, field meanings, privacy classes, and migration policy.
2. **A typed action schema.** Canonical action bytes, actor/seat rules, and resource bounds.
3. **A deterministic resolver.** Given exact public/private witness inputs, produce the proposed next state and explanation events.
4. **Verifier law.** Stock constraints and/or a Custom VK proving the transition and binding all public inputs.
5. **Foreign-entity projections.** Optional contracts saying which creature, asset, guild, weather, season, or realm facts the game consumes.
6. **Receipt/replay semantics.** What a verifier needs to reconstruct, audit, or succinctly verify the game.
7. **An Offering/ViewNode projection.** Actions, viewer-specific visibility, and surfaces; channel renderers remain shared.

It should not implement a new identity system, wallet, provenance chain, federation adapter, persistence format, or frontend-specific rules engine.

### What the current game portfolio proves

Automatafl proves that a hand-authored transition AIR can check `new == apply_turn(old, moves)` and expose a foldable commitment (`dregg-automatafl/src/lib.rs:1`, `dregg-automatafl/tests/prove_fold.rs:57`). Its offering proves a viewer-specific hidden-state surface and a real receipted game loop (`dregg-automatafl/src/surface.rs:25`, `dregg-automatafl/src/surface.rs:587`).

Multiway-tug proves a different shape: heap-backed game state, conservation and one-use teeth, collectible assets, a hidden-hand Merkle verifier, a fold path, and an Offering (`dregg-multiway-tug/src/lib.rs:14`, `dregg-multiway-tug/src/lib.rs:57`). These are valuable because they are different. They show that “a game” cannot be equated with a spween story or one stock schema.

What they do **not** yet prove is a single registration flow in which the live offering's resolve turn necessarily carries and passes the exact custom proof that defines the game's advertised law. That weld is the productization gate for the module architecture.

### Can a dragon's parameters feed any game?

**Mechanically: yes, through a declared projection. Universally: no, and that is a feature.**

Any game can depend on `Hoardlight.ResonanceBraid.v1` or a narrower public projection. The cross-entity verifier proves the values and roots it consumed. The game ruleset decides what those values mean. The result may be power, weather, cosmetics, matchmaking, dialogue flavor, handicapping, or nothing.

No game should import the dragon crate and read slots by convention. No dragon update should silently change another game's outcome. No competitive game should be forced into pay-to-win because an asset has a large number. Versioned projections and ruleset roots make reuse explicit, reviewable, and historically stable.

The stable `AssetId` already shows the cross-game addressing idea: it survives changing note cells and is intended as the handle another game or market names (`dreggnet-asset/src/lib.rs:40`, `dreggnet-asset/src/lib.rs:119`). The missing layer is a shared finalized ledger plus a general verified projection from the asset/entity into the consuming game's public inputs.

---

## 6. Axis four: non-AI features — from feature crates to a society

A living world is not made alive by adding more narrators. It becomes alive when people can inhabit places together, form durable institutions, make and exchange things, acquire reputations, keep promises, and leave history.

The RPG crates already contain much of the right social algebra:

- assets are owner-signed successor notes with stable identity, immutable trait roots, soulbinding, and recomputable lineage (`dreggnet-asset/src/lib.rs:9`, `dreggnet-asset/src/lib.rs:247`);
- trading binds owner-signed asset transfer to sealed escrow, settles only when both legs are present, and lets a ghosted depositor reclaim (`dreggnet-trade/src/lib.rs:12`, `dreggnet-trade/src/lib.rs:398`);
- guild membership is a capability grant over a shared cell, with nonmembers refused by the executor (`dreggnet-guild/src/lib.rs:8`, `dreggnet-guild/src/lib.rs:152`);
- faction standing has a typed shared projection and a persistence adapter (`dreggnet-faction/src/standing.rs:1`, `dreggnet-faction/src/standing.rs:95`);
- quests use ordered committed steps, replay-verified completion, and a real cross-cell reward giver (`dreggnet-quest/src/lib.rs:45`, `dreggnet-quest/src/lib.rs:59`);
- the tavern demonstrates distinct identities sharing a board, presence, private stalls, party formation, live receipt events, and an overreach refusal (`dreggnet-tavern/src/lib.rs:1`, `dreggnet-tavern/src/lib.rs:20`).

This is not empty roadmap scaffolding. It is a real vocabulary for a society.

### What “deepen into a real society/economy” means

It does not mean creating twenty more isolated feature crates. It means making the existing objects persistent, mutually referential, and governed inside one realm:

- **One identity spine.** Device keys, platform bindings, recovery/rotation, pseudonymous realm personas, agent identities, guild membership, asset ownership, and author identity must resolve through explicit credentials rather than name-derived adapters.
- **One shared asset/economic ledger seam.** A crafted item, stall listing, escrow deposit, trade settlement, hoard placement, and another game's equipment projection must name the same finalized note and lineage.
- **Durable places.** Taverns, roosts, guild halls, markets, homes, workshops, and public boards survive process restart and have occupancy, permissions, history, and moderation state.
- **Durable social objects.** Invitations, parties, contracts, listings, bids, quests, reputations, sanctions, elections, and appeals are cells/receipts with indexes—not ephemeral bot state.
- **Economic policy.** Sources, sinks, fees, leases/expiry, scarcity domains, market abuse controls, fraud proofs, treasury rules, and anti-sybil costs become explicit rulesets. The trade crate itself names order books, a market frontend, and a treasury fee as unbuilt (`dreggnet-trade/src/lib.rs:55`).
- **Governance without omnipotence.** Institutions receive narrow capabilities: publish a room pack, schedule a festival ruleset, moderate a board, disburse a voted treasury leg. Governance does not receive a magic rewrite-state method.
- **Queryability.** Ownership, ancestry, price history, memberships, standing, contributions, authored content, and dispute outcomes need durable proof-aware indexes.

### The honest gap

The current web feature world can make craft, inventory, and trade share one object-identical `Rc<RefCell<GameWorld>>` (`dreggnet-surfaces/src/world.rs:254`). That closes a valuable demo-level object identity seam, but it is still one-process memory. `dreggnet-adventure` integrates a whole loop and preserves run/item/player identity, yet says the gear and companion aid cells are not bound onto the literal Descent world because there is no exposed shared executor handle (`dreggnet-adventure/src/lib.rs:55`). Guild state and its board are also in-process and name a durable store as a residual (`dreggnet-guild/src/lib.rs:51`).

The substrate work is therefore not “invent social features.” It is **graduate the existing social facts onto one durable identity, realm, ledger, and finality model**.

---

## 7. Axis five: the decentralized MUD

Is the decentralized MUD simply “Hoardlight persisted + multiplayer + federated”?

**At the level of primitives, almost. At the level of architecture, those three words each hide a protocol.**

Hoardlight's daily Descent is an instance: a committed seed, a bounded run, one or a few players, a terminal result, and selected outputs carried home. A MUD is a realm: no ordinary terminal state, many actors, long-lived places and institutions, concurrent decisions, durable indexes, and state replicated across operators.

The same turn substrate can serve both. What changes is the world manifest and service around it.

### 7.1 Daily instance versus persistent realm

A daily Downbelow should have:

- a parent persistent realm (Hearthspire);
- an immutable day seed, generator version, content roots, and ruleset roots;
- explicit admission, practice/ranked, party, and expiry policy;
- a terminal export policy saying which receipts/assets/memories may cross back into Hearthspire;
- no ability to mutate yesterday's instance after finalization.

The persistent realm has:

- stable world identity and a continually advancing finalized root;
- durable rooms, residents, groups, markets, content catalog, and governance;
- a registry of child instances and their certified outputs;
- retention and availability rules sufficient to recover and audit its history.

This makes the daily game a **portal and event inside the MUD**, not the MUD database itself.

### 7.2 Many players in one scene

The local node proof already has the right core: two distinct signers act on one shared board, both observe committed receipt events, each receipt is attributed, and capability overreach is refused (`node/src/shared_world.rs:8`). The MUD proof similarly hosts rooms, a character, an NPC, and fork-scoped dungeon affordances as real cells (`node/src/mud_e2e.rs:9`, `node/src/mud_e2e.rs:217`).

Production adds semantics the demo can avoid:

- scene occupancy and visibility at a particular finalized root;
- ordering and conflict behavior when many actors target the same entity;
- private/public/team projections;
- leases, timeouts, disconnects, and asynchronous turns;
- admission, rate, moderation, and resource budgets;
- atomic multi-entity transactions or explicit sagas when one action touches room, character, item, quest, and market state;
- deterministic GM/NPC reactions that cannot race differently on different nodes.

Those belong in versioned realm/game rules, not frontend orchestration.

### 7.3 What federation actually gives

The real node federation is more than a replicated database. The blocklace path stages signed turn payloads into round-disciplined blocks so waves can finalize cross-node (`node/src/blocklace_sync.rs:258`). Locally finalized blocks produce votes bound to the exact canonical ledger root (`node/src/blocklace_sync.rs:4105`, `node/src/blocklace_sync.rs:4124`). A block becomes consensus-attested only after a threshold of distinct committee members signs it (`node/src/blocklace_sync.rs:240`), and persisted attested roots verify a threshold of both classical and enrolled post-quantum signatures over the exact block/root (`persist/src/federation.rs:191`, `persist/src/federation.rs:213`).

That gives the MUD:

- a cross-node order for admitted full turns;
- deterministic execution against a common ledger;
- quorum-attested finalized roots;
- restart anchors and auditable receipt history;
- no single serving node able to invent a different finalized state and pass verification;
- a basis for clients to follow events and verify membership/proofs against trusted roots.

Snapshot machinery can ship checkpoint plus overlay and require reconstruction to a trusted finalized root (`persist/src/snapshot.rs:72`, `persist/src/snapshot.rs:287`). That is the right recovery/data-plane primitive.

### 7.4 What federation does not yet give the game layer

It does not automatically turn every embedded app into that replicated world.

The widely used `NodeTarget` route submits only an app receipt commitment (`node-target/src/lib.rs:91`). Its real HTTP transport makes that commitment one event word inside a genuine node turn (`node-target/src/lib.rs:359`). `spween-dregg` first commits the game turn in its private `EmbeddedExecutor`, then routes only `receipt.turn_hash` under the scene domain (`spween-dregg/src/world.rs:436`). A remote node can attest that it logged that commitment; it cannot re-execute the scene from the submitted object, serve the authoritative room state, or transport the cross-cell witness because it never received those materials.

The cross-cell demo names the remaining production seam exactly: an independently finalized peer-root channel plus cryptographic opening verification for a peer on another node (`dungeon-on-dregg/src/multicell.rs:48`). The node's checkpoint-block pipeline also contains an explicit unwired path: finalized checkpoint payloads are observed but not stored there (`node/src/blocklace_sync.rs:4083`). These are not reasons to distrust the federation core; they are reasons not to call a commitment-routing adapter a federated MUD.

The game layer still needs:

- one ingress carrying full canonical game turns, ruleset/content references, agent envelopes, witnesses, and data-availability locators;
- world-aware deterministic execution of those turns on federation nodes;
- finalized world-root and per-entity witness transport to clients and other realms;
- a canonical query/index service derived from finalized receipts;
- content/ruleset availability and verifier distribution;
- realm membership, governance, upgrade, and emergency/refusal policy;
- cross-realm transfer/message protocols for objects that truly move between federations.

### 7.5 Who owns the world?

“Nobody owns it” must not mean “nobody is responsible for it.” The intended answer is:

- players own/control their keys and capability-scoped entities;
- authors sign and receive attribution for immutable content contributions;
- institutions control narrow capabilities under their constitutions;
- a realm's governance authorizes future manifests/ruleset roots under explicit thresholds and activation rules;
- the federation committee orders and attests turns but does not get to reinterpret them;
- any verifier can reconstruct the same state and detect a fork, omitted dependency, invalid upgrade, or fabricated history.

No single host owns the power to rewrite the world. The world is owned, in the constitutional sense, by its manifest, capability graph, governance receipts, and replicated history.

### 7.6 Is the world reconstructible from receipts?

That should be a protocol invariant, with a precise qualification:

> Full canonical turn bodies plus genesis, schemas, rulesets/verifiers, content, ordered finality, and required witness/agent artifacts must reconstruct the world. A receipt hash or finalized root alone cannot.

HEAD already demonstrates replay verification for spween playthroughs (`spween-dregg/src/verify.rs:97`) and ledger recovery from checkpoints/overlays (`persist/src/snapshot.rs:1`). But snapshot installation explicitly does not provide the shipping node's full per-turn commit log (`persist/src/snapshot.rs:315`). Succinct proof-backed UGC entries intentionally store no moves (`ugc-dregg/src/lib.rs:944`). Those are valid modes, but they answer different questions: current state availability, proof of a history property, and full narrative reconstruction are not interchangeable.

The living-world protocol needs explicit retention classes:

- **state availability:** enough snapshot/witness material to use the current world;
- **verification availability:** enough proof and manifest material to verify the root/history claim;
- **historical replay availability:** all canonical turns and dependencies needed to reconstruct every intermediate state and story;
- **private history:** encrypted or selectively disclosed artifacts whose commitments remain public.

---

## 8. The central seam: Stage 1 substrate versus Hoardlight content

Stage 1 in the vision is intentionally tiny: one dragon, eight values and two knots, a six-family daily, four approaches, wakefulness/spook/shinies/nooks, First Flame, a three-slot pocket, early growth, Discord, and a web card (`docs/design/DRAGON-DESCENT-VISION.md:477`).

Small product scope must not mean Hoardlight-shaped infrastructure. The following division is the line to protect.

| Build as GENERAL SUBSTRATE in Stage 1 | Supply as HOARDLIGHT CONTENT in Stage 1 | Stage 1 exit condition |
|---|---|---|
| **Versioned world/instance manifest**: realm, world, parent, lifecycle, genesis, schemas, content, ruleset catalog, identity and ledger domains | Hearthspire as parent; today's Downbelow as a daily child instance; First Flame/practice policy | Every turn names the world/instance and exact manifest version; a daily can expire without erasing its history |
| **Versioned entity-schema registry** with canonical codecs, privacy labels, migration rules, and schema roots | Dragon entity with eight resonance dimensions, two knots, wakefulness/spook/growth fields; pocket entity with three slots | No resolver or UI reads raw slot numbers by convention; historical schema versions remain decodable |
| **Versioned resolver and ruleset catalog** mapping typed action + schemas + scene to exact ruleset/VK roots | The four approaches, resonance coefficients, reaction thresholds, dream-spill and banking laws | Receipt commits the selected roots; changing balance creates a new root, never changes an old receipt |
| **General bounded cross-entity composition verifier** over typed projections, canonical entity ordering, finalized roots, and explanation commitments | Dragon braid + pocket shinies + room stimulus -> named reaction, wakefulness/spook/loot delta | The verifier is parameterized by schemas/ruleset, not by “one dragon + three charms”; forged/missing/stale peer inputs refuse |
| **Room/scene grammar and compiler contract**: typed stimuli, choices, effects, visibility, imports, rule refs, enforcement labels, resource bounds | Button-Mushroom Lift, Moth Librarian, Teacup Geyser, Bellroot Garden, Polite Puddle, Moonmilk Pantry; cozy prose and art refs | Six families compile as content bundles; unsupported gates are visibly presentation-only or rejected, never mislabeled enforced |
| **Lifecycle-safe genesis/factory path** that cannot be called after construction | Initial dragon/day/pocket state values | Post-genesis raw calls cannot use setup authority; the current public `genesis` hatch is gone or provably one-shot |
| **Canonical identity/realm binding** with device/platform credentials, actor attribution, recovery/rotation hooks, and cross-surface session identity | Player owns one dragon; ranked First Flame nullifier/attempt policy | Discord and web address the same actor, dragon, daily, and run—not derived look-alikes or parallel sessions |
| **Shared-ledger interface** for world entities and asset notes, with finalized observation APIs | Provisional/banked/nibbled shinies and the three-slot Expedition Pocket | A shiny named in the pocket is the same asset later viewed, crafted, or traded; Stage 1 may limit verbs but not create a second identity |
| **Attested-agent boundary in the turn/receipt schema**, optional and empty when no agent participates | No required AI in Stage 1; later Storyflame prompt/personality/policy are Hoardlight content | Adding Storyflame in Stage 2 adds an agent envelope/policy root, not a new turn type or privileged mutation path |
| **Receipt/event/explanation schema** that binds pre-state, inputs, selected law, post-state, causes, provenance, and refusals | “Puddle-Song,” “Glitter-Sneeze,” “Cozy Deadlock,” and the human-readable “Why?” mapping | Replay and explorer can distinguish law, inputs, result, and presentation; an explanation cannot diverge from the proven terms |
| **Offering/ViewNode semantic vocabulary and session routing** with viewer-aware projections | Dragon portrait, room card, resonance hints, pocket editor, tuck-in/descend affordances, cozy voice | Discord and web are views of one session; channel degradation is intentional and tested at the semantic level |
| **Content-addressed bundle and availability contract** with author/procgen provenance and safe resource limits | Six room-family bundle, shiny catalog, reaction names, localized prose, deterministic art inputs | A stranger can fetch/recompile the exact content referenced by a receipt; new packs are additive roots |

### The governing equation

For Stage 1 and every later stage:

> **game = data + rulesets over a versioned verifiable engine**

“Data” includes content and schema instances. “Rulesets” include stock constraint programs and Custom VKs. “Versioned engine” includes the resolver, canonical encodings, verifier/public-input contracts, and historical compatibility.

New material is additive:

- new dragon room: content root;
- new story genre: content schema and perhaps a new ruleset root;
- new game: game-module manifest and VKs;
- new AI NPC: agent identity, mandate, provenance policy, and content;
- new market rule: ruleset root activated by governance;
- new surface: backend/view projection;
- new realm: world manifest and genesis.

None should require editing what an old receipt meant.

### Where a naive Stage 1 becomes a cul-de-sac

A naive implementation will be fast and wrong if it:

- puts eight resonances into anonymous fixed slots and lets every consumer memorize their indices;
- hardcodes “one dragon + three pocket items + one room” into the custom circuit public inputs;
- records a resolver version string but not the canonical ruleset/VK root;
- lets Discord own the run while web reconstructs a decorative copy;
- treats `DreggIdentity(String)` or a platform user id as the permanent cross-game principal;
- uses a local `SharedWorld` and promises federation later;
- persists only the daily result, not the ordered full turns and dependencies;
- conflates a daily child instance with the persistent Hearthspire realm;
- allows `genesis` or admin restore methods after world birth;
- lets Storyflame call a world mutation API rather than submit the same typed action everyone else submits;
- bakes the cozy room grammar into the resolver instead of referencing content data;
- turns “why?” into host-authored prose not bound to the verifier's terms.

Every item above is cheap to do once and expensive to remove after players, assets, content packs, and historical receipts depend on it.

---

## 9. The decisions that are expensive to retrofit

### 9.1 Schema and wire versioning

`dregg-schema::Schema` currently has a name and ordered components, with allocation order determining slots; it has no schema version or root in its type (`dregg-schema/src/schema.rs:62`). `SchemaGame` turns `schema.name` directly into `scene_id` and installs the emitted program (`dregg-schema/src/game.rs:70`, `dregg-schema/src/game.rs:96`). That is a strong typed-authoring prototype, not a durable cross-game schema protocol.

Choose now:

- canonical integer/string/map/enum encodings;
- explicit schema ID versus schema version versus content root;
- compatible additions versus breaking migrations;
- whether migrations are proved turns, read-time projections, or child entities;
- how private fields and selective disclosure are versioned;
- how historical decoders/verifiers remain available.

### 9.2 Ruleset-root commitment and activation

A ruleset root must be in the turn/receipt, not inferred from server build, method name, scene name, or current registry. Define catalog inclusion proofs, activation height/time, deprecation without historical deletion, emergency refusal, and governance authority before the first ranked day.

The Custom VK registry is safe dispatch plumbing, but because each executor decides what it registers (`cell/src/custom_effect.rs:184`), two hosts can currently be configured with different accepted sets. The realm catalog is what turns local configuration into shared law.

### 9.3 General parameter composition

The resonance proof will become the most reused and most tempting-to-hardcode component. Its public inputs must be a bounded list of typed projections plus roots and roles—not a fixed Rust struct whose field count encodes Stage 1.

Define now:

- canonical subject ordering and duplicate rejection;
- schema/projection compatibility;
- missing/hidden/default values;
- finalized-root and witness semantics;
- role tags such as actor, partner, equipped, room, weather, institution;
- privacy boundary and selective-disclosure proofs;
- explanation term commitments;
- resource/fuel bounds and denial-of-service limits.

### 9.4 World lifecycle: realm, instance, fork, and return

Daily instancing is a product feature, not the default ontology. Name persistent worlds and child instances separately now. Specify what can cross the membrane, whether a child may observe a moving parent or pins a parent root at birth, and how certified outputs return.

Without this, “make it a MUD later” becomes a rewrite from per-session objects to durable realm objects. The node MUD fixtures already show both a shared root surface and fork-scoped dungeon affordances (`node/src/mud_e2e.rs:240`); turn that distinction into protocol rather than leaving it in a JavaScript host program.

### 9.5 Identity across games, surfaces, and realms

Do not make the first Discord ID the world identity. Define a principal/credential model with key rotation, recovery, device delegation, platform bindings, pseudonymous realm personas, human/agent attribution, and opt-in cross-realm linkability.

The current offering identity is opaque and can be cryptographic if its derivation inputs align (`dreggnet-offerings/src/lib.rs:302`), but “iff the derivation inputs match” is not an account-linking or recovery protocol. Assets, authorship, guilds, votes, runs, dragons, and agents need one explicit answer.

### 9.6 Genesis and privileged maintenance

Genesis must not be a normal callable method. Snapshot restore, migration, moderation, and repair must each have separately scoped, receipted, versioned authority. The current callable spween genesis hatch is the concrete warning (`spween-dregg/tests/heap_hatch.rs:114`). The same pattern appears in schema games, whose public `seed()` simply chooses the permissive genesis method (`dregg-schema/src/game.rs:134`).

### 9.7 Data availability and historical meaning

Content hashes, VK hashes, state roots, and receipt hashes are promises about bytes. Decide who stores those bytes, retention classes, archival incentives/obligations, erasure/privacy behavior, and what a client does when an old dependency is unavailable.

`ugc-dregg` is already content-addressed and preserves author signature and remix parentage (`ugc-dregg/src/lib.rs:133`, `ugc-dregg/src/lib.rs:231`), but its registry is an in-memory `BTreeMap` (`ugc-dregg/src/lib.rs:1048`). That is the right semantic model awaiting a durable registry.

### 9.8 Multiplayer concurrency and finality

Choose whether a game action pins the entire world root, the touched entity roots, or a conflict domain. Define optimistic concurrency, conflict receipts, queued/asynchronous actions, multi-cell atomicity, and deterministic reactions. These choices touch UX, proof public inputs, storage indexes, and federation throughput; they are costly to add after one-player daily semantics become assumed everywhere.

---

## 10. Honest inventory: substrate, prototypes, and missing pieces

| Category | What is genuinely reusable at HEAD | What is prototype-shaped or separate | What all five growth axes still need |
|---|---|---|---|
| Turn law | Default-deny `Cases`, broad `StateConstraint` ISA, fail-closed executor evaluation, custom effects and VK v2 | Cross-cell authority scans only plain predicates; embedded witnesses rely on local recomputation | Versioned resolver/catalog; general typed multi-entity composition verifier; independent finalized witness verification |
| Games | Real Automatafl and tug transition/proof work; playable Offerings; hidden-state UI patterns | Live offering mover/projection and strongest custom proof/fold path are not one mandatory path | `GameModuleManifest`; standard action/public-input/replay contracts; proof-to-live-turn weld |
| Stories | spween scene compiler, receipts/replay, collective winner binding; signed UGC/remix; committed procgen | Compiler v0, fixed slots, handler-only gates, callable genesis; UGC registry in memory | Versioned room grammar, safe compiler contract, durable content/ruleset registry and availability |
| AI | Explicit fixture-vs-live provenance policy; real Bedrock MPC-TLS path; committed prompts; cap model | Default DM landing uses fixture; local modeled world and host cap object | General attested-agent envelope in real turns; role/mandate registry; durable provenance indexes; production notary operations |
| Assets/economy | Stable asset IDs, owner-signed transfer, provenance, soulbinding, escrow trade | Per-holder sovereign executors; app wallets/order matching; local/in-process compositions | Shared federated asset ledger, temporal/lease rules, market/index service, economic governance |
| Social world | Node signed turns, one-node multiplayer shared state, attribution, SSE, tavern/guild/party primitives | Tempdir/in-process sessions, fixed/demo rosters, thin places, local stores | Persistent multiplayer realm service, invitations/presence/moderation, durable places and social indexes |
| Views | Offering/Frontend and rich viewer-aware `ViewNode`; multiple backends | Interaction parity is incomplete; some fronts open separate worlds or render thin forms | One session router/world service; semantic conformance tests and intentional channel profiles |
| Persistence | Durable commit records, attested roots, checkpoint/overlay recovery, trusted-root snapshot verification | App save/replay formats are separate; checkpoint payload path has an unwired branch; snapshots need not carry full history | Realm-aware state/history availability, turn/content/VK archival, durable query indexes |
| Federation | Full signed-turn blocklace order, quorum votes over canonical roots, hybrid signature verification | `NodeTarget` often logs only app commitments; app ledgers remain local | Canonical game-turn ingress and execution, finalized root/witness transport, realm queries, cross-realm messaging/assets |
| Identity | Real signing keys in node turns and collective ballots | `DreggIdentity(String)`, name-derived adapters, per-feature identities | Principal/credential/realm identity protocol with recovery, rotation, device/platform bindings, human/agent attribution |

The central missing object is not “the MUD crate.” It is a **versioned living-world protocol** that binds these existing primitives:

```text
WorldManifest
  + GameModuleManifest(s)
  + Content/Schema/Ruleset registries
  + canonical full TurnEnvelope
  + persistent shared entity/asset ledger
  + finalized root/witness and data-availability services
  + identity/realm credentials
  + durable provenance/query indexes
```

Once that exists, the MUD is a deployment and lifecycle of the substrate—not another bespoke game.

---

## 11. A disciplined growth path

### During Hoardlight Stage 1

Build the general contracts in Section 8, but exercise only one delightful slice. One player, one dragon, one daily, six room families, one pocket, four approaches. No breeding, open market, guild government, UGC editor, or live AI is needed to validate fun.

The architectural gates are:

1. no callable post-genesis setup authority;
2. every ranked turn binds world, entity schema roots, content root, action, ruleset/VK roots, and exact pre/post roots;
3. the resonance verifier accepts general typed entity projections;
4. Discord and web address one world/session;
5. identity and asset references are stable enough to survive future games and realms;
6. complete replay materials are retained for the first ranked history;
7. the receipt has an empty-but-versioned agent-envelope lane rather than assuming “no AI” forever.

### When creatures and AI deepen

Add new entity schema versions and agent mandates, never new privileged paths. Storyflame becomes one attested post-resolution agent. NPCs and companions reuse the same envelope. Breeding adds a new contribution/provenance artifact and ruleset root rather than changing what a v1 dragon was.

### When social/economic life opens

Move dragons, shinies, parties, roosts, standings, stalls, and guild cells into the shared realm ledger. Replace local adapters with realm credentials and durable indexes. Let the Warm Shelf be a persistent place whose games are module references and whose markets settle the same asset notes players carry.

### When UGC and collective canon open

Publish signed room packs and remixes into the durable content registry. Let communities vote to append content roots to their realm or season. Keep validation, resource bounds, ruleset compatibility, moderation, and provenance explicit. Crowd choice remains unable to vote past the executor's law.

### When federation becomes the world

Stop routing only app commitments. Submit the full canonical turn envelope to the realm federation, execute it there, serve the authoritative world state and witnesses from finalized roots, and make embedded mode merely a local single-node deployment of the same protocol.

That is the moment “decentralized MUD” becomes a literal description rather than an architectural rhyme.

---

## 12. The living world at the end

Morning opens the Downbelow from a public committed seed. Thousands of players enter child instances of the same impossible burrow with dragons whose inherited, learned, and hoarded parameters are real entities—not server-side character rows. Every reaction is surprising before it happens and inspectable afterward.

At noon, a room written by a human author and selected by a roost vote enters next week's community burrow. Its content root, parent remix, author signature, editor-agent provenance, and permitted ruleset are visible. The vote can append it to the future; nobody can make it appear in yesterday's receipts.

In the Warm Shelf, two people play Ribbonpull, a third opens Automatafl, a guild recruits for a collective descent, and a market stall escrows a moon-glass spoon. The same identities, creatures, assets, standings, and receipts move through every activity. A dragon's braid creates exhibition weather in one game, opens a peculiar dialogue in another, and is ignored by a normalized ranked match because that game's projection contract says so.

AI is everywhere without being sovereign. A companion offers advice under an owner-granted mandate. An NPC remembers a promise. A dungeon master proposes a festival encounter. A room-author agent drafts three variants. An agent-player takes a seat in a bot-labeled league. Every one carries a provenance badge derived from evidence, a committed prompt/tool/model identity, a bounded mandate, an exact pre-state, and the resolver's verdict. Their words may be wild. Their power is not.

At night, different operators host the realm. They exchange full signed turns, agree on order, execute the same versioned law, and attest the same root. A new node joins from a snapshot verified against that root, fetches the content and verifier dependencies, and continues. Archivists retain the full story history; light clients retain proofs and the heads they care about. A serving operator can disappear without taking Hearthspire with it.

Nobody owns the world in the old sense. Players own keys and capabilities. Authors own attribution. Institutions hold narrow constitutional powers. A federation attests what happened. The manifests and receipts say what it meant. No administrator owns a hidden database switch that can make Pip's family, yesterday's vote, a traded shiny, or a room's law become something else.

And Hoardlight is still there—not swallowed by infrastructure, not demoted to a tech demo. It remains the first view: one tiny dragon, one impossible burrow, one shiny with a past, one soft nook, and one irresistible room too many.

The difference is that the light in that window now belongs to a whole city.

---

## 13. The line to protect

Hoardlight is not a game we extend until it resembles a MUD.

It is the first game that forces us to build the substrate a MUD, a society, many stories, many games, and accountable agents can all inhabit.

If a new story requires a kernel edit, the seam failed.

If a new game requires a new identity or asset universe, the seam failed.

If an AI receives power because it produced prose, the seam failed.

If federation records a hash while the authoritative world remains private to one process, the seam failed.

If an old receipt changes meaning when balance code changes, the seam failed.

If Stage 1 remains small and lovable while its laws, schemas, identities, content, agents, views, persistence, and receipts are already versioned additions to a general world, the thesis wins.

Then Hoardlight is not a cul-de-sac.

It is genesis.
