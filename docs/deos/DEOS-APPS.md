# deos apps — the model, the gap census, the forcing function

*(2026-06-14. ember: "rebuild the appframework… support people to make apps that
don't just EXERCISE dregg primitives but actively EXEMPLIFY, ELEVATE, and SUBLIMATE
the deosic ambitions." This doc is the honest census of what's missing + the deos
app model + the rebuild plan. Companion: `DEOS.md`, `REHYDRATABLE-SURFACES.md`,
`PG-DREGG-VS-DBOS.md`.)*

## The gap census — what slipped through the cracks

1. **Proof-deep, product-thin.** We built an extraordinary verification substrate
   and almost nothing a person would open and *use for its own sake*. Every existing
   `starbridge-app` is a proof-of-ONE-primitive — disintegrated demos, not apps. The
   honest gap: nothing is *good as an app first, verified-secure second*.
2. **There is no deos app MODEL.** "App" currently means "a Rust crate poking dregg
   primitives." There is no answer to *what is a deos application as a shape*: a set
   of cells exposing affordances, rendered as surfaces, distributed across the
   web-of-cells, rehydratable, with agents (human or AI) as first-class users. The
   framework must DEFINE that shape and make it cheap.
3. **The interactive/real-time tempo gap.** dregg's tempo is "commit a verified turn."
   Games, live collaboration, and co-presence need a faster tempo (frames, presence,
   optimistic updates). The bridge exists in design — **optimistic local interaction +
   verified turns at trust boundaries** (the #169 proving-modality dial) — but no app
   realizes it. Until one does, deos is turn-paced, and "webby" is aspirational.
4. **The distributed-app gap.** Apps are single-cell / single-node. The web-of-cells
   vision (an app spanning federated cells, agents reacquiring sturdyrefs across the
   membrane) has *zero* app exemplifying it. Multiplayer / collaborative is the test.
5. **Agent-as-first-class-user is unbuilt.** deos is *agentic*, but the apps are
   human-or-toy. The deos-native shape: the affordance set IS an agent's attenuated
   action space, and AI agents are primary users negotiating across membranes. The
   swarm-orchestration app gestures at it; it is not the real thing.
6. **The pg-dregg / sdk-py / web-surface stack is uncomposed.** We just built pg-dregg
   (durable verified state), the SDKs (agent API), and the web-surface + rehydration +
   affordance stack (the deos UI). They are three good pieces that *do not yet compose
   into "the deos app stack."* The framework rebuild IS that composition.
7. **No builder dev-experience.** No `dregg new deos-app` scaffold, no affordance
   hot-loop, no "useful deos app in an afternoon." Adoption (the pug-handoff bar) needs it.

## The deos app model (what the rebuilt framework makes cheap)

A **deos app** is: a set of **cells** exposing **affordances** (cap-gated verified-turn
templates — `affordance.rs`) → rendered as **web surfaces** (`starbridge-web-surface`)
→ over **durable verified state** (`pg-dregg`: reads are free SQL, writes are verified
turns) → reached by **agents** (human or AI) through the **SDKs** (`sdk-py`/`sdk-ts`
`dregg.pg` + the affordance API) → distributed across the **web-of-cells** (federated,
sturdyref-linked) → **rehydratable** (frustum-snapshots: snapshot the app, a peer
re-expands their attenuated per-viewer view). The framework's job: compose those six
layers and scaffold one in an afternoon. The app builder writes *affordances + a
surface*; the framework wires the verified state, the SDK surface, the distribution,
and the rehydration.

**This is an EVOLUTION, not a rebuild — `dregg-app-framework` already has the bones.**
(Correcting an earlier mischaracterization: it is a rich ~13.6K-line axum framework,
not a primitive-call harness.) What EXISTS: `server` (AppServer + health/CORS/admin),
`middleware` (verifies dregg presentation proofs at the HTTP boundary), `authorizer`
(Bearer/**Capability**/Signed — the cap-gated request model), `cipherclerk` +
`EmbeddedExecutor` (agent signing + embedded turns), `dispute`'s **OptimisticSettlement**
(the optimistic-tempo primitive already lives here), `captp_server` + `discovery`
(the captp/nameservice distribution substrate), the `StarbridgeAppContext` +
`register(ctx)` app-registration model, and `webgen` (renders an app's slot/event
vocabulary to anti-drift JS constants). The deos ELEVATION wires the just-built deos
steel into those bones:
- `register(ctx)` → also register **affordances** (`CellAffordance` surfaces) + their
  caps, not just factories/inspectors.
- `webgen` → grows from "emit JS constants" to **render the affordance SURFACE** (the
  htmx-on-crack page that posts cap-gated affordance fires).
- `middleware`/`authorizer` → the affordance-fire gate is the same proof/cap check,
  pointed at the affordance's `required ⊆ held` (`is_attenuation`).
- `persistence`/`store` → AUGMENT with **pg-dregg** (durable verified state: reads are
  free SQL, writes are verified turns) where an app wants it.
- `dispute::OptimisticSettlement` → the **interactive-tempo bridge** (optimistic local
  + verified-at-boundary, #169) is partly here already; extend it to affordance fires.
- + wire in **rehydration / frustum-snapshots** (`starbridge-web-surface`) as a new
  framework capability (snapshot an app surface, a peer rehydrates their attenuated view).

## The forcing function, BUILT: a deos webgame (fog-of-war IS the membrane)

*(BUILT 2026-06-14. `starbridge-web-surface/src/game.rs` + `src/world.rs` +
`src/vision_predicate.rs` + `examples/{fog_of_war_demo,deos_world_demo}.rs`, on the
affordance + membrane + web-of-cells steel. Two runnable demos: `cargo run --example
fog_of_war_demo` (the tight 5×5 skirmish that isolates the no-peek keystone) and
`cargo run --example deos_world_demo` (the FULL world — terrain/line-of-sight, mixed
unit archetypes, objectives, a federated lobby, a full agent-vs-agent match, and the
membrane-negotiation spectator); both `--headless` exit 0. 95 lib tests + 4
integration green. Keystone tests: `no_peek_a_player_cannot_rehydrate_an_enemy_tile`
(the lattice/membrane axis), `no_peek_for_real_only_the_secret_holder_can_prove_vision`
(the PROOF-BACKED axis), `two_agents_play_a_full_match_to_a_decision_entirely_through_the_cap_gate`
(the agentic axis), and `a_player_cannot_grant_a_view_of_the_enemy_side` (the
no-peek carried to the negotiation layer).)*

The sharpest exemplar is a multiplayer game, because the deos novelty *is a game
mechanic made into a security property*. The game spans two boards on one engine: a
tight **5×5 skirmish** (`demo_skirmish`) that isolates the no-peek keystone, and a
**12×12 world** (`demo_world`) with terrain, mixed unit archetypes, objectives, and a
win condition. In both, **what a player can SEE is exactly what its caps authorize it
to rehydrate** — fog of war as a **cap-confinement property**, not a client-side
visibility flag:

- **Fog of war = the membrane's per-viewer projection** (`Board::project_for`), backed
  by a genuine **proof obligation** (`vision_predicate.rs`). In a normal game, "what
  you can see" is a rendering trick the client could cheat. Here, vision rides the REAL
  cap lattice on **three** axes:
  1. **Player identity = `AuthRequired::Custom { vk_hash }`** — two players' identities
     are *incomparable* (neither attenuates the other), so a tile gated to the enemy's
     identity is un-projectable by the genuine `is_attenuation` (the membrane mints NO
     projection — `Board::can_rehydrate_tile` → `Amplification`). This is the structural
     refusal.
  2. **The vision frustum = the real `fetch_allow`** allowlist of tiles a side's units
     illuminate (`SurfaceCapability::may_fetch` per tile). In the 12×12 world the
     frustum has genuine **shape**: `Terrain::Blocking`/`Impassable` tiles **occlude
     line-of-sight** (`Board::has_line_of_sight`, a supercover walk), so a unit's
     vision is a cone the terrain carves, not a uniform Chebyshev disc — a tile in
     range but behind a forest is provably fogged.
  3. **The PROOF axis — the `vk_hash` is EARNED, not inert.** The `vk_hash` is a real
     `canonical_predicate_vk` of a real vision *program* (the side's Ed25519 public key,
     domain-tagged), registered in a real `WitnessedPredicateRegistry` with a genuine
     `WitnessedPredicateVerifier` — **the same registry + dispatch the `dregg-turn`
     executor runs for `Authorization::Custom`**. To project a side's tiles you must
     **PRODUCE a proof the registry verifies** (an Ed25519 signature over the canonical
     turn-bound message), via the paired `WitnessProducer` (the producer⊣verifier
     adjunction). It is **fail-closed and EUF-CMA**: a player holding only its own side's
     secret literally *cannot construct* a verifying proof for the enemy's vision
     (`VisionGateError::NoSecretForSide`), and a forged proof (signed with the wrong
     key) is rejected by the real verifier. The keystone `no_peek_for_real_…` proves
     this; the demo's step (ii-b) narrates it live.

  So "**you provably cannot peek**" is no longer the lattice-incomparability pun alone
  (which left the `vk_hash` an inert tag) — it is a real proof obligation: *you cannot
  even prove the enemy's vision.* Fog of war stops being honor-system and becomes a
  confinement theorem with cryptographic teeth.
- **The world has a point.** Three capturable **objectives** (control points) and
  four unit **archetypes** (`UnitKind` — Scout/Soldier/Sensor/Commander, each with a
  distinct vision/movement profile) give the 12×12 board real texture and a win
  condition: hold a majority of objectives (**Domination**), capture the enemy
  **Commander** (**Decapitation**), or wipe out the enemy (**Annihilation**)
  — `Board::outcome` → `GameOver { winner, reason }`.
- **Moves + objective-captures = affordances** (cap-gated verified turns). A move is a
  real `CellAffordance` firing a real `Effect::SetField`; **claiming an objective** is
  a `capture:<obj>` affordance firing a real `Effect::EmitEvent` (a second genuine
  effect kind). → **anti-cheat is free**: an unauthorized fire (e.g. Red firing Blue's
  move, or Blue's objective capture) is a refused turn (`FireError::Unauthorized`), the
  SAME `is_attenuation` gate, in-band.
- **Multiplayer = the web-of-cells** (each player a cell; the board a shared cell; each
  objective a cell). `world::GameWorld::publish` publishes the board/players/objectives
  as real attested cells into a `WebOfCells`; `world::Lobby` hosts a **federation** of
  worlds, each independently addressable by `dregg://` ref (distinct seed bases, no
  cell collision). A peer reaches a world by a verified attested read, not by trusting
  a server.
- **Agents-as-players** (`AgentPlayer`) — an AI fires the SAME cap-gated affordances as
  a human; its action space IS its attenuated cap set, so it cannot cheat any more than
  a human can. An `AgentPolicy` (Aggressive / Objective / Scout) is the *brain* — it
  only **ranks within** the fixed cap-gated action set; a smarter brain does not get a
  bigger cage. `game::play_match` runs two agents to a win condition through the gate,
  every action a real fired affordance. *This* is "agentic desktop."
- **Spectating = the membrane as a NEGOTIATION surface** (the doc's GitHub-org-settings
  framing, `REHYDRATABLE-SURFACES.md` residual #1 — the negotiation UX, now steel).
  `world::MembraneNegotiation` lets a player **propose** an attenuated `SpectatorGrant`
  — watch-my-side / objectives-only-scoreboard / full-board-post-game — minted ONLY as
  a genuine `is_attenuation` of what the granter holds. The negotiation's
  who-proposes/who-refuses is structural: Blue **cannot** grant a view of Red's side
  (`NegotiationError::GranterLacksAuthority` — the no-peek, lifted to the grant layer);
  a full-board grant is refused mid-game (`GameStillLive` — "can't make a repo public
  while it has secrets"); a re-share chain A→B→C composes through the real
  `Membrane::reshare` (an amplifying forward is `ReshareWouldAmplify`). A
  `SpectatorSession` carries the `Rehydration` liveness-type (Live /
  ReplayedDeterministic / ReconstructedApproximate, DERIVED) and is fog-respecting (a
  scoreboard leaks no unit positions; a Blue-side session hides Red's units). The
  rehydratable frustum-snapshot (`Board::snapshot_for`) is the same property at the
  affordance-surface level.

The fog-of-war world EXERCISES every hard part (distribution across a federation,
agent-as-first-class-user playing to completion, rehydration + the membrane
negotiation) and EXEMPLIFIES deos (the security properties ARE the game mechanics). It
is "htmx on crack" you can play — and it is *secure by construction*.

**The two tiers of the vision proof (honest):** the proof obligation above is
**Tier A** — a genuine `WitnessedPredicateVerifier` whose `vk_hash =
canonical_predicate_vk(bytes)`, registered in the real registry, verifying a real
Ed25519 knowledge-of-secret proof, fail-closed, producer⊣verifier round-tripped. It is
sound (only the secret-holder can prove a side's vision; forgeries rejected) and needs
no circuit crate, so it lives in the standalone `starbridge-web-surface`. **Tier B** is
the *zero-knowledge* form: a `dregg-circuit` AIR for the vision predicate with a layered
`canonical_predicate_vk_v2(air_fingerprint, …)` hash, proven by plonky3 and verified by
the circuit-backed verifier the executor installs (a real STARK, not a signature). Tier
B **cannot** live in this crate — `dregg-cell` must not depend on `dregg-circuit` (the
design's own dependency-cycle rule, which is *why* the default registry ships
`NotYetWiredVerifier` fail-closed for the STARK kinds and the host upgrades them). The
obligation *shape* is identical between tiers (register a `Custom` verifier under a real
predicate-vk; produce/verify through the registry); Tier B is a swap of the verifier's
internal algebra (Ed25519 → STARK) + the vk recipe (`_vk` → `_vk_v2`), registered the
same way in a `dregg-turn` integration. (A Lean model of the vision AIR — the
`metatheory` circuit-from-Lean path — is the verified-construction route to Tier B.)

**What else remains WOOD (named, not papered):** the interactive/real-time tempo (#169
optimistic-local + verified-at-boundary) is not yet wired — the game is turn-paced;
and a fired `AffordanceIntent` (a move's `SetField`, an objective-capture's
`EmitEvent`) carries the REAL effect but handing it to a live `dregg_turn::TurnExecutor`
is the same inherited seam `affordance.rs` names (the game mirrors the effect onto its
own board model in the interim, exactly as `MockSurface` advances from a gated request).
The fog (proof-backed, terrain-occluded), the moves + objective-captures, the
heterogeneous units + win conditions, the federated web-of-cells distribution, the
agents (playing a full match), and the membrane-negotiation spectator are all the
genuine cap discipline today (Tier A).

## The plan (the HARDSWAP has since cleared — items 1-2 LANDED)

*(The 2026-06-14 "sequenced behind the rotation HARDSWAP" framing is history: the
cutover cleared the root workspace + `metatheory`, the tree is unified (one target),
and the app-framework rebuild is BUILT. Kept below with the built items relabeled.)*

- **DONE (standalone `starbridge-web-surface`):** the affordance + frustum-snapshot
  stack (`a9401bb9`) — the deos UI substrate — AND **the forcing-function webgame
  BUILT on it** (`game.rs` + `fog_of_war_demo.rs`): fog-of-war = the membrane's
  per-viewer projection, the no-peek keystone, moves = cap-gated affordances, an AI
  agent-player, and a fog-respecting spectator snapshot. This proves the deos thesis
  end-to-end (the security property IS the game mechanic) on the genuine cap discipline.
- **ALSO landed (standalone runnable app exemplars, each grounding a named census gap):**
  `starbridge-apps/` now carries 30 apps, all with READMEs, including three that directly
  exercise the distributed / multiplayer / durable axes the census named as unbuilt:
  `starbridge-apps/branch-stitch-multiplayer` (the distributed-Houyhnhnm flagship — two
  participants fork ONE shared verified object and stitch; the #4 distributed-app gap, also
  runnable via `cargo run -p starbridge-branch-stitch-multiplayer` per `DEOS-RUNS.md`),
  `starbridge-apps/tussle` (a verified joint-combat multiplayer match — two figures fight by
  posing their joints), and `starbridge-apps/vat` (a persistent, durable, forkable rented
  World — the durable-state / rehydratable-surface axis). These are runnable app crates in
  their own right; they are NOT yet re-expressed on `dregg-app-framework`'s composition
  (plan item 4). (`starbridge-apps/shared` is a browser helper library, not an app.)
- **Since the cutover landed:**
  1. **DONE — the app-framework IS the deos-app composition.** `app-framework/src/deos_app.rs`
     defines `DeosCell`/`DeosApp` wiring affordance surfaces over the `EmbeddedExecutor`,
     the web-of-cells publish, the rehydration seam, and the generated web component —
     with the cap∧state `GatedAffordance` rung (`src/affordance.rs`, the Rust twin of the
     Lean `Dregg2.Deos.GatedAffordance`). `DeosApp::register` registers the gated
     affordances + caps.
  2. **DONE (mechanism) — the live-`TurnExecutor` fire path is closed.**
     `DeosCell::fire_gated_through_executor` runs a real verified turn through the
     `EmbeddedExecutor` (exemplar: `app-framework/examples/deos_council_board.rs` +
     `app-framework/tests/deos_council_board.rs` — the `approve` button lights IFF caps AND state pass,
     a both-pass fire runs a real verified turn). Remaining forward: lift the fog-of-war
     game itself onto this path + pg-dregg durable state + the web-of-cells lobby, so the
     skirmish is a multi-node integrated deos app, not a single-process model.
  3. **OPEN — the #169 tempo dial for interactive** (optimistic local +
     verified-at-boundary) so the game is real-time, not turn-paced.
  4. **Re-express 1-2 existing apps** on the framework to prove the composition (the
     council board is the first integrated exemplar; the supply-chain / orchestration
     apps are next).
- **WOOD:** the seL4 compositor-PD + the libservo link (the real pixels).
