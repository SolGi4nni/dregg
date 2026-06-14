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

## The forcing function: a deos webgame (fog-of-war IS the membrane)

The sharpest exemplar is a multiplayer game, because the deos novelty *is a game
mechanic made into a security property*:

- **Fog of war = the membrane's per-viewer projection.** In a normal game, "what you
  can see" is a rendering trick the client could cheat. In deos, what an agent can see
  is *what its caps authorize it to rehydrate* — the membrane will not project the
  enemy's hidden state to you, and the rehydration is cap-gated + verified, so
  **you provably cannot peek**. Fog of war stops being client-side honor-system and
  becomes a confinement theorem.
- **Moves = affordances** (cap-gated verified turns) → **anti-cheat is free** (an
  illegal move is a refused turn; the witness-graph records who did what).
- **Multiplayer = the web-of-cells** (each player a cell; the board a shared cell;
  federation is the lobby).
- **Agents-as-players** — AI opponents/allies are first-class users firing the same
  affordances, attenuated by the same caps. *This* is "agentic desktop."
- **Spectating = rehydratable frustum-snapshots** — share a snapshot; a spectator
  rehydrates a *fog-of-war-respecting* view (they see only what their spectator-cap
  authorizes), and the liveness-type tells them live-vs-replay.

A fog-of-war strategy game (or a hidden-information card game) is the smallest thing
that EXERCISES every hard part (interactive tempo, distribution, agent-as-user,
rehydration) and EXEMPLIFIES deos (the security properties ARE the game mechanics).
It is "htmx on crack" you can play.

## The plan (sequenced behind the HARDSWAP)

- **NOW (parallel, standalone `starbridge-web-surface`, disjoint from the deputy):**
  the affordance + frustum-snapshot stack (`a9401bb9`) — the deos UI substrate.
- **The instant the HARDSWAP clears the root workspace + `metatheory`:**
  1. **Rebuild the app-framework as the deos-app composition** (a `deos-app` crate /
     scaffold that wires cells×affordances + pg-dregg state + the sdk surface + the
     web-of-cells distribution + rehydration; `dregg new deos-app`).
  2. **Build the forcing-function webgame** (fog-of-war = membrane) end-to-end on it.
  3. **The #169 tempo dial for interactive** (optimistic local + verified-at-boundary)
     so the game is real-time, not turn-paced.
  4. **Re-express 1-2 existing apps** on the new framework to prove the composition
     (the supply-chain / orchestration apps become *integrated* deos apps).
- **WOOD:** the seL4 compositor-PD + the libservo link (the real pixels).

Why behind the HARDSWAP: `dregg-app-framework` is a root-workspace crate depending on
turn/cell/sdk — exactly what the deputy is rewriting — so rebuilding it now would
build against a moving target AND break the deputy's `cargo test --workspace` gauntlet.
Design now; build the instant the cutover lands.
