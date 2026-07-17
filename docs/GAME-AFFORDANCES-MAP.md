# Game Affordances — Preingest Map

*A self-contained orientation map of everything game-shaped in the dregg monorepo, written for
collaborators (h\input{GAME-AFFORDANCES-MAP.md}

uman and agent) who are about to spelunk. Every path, type, and function name below
is quoted from real code at HEAD (2026-07-16) — nothing is invented. Feed this file to your agents
before they touch the tree; it replaces the first ~200k tokens of blind exploration.*

**Maturity vocabulary used throughout** (the repo's own convention):
- **deployed** — installed on the real executor / light-client path, or live on the devnet box.
- **driven** — the deliverable IS a green integration test exercising the real path. Heavy
  prove/fold gates are usually a separate `#[ignore]` SLOW test (minutes+): run with `-- --ignored`.
- **scaffold / NAMED** — real code or a named residual, not yet on the driven path. The codebase
  *labels its own inadequacies*; trust the labels, and read `lib.rs` headers first — they carry the
  honest scope notes.

---

## 0. Orientation in sixty seconds

**The one sentence:** a dregg **turn** is the exercise of an attenuable, proof-carrying token over
owned state, leaving a **receipt** — and a game move is just a turn, so **every move is a receipt**.

An illegal move doesn't get caught after the fact: it has *no satisfying witness* and is refused by
the executor (`spween_dregg::WorldError::Refused`) committing nothing. A finished match can fold to
ONE succinct STARK proof that a light client accepts in O(1), storing no moves — so you can rank a
win on a leaderboard without ever revealing your strategy.

**Repo shape:** one Cargo workspace at the monorepo root (edition 2024, `resolver = "3"`). The
game-relevant clusters:

| Cluster | Crates |
|---|---|
| Substrate | `spween-dregg` (WorldCell), `cell`/`turn`/`types`, `app-framework`, `dregg-schema`, `game-turn-slice`, `dice`, `ugc-dregg`, `procgen-dregg` |
| The three games | `dungeon-on-dregg`+`attested-dm`+`dreggnet-adventure` (The Descent), `dregg-multiway-tug`, `dregg-automatafl` |
| RPG feature engine | `dreggnet-{asset,party,quest,faction,craft,gear,companion,cheevo,trade,guild,tavern,saga,market,names}` |
| Surfaces & hosting | `dreggnet-offerings`, `dreggnet-surfaces`, `deos-view`, `dreggnet-web`, `dreggnet-telegram`, `dreggnet-wechat`, `discord-bot`, `dreggnet-sprite` |
| Proof spine | `circuit`, `circuit-prove`, `lightclient`, `dreggnet-game-board`, `dreggnet-prove-service` |
| Governance | `collective-choice`, `dregg-governance`, `dreggnet-council`, `dregg-interchain-gov`, `dregg-pay`, `dregg-season` |

Caveat for external agents: some crates are workspace members but **not default-members** (they pull
heavy graphs — gpui, SpiderMonkey). `cargo test -p <crate>` works; `cargo test` at the root won't
reach them. Notable: `dreggnet-adventure`, `dreggnet-saga`, `dreggnet-tavern`.

---

## 1. The one architecture idea: two rule-enforcement idioms

Every game rule is enforced at one of two tiers. Choosing the right tier per rule is *the* design
decision (this was an explicit, hard-won architecture correction):

**(a) StateConstraint teeth — for simple per-state predicates.** The tooth ISA lives at
`cell/src/program/types.rs`: `CellProgram { None, Predicate(Vec<StateConstraint>),
Cases(Vec<TransitionCase>), Circuit{..} }` with guards (`MethodIs`, `SlotChanged`, `AnyOf`, …) and a
~30-variant `StateConstraint` enum (`types.rs:970`): `FieldEquals/FieldGte/FieldLte/SumEquals`
(static), `FieldLteField/FieldLteOther` (cross-slot), `WriteOnce/Immutable/Monotonic/
StrictMonotonic/FieldDelta/SumEqualsAcross` (transition), temporal gates, and `ObservedFieldEquals`
(cross-CELL). The executor re-checks these on every turn — cheap, no proving needed. Use for:
bounded stats, monotone resources, write-once identity/permadeath, conservation, phase discipline.

**(b) Custom VK / custom AIR leaf — for whole transition functions.** When the rule is
`new == f(old, moves)` and no fixed tooth expresses `f`, author a custom AIR gated by
`StateConstraint::Custom`, translation-validation style: an untrusted oracle computes the next
state off-circuit; the AIR re-checks it. The binding ABI is
`circuit/src/effect_vm/custom_state_binding.rs` — a custom proof's public-input prefix
(`pis[0..8]` = PRE-state commit, `pis[8..16]` = POST-state commit, via `custom_pi_state_prefix`)
must equal the turn's real state commitments. Current resolution, honestly: the **executor-side
tooth is deployed fail-closed** (`TurnExecutor::enforce_custom_proof_state_binding` runs before
any leg verify commits — a sub-proof about a different pre-state/cell is refused); the
**in-circuit fold leg** (`prove_custom_leaf_with_state_commitment` +
`prove_custom_binding_node_state_segmented`) is built and both-polarity-tested, and routing it
through the chain fold plus discharging the welded-twin/umem residual and the Lean `proofBind`
flip is an **active in-flight lane** (see `docs/EXCELLENCE-BACKLOG-2026-07-16.md` §3 — this
cluster is the deep end of the pool; coordinate before touching anything under `circuit-prove/`).

**The exemplar to copy is `dregg-automatafl`** (see §3): `reference.rs` oracle + `air.rs` gates +
`Builder::air_accepts` as the fast shadow, with the real prove/fold as the `#[ignore]` gate. Its
AIR is deliberately HASH-free/Merkle-free/Lookup-free — the recipe that dodges every
custom-leaf-adapter residual.

**Never touch:** `custom_state_binding.rs` (the ABI), `turn/src/executor/` internals, the fold
connectors, the light client. Those are the platform floor. You author schemas, offerings, AIRs,
and feature crates *on top*.

---

## 2. The substrate — what you build on

### `dregg-schema` — declare components, get a verified game (deployed)
The keystone front-end. You declare state as intent via five archetypes
(`dregg-schema/src/schema.rs`: `Archetype { Stat{min,max}, Resource, Identity, Invariant{other,
delta}, Collection }`, fluent `Schema` builders) and the crate lowers it through a
translation-validated allocator (`layout.rs`: `allocate() -> Layout`, then `CheckedLayout::new`
enforces the decidable `Legal` disjoint+in-bounds obligation — an ill-aligned layout is
*unconstructable*) to a generated `CellProgram::Cases` (`emit.rs`: Stat→`FieldGte+FieldLte`,
Resource→`Monotonic`, Identity→`WriteOnce`, Invariant→`FieldLteOther`, Collection→heap-atom teeth;
default-deny on unknown methods) deployed on a real `WorldCell` (`game.rs`: `SchemaGame::deploy`,
`Turn` builder `.set(component, value).commit() -> Result<TurnReceipt, GameError>`). Worked
example: `dregg-schema/src/lib.rs:65 descent_schema()`. **You never hand-write a StateConstraint,
slot index, or heap key.** Driven: `dregg-schema/tests/allocator.rs`, `tests/refinement.rs` (fast, non-vacuous).

### `spween-dregg` — the WorldCell everything runs on (deployed)
`spween-dregg/src/world.rs: WorldCell` — `deploy_compiled(story, seed)` (`:168`),
`apply_raw(method, effects) -> Result<TurnReceipt, WorldError>` (`:472`), `snapshot()`,
`read_heap(key)`. 16 state slots (`compiler.rs:134`). Also the spween narrative-choice DSL, its
scene→`CellProgram` compiler, replay `verify`/`verify_chain_linkage`, the `Driver`, and the
collective-vote branch loop (§6). The underlying executor (`turn/`, crate `dregg-turn`) is the
legacy dregg1 Rust executor, load-bearing, mid-swap to a verified Lean executor behind a
differential shadow (`DREGG_LEAN_SHADOW=1`) — you don't touch it.

### `game-turn-slice` — the teeth→circuit compiler (driven)
Bridges the two-language gap between executor teeth and the recursion-foldable circuit DSL.
`game-turn-slice/src/compiler.rs: GameProgramCompiler` (`lower_state_constraint`,
`SlotAssignment`, `witness`, `finish`). Algebraic teeth lower to single polynomials; ordering teeth
(`FieldGte/Monotonic/…`) lower through a real **bit-decomposition range gadget** (never a refused
`Lookup`). Fast gate: `game-turn-slice/tests/game_program_compiler.rs::compiler_lowering_table` (always runs);
whole-program leaf + fold + `verify_history` accept/reject is the `#[ignore]` battery.

### `dice` — verifiable randomness (driven, real drand interop)
`dice/src/event.rs: EventId::derive` (domain-separated, binds game/sequence/pre-state/action/
purpose/draw_count); `source.rs: trait RandomnessSource` with `Deterministic`, `CommitReveal`,
`MockBeacon`, `ServerVrf` (post-quantum LB-VRF), `Hybrid`, and `trait Beacon` incl. the production
`DrandBeacon` (real threshold drand-BLS `quicknet`, pairing-verified, interop-tested against a
published vector); `draw.rs: DrawStream::draw_bounded` (unbiased, reject-free). The `lib.rs` header
honestly maps which source closes which grindability escape. Named residual: a live drand
round-fetch HTTP client (verification done, network fetch not).

### `ugc-dregg` — the no-cheat currency (driven)
Content-addressed `Universe`/`UniverseId` (published, ed25519-attributed) and
`Completion`/`verify_completion` — a completion is accepted only if it *re-executes* to the
declared `WinCondition`. The `Completion` object is the currency that flows quest→cheevo→guild
(§4). `procgen-dregg` feeds it: `daily_seed`/`generate`/`verify_generation`, beacon-seeded daily
dungeons.

### `dreggnet-game-board` + `dreggnet-prove-service` — match → one proof → leaderboard (driven / scaffold)
`dreggnet-game-board/src/lib.rs`: leg 1 lowers a played match to foldable leaves (`TugMatch::leaves`
via `membership_leaf_for_play`; `AutomataflMatch::leaves` via `build_d1_honest`; `win_leaf` uses the
range gadget); leg 2 `prove_match -> MatchProof` folds via `prove_turn_chain_recursive` and
SELF-ATTESTS through `dregg_lightclient::verify_history_bytes`; leg 3 `GameBoard::submit` verifies
O(1) and ranks — `stores_no_moves()` is the private-strategy property; leg 4 `ProvingService`
queues the slow fold on a background worker. The full crown is `tests/end_to_end.rs` (`#[ignore]`
SLOW). `dreggnet-prove-service` generalizes leg 4 (bounded queue, N workers, GPU dispatch with
bit-exact CPU fallback) — scaffold, not on the live play path: **the live demo verifies by REPLAY,
not STARK**; the portable proof is the labeled Phase-3 upgrade.

---

## 3. The three shipped games (the exemplars)

### The Descent — flagship roguelite (deployed + driven)
Four crates compose:
- **`dungeon-on-dregg`** — the playable dungeon: `scene()`/`compiled()`/`deploy(seed)` plus a
  larger `keep_scene()` world; `descend_gate_constraints()` is the executor-enforced descent gate.
  Modules for combat, dice-combat, loot, progression, skills/spells, overworld, dialogue,
  multicell, mud, meta. 10 runnable examples (`examples/descend.rs` is the canonical driver:
  legal receipt chain + refused illegal descent).
- **`attested-dm`** — the un-jailbreakable AI DM: `DmAttestationCarrier::attest_body ->
  ZkOracleAttestation` proves each narration turn authentic + well-formed + injection-free; a
  player prompt-injection reflected into the narration is *caught* and the DM's turn refused.
  Real MPC-TLS leg is behind `tlsn-live`; default is the modeled carrier (labeled).
- **`dreggnet-offerings/src/daily_descent.rs: DailyDescentOffering`** — the daily, provably-fair,
  permadeath run: drand-seeded daily world, persistent hardcore `Character`, no-cheat leaderboard
  via `verify_completion`.
- **`dreggnet-adventure`** — the integration proof (single 1563-line `lib.rs`): one
  `PlayerIdentity`, gear+companion loadout gating cross-cell, faction-gated quest, ONE `Completion`
  feeding cheevo+guild+quest turn-in, loot→craft→trade as the same note. `cargo test -p
  dreggnet-adventure`.

### multiway-tug — verified card game with a zk hidden hand (driven)
`dregg-multiway-tug`: 2-player tug over seven guilds (influence `[2,2,2,3,3,4,5]`, 21 total; four
once-per-round actions; win ≥11 influence or ≥4 guilds). Phase 0 rules are pure teeth
(`SumEquals==21` conservation, `WriteOnce` one-action-per-round, `Monotonic` placements,
default-deny) — see `dregg-multiway-tug/tests/round.rs` (8 named non-vacuous tests). Phase 2 is the **zk hidden
hand**: `hidden_hand.rs: HandTree::commit` (depth-2 Poseidon2 Merkle), `prove_play(card_id) ->
PlayProof` — prove a legal play revealing nothing; a fabricated card has no leaf. Phase 3
`fold.rs` lowers plays into leaf bundles → one `WholeChainProof` (whole-match fold is `#[ignore]`
SLOW). Phase 1 packs (`packs.rs`) and Phase 5 offering (`surface.rs: TugOffering`, per-player fog)
are built. Open: Phase 4 Lean refinement.

### automatafl — the Custom-VK exemplar (driven; copy this to build a complex game)
`dregg-automatafl`: simultaneous-move cellular-automaton boardgame (n=2, 5×5). `reference.rs:
apply_turn` is the off-circuit oracle; `air.rs` staged builders `build_d1/d2/d3/build_sealed`
(+`_honest` witnesses); `builder.rs: Builder::air_accepts` is the fast refinement shadow;
`game.rs: AutomataflGame` deploys the same match on a real WorldCell with a commit→reveal→resolve
tooth discipline (idioms (a) and (b) in one game); `surface.rs: AutomataflOffering` renders the
board as a `ViewNode::CoordGrid` with legal-move highlighting and sealed-move fog. Lean spec:
`metatheory/Dregg2/Games/Automatafl.lean` (pure `applyTurn`, invariants proven no-sorry; the
concrete Rust-AIR↔Lean `Refines` tie is the open leg). Real leaf→fold→light-client-accept:
`tests/prove_fold.rs` (`#[ignore]` SLOW).

**Game-adjacent extras** (one line each): `mud-dregg` — multiplayer MUD where divergent player
timelines are branch-stitched configs (playable binary); `interactive-fiction-demo` — crowd-voted
spween story × mud timelines × attested DM in one binary; `narrator` — hosted narrator (Bedrock/
Ollama/Scripted fallback) behind a hard $20 spend ceiling; `dreggnet-tournament` — verifiable
single-elimination bracket; `rbg` — not a game (userspace directory/VFS primitives).

---

## 4. The RPG feature engine — ten crates + the composition proof

Each crate is an **additive** layer consuming the substrate, modifying nothing beneath. The base is
**`dreggnet-asset`**: owned, transfer-gated, provenance-chained, content-addressed asset cells
(`AssetWorld::{mint, mint_soulbound, transfer, attempt_respend, verify_provenance, revoke}`,
`AssetId([u8;32])`) — ownership IS the signature gate; a double-spend is refused; lineage replays.

| Crate | Affordance (all driven green unless noted) |
|---|---|
| `dreggnet-party` | Seats-with-roles co-op: `Party::muster/act_in_role` (acting outside your seat = real refusal), quorum fork-votes (`PartyFork` on the real vote engine), shared focus pool, `WriteOnce` loot split |
| `dreggnet-quest` | Order-gated multi-step objectives (`WriteOnce` step flags + `BoundedBy` ordering + `FieldGte` turn-in); `verify_quest` replays; faction-gated giver |
| `dreggnet-faction` | `Monotonic` reputation slots, `FieldGte` content unlock, `WriteOnce` betrayal seal, rival cap via `FieldLteOther`; JSON standing persistence |
| `dreggnet-craft` | Provably-fair forge: verified quality draw off a committed seed; inputs genuinely SPENT (the economy's first sink); outputs carry a real `StatBlock` |
| `dreggnet-gear` | Equip gates a run ability cross-cell via `ObservedFieldEquals` (kernel predicate, not a client `if`); echoes-bought class talents — no-P2W by construction |
| `dreggnet-companion` | Owned asset fused with a leveling cell (real XP story + hardcore permadeath); level-gated buffs fail-closed; breeding spends both parents; escrow swaps |
| `dreggnet-cheevo` | Achievement = anchored predicate over a VERIFIED run; mints a SOULBOUND asset; laundering fails reverification |
| `dreggnet-trade` | Scam-proof atomic swap: asset transfer bound to `SealedEscrow` legs; settle crosses both or depositor made whole; provenance travels |
| `dreggnet-guild` | Membership = capability set; leaderboard sums only verified clears; escrow treasury (**no officer can abscond**); quorum-elected officers |
| `dreggnet-tavern` | Persistent multiplayer hub over the live node wire (SSE); un-spoofable presence; heavyweight (pulls `dregg-node`), thinner scope, residuals named |
| `dreggnet-market` / `dreggnet-names` | Offering-abstraction proofs: sealed-bid auction clearing through Σδ=0 verified settlement; first-claim nameservice |

**`dreggnet-saga` is the composition proof** — the tests to read first: one `Completion` object
verified identically by quest, cheevo, and guild; one crafted note whose provenance lineage
CONTINUES through escrow to the buyer (no re-mint); one `PlayerIdentity` deriving party-seat ballot
key + guild member + asset holder. Object identity, not name-convention look-alikes.

**The nine idioms a new feature crate follows** (this is the pattern language):
1. Consume, never modify — path-dep the substrate; record reconciliation wants as named follow-ups.
2. Every affordance is a kernel tooth, never host-side bookkeeping.
3. Cross-cell gates via `ObservedFieldEquals` + a `WitnessBlob` Merkle-open; **fail-closed** on a
   stripped witness.
4. Ownership = the signature gate; owned things are `dreggnet-asset` notes; soulbound = no
   transfer path; content-address the id.
5. Value moves through escrow (`open/deposit/settle/reclaim`; reclaim only to the depositor).
6. Collective decisions through `collective-choice` (Ineligible / BadSignature / DoubleVote).
7. No-cheat = replay (`verify_completion`); never trust a self-reported count.
8. Non-vacuous tests: every gate gets an honest-commit leg AND a refused-forgery leg, plus an
   anti-ghost assertion that refused state didn't leak.
9. Render via `Offering`/`ViewNode` so every frontend paints for free (§5).

---

## 5. How a player actually plays — surfaces + deploy

**The hosting abstraction** is `dreggnet-offerings/src/lib.rs:446 trait Offering`: associated
`Session`; `open / actions / advance(Action, DreggIdentity) -> Outcome / verify / render ->
Surface / price`. `Surface(pub deos_view::ViewNode)` — every frontend is a renderer of this one
tree. `Outcome::{Landed{receipt,..}, Refused}` is the anti-ghost shape. `render_for(viewer)` /
`advance_collective` are the hidden-hand and crowd-play hooks. `OfferingHost` (`src/host.rs:263`)
is the keyed registry with session-resume (a tampered move log fails to reopen).

**Render once, play everywhere:** the `ViewNode` enum (`deos-view/src/tree.rs:25` — VStack, Row,
Text, Button{label,turn,arg}, Table, Menu, Gauge, CoordGrid…) renders through real backends:
`text.rs: render_text`, `web.rs: render_html`, `discord.rs: render_card`, `telegram.rs`,
`wechat.rs`. `dreggnet-surfaces::register_surfaces(host)` mounts eight feature surfaces in one
call; `dreggnet-surfaces/tests/golden_render.rs` asserts cross-backend invariants. `dreggnet-sprite` renders
deterministic asset→SVG (same asset ⇒ byte-identical SVG; rarity weights `[1000,420,150,40,6]`),
served at `/sprite/{kind}/{ref}` + `/gallery`.

**Identity, honestly:** on the offering path `Offering::advance(session, input, actor:
DreggIdentity)` treats the actor as *attribution metadata* — no signature is consumed; the turn
commits under the world's cap. Web derives the actor from a self-asserted cookie
(`blake3(dregg_user)`), the chat adapters derive real ed25519 cipherclerks but custodially (the
adapter's secret → every user's key) and use only the pubkey for attribution. The one place
identity binds cryptographically today is `dreggnet-party` (seat custody keys + `AuthRequired`
caps + signed ballots) — that's the pattern the platform intends to spread; the passkey seam is
named in code at `dreggnet-offerings/src/session.rs` (`Custodian::identity_for`). The executor
always referees *legality*; the open work is refereeing *attribution* (see the closure ledger).

**The minimal path to a new playable game surface** (all pieces exist):
1. Implement `Offering` for your game; build `render` from the shared builders in
   `dreggnet-surfaces/src/lib.rs:88` (`section`, `menu`, `action_menu`, …).
2. Register one line in `dreggnet-web/src/lib.rs::catalog_default_host` (see `tug` / `automatafl`
   there as the model).
3. It's live at `/offerings/{yourkey}/session/{id}`, verifiable at `.../verify` — no per-frontend
   code.
4. Ship: `deploy/games/deploy-hbox.sh --funnel` (build → snapshot → install → health-check →
   auto-revert), then the ember-gated `tailscale funnel` flip.

**What runs live today** (probed 2026-07-16: `/health` ok, `/offerings` 200):
`https://hbox-dregg.skunk-emperor.ts.net` — Tailscale Funnel →
`dreggnet-web-server` as a lingering systemd user unit on hbox (`deploy/games/
dregg-web-games-funnel.service`, loopback `:8790`). Catalog at `/offerings` (dungeon, council,
market, tug, automatafl + feature surfaces); Descent board at `/descent/leaderboard` (durable
sqlite, re-verified by replay on boot). `RUNBOOK-FUNNEL.md` is the real runbook; `RUNBOOK.md`
(AWS gateway) is explicitly marked aspirational.

---

## 6. The governance thread — a game is a little DAO

The thesis, stated in code (`interactive-fiction-demo/src/lib.rs:29`): *the crowd-vote that picks a
story branch is the same kind of collective decision that governs the polity.* Game modes call the
SAME engine the federation calls — the analogy is literal.

**The engine: `collective-choice`** (the most mature crate in the thread; Lean mirror
`metatheory/Dregg2/Apps/MultisigVote.lean`). One `EmbeddedExecutor` hosts every poll/ballot/tally
as verified turns: one-vote-per-ballot (`WriteOnce` VOTE slot on a factory-born ballot cell),
monotone tally (replay can never shrink the board), an in-cell `AffineLe` quorum gate guarding
`RESOLVED`, non-amplifying liquid delegation (`Mandate::sub_delegate`; delegated authority ⊆
granted), and a nullifier set — one-vote defence at three independent depths. Fresh as of
`bc512214f` (2026-07-16): **weighted voting on the verified engine** — `cast_weighted(poll,
ballot, option, weight)` bumps the tally by exactly the granted weight under the same one-ballot
gates (a whale is one nullifier, never W ballots); zero-weight refused before burning the ballot;
the host-side `HostBallotBox` is demoted to a compat shim — new flows go through
`dregg-governance::VerifiedHoldingBallotBox`.

**DAO concept → dregg primitive:**

| DAO concept | Real path |
|---|---|
| Seats / members | `dreggnet-party` `Seat` ed25519 custody keypair = ballot identity; guild membership = minted member cell whose caps ARE its rights |
| Verified ballots | `BallotCap` single-use; double-vote refused three ways; forged sig = `BadSignature`, non-member = `Ineligible` |
| Token voting | `cast_weighted` + proof-of-holdings (`dregg-governance/src/holding_weight.rs`: Lean-proven `grantWeightCore` verdict, consume-once nullifier per (poll, holder, asset) — defeats flash-loan re-vote), non-custodial: a read proof of your own wallet, never a lock |
| Quorum / enactment | The `AffineLe` gate is the referee — below quorum nothing enacts; same gate in party forks, guild elections, council enacts, liquidity votes |
| Treasury | `GuildTreasury` over `SealedEscrow` (reclaim only to depositor — no officer absconds); treasury *actions* require a passed vote (`dregg-pay/src/governance.rs: LiquidityGovernance` — only a passed vote yields the `SwapAuthorization`) |
| Auditability | Every cast is a `TurnReceipt`; `verify_collective_certified` proves the shown outcome equals what the crowd chose |
| Cross-chain constituency | `dregg-interchain-gov` joins Solana/EVM/Cosmos holdings into one tally (chain tags pinned at compile time; fixtures-driven, no live consensus ingested yet) |

**Governance as a playable surface:** `dreggnet-council` hosts propose→vote→enact as an Offering —
the same trait that hosts a dungeon; "a jailbroken narration cannot move the treasury; only a
passed vote can."

**Token posture** (canonical: `docs/TOKENOMICS.md`): $DREGG buys SERVICES, never power, never
yield; governance weight comes from proven holdings at a snapshot, no staking/locking; no burn, no
P2E — leaderboard reward is glory. Seasons (`dregg-season`) are the temporal unit protocol-upgrade
votes punctuate. Honest scope: the rails RUN on mock/fixture chains; no live mainnet holding or
real $DREGG payment has been exercised yet.

---

## 7. Starter projects (scoped for modest budgets)

Builder-side (each lands with existing tests as the model):
1. **A new small game as an Offering** — declare state with `dregg-schema`, rules as teeth, render
   via the shared builders, register in `catalog_default_host`. Smallest full-stack path; copy
   `dregg-multiway-tug` Phase 0 + `surface.rs`. (The board node already exists:
   `ViewNode::CoordGrid` renders in every backend, styled on web.)
2. **A new feature crate** following the nine idioms (§4) — e.g. bounties, arenas, housing; the
   saga tests show the handoff discipline to prove.
3. **Live channel transport** — `dreggnet-telegram`/`-wechat` are driven against `MockTransport`;
   a long-poll loop binary + a deploy unit + a real token turns either live (token custody is the
   only ember-gated step).
4. **`<dregg-sprite>` wasm custom element** (named E3 in `dreggnet-sprite/src/lib.rs:44`).
5. **The drand round-fetch HTTP client** — `dice` verifies real drand `quicknet` signatures
   already; the network fetch is the one missing piece (one small client + the existing
   `verify_beacon_round`).

Crypto/governance-side:
6. **New `DecisionRule` shapes** — ranked / quadratic tallies over the same `Monotonic` slots +
   nullifier discipline in `collective-choice`.
7. **A game mode that IS a governance mode** — e.g. a faction senate where standing
   (`dreggnet-faction`) grants weighted ballots via `cast_weighted`; every primitive exists.
8. **Weighted council votes** — `dreggnet-council` opens plain polls today; exposing
   `open_poll_weighted`/`cast_weighted` through the same Offering makes holdings-weighted
   governance *playable*.

---

## 8. The closure ledger (every known limit, with its status)

The codebase labels its own inadequacies; this table is the game-lane view of that ledger. Statuses:
**CLOSED** (landed at HEAD), **IN-FLIGHT** (a lane is actively driving it), **DESIGNED** (the plan
is written; execution is scheduled), **NAMED** (tracked, not yet designed).

| Limit | Status |
|---|---|
| Board-grid rendering | **CLOSED** — `ViewNode::CoordGrid` renders in text/discord/web (styled game board, `deos-view/src/web.rs:1956`); tug + automatafl offerings registered with per-viewer fog |
| Solana value-path suspects (finality / stake completeness / rotation binding) | **CLOSED** (`72561117d`, red-first both polarities) + rung-1 live-feed ingestion landed (real SPL over live RPC on a local validator) |
| Ephemeral web sessions | **CLOSED** — `DREGGNET_WEB_SESSION_DIR` welds `FileResumeStore` into the web boot path: per-session move-log write-through, boot resume by replay, tampered log refuses to reopen (evidence kept). Driven both polarities through the real router across a simulated restart |
| Custom-VK state binding (the path complex mechanics ride) | **IN-FLIGHT** — executor tooth deployed fail-closed; the state-segmented fold node is routed in the active lane; welded-twin/umem residual + Lean `proofBind` flip remain (coordinate before touching `circuit-prove/`) |
| Anchoring node down (`:8420`) | **DESIGNED** — a lingering systemd user unit with a persistent `--data-dir` on hbox (`deploy/games/RUNBOOK-FUNNEL.md` TODO-1); one build (`swarm-build cargo build --release -p dregg-node`) + one ember decision (fresh genesis = a new season — honest devnet churn is a feature, and `dregg-epoch`/`dregg-genesis-snapshot` are the boundary tools) |
| Replay-verify (not STARK) on the live play path | **DESIGNED** — labeled Phase 3: submit enqueues into `dreggnet-prove-service::MatchProveService` (bounded queue, GPU dispatch, bit-exact CPU fallback); the board keeps replay as fast admission and upgrades entries to proof-backed when the `MatchProof` lands + `verify_history_bytes` re-attests |
| Telegram/WeChat live; Discord off the AWS edge | **DESIGNED** — transports are injected and driven vs mocks; live = token + loop binary + unit (starter #3); the bot's `/offering` adapter carries every surface once moved |
| Mainnet holdings feed | **DESIGNED** — the `SnapshotFeed` design (what a snapshot provides that RPC structurally cannot) is written in the `dregg-governance` module doc; rung-1 proved the pipeline on a live local validator |
| Player identity signs nothing (web = self-asserted cookie; adapters = custodial keys, attribution-only) | **rung 1 CLOSED** (`6fa643d05`) — `dreggnet-offerings/src/signed.rs`: `Attribution{Signed\|Asserted}` makes trust visible; `SignedAction` + `OfferingHost::advance_signed` verify strict ed25519 over a pinned canonical message with replay-protected counters; `SessionKey` grants bind to a holder pubkey; resume logs carry provenance wire-compatibly. **Rung 2 open**: put the secret on the player's device (cipherclerk-in-wasm / WebAuthn) and wire the surfaces through `advance_signed`. Backlog G1 |
| Unbounded session minting + no throttling (web AND bot — same disease twice) | **host-layer CLOSED** (`295b7f73d`) — `SessionPolicy` (quota/rate/TTL/LRU) lives ONCE in `OfferingHost`; lazy resume-on-touch makes it a working-set model over the durable store; signed-counter floors persist merge-max so eviction/restart can never reset replay protection; web wired (429/409, env-driven). Open: port the bot's `Store` + the legacy `WebState` surface onto the policied host. Backlog G2 |
| `/descent` pinned-drand fallback (same dungeon absent egress) | **NAMED** — label staleness in the surface or fail-closed to the last verified live round; alert when stale >1 day. Backlog G3 |
| Generic collective close (crowd mode beyond `/dungeon`) | **NAMED (CHEAP)** — the machinery is driven, `#[allow(dead_code)]`; register the close affordance. Backlog G5 |
| Forge/`.dungeon` authoring for the DEPLOYED substrate | **core CLOSED** (`1dd8a566b`) — `dungeon-on-dregg/src/dsl/`: ported parser+validator + the `compile_world` lowering with biconditional translation validation (dropped tooth = MISSING, injected = PHANTOM, never returned on failure); driven on the real executor both polarities. Open plumbing: `/author`+`/validate` on the real service, forge front-end repoint, funnel wiring; unsupported constructs (combat/spell/consumable/light/lose) refuse by name — each has a proven executor idiom in-crate awaiting wiring. Backlog G7 |
| automatafl Rust-AIR↔Lean `Refines`; multiway-tug Phase 4 (Lean refinement) | **NAMED** — the Lean specs exist (`Automatafl.lean` proven no-sorry at spec level; `MultiwayTug.lean`); tying the concrete AIRs to them is the open proof lane |
| `attested-dm` real MPC-TLS leg (`tlsn-live`) | **NAMED** — the modeled carrier is the labeled default; the real carrier is the standing cross-cutting frontier lane (shared with the whole zkOracle stack, not game-specific) |
| Discord payments watcher | **NAMED** — the bot's pay path constructs a `MockWatcher` unconditionally (`discord-bot/src/pay.rs:445`); the PAYMENTS-GO-LIVE runbook is written, unfired |

---

## 9. The doc shelf (fresh as of the 2026-07-16 docs campaign)

`docs/GAMES-AS-RECEIPTS.md` (the philosophy) · `docs/VERIFIED-GAME-PORTFOLIO.md` (the three games)
· `docs/GAME-STRATEGY.md` (the schema archetypes) · `docs/GAME-ROLEPLAY-STACK-MAP.md` (the RPG
crates) · `docs/GAME-ENGINE-ROADMAP.md` + `docs/GAME-INFRA-ROADMAP.md` (what's next) ·
`docs/AUTOMATAFL-N2-DESIGN.md` (the Custom-VK exemplar's design) · `docs/DESIGN-verifiable-game.md`
+ `docs/DESIGN-dregg-dice.md` (randomness) · `docs/FRONTEND-PLAN.md` (surfaces) ·
`docs/CONTENT-AND-ASSET-SPEC.md` (assets/sprites) · `docs/TOKENOMICS.md` (the canonical token
answer) · `docs/DEVNET-UPGRADE-AND-TREASURY-DIRECTIONS.md` (seasons/treasury).

*Read `lib.rs` headers first, trust the maturity labels, and run the named tests before believing
any claim — including this map's.*
