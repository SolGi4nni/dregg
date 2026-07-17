# The Attested Game Engine — Roadmap

**Vision:** a verifiable AI-game-master *platform*. An AI narrates rich adventures; the world
resolves every move by rules a stranger can check; randomness is provably fair; content is
authorable by anyone in text; and a full playthrough — its randomness and its rule-adherence —
is verifiable without trusting the server. "Single-player web3 that actually works," because the
rules are the referee.

Ordering principle: **leverage** — build the primitives that unlock the most downstream first,
and keep every capability *world-resolved* (the AI proposes; the world disposes) and *verifiable*.

> **Scope:** this is the `attested-dm` ENGINE roadmap. The shipping strategy of record is
> `docs/GAME-STRATEGY.md` — the portfolio ships on the DEPLOYED executor path only, never on
> this engine's own blake3 hash-chain ledger (a labeled toy relative to the deployed VK).

---

## Phase 0 — the hardened base ✅ (done)
The engine (`attested-dm`): closed typed-action resolution (`resolve_action`), a prev-linked
hash-chain ledger, capability-gating (`DmCaps`), input slot-confinement. Seven built-in worlds
(`arena_gauntlet` · `bramble_keep` · `deepdark_mine` · `loot_chest_demo` · `starfall_spire` ·
`sunken_vault` · `venom_deep`, exported from `attested-dm/src/lib.rs`) with distinct mechanics
(crawl · NPCs+combat · spellcasting · light-as-resource · tactical encounter). A readable `.dungeon`
DSL + a real validator (`parse_dungeon`/`validate`). The collective vote (`/party`). A hosted,
**hard-$20-metered** narrator (`dregg-narrator`, Claude Haiku 4.5 via Bedrock). The arcade +
authoring pages (`/hub /vault /party /author /forge`). **Hardened by a 4-lane correctness review.**

Honest gaps (the frontier, see Phase 3): the attestation's *authentic* leg is a fixture; the
in-circuit half of verifiable rule execution is open (`verify_ledger_replay` re-runs the resolver
off-circuit — see Phase 3).

## Phase 1 — depth + delight ✅ (done)
- **Consumables + status effects** — potions heal, elixirs buff, poison ticks; consumed, timed,
  world-resolved; DSL support (`ConsumableRule`/`ConsumableEffect` in `attested-dm/src/game.rs`:
  `Status` durations tick down per step, `Cure` clears them, the item is consumed by a
  `WorldEffect::ConsumeItem`). The seed of a combat engine.
- **Room-map visualizer + live-validating forge** — the dungeon graph + your position
  (`demo/roommap.ts`); authoring with line-pinned parse errors and full semantic issue lists
  surfaced as you type (`demo/forge.ts` — on any failure the previous world is torn down, never
  silently kept behind an error).

## Phase 2 — the high-leverage primitives ✅ (done)
- **Verifiable randomness** — the `dregg-dice` crate (`dice/`): provably-fair dice / loot / crits /
  procgen, and it lands PAST commit-reveal — `ServerVrf` is a real post-quantum LB-VRF (`pqvrf`,
  Esgin et al. Set I; uniqueness reduces to Module-SIS), alongside `MockBeacon` for tests. The
  crate's own docs state plainly that commit-reveal does not prevent selective abort.
- **Save/load persistence** — `attested-dm/src/savegame.rs`: `GameSession` ⇄ a portable `SaveGame`
  (JSON via serde) with a `world_fingerprint` pinning the static map and `dm_seed` pinning the
  modeled randomness; versioned wire format.
- **Overworld** — `attested-dm/src/overworld.rs`: a `Region` of named `Location`s (each a dungeon)
  joined by travel `Edge`s; a location is credited complete ONLY through
  `RegionProgress::record_completion`, so forged or tampered completion claims do not travel.

## Phase 3 — RPG systems + the trust frontier ⚔️
- **Combat engine** — the initiative-ordered tactical encounter core is built
  (`attested-dm/src/game.rs`: `EncounterRule`/`Combatant`/`Ability` — initiative order, multiple
  auto-acting foes, a closed ability set (strike / guard / cooldown special), deterministic
  targeting, verified damage draws; `arena_gauntlet` exercises it). A labeled FIRST slice: open are
  positioning/range, a richer action economy, interacting status stacks, and equipment modifiers.
- **Character progression** — xp, skills, classes (warrior/mage/rogue) with distinct action sets.
- **Verifiable rule execution** — the re-execution light client is built: `verify_ledger_replay`
  (`attested-dm/src/game.rs`) re-executes a ledger from genesis, re-runs `resolve_action` over the
  bound actions, and checks every recorded effect (trust-minimized). Open: the critical resolver
  invariants proven *in-circuit* via dregg's real `circuit`/fold machinery (trustless) —
  feasibility is scoped against what `circuit-prove` actually provides.

## Phase 4 — the platform flywheel 🌐
- **UGC community** — the `/forge` + library become a platform: publish, play, rate authored
  dungeons; **verifiable leaderboards + speedruns** (the receipt chain already proves a legit win).
- **Co-op party play** — multiple real players, each a character in one adventure (beyond voting).
- **Discord integration** — the dungeon commands are live in-tree
  (`discord-bot/src/commands/dungeon_offering.rs`, `descent.rs`, plus the generic `/offering`
  adapter in `offering.rs`); the `/descent` no-cheat leaderboard is persistence-backed —
  `SqliteDescentBoardStore` (`discord-bot/src/descent_board_store.rs`) survives restart and is
  re-verified by replay on boot. What remains here is channel save state.
- **Deepen the attestation** — fixture → real zk (prompt-faithful-to-template + no-omission proofs).

## Cross-cutting
Presentation (richer UI, animated map, ambient sound, TTS narration, a real client). Docs +
examples per capability. The teeth (world-resolves, chain, cap-gate, slot-confinement, anti-ghost)
audited whenever a mechanic is added.

---

## How we build — the multimodel workflow
- **Codex** (a different model = creative divergence) takes large open-ended **designs and builds**
  — architecture, ambitious systems, whole subsystems. Run via `codex exec` (read-only for design,
  workspace-write for builds), harvested and **grounded before landing** — a name is not a proof.
- **Claude** (this loop) drives **integration, verification-by-driving, hardening, and commits** —
  every subagent/codex output is verified by building + running, never trusted on its word;
  security teeth are re-audited; commits are path-specific.
- **Parallel-safe fan-out:** frontend (`demo/`) and new self-contained crates (`dregg-dice`) run
  in parallel with engine work; engine lanes serialize on `attested-dm/src/game.rs` (shared-tree
  safety). New crates + `demo/` are the parallel lanes; `game.rs` is one-at-a-time.
- **Verify > believe:** a lane is done when it builds + its driven test passes on *our* tree, not
  when it reports success. Findings are traced before they're bugs; claims are earned, not named.
