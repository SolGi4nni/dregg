# The Attested Game Engine — Roadmap

**Vision:** a verifiable AI-game-master *platform*. An AI narrates rich adventures; the world
resolves every move by rules a stranger can check; randomness is provably fair; content is
authorable by anyone in text; and a full playthrough — its randomness and its rule-adherence —
is verifiable without trusting the server. "Single-player web3 that actually works," because the
rules are the referee.

Ordering principle: **leverage** — build the primitives that unlock the most downstream first,
and keep every capability *world-resolved* (the AI proposes; the world disposes) and *verifiable*.

---

## Phase 0 — the hardened base ✅ (done)
The engine (`attested-dm`): closed typed-action resolution (`resolve_action`), a prev-linked
hash-chain ledger, capability-gating (`DmCaps`), input slot-confinement. Four dungeon games with
distinct mechanics (crawl · NPCs+combat · spellcasting · light-as-resource). A readable `.dungeon`
DSL + a real validator (`parse_dungeon`/`validate`). The collective vote (`/party`). A hosted,
**hard-$20-metered** narrator (`dregg-narrator`, Claude Haiku 4.5 via Bedrock). The arcade +
authoring pages (`/hub /vault /party /author /forge`). **Hardened by a 4-lane correctness review.**

Honest gaps (the frontier, see Phase 3): the attestation's *authentic* leg is a fixture;
`verify()` authenticates the chain but does not re-run the resolver.

## Phase 1 — depth + delight 🔨 (in flight)
- **Consumables + status effects** — potions heal, elixirs buff, poison ticks; consumed, timed,
  world-resolved; DSL support. The seed of a combat engine.
- **Room-map visualizer + live-validating forge** — see the dungeon graph + your position; author
  with errors surfaced as you type. The seed of an overworld + a visual editor.

## Phase 2 — the high-leverage primitives 🎯 (next)
- **Verifiable randomness** (`dregg-dice`, parallel-safe new crate) — provably-fair dice / loot /
  crits / procgen. *Aim past commit-reveal* (VRF / beacon / in-circuit — codex is designing the
  ambitious version). Unlocks skill checks, loot, and procedural generation at once.
- **Save/load persistence** — serialize + resume a `GameSession`; the "resumable across sessions"
  capability. Unlocks Discord cross-session play, resumable web play, and overworld persistence.
- **Overworld** — connect dungeons on a region map with a hub; travel between adventures. Turns
  "N games" into one world. (The room-map is step one.)

## Phase 3 — RPG systems + the trust frontier ⚔️
- **Combat engine** — turn-based tactical: initiative, multiple enemies, abilities, targeting,
  status stacks. The deepest single gameplay upgrade.
- **Character progression** — xp, skills, classes (warrior/mage/rogue) with distinct action sets.
- **Verifiable rule execution** — close the honest gap: a re-execution light client that re-runs
  `resolve_action` over the bound actions (trust-minimized), then the critical resolver invariants
  proven *in-circuit* via dregg's real `circuit`/fold machinery (trustless). Codex is assessing
  feasibility against what `circuit-prove` actually provides.

## Phase 4 — the platform flywheel 🌐
- **UGC community** — the `/forge` + library become a platform: publish, play, rate authored
  dungeons; **verifiable leaderboards + speedruns** (the receipt chain already proves a legit win).
- **Co-op party play** — multiple real players, each a character in one adventure (beyond voting).
- **Discord integration** — the `/dungeon` bot (built, blocked only by an external `turn` refactor)
  + persistence-backed features (channel save state, leaderboards).
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
  in parallel with engine work; engine lanes serialize on `attested-dm/game.rs` (shared-tree
  safety). New crates + `demo/` are the parallel lanes; `game.rs` is one-at-a-time.
- **Verify > believe:** a lane is done when it builds + its driven test passes on *our* tree, not
  when it reports success. Findings are traced before they're bugs; claims are earned, not named.
