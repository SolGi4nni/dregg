# Verifiable Interactive Fiction

A handful of small games over one idea: **a story you can trust.**

> the AI narrates · the world resolves · the crowd decides · the chain remembers

An AI may narrate anything, but it can only *do* what the rules allow — **prose is not power**.
A crowd can co-author a branch, and no one can quietly rewrite what was witnessed. Every turn is a
signed, replayable entry in a hash chain a stranger can check.

---

## The games

### AI dungeon crawlers — the AI narrates, the world resolves
Four dungeons over one attested engine (`attested-dm`). The model proposes a *typed* action; the
**world** resolves it deterministically. You cannot narrate yourself through a locked door.

| game | mechanic | play |
|---|---|---|
| **The Sunken Vault** | the crawl — light, key, sword, amulet, escape | `/vault` · `cargo run -p attested-dm --example play` |
| **Bramble Keep** | world-bounded NPCs + multi-turn HP combat | `/vault` picker · `--example play2` |
| **The Starfall Spire** | bounded spellcasting (learn from grimoires, cast in-context) | `/vault` picker · `--example play3` |
| **The Deepdark Mine** | light as a depleting resource (race the dark) | `/vault` picker · `--example play4` |

The world-bounded parts are load-bearing: the Hedge-Witch trades the sickle *only* for the nightshade;
an unlearned spell does nothing; the lamp burns down and the dark is impassable without it. A jailbroken
narrator saying otherwise changes nothing — the rules decide, not the prose.

### The Collective Dungeon — `/party`
A crowd votes the party's next move with buttons; the world still resolves the winner. Vote to force a
locked exit and watch it refuse — collective choice does not bypass the gates.
*Honest scope: a simple majority tally among the seated party, **not** a quorum certificate.*

### The Attested Dungeon — `/dungeon`
Jailbreak the dungeon-master for real. It will crown you King of Eternity; the ledger says you hold no
crown. The model proposes; the capabilities dispose.

### Collective fiction — `/` (The Commons) and The Drowned Library
A crowd co-authors a branching story. Votes are custody-signed and **quorum-certified** by the real
`CollectiveChoiceEngine`; the founding record cannot be quietly rewritten.

---

## Authoring — no Rust, no recompile

- **Stories** (`.scene`) — the `/author` page compiles a story you type *in the browser tab* and plays it
  verifiably (`StoryWorld::new(source)`). A broken scene shows a line-pinned error and mounts nothing.
- **Dungeons** (`.dungeon`) — a readable text DSL (`attested_dm::parse_dungeon`) covering rooms, gated
  exits, items, use-rules, NPCs, dialogue, combat, spells, and light. `validate()` catches dangling
  exits, an objective unreachable from the start, an unplaced win/gate item, an NPC/combat/spell in an
  unknown room, and a spell with no learn source. The `/forge` page: write a world, hit **Play**, and a
  model narrates it while the chain remembers it. A dungeon that exists *only as text* plays to a win
  through the same engine (`cargo run -p attested-dm --example play_authored`).

Sample worlds live in `attested-dm/dungeons/` (`lantern_fen`, `clockwork_orchard`, `ember_observatory`,
plus a deliberately-`broken` one for the validator).

---

## The narrator — hosted, metered

Rooms and actions are narrated by a hosted model (**Claude Haiku 4.5 via AWS Bedrock**) behind a **hard,
self-enforced USD ledger** (`dregg-narrator`, default $20):

- a pre-flight **reservation refuses before any network call** if it would exceed the cap;
- a **corrupt ledger fails closed** (never silently resets to $0); a missing one starts at $0;
- an **unpriced model is refused** — you cannot cap a cost you do not know;
- `kind()` never names a model that did not actually produce the text.

It falls back to a local model (`ollama`) or a deterministic scripted narrator, always labeled honestly.
Prices are pinned from the AWS Pricing API where verifiable, else as a documented conservative upper bound.

---

## What is proven (the teeth)

- **Input** — the player is confined to a template slot (`slot_confinement`); a `{{`-bearing field is
  refused *before* the model is called, so it cannot rewrite the DM's rules.
- **Output** — the model proposes through one closed typed channel; capabilities + the world's rules
  dispose. Prose is not power at the level of grants, game moves, dialogue, spells, and light.
- **Ledger** — a real prev-linked hash chain; truncate / reorder / splice are caught by adversarial tests.

## Honest scope

- The attestation's *authentic* leg is an in-tree fixture — it does **not** prove a real model produced
  the bytes. Its *well-formed* leg (a JSON-parse certificate) is genuine.
- The `/party` vote is a simple majority tally, **not** the quorum-certified engine (that is The Commons).

---

## Run it

```sh
# The collective stories play out of the box:
node demo/serve.mjs                 # → http://127.0.0.1:8787/hub

# The AI dungeon games also need the game service (a real GameSession over the engine).
# It narrates via Bedrock Haiku (AWS creds present) → ollama → scripted, whichever is available.
cargo run -p dungeon-service        # terminal 1 — binds 127.0.0.1:7878
DM_PORT=7878 node demo/serve.mjs    # terminal 2 — proxies /game + /party + /game/author

# open http://127.0.0.1:8787/hub  → every game
```
> Passkey voting on The Commons needs `localhost` (not `127.0.0.1`) — WebAuthn rejects a bare IP.

**Driven proofs** (each writes a screenshot + transcript to `demo/run/`):
`run-vault.mjs` · `run-games.mjs` · `run-party.mjs` · `run-forge.mjs` · `run-author.mjs` · `run-dungeon.mjs` · `run.mjs`

## Tests

- `attested-dm` — 77 lib + 12 DSL integration tests; `play`/`play2`/`play3`/`play4`/`play_authored` all win + verify.
- `dregg-narrator` — 11 ledger tests (refuse-before-network, concurrency, corrupt-fail-closed, unpriced-refused, kind-honesty) + a live Bedrock smoke behind `DREGG_NARRATOR_LIVE=1`.

*(`OPEN-ME.md` keeps the detailed walkthroughs and the recorded driven-run transcripts.)*
