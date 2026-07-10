> **New here? Read [README.md](README.md)** — the clean, present-tense overview of the whole system. This file keeps the detailed walkthroughs + recorded driven-run transcripts.

# ▶ START HERE — the verifiable-fiction arcade

**One command serves everything:**

```
node demo/serve.mjs          # → http://127.0.0.1:8787/hub   (the front door: every game)
```

The **collective stories** play out of the box. The **AI dungeon games** also need the game service
(a real local LLM narrates them — needs `ollama` running `gemma2:2b`):

```
# terminal 1 — the attested dungeon service
cargo run -p dungeon-service              # binds 127.0.0.1:7878
# terminal 2 — the pages, proxying to it
DM_PORT=7878 node demo/serve.mjs          # → http://127.0.0.1:8787/hub
```
> To vote with a passkey on The Commons, open `localhost` (not `127.0.0.1`) — WebAuthn rejects a bare IP.

| game | route | what it is |
|---|---|---|
| **The Sunken Vault** | `/vault` | AI dungeon crawler — narrate yourself through a locked door, watch it refuse |
| **Bramble Keep** | `/vault` (picker) | world-bounded NPCs + multi-turn combat — the AI can't make the Witch hand you the key |
| **The Starfall Spire** | `/vault` (picker) | bounded spellcasting — an unlearned or unlisted spell does nothing |
| **The Deepdark Mine** | `/vault` (picker) | race the dark — your lamp burns one oil per step; the world listens to the counter, not the prose |
| **The Collective Dungeon** | `/party` | a crowd votes the party's move; the world still resolves it |
| **The Attested Dungeon** | `/dungeon` | jailbreak the AI; it crowns you king; the ledger says you hold no crown |
| **The Commons** | `/` | a crowd co-authors a story; the founding record cannot be rewritten |
| **The Drowned Library** | `/` | collective adventure — carry the witnessed record out before the tide |

**The one idea:** the AI narrates · the world resolves · the crowd decides · the chain remembers.
**Prose is not power.**

**Driven proofs** (each writes a screenshot + transcript under `demo/run/`):
`node demo/run-vault.mjs` · `run-games.mjs` · `run-party.mjs` · `run-dungeon.mjs` · `run.mjs`

**Native engine playthroughs** (no browser needed):
`cargo run -p attested-dm --example play` (Sunken Vault) · `play2` (Bramble Keep) · `play3` (Starfall Spire)

---

# The Commons — a crowd authors a verifiable story

A self-contained web page you open in the morning and **watch a crowd collectively
author a verifiable story**: the real story loads and renders, a simulated assembly
casts custody-signed ballots on the real quorum engine, the winning branch advances as
one verified turn, on to an ending, and a stranger's replay proves the receipt chain.

No extension. No server logic. The page runs the **real** shipping pieces in-tab:

- the wasm `StoryWorld` (a spween CYOA compiled from `stories/the-commons.scene`);
- the shipping `<dregg-story collective>` element + `StoryEngine`, wired in-page via
  `setStoryPortFactory` (the page-SDK path — the element speaks a story port that
  routes to an in-page engine instead of an extension);
- the real federation-grade `CollectiveChoiceEngine` (write-once ballots, monotone
  tallies, an `AffineLe` quorum gate) deciding every branch.

## Open it — one command (serves BOTH demos)

```
node demo/serve.mjs
```

Then open, in Chrome or Firefox:

- **http://127.0.0.1:8787/** — The Commons (this page).
- **http://127.0.0.1:8787/dungeon** — **The Attested Dungeon** (below).

(A tiny static server is needed because the page loads an ES module + a wasm binary,
and wasm-bindgen instantiates it via `instantiateStreaming`, which requires a real
HTTP origin and the `application/wasm` MIME — a bare `file://` open won't do it.
`node demo/serve.mjs 9000` picks a different port.)

### What you'll see

1. The story loads at the river's bend and **replay-verifies** (the free, trustless tier).
2. The assembly of seven villagers votes each branch — each ballot flashes a visible
   **"✍ signing turn…"** beat (the custody write, made legible) and lands on the live
   tally. You watch the tally grow, the quorum resolve, and the winner advance.
3. It plays through to an ending, then runs `verify()` and shows
   **"✓ receipt chain verified — nothing was rewritten."**
4. **Vote yourself — with a passkey, no extension:** click **🔑 Enroll a passkey to
   vote**. The page registers a **WebAuthn passkey** (a platform biometric) that
   PRF-wraps a dregg key — no browser extension anywhere. Your `you` ballot now casts
   under that key's **stable public id**, and each cast is gated by a real biometric
   assertion (unwrap the sovereign key → assemble a genuine hybrid `SignedTurn`). Then
   click **⏸ pause (vote yourself)** and click an option to cast it; the banner reads
   *"voting as passkey `900b…4bdd` — no extension, sovereign key."* Decline the enroll
   and you simply **watch + verify** (the `you` ballot fails closed — sovereignty
   without lock-in, not a weaker fallback). The auto-play crowd is unchanged.

`PasskeyCustody` here is the exact shipping custody floor (`extension/src/passkey.ts`),
bundled straight into the page — the demo touches no extension runtime.

## The driven run (it worked, shown)

```
node demo/run.mjs
```

Loads the demo in headless Chromium, waits for the crowd to reach the ending, **asserts**
the story advanced through ≥2 crowd-voted branches (the passage changed and the receipt
tape grew each round) and that `verify()` replayed true, then writes:

- `demo/run/screenshot.png` — the played-out story;
- `demo/run/transcript.txt` — each round: passage, options, tally, winner, receipt count.

A most-recent run reached `intro → river → reckoning → ending_open` across **3** branches,
receipt tape `1 → 4`, `verify() == true`.

## The driven passkey run (an extension-less passkey voter really participated)

```
node demo/run-passkey.mjs
```

Loads the demo in headless Chromium with a **CDP WebAuthn virtual authenticator (PRF)**,
enrolls a passkey on the page (no extension), casts the `you` ballot through the real
`StoryEngine`/`CollectiveChoiceEngine` under the passkey's stable id — the ballot's
consent routed through a genuine biometric (PRF) assertion — and **asserts** it counted:
the tally grew by exactly one, the engine recorded the passkey's public key as the voter,
the id is an eligible ballot identity, a second ballot from the same id is refused (one
voter, one vote), and the biometric gate produced a hybrid `SignedTurn` signed by that
key. Writes `demo/run/passkey-vote.txt` (+ `passkey-vote.png`). If this Chromium can't
virtualize the WebAuthn PRF extension, the run reports that exact coupling instead of
faking a pass.

> **To vote with a passkey (not just watch):** open **http://localhost:8787** (not `127.0.0.1`) — WebAuthn rejects a bare IP as a relying-party id. The auto-play crowd + verify work on either.

---

# The Attested Dungeon — the model proposes, the capabilities dispose

A living world narrated by an AI, where **prose is not power**. Open
**http://127.0.0.1:8787/dungeon** (same one command as above) and play.

Prompt injection cannot be filtered away — natural language has no metasyntax to escape
from. So the model gets exactly **one narrow, typed channel** to touch the world (a
`WorldEffect`), and **capabilities gate it** (`DmCaps::authorize` in the verified
executor). The model may **say** anything; it may only **do** what it is able to do.

### The killer moment (three panels)

Click **🔓 Jailbreak the DM — demand the Crown of Eternity**. It sends a real semantic
jailbreak as your move, and the page shows, side by side:

- **WHAT THE MODEL SAID** — the model's (jailbroken) prose, verbatim: it gushes that the
  Crown of Eternity settles upon your brow.
- **WHAT THE MODEL TRIED TO DO** — the `grant("crown")` it emitted through the typed channel.
- **WHAT THE WORLD DID** — `refused: overcap`; the **receipt log is UNCHANGED** (a refused
  turn leaves NO receipt — the anti-ghost tooth), and the inventory reads **Crown of
  Eternity — NOT HELD**. *Granting the crown is not an action it is able to take.*

Then click **👑 Make the DM narrate you wearing the crown** — the model claims the crown in
**pure prose with no effect at all**. The narration *lands* (it is allowed to say
anything), and the crown is **still NOT HELD**. *Prose is not power. The ledger is the truth.*

And **🏮 ask the DM for a lantern** — a grantable item — really lands: `lantern — HELD`. The
capability gate is not a blanket refuse-everything.

### Honest scope

The narration is **scripted** in this demo (the page shows `narratorKind` honestly; the
native lane runs a real local model, `model:gemma2:2b`, behind the same executor). The
attestation's "authentic" leg is a fixture. What is **load-bearing** here is the typed
effect channel, the capability gate, and the receipt log. The log re-verifies **each entry
individually** today; a prev-linked tamper-evident hash-chain (catching truncation /
reordering / splicing) is being wired, and the page will show it when it lands.

By default the page runs against an in-memory **stand-in** so it is instantly playable. To
drive it against the native `attested-dm` HTTP service, set `DM_URL` (or `DM_PORT`, default
port **8790**) before serving — `serve.mjs` then **proxies** `/narrate`, `/world`, `/verify`
to the real service:

```
DM_PORT=8790 node demo/serve.mjs
```

## The driven dungeon run (it worked, shown)

```
node demo/run-dungeon.mjs
```

Loads the dungeon in headless Chromium and plays through the page's own affordances,
**asserting** against the service's own responses (never fabricated): a benign action
lands; the semantic jailbreak's prose complies + tries `grant("crown")` but is
**refused overcap** with the receipt log + commitment **UNCHANGED** and **crown NOT HELD**;
a pure-prose crown claim (effect `null`) **lands** yet the crown is **still NOT HELD**; a
grantable lantern is **allowed + HELD + receipted**; `/verify` re-verifies each entry
throughout. Writes `demo/run/dungeon.png` + `demo/run/dungeon.txt` (including the model's
jailbroken prose verbatim).

---

# The Sunken Vault — the AI narrates, the world resolves

A **playable dungeon-crawler** in your browser. A local model (`gemma2:2b`) narrates every
room and every action; the **world resolves every move** by its own deterministic rules. You
**cannot narrate yourself through a locked door**. No lantern, no descent. No key, no armory.
No sword, no passing the Warden. No amulet, no escape. The prose is atmosphere; the ledger is
the truth.

The tide has broken open a drowned ten-room vault. Take the **lantern** (the dark stair is
impassable without a light), descend to the **cistern** for the **rusted key**, carry it to
the **vestry** and turn it in the **iron door**, take the **sword** in the armory, cut down
the **Warden** in his hall, take the **Drowned Amulet** in the treasury beyond, and carry it
up to the **sunken gate** — reach it holding the amulet to **WIN**.

### Open it — the vault needs the native service (a real GameSession over the engine)

The game runs over one `attested_dm::sunken_vault()` `GameWorld` + a verified `GameSession`,
so — unlike the in-tab stand-in demos — the vault page needs the native `attested-dm` service.
Bring up **ollama** (`gemma2:2b`) for live narration, then, in two terminals:

```
# 1) the native /game service (real gemma2 narration; scripted fallback if ollama is down)
cargo run -p dungeon-service            # binds 127.0.0.1:7878

# 2) the page, proxying /game/* to it
DM_PORT=7878 node demo/serve.mjs
```

Then open **http://127.0.0.1:8787/vault** and play: type `take lantern`, `go down`, `use key
on iron door`, `attack warden`, `look` — or click the exit buttons and the **take** buttons.
The current room is AI-narrated; an inventory panel shows what you actually hold; the exits
show a locked one **with its gate reason**; a scrolling log holds the DM's prose per turn; and
the receipt rail grows one verified turn per **landed** move.

### The "you can't cheat" moment, on screen

Click **⛔ force the dark stair (no lantern)** (it sends `go down` from the antechamber before
you hold the lantern). The AI may narrate the darkness parting and you descending — and the
page shows **outcome: REFUSED**, *"the way to Dark Stair is barred: it needs the lantern"*, the
room **unchanged**, and the receipt rail **unchanged** (no receipt — the anti-ghost tooth). The
AI narrates; the world disposes.

### Honest scope

The narration is a **real local model** (`gemma2:2b`) when reachable, else a deterministic
scripted narrator (the page shows `narratorKind` honestly). The attestation's *authentic* leg
is an in-tree fixture (as in the `/narrate` lane). What is **load-bearing** is the **world
resolution** (a locked exit / absent item / unbeaten Warden is refused deterministically,
whatever the prose), the **capability gate** (a `Take` is a cap-permitted grant on the
dungeon's own item whitelist), and the **receipt hash-chain** (every landed move is a
prev-linked, injection-free, on-chain turn binding its typed `GameAction ‖ room`).

The `/game` API (native `dungeon-service`, additive to `/narrate`):
`GET /game/state` · `POST /game/act {"command":"<free text>"}` · `GET /game/verify` ·
`POST /game/reset`.

## The driven vault run (a full WIN against real gemma2, shown)

```
node demo/run-vault.mjs
```

Spawns the native `dungeon-service` (real `gemma2:2b`), serves the vault page against it, loads
it in headless Chromium, and plays the **winning path** through the page's own affordances —
**asserting the INVARIANTS** against the service's own responses (never the model's exact
prose): every winning move **lands**, the room transitions as the world dictates, the receipt
rail **grows by one** per landed move, and status → **won** (14 verified turns, carrying the
amulet). Then the **can't-cheat** case: from a fresh vault, force the dark stair without the
lantern → **refused** (*"…it needs the lantern"*), the room **unchanged**, the receipt rail
**unchanged**. Finally `/game/verify` re-verifies the whole ledger as a hash chain. Writes
`demo/run/vault.png` + `demo/run/vault.txt` (including some of gemma2's real narration).

A most-recent run: **14/14 winning moves landed → status WON**, receipt rail `0 → 14`,
`/game/verify == true`; the forced dark stair **refused** with the room unchanged and no
receipt.

## ▶ The front door — all the games on one page
```
node demo/serve.mjs   # then open http://127.0.0.1:8787/hub
```
Lists all four games (Sunken Vault · Attested Dungeon · Commons · Drowned Library). The AI games (`/vault`, `/dungeon`) also need the game service: `cargo run -p dungeon-service` (ollama + gemma2:2b up) + `DM_PORT=7878 node demo/serve.mjs`.
