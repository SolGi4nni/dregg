# dregg game engine — fun + infra plan (2026-07-12, 3-thinker synthesis)

From a game designer (is it fun?), a platform architect (reusable engine?), and a prior-art scholar (autonomous worlds /
ZK games / what makes games fun). They converge. (Companion to docs/GAME-ENGINE-ROADMAP.md + docs/GAME-ROLEPLAY-STACK-MAP.md;
docs/GAME-STRATEGY.md sequences this plan and carries the locked decisions.) A `[BUILT: path]` tag marks an item that is
real code at HEAD — read that module's own "honest scope" section for its named seams; untagged items are open.

## The diagnosis
World-class verifiable-turn engine + N-surface platform. The two gaps the thinkers named, at HEAD:
- **"Not FUN yet — you cannot lose."** True of the original universes (the `FieldGte(hp, 1)` floor REFUSES a lethal blow;
  dice_combat.rs:543), and answered by a stakes-forward universe: **dungeon-on-dregg/src/bloodgate.rs** ("The Bloodgate
  Trial") routes a lethal position to a committed DEFEAT passage, so a run can be genuinely LOST. The other two
  fun-killers — your choices rarely fork · your character never changes how you play — have built answers too (A2, A5).
- **"Not a game-engine PLATFORM yet."** The keystone (a general game-state schema + verified allocator) is a built crate
  (**dregg-schema**, B1), as are the reactive-read indexer (B2) and session-key play UX (B3); the author SDK (B5) is the
  open platform gap.

## dregg's unfair advantages (all three flagged; the AW engines would kill for these)
Verification is the SUBSTRATE not a bolt-on · a real attenuable capability/authority model (not just token ownership) ·
**attested AI narration bound to verified state = THE cure for AI Dungeon's fatal flaw** (the DM can't forget your HP or
teleport you) · provably-fair randomness native.

## TRACK A — FUN (ranked; every fix rides a tooth the engine already proves)
1. **Real loss / stakes** [BUILT: dungeon-on-dregg/src/bloodgate.rs]. A lethal position routes to a terminal DEFEAT
   passage (a WriteOnce `downed` flag + `-> END`) — the loss is FORCED by the executor, and a LOST run re-verifies by
   replay exactly like a WON one. Opt-in hardcore rides the persistent character [BUILT:
   dreggnet-offerings/src/character.rs + daily_descent.rs — a hardcore death is WriteOnce-final and a re-opened dead
   character loads dead] — the no-cheat leaderboard means PROVING YOU SURVIVED.
2. **Forking dilemmas + a meaningful choice every turn** [BUILT: bloodgate.rs]. A provably-fair d20-vs-DC gamble gates a
   shortcut past the fight (a forged pass is caught on replay), and a shared WriteOnce slot makes opportunity cost real
   (the crown OR the key — both claims write the same `hands` slot). Makes the crowd ARGUE.
3. **Flagship = a ROGUELITE on the daily procgen dungeon** [BUILT: dreggnet-offerings/src/daily_descent.rs; played live
   via discord-bot/src/commands/descent.rs]. The daily drand-beacon-seeded world (verification is a real quicknet
   pairing check; fetching the day's round is the named client seam), permadeath on the bloodgate pattern, the
   persistent hardcore character, the ugc-dregg no-cheat leaderboard. Turn-based + permadeath + meta-progression is
   NATIVE to "a turn = an attenuable proof-carrying token"; the receipt IS the run. Precedent: Loot Survivor (genre
   works on-chain), Hades/STS/FTL (the fun). Real-time RTS fights the substrate.
4. **Attested-DM roguelike (the unfair advantage)** [attestation wiring BUILT: deos-hermes/src/narrator_crown.rs +
   dungeon-on-dregg/src/narrator.rs]. Rebuild AI Dungeon WITH the rules layer it never had: verified state adjudicates
   HP/inventory/dice, the attested LLM narrates within it. dregg's edge is decisive; the incumbent's failure (memory
   cliff + no adjudication) is documented. The crown is welded over the game narrator (GAME-STRATEGY locked decision
   #3): AttestedNarrator proves the injection-free leg in-circuit and binds the attestation commitment into the turn
   receipt, and narrate_turn_bedrock_attested carries the real Bedrock presentation (tlsn-live-gated). The named
   operational remainder: the default authentic-provenance leg is a self-signed fixture — a live pinned-notary session
   closes it.
5. Deeper retention: build identity [BUILT: character.rs binds the proven progression sheet to the player's stable
   DreggIdentity — a character carries + levels across runs; dreggnet-gear/src/talents.rs wires the spells.rs spellbook
   class-gated, so a Mage run != a Warrior run]; loot that matters [BUILT: dungeon-on-dregg/src/loot.rs — a chest = a
   provably-fair draw minting an owned, transferable dreggnet-asset with run-bound provenance; a legendary is a
   PROVABLE flex]; the crowd IS the party [BUILT: dreggnet-party — seated identities, each seat's held caps ARE its
   role, an on-ledger loot split]; the finished dialogue.rs in the play surface; a Monotonic countdown; leaderboard
   streaks.

## TRACK B — INFRA (ranked; keystone first)
1. **THE KEYSTONE — a general game-state / ECS-style component schema + a VERIFIED allocator** [BUILT: dregg-schema].
   Author declares typed components -> a checked slot/heap layout (Legal: disjoint + in-bounds, the RotatedLayout
   discipline — an ill-aligned layout is UNCONSTRUCTABLE) -> a generated CellProgram -> a typed API, via TRANSLATION
   VALIDATION (untrusted allocator search, CHECKED output). All three thinkers converged on this (the architect's #1 +
   the scholar's "adopt ECS — MUD/Dojo/Cardinal did" + the "verified layout optimizer" forward vision). The crate's own
   honest scope: the Legality + refinement checks are the Rust translation-validation forms; the Lean-PROVEN Legal
   obligation and the game-turn-slice leaf refinement are its named seam.
2. **A reactive-read INDEXER** [BUILT: starbridge-web-surface/src/indexer.rs]. Torii/MUD pattern, welded from two
   halves that exist: ReceiptStream verified ingest (a receipt folds only if in-order + un-forged) + dregg-query
   (EDB/CALM/MMR non-omission) into a MaterializedView — reactive query subscriptions, local tx simulation, and
   non-omission attested answers, so a client renders a living world at low latency.
3. **Session keys + passkeys + paymaster UX** [BUILT: dreggnet-offerings/src/session.rs]. A session key = a
   caveat-bounded delegation of the player's play cap — macaroon attenuation, no new trust model; the paymaster binds
   to the real dregg-pay CreditLedger (dreggnet-offerings/tests/session_paymaster.rs: a paid move is a genuine debit, an out-of-credit
   move commits nothing).
4. **Durable persistence** [partially built]. The character store is durable (discord-bot/src/character_store.rs,
   sqlite — a leveling character survives a restart) and session resume reopens by REPLAY of the reproducible public
   input, never a trusted blob (dreggnet-offerings/src/resume.rs). Durable backing for the remaining in-memory stores
   stays a named seam at each trait boundary.
5. **A game-author SDK / paved path** [open] (the Offering/Host/Frontend spine is generic; missing = a scaffold +
   docs/guide so a STRANGER ships a dregg game — the pug bar; capability confinement is the SAFE moddability pure-EVM
   can't offer).
6. The asset/economy layer is largely built as crates (dreggnet-asset / -trade / -craft / -gear / -companion — see
   docs/GAME-INFRA-ROADMAP.md for the per-item map); no-cheat tournaments exist (dreggnet-tournament: brackets advance
   only on a verified win, replay or succinct-proof submission; a Descent bracket rides it in
   dreggnet-offerings/src/descent_tournament.rs). Open: matchmaking, game-tick/settlement-tick separation (World
   Engine/Keystone/Paima), parallel sessions.

## Failure modes (documented by the field)
Tokenomics-first (P2E collapse — fun BEFORE economy); interoperability theater; tech-demo-not-a-game (verifiability is not
a mechanic); crypto-native-only accessibility (why Cartridge exists); AI-DM without rules / with a memory cliff (AI Dungeon
— bind narration to verified state + design moderation up front); crowd-play without an aggregator (TPP Democracy mode —
but a deviant minority can be productive, don't over-sanitize); commit-reveal mid-game (use zk); real-time genres.

## Where the plan stands
docs/GAME-STRATEGY.md is the sequenced record. A1–2 (real loss + forking dilemmas), A3 (the daily roguelite flagship),
A4's attestation wiring (narrator_crown.rs; the authentic-provenance leg's live pinned-notary session is the named
operational remainder), B1 (the schema keystone), B2 (the indexer), and B3 (session-key UX) are code at HEAD; open is
B5 (the author SDK) — and the human bars: a real (non-team) replay signal and real players, which no amount of code
satisfies. None of it has a durable public deployment.
