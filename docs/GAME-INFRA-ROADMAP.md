# The Descent / dregg game-engine — infra roadmap (2026-07, 3-ideator + NFT synthesis)

What to build for the game, grounded in the real engine. Every item rides a primitive that already ships on the executor;
the "verifiable edge" is the thing a normal engine can't sell. Companion to GAME-STRATEGY / GAME-FUN-AND-INFRA-PLAN /
CONTENT-AND-ASSET-SPEC. A `[BUILT: crate]` tag marks an item that is real code at HEAD — each of those crates' docs carry
their own honest-scope section; untagged items are open.

## THE CROWN — the only-dregg-can-do thing (lead with this)
Records + items are PROOFS, not server rows. The sharpest unlock: **PRIVATE-STRATEGY play** — the proof-leaderboard (ugc
`submit_proof`) verifies a fold proof in O(1) and stores NO moves, so you prove "I soloed today's hardcore, no hits" WITHOUT
revealing HOW (route/build stay secret forever). A normal engine has only trust-the-client (cheatable) or demand-the-replay
(leaks strategy); dregg has a strictly-better third. Composes with: **items whose provenance IS their identity** (a loot
AssetId encodes the drop; rarity a provable ~3% tail), **no dupes by construction** (double-spend = a type error, the #1 MMO
economy-killer gone), **un-fakeable cheevos** [BUILT: dreggnet-cheevo — an achievement = an anchored, re-checkable predicate
over a verified run (depth>=N, no-death clear), mintable soulbound]. The tournament bracket rides the proof path too
[BUILT: dreggnet-tournament accepts a succinct `Registry::submit_proof` submission alongside replay]. Cross-game portable
holdings stay near-free (the AssetId is already game-independent).

## SOCIAL / MULTIPLAYER (ranked; the biggest play-together unlocks are closest to built)
1. **PARTIES (small->med, #1)** [BUILT: dreggnet-party]: the crowd IS the party, each seat a job — a fixed roster of
   seated identities sharing one run, each seat a player-cell whose held capabilities ARE its role (a division of labor
   the executor enforces move-for-move; rides mud.rs seated player-cells + collective.rs::open_with signed roster/quorum
   + combat.rs FOCUS_BUDGET), with an on-ledger loot split. Escapes the TPP mush via DISTINCT caps per seat. Edge:
   nobody plays your seat / forges your vote / fakes the loot split.
2. **SHARED HUB / TAVERN (small)** [BUILT: dreggnet-tavern]: node/src/shared_world.rs boot_shared_world (a hosted board +
   presence seats + live receipt-stream sync + over-reach refusal), re-homed as a persistent tavern between runs — an
   LFG board + per-patron market stalls, live co-inhabitance on the node's one ledger. Un-fakeable presence — the
   connective tissue that makes every other social system discoverable.
3. **PLAYER TRADING** [BUILT: dreggnet-trade]: a dreggnet-asset transfer (a real owner-signed spend) bound to a
   sealed-escrow leg from starbridge-escrow-market = a trustless atomic swap — scam-proof P2P trade + real provenance.
   Keep tradable to cosmetics/provenance/mats, NEVER power.
4. **RAIDS (big, the frontier)** [open]: a PROVEN world-first kill — combat.rs reverify_draw (un-forgeable dice) +
   multicell.rs ObservedFieldEquals (phases gate on prior-phase completion) + collective coordination. Needs the
   multi-cell concurrent-battle frontier combat.rs names. Stage after parties+hub.
5. **GUILDS** [BUILT: dreggnet-guild]: a formed persistent group as a cap-bounded shared cell — an aggregate of
   un-forgeable clears + an escrow treasury, every guarantee a primitive the executor already re-checks.
6. **SPECTATOR (med, machinery built)**: fog-respecting, anti-stream-snipe (a full-board mid-game grant is REFUSED); the
   SpectatorGrant/MembraneNegotiation stack is remarkably complete.

## WORLD / QUESTS / CONTENT (quests + UGC + factions are ONE tent)
1. **QUESTS** [BUILT: dreggnet-quest]: the dialogue idiom generalized — a quest-giver hands a multi-step gated objective;
   each step a WriteOnce step-flag, ORDER-gated; turn-in a FieldGte tooth on the committed steps; a completion re-executed
   to a declared WIN through ugc-dregg's no-cheat gate. The FAILURE MODE it exists to kill: quest state as host
   bookkeeping (the LARP) — here every step-flag is gated committed cell state a stranger re-executes.
2. **UGC / AUTHORING (the flywheel)**: a stranger authors a quest/world as a spween .scene (text, no Rust) -> the no-cheat
   board. Safe MODS = a new TransitionCase under an attenuated cap. Authorship is ed25519-attested and remix lineage is a
   content-addressed parent edge [BUILT: ugc-dregg — a publish claiming another author's key without a valid signature is
   refused; publish_derived refuses a remix of an unpublished parent]. The one missing surface stays open: E4 `/gallery
   publish-scene` -> authored_signed (small, high leverage).
3. **FACTIONS / REPUTATION** [BUILT: dreggnet-faction]: per-NPC disposition generalized to a faction cell — per-faction
   Monotonic rep slots + rival-ceiling cross-slot teeth, every rule a real executor predicate. The standing guidance
   holds: ship rep only WITH the content it gates.
4. **PERSISTENT WORLD / PLACES** [partially built]: the overworld region offering exists
   (dreggnet-offerings/src/overworld.rs — a RegionMap of universes on a real region cell, travel gated on VERIFIED
   completion). Open: a TOWN HUB Loc (dialogue NPCs — quest-givers, faction reps, merchants) + durable place state + a
   living world.
5. **WORLD EVENTS / SEASONS** [abstraction BUILT: dregg-season — carries hall-of-fame/prestige/champions across upgrade
   boundaries]: a beacon-seeded limited-time Universe (everyone plays the same, verifiable by re-derivation) + collective
   boss invasions (the crowd can't vote past the teeth). Content wiring stays open.
6. **AI-DRIVEN CONTENT** [open]: the crown applied to content — AI PROPOSES a typed Command / an authored scene, the world
   + the no-cheat board DISPOSE (an ill-formed/cheating scene fails the publish gate; an AI grant of an unearned reward
   refused).

## PROGRESSION / ECONOMY
1. **CRAFTING** [BUILT: dreggnet-craft]: a provably-fair forge that CONSUMES a typed multiset of owned inputs (the
   economy's first real sink); the outcome a verified draw; a forged craft mints nothing.
2. **GEAR** [BUILT: dreggnet-gear]: assets gated CROSS-CELL by real ownership ("this ability unlocks because you own+equip
   the flaming sword" is a kernel predicate); durability as a Monotonic sink.
3. **DEEPER PROGRESSION** [BUILT: dreggnet-gear/src/talents.rs]: the spells.rs spellbook wired class-gated into play (a
   Mage run != a Warrior run) + an echoes-gated talent tree. Talents bought with death-earned ECHOES, never $DREGG.
4. **THE ECONOMY** [partially built]: escrow swaps [dreggnet-trade] + sinks (craft/durability) + faucets
   (loot/echoes/quests) exist as crates; respec/entry sinks and the tuned loop are open. No-P2W BY CONSTRUCTION: $DREGG =
   the illiquid service-pile (buys cosmetics/AI-DM/seats), power from earned play, rank re-executed against the shared
   seed (can't be bought).
5. **COMPANIONS** [BUILT: dreggnet-companion]: an owned asset (a dreggnet-asset note hatched from a provably-fair draw)
   FUSED with a leveling cell — a provable bond, can't be faked-leveled or duped; hardcore permadeath makes it real.
THE KEYSTONE UNDERNEATH [BUILT: dregg-schema — schema -> checked layout -> generated CellProgram -> typed API, via
translation validation]: the standing rule is to route new game-state through it (declare components, don't hand-roll a
16-slot layout each time) — one reusable game-state layer, the keystone's payoff.

## NFT (project the proven achievements onto a durable external chain + take a fee on the motion)
The provable achievement is ALREADY built dregg-native (dregg-season hall-of-fame/prestige/champions, loot.rs fair-drop
assets, the no-cheat board, meta.rs, dreggnet-cheevo). Of the 3 legs: (1) the Solana EXPORT leg is built
[dregg-pay/src/nft_mint.rs — the inverse of the import rail: a 1-of-1 SPL NFT whose metadata memo carries the run/cheevo
commitment; reuses HD custody signing; Metaplex/cNFT is a bigger later dep]; (2) the FEE/ROYALTY rail is open (NO
settlement path has a cut today — a marketplace/OTC cut at settle -> the treasury, which already receives); (3) RE-IMPORT
is nearly free (ProvenForeignHolding + bridge_mint_against_lock fits a 1-of-1 SPL as-is -> mint the dreggnet-asset). Bots:
/claim-a-cheevo, an artist /store, /mint over the /gallery + deposit-address + signing pattern. Angle: EARNED, PROVABLE
NFTs (a cheevo backed by a verifiable run), not JPEGs. NOT dregg-native (dodges devnet churn); importable when stable.

## THE PORTFOLIO (the platform proof)
automatafl (a verified BOARDGAME — Lean-proven mechanics + a STARK) + multiway-tug (a verified CARD GAME — cards as assets +
a hidden hand) are the keystone's 2nd/3rd customers, built ON dregg-schema at HEAD: dregg-multiway-tug lays out its state
as a dregg-schema-allocated layout, dregg-automatafl's prove/fold path mirrors game-turn-slice, and dreggnet-game-board
ships their full-STARK asynchronous leaderboard. Turn-based = native to a proof-carrying-turn engine. (Plans: separate
docs.)

## WHAT REMAINS (the standing rule + the open set)
The recurring failure mode across ALL of it: any world/game state that is host bookkeeping instead of a gated committed cell
is the LARP. Everything must be a real StateConstraint the executor re-checks + a stranger can replay — that rule outlives
this roadmap's sequencing, most of which is executed (crown cheevos + proof-path bracket, parties-with-distinct-caps,
the tavern hub, trading, quests, factions, gear/talents, crafting, companions, guilds, the season abstraction, the NFT
export leg). Open: raids (the multi-cell frontier), the `/gallery publish-scene` surface, the town hub + living-world
content, seasonal content wiring, the fee/royalty rail, and the economy's tuning.
