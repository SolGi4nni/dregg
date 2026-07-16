# HOARDLIGHT

## The Dragon Descent

> Every morning, the same impossible burrow opens for everyone. Every dragon makes it a different story.

**Hoardlight** is a cozy, daily, push-your-luck descent about raising a tiny dragon into a magnificent, peculiar proper dragon. You nose through enchanted rooms, gather shinies, and decide at each warm little rest-nook whether to dream home with what you have or whisper the most dangerous sentence in dragon culture:

**“One more room.”**

No dragon dies. A dragon who runs out of wakefulness gets overwhelmed, makes one heroic squeak, curls into a cinnamon roll, and dreams home. Some loose shinies tumble from the dream on the way. The loss matters; the creature does not become disposable.

The larger promise is stranger and more important: a dragon is not a skin wrapped around four combat stats. It is a living, on-chain system of small parameters whose interactions become behavior. Its birth braid comes from two real parents. Its learned facets come from real adventures. Its hoard changes how those parameters resonate. Two dragons acting together produce cross-terms neither has alone. Every surprising result has an inspectable explanation and an unbroken provenance trail.

This is the game only dregg should host: **a creature-raising game where emergence is real state, family history is playable, secrets remain private but provable, and the cute story visible in Discord is the projection of a world that cannot quietly cheat.**

---

## 1. The feeling

Hoardlight takes place under **Hearthspire**, a leaning town built around the chimney of a sleeping mountain. Little dragons nest in kettles, window boxes, hat cupboards, and the hoods of people who stood still too long. The town’s basement is the **Downbelow**, an endlessly rearranging repository for everything the world has misplaced: buttons, moon reflections, unsent postcards, thunder trapped in jars, the left socks of giants, and treasures that insist they are not treasures.

Each dawn, the Downbelow gives a great subterranean *hiccup*. Its rooms settle into a new configuration from the day’s beacon. Bells ring. Dragonlings tumble out of bed. The Descent begins.

The tone is:

- **Adventurous, never cruel.** The tension comes from greed, curiosity, surprise, and the comedy of being very small in a very odd place.
- **Earnestly cute.** Dragons purr hot enough to toast bread. A proper dragon may be mountain-sized in spirit while still keeping a favorite spoon.
- **Specific and tactile.** Shinies have names, histories, funny silhouettes, and parameter signatures. “+3 loot” is never the fantasy.
- **Generous about failure.** A failed run creates a nap story, a verified personal record, and often a clue. It does not delete a friend.
- **Proudly legible.** The chain is presented as a magical scrapbook, not buried as infrastructure. “Show me where this came from” is always one click away.

Example rooms include the Button-Mushroom Lift, the Moth Librarian’s Reading Sock, a Teacup Geyser, the Bellroot Garden, the Suspiciously Polite Puddle, and the Moonmilk Pantry. The Downbelow is not full of enemies waiting to be killed. It is full of situations waiting to meet *this particular dragon*.

---

## 2. The north-star loop

### The daily promise

At the same UTC boundary, everyone receives the same committed daily seed. That seed determines the room graph, stimuli, shiny families, fair draw stream, and public daily oddity. The procgen path already derives a byte-identical dungeon from a committed seed with indexed draws (`procgen-dregg/src/lib.rs:1-32`, `procgen-dregg/src/lib.rs:141-163`), while the live beacon path verifies the published drand reveal before deriving the day (`procgen-dregg/src/beacon.rs:275-362`).

The shared seed does **not** make every run the same. It creates a common topic of conversation:

> “Did your dragon make the puddle sing?”  
> “No, Pip has too much Puff and launched it through the ceiling.”

The daily map is one shared instrument. Each dragon is a different way of playing it.

### Before the door

The player opens `/descent` and sees:

1. **Today’s tiny omen.** “All echoes are slightly sticky.”
2. **Their dragon, visibly growing.** Its current silhouette, mood, favorite shiny, stage, resonance braid, and the one recent change worth noticing.
3. **A three-slot Expedition Pocket** at hatchling stage. The player chooses hoard charms whose parameters will join the run. Later stages unlock richer hoard layouts, not merely bigger numbers.
4. **One ranked First Flame.** A dragon gets one WriteOnce ranked attempt per day. Practice dreams can be replayed afterward, but the public daily board records the unrehearsed journey. This turns verification into a game rule rather than a badge pasted on the result.

### A room, moment to moment

Every room is a 30–90 second decision:

1. **Arrive.** See charming art, two lines of authored prose, the room’s public “temper” icons, and a soft hint about what it responds to.
2. **Read your dragon.** The UI highlights likely resonances without revealing the entire result. It might say: “Puff wants to help. Hush is tugging the other way.”
3. **Choose an approach.** Usually three verbs with personality rather than tactical jargon: *sniff it*, *nuzzle it*, *make a grand entrance*, *sit very still*, *ask the spoon*.
4. **Resolve the composition.** The room combines its committed parameters with the dragon, chosen action, and carried hoard. A receipt records the exact landed transition. The player sees a named reaction—**Mothfriend**, **Glitter-Sneeze**, **Puddle-Song**, **Cozy Deadlock**—and can open “Why?” for the actual terms.
5. **Take the consequence.** Gain provisional shinies, alter wakefulness or spook, learn a room secret, or create a path that only this parameter mixture opens.
6. **Choose at the nook.** Bank the haul and dream home, rearrange one pocket slot, or descend.

The current narrative DSL already makes every choice a real executor turn and compiles many conditions into cell predicates (`spween-dregg/src/lib.rs:1-37`, `spween-dregg/src/compiler.rs:391-503`). The new game replaces the existing fight/key/hoard daily script with a room library built around resonance, greed, and recovery; the present daily is only a small authored corridor (`dreggnet-offerings/src/daily_descent.rs:214-340`).

### Banking, spilling, and the nap

Finds inside a run begin as **provisional shiny claims** bound to that run’s seed, draw index, room, and receipt chain. They become asset notes only when banked or retained at run-end. This avoids minting and reversing a global asset on every room while preserving exact origin.

At a nook, the player can:

- **Tuck In:** bank everything and end the ranked run.
- **Pocket One:** protect one favorite loose shiny, at a wakefulness cost.
- **One More Room:** continue with the full loose bundle at risk.

If wakefulness reaches zero or spook overflows, the dragon curls up. A committed spill rule chooses which unprotected provisional finds are left in the dream. The operator cannot spare a valuable item for a favorite player, and the player cannot claim a more favorable spill. The dragon returns safe, gets a little “I dreamed of…” vignette, and keeps its banked haul, protected keepsake, memories, and verified depth.

### The boards are stories, not one ladder

One globally optimal metric would flatten this system. The daily page instead celebrates several replay-verified stories:

- **Deepest Little Nap** — furthest room reached before curling up.
- **Brightest Tuck-In** — highest banked shiny resonance.
- **Oddest Harmony** — rarest named room reaction.
- **Gentlest Route** — most rooms resolved without adding spook.
- **Family Trick** — a reaction last seen in an ancestor’s verified run.
- **First to Find It** — earliest verified discovery of the daily secret.

The engine already treats stored runs as untrusted input and regenerates a fresh world, replays the moves, checks chain linkage, and re-evaluates the win predicate (`ugc-dregg/src/lib.rs:710-850`; `dreggnet-web/src/descent.rs:227-256`). Hoardlight broadens “win” into several committed predicates, but never into an admin-set verified flag.

---

## 3. The heart: the Resonance Braid

### Parameters, not stats

Every dragon has eight bounded birth resonances:

| Resonance | What it tends to mean | What too much can do |
|---|---|---|
| **Warmth** | courage, heat, ripening, comfort | melt, wake, overwhelm |
| **Glimmer** | curiosity, reflection, treasure-sense | distract, dazzle, attract attention |
| **Puff** | lift, force, noise, dramatic entrances | scatter, topple, startle |
| **Hush** | patience, listening, soft movement | stall, fade, miss a bold opening |
| **Root** | steadiness, memory, growth | stick, resist, become stubborn |
| **Ripple** | flexibility, water, mimicry | wobble, spread, lose shape |
| **Tingle** | static, magnetism, sudden insight | spark, cling, twitch |
| **Curl** | coziness, protection, storage, sleep | doze, hoard, refuse to uncurl |

Each birth value is small—conceptually 0–15—and the birth total is conserved. There is no perfect dragon with every number maxed. Growing does not erase the original distribution. It adds room to express it.

A dragon also carries a sparse set of **knots**: signed relationships between pairs of resonances. A `Warmth×Puff` knot may make a glorious baking breath; a `Glimmer×Hush` knot may reveal shy constellations; a negative `Root×Ripple` knot may make the dragon hilariously indecisive around mud. Knots are where siblings with similar values become unmistakably different.

The current companion schema has species/rarity/level/XP and executor-gated abilities, buffs, breeding, and active swaps (`dreggnet-companion/src/lib.rs:298-316`, `dreggnet-companion/src/lib.rs:903-1039`). That is useful scaffolding, but it is not this system. The Resonance Braid must become a first-class, versioned state schema, not an opaque metadata blob or a repainted rarity roll.

### A bounded nonlinear resolver

For one room, the conceptual calculation is:

```text
effective = clamp(birth braid + learned facets + pocket layout + chosen approach)

reaction[j] = room bias[j]
            + Σ linear[j,k] · effective[k]
            + Σ pair[j,k,l] · effective[k] · effective[l]
            + Σ knot[j,k,l] · knot[k,l]
```

Everything is bounded, integer, versioned, and deterministic. The room’s sparse coefficients and thresholds come from authored templates plus indexed daily draws. The winning reaction is not simply the largest number: thresholds can activate multiple tags, cancel one another, open a route, change a shiny, or create a comic complication.

Players never need to do matrix arithmetic. They learn a readable ecology:

- Warmth plus Puff makes airborne things more airborne.
- Hush can calm Tingle, unless Glimmer gives it something fascinating to cling to.
- Root loves the Bellroot Garden but can turn the Polite Puddle into a boot-shaped commitment.
- Curl protects a shiny from a scare, but high Curl near Moonmilk may end the run in an extremely contented nap.

After resolution, **Why this happened** expands into a charming audit card:

```text
PUDDLE-SONG

+6 Ripple from Pip
+4 Hush from the Blue Button
+5 because Ripple × Hush harmonized
-3 because today’s puddles are Sticky
crossed the Singing threshold at 12

day 47 · room 6 · draw 19 · receipt 8fc1…
```

This is the design’s central discipline: **the chain explanation and the player explanation are the same explanation at different resolutions.**

### Approaches transform; they do not add “attack power”

Room choices apply small, public transformations to the braid:

- **Sniff** rotates attention toward Glimmer and Hush.
- **Nuzzle** couples Warmth and Curl while damping Puff.
- **Grand Entrance** couples Puff and Tingle, increasing both upside and spook.
- **Sit Very Still** lets Root stabilize one volatile pair.
- **Ask a Friend** replaces one self-pair with a cross-dragon pair.

This keeps each decision meaningful even when the player knows the room. A dragon is not automatically good at every problem matching its highest value; the player chooses which part of it to bring forward.

### The hoard is a circuit

Shinies also carry small resonance vectors, one knot or quirk, material tags, and full provenance. A run pocket and the home hoard are **layouts**, not lists. Adjacency and orientation matter:

```text
[Moon Button] — [Warm Spoon] — [Bottle of Almost-Thunder]
     Hush           Curl              Tingle
```

The spoon can damp the bottle, or the button can reflect it, depending on placement. A hatchling has three expedition slots. A wyrmling has five and can form a loop. A proper dragon has eight and one “heart” slot that changes how the whole circuit resolves.

This makes mediocre-looking heirlooms stay interesting. A +1 Hush button inherited through four owners might be the missing bridge between two much louder treasures. Because forged outputs are the same asset notes that inventory and trade continue to hold—not copied DTOs—the material’s identity can survive craft, ownership, and sale (`dreggnet-craft/src/forge.rs:211-225`, `dreggnet-surfaces/src/world.rs:1-46`).

### Hoard-fed growth has two different verbs

- **Bask:** arrange owned treasures around the dragon for temporary expression. The items remain tradeable, and their effects apply only while live ownership/equip gates hold.
- **Nibble:** consume a snack-grade shiny to add a small permanent learned facet. The shiny’s note ends; the dragon’s growth receipt names it. Nothing is duplicated—the object’s story continues as part of the dragon.

One asset can nourish one dragon once. The consumed note, owner signature, exact delta, and resulting dragon root are one provenance edge. This gives the hoard economic tension without turning every beloved heirloom into optimal food.

### Composition between creatures

When two dragons act together, the game does not average their stats. One chooses a role transform and the resolver includes **cross-dragon terms**:

```text
duet = A + rotate(B, role)
     + cross · (A[k] × B[l])
```

A warm, shy dragon and a sparkly, loud dragon may make a thundercloud feel safe. Two individually excellent Puff dragons may launch the objective into another channel. Order and role matter; neither player is reduced to “contribute power.”

The signature mechanic is the **Family Trick**. If a landed duet activates a knot that one dragon demonstrably inherited and the other dragon complements, the reaction records the relevant ancestry edges. Descendants may rediscover, invert, or complete tricks no designer explicitly authored. Provenance becomes an input to wonder, not merely a receipt after it.

The executor already has the crucial cross-cell tooth: `ObservedFieldEquals` compares a field in one cell against a witnessed field in another under a finalized ledger root and fails closed without authority (`cell/src/program/types.rs:1500-1534`, `cell/src/program/eval.rs:2049-2107`). Simple ownership, readiness, stage, equip, and partner-consent gates can therefore be executor-refereed. The nonlinear duet itself needs a dedicated transition verifier/AIR; it must not be smuggled in as trusted host arithmetic.

### Rules that keep emergence healthy

1. **Birth budgets are conserved.** Lineage redistributes possibility; it does not print total power.
2. **Every strength has contexts where it complicates things.** No resonance is a dump stat and no build solves every room.
3. **Knots are sparse.** A player can learn a dragon’s personality without inspecting hundreds of coefficients.
4. **Daily coefficients come from a curated grammar.** Procgen combines authored, testable room families; it does not emit arbitrary nonsense.
5. **Exact math is inspectable after resolution.** Mystery precedes the choice, never the audit.
6. **Version roots travel with every result.** A future balance change cannot reinterpret an old dragon or run.
7. **Cosmetic rarity is not parameter dominance.** Rare means unusual shape, provenance, or knot—not “strictly better.”

---

## 4. Growing a dragon

Growth is the whole loop made visible. The home screen should never leave the player wondering what their adventures are feeding.

### Hatchling

A kettle-sized wobble with oversized feet.

- Three expedition-pocket slots.
- One visible birth knot and several undiscovered tendencies.
- Can run the daily Descent, collect shinies, bask, nibble, and join a supervised Huddle.
- Art changes quickly: horn buds, tail tuft, wing shape, favorite sleeping pose.

### Wyrmling

Longer, bolder, capable of being embarrassed.

- Five pocket slots and loop-shaped hoard circuits.
- Chooses one **expression**—not a class, but a stable way to transform an approach: Hearthkeeper, Cloudsniffer, Mosslistener, Bellchaser, and more.
- Can lead Huddles, forge, carry a guild responsibility, and offer a Nest Promise.
- Inherited and learned knots become fully visible.

### Proper Dragon

Magnificent. Still perhaps obsessed with spoons.

- Eight-slot hoard with a heart position.
- Can establish a named nook in the Warm Shelf tavern, sponsor community errands, and become an ancestor.
- Unlocks no universal power multiplier. Its advantage is a larger expressive vocabulary, richer compositions, and social authorship.
- Receives a permanent, soulbound **Becoming Scale** whose proof lists the diverse acts that completed growth.

Stage thresholds should require *breadth*, not grinding one resource: shinies from several daily seeds, a social Huddle, a personally meaningful achievement, and enough nourishment across multiple resonance families. Soulbound achievement notes already support untradeable earned history at the ISA layer (`dreggnet-cheevo/src/lib.rs:1-40`, `dreggnet-asset/src/lib.rs:247-287`).

Growth changes the deterministic dragon portrait. Asset-derived SVG art is already a pure function of an asset address for gear/cards (`dreggnet-web/src/sprite.rs:1-28`); Hoardlight extends that idea to a dragon renderer whose inputs are the dragon’s identity, stage, braid, knots, lineage marks, and chosen keepsake. The portrait is not an uploaded claim. It is another faithful view of state.

---

## 5. Eggs, lineage, and the joy of clicking backward

### Nesting is consent, not consumption

Two keepers offer a **Nest Promise**. Each parent signs, names the other parent, selects one inheritable expression, and commits one seasonal nesting opportunity. The parents remain alive and playable. The egg seed binds:

```text
verified beacon reveal
+ both parent asset ids, canonically ordered
+ both signed Nest Promises
+ nest season and egg ordinal
+ inheritance ruleset root
```

For every birth locus, an indexed fair draw chooses parent A, parent B, or a low-probability bounded mutation. Separate draws select sparse knots, cosmetic morphology, and one “echo”—a non-power memory mark derived from a parent’s soulbound history. The draw machinery already binds an event to its full context and exposes indexed unbiased streams (`dice/src/lib.rs:1-26`, `dice/src/draw.rs:52-131`). There is no reroll button the server can secretly press.

Every locus carries an origin:

- `From(parent A, Warmth locus)`
- `From(parent B, Hush locus)`
- `Mutation(day 183, draw 14, +1 Ripple / -1 Root)`
- `Recombined(parent knot A, parent knot B)`

The birth budget remains conserved after mutation. A mutation moves a point or changes a sparse relationship; it does not manufacture a superior tier.

Eggs may be gifted or traded before hatching. Hatching binds the dragon to its keeper as a soulbound creature identity. This permits a warm egg economy without turning raised friends into liquid level bundles.

### Why lineage is worth browsing

The **Dragon Almanac** is a primary game surface, not an explorer link hidden in settings. A dragon page shows:

- Its animated portrait and current braid.
- A color braid where every segment can be clicked to its parent of origin.
- The egg’s fair draw transcript and ruleset version.
- Parents, siblings, descendants, and verified Family Tricks.
- Learned facets, each linked to the shiny it consumed and the run that found it.
- Soulbound memories: First Nap, Puddle-Singer, Proper Dragon, tournament ribbons.
- A timeline of keeper, nest, forge, guild, and adventure events.

A shiny page is equally explorable:

> **Warm Spoon of Day 47**  
> Moon-silver found by Juniper in room 8 of the verified Day 47 Descent → traded to Moss → combined with a Bellroot clipping and a cracked button under recipe v3 → fair rarity draw 2 → basked beside Pip during the Great Puddle Huddle → currently in Ember’s hoard.

The asset layer already supplies stable asset identity, owner-signed successor notes, linear predecessor links, immutable trait roots, and chain verification (`dreggnet-asset/src/lib.rs:1-43`, `dreggnet-asset/src/lib.rs:439-503`). Craft draws bind the beacon, recipe, and sorted input set and can be reverified (`dreggnet-craft/src/draw.rs:27-72`, `dreggnet-craft/src/draw.rs:144-181`). Hoardlight makes those facts delightful to browse.

### What must change for true lineage

The current companion `breed` path validates both owned parents, hashes their IDs into a species tag, spends both parent assets, and hatches a fresh fair rarity draw (`dreggnet-companion/src/lib.rs:1174-1226`). That proves a two-parent event happened; it does **not** inherit a parameter vector from either parent, preserve living parents, or create per-locus origin edges.

The asset note itself has one linear `prev_note`, not a two-parent DAG (`dreggnet-asset/src/lib.rs:142-183`). Hoardlight therefore needs a versioned dual-parent birth artifact and contribution receipts in addition to the existing owner lineage. This is a real new protocol object, not frontend work.

---

## 6. Discord is the town square

Discord is not a notification pipe for a web game. It is where dragons live together.

### The daily thread

At reveal, the bot opens a dated thread:

> **THE DOWNBELOW HICCUPED — Day 183**  
> Today, echoes are sticky.  
> 214 dragonlings are peering over the edge.

`/descent` opens a private or ephemeral preparation card, then posts shareable milestones into the daily thread: a rare room reaction, a funny nap, a new board category, or a discovered secret. Buttons drive the real offering turns; the existing generic Discord adapter already turns one `ViewNode` surface into embeds, buttons, modals, typed actions, and executor-refereed advances attributed to a derived cryptographic identity (`discord-bot/src/commands/offering.rs:1-31`, `discord-bot/src/commands/offering.rs:177-226`).

The interface should feel native:

- `/dragon` — the portrait, growth, braid, favorite shiny, and Almanac link.
- `/descent` — today’s run.
- `/hoard` — rearrange the circuit with select menus and a visual grid.
- `/huddle` — create, join, pledge, and resolve a group event.
- `/lineage` — browse an egg, parent, trait, or shiny trail.
- `/nest` — offer or accept a signed Nest Promise.
- `/duel @player` — challenge a human to Automatafl.

The current bot already has a live daily command, persistent character store, verified beacon selection, durable board rows, and replay-on-load (`discord-bot/src/commands/descent.rs:9-39`, `discord-bot/src/descent_board_store.rs:1-26`). Hoardlight is a replacement experience over that plumbing, not a greenfield Discord prototype.

### Huddles: creatures doing things together

A **Huddle** is a 2–8 dragon asynchronous problem lasting several hours:

- Keep a moon-egg warm while its mother visits the dentist.
- Untangle the Bellvine without ringing Tuesday out of order.
- Convince a cloud whale that the guild hall is not a hat.
- Carry a gigantic teacup through a doorway designed by someone unserious.

The initiator posts a shared card. Players pledge a dragon, choose a role transform, and optionally commit one private approach. At close, the resolver reads each pledged dragon’s *actual current cell*, actual equipped hoard, actual keeper consent, and actual soulbound qualifications. It composes the parameters once and lands a joint result with a contribution breakdown.

Suggested role transforms are **First Sniff**, **Warm Wing**, **Pocket Keeper**, and **Chorus**. They alter how a dragon’s values enter the cross-terms; they are not tank/healer/DPS labels. The group discusses combinations, not power scores.

Some Huddles use **secret wishes**: each player sees their own committed hand or pledge, while others see fog. Only the selected public contributions are revealed. The hidden-hand primitive already blinds a Poseidon Merkle root, executor-checks membership, and updates the root on play (`dregg-multiway-tug/src/hidden_hand.rs:1-53`); a whole private match can fold to one succinct proof while unrevealed cards remain private (`dregg-multiway-tug/src/fold.rs:1-39`, `dregg-multiway-tug/src/fold.rs:251-278`). Hoardlight should generalize that substrate into Huddle pledges rather than leaking everyone’s plan through the bot.

Per-viewer projection is already a first-class offering verb, and the connected web/Discord adapters invoke it for the actual viewer (`dreggnet-offerings/src/lib.rs:492-527`, `discord-bot/src/commands/portfolio.rs:139-146`). That means “my hand to me, fog to you” can remain one game state rather than separate trusted messages.

### The Warm Shelf, Roosts, and errands

- **The Warm Shelf** is the persistent tavern: presence, looking-for-Huddle posts, nest announcements, tiny stalls, and the social fire. The live tavern already models multiple signed identities sharing one ledger, presence, listings, and party-up events (`dreggnet-tavern/src/lib.rs:1-37`, `dreggnet-tavern/src/lib.rs:438-650`). Its current offering surface is only a read mirror, so the designed experience must graduate beyond that skeleton (`dreggnet-surfaces/src/tavern.rs:164-176`).
- **Roosts** are guilds. They keep a communal hoard, sponsor Huddles, elect a Bellkeeper, and compete on verified collective curiosities rather than raw wealth. The guild core already has cap-based membership, verified boards, sealed treasury flows, aggregate stats, and signed-seat governance (`dreggnet-guild/src/lib.rs:1-50`; `dreggnet-guild/src/governance.rs:41-105`).
- **Errands** are short quest chains for town characters. A Moth Librarian remembers whether the dragon returned a page; neighborhood standing gates later choices. Quest phase ordering, reward gates, and cross-cell giver checks exist (`dreggnet-quest/src/lib.rs:1-82`, `dreggnet-quest/src/giver.rs:120-216`), while faction standing has monotone reputation, thresholds, betrayal flags, and rival caps (`dreggnet-faction/src/lib.rs:1-72`). In Hoardlight these become cozy clubs—the Moth Library, Bellgardeners, Cloud Postal Union—not war factions.

---

## 7. Storyflame: the narrator that cannot award itself a crown

**Storyflame** is an optional narrator for landed outcomes. It sees the committed room state, the selected approach, and the verified result, then turns them into two warm sentences. It never chooses the result, grants an item, edits a parameter, or turns a refusal into a success.

This boundary is already native to `attested-dm`: the model proposes through a closed typed action channel and the deterministic world disposes; prose claiming a locked door opened changes nothing (`attested-dm/src/game.rs:1-29`). Cap bounds refuse over-authority effects before state advances (`attested-dm/src/lib.rs:51-56`). The prompt template and player slot are committed and re-renderable (`attested-dm/src/prompt_template.rs:54-113`, `attested-dm/src/prompt_template.rs:196-208`).

The provenance badge must be exact:

- **Scripted** — authored room prose.
- **Local model** — model-generated, no real external model-provenance claim.
- **Attested transport** — a real MPC-TLS session, though the present test endpoint is not a real model.
- **Attested model** — the live Bedrock path binds the completion a real model returned.

The code explicitly distinguishes the default self-signed fixture, real MPC-TLS transport, and live Bedrock model provenance (`attested-dm/src/lib.rs:15-37`). Hoardlight must never label the fixture “provably AI.” The useful promise is stronger than marketing fuzz: **Storyflame can be charming, but it cannot lie the world into changing.**

---

## 8. Automatafl is the Duel—human versus human, always

In Hearthspire, formal dragon duels happen on the **Cloudboard**. Two human keepers place Puffstones on a 5×5 rooftop board. Both secretly choose a move; both commit; both reveal; attraction and repulsion rays resolve; then the little automaton steps. Spectators see sealed intent until reveal. A match is short, positional, social, and wonderfully blameable.

This is **Automatafl**, and it is the game’s one thing called **the Duel**.

Hard rules:

1. **Human versus human only.** No AI opponent, no solo puzzle masquerading as a match, no Downbelow guardian, no mandatory PvE gate.
2. **Dragon progression cannot buy board power.** Your dragon is the duelist identity and spectacle, not a stat advantage.
3. **Parameters may compose only symmetrically.** Both dragons’ braids can derive shared weather, board colors, sound, or a mirrored exhibition modifier applied equally to both seats. Ranked rules remain normalized.
4. **Results create soulbound ribbons and lineage anecdotes, not stolen creatures.** Optional escrow wagers can be a later consensual mode.

The live game already defines the 5×5 schema, simultaneous commit/reveal/resolve phases, and transition teeth (`dregg-automatafl/src/game.rs:1-31`, `dregg-automatafl/src/game.rs:47-111`). Its reference engine implements the attraction/repulsion raycast, automaton step, scoring, and conflicts (`dregg-automatafl/src/reference.rs:109-330`). The current offering renders the board and viewer-specific sealed information (`dregg-automatafl/src/surface.rs:1-35`, `dregg-automatafl/src/surface.rs:450-579`).

The proof code contains in-proof Poseidon-sealed moves (`dregg-automatafl/src/moves.rs:586-701`), but the playable surface still uses its host session seal, and the full n=5 D3 trace exceeds the current width used by proof tests (`dregg-automatafl/tests/prove_fold.rs:108-115`). Those are proof-wiring/engineering gaps, not a reason to misuse Automatafl as PvE content.

The existing multiway-tug becomes a separate Warm Shelf parlor game, **Ribbonpull**: a two-player hidden-hand influence game about persuading seven neighborhood clubs. It is not “the Duel” and it is not a solo activity. Its greatest strategic value to Hoardlight is the reusable hidden-hand and one-proof private-session substrate.

---

## 9. Where the engine lands

This map distinguishes what exists at HEAD from the game identity it should receive. It is deliberately not a crate-name reskin checklist.

| Engine piece | What it really provides now | Hoardlight landing |
|---|---|---|
| `cell/src/program` + executor | Default-deny cases; method/effect/slot guards; WriteOnce, monotonicity, exact deltas, inequalities, and finalized-root cross-cell equality (`cell/src/program/types.rs:23-42`, `cell/src/program/types.rs:895-1055`, `turn/src/executor/execute_tree.rs:66-130`). | The constitution: one First Flame per day, exact growth deltas, nest consent, stage gates, actual partner/equip checks. A new verifier handles nonlinear resonance math. |
| `dreggnet-asset` | Owner-signed successor notes with stable asset ID, immutable traits, spend state, soulbound enforcement, and verifiable provenance (`dreggnet-asset/src/lib.rs:57-74`, `dreggnet-asset/src/lib.rs:645-719`, `dreggnet-asset/src/lib.rs:860-920`). | Shinies, eggs, forge outputs, ribbons, Becoming Scales, and consumable nourishment. |
| `dreggnet-companion` | Owned hatchable companions; progression; executor-gated buffs, abilities, swap; a two-parent breeding event (`dreggnet-companion/src/lib.rs:718-899`, `dreggnet-companion/src/lib.rs:903-1039`, `dreggnet-companion/src/lib.rs:1174-1226`). | Dragon lifecycle scaffold. Replace rarity-centric fresh eggs/perishing with resonance inheritance, living parents, drowsiness, and visible stages. |
| `dreggnet-craft` | Exact material multiset recipes, beacon-bound weighted draws, input burns, output mint, and shared-ledger provenance (`dreggnet-craft/src/recipe.rs:75-152`, `dreggnet-craft/src/forge.rs:237-384`). | The Hearthforge: combine found materials into hoard charms, egg cradles, and quirky treasures whose parameters and ancestry remain inspectable. |
| `dreggnet-gear` | Asset-bound stat roots, wear, loadouts, and equip/use gates tied to live ownership with `ObservedFieldEquals`; multi-peer set checks exist (`dreggnet-gear/src/gear.rs:249-270`, `dreggnet-gear/src/gear.rs:375-585`, `dreggnet-gear/src/multislot.rs:1-29`). | Expedition Pocket and hoard circuit. Replace Might/Ward/Guile dominance with resonance vectors, adjacency, and live ownership. |
| `dreggnet-trade` | Sealed escrow legs for assets/DREGG, deposit, settle/reclaim, plus listing/buy (`dreggnet-trade/src/lib.rs:109-136`, `dreggnet-trade/src/lib.rs:319-453`, `dreggnet-trade/src/lib.rs:481-553`). | Moonmarket for shinies, materials, charms, and unhatched eggs. Raised dragons remain soulbound. |
| inventory | There is no standalone `dreggnet-inventory` crate. `dreggnet-surfaces/src/inventory.rs` is an offering over the shared `AssetWorld`; craft/inventory/trade can share one object-identical ledger (`dreggnet-surfaces/src/lib.rs:153-163`). | The Satchel and Hoard views: ownership, live layout, favorite/pinned items, and provenance entry points. |
| `dreggnet-guild` | Capability membership, verified completion boards, sealed treasury, aggregate guild stats, signed-seat governance (`dreggnet-guild/src/lib.rs:1-50`, `dreggnet-guild/src/treasury.rs:1-23`). | Roosts, communal hoards, Huddle sponsorship, Bellkeeper elections, and cooperative discovery boards. |
| `dreggnet-tavern` | Multi-identity shared ledger with presence, event synchronization, private stalls, LFG listings, and party-up events (`dreggnet-tavern/src/lib.rs:150-178`, `dreggnet-tavern/src/lib.rs:284-370`, `dreggnet-tavern/src/lib.rs:606-650`). | The Warm Shelf, the persistent social home. Needs designed rooms, durable service deployment, and richer render/state graduation. |
| `dreggnet-party` | A fixed four-seat role roster, shared focus, WriteOnce loot split, and signed fork resolution; live join/raid flow is not complete (`dreggnet-party/src/lib.rs:1-55`, `dreggnet-party/src/lib.rs:228-317`, `dreggnet-party/src/lib.rs:418-540`). | Huddle roster/consent/fork scaffold. Replace demo seats and combat roles with live claims and resonance role transforms. |
| `dreggnet-quest` | Committed quest phase/flags, ordering, completion gates, replay, reward slot-change gates, and a cross-cell giver mode (`dreggnet-quest/src/lib.rs:1-82`, `dreggnet-quest/src/giver.rs:120-216`). | Town errands, room secrets, Proper Dragon sponsorships, and long-running character relationships. |
| `dreggnet-faction` | Monotone standing, threshold gates, one-way betrayal, rival caps, data-driven faction definitions, and persistence adapters (`dreggnet-faction/src/lib.rs:1-72`, `dreggnet-faction/src/roster.rs:216-377`, `dreggnet-faction/src/standing.rs:146-203`). | Cozy neighborhood clubs with mutually interesting loyalties. Dynamic cross-ledger integration still needs tightening. |
| `dreggnet-cheevo` | Predicates over replay-verified runs that mint ISA-enforced soulbound notes (`dreggnet-cheevo/src/lib.rs:180-243`, `dreggnet-cheevo/src/lib.rs:558-607`). | Memory Scales, nap stories, growth milestones, Family Tricks, and human-vs-human duel ribbons. |
| `dreggnet-adventure` | An integrated adventure report with exact item identity and composition seams; gear/companion aid cells are still separate from the Descent world (`dreggnet-adventure/src/lib.rs:1-77`). | One canonical “dragon went down, brought this home, grew this way” lifecycle receipt. Use it as an integration spine, not as a second game loop. |
| `dreggnet-saga` | Weaves run, item, faction, and identity artifacts while preserving object identity; tavern graduation is still named work (`dreggnet-saga/src/lib.rs:1-93`). | Almanac story bundles and share cards: one queryable thread across a life, shiny, family, guild, and adventure. |
| `dreggnet-offerings` | Frontend-neutral `Offering`, typed actions, landed/refused outcomes, viewer-aware render, and one surface/action vocabulary (`dreggnet-offerings/src/lib.rs:91-200`, `dreggnet-offerings/src/lib.rs:430-531`). | The one Hoardlight interaction core used by Discord, web, Telegram, and WeChat. |
| `dreggnet-surfaces` | Registers feature offerings; craft/inventory/trade share one `SharedWorld`, but most pages are thin generated forms (`dreggnet-surfaces/src/lib.rs:1-59`, `dreggnet-surfaces/src/lib.rs:145-205`). | Replace the demo catalog feel with dragon-specific designed experiences: Hoard, Forge, Almanac, Warm Shelf, Roost, Huddle. |
| `dreggnet-web` | Server-rendered multi-offering host, per-viewer rendering, verified Descent spectator/run pages, durable run inputs, and deterministic asset SVG endpoints (`dreggnet-web/src/lib.rs:24-46`, `dreggnet-web/src/descent.rs:1-31`, `dreggnet-web/src/sprite.rs:154-229`). | The rich visual home: dragon/lineage explorer, hoard circuit editor, replay scrubber, daily community board, and art. |
| `dreggnet-telegram` | Derived identities, shared offering actions as inline keyboards, and DM/group/topic session shapes (`dreggnet-telegram/src/lib.rs:1-34`, `dreggnet-telegram/src/lib.rs:51-88`). | A lighter daily and Huddle surface with group play; not a separate rules implementation. |
| `dreggnet-wechat` | Derived identities and the same offerings rendered as Official Account numbered replies; current session shape is 1:1 (`dreggnet-wechat/src/lib.rs:10-43`, `dreggnet-wechat/src/lib.rs:169-197`). | A delightful numbered-choice solo daily and notifications; social Huddles need a Mini-Program or link to the web/Discord shared session. |
| `discord-bot` | Bespoke daily run, generic offering adapter, viewer-aware portfolio mounting, persistent characters and board input (`discord-bot/src/commands/descent.rs:9-39`, `discord-bot/src/commands/portfolio.rs:1-28`). | The first-class town square and initial flagship client. Its portfolio worlds are currently separate per offering, so Hoardlight needs a shared world/session service. |
| `dungeon-on-dregg` | Real room state, items, tactical action resolution, dice/loot, progression, dialogue memory, collective choices, and an example of genuine cross-cell gating (`dungeon-on-dregg/src/lib.rs:1-39`, `dungeon-on-dregg/src/multicell.rs:1-63`). | Reuse rooms, choices, loot claims, dialogue, and collective structure. Do not inherit grim combat/permadeath as the game’s center. |
| `dregg-automatafl` | Simultaneous sealed-move 5×5 automaton game with viewer fog and transition proof work (`dregg-automatafl/src/game.rs:1-31`, `dregg-automatafl/src/surface.rs:1-35`). | The Cloudboard Duel: PvP, person versus person, never solo or AI. |
| `dregg-multiway-tug` | A two-player, seven-lane hidden-hand influence game plus a stronger reusable hidden-hand/fold path (`dregg-multiway-tug/src/lib.rs:1-42`, `dregg-multiway-tug/src/fold.rs:1-39`). | Ribbonpull parlor game and the cryptographic basis for secret Huddle pledges. |
| `spween-dregg` | Authored branching scenes compiled to real cells, choice receipts, chain replay, and verified collective choices (`spween-dregg/src/lib.rs:1-37`, `spween-dregg/src/verify.rs:97-185`). | Descent room authoring and replay. Unsupported condition shapes must remain handler-only or gain real predicates, never be mislabeled enforced. |
| `ugc-dregg` | Signed authored worlds/forks and completion admission by fresh-world replay plus a proof-anchor path; the real multi-turn Descent-to-fold glue is not complete (`ugc-dregg/src/lib.rs:41-103`, `ugc-dregg/src/lib.rs:494-514`, `ugc-dregg/src/lib.rs:710-850`). | Community room packs, seasonal burrows, verified discovery predicates, and eventual succinct run submissions. |
| `procgen-dregg` | Reproducible committed draws into a finite curated room graph, with live verified beacon retrieval (`procgen-dregg/src/lib.rs:34-63`, `procgen-dregg/src/beacon.rs:199-362`). | The daily Downbelow shuffle. Expand the authored room/reaction grammar; do not ask a raw generator to invent game truth. |
| `dregg-dice` (`dice/`) | Full-context event IDs, multiple evidence kinds, indexed unbiased bounded/weighted draws (`dice/src/lib.rs:1-26`, `dice/src/draw.rs:52-131`). | Egg inheritance, mutation, room/shiny selection, spill selection, and craft outcomes with no operator rerolls. |
| `attested-dm` | Typed world resolution, cap-bounded effects, committed prompts, injection refusal, receipt chains, and provenance policies that distinguish fixtures from real transport/model paths (`attested-dm/src/lib.rs:15-82`). | Storyflame: optional, delightful, provenance-badged narration after the rules resolve. Never the referee. |
| `deos-view` | One serializable `ViewNode` tree with sections, tabs, gauges, menus, grids, progress, tiles, coordinate boards, and progressive disclosure (`deos-view/src/tree.rs:1-13`, `deos-view/src/tree.rs:79-142`, `deos-view/src/tree.rs:144-300`). | One designed dragon experience projected appropriately to every surface—not a lowest-common-denominator form generator. |
| `dreggnet-sprite` | Deterministic address-derived SVG gear/card art, already served by web (`dreggnet-web/src/sprite.rs:1-28`). | Seed for faithful visual identity. Add dragons, eggs, room keepsakes, and lineage marks as state-derived art families. |

---

## 10. What is uniquely dregg about the game

### 1. A creature can surprise you without the server being allowed to invent why

Emergent behavior comes from committed parameters, a committed daily room, and a versioned deterministic resolver. The player can be surprised before the outcome and certain afterward. Most creature games offer either hand-authored personality theater or opaque server simulation. Hoardlight can make personality a public, inspectable system without making it simple.

### 2. “My dragon helped your dragon” is an executor fact

A Huddle does not trust a screenshot, cached profile, or Discord role. It gates on the partner creature’s finalized state, equipment ownership, stage, consent, and contribution. One cell can depend on another cell’s witnessed field. That makes cooperative composition materially different from posting numbers into a bot command.

### 3. Heredity is neither a database column nor a lootbox claim

Every inherited locus names its source. Every mutation names its fair draw. Parents cannot be silently swapped after a cute egg is previewed. The family tree is a proof graph whose interesting parts—knots, echoes, Family Tricks—change future play.

### 4. The object in the story remains the object in the economy

The Moon Button found on Day 47 is the same note in the Satchel, the same input consumed at the Hearthforge, and the same resulting provenance edge when its material becomes a spoon. Craft, inventory, trade, and explorer do not each mint their own version of its history.

### 5. Privacy can be a social mechanic without becoming a trust-me mechanic

Secret Huddle wishes, hidden parlor hands, and sealed Duel moves can be different per viewer while remaining one state. A succinct proof can certify the private sequence without disclosing the rest of the hand. “The bot knew it” is not the security model.

### 6. A leaderboard entry is an executable claim

The board can regenerate the day and replay the choices. First Flame, deepest nap, rare harmony, and community-authored clears can all be predicates over actual runs. A database edit cannot manufacture the underlying playthrough.

### 7. Achievements are memories that cannot be bought off another dragon

Soulbound Memory Scales can gate a cosmetic, a town dialogue, a Nest echo, or a Proper Dragon ceremony. Their non-transferability is enforced where assets execute, not merely hidden from a trade screen.

### 8. The narrator’s provenance and authority are visible separately

Storyflame’s words may be scripted, local-model, transport-attested, or real-model-attested. The badge says which. None of those paths gains permission to mutate the world outside typed, cap-bounded effects. This lets AI add warmth without becoming an unaccountable game master.

---

## 11. Build path: find the fun before building the kingdom

### Stage 1 — One More Room

**Goal:** the smallest thing that is genuinely fun for a week.

Build only:

- One dragon per player with a fixed eight-value birth braid and two knots.
- One daily seed, 8–12 rooms drawn from six excellent authored room families.
- Four approach transforms.
- Wakefulness, spook, provisional shinies, nooks, tuck-in, and deterministic dream spill.
- One ranked First Flame plus unranked practice dreams.
- Three-slot Expedition Pocket.
- Hatchling growth bar fed by banked/nibbled shinies.
- Discord first, with a simple web run card and replay-verified daily categories.

Do **not** build breeding, an open market, guild governance, UGC, or Automatafl into this milestone. Prove that reading a room, knowing Pip, choosing an approach, and saying “one more room” is fun.

Technical emphasis: define the versioned Resonance Braid schema and one authoritative bounded resolver. Use existing state predicates for First Flame, exact deltas, banking, and stage bounds; add the minimum custom transition proof needed for the nonlinear outcome. Rewrite the current grim daily content rather than stacking cozy copy on its HP/warden structure.

### Stage 2 — My Dragon Is Becoming Someone

**Goal:** make every return feel like raising a creature.

- Hatchling → Wyrmling visual transformation.
- Deterministic dragon portraits and room/shiny art.
- Hoard circuit editor with adjacency.
- Bask versus Nibble and continuous shiny-to-growth provenance.
- Almanac v1: click a learned facet back to its shiny and verified run.
- Soulbound Memory Scales and breadth-based growth gates.
- Storyflame as optional post-resolution narration with an honest provenance badge.

### Stage 3 — Dragons Do Things Together

**Goal:** make Discord indispensable.

- Live Huddle creation, join/consent, role transforms, and 2–4 dragon cross-parameter resolution.
- Warm Shelf presence/LFG and native thread lifecycle.
- Per-viewer secret wishes using hidden-hand commitments.
- Roost roster, small communal hoard, and verified cooperative boards.
- Wyrmling → Proper Dragon ceremony requiring one meaningful social contribution.

This stage also needs a production finalized-root/witness channel across nodes. The current in-process cross-cell example recomputes from a genuine ledger but explicitly names cross-node transport as missing (`dungeon-on-dregg/src/multicell.rs:48-63`).

### Stage 4 — The Family Album

**Goal:** deliver the owner’s central lineage promise correctly, not approximately.

- Nest Promises and non-consuming parent participation.
- Fair per-locus crossover and bounded mutation.
- Dual-parent birth artifact and per-locus origin receipts.
- Transferable eggs; soulbound hatched dragons.
- Full Dragon Almanac family graph, siblings, descendants, echoes, and Family Tricks.
- Provenance-conditioned room and Huddle reactions.

This stage begins with protocol design. The existing one-predecessor asset chain and parent-consuming fresh-draw breed function are not a safe shortcut.

### Stage 5 — A Living Hearthspire

**Goal:** let the systems produce stories beyond the daily.

- Hearthforge recipes and material families.
- Moonmarket over the same live asset world.
- Town errands, dialogue memory, and cozy club standing.
- Roost governance, treasury, sponsored events, and seasonal goals.
- Community-authored room packs with replay-verified completion predicates.
- Rich web lineage/provenance/replay explorer; Telegram group and WeChat companion surfaces.

### Stage 6 — The Cloudboard Season

**Goal:** add the excellent human competitive game on its own terms.

- PvP Automatafl challenges, matchmaking, spectators, normalized ranked seasons.
- Symmetric braid-derived exhibition weather and dragon spectacle.
- Soulbound duel ribbons and optional consensual shiny escrow.
- Wire the playable match to in-proof sealed moves and address the n=5 proof-width/folding path.
- Ribbonpull as a Warm Shelf parlor game.

No Automatafl AI is on this roadmap. A shortage of human opponents is solved with async challenges, scheduled club nights, spectating, rematches, and Discord matchmaking—not a bad bot.

---

## 12. Honest gaps between this vision and HEAD

These are product and protocol gaps the design intentionally creates or exposes:

1. **The Resonance Braid does not exist.** Current companion and gear schemas are conventional rarity/level/stat systems. The bounded nonlinear composition resolver, ruleset roots, knot schema, and explanation artifact need design, implementation, and proofs.
2. **True inheritance does not exist.** Current breeding spends both parents and makes a fresh fair egg keyed partly by parent IDs; it does not copy loci, preserve parents, or prove a per-trait origin.
3. **Asset lineage is linear.** Dual-parent birth provenance requires a new DAG-shaped artifact or contribution-receipt layer.
4. **The current Daily Descent is tonally and mechanically wrong for this game.** It is a small fight/key/hoard route with HP, a warden, gold, defeat, and optional hardcore death—not push/bank/drowsy resonance exploration.
5. **The shared world is not shared everywhere.** The web surface can mount craft/inventory/trade over one `SharedWorld`, but Discord’s generic portfolio currently opens each over its own demo world (`discord-bot/src/commands/portfolio.rs:22-28`). Companion, adventure aid, faction, tavern, and Descent integrations also have separate-ledger seams.
6. **Complex cross-creature resolution is not a stock predicate.** `ObservedFieldEquals` is real and sufficient for many gates, but the joint nonlinear calculation needs a dedicated verifier. Production cross-node finalized-root/witness transport is also unfinished.
7. **Party and tavern are prototypes, not the social experience.** Party uses a fixed demo roster; the tavern offering is a read mirror. Live join/invite, asynchronous Huddle lifecycle, durable rooms, and designed Discord orchestration remain.
8. **The surfaces are functionally broad and experientially thin.** `ViewNode` has the vocabulary, but current feature offerings are mostly tables, menus, and generated forms. Dragon art direction, information hierarchy, progressive reveal, animation, sound, and mobile/chat-specific interaction all need design work.
9. **Procgen breadth is finite.** The committed generator uses curated tables. Hoardlight needs a substantial authored grammar of room stimuli, reactions, shiny families, and safe coefficient combinations.
10. **Full succinct Descent proofs are not wired.** Replay verification and proof anchors exist, but the real multi-turn daily run-to-fold integration is named unfinished. A STARK can be succinct without being zero-knowledge; privacy claims must remain specific.
11. **Automatafl’s proof path and playable path are not fully one path.** In-proof sealed moves exist, but the offering session and full 5×5 folding limits need integration work.
12. **AI provenance depends on the path used.** Default attestation is a self-signed fixture. Real model provenance is wired on the Bedrock path but depends on live credentials/network. The UI must never collapse those into one green check.
13. **Explorer queries need indexing.** The raw provenance facts are valuable, but fast ancestry, “show every descendant with this knot,” cross-artifact timelines, and provenance-gated mechanics require durable indexes and proof-aware query APIs.
14. **Dragon-faithful art is new.** Existing deterministic sprites prove the approach for gear/cards, not a polished growing creature with readable inherited morphology.

None of these gaps invalidates the vision. They tell us where the irreplaceable work is. The engine has already solved enough of the hard substrate that we should spend our next courage on the parts players can love: one peculiar dragon, one shared impossible burrow, one shiny with a story, and one irresistible room too many.

---

## 13. The line to protect

If Hoardlight becomes a conventional roguelite with blockchain receipts, it has failed.

If dragons become rarity tiers with breeding odds, it has failed.

If Discord becomes a feed of links to the “real game,” it has failed.

If the narrator can award what the rules did not, the Duel gets an AI opponent, failure kills a creature, or provenance is visible only to developers, it has failed.

The thing worth building is more tender and more ambitious:

**A dragon becomes itself through a long chain of small, verifiable encounters. Its oddness composes with the world, with its hoard, with its family, and with other dragons. Players gather around those interactions because nobody—not the server, not the narrator, not the market, not even the designer—can quietly replace the story that really happened.**

Then the little dragon peers into the next room.

Its pocket is full. Its eyelids are heavy. Something down there is making a noise like a spoon learning to sing.

One more room.
