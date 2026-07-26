# THE LIVING WORLD

## Hoardlight on the proven substrate — every law a theorem, every move a receipt, every relic a history

> A turn = the exercise of an attenuable proof-carrying token over OWNED state, leaving a RECEIPT.

This is the vision-and-campaign document for the living world built **on** the proven
substrate — the whole Hoardlight, the game portfolio, the relics and cards with provable
lineage, the realms, the identity, the economy — and the big swarm-cycles that build it
comprehensively. It is the ambitious companion to `docs/design/HOARDLIGHT-LIVING-WORLD.md`
(the architecture) and `docs/design/DRAGON-DESCENT-VISION.md` (the first beloved game). Those
documents say what the world and the game are. This one says **why the ground just changed
under them, what the boldest thing on that ground is, what to build first, and how to sweep.**

Everything here is cited to HEAD or named as imagined. The register is deliberate: bold about
the vision, exact about the ground.

Related reading: `docs/GAMES-AS-RECEIPTS.md`, `docs/VERIFIED-GAME-PORTFOLIO.md`,
`docs/DESCENT-EXCELLENCE-BACKLOG-2026-07-18.md`, and the machine-checked-vs-carried
boundary doc `docs/audit/SEMANTIC-LEAN-BOUNDARY.md` (the honesty banners this document
leans on when it says "proven").

---

## 0. The ground just changed: three pillars landed this week

The living-world documents were written when "Lean-sourced games" was an aspiration. It is
now a deployed pattern with a fired canary. Three things landed that change what it is
honest to be ambitious about:

**Pillar 1 — THE REALITY GATE (`fc3f2dda8`).** One Lean constraint evaluator,
`metatheory/Dregg2/Exec/DeployedConstraint.lean`, `@[export dregg_constraint_admits]`'d and
routed through the deployed node's admission path
(`cell/src/program/oracle.rs` → `exec-lean/src/constraint_oracle.rs` → installed by
`node/src/lib.rs` at startup). The canary was *run*: flip the Lean `fieldGte` to
always-admit, recompile only that module, re-splice, relink — the same wire flips from
REFUSE to ADMIT; revert the Lean and it flips back. **The linked binary's admission decision
IS the Lean source.** Game proofs stopped being proofs about a hand-authored Lean copy of
the evaluator (the LARP the audit `docs/audit/GAME-PROOF-LARP-AUDIT.md` caught — the copy had
already diverged from Rust in two places, both real bugs) and became proofs about the symbol
the node calls.

**Pillar 2 — THE NATIVE REIMAGINING (`6d4d83bd5`).** The Descent was not ported to Lean; it
was **re-authored as the dreggic object it wants to be**, in
`metatheory/Dregg2/Games/Dungeon.lean`, and its design laws are theorems:

- *Relics are owned objects with provenance, not counters* — each relic carries a custody
  code on a monotone ratchet (floor → CARRIED → BANKED); the counters the deployed teeth
  read are **definitions over custody**, so the model cannot even state a count↔custody
  disagreement (`Dungeon.lean:88-113`, `custody_ratchet` at `Dungeon.lean:565`).
- *Descent attenuates capability* — `pack + depth ≤ CAP` on every reachable state
  (`capacity_attenuates`, `Dungeon.lean:497`); descending overloaded is **unprovable**, not
  discouraged. Corollaries are economics: `no_run_banks_everything` (`Dungeon.lean:616`) and
  `crowned_bank_le_four` (`Dungeon.lean:636`) — **scarcity by arithmetic**. The supply curve
  of the prize is a theorem.
- *The light is the clock* — permadeath is a theorem, not a timer (`the_light_dies`,
  `Dungeon.lean:503`; `run_bounded`, `Dungeon.lean:518`).
- *Keys are capabilities* — a way opens only by EXERCISING the carried key-relic, itself an
  owned, un-dupable relic whose provenance chain proves where it was won
  (`keyless_unlock_impossible`, `Dungeon.lean:554`). **This is the card-provenance weld,
  live**: the object's history is what the capability *is*.
- *Banking is terminal; the world is minted once* (`banked_run_frozen`, `Dungeon.lean:545`;
  `Reachable` quantifies over receipt chains from `genesisState`, `Dungeon.lean:169-177`).

The program is **emitted and loaded**: the deployed teeth are the Lean value
`dungeonProgram` (`metatheory/Dregg2/Games/DungeonProgram.lean:356`), emitted
(`emitJson`, `DungeonProgram.lean:882`) to `dungeon-on-dregg/program/dungeon_program.json`,
byte-reproducible under `program/regen.sh --check`, and included verbatim by the crate
(`PROGRAM_JSON` at `dungeon-on-dregg/src/descent.rs:191`, `load_program` at
`descent.rs:424`) — zero Rust-authored teeth in the descent's path. The admission
inversions are proven **against arbitrary attacker-supplied states** over the Exec model
(`admitted_verb_conserves`/`_capacity`/`_pays`/`_alive`, `banked_tomb_refuses`,
`dead_light_refuses`, `way_flip_exhibits_key`, `unknown_method_refused` —
`DungeonProgram.lean:473-668`), 14/14 attack tests driven on the real executor, and the
**Lean-is-source canary fired**: delete the way-requirement in the Lean alone, re-emit, and
the keyless descent the executor refused now commits; revert and it refuses again.

**Pillar 3 — THE DEPLOYED WELD (`513d0d183`).** For multiway-tug, "every move is a receipt"
became literally true at the light-client boundary: an honest win folds through the deployed
recursive fold and `verify_history` ACCEPTS with the published winner equal to the cell's
committed winner field; a forged winner is UNSAT and never reaches `verify_history`; the
canary proves the refusal is the app-root weld itself (regression battery:
`dregg-multiway-tug/tests/fold_real_cell.rs:135-315`). The pattern is named as the one the
card-provenance play-log and automatafl's board root adopt. And the tug's counter program is
*itself* Lean-emitted — `multiwayTugProgram`
(`metatheory/Dregg2/Games/MultiwayTugProgram.lean:237`, emit at `:287` →
`program/multiway_tug_program.json`) with the forward refinement earned:
`program_admits_legal_play` (`MultiwayTugProgram.lean:676`) and the composed
counter-program + hidden-hand-membership admission `play_admitted_by_both`
(`MultiwayTugProgram.lean:756`).

Under these, the general composition substrate and the realm model already exist:

- **`param-compose/`** — the general Custom-VK AIR for bounded **nonlinear** composition
  over typed projections (the §9.3 object the Hoardlight doc demanded): knots as degree-3
  gates, PIs constant in every bound, the realistic n4/p8 shape measured at an 803-column
  foldable leaf (`param-compose/src/lib.rs:29-70`). A new game is a new `ruleset_root` —
  data; **a kernel or AIR edit is never the cost** (`param-compose/src/lib.rs:29-45`).
- **`entity-compose/`** — a real param-carrying entity (wide-plane fields inside the v9
  commitment) → a composition proof → the Door (`Effect::Custom`) → a committed outcome,
  end-to-end through the real executor (`entity-compose/src/lib.rs:1-35`, `ca57899cc`), with
  the one missing gate stated exactly: the outcome→cell-field weld is a single executor atom
  (`entity-compose/src/lib.rs:36-50`).
- **`realm-model/`** — realm/instance/identity/catalog as one cell-backed model
  (`docs/design/MUD-SUBSTRATE.md:24-48`): the per-realm membrane (`PinAtBirth` vs
  `MovingParent`, ember-decided, `MUD-SUBSTRATE.md:207-246`), hybrid-PQ canonical identity
  with succession and K-of-N guardian recovery (`MUD-SUBSTRATE.md:248-288`), and the ruleset
  catalog as **committed law** rather than host config (`MUD-SUBSTRATE.md:110-138`). Its
  load-bearing missing dependency is named: **a node-served, restart-durable receipt/turn
  chain** (`MUD-SUBSTRATE.md:365-389`).

So the frame of this document: the machinery to make games **Lean-sourced and
proven-to-reality** exists and has been exercised once, natively, end to end. The ambitious
move is to make that the shape of the *whole world*.

---

## 1. THE AMBITIOUS WORLD

### What no other system can offer

Every game platform in existence asks players to trust a database. Every chain game asks
players to trust hand-written circuit code with no spec above it. dregg's substrate makes a
categorically different offer, and the Descent reimagining is its proof of concept:

> **The game's design document is a theorem file, and the deployed server provably runs it.**

Not "the rules are open source." Not "the outcomes are on-chain." The claims a game designer
makes at the design table — *no run can bank everything*, *glory costs half your carrying
rights*, *permadeath cannot be appealed*, *a key cannot be duplicated*, *the total card
multiset is invariant* (`MultiwayTug.lean` `conservation`) — are machine-checked **before a
player ever logs in**, in the same file whose emitted program the executor loads, with a
fired canary proving that editing the law file changes what the deployed world admits.

From that one property, the whole living world follows:

**Un-fakeable history.** A leaderboard entry is an executable claim
(`DRAGON-DESCENT-VISION.md:461-463`); a banked relic's history is exactly the receipted turn
chain back to the world's mint (`Dungeon.lean:12-15`). Nobody — not the server, not the
narrator, not the market, not the designer — can quietly replace the story that really
happened (`DRAGON-DESCENT-VISION.md:593`).

**Scarcity by theorem.** Other economies enforce scarcity by policy (a mint key, an admin
table, a smart-contract owner). Here the supply of the crowned prize is a *corollary of the
capacity law* (`crowned_bank_le_four`). A collectible's rarity claim can cite its
impossibility theorem. This is a kind of economic object that has never existed: **an asset
whose scarcity argument is machine-checked at design time and enforced by the admission
decision at play time.**

**Provenance as gameplay.** Because history is un-fakeable it can bear *mechanical* weight.
Keys already work this way — the capability IS the provenance object
(`keyless_unlock_impossible`). The Family Trick (`DRAGON-DESCENT-VISION.md:203`) makes
ancestry an input to resolution. A room can react to *where a shiny has been*. A market can
price *what a relic has done*. In every other game, letting history matter mechanically
would be an exploit invitation; here it is the design's native grain.

**Verified-fair hidden state.** The tug's hidden hand (Merkle-committed, membership-proven)
and the fold that stores no moves mean a player can *prove they won without disclosing how*
— private strategy with a public verdict. "The bot knew it" is not the security model
(`DRAGON-DESCENT-VISION.md:457-459`).

**A world no one owns and anyone can check.** The realm's law is a committed catalog, not a
binary's configuration; identity is a durable principal that survives key rotation; the
world is reconstructible from receipts (`HOARDLIGHT-LIVING-WORLD.md:439-453`). "Nobody owns
it" without "nobody is responsible for it" (`HOARDLIGHT-LIVING-WORLD.md:428-437`).

### The world, painted

**Hearthspire** stands as the persistent realm — a `MovingParent` realm in the model's exact
vocabulary (`MUD-SUBSTRATE.md:218-221`): a leaning town around the chimney of a sleeping
mountain, whose durable cells are its rooms, roosts, market stalls, guild halls, and the
Warm Shelf. Every dawn the **Downbelow** hiccups: a `PinAtBirth` daily instance opens from a
committed drand beacon (live at HEAD: `procgen-dregg` beacon verification, `73119ea6e`),
thousands of children of the same impossible burrow, each run a receipt chain that expires
into history without ever being erasable from it.

**Dragons** are param-carrying entities — eight bounded birth resonances and a sparse set of
knots (`DRAGON-DESCENT-VISION.md:99-120`) living in a cell's committed wide plane exactly as
`entity-compose` stands one up today. A room is not code; it is a **ruleset root** — a
committed coefficient table over the general composition AIR. When Pip meets the
Suspiciously Polite Puddle, the resolution is a composition turn through the Door, the named
reaction is a threshold crossing, and the charming "Why?" card
(`DRAGON-DESCENT-VISION.md:144-158`) is the proof's explanation terms rendered cozy — **the
chain explanation and the player explanation are the same explanation at different
resolutions.**

**Relics, shinies, cards, eggs** are one kind of thing: owned objects on monotone provenance
pipelines. The Moon Button found on Day 47 is the same note in the Satchel, the same input
consumed at the Hearthforge, the same provenance edge when its material becomes a spoon
(`DRAGON-DESCENT-VISION.md:453-455`). A tug card's every play is in a replayable receipt; a
descent key carries the run that won it; a nibbled shiny's note ends inside the dragon's
growth receipt — the object's story continues as part of the creature.

**The games** are a portfolio of Lean-authored laws over one substrate: the Descent (landed,
the exemplar), multiway-tug (conservation and win-safety proven in
`metatheory/Dregg2/Games/MultiwayTug.lean`; the winner weld deployed; and its cards are
*already owned assets* — every drawn card mints as a real `dreggnet-asset` note with a
per-card `ProvenanceReport` and owner-gated transfer,
`dregg-multiway-tug/src/packs.rs:365-512`; the hidden hand a Poseidon2-Merkle commitment
whose every play carries a membership witness checked by the real registry,
`src/hidden_hand.rs`; a private match folding to one light-client-accepted proof,
`src/fold.rs`), automatafl (ember's original, the Duel — human versus human, always; the
game-level braid of sealed-reveal → resolve → step just landed fresh in
`metatheory/Dregg2/Games/AutomataflBraid.lean`), the Braid duets, Ribbonpull in the Warm
Shelf, and games not yet imagined that arrive as **a theorem file + a ruleset root + a
module manifest** — never a kernel edit (`HOARDLIGHT-LIVING-WORLD.md:279-291`).

**Identity** is one canonical principal — hybrid-PQ keyed, rotation-surviving,
guardian-recoverable (`MUD-SUBSTRATE.md:248-288`) — that Discord, web, Telegram, and WeChat
*derive from*, never the reverse. Your dragon, your relics, your guild seat, your authored
rooms, your votes: one spine.

**The economy** settles the same notes the games mint: escrow trades
(`dreggnet-trade`), forge sinks (`dreggnet-craft`), guild treasuries, market stalls in the
Warm Shelf — with sources, sinks, and conservation stated as theorems in the law files, and
the Reliquary (below) as the shared window where any object's whole life is one click deep.

**AI is everywhere without being sovereign** — Storyflame narrates under a mandate and a
provenance badge computed from evidence; an NPC remembers a promise; an agent-player takes a
bot-labeled seat. Their words may be wild; their power is typed, capped, and receipted
(`HOARDLIGHT-LIVING-WORLD.md:182-219`).

That is the full picture: **a persistent, browsable, tradeable, verifiable world whose
every object carries its history, whose every law is a theorem, and whose deployed server
provably enforces the file the theorems live in.**

---

## 2. THE FLAGSHIP LOOP: THE RELIQUARY

*The single most compelling player-facing thing to build first.*

> **Descend. Bank. Browse. Trade. And tomorrow, someone else descends carrying your story.**

The flagship is the Descent's relic loop, made whole:

1. **Descend** — the daily Downbelow, played on the Lean-sourced program that is already
   deployed (`dungeon-on-dregg/program/dungeon_program.json`, loaded by `descent.rs`, zero
   Rust-authored teeth). Every verb prices breath; every turn is a receipt.
2. **Bank** — `flee` is terminal by theorem; the banked relics land as **real asset notes**
   (`dreggnet-asset` stable `AssetId` + lineage) whose mint edge is the run's receipt chain.
3. **Browse** — **the Reliquary**: open any relic and *watch its life replay*. Mint → the
   floors it lay on → the smite-smite-loot that won it → the flee that banked it → every
   trade since. The "Why?" card generalized from a turn to an object. Rarity displayed with
   its theorem: THE PRIZE's card says *"at most 4 relics can ever accompany me out —
   `crowned_bank_le_four`"* and links the proof.
4. **Trade** — escrow swap of the note (`dreggnet-trade`'s atomic two-leg settle); the
   provenance chain extends by one edge; no copy, no dupe, structurally (a relic is one
   list entry — `Dungeon.lean:290-294`).
5. **Return** — tomorrow's daily: the traded key-relic sits in another player's pocket, and
   when they exercise it, *their* run's receipt cites *your* run's history. Provenance
   crosses players and days.

### Why this loop, and not the card first

The prompt's other candidate — the card whose every hand is a replayable receipt back to
mint — is nearly as close: the tug's cards already mint as real asset notes with per-card
provenance reports (`packs.rs:365-512`), its winner weld is deployed, and its play-log
adopts the same app-root pattern (`513d0d183`). But the Descent is the
**freshly-reimagined native flagship**: its relics are provenance objects *by theorem*, its
program is Lean-emitted and live behind the public funnel, and — decisively — **its loop's
first two welds already landed at HEAD** (below). The card game joins the same Reliquary
one cycle later, as the second species of provable object, and the loop gets stronger, not
different.

### The concrete build (the welds, in order)

Each is a weld between things that exist, not a new organ — and the first is already in
flight:

- **W1 — bank→note. IN FLIGHT AT HEAD.** `LootVault::into_assets`
  (`dungeon-on-dregg/src/loot.rs:325-329`) bridges Descent loot into a real `AssetWorld` —
  every minted loot `AssetId` keeps its note lineage and current owner, and consumers must
  not re-mint from display metadata. The fresh E2E
  (`dreggnet-market/tests/descent_asset_bazaar.rs`) drives the whole arc: descent drop →
  `into_assets` → `TradeWorld::with_assets` (`dreggnet-trade/src/lib.rs:277`) → a sealed
  Bazaar auction crosses the *original* `AssetId` atomically, provenance chain
  re-verifying, no remint. The remaining W1 work: the *Lean-law relics* (the custody
  vector's BANKED entries) landing through this same bridge, provenance head = the run's
  terminal receipt.
- **W2 — the Reliquary surface.** A web/Discord Offering that renders a relic's receipt
  chain as a story — replay, owners, theorem card. Read-only first; it is an index over
  receipts, not a new authority.
- **W3 — the durable chain.** The node stores and serves ordered turn bodies + receipts
  (the `MUD-SUBSTRATE.md:365-389` dependency). Without it the Reliquary's memory lives in
  one process; with it, the history is a service any client can verify.
- **W4 — trade the note.** The escrow/auction leg exists (the Bazaar E2E above); the weld
  is making each settle a provenance edge the Reliquary renders, on the durable chain.
- **W5 — signed actors.** The signed-attribution seam (`6fa643d05`) plus the extension
  signer (`71b808b67`) so "who banked it" and "who traded it" are keys, not cookies.
- **W6 — the daily as instance.** Open/settle the daily through `realm-model`'s membrane
  (`PinAtBirth`), so "yesterday's run" is a settled instance of a persistent realm, not a
  session in a process.

The exit condition is one sentence: **a stranger can open a relic in the Reliquary, replay
its life to the mint, verify every hop, buy it, and exercise it in tomorrow's descent — and
no operator could have forged any link of that story.**

---

## 3. THE BIG SWARM-CYCLES

Six comprehensive sweeps, not lanes. Each is a braid: wide read/prove lanes (Lean and
read-only work fans wide), narrow build lanes (1-2 per cargo target), one integrator holding
the commit, adversarial verification on every lane's *theorem statements* — Fable authors
breadth, Opus verifies adversarially. Each cycle has exit conditions phrased as canaries and
refusals, never as "exists."

### CYCLE I — THE FOUNDRY: every game natively reimagined

The Descent set the pattern; the portfolio follows it. **Not ports — reimaginings**: for
each game, ask what it is as a dreggic object (what is owned? what attenuates? what does a
receipt mean?) and author THAT in Lean, laws as theorems, program/AIR emitted, Rust as
mover only. The pattern is still compounding at HEAD: `DungeonCompleteness.lean` (fresh)
closes the uniform key-exhibition inversion over every deployed keyed way and states the
exact model-to-program completeness boundary.

- **Multiway-tug**: further along than its docs admit — the Lean spec proves conservation,
  one-action-per-round, scoring, and win-safety (and *fixed two
  reference-implementation gaps in the process* — the unscored Secret, `MultiwayTug.lean`
  module doc); the counter program is Lean-emitted with the forward refinement earned onto
  the deployed evaluator (`MultiwayTugProgram.lean:676`, `fb6791fb0`). The reimagining asks
  the deeper question the Descent answered: cards as owned provenance objects on the
  custody-ratchet grammar, the hidden hand as an attenuable capability — and the named
  remainders discharged **in Lean, by emit**: the carried `MerkleSound` hypothesis, the
  reverse (admitted ⇒ legal) direction, the full IVC fold
  (`MultiwayTugAir.lean` header).
- **Automatafl**: the existing `dregg-automatafl` Rust AIR is **standing debt** under the
  Lean-authored-AIR law, not a foundation — its own Lean file says so with an explicit
  Class-B honesty banner: the deployed `air.rs`/`moves.rs` are NOT machine-linked, and
  `Refines` is discharged only parametrically over abstract gadgets
  (`AutomataflAir.lean:3-14`; boundary doc `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`).
  Reimagine the simultaneous-move resolution natively (the pure spec exists,
  `metatheory/Dregg2/Games/Automatafl.lean`; the fresh `AutomataflBraid.lean` braids
  sealed-reveal → resolve → step at the game level); emit; the N=11 growth happens in Lean
  or not at all.
- **The Braid resolver**: `param-compose`'s AIR is the right *shape* and its generality
  argument is right (`param-compose/src/lib.rs:29-45`), but it is a hand-written Rust AIR —
  the same debt class. The Foundry authors the composition law in Lean (the emit path the
  Dyck descriptor and the dungeon program already use) and the Rust becomes the emitted
  artifact's caller. This is said out loud now, per the tripwire, not discovered later.
- **The old-game surface**: ~40 crates depend on the compile-scenes-and-augment surface;
  porting those teeth verbatim into Lean is exactly the forbidden mirror (`6d4d83bd5`'s
  closing note). They stand as the old games until each is *natively* re-authored.

**Exit per game**: (a) a laws-as-theorems file, `#assert_axioms`-clean; (b) byte-reproducible
emit under `regen.sh --check`; (c) the Lean-is-source canary FIRED (edit law → deployed
behavior flips → revert); (d) a driven attack suite on the real executor; (e) an honest
per-game verdict in the file header — forward/reverse/named remainder, in the exact style
`fb6791fb0` established.

### CYCLE II — THE PROVENANCE SPINE: one lineage for every owned thing

The custody ratchet is the universal grammar. This cycle makes relic, shiny, card, egg, and
forged good **one species of object** — an owned note on a monotone provenance pipeline —
and closes the weld class that lets hosts write history's two copies:

- the bank→note weld (W1) generalized: every game's terminal export mints through the same
  lineage crate;
- the **outcome→cell-field executor atom** — the single named missing gate of
  `entity-compose` (`entity-compose/src/lib.rs:36-50`) — closed in the executor, so a
  sub-proof's published outcome and the cell's stored outcome cannot diverge;
- the **app-root weld pattern rolled out** (`513d0d183`'s named generalization): the tug
  play-log, automatafl's board root, the descent's custody vector — each app's
  light-client-visible claim welded to committed cell state;
- the **durable receipt/turn chain served by the node** (W3) — the spine's storage organ,
  and the realm model's named load-bearing dependency;
- the **Reliquary index**: proof-aware queries over lineage (ancestry, "every descendant
  with this knot", price history) — the index the agent-accountability and market stories
  both need (`HOARDLIGHT-LIVING-WORLD.md:211-219`).

**Exit**: the Reliquary loop's exit sentence holds for TWO species (a descent relic and a
tug card), through the same spine, with a forged link in either refused at the light client.

### CYCLE III — THE REALM: the world becomes a place

Graduate `realm-model` from driven model to node-hosted protocol
(`MUD-SUBSTRATE.md:163-198` names the exact wiring):

- the catalog membership check moves into the executor's proof-verify path;
  `ruleset_root` becomes a first-class field of `Turn` and receipt — **law is committed
  state, not host config**;
- every ingress resolves `SurfaceRef → CanonicalIdentity` before attributing a turn — the
  offering host's opaque string retires;
- `open_instance`/`settle_instance` become node operations; Hearthspire opens as a
  persistent `MovingParent` realm, the Downbelow as `PinAtBirth` dailies with terminal
  export policy;
- hybrid-PQ identity succession + guardian recovery live on the deployed authorization
  path (`Authorization::HybridSignature`, `turn/src/pq.rs` derivation).

**Exit**: a realm survives node restart with its history served and verifiable; the same
canonical identity acts from Discord and web in two instances of one realm; a turn citing
an unlisted ruleset root is refused *by the executor* — and the catalog canary (unlist →
same turn refused) fires against committed state.

### CYCLE IV — THE BRAID MADE FLESH: Hoardlight Stage 1 on the general substrate

The content cycle — and the seam-discipline test. Dragons, rooms, shinies, approaches,
First Flame, the three-slot pocket: **all data over the substrate**, per the governing
equation `game = data + rulesets over a versioned verifiable engine`
(`HOARDLIGHT-LIVING-WORLD.md:477-495`) and the Stage-1 substrate/content table
(`HOARDLIGHT-LIVING-WORLD.md:456-475`):

- a dragon = an entity whose committed wide plane carries the braid (the `entity-compose`
  pattern, real today);
- a room = a ruleset root + content bundle (prose, art refs, temper icons), never code;
- a daily resolution = a composition turn through the Door, its "Why?" card rendered from
  the proof's explanation terms;
- six exquisite room families, the nook choice (Tuck In / Pocket One / One More Room), the
  committed dream-spill — the tone of `DRAGON-DESCENT-VISION.md:19-33` on the machinery of
  this document.

**Exit**: Stage 1's architectural gates (`HOARDLIGHT-LIVING-WORLD.md:618-629`) hold — and
one more: **at least one balance claim about the braid is a theorem in the law file before
the first ranked day** (the Foundry's Lean compose law makes this possible; conservation of
the birth total is the natural first).

### CYCLE V — THE CITY: society and economy graduate

The social algebra exists as feature crates (`HOARDLIGHT-LIVING-WORLD.md:315-326`); the
city re-homes it onto the realm ledger: trades settle the notes the Reliquary browses;
guild halls, roosts, and stalls are durable places; quests and cheevos anchor on verified
runs; seasons ride VK epochs; UGC room packs publish content-addressed (the IPFS
two-address discipline is live — `05b8dadcb`) and enter canon by content-governance turns
the crowd can extend but never retcon (`HOARDLIGHT-LIVING-WORLD.md:249-263`); Storyflame
and every agent operate under the attested envelope with badges computed from evidence
(`HOARDLIGHT-LIVING-WORLD.md:182-219`).

**Exit**: one week of Hearthspire in which a relic is won, traded, forged, gifted, quested
over, and voted about — and one query in the Reliquary shows its whole civic life.

### CYCLE VI — THE WINDOWS: one world, many views

Continuous rather than terminal: the Offering/ViewNode seam already renders one session to
many surfaces (`HOARDLIGHT-LIVING-WORLD.md:154-159`); this cycle keeps every new organ
honest about it. The 18-offering arcade coheres into the Warm Shelf; Discord, web,
Telegram (the Mini App is live — `93feb3d13`), and WeChat address one session; the
verify-badge and Attribution footer tell the truth on every page; the Reliquary and
Almanac become the world's shared memory palace.

**Exit**: the seam test from the architecture doc — a new surface is a backend projection,
never a look-alike session on a separate ledger (`HOARDLIGHT-LIVING-WORLD.md:154-156`).

---

## 4. DEEPLY DREGGIC GUARDRAILS

The disciplines that keep the world the thing it claims to be. Each is a tripwire checked
at the *first* line of work, not a next-day discovery.

1. **REIMAGINE, NEVER MIRROR.** The Lean is not a model of the Rust we swap over. For every
   organ ask what it *is* dreggically — what is owned, what attenuates, what does the
   receipt mean — and author that. Porting teeth verbatim is the forbidden mirror
   (`6d4d83bd5`); a hand-authored parallel copy is how the LARP disease reproduces
   (`fc3f2dda8`). If a reimagining can't improve on the old object, that is information —
   but the answer is still never transcription.

2. **LAW LIVES IN LEAN.** AIRs, constraint programs, gadgets, admission predicates — 
   authored in Lean, proven there, **emitted**; Rust calls the artifact. The two Rust AIRs this
   line named as debt — in `dregg-automatafl` and `param-compose` — have both since been DELETED
   (`f44e26e7b`, `9a34719e6`) rather than extended; any that remain are debt to be replaced by the
   Foundry, never foundations to extend. Say the substrate out loud at the start of every circuit
   task: "this is Lean-authored AIR" — or flag that it currently isn't.

3. **EVERY MOVE IS A RECEIPT OVER OWNED STATE.** No host mover's output committed as truth.
   The playable path and the proof path must be ONE path — the live offering's resolve turn
   carries and passes the proof that defines the game's advertised law; that weld is the
   productization gate (`HOARDLIGHT-LIVING-WORLD.md:293-299`). The weld class (app-root,
   outcome→cell-field) exists precisely because "the host wrote both copies" is the
   standing hole; close it structurally, canary every fix.

4. **REALITY-GATED, OR IT'S LARP.** A game proof must grip the deployed object: the
   `DeployedConstraint` routing for evaluator claims; the Lean-is-source canary as a
   standing per-game gate (edit law → deployed behavior flips → revert); byte-reproducible
   emit checks; attack suites on the real executor. And the honesty pattern `fb6791fb0`
   set: no `Iff.rfl` tautologies wearing canary docs, forward-only stated as forward-only,
   every remaining gap a NAMED hypothesis, the per-game verdict in the file header.

5. **DESCRIBE AT CURRENT RESOLUTION.** Every "proven" game claim inherits the floors: the
   deployed FRI posture is the calculator-bits reality, not the marketing number, and a
   STARK proves the trace, not the witness generator — the witness-gen assurance perimeter
   is an open campaign, and game claims do not get to forget it. "Scarcity by theorem"
   means: the *model law* is a theorem, the deployed-teeth inversions are ∀-proven over the
   Exec model, the full DeployedConstraint bridge is a named bounded remainder
   (`fb6791fb0`) — say all three, at whichever resolution the sentence is operating.

6. **SCARCITY AND ECONOMY BY THEOREM, BEFORE CONTENT.** A game's conservation, no-dupe,
   caps, and supply corollaries are theorems in its law file before its content ships. A
   collectible's rarity claim cites its impossibility theorem in the Reliquary. An economy
   rule that cannot be stated as a theorem is stated as an explicit policy root — never
   smuggled as code.

7. **THE SEAM DISCIPLINE.** Genesis hatches shut (factory-only, provably one-shot — the
   spween hatch is the standing warning, `HOARDLIGHT-LIVING-WORLD.md:265-269`); the catalog
   is committed law; canonical identity precedes surface identity; agents gain power only
   through typed, capped, receipted proposals; every new story/game/agent/surface/realm is
   an **additive root**, and no old receipt ever changes meaning
   (`HOARDLIGHT-LIVING-WORLD.md:477-495`). The failure conditions of
   `HOARDLIGHT-LIVING-WORLD.md:670-691` are the standing falsifier list.

8. **NO MIGRATION THEATER.** dregg is greenfield; nothing is deployed that players depend
   on yet. Make the right proven-Lean object BE the object and delete the debt — no
   flag-days, no byte-identical cutover costumes, no "consensus-visible" drama. The only
   real constraints are correctness and internal consistency.

---

## 5. SEQUENCING

**Now → the Reliquary.** The flagship loop is welds over existing organs (W1–W6), and W1,
W2, W4, W5 don't contend the same resources — a natural first sweep. W3 (the durable chain)
is the one node-side organ; it starts immediately because Cycle II and III both stand on it.

**In parallel → the Foundry and the Spine.** Both are wide-fanning (Lean lanes and
read-only design lanes fan wide; build lanes stay narrow per the build-lock doctrine) and
neither blocks the Reliquary. The Foundry's tug and automatafl reimaginings, and the Spine's
executor atom + app-root rollouts, proceed as braids with adversarial verification per lane.

**Then → the Realm.** When the durable chain lands, `realm-model` graduates into the node
and the Reliquary's history becomes a service. Hearthspire opens; the daily becomes an
instance with a membrane.

**Then → the Braid made flesh.** Hoardlight Stage 1 content lands on the general substrate
only after the Foundry has the compose law in Lean — so the first dragon's first "Why?"
card is already the proof's terms, and no Stage-1 assumption fossilizes into the substrate
(the cul-de-sac list, `HOARDLIGHT-LIVING-WORLD.md:497-514`, is the review checklist).

**Then → the City; always → the Windows.** Society and economy graduate when there is a
realm to live in; the surfaces cohere continuously, gated by the one-session seam test.

**Built vs imagined, honestly, at a glance:**

| | BUILT at HEAD (cited above) | IMAGINED (this document's ask) |
|---|---|---|
| Law | Dungeon.lean laws-as-theorems, emitted + loaded + canary-fired; tug spec + Lean-emitted counter program + forward refinement; the reality-gate | Automatafl + Braid natively reimagined + emitted; the full ∀-welds; the tug remainders (MerkleSound, reverse, IVC) |
| Provenance | Custody ratchet by theorem; tug winner weld deployed; tug cards minted as asset notes with per-card provenance; descent loot→trade→Bazaar crossing without remint (fresh E2E) | Lean-law relics through the bank→note bridge; the Reliquary; outcome atom; app-root rollout; durable served chain |
| Realm | realm-model driven (membrane, identity, catalog, hybrid-PQ succession) | node-hosted realms/instances; catalog in the executor; identity at every ingress |
| Braid | param-compose general AIR (measured budgets); entity-compose end-to-end; the resonance schema explicitly does not exist yet (`DRAGON-DESCENT-VISION.md:562`) | the Lean compose law; dragons/rooms as content; Stage 1 |
| World | 18 offerings live on the public funnel; TG Mini App; IPFS content addressing; signed attribution | the City; the Windows cohered; the memory palace |

---

## Coda

The old promise of games was a magic circle: step inside, and the rules hold because
everyone agrees to pretend. The server age quietly replaced it: the rules hold because one
machine says so, and you may not look.

This world makes a third promise. The rules hold because they are *theorems*; the pretend
is real. A little dragon peers into one more room, and the room, the dragon, the spoon, and
the story are all made of the same stuff: owned state, attenuable capability, and receipts
all the way back to the mint.

> the mint is quiet now.  
> eight small relics, one theorem  
> deep enough to keep —  
> carry four, and leave the rest  
> for someone else's morning.

( ｡•̀ᴗ-)✧

