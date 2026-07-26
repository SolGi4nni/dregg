# The MUD: what world model exists, what game is missing, and the plan

ember: *"i want to get a real MUD going with a real economy and real whatevers."*

**The blunt answer: this is an engine looking for a game, and the game is a PLACE, not a dungeon.**
Six MUD substrates exist in this repo. Each one works. None of them knows about any of the others,
and not one of them is a place a second person can walk into. The economy is not missing either:
faucet, sink, atomic swap, sealed-bid auction, owned notes with provenance, and a monotone standing
ledger are all built and all tested. What is missing is the thing that makes an economy an economy
instead of a demo, which is **a reason to want something someone else has**.

This document is scholarship first, a design argument second, a critique third, and a plan fourth.
Everything is cited to HEAD. Where a prior lane's number was wrong I say so and give mine.

⚑ **Working-tree note #1 - the narrator lane LANDED while this was being written.** The brief said
to assume a sibling lane was generalising `legal_commands` and to build on it. **It is in the tree
now** (uncommitted: `M dungeon-on-dregg/src/narrator.rs`, `M spween-dregg/src/world.rs`,
`M dreggnet-offerings/src/dungeon.rs`, `M .../dungeon/narrated.rs`), and it is better than the
brief described. `legal_commands` is now `view.commands()` - a plain read of a set
`scene_view` derives **once, from the compiled scene**, then filters through
`WorldCell::probe_choice(..).offerable()` against committed state. So plan item 1 below is DONE, and
it closed a second wound for free (§3.4). Line numbers in those four files are moving under me;
where I cite them I name the **symbol** first and treat the line as advisory.

⚑ **Working-tree note #2.** `metatheory/Dregg2/Games/Dungeon.lean` is **modified and
mid-surgery** in the shared tree right now: the header and `abbrev CAP : Nat := 7` (`:145-153`) have
been flipped to a `CAP 8 -> 7` + key-hangs-in-the-door design, while `step .unlock` (`:406-411`)
still leaves custody untouched and two live proof steps still assert `have hCAP : (CAP : Nat) = 8
:= rfl` (`:762`, `:809`). At HEAD the file is self-consistent at `CAP := 8`. That lane owns the
Descent's rules; **nothing in this document touches `descent.rs` or `Dungeon.lean`**, and any plan
item that leans on Descent constants should read the Lean, not the `dungeon-on-dregg/src/descent.rs`
mirror or the (Jul 25) emitted `program/dungeon_program.json`, whose 240 `affineLe` teeth all still
carry `c: 8`.

---

## PART 1 - SCHOLAR: what world model actually exists?

### 1.1 The measured surface, corrected

The prior lane measured the playable surface and its numbers mostly hold. Corrections:

| measure | prior lane | measured here | cite |
|---|---|---|---|
| scenes in `dungeon-on-dregg` | 7 | **7** | `lib.rs:285, 515, 1487, 2201, 2986, 3936, 4445` |
| scenes REGISTERED in the overworld | 4 | **4** ("The four wired universes") | `dungeon-on-dregg/src/overworld.rs:86-161` |
| rooms | 20 | **20** | per-scene: 3/3/3/2/4/3/2 |
| choices | 48 | **51 authored** | raw `^* [` count across the seven DSL consts |
| Keep prose | "3 rooms / ~120 words" | **3 rooms; 182 words total** (59 description + 123 choice labels); the narrator-visible subset was **~101** | `lib.rs:376-463` |
| narrator reach | 3 rooms | **3 rooms at HEAD, 20 in the working tree** - `scene_view` now derives the legal set from the compiled scene, so the narrator runs on any registered scene | `narrator.rs::scene_view`, `::legal_commands` |
| `dungeon-on-dregg` src | - | **31,051 lines** | `wc -l src/*.rs src/dsl/*.rs` |
| whole game layer src | - | **~215,000 lines across 22 crates** | `dreggnet-web` 42k, `dungeon-on-dregg` 31k, `dreggnet-market` 30k, `dreggnet-offerings` 24k, ... |
| `attested-dm` prose | "~75 rooms, ~7,400 words" | **95 rooms** (72 Rust-constructed + 23 in `.dungeon` files), **~2,700 words** of in-world prose, against **~32,600 words** of design commentary | `attested-dm/src/game.rs:3612-5207`; `attested-dm/dungeons/` |

Two of the prior lane's reachability claims need splitting:

- **`dialogue.rs` (960 lines) really has zero code importers.** Every repo-wide hit on
  `dungeon_on_dregg::dialogue` is a doc comment in `dreggnet-faction/src/lib.rs` and
  `dreggnet-quest/src/lib.rs`. Same for `skills.rs` (only `examples/skills_spells.rs`).
- **`combat.rs` and `loot.rs` are NOT test-only.** `combat::Arena` is a real dependency of
  `dreggnet-party/src/encounter.rs:45` and `dreggnet-surfaces/src/party.rs:35`; `loot` is a real
  dependency of `dreggnet-craft/src/forge.rs:13`, `dreggnet-offerings/src/native_descent.rs`,
  `dungeon-on-dregg/src/descent.rs`. They are reachable from a *served offering*. What is true is
  the sharper thing: **no ROOM reaches them**, because a room cannot express a fight.

⚑ **And one finding of the same class the prior lane was hunting, that it did not name.** The whole
game layer is excluded from the workspace's `default-members`. Of 223 `members` in
`/Users/ember/dev/breadstuffs/Cargo.toml:38`, **74 are absent from `default-members` (`:45`)**, and
they include `dungeon-on-dregg`, `mud-dregg`, `attested-dm`, `spween-dregg`, `narrator`,
`dreggnet-web`, `dreggnet-offerings`, `dreggnet-market`, `dreggnet-catalog`, `dreggnet-tavern`,
`dreggnet-guild`, `dreggnet-faction`, `dreggnet-gear`, `interactive-fiction-demo`. A bare
`cargo test` at the workspace root **never reaches the game.** This is the GATING-DEFAULTS-TO-SILENCE
class applied to the entire product: not broken code, just code that emits no line when it rots.

### 1.2 What a world model IS here: rooms and choices, plus one thing a MUD has never had

The model is **a room graph whose every edge is a constraint the executor re-checks.** That is the
whole idea and it is genuinely realised.

A `.dungeon` file (`dungeon-on-dregg/src/dsl/`) parses 15 top-level directives
(`parse.rs:492-588`: `name:`/`title:`, `start:`, `player_hp:`, `objective:`, `lose:`, `use`,
`status`, `consumable`, `room`, `npc`, `oath`, `hostile`, `combat`, `spell`, `light`) plus block
sub-directives (`items:`, `exit`, `about`, `topic`, `branch`, `victory`, `death`, `weapon`,
`armor`, `dark:`, `refuel`, `stranded`). `compile_world` (`compile.rs:919`) lowers it to a
`spween::Scene`, hands that to the v0 compiler, augments it, and then **re-derives the expected
constraint multiset from the source and compares both directions** (`check_lowering`,
`compile.rs:99-113`) - no missing teeth, no phantom teeth. A gated exit becomes a real
`FieldGte`; `requires flag oath is 2` becomes a real `FieldEquals`; `topic ... once` becomes a
spend counter `{once_tag <= 0} ~ once_tag += 1` lifted to a post-state `FieldLte`
(`compile.rs:15-32`). Every case additionally carries a **nav pin** and **write confinement** -
`Immutable` on every var the choice does not legitimately write - so an item grant stapled onto
another method's turn is an executor refusal, not a bug report (`compile.rs:69-80`).

**That is what `spween-dregg`'s world-cell gives a room that a normal MUD room does not.** In a
normal MUD, the room is a server object and the rule is an `if` in the server. Here the rule is a
`CellProgram` case the verified executor re-checks on every touching turn, the cell id is
`blake3::derive_key("spween-dregg-world-owner-v1", scene_id || seed)` so the same scene reproduces
byte-identically (`spween-dregg/src/world.rs:357`), and a choice whose gate did not fully lower
to teeth is **refused outright** rather than committed on a handler's word
(`world.rs::require_fully_gated`, ~`:888`). The dungeon master cannot cheat, because there is no privileged path: an
author-supplied `WriteOnce` or `Monotonic` is enforced identically to a compiler-emitted one,
"the executor never distinguishes who authored a case" (`world.rs::deploy_compiled`, ~`:308`).

### 1.3 What the DSL refuses, and why the refusal is a lie about the substrate

`reject_unsupported` (`compile.rs:685-736`) refuses nine constructs **by name**: `hostile`,
`combat`, `spell`, spell-rules, `consumable`, `status`, `light`, `lose:`, `player_hp:`. The
`salt_reliquary.dungeon` author's own `REMAINING WALLS` block is the honest field report:

> **W1. NO COST.** `salt_tithe` is still in hand after Ferrun takes it. ... Tolls, offerings,
> ammunition, rations - **every economy is unwritable.**
> **W3. ONE ENDING.** ... the drowned's ending, where you leave the crown on the bier, is not
> representable.
> **W4. NO RISK.** ... A deployed authored dungeon is a puzzle box you cannot die in.
> **W7. NO CHECK.** Nothing rolls.

⚑ **Two facts turn this from a design ceiling into a to-do list.**

**First: attested-dm already implements all nine, and executes them.** The parser
`dungeon-on-dregg/src/dsl/parse.rs` is a near-verbatim port of
`attested-dm/src/dungeon_dsl.rs` (934 changed lines of 1,839; error messages preserved), and
attested-dm's `resolve_action_rng` (`attested-dm/src/game.rs:1712`) dispatches into every single
one: light's dark-room refusal at `:1776-1782`, oil burn + status tick + poison HP in `move_effect`
at `:2395-2434`, spells at `:1962`, refuel at `:2042`, consumables at `:2076` (which emits
`WorldEffect::Batch([effect, ConsumeItem])`), HP combat at `:2113`, one-shot hostiles at
`:1905-1931`, `lose:` at `:2506-2511`. Four `.dungeon` files in `attested-dm/dungeons/` exercise
them, and `attested-dm/tests/dungeon_dsl.rs:47/88/419/462` play them to a win. **The forward port took the
static data and the parser and left the resolver behind.** `dsl/ir.rs` is a strict subset of
attested-dm's `GameWorld` - zero dynamic state, zero resolver, zero effect vocabulary - plus
exactly one addition, `OathRule` (`ir.rs:457-471`), which is the best construct in either grammar.

**Second, and this is the sentence that matters most in this whole document: the executor tooth for
COST already exists, is documented with `gold` as its worked example, and is clamp-safe.**
`spween-dregg/src/compiler.rs:829-851`:

> The lift `pre op base <=> post op (base+d)` assumes `post = pre + d` exactly, but the executor
> clamps a `Modify` at zero. When the shifted threshold lands `<= 0`, the clamp makes the lifted
> bound vacuous - e.g. `{gold>=50} ~ gold-=50` shifts to `FieldGte(gold, 0)`, always true, so a
> broke buyer's clamped-to-zero purse still passes. `FieldDelta{index, d}` requires `post == old +
> d` ... so the two teeth together are equivalent to the pre-gate exactly.

And `cross_var_teeth` (`spween-dregg/src/compiler.rs:936`) lowers `{ gold >= "$price" }` - **a real cross-field
price** - to `FieldLteOther` / `HeapFieldLteOther`.

So: **"you cannot author a dungeon where a player can spend anything" is true of the grammar and
false of the substrate one layer beneath it.** W1 is not an engine gap. It is a missing
`Effect::Modify { delta: -1 }` in a lowering function and a missing keyword in a parser. That is
the highest-value fact in this document and it reframes the whole plan.

### 1.4 The party surfaces

`dreggnet-party` seats exactly four: `Role::ALL = [Tank, Scout, Mage, Healer]`
(`dreggnet-party/src/lib.rs:162`). Two different enforcement models:

- **The party world** (`lib.rs:535-637`) is the strong one: one `starbridge_v2::world::World`, eight
  cells, per-seat mandates granted at `:597-602` so each role holds a cap to exactly its own cell.
  Role cells carry `WriteOnce{ROLE_SLOT}` (once per encounter, `:548-554`); the fork gate carries
  `WriteOnce{GATE_SLOT}` so a resolved fork is final (`:564-570`); the loot cell carries four
  `WriteOnce`s (`:583-593`). ⚑ And there is already a **shared budget**: the focus cell carries
  `FieldLteField{spent <= budget}` with `FOCUS_BUDGET = 40` and `FOCUS_COST = 15` (`lib.rs:95-99`,
  `:571-581`) - **exactly two casts across the entire party.** That is a scarce common-pool
  resource enforced by a tooth. It is the only one in the repo.
- **The crew descent** (`crew_descent.rs:36-40`) seats the same four onto the Descent with
  role-owned verbs (Bulwark takes relics, Striker smites, Pathfinder unlocks and delves, Mender
  climbs out) and two irreversible verbs behind a Council vote (`:359-402`). Its own honest
  residual, `crew_descent.rs:82-88`: **the role-to-verb ownership is enforced by this layer plus
  the mover's signature, NOT by an executor capability - "the Descent's cell cannot express one."**
  `crew_descent` and `crew` have zero consumers outside the crate.

Formation exists and is good: `PartyLobby` (`lobby.rs`) with claim/ready/leave/launch, a
domain-separated blake3 event chain (`:536-557`), replay verification that refuses a
valid-but-truncated prefix (`:385`). Fog exists and is honest about itself: `render_for`
(`dreggnet-offerings/src/lib.rs:678`) plus a **declared** `hidden_information` flag (`:829`),
because a frontend cannot learn hiddenness by diffing renders (`:807-828`), and an `Audience::Shared`
branch that structurally *cannot* call `render_for` (`audience.rs:70-88`). It is tested hard - the
generalized fog harness (`dreggnet-web/tests/catalog_flow_harness.rs:1355`) exists precisely because
tug once leaked a seat's hand **through button labels** while its fog sections were correct. But
read its own scope line (`audience.rs:14-16`): *"It does not turn host-visible secrets into
cryptographic no-viewer custody."* The cryptographic version - vision as a cap frustum plus a
knowledge-of-secret proof, `no_peek_for_real_only_the_secret_holder_can_prove_vision` - exists at
`starbridge-web-surface/src/game.rs:2403` and **has zero consumers in `dreggnet-*`.**

### 1.5 ⚑ There are SIX MUD substrates, and none of them knows about the others

This is the central scholarly finding. The repo does not lack a MUD. It has six, at different
altitudes, sharing nothing.

| # | substrate | what it proves | status |
|---|---|---|---|
| 1 | `spween-dregg::WorldCell` | a room graph whose gates are executor teeth, translation-validated | **live** - the target of the `.dungeon` compiler and every served offering |
| 2 | `starbridge-v2/src/mud.rs` (1,804 lines, 15 tests) | a room is a cell holding its contents; a locked door is an absent cap; pickup moves the cap and the item cannot be duped; a multi-hop trade conserves value at `Sigma-delta = 0`; a five-test speech/presence suite | tests only |
| 3 | `dungeon-on-dregg/src/mud.rs` | N player-cells on ONE shared world; a `WriteOnce` owner slot on a contested lantern; forge-another-player's-move is a real `CapabilityNotHeld` | tests only; `CommandOutcome` re-exported by `dreggnet-guild`/`dreggnet-surfaces` |
| 4 | `mud-dregg` (668 lines, a `run_arc` binary) | multiplayer IS branch-stitch: two players fork, explore, stitch; disjoint edits merge, a genuine two-players-one-sword conflict is a `#`-conflict REFUSED, never last-writer-wins | a demo binary |
| 5 | `node/src/mud_e2e.rs` + `node/src/shared_world.rs` | the MUD as a pure userspace deos-js program the node hosts; two distinct key-ceremony identities co-inhabit one live world over real HTTP with an SSE receipt stream and an un-fakeable presence seat | ⚑ `#![cfg(feature = "deos-host")]`, and `deos-host` is **not** in `node`'s `default` (`node/Cargo.toml:177,187`). One test each. |
| 6 | `realm-model` + `node/src/realm_service.rs` | the durable protocol: persistent REALM vs child INSTANCE, canonical identity that surfaces derive from, ruleset catalog as committed law. **17 HTTP routes, mounted by default** (`node/src/api.rs:2259`, bearer-gated), replayed fail-closed from `persist`'s `REALM_LOG` on boot, canaried across a real restart (`realm_service.rs:2075`) | **live in the node** |

And the presence organ, `dreggnet-tavern`: a shared board, a presence seat per patron whose
`PRESENT` flag only its own holder can flip, a live receipt stream so patron B *sees* patron A act,
and a receipted over-reach refusal when a patron pokes another's private stall. It has **zero crate
dependents** - I checked every `*/Cargo.toml`. The frontend that renders a tavern,
`dreggnet-surfaces/src/tavern.rs`, is explicit about what it is: *"a **read mirror** of the live
board ... `actions` is empty (nothing commits *here*)"* (`:19-23`), painting from an in-memory
`Vec<Patron>`.

**That is the shape of the whole problem in one crate pair.** The organ that makes a MUD a MUD is
built, tested, un-fakeable, and wired to nothing; the thing players can actually click is a picture
of it.

### 1.6 The one limit that forecloses the obvious plan

`WorldCell::apply_choice(&self, passage_name, choice_index, choice)` (`world.rs:719`) takes **no
actor**. A `WorldCell` holds one `cclerk` (`world.rs`, the `WorldCell` struct). Every turn on a compiled `.dungeon`
world is signed by the *world*, not by the player.

**An authored dungeon is therefore single-writer and player-anonymous at the executor, by
construction.** Attribution exists, and as of today it is real - `Attribution::Signed` means an
Ed25519 key verified over the turn (`dreggnet-offerings/src/signed.rs:8-20`), and rung 2 (a browser
key the server cannot make) landed in `995a779c9`. But it lives at the **session/move-log** layer,
not on the cell turn. So: you cannot make a `.dungeon` room multiplayer by adding players to it.
The `.dungeon` lane and every multiplayer lane are different substrates that cannot meet without
a seat on the turn.

---

## PART 2 - VISIONARY: the game

### 2.1 What this engine makes possible that a normal MUD cannot

Strip the candidates down to the ones that survive contact with the code.

**Survives, and is the headline: standing that nobody can launder.** `dreggnet-faction`
(`src/lib.rs:22-44`) makes reputation a `Monotonic` slot - *"rep can rise but is never un-earned"* -
and a betrayal a `WriteOnce` **permanent seal**: turning on the Embers sets `embers_betrayed`, and
the Ember content is closed to you forever, gated by `FieldGte(rep, THRESHOLD)` **and
never-betrayed**. In every MUD that has ever shipped, reputation is a row an admin can edit and a
forum post can dispute. Here it is a tooth. **The world remembers that you defected and neither the
GM nor you can unwrite it.** That is not a better implementation of an old feature. It is a
different object.

**Survives: loot with custody you can hand to a stranger.** `dreggnet-asset` gives owned,
transfer-gated, provenance-chained notes; `dreggnet-craft` is *"the economy's first real sink"* -
it consumes a typed multiset of owned materials and **destroys them on-chain**, keeping only a
`ProvenanceNote` of the runs they came from because the inputs themselves are gone
(`dreggnet-craft/src/forge.rs:127-168`); `dreggnet-trade` is a trustless atomic swap. So "this sword
was banked on day 12 out of the Undervault by someone who then burned three relics to forge it" is
a *checkable statement about a burned object*, in a stranger's hands, with no server to trust.

**Survives with a caveat: an AI narrator that cannot lie about mechanics.** The confinement is real
and it is checked four times before the executor even sees it: the tool schema is *built from*
`legal_commands` with `additionalProperties: false` (`discord-bot/src/commands/fiction.rs::chutes_turn_tool`,
~`:889-918`); the response must be empty assistant text plus exactly one tool call with exactly the
key set `{command, narration}` (`::admit_chutes_turn`); the keyword must be in the room's legal set
or `BrainRefusal::IllegalCommand` (`narrator.rs::parse_confined_response`); and it is **re-checked
against the authoritative current room** after the provider answers
(`dreggnet-offerings/src/dungeon/narrated.rs`, `view.offers(&narrated.command)`). Prose becomes no
`SetField` at all - it is BLAKE3'd into a receipt-only `EmitEvent`. The keystone test is
`a_confined_move_resolves_on_the_world_and_prose_is_not_power`: the narrator says "you slay the
warden and 1000 gold rains", the move commits, `hp` falls to 30, and **`gold` stays 0**.

⚑ In the working tree the narrator lane makes this claim *structurally* stronger, and the reasoning
in its own doc comment is worth quoting because it is the right kind of argument:

> The tool schema's `enum`, the prompt's offered list, and the post-hoc re-check are all built from
> ONE `SceneView` value: not three derivations that could disagree, one vector read three times. ...
> a schema wider than the re-check is a hole, and a re-check wider than the schema is a move nobody
> offered. And the set can never be WIDER than what the executor will dispatch: every entry is a
> `(room, index)` coordinate read off a compiled passage's own choice list.

The caveat, correctly named in `d15c61b74`: the receipt attests that *some* narration was committed,
not *which* - `Playthrough` carries no prose (`spween-dregg/src/world.rs`, `Playthrough` is
`{genesis, genesis_state, steps}`) and `verify_dungeon_record` reads the text from the live
in-process session (`dreggnet-offerings/src/dungeon.rs`, `session.narration_log()`). **State is
confined. Prose does not replay.** The route that would close it exists and is unused on the live
path: `binary_operation_replay_material` retains the whole canonical `ChutesNarratedRequest`, prose
included, but `discord-bot/src/commands/fiction.rs` calls `advance_narrated_receipt_in_enclave`
directly and `CHUTES_NARRATED_OPERATION` has zero non-test callers.

**Does NOT survive as stated: "each seat's information is genuinely private."** It is private from
other *viewers of the same render*, which is exactly what a normal MUD's server-side visibility
gives you. The cryptographic version exists and is unwired (§1.4).

### 2.2 The design: THE HEARTH

**A MUD is persistence plus presence plus consequence.** This repo has world-class consequence, a
built-and-unwired presence organ, and durable persistence at the realm layer that no game touches.
So build the thing that is *only* those three, and put no dungeon in it at all to start.

**The Hearth is one persistent room that a handful of people are in at the same time, where the
only verbs are ones whose consequences are permanent.**

Not a lobby. Not a menu. A place with a name, a fire, a board, and a ledger stone, that is *already
different* when you come back tomorrow because of what other people did while you were gone.

**Moment to moment.** You open a URL. There is prose, and under it a line that says who else is
here - not a roster the server asserts, but presence seats whose `PRESENT` flag only their own
holder can flip (`dreggnet-tavern/src/lib.rs`; `node/src/shared_world.rs`), so *nobody can fake
being here as someone else.* You type:

```
> look
> say i have a mender's charm and i want the long stair opened
> post lfg: two more for the Undervault, i pay in salt
> show
> give salt_tithe to bramwen
> swear tide
```

`say` writes a glyph into the room cell (`SLOT_SAY`) and everyone watching the receipt stream sees
it land, attributed. `give` is a real owner-signed asset transfer that either commits or refuses;
there is no "the server dropped it" and no dupe, because a duplicate is a `#`-conflict the
settlement gate refuses (`mud-dregg/src/scenario.rs`, tooth 4). `swear` is the `oath` construct -
one shared spend counter across branches, so **swearing any branch forecloses the rest, forever,
by a tooth** (`compile.rs:36-42`). Tomorrow the Embers will deal with you and the Tide will not,
and no one can undo it including the person running the server.

**Why do you come back tomorrow?** Three reasons, in ascending order of how much work they are:

1. **Somebody is owed something.** You promised Bramwen a censer for the stair. That promise is a
   real committed record, not a memory.
2. **The hearth changed.** A realm epoch ticked; the hoard on the ledger stone is what the week's
   expeditions settled back (`RealmWorld::settle_instance` advances a durable `HOARD`/`EPOCH`), so
   the shared place *visibly reflects other people's runs.*
3. **The door you did not take is closing.** Standing accrues monotonically and a betrayal seals.
   Every day you spend on the Tide's side is a day the Embers' content moves further out of reach.

**And what multiplayer means here.** We have **no matchmaking, no presence on the web, no chat**, and
a second player currently joins by being *sent a link by hand* - and that door exists for exactly
two games (`dreggnet-web/src/table_seats.rs:297`: `pub const ALL: [TableLock; 2] = [AUTOMATAFL,
TUG]`). The Hearth's answer is not matchmaking. It is **one address**. A MUD does not match you
with anyone; it is somewhere you go, and the other people are the ones who also went. The `dregg`
CLI and `dregg-tui` already exist; a text client over a shared room is the smallest possible
frontend and the most honest one.

### 2.3 The economy: two currencies, both already built

Part 3 of the Descent's diagnosis - *"a decision needs two incomparable currencies"* - is exactly
right and it applies here. The MUD's two currencies exist, in code, today, and they are
incomparable for a *structural* reason rather than a balance-sheet one:

| | **COIN** (what you carry) | **STANDING** (who owes you, who is closed to you) |
|---|---|---|
| primitive | `dreggnet-asset` owned notes; `{gold >= 50} ~ gold -= 50` teeth (`spween-dregg/src/compiler.rs:829-851`) | `Monotonic` rep slots + `WriteOnce` betrayal seals (`dreggnet-faction/src/lib.rs:22-29`) |
| can it go down? | **yes** - the craft sink destroys inputs on-chain | **no** - `Monotonic` refuses a decrease |
| transferable? | **yes** - `dreggnet-trade` atomic swap | **no** - it is a fact about a cell, not a note |
| how do you spend it? | pay it | you cannot. You can only **foreclose** with it: swear, and the other branch is shut by a tooth |
| faucet | loot drops, quest rewards | acts you performed, witnessed |
| sink | craft, tolls, durability | none, and there must not be one |

They cannot be exchanged in either direction, and *that is enforced, not agreed*. You cannot buy
standing, because `Monotonic` only rises through the gated acts that raise it. You cannot sell
standing, because there is no note to hand over. **So every interesting choice in the Hearth is
"do I pay in coin or do I close a door?"** - and `dungeons/salt_reliquary.dungeon` already writes
that scene. Ferrun the tide-warden sells the gate for a `salt_tithe` **and** a hand on his ledger;
the long stair costs no coin and is only walked by someone who swore to the drowned. The author
found the two-currency design unaided. The compiler refuses to let either half cost anything.

**What this buys that a token does not.** A normal MUD economy dies of inflation because every
faucet mints and the only sink is a repair bill. Here the second currency has no faucet-sink
dynamics at all - it is a *record*, and its scarcity is that it is irreversible. That is a supply
curve you cannot farm.

---

## PART 3 - CRITIC: why this is a substrate and not a game

### 3.1 It is hollow, and here is where the hollow is

Saying it plainly, in those words: **the world layer is hollow.** Not the crypto, not the executor,
not the offering host - those are the most solid things in the repo. The hollow is a thin band
between "a constraint is enforced" and "a person wants something", and it is hollow in a specific,
diagnosable way: **every organ is built, tested, honest about its own limits, and connected to
nothing.**

- The presence engine has zero dependents; the presence *surface* is a mock (§1.5).
- The narrator drove **3 rooms of 20** for as long as the Keep has existed, because
  `legal_commands` was a hardcoded three-arm `match` on three string literals. That is fixed in
  the working tree - and it is the cleanest example of the shape: the wall was never the model, the
  substrate, the prose, or the money. It was **forty lines of `match`**, in front of seventeen
  rooms that were already compiled and already gated.
- The one dungeon we have is **not on the ship list**: `SHIPPED_KEYS: [&str; 3] = ["descent",
  "automatafl", "tug"]` (`dreggnet-catalog/src/lib.rs:617`). The Keep is registered in a catalog of
  23 and gated out of the menu.
- `dialogue.rs` (960 lines, an entire NPC disposition system) has zero code importers.
- The cryptographic fog has zero `dreggnet-*` importers.
- `crew_descent` - the four-seat party on the real Descent - has zero consumers outside its crate.

### 3.2 Content problem, authoring problem, or design problem? All three, and the order matters

**It is a design problem first**, and the evidence is that there is **no objective function anywhere
in the corpus**. I had the seven strategy documents read end to end. There is no score, no rating,
no rank formula, and **no quantity that can decrease**. "Rank a win on a leaderboard"
(`docs/GAME-AFFORDANCES-MAP.md:27-28`) never says rank *by what*. The nearest thing to a scalar is
`dreggnet-guild`'s *"sums only verified clears"* - monotone. Achievements are threshold predicates.
The word "ghost" (as in "beat your own ghost", `docs/GAME-STRATEGY.md:106`) appears exactly once in
the corpus and has no crate, no tag, no phase.

And the reason is structural, which is why one file cannot fix it. The tooth vocabulary is built
to **forbid decrease**: `Monotonic`, `WriteOnce`, `FieldGte`, conservation. The single most honest
line in the entire document set is `docs/GAME-FUN-AND-INFRA-PLAN.md:10`:

> **"Not FUN yet - you cannot lose."** True of the original universes (the `FieldGte(hp, 1)` floor
> REFUSES a lethal blow; dice_combat.rs:543)

That is a designer noticing that the verification substrate's core safety property - *illegal
transitions are refused* - is structurally hostile to the transition "you died." One file
(`bloodgate.rs`) routes around it for the single case of death. **Nothing was ever written to make a
number go down**, and the DSL's `lose:` refusal is the same wound at the authoring layer.

**The Keep is the specimen.** Its objective is a four-item to-do list -
`"trade past the gate-warden, claim the crown, descend the collapsing stair, and seize the hoard"`
(`dreggnet-offerings/src/dungeon.rs:105`) - and each item is one button
(`lib.rs:389/393/401/409/439`). The canonical win is six presses (`overworld.rs:96-106`). There is
no score, no rank, no failure you cannot decline. **A to-do list is not an objective function; it is
a checklist with prose on it.**

**It is an authoring problem second**, and §1.3 sizes it exactly: nine refusals, all nine with a
working reference semantics in `attested-dm` and a proven executor idiom in `dungeon-on-dregg`,
and the load-bearing one (cost) already lowered and documented in the compiler beneath.

**It is a content problem third and least.** ~36 lines of Rust per word of prose in
`dungeon-on-dregg`, and ~54:1 across the whole game layer, is a real number, but writing 10,000
words into a grammar that cannot charge for anything just produces 10,000 words of scenery. The
`tide_lamp` in `salt_reliquary.dungeon` is exactly this: a real object, in real prose, that is
scenery because the `light` block that would make it matter does not deploy.

### 3.3 Does the Descent's diagnosis apply?

**Yes, and more sharply, because the MUD has no scalar at all.** The Descent has one currency
(capacity), every cost is additive in it, so the optimum is a shortest path and shortest paths are
unique: 0 strict forks on 16/16 days. The Hearth as it stands would be worse - it has *zero*
currencies, so there is nothing to be optimal about. The two currencies are named in §2.3, and the
test of the design is the same one the Descent lane used: **enumerate, and count strict forks.**
A Hearth where every choice is "pay coin or close a door" has forks by construction, because coin
is recoverable and a foreclosure is not, so no exchange rate exists.

### 3.4 The same class of wound the Descent lane found - one more instance, and it just closed

The Descent lane proved `lunge` is offered as a live button at 8-10 of the ~21 crown-line turns
while being a provable forfeit. **The narrator had the identical wound.** `KP_CLIMB_BACK`
(`dungeon-on-dregg/src/lib.rs:497-498`: *"climb back up (`depth -= 1`) - refused (the stair
collapsed: one-way)"*) sat in the sanctum's legal set, so roughly one press in three in that room
was a guaranteed refusal we paid a model to choose.

⚑ **The working-tree `scene_view` closes it, and closes the whole class.** It filters every derived
command through `world.probe_choice(&room, idx, choice).offerable()`, and `offerable()` is
`!matches!(self, ChoiceAdmission::Refuses(_))` (`spween-dregg/src/world.rs:153-171`) - a probe of
the *installed teeth against committed state*. `Undecided` stays offered, deliberately: the
executor is still the referee. So a choice the referee will decisively refuse is no longer offered
to anyone, and the general rule is now available for free to every surface, not just the narrator.

**That generalises into a gate, and someone should build it (plan item 7).** "Is any enabled control
on this surface a decisive `ChoiceAdmission::Refuses`?" is a one-line invariant that would have
caught `lunge` and `climb_back` both, and is exactly the *documented-is-not-detected* discipline:
the Descent lane wrote the `lunge` wound down; nothing can currently make it go red.

### 3.5 The documentation is not a reliable map, and should not be used as one

Ten direct contradictions across the seven strategy documents; the load-bearing ones:

- The thesis sentence of `GAME-AFFORDANCES-MAP.md:26-28` ("a match folds to ONE succinct STARK a
  light client accepts in O(1)") is contradicted 170 lines later by its own `:197-198` ("`#[ignore]`
  ... **not yet run**") and by `VERIFIED-GAME-PORTFOLIO.md:150-152` ("a wiring claim, not a result").
- `GAME-ENGINE-ROADMAP.md` is undated, is almost entirely green checkmarks, and its own scope note
  (`:12-14`) says the substrate it describes is *"a labeled toy relative to the deployed VK"* that
  the strategy forbids shipping on.
- `GAME-STRATEGY.md:126-128` **locked** "wire the real attestation crown for launch, not a fixture"
  on 2026-07-12. Two weeks later it is still NAMED (`GAME-AFFORDANCES-MAP.md:389`), the fixture is
  still the default, and **no document records the slip** - while `GAME-AFFORDANCES-MAP.md:160`
  goes on marketing "the un-jailbreakable AI DM", which `GAME-STRATEGY.md:102-103` forbids absent
  the wiring.
- `[BUILT: path]` is defined (`GAME-FUN-AND-INFRA-PLAN.md:5-6`) as "real code at HEAD". Across four
  documents, 55 such tags assert **that a file exists.** `GAME-AFFORDANCES-MAP.md:10-16` has a
  strictly better vocabulary (deployed / **driven** = a green integration test on the real path /
  scaffold-NAMED) and the four documents carrying most of the tags do not use it.

The best-disciplined document in the set is `VERIFIED-GAME-PORTFOLIO.md`, which retracts its own
prior claims with quantified reasons - including that multiway-tug's shipped Rust `winner_of` drew
**78.5%** of played rounds against the Lean model's **5.1%**, undetected until a model was hooked up.
Read that one; treat the rest as a lead list.

Two staleness repairs made in this pass (trivial and named; nothing else touched):
`realm-model`'s crate-doc header claimed the node-served durable receipt chain "does not yet
exist" while its only consumer, `node/src/realm_service.rs:10-14`, says it is built and drives it
(`persist/src/tables.rs:295`, `node/src/state.rs:914`, driven by `node/src/state.rs:3727`); and
`docs/design/MUD-SUBSTRATE.md`'s receipt-chain section said "it is not served today" while its own
STATUS block 200 lines above records it as the landed keystone.

---

## PART 4 - THE PLAN

Ranked, first-first. **S** = under a day. **M** = a few days. **L** = a swarm cycle.
**RULES** = machine-checked law, authored in Lean, re-emitted. **SURFACE** = everything else.
Track: `[D]`esign, `[A]`uthoring, `[E]`ngine, `[C]`ontent.

### If you only do one thing

**Do item 5.** Everything above it is leverage on a game that does not have an objective yet.
Items 2-4 are cheap enough to do anyway, and item 5 is the one that decides whether any of it is a
game. But the *honest* first-first ordering puts the cheap unblocks first because they are hours,
not weeks, and item 5 needs a decision from you.

---

### 1. ~~`legal_commands` derives from the compiled scene~~ - **LANDED IN THE TREE** `[E]` SURFACE

Was: `legal_commands` is a hardcoded three-arm `match` on three string literals; replace it with a
read off the compiled scene. Ranked "⚑ S, ~40 lines, HIGHEST LEVERAGE" in `d15c61b74`.

**Done, uncommitted, and done better than specified.** `legal_commands(view)` is now
`view.commands()`; `scene_view` derives the set once from the compiled passage via
`derive_room_commands` and filters it through `WorldCell::probe_choice(..).offerable()` against
committed state. What it bought:

- the narrator runs on **any registered scene** - 20 rooms instead of 3;
- the tool-schema enum, the prompt's offered list, and the post-hoc re-check are now **one vector
  read three times** rather than three derivations that could disagree, so a derivation bug is
  visible in all three at once instead of opening a gap between them;
- the set **can never be wider than what the executor will dispatch**, because every entry is a
  `(room, index)` coordinate read off a compiled passage's own choice list;
- the always-refused-button class dies (§3.4).

**Remaining, for whoever finishes it:** confirm the 7 certified-private-result choices
(`dungeon-on-dregg/src/lib.rs:485-504`) are still excluded - a `probe`-based filter must not
silently re-admit them; and note that `scene_view` now carries `prose`, which is a new ingress into
the model's prompt and should be reviewed as one.

### 2. COST in the `.dungeon` grammar - `[A]` **S-M**, SURFACE (the tooth already exists)

Add a spend to the grammar and one arm to the lowering. Suggested syntax, matching the existing
style: `topic pay once requires item salt_tithe -> spends salt_tithe, opens toll_paid "..."`.

- **Lowering:** `Effect::Modify(ModifyEffect { var: has_salt_tithe, delta: -1 })` on a choice whose
  condition already carries `{ has_salt_tithe >= 1 }`. `compare_teeth`
  (`spween-dregg/src/compiler.rs:852`, doc at `:829-851`) lowers exactly this, clamp-safe, with the
  `FieldDelta` companion pinning the delta - **`{gold>=50} ~ gold-=50` is its own worked example.**
  Extend `check_lowering` (`dungeon-on-dregg/src/dsl/compile.rs`) with the expected `FieldDelta` so
  a cost that failed to lower is a `ValidationFailed`, not a free lunch.
- **Payoff:** W1 dies. `salt_reliquary.dungeon` compiles with a real toll. **The entire economy
  becomes authorable in one afternoon** - tolls, offerings, rations, ammunition, entry fees.
- **Immediately after (also S, same machinery):** a numeric `purse` var and a var-vs-var gate
  (`requires purse >= price`), which `cross_var_teeth` (`spween-dregg/src/compiler.rs:936`) already
  lowers to `FieldLteOther` / `HeapFieldLteOther`. ⚑ Note its clamp guard refuses a *spending*
  cross-var gate (`dg < 0` returns `None`), so a priced purchase needs either a literal price or an
  extension there - name it, do not paper it.

### 3. `lose:` and multiple endings - `[A]` **M**, SURFACE

W3 and W4. `objective:` is currently a single `reach ROOM holding ITEM`. Make terminals a list:
`ending drowned in reliquary requires flag oath_allegiance_drowned and not holding drowned_crown`,
and `lose:` a real terminal on a flag reaching a bound. Both lower to the same `Claim`-choice shape
the win terminal already uses (`compile.rs:15-32`).

- **Payoff:** the oath forks the middle of the dungeon *and the ending*. Risk becomes writable.
  This plus item 2 is the whole of "a dungeon where a player can die or spend anything."
- Keep `hostile`/`combat`/`spell`/`status`/`light` refused for now. They have reference semantics in
  `attested-dm/src/game.rs` and executor idioms in this crate, but they are a bigger lowering job
  and **they are not what a MUD needs first.**

### 4. THE HEARTH, minimum viable - `[E]` **M-L**, SURFACE

One durable room, N seats, three verbs: `look`, `say`, `enter`. Compose, do not invent:

- **the room + durability:** `realm-model` / `node/src/realm_service.rs` - realms already survive
  restart with a fail-closed replay and are canaried (`realm_service.rs:2075`);
- **presence + live sync:** `dreggnet-tavern`'s seat cells and `/api/events/stream` subscription -
  the un-fakeable presence flag and the receipted over-reach refusal are already driven;
- **speech:** `SLOT_SAY` from `dungeon-on-dregg/src/mud.rs` / `starbridge-v2/src/mud.rs`'s speech
  suite;
- **the door:** the `table_door` pattern (`dreggnet-web/src/table_door.rs`) generalised past its
  two-lock hardcode (`table_seats.rs:297`) - except the Hearth needs no per-seat secret, because it
  is a *public place*. One URL.
- **the client:** a text client. `dregg-tui` and the `dregg` CLI already speak to a node.

**Exit condition, stated as a falsifiable test, not a vibe:** two distinct key-ceremony identities
enter one Hearth from two processes, each sees the other's `say` land attributed on the live stream,
one gives the other an asset and the transfer commits, the node is restarted, and **both the room's
state and the transfer survive** - driven, not asserted.

**The named residual you must not paper over:** `WorldCell::apply_choice` takes no actor (§1.6). The
Hearth cannot be a compiled `.dungeon` world until a seat exists on the turn. Either build the
Hearth on the `realm_service` path (where `RealmTurn` already carries an actor `SurfaceRef`) and
keep `.dungeon` for solo content, or add an actor to the world-cell turn. **That is an architecture
decision and it is ember's.** Do not let a lane pick it by accident.

### 5. ⚑ THE OBJECTIVE - `[D]` + **RULES** (Lean), **L**

The one that decides whether any of the above is a game.

**5a. Name the two currencies and make every consequential choice price one against the other.**
Coin (spendable, transferable, decreases) and Standing (`Monotonic`, foreclosed by `WriteOnce`,
never spent). Both are built (§2.3). The design work is not building them; it is **auditing every
authored choice for whether it prices one against the other**, and rewriting the ones that do not.

**5b. Write one quantity that can go down, in Lean, and prove it can.** This is the substrate's
deepest bias (§3.2) and it must be attacked at the rules layer, not with a second `bloodgate.rs`.
The property to state and prove is not "a number decreases" - it is that **a reachable state exists
from which the player's position is strictly worse and not recoverable within the run.** Then prove
the negation is refutable: a run that never chose badly does not reach it. Apply the
`feedback-prove-the-floor-false` discipline - satisfiable, refutable, not provable.

**5c. Measure it the way the Descent was measured.** Replicate the mover, enumerate the reachable
state space, count **strict forks** (two optimal continuations differing in what remains, not its
order). Run the negative control: loosen a budget and confirm forks stay at zero, so you know you
are measuring choice and not slack. If the Hearth's fork count is 0, the two currencies were not
actually incomparable and you have found that out in a day instead of a season.

### 6. Content, last and on purpose - `[C]` **M**, ongoing

`attested-dm` holds 95 rooms and ~2,700 words of real prose on a toy ledger, and
`dungeon-on-dregg` imports exactly one 250-word constant from it (`VOICE_SPEC`, used at
`narrator.rs:1440`, defined at `attested-dm/src/voice.rs:76-97`).
After items 2 and 3, most of that prose becomes *portable* - the parser is already the same parser.
Port the four `.dungeon` files first (`clockwork_orchard` already compiles today), then the Rust
worlds. **Do not port before items 2-3 land**, or you will port 95 rooms of scenery.

### 7. Wire the organs that are already built - `[E]` **S** each, in parallel with the above

Each of these is a dependency edge, not a feature:

- **`dreggnet-tavern` -> the web surface.** Today `dreggnet-surfaces/src/tavern.rs` paints an
  in-memory mock and links out. Bind the join button to a booted tavern session - the crate's own
  "NAMED NEXT" (`tavern.rs:25`).
- **`node`'s `deos-host` feature.** `shared_world.rs` and `mud_e2e.rs` - the live co-inhabitance
  rung the vision documents lean on - are `#![cfg(feature = "deos-host")]` and `deos-host` is not
  in `default` (`node/Cargo.toml:177,187`). Either promote it or stop citing them as deployed.
- **The `default-members` exclusion (§1.1).** 74 of 223 members are excluded and the game layer is
  almost all of them. Either add the game crates or add a named CI lane that builds them, because
  right now `cargo test` at the root is silent about the entire product.
- **`dialogue.rs`, `skills.rs`, the cryptographic fog, `crew_descent`.** Four systems with zero
  consumers. Each is either a plan-item dependency or debt. **Say which, per crate, and delete the
  ones that are debt** - the unadditive move, per `feedback-mapping-is-the-launchpad-not-the-outcome`.
- ⚑ **THE DEAD-BUTTON GATE (§3.4), and it is now cheap.** One invariant, addable to the existing
  cross-backend surface harness: *no enabled control on any rendered surface may be a decisive
  `ChoiceAdmission::Refuses` against the session's committed state.* `WorldCell::probe_choice` is
  the oracle and the narrator lane just proved it works as a filter. This would have caught the
  Descent's `lunge` (a live button on 8-10 of ~21 crown-line turns, silently forfeiting the run)
  and the Keep's `climb_back`, and it is the difference between a wound that is documented and a
  wound that can go red. **A documented wound is not a detected one.**

---

## The one-paragraph version

The engine is not the problem and neither is the prose. There are six working MUD substrates, a
built-and-tested economy with a real sink and a real atomic swap, an un-fakeable presence layer
with zero dependents, durable realms serving 17 live routes, and a narrator that provably cannot
lie about state. What there is not, anywhere, is **a place, a second person in it, and a number that
can go down.** The `.dungeon` grammar cannot charge for anything even though the compiler beneath it
lowers `{gold>=50} ~ gold-=50` clamp-safe as its own documented example; the Keep's objective is a
four-item checklist and it is not even on the ship list; and the substrate's finest property -
that illegal transitions are refused - is precisely what makes loss hard to express, which one file
has worked around exactly once. Build the Hearth: one durable room, real presence, two incomparable
currencies (coin, which you spend, and standing, which is `Monotonic` and foreclosed by
`WriteOnce`), and one loss you cannot decline. Then measure the fork count the way the Descent was
measured, before writing a single new room.
