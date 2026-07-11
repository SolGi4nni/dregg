# Authoring Dungeons — the `.dungeon` text format

A dungeon is a **text file a person can write**. `attested_dm::parse_dungeon` turns it into a
first-class `GameWorld` that plays through the same attested engine as the hand-written games:
every turn is a cap-gated, hash-chained, replay-verifiable receipt. No Rust, no recompile — write
a file, hit **Play** in `/forge`, and a model narrates it while the chain remembers it.

Parsing is **fail-closed**: syntactic *and* semantic mistakes (a dangling exit, an unreachable
objective, an item that exists nowhere) both refuse the parse with a line-numbered error. A broken
dungeon never becomes a world.

---

## The shape of a file

Lines are the unit. Blank lines are ignored; `#` and `//` begin a comment to end-of-line (except
inside a `"quoted string"`). Top-level directives start at column zero; a **block** (`room`, `npc`,
`spell`, `light`, `combat`, `hostile`) owns the *indented* lines beneath it.

### Header (top level)
```
name: The Sunken Vault                 # flavour (also: title:)
start: shore                           # the opening room id (required)
objective: reach sunken_gate holding amulet   # win = be in <room> holding <item>
lose: slain >= 1 -> "cut down by the Warden"  # a flag reaching >= v ends the run ( >=1 default)
player_hp: 10                          # optional; needed for HP combat (also: player_max_hp:)
```

### Rooms
```
room shore "The Salt Shore"            # room <id> "<Display Name>"
  The tide has gone out; the vault's mouth stands open.   # any plain line = description
  items: lantern, coil_of_rope         # comma list (or: item lantern)
  exit north -> antechamber            # exit <dir> -> <room>
  exit down  -> dark_stair requires item lantern       # a Gate: needs an item in inventory
  exit east  -> armory   requires flag door_unlocked >= 1   # a Gate: needs a flag value
```
A gated exit is refused until its gate holds — you cannot narrate through it.

### Use-rules — make an item *do* something
```
use rusted_key on iron_door in vestry -> flag door_unlocked "The lock turns."
```
`use <item> [on <target>] in <room> -> flag <name> [= v] "<narration>"`. Sets a world flag (which
can open a gate). The item must be held and you must be in that room.

### NPCs + dialogue
```
npc witch "The Hedge-Witch" in witch_hut
  about "a swamp-crone who trades only in fair exchange"
  topic sickle requires item nightshade -> gives sickle "A fair trade." else "Bring nightshade."
  topic lore -> reveals "She tells of the keep's fall."
```
A `topic` grants (`gives <item>`) or narrates (`reveals`) **only** when its `requires` holds; the
`else` line is spoken otherwise. The Hedge-Witch trades the sickle *only* for the nightshade — the
rule decides, not the prose.

### Combat
Two forms. A one-shot **hostile** (a gate you pass by holding the right weapon):
```
hostile warden in warden_hall defeated_by sword
  victory flag warden_defeated
  victory "Your sword finds the gap; the Warden falls."
  death flag slain
  death "Bare-handed, you are no match."
```
A multi-round **combat** enemy (needs `player_hp:`):
```
combat voidling in stairhead hp 9 attack 3
  weapon flare_blade damage 3
  unarmed 0
  armor bark_shield 1                  # optional mitigation
  victory flag voidling_felled
  victory "The flare blade sears through the dark."
  hit "White fire bites the Voidling."
  flail "Your bare strike passes through it like smoke."
```

### Spells
```
spell light requires flag learned_light    # or: spell light innate
  in gallery   -> flag gallery_lit "Mage-light pours up the stair." fizzle "It finds nothing here."
  in stairhead -> conjure flare_blade "A blade of white fire kindles."
  in shrine    -> buff blessed "A warmth settles over you."
```
A spell does nothing until learned (a `requires flag` set by reading a grimoire via a use-rule), and
each casting is bounded to its declared `SpellEffect` in that room.

### Light — a depleting resource
```
light lamp oil 8                       # light <lamp-item> oil <start>
  dark: dark_stair, cistern            # pitch-dark rooms (impassable unlit)
  refuel oil_flask +5 "You fill the lamp." spent "The flask is dry."
  stranded stranded -> "the dark keeps you"   # sets the strand flag AND a lose condition
```
The lamp burns one oil per step; entering a dark room unlit strands you.

### Consumables + status effects
```
status venom poison 2                  # a timed debuff: 2 wounds/turn while active
status warded shield 3                 # a timed buff: mitigates 3 while active
consumable salve   use -> heal 4 "You break the salve; the ache dulls."   # heal N (clamped at 0)
consumable bile    use -> status venom 8 "Venom floods your veins."       # grant a timed status
consumable antidote use -> cure venom "The green fire goes cold."          # zero a status
consumable sigil   use -> flag ward_lifted "The sigil crumbles; the ward lifts."
```
A consumable applies its bounded effect and is **consumed** (a second use is refused). Status
counters tick down each turn; the world computes every value — a jailbroken "you are invincible"
heals exactly `N`, no more.

---

## What the validator checks (and refuses)

`parse_dungeon` refuses, and `validate` reports every issue, when a world is unsound:
- an **exit** leads to an unknown room;
- the **objective room** is unreachable from `start`, or the **win item** is placed only in a room
  unreachable from start;
- a **gate item / win item** is never placed anywhere;
- an **NPC / combat / spell / consumable** names an unknown room or an unplaced item;
- a **spell** has no learn source (nothing sets its `requires` flag).

Warnings (advisory, don't block): a flag-gated exit whose flag no declared rule ever sets — a
likely permanently-sealed door.

---

## Playing what you wrote

- **In the browser:** the `/forge` page — type a `.dungeon`, watch errors surface live as you type,
  hit **Play**. A room-map of your world renders on a successful parse (spot a disconnected room at a
  glance).
- **Native:** put the source in `attested-dm/dungeons/` and `cargo run -p attested-dm --example
  play_authored` — a dungeon that exists *only as text* plays to a win through the real engine and
  re-verifies.

Sample worlds: `attested-dm/dungeons/` (`lantern_fen`, `clockwork_orchard`, `ember_observatory`,
`venom_warren`, plus a deliberately-`broken` one for the validator).

*(Not yet in the DSL — authored in Rust for now: the multi-combatant **combat encounter** engine and
**verifiable-random loot** chests. They're on the roadmap for the text format.)*
