# SPWEEN ON DREGG — on-chain choose-your-own-adventures + MUDs, collectively authored

*How `spween` (a narrative-choice DSL) composes with dregg to make interactive fiction that is
verifiable (nobody can retcon the story), cap-secure (nobody can forge your move), and
**collectively authored** (the audience votes the next branch). Written for kanzokax, who wants to
build and run this kind of thing on dregg.*

> Present-tense, first-principles. Everything is grounded to file:line in the two repos it composes:
> `~/dev/spween` (the story engine) and `~/dev/breadstuffs` (dregg). This doc designs the
> integration; it builds no code.

---

## 0. THE ONE-SENTENCE SPINE

> **A federation governance-vote, a community poll, and a choose-your-own-adventure collective choice
> are the SAME primitive: a group collectively and verifiably deciding what happens next over shared
> state. dregg makes them one thing — a choice is a *turn*, a collective choice is a *vote that
> resolves to a turn*, and either way the world-cell advances and leaves a receipt that cannot be
> forged or rewritten.**

spween already models "what happens next over shared state" for a *single* reader on an *ephemeral*
in-memory state. dregg supplies exactly the three things spween's `EffectHandler` leaves as a hole:
persistent, non-forgeable, non-rewritable shared state (the *world-cell*); an unforgeable notion of
"who chose" (the *cap-gated turn*); and a way for *many* deciders to agree on one next step (the
*vote* and the *branch-stitch lattice*). The story stops being a private playthrough and becomes a
public, tamper-proof, collaboratively-authored artifact.

---

## 1. WHAT SPWEEN IS (grounded)

`spween` is a **game-agnostic DSL for narrative/choice-based content** — a Twine/Ink-class
interactive-fiction engine, written in Rust
(`~/dev/spween/Cargo.toml` package description; `~/dev/spween/src/lib.rs:1-9`). It is a clean
lexer → parser → AST → tree-walking runtime pipeline (`~/dev/spween/README.md:40-58`), plus a WASM
browser playground (`~/dev/spween/playground/`).

### 1.1 The data model (a story is a tree of passages and choices)

A whole story compiles to a `Scene` (`~/dev/spween/src/ast.rs:19-26`):

| spween concept | type (file:line) | what it is |
|---|---|---|
| **story / scene** | `Scene { meta, passages, span }` — `ast.rs:19-26` | one narrative file |
| **metadata** | `SceneMeta { id, title, tags, weight, cooldown, requires, custom }` — `ast.rs:30-47` | YAML frontmatter; `requires` is a precondition `Condition` |
| **passage / room / node** | `Passage { name, content }` — `ast.rs:51-58` | a named story node (`=== intro`); `name` is the navigation address |
| **passage body** | `PassageContent = Prose \| Choice \| Effect` — `ast.rs:62-69` | narrative text, a decision, or a state mutation on entry |
| **a choice / link** | `Choice { text, condition, effects, target }` — `ast.rs:82-93` | a decision point: display text, an optional gate, effects to run when taken, where it goes next |
| **navigation** | `NavigationTarget { target, is_end }` — `ast.rs:97-104` | `-> passage_name`, or `-> END` |
| **a gate** | `Condition` → `ConditionExpr` (`And`/`Or`/`Atom`) → `ConditionClause` (`Has` / `Compare` / `Not`) — `ast.rs:112-165` | `{ courage >= 5 }`, `{ inventory.key }`, boolean-combined |
| **a state change** | `Effect = Set \| Modify \| Call` — `ast.rs:190-233` | `~ gold += 100`, `~ flag = true`, `~ call("notify", ...)` |
| **a variable's value** | `Value = Null \| Bool \| Int \| Float \| String` — `~/dev/spween/src/value.rs:8-19` | the state vocabulary |

The DSL surface (from `README.md:66-92` and `src/lib.rs:13-34`) looks like:

```
---
id: tavern_encounter
title: The Mysterious Stranger
weight: 10
---
=== intro
A hooded figure sits alone in the corner of the tavern.
* [Approach them] { courage >= 5 }
  ~ courage -= 1
  -> conversation
* [Order a drink instead]
  ~ gold -= 2
  -> END
```

### 1.2 The execution model (a choice is the only way state changes)

The runtime is a tree-walking interpreter over a **user-supplied state backend**. The crucial design
fact — and the exact seam dregg plugs into — is that spween's runtime **knows nothing about your
game state**. It defers every read and write to an `EffectHandler` trait
(`~/dev/spween/src/runtime.rs:51-63`):

```rust
pub trait EffectHandler {
    fn get_var(&self, name: &str) -> Value;                 // read state
    fn set_var(&mut self, name: &str, value: Value);        // write state
    fn has(&self, category: &str, key: &str) -> bool;       // membership (inventory.sword)
    fn call(&mut self, name: &str, args: &[Value]) -> Result<(), String>;  // custom effect
}
```

The runtime holds only *control-flow* state — `RuntimeState = Running(passage_idx) \| Ended`
(`runtime.rs:67-72`). All *world* state lives behind the handler. The one state-advancing operation is
`select_choice(index)` (`runtime.rs:251-316`): it checks the chosen choice's condition against the
handler (`evaluate_condition`, `runtime.rs:345`), runs its effects through the handler
(`execute_effect`, `runtime.rs:423-448`), then navigates to the target passage. Conditions are pure
reads (`current_choices` reports each choice's `available` flag, `runtime.rs:216-238`); only
`select_choice` mutates.

**This is already dregg's shape.** A spween choice is a guarded, effectful state transition over an
externally-owned store — which is precisely a dregg *turn*: a cap-gated, receipted transition over a
cell, guarded by a `CellProgram` and applied by the verified executor. The `EffectHandler` is the
seam; dregg is the backend that makes the seam **persistent, unforgeable, and un-rewritable**.

### 1.3 What spween does NOT have (the holes dregg fills)

- **No persistence, no identity, no authority.** The playground handler is three `HashMap`s in memory
  (`~/dev/spween/playground/src/lib.rs:9-15`); `start()` throws state away
  (`playground/src/lib.rs:95-106`). There is no notion of *who* is choosing, no protection against a
  choice being forged, and no record that survives the run.
- **Single reader.** The runtime advances one `passage_idx`. There is no multiplayer, no shared
  world, no collective decision.
- **`call()` is an unverified escape hatch.** `Effect::Call` (`ast.rs:225-233`) just forwards a name +
  args to the handler; whether that call is *allowed* is entirely the handler's problem. dregg turns
  that into a cap-gated, executor-checked affordance.

---

## 2. THE DREGG PIECES IT COMPOSES WITH (grounded)

dregg's mapping — *a cell = an entity, a turn = a cap-gated + receipted action* — is stated verbatim
in the first-room README ("ember's vision"):
`~/dev/breadstuffs/starbridge-apps/first-room/README.md`, "The mapping" section. The pieces:

### 2.1 The world-cell + turn substrate (persistent shared state; a choice = a turn)

A dregg **cell** is a persistent entity whose installed `CellProgram` (its rules) is re-checked by the
verified executor on *every* turn. State changes only through a signed turn that the executor admits;
a refusal advances no chain and leaves no receipt (the "anti-ghost" tooth,
`first-room/src/room.rs:1-12`). This is exactly the `EffectHandler` contract, but *enforced*: nobody
can `set_var` except through a turn their capability authorizes, and the sequence of turns is a
tamper-proof ledger.

### 2.2 The live-world JS layer (a world you can crawl and drive as cells)

`deos-hermes`'s `run_js` tool (`~/dev/breadstuffs/deos-hermes/src/run_js.rs:1-45`) runs arbitrary JS
(real SpiderMonkey via `deos-js`) over a **live World**: it crawls cells (`deos.world.cells()`,
`cell.reflect()`) and *fires affordances* — each fire being "a real cap-gated verified turn →
`TurnReceipt`" (`run_js.rs:11-13`). The **ATTACHED** binding drives the operator's *actual* live
cells (`run_js.rs`, "Two binding paths"). This is the natural host for a spween world: the story
world is a set of cells; the JS layer renders prose, presents choices, and fires the chosen
choice-as-turn. Critically, the runtime is mounted under the *caller's attenuated cap, never root*
(`run_js.rs:19-24`) — a player drives the story only within their own authority.

### 2.3 privacy-voting (a collective decision, verifiably tallied)

`starbridge-privacy-voting` (`~/dev/breadstuffs/starbridge-apps/privacy-voting/README.md`) gives
one-vote-per-ballot polling with monotone, tamper-evident tallies — built from primitives only, with
**no domain-specific `Effect::CastVote`**. A **poll cell** holds `Monotonic` tallies and a `WriteOnce`
`CLOSED` slot (closes exactly once); a **ballot cell** has a `WriteOnce` `VOTE_SLOT` (one vote per
ballot, no double-spend). A `cast_vote` turn on a ballot triggers a `record_tally` turn on the poll
(`privacy-voting/src/reactor.rs:5-31`). This is the collective-decision engine: the audience's votes
are ballots; the winning branch is read off the closed tally.

### 2.4 branch-stitch-multiplayer (divergent timelines, merged soundly)

`starbridge-apps/branch-stitch-multiplayer` (`Cargo.toml` description) lets two participants **fork
one shared verified world, diverge on independent verified branches, and stitch back through a single
settlement-sound gate**: disjoint edits merge clean, a same-address clash is refused fail-closed
(never silent last-writer-wins), a revoked capability is linear-dropped while the rest settles. It is
`BranchStitchSession` (`starbridge_v2::branch_stitch_session`), lifted from
`ForkMembraneHost::stitch_pair`, merge guts in `grain-fork/src/lib.rs::stitch`
(`~/dev/breadstuffs/docs/deos/BRANCH-AND-STITCH-PROTOCOL.md`, opening). **This is multiplayer CYOA:
players fork the story, explore a branch privately, and stitch the good part back.**

### 2.5 first-room (a MUD room) and tussle (a joint-turn game)

- **first-room** (`starbridge-apps/first-room/src/room.rs`) is a `Room { cell, name, inhabitants }`:
  a place that *contains* inhabitants who act only through a mandate they provably can't exceed; each
  action is a real signed turn, each refusal rendered in-room. **This is the MUD room primitive** — a
  room is a cell, an inhabitant is a cell, entering/acting are turns.
- **tussle** (`starbridge-apps/tussle/Cargo.toml`) is a Toribash-style *two-party joint-turn* game:
  figures are cells, moves are `SEALED` commit-reveal (BLAKE3, fog-of-war), and resolution runs as a
  **2-party JOINT TURN** through the verified `settle_ring_verified` executor with a typed
  `SymMemberOf` enum tooth (an illegal move is an executor refusal, not app bookkeeping). **This is
  the pattern for simultaneous / hidden-information choices** — several players commit their move,
  reveal, and a deterministic joint turn resolves the branch.
- **gallery** (`starbridge-apps/gallery/README.md`) is sealed-submission commit-reveal curation —
  reusable when audience choices must be hidden until a reveal (blind voting).

### 2.6 The formal semantics: branching narrative IS the distributed-time-travel lattice

This is the deep result. `docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` proves that dregg's whole
branch/merge/settle picture is **navigation of the lattice of consistent configurations of a prime
event structure** (`§0` one-sentence answer; `§2.1` the formal object `(E, ≤, #)`,
`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:145-166`). A **configuration** is a downward-closed, conflict-free
set of events; **forking** is picking any configuration; **merging** is set union *when the union is
still conflict-free* (`§2.1`, ":167" region); **settlement** is a preferred maximal configuration
chosen by consensus. The blocklace *is* a prime event structure (`§3.1` table,
`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:341` onward), and Settlement Soundness is proven and
axiom-clean (`metatheory/Metatheory/SettlementSoundness.lean:153`; composed against the deployed
circuit at `metatheory/Dregg2/Circuit/SettlementSoundness.lean:244`).

**A CYOA's branch tree is a config lattice.** Every passage-path a player can walk is a configuration
of "choices taken so far"; a fork is a player exploring a counterfactual branch; undo is
causal-consistent reversibility (RCCS, `§2.2`, `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:172-211`) — you
can rewind a story branch exactly as far back as causality allows. Two players whose branches touch
disjoint state merge; two whose branches edit the same variable *conflict* and cannot silently merge
(`#`, conflict inheritance). **spween's narrative branch structure is not merely *like* dregg's
config lattice — under this mapping it *is* one.** The canon story is the settled tip; side branches
are entertained but real only once stitched onto the consensus tip.

---

## 3. THE INTEGRATION — how spween runs on dregg

The mapping is one-to-one because spween already externalized its state behind a trait and dregg is
the enforcing backend:

| spween | dregg | grounding |
|---|---|---|
| a `Scene` (whole story) | a **world-cell** whose `CellProgram` encodes the passage graph + effect rules | `ast.rs:19-26` ↔ cell/`CellProgram` (`first-room/README.md` mapping) |
| a `Passage` (`name`) | the cell's current **passage slot** (a `SetField` state) | `ast.rs:51-58` ↔ `Effect::SetField` (privacy-voting/gallery use it) |
| variables (`get_var`/`set_var`) | cell **slots**, written by turns, guarded by slot caveats | `runtime.rs:51-63` ↔ `StateConstraint` caveats (`privacy-voting/README.md`) |
| `select_choice(i)` (state advance) | a **cap-bounded turn** — the executor checks the choice's `condition` as a `CellProgram` predicate and applies its effects | `runtime.rs:251-316` ↔ verified turn |
| a `Choice.condition` gate | a `CellProgram` predicate re-checked every turn | `ast.rs:112-165` ↔ `CellProgram::evaluate` (tussle `SymMemberOf`) |
| `Effect::Call` (unverified escape) | a **cap-gated affordance** — allowed only if the caller's held authority satisfies `required` | `ast.rs:225-233` ↔ `run_js.rs:19-24` cap tooth |
| who is playing | the **capability** on the turn — nobody can forge another player's move | (no spween analog) ↔ `Authorization::Signature` |
| the playthrough history | the **receipt ledger** — a tamper-proof, un-retconnable record | (no spween analog) ↔ `TurnReceipt` |
| a collective choice (audience decides) | a **vote** whose winning branch is a turn | (no spween analog) ↔ privacy-voting |
| divergent multiplayer timelines | **branch-stitch** over the config lattice | (no spween analog) ↔ branch-stitch-multiplayer / §2.6 |

Three properties fall out for free, none of which stock spween has:

1. **Unforgeable moves.** A choice is a signed turn bound to the player's cell; you cannot cast
   another player's choice (the confused-deputy property, `run_js.rs:15-17`).
2. **Un-rewritable narrative.** The story history is the receipt ledger; a past passage/choice cannot
   be secretly changed — the story *literally cannot be retconned* (anti-ghost + monotone slots).
3. **Provable availability of a choice.** A gated choice (`{ courage >= 5 }`) is a `CellProgram`
   predicate the executor re-checks; a client cannot present an ineligible choice as taken.

---

## 4. THE MODES

### 4.1 Single-player CYOA — a verifiable playthrough

The smallest mode. A `Scene` compiles to one world-cell owned by the player. Each `select_choice`
is a turn on that cell: gate checked → effects applied → passage slot advanced. The whole playthrough
is a receipt chain — a *provable* run (you can prove you reached the secret ending honestly, that you
had the courage stat, that you never edited the save). spween's runtime already produces exactly this
control flow (`runtime.rs:251-316`); dregg makes the state authority-bound and the trace permanent.

### 4.2 Collective CYOA — the audience votes each branch (THE KILLER MODE)

This is Twitch-Plays / mass-participation interactive fiction, made trustworthy. At each choice
passage:

1. The world-cell is at passage `P`, exposing its `Choice`s (`current_choices`, `runtime.rs:216-238`)
   — with per-choice availability already computed as `CellProgram` predicates.
2. A **poll cell** opens over the available choices; each audience member gets a **ballot cell** (one
   vote per ballot, `WriteOnce VOTE_SLOT`, `privacy-voting/README.md`). Votes are cast as turns; the
   `record_tally` reactor keeps a monotone, tamper-evident tally (`privacy-voting/src/reactor.rs`).
   Optionally the ballots are *sealed* (commit-reveal, gallery/tussle style) so early votes don't
   sway later ones — blind collective choice.
3. The poll closes exactly once (`WriteOnce CLOSED`). The winning branch is read off the tally, and
   **the winning choice is applied as a single turn on the world-cell** — the story advances to the
   voted passage.

The result: *uncensorable collective fiction*. Run on the federation, no operator can stuff the
ballot, silently pick a different branch, or rewrite what the crowd chose — every step is a receipt.
This is the mode where the §0 spine is most visible: the collective choice *is* a governance vote over
the shared story-state, and dregg treats it as exactly that.

### 4.3 A MUD — rooms as cells, commands as turns, multiplayer via branch-stitch

- **Rooms are cells** (`first-room/src/room.rs`): a `Room { cell, name, inhabitants }`. A spween
  `Passage` maps to a room; navigation (`-> tavern`) is moving between room-cells.
- **A player is an inhabitant cell** acting only through a mandate it can't exceed
  (`first-room/README.md` mapping). A MUD command (`go north`, `take sword`, `attack goblin`) is a
  **turn**: a spween `Choice`/`Effect` fired as a cap-gated affordance. `take sword` is `Effect::Call`
  → a cap-checked inventory turn (`ast.rs:225-233` ↔ `run_js.rs` cap tooth). Nobody can forge your
  character's actions; an over-reach is refused in-band and rendered as an in-room refusal
  (`room.rs:1-12`).
- **Multiplayer / divergent play is branch-stitch.** Two players in the same room fork the world,
  each explores their own thread, and stitch back through the settlement-sound gate: disjoint actions
  merge, a genuine conflict (both grab the one sword) is refused fail-closed, never silent
  last-writer-wins (`branch-stitch-multiplayer/Cargo.toml`; §2.6). Simultaneous hidden actions (two
  players' combat moves) use the tussle joint-turn commit-reveal pattern (`tussle/Cargo.toml`).
- **An attested NPC dungeon-master** — the striking one. dregg has a **confined, attested LLM brain**
  (`ConfinedBrain` plugs a jailed subprocess into the `AgentBrain` seam; the crown / grain-jail line —
  a model-driven body that reaches exactly one granted egress door and drives a real cap-gated,
  metered cell). Wire that brain as the MUD's dungeon-master: it narrates and reacts by *firing turns*
  through `run_js` over the world (`run_js.rs`), **empowered but bounded** — it authors freely inside
  its own attenuated authority and can never rewrite a player's state or exceed its mandate. A
  verifiable AI game-master whose every narration-effect is a receipted turn.

---

## 5. WHAT KANZOKAX BUILDS FIRST — the smallest real thing

**A spween story compiled to a dregg world-cell + a vote-driven branch loop, running.** Concretely:

1. Take a spween `.scene` (start with `~/dev/spween/playground/www/examples/tavern.scene`).
2. Compile it to a world-cell: passages → the passage-slot state machine, choices → the turn-able
   transitions with their conditions as `CellProgram` predicates, effects → slot writes (§6 step 2).
3. Drive it in collective mode: at each choice passage, open a privacy-voting poll over the available
   choices, let the audience vote, close, and apply the winning choice as one turn.
4. Run it locally first (single node, the `run_js`/deos-js live-world host); then on the federation for
   uncensorable collective fiction.

That is the whole loop — a story, a crowd, a verifiable branch each round — and it reuses three
existing apps almost wholesale.

---

## 6. BUILDABLE-NOW vs NEW

### Buildable now (the substrate already gives it)

- **The vote → decision engine.** privacy-voting is a complete one-vote-per-ballot, monotone,
  tamper-evident poll with a tally reactor (`privacy-voting/README.md`, `reactor.rs`). The
  collective-choice mode needs orchestration around it, not new primitives.
- **The room / entity / command substrate.** first-room already models rooms-as-cells, inhabitants
  acting through mandated turns, and in-room refusals (`first-room/src/room.rs`).
- **Multiplayer divergent timelines.** branch-stitch-multiplayer + `BranchStitchSession` is a
  runnable fork→diverge→stitch primitive with the soundness gate (`branch-stitch-multiplayer`,
  `BRANCH-AND-STITCH-PROTOCOL.md`).
- **A live world you can crawl + drive from JS.** `run_js`/deos-js drives a live World, each fire a
  cap-gated receipted turn (`run_js.rs`).
- **Hidden / simultaneous choices.** tussle's commit-reveal joint-turn + gallery's sealed submission
  give blind voting and simultaneous moves off the shelf.
- **The formal narrative semantics.** The config-lattice / RCCS / Settlement-Soundness story is
  proven (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`; `SettlementSoundness.lean:153`) — the branching-story
  math is done, not to-be-invented.

### New (what a real spween-on-dregg needs)

1. **A spween → cell compiler.** The genuinely new artifact: lower a parsed `Scene`
   (`spween::parse`, `src/lib.rs:63`) into a `FactoryDescriptor` + `CellProgram`. Passages → the
   passage-slot state machine; `Choice.condition` (`ast.rs:112-165`) → `CellProgram` predicates;
   `Effect::Set/Modify` (`ast.rs:190-221`) → slot writes with the right caveats (`Monotonic` for
   score-like stats, `WriteOnce` for one-shot flags); `NavigationTarget` (`ast.rs:97-104`) → the
   passage transition. spween is `no_std`-friendly and already `serde`-serializable behind a feature
   (`Cargo.toml` `serde`), so the AST ships cleanly to the compiler.
2. **A dregg `EffectHandler` impl.** Implement spween's own trait (`runtime.rs:51-63`) backed by cell
   slots + turns instead of HashMaps — so the *stock spween runtime* can drive a dregg world directly
   (the fastest path to single-player mode, §4.1). `get_var`/`has` read cell state; `set_var`/`call`
   emit turns.
3. **The vote-driven branch loop.** The orchestration that, at a choice passage, opens a poll over
   `current_choices`, collects ballots, closes, and applies the winner as a turn (§4.2). This is glue
   over privacy-voting, not a new primitive.
4. **The MUD command → turn mapping.** A parser from free-text MUD commands to spween
   choices/effects, each fired as a cap-gated turn (§4.3). `Effect::Call` is the natural target
   (`ast.rs:225-233`).
5. **(Stretch) the attested-DM binding.** Wire the confined LLM brain as a `run_js`-driven narrator
   whose effects are receipted turns (§4.3).

**Design note (project value, not a shortcut):** the compiler's default must lower `Effect::Call`
(`ast.rs:225-233`) to a *cap-gated affordance*, never an `Authorization::Unchecked` escape — the
whole point is that a story effect can't do anything the player's authority doesn't permit. Keep
spween's own `EffectHandler` trait as the seam (don't fork the engine); dregg is the backend behind
it.

---

## 7. RANKED BUILD STEPS (spween-on-dregg MVP)

1. **`EffectHandler` over a dregg cell** — implement `runtime.rs:51-63` backed by one world-cell's
   slots + turns. Lands single-player verifiable CYOA (§4.1) with the *stock* spween runtime. Smallest
   real thing that proves the seam.
2. **spween → cell compiler v0** — lower `Scene` → `FactoryDescriptor` + `CellProgram` (passage state
   machine + `Choice.condition` predicates + effect slot-writes). Makes the story rules
   executor-enforced, not just handler-enforced.
3. **The vote-driven branch loop** — glue privacy-voting to `current_choices` at each choice passage;
   close → apply winner as a turn. Lands **collective CYOA (§4.2), the killer mode.**
4. **Sealed / blind voting** — swap plain ballots for commit-reveal (tussle/gallery) so early votes
   don't anchor. Optional but high-value for fairness.
5. **MUD command → turn mapping + rooms-as-cells** — reuse first-room's room model; parse commands to
   spween choices/effects fired as turns. Lands single/small-group MUD (§4.3).
6. **Multiplayer divergent play via branch-stitch** — fork the world per player thread, stitch back
   through the soundness gate. Lands multiplayer MUD / divergent-timeline CYOA.
7. **(Stretch) attested NPC dungeon-master** — the confined LLM brain narrates by firing receipted
   turns through `run_js`.

Run steps 1–3 locally, then put step 3 on the federation: that is on-chain, collectively-authored,
uncensorable interactive fiction — the vision, standing up.

---

## 8. THE POINT, restated

spween is a clean narrative-choice engine that deliberately externalized its state behind one trait.
dregg is the backend that makes that state persistent, unforgeable, un-rewritable, and
**collectively decidable**. The moment you plug them together, a story choice and a governance vote
stop being two different things — they are both *a group deciding what happens next over shared
state, and leaving a receipt*. Interactive fiction becomes a public, tamper-proof, collaboratively
authored artifact: a story the crowd writes together and no one can retcon.

```
a passage is a place,        a choice is a turn,
a crowd is the author,       a receipt is the proof —
the story cannot lie
about the road it took.
```
