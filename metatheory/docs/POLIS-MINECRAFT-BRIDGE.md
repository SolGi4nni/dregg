# The polis Minecraft bridge — real LLM agents in a real world, governed by the verified Lean `govStep`

This is the design for the substrate swap the in-Lean sandbox deferred: replace the scripted Lean
policies with **real LLM agents** acting in a **real Minecraft world**, while keeping the *same*
verified governor that the sandbox proved tames every adversary. The arena gets real; the cage stays
proven.

The discipline carries over verbatim: **verify the cage, not the animal.** We never inspect the
agent's interior (its weights, its chain-of-thought, its "intent"). We govern the **proposed move**
against a **floor** read off **public world state**, admit-or-shield, and log. The governor is the
constitution's envelope (`docs/POLIS.md`), made computable in `PolisSandbox.govStep` and proven safe
in `PolisSandboxN.sandbox_governed_safe` (∀ controller, ∀ agent count). The LLM is just one more
controller — the universally-quantified `ctrl : World → Move`.

---

## 1. Architecture

Three processes, one trust boundary.

```
  ┌─────────────────┐     propose(Move)      ┌──────────────────────┐
  │  LLM AGENT LOOP  │ ─────────────────────▶ │   GOVERNOR SERVICE   │
  │  (per bot)       │                        │  (the verified       │
  │  observe→reason  │ ◀───────────────────── │   govStep, as a      │
  │  →propose        │   admit / refuse+why   │   lean_exe)          │
  └────────┬─────────┘                        └──────────┬───────────┘
           │ admitted move only                          │ reads abstract World
           ▼                                              │ (projected from world)
  ┌─────────────────┐    bot.dig/place/...    ┌──────────────────────┐
  │   MINEFLAYER     │ ─────────────────────▶ │   MINECRAFT SERVER    │
  │   bot (JS)       │ ◀───────────────────── │   (vanilla / Paper)   │
  └─────────────────┘    world snapshot       └──────────────────────┘
```

- **LLM agent loop (one per bot).** A Mineflayer bot supplies perception (nearby blocks, entities,
  inventory, position, who-built-what from a claims ledger). An LLM is prompted with that perception
  plus the **action grammar** (§2) and asked to emit ONE structured `Move` per tick (a JSON tool
  call). The agent is free to scheme; it just cannot act outside the grammar, and every emitted move
  goes to the governor first. The LLM's reasoning is private and **never read by the governor** —
  this is the ∀-opaque controller, exactly as in the proof.

- **Governor service.** A long-lived process wrapping the verified `govStep`. It holds the current
  **abstract `World`** (the projection of the Minecraft world onto the small state the floor needs —
  §3). On each proposal it computes `stepMove world m`, evaluates `worldFloor` (and the
  liveness-aware `reachHome`-style viability check — §4), and returns **admit** (with the new
  abstract world) or **refuse** (with the *reason*: which floor conjunct the move would break). It is
  the only component that decides; it is the only component that must be trusted; and its decision
  function is the kernel-checked Lean term.

- **Apply / block.** On **admit**, the Mineflayer bot executes the corresponding real action
  (`bot.dig`, `bot.placeBlock`, `bot.attack`, pathfinder goto, a trade transaction, a claim write).
  On **refuse**, the action is **not executed**; the bot receives the refusal+reason (which it may
  feed back to the LLM as an observation: "your build-grief on Alice's house was refused"), and the
  event is appended to an **audit log** (move, world-before, predicted world-after, the broken floor
  conjunct, timestamp, actor). The refusal is the live-world analogue of `govStep`'s `else w`
  branch — the shield.

The trust story is the dregg story: **the governor is the seam, and the seam is verified.** Bots,
LLMs, and the Minecraft server are all untrusted. A bot that lies about its intent, an LLM that
plans domination across many turns, a compromised Mineflayer client — none can move the abstract
world below the floor, because the only path from a proposal to an applied effect runs through
`govStep`, and `govStep` provably preserves the floor for *any* controller.

---

## 2. The action grammar — Minecraft actions as sandbox `Move`s

A `Move` in the sandbox is `{ actor, action }`. We instantiate `Act` for Minecraft. Each constructor
is a coarse, **governable** abstraction of a family of low-level Mineflayer calls — coarse enough that
the floor can reason about it, faithful enough that the bot can execute it.

| sandbox `Act` (Minecraft) | LLM emits | Mineflayer executes on admit | floor cares because… |
|---|---|---|---|
| `move (to : Region)` | `{move, to}` | pathfinder `goto` | path-home preservation; spawn proximity |
| `mine (b : BlockRef)` | `{mine, block}` | `bot.dig` | resource monopoly; griefing another's build |
| `place (b : BlockRef)` | `{place, block, item}` | `bot.placeBlock` | griefing (placing in another's claim / boxing-in) |
| `attack (v : AgentId)` | `{attack, victim}` | `bot.attack` | spawn-camping; foreclosing a victim's exit |
| `trade (v, give, get)` | `{trade, …}` | villager / chest-swap protocol | laundering (claiming tier on un-earned goods) |
| `claim (r : Region)` | `{claim, region}` | append to claims ledger | resource monopoly; everyone retains buildable land |
| `noop` | `{noop}` | — | the always-safe move (shield's fallback) |

This is the **exact shape** of `PolisSandbox.Act` (`noop | stepHome | trap victim`) and
`PolisSandboxN.Act` (`noop | stepHome | trap (victim : Fin n)`), widened from 3 to 7 constructors.
`trap` generalizes to `attack`/`place`/`mine` whenever the effect *forecloses* a victim; `stepHome`
generalizes to `move`. The N-agent file already proves governance for `Act n` over `Fin n` agents
with `trap (victim : Fin n)` — the Minecraft `attack (v : AgentId)` is the same constructor under a
different name, so `sandbox_governed_safe` applies unchanged.

**The grammar is the safety boundary on expressivity.** Anything an agent cannot express as a `Move`
cannot reach the world. Strong forms of harm that have no constructor are *safe by
inexpressibility* — the same load-bearing line dregg uses everywhere (e.g. the strong guarded hole).
A low-level Mineflayer escape hatch (raw packet injection) would bypass this; the bot process must be
the **only** holder of the server connection and must accept *only* admitted `Move`s from the
governor — never act on its own LLM output directly.

---

## 3. The floor — a Minecraft-meaningful `worldFloor`

The abstract `World` is a **projection** of the live Minecraft world onto exactly the state the floor
predicates need. Following `PolisSandboxN.World n = Fin n → …`, we use a per-agent record plus shared
ledgers:

```
World :=
  { perAgent : AgentId → { pos : Region, lastHit : Nat, reachableHome : Bool }
  , claims   : Region → Option AgentId          -- the claims ledger (who owns what land)
  , holdings : AgentId → ResourceVec            -- per-agent stockpile of each tracked resource
  , builds   : BlockRef → Option AgentId }       -- who placed/owns each protected block
```

The **floor** is a conjunction of decidable predicates — each conjunct is a Minecraft-meaningful
right, and each maps onto a sandbox theorem already proven:

1. **No spawn-camping.** For every agent `v`, the time since `v` was last killed near a spawn region
   is above a cooldown, OR no other agent is positioned within attack range of `v`'s spawn. This is
   the `trap`/`attack` foreclosure conjunct — exactly `worldFloor`'s "every agent retains its
   bounded exit" (`PolisSandbox.worldFloor : w false ≤ budget ∧ w true ≤ budget`), with "distance to
   home > budget" recast as "respawn path is camped."

2. **No permanent resource monopoly.** For each tracked resource, no single agent holds more than
   `cap` of the reachable total — `∀ a, holdings a r ≤ cap`. This is *verbatim*
   `PolisSandboxCompete`'s fair-share floor (`holdF ≤ cap ∧ holdT ≤ cap`), where the shared pool is a
   biome's finite ore/wood and the `grab` move is `mine`. `governed_preserves_commons` is the proof
   that the greedy miner is capped and the commons survives for the slower agent.

3. **No griefing another's build.** A `mine`/`place` move that destroys or boxes-in a block owned by
   another agent (per the `builds` ledger and the claims ledger) breaks the floor. The owner's
   structure is their "exit option"; griefing forecloses it — the `trap` shape again, keyed on
   `builds b = some other`.

4. **Everyone retains a path home.** For every agent, a respawn/return route to its claimed base must
   remain traversable after the move — no agent may seal another in. This is the **liveness** floor,
   not the one-step floor: it is precisely `PolisSandboxLongGame.reachHome` ("the victim can reach
   home within `k`"), generalized to "agent `v` can reach its base within `k` traversal steps given
   the post-move block/claim layout." The `close`-the-gate long game is, in Minecraft, *walling
   someone in over several lawful-looking placements* — caught only by the viability governor (§4).

`worldFloor` is the AND of (1)–(4) and is **decidable** (each conjunct is a bounded `∀` over the
fixed agent set / region grid — `Fintype.decidableForallFintype`, as `PolisSandboxN` already uses).
Decidability is what lets `govStep` *run* and lets the conjunct-level refusal reason be reported.

**Opacity is preserved.** Every conjunct is a function of *public* world state (positions, ledgers,
holdings, block ownership). None reads an agent's interior. We govern the trace-shape — what the move
*does* to shared state — not the motive, exactly as `govStep` never inspects `ctrl`.

---

## 4. How the verified `govStep` generalizes to it

The generalization is **structural substitution**, not new metatheory. The proofs depend only on:

- a type `World` with `Decidable (worldFloor w)` — satisfied by the projection of §3;
- a `stepMove : World → Move → World` — the abstract effect of an admitted action;
- `govStep w m := if worldFloor (stepMove w m) then stepMove w m else w` — unchanged.

Then the live-world guarantees fall out of the *existing* theorems by instantiation:

- **Safety, ∀ adversary, ∀ agent count** — `PolisSandboxN.sandbox_governed_safe`:
  `∀ ctrl w0, worldFloor w0 → ∀ k, worldFloor (govTraj ctrl w0 k)`. The LLM is the `ctrl`. No
  trajectory of admitted moves — however cleverly the LLM schemes — drops the abstract world below
  the floor.
- **Least-restrictive / gentle governance** — `govStep_admits_benign`
  (`worldFloor (stepMove w m) → govStep w m = stepMove w m`) and `govStep_refuses_only_harmful`
  (`govStep w m ≠ stepMove w m → ¬ worldFloor (stepMove w m)`). Every honest move is applied
  untouched; **every refusal is a genuine floor-break**, so the audit log never contains a false
  positive. This is what makes the governor *fair* to play under, not a nag.
- **The long game** — the one-step floor (conjuncts 1–3) is myopic and a multi-turn LLM *will*
  exploit it (the gate-close = wall-someone-in attack). Conjunct 4 is the **viability governor**
  `viabilityGov w a := if reachHome budget (gstep w a) then gstep w a else w`, and
  `PolisSandboxAdaptive.viability_withstands_all_attacks` proves that from a reach-home-able world,
  **no adaptive attack of any depth** strands a victim. An LLM searching the move space for a
  stranding sequence is exactly `existsStrandingAttack`; against the viability conjunct it provably
  `= false` forever. So the Minecraft "wall someone in slowly" attack is closed *by a theorem*, not
  by a heuristic.
- **Coalitions** — `PolisSandboxN.coalition_single_erasure_insufficient`: two bots ganging up to
  foreclose a third is a texture the governor still tames, and the detector correctly attributes it
  to the *whole* coalition (erasing one member doesn't restore the victim). Multi-LLM Minecraft
  politics is in scope.

The one obligation the bridge adds is **projection faithfulness**: the abstract `stepMove` must
over-approximate the real Minecraft effect of an admitted `Move` (i.e. the real effect is no *worse*
for the floor than the abstract one predicts). This is the live-world analogue of dregg's
executor↔spec corner. It is discharged by making the projection conservative (round positions to
region cells; treat ambiguous block ownership as owned-by-other) and by a **runtime invariant check**:
after applying an admitted move, re-project the real world and assert `worldFloor` still holds; if
the real world ever drops below the floor despite an admit, that is a projection bug, surfaced loudly
(green-or-bust — never silently continue).

---

## 5. Infra plan (honest, buildable)

### 5.1 The Lean→service bridge

Two routes, chosen by a **differential check**, not by taste:

- **Route A — compile a `lean_exe` (preferred).** Add a `[[lean_exe]]` target to `lakefile.toml`
  exposing `@[export] govStepC : abstract-world-bytes → move-bytes → (admit/refuse + new-world)`.
  The governor service is then *the actual kernel-checked term*, called over a tiny line-protocol
  (newline-delimited JSON on stdin/stdout, or a Unix socket). No re-implementation, no drift: the
  thing that decides in production is the thing that was proven. Cost: a Lean toolchain in the
  deployment, and serialization glue (the abstract `World` is small — a few hundred bytes — so this
  is cheap). This is the route the memory's "EMBEDDABLE-LEAN-RUNTIME" spike already showed is viable
  (the executor PD boots an embedded Lean runtime).

- **Route B — port `govStep` to the service language (TS/Rust) WITH a differential check.** If a
  Lean toolchain in the loop is too heavy, re-implement `govStep`/`worldFloor`/`reachHome` in the
  service, and run a **continuous differential test**: a corpus of `(world, move)` cases (random +
  the proven `#eval` fixtures from the sandbox files) is decided by *both* the Lean `lean_exe` and
  the port, and any disagreement fails CI. This is the dregg "two gates provably agree" pattern, but
  honestly *weaker* than Route A: the differential proves agreement only on the sampled corpus, not
  universally. **Default to A; fall back to B only under a measured toolchain-weight constraint, and
  never ship B without the differential gate.**

Either way the **decision logic is never hand-translated into prompt text** — the LLM proposes; Lean
decides.

### 5.2 The Mineflayer / LLM loop

- One Node process per bot, `mineflayer` + `mineflayer-pathfinder`. Perception → a compact
  observation JSON → LLM (one structured-output call per tick, the `Move` grammar as the tool
  schema). The tick rate is throttled (e.g. one proposed move per 1–2 s) so the LLM call latency
  (§5.3) and the governor round-trip fit inside a tick.
- The bot process holds the *only* server connection and acts *only* on governor-admitted moves.
- The claims/builds/holdings ledgers are owned by the governor service (it is the source of truth for
  the abstract world); the bots read them via perception, they do not write them directly — a write
  is the *effect of an admitted `claim`/`place`/`mine` move*.

### 5.3 Latency

- LLM call: ~0.5–3 s/tick dominates. Governor round-trip: sub-millisecond (`govStep` is a bounded
  `decide`-shaped computation over a small world; the serialization is the only real cost). So the
  governor is **never the bottleneck**, and we can afford the conservative re-projection invariant
  check (§4) on every applied move.
- The viability conjunct (`reachHome budget`) is a bounded `k`-step search over the region grid;
  keep `k` and the grid small enough that it stays well under a millisecond — the same "small worlds
  for cheap decide" discipline the sandbox uses. If the grid grows, precompute reachability
  incrementally rather than raising `k`.

### 5.4 Open problems (named, with their closure lane)

- **Partial observability.** The governor needs the *true* abstract world to decide, but Minecraft
  perception is local (a bot sees nearby chunks). Closure: the governor maintains the authoritative
  ledgers (claims/builds/holdings are governor-owned, so exact), and for *positional* conjuncts uses
  a server-side query (RCON / a server plugin) rather than per-bot perception — the governor reads
  ground truth, not a bot's possibly-stale view. The bot's perception drives the *LLM*, not the
  *decision*.
- **Projection faithfulness (the hard corner).** Proven only by conservative over-approximation +
  the runtime invariant assertion (§4); a *formal* refinement (real Minecraft step refines the
  abstract `stepMove`) is out of reach (no formal Minecraft semantics) and is the honest terminal
  seam here — analogous to dregg's irreducible crypto/identity seams. We bound it (conservative
  projection, loud invariant violation), we do not eliminate it.
- **Liveness scope.** Conjunct 4 proves *reach-home is preserved*; it does not prove an agent
  *makes progress on its own goals*. The sandbox's `viability_withstands_all_attacks` is the
  available guarantee; richer liveness (obligations complete) is the same open milestone the in-Lean
  phase listed.
- **Grammar coverage vs. expressivity.** Harm only via the grammar is governed; the grammar must be
  rich enough to be *fun* yet coarse enough to *decide*. Widening it (e.g. redstone contraptions,
  TNT) reopens the floor design — each new constructor needs its floor conjunct + its theorem before
  it ships (we do not name, we ship).

---

## 6. What carries over, in one line per claim

| live-world claim | the proof it rests on |
|---|---|
| No LLM trajectory drops the world below the floor | `PolisSandboxN.sandbox_governed_safe` |
| Honest play is never refused; every refusal is a real harm | `govStep_admits_benign`, `govStep_refuses_only_harmful` |
| The slow "wall-someone-in" long game is closed | `PolisSandboxAdaptive.viability_withstands_all_attacks` |
| A greedy miner can't monopolize the commons | `PolisSandboxCompete.governed_preserves_commons` |
| Coalition foreclosure is tamed + correctly attributed | `PolisSandboxN.coalition_single_erasure_insufficient` |
| The governor decides without reading the agent's interior | the ∀-opaque `ctrl` in every `govTraj` theorem |

The grounding stays the constitution (`docs/POLIS.md`) and the runnable arena (`docs/POLIS-SANDBOX.md`):
the Minecraft bridge changes only *who the controller is* (an LLM, not a scripted policy) and *what
the world is* (a Minecraft server, not a `Fin n → Nat`). The governor — the proven part — does not
change at all. That is the whole point.
