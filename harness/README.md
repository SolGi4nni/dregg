# minecraft-polis-harness

A real agent harness: a Mineflayer (Node.js) Minecraft bot driven by a Claude
LLM agent loop, where **every proposed action passes through the verified polis
governor before it can touch the world**.

The loop:

```
connect bot
  └─ each tick:
       observe world ─▶ LLM proposes action ─▶ GOVERNOR decides ─┬─ admit ─▶ apply ─▶ log
                                                                 └─ refuse ──────────▶ log (world unchanged)
```

The governor is the seam where the kernel-checked decision from
`metatheory/Metatheory/PolisSandbox.lean` plugs in. It enforces `govStep`:
**admit a move iff executing it preserves the shared floor; otherwise shield**
(refuse, world unchanged). That decision is proven safe for *every* controller —
the LLM included — by `sandbox_governed_safe`, and proven gentle (honest play is
never blocked, only genuine harm is refused) by `govStep_admits_benign` /
`govStep_refuses_only_harmful`. We verify the cage, not the animal.

## Layout

```
harness/
  package.json              deps: @anthropic-ai/sdk, mineflayer
  README.md                 this file
  src/
    index.js                the governed agent loop (live + dry-run entry)
    agent.js                Claude proposes one action/tick (model: claude-opus-4-8)
    world.js                projects live MC state -> governor's model; simulates a move
    actuator.js             applies an ADMITTED action to the bot (only reached on admit)
    log.js                  one-line verifiable receipt per tick
    dryrun.js               runs the loop with a fake bot + scripted agent (no deps)
    governor/
      governor.js           THE SEAM: admit/refuse, stub + lean backends
      selftest.js           asserts the govStep contract (no deps)
  governor-lean/
      README.md             how the verified lean_exe replaces the stub
```

## What runs right now vs. what needs a server / key

**Runs with nothing but Node** (no Minecraft server, no API key):

```
node src/governor/selftest.js     # asserts the govStep admit/refuse contract
DRY_RUN=1 node src/index.js       # drives the FULL loop with a fake bot + scripted agent
```

The dry-run exercises the exact wiring of live mode — observe → propose → govern
→ apply/shield → log — substituting only the bot (scripted state) and the agent
(scripted proposals, including a deliberate self-domination move that the
governor refuses).

**Needs a reachable Minecraft server AND an Anthropic API key** (the live loop):

```
npm install
export ANTHROPIC_API_KEY=sk-ant-...
export MC_HOST=localhost MC_PORT=25565
node src/index.js
```

Without a server `mineflayer.createBot` cannot connect; without a key the agent
call fails. That is expected — the live loop genuinely needs both. Use the
dry-run / selftest to see the structure work end-to-end without them.

## The governor backends

`src/governor/governor.js` selects a backend by `GOVERNOR_BACKEND`:

- `stub` (default) — a faithful JS re-implementation of the floor check. Runs
  with no Lean toolchain. It is a *mirror* of the proof, not the proof.
- `lean` — shells out to a `lean_exe` that decides admit/refuse with the same
  kernel-checked `govStep`. This is where the verified artifact replaces the
  mirror. See `governor-lean/README.md` for the wire contract and how to build
  the executable. The agent loop is identical either way — swapping the mirror
  for the proof changes nothing upstream.

## Configuration (env)

| var | default | meaning |
|---|---|---|
| `ANTHROPIC_API_KEY` | — | required for the live loop |
| `ANTHROPIC_MODEL` | `claude-opus-4-8` | LLM agent model (`claude-sonnet-4-6` for cheaper) |
| `MC_HOST` / `MC_PORT` | `localhost` / `25565` | Minecraft server |
| `MC_USERNAME` / `MC_AUTH` | `polis-agent` / `offline` | bot identity |
| `TICK_MS` | `4000` | ms between governed ticks |
| `DRY_RUN` | — | `1` to run the no-deps dry run |
| `GOVERNOR_BACKEND` | `stub` | `stub` or `lean` |
| `GOVERNOR_LEAN_EXE` | — | path to the lean governor exe (when backend=lean) |

## Honest limits

- This is a **skeleton**: the world projection in `world.js` (health/food →
  distance-from-safe) and the action vocabulary are illustrative, tuned so the
  seam is demonstrable. A real deployment defines its own floor.
- The default governor is the **stub** (a JS mirror). The `lean` backend's
  executable is specified (`governor-lean/README.md`) but not yet built into the
  metatheory lakefile — until then the running decision is the mirror, which
  agrees with the proof by construction but is not itself kernel-checked.
- The actuator implements a few actions; risky ones (`dig_down`,
  `jump_into_lava`) are intentionally not actuated — they exist so the agent can
  propose them and the governor can refuse them, demonstrating the seam.
