# The verified governor backend

The harness's governor seam (`src/governor/governor.js`) has two backends. The
default `stub` is a faithful JavaScript mirror of the admit/refuse decision. This
directory is for the `lean` backend — where the **kernel-checked** decision
replaces the mirror, so the verdict the harness enforces is the same `govStep`
that `sandbox_governed_safe` is proven about.

## The decision being enforced

From `metatheory/Metatheory/PolisSandbox.lean`:

- `worldFloor w` — every tracked agent stays within recovery `budget` (= 5).
- `govStep w m` — **admit the move iff the resulting world preserves the floor,
  else shield** (leave the world unchanged).

And the guarantees (`PolisSandbox.lean`, `PolisSandboxRun.lean`):

- `sandbox_governed_safe` — under `govStep`, the floor holds at every tick, for
  **every** controller (the LLM included). The cage is verified, not the animal.
- `govStep_admits_benign` — any floor-preserving move is admitted unchanged
  (honest play is never blocked).
- `govStep_refuses_only_harmful` — every refusal is a genuine floor break.

The JS stub re-implements exactly this floor check. The Lean backend calls the
real definition.

## Wire contract

The Lean executable reads one line of JSON on stdin and prints one line of JSON
on stdout:

```
stdin:  {"world":{"self":1},"nextWorld":{"self":99},"budget":5}
stdout: {"admit":false,"reason":"move breaks the floor"}
```

`src/governor/governor.js` (the `lean` backend) already speaks this contract.

## Building the executable

The decision is pure and decidable, so a small `lean_exe` over `PolisSandbox`'s
`worldFloor` is all that's needed. Sketch (`PolisGovernorMain.lean`):

```lean
import Metatheory.PolisSandbox
-- parse stdin JSON -> a Finset/list of agent dists for `nextWorld`
-- decide `worldFloor nextWorld` using the EXISTING Decidable instance
-- print {"admit": <decide result>, "reason": ...}
```

The load-bearing line is that `admit` is computed by `decide (worldFloor
nextWorld)` against the very instance the theorems use — not a re-derivation. Add
a `lean_exe polis_governor` target to the metatheory lakefile, build with
`lake build polis_governor`, then run the harness with:

```
GOVERNOR_BACKEND=lean \
GOVERNOR_LEAN_EXE=/Users/ember/dev/breadstuffs/metatheory/.lake/build/bin/polis_governor \
node src/index.js
```

Until that target exists, the stub backend is the running governor and this file
is the spec the Lean exe must meet. The stub and the proof agree by construction
(same floor check); the Lean backend removes the "by construction" and replaces
it with "by the kernel".
