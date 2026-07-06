# The confined-body grain: an OS-jailed agent behind the grain seam

A grain is a hosted agent whose mind is a committed, forkable cell funded by its
own lease (`grain-fork`, `agent-platform`). Its mind is driven by an
[`AgentBrain`](../../dregg-agent/src/agent.rs) — the seam that yields the next
`AgentAction`, observes the braid's verdict, and repeats. Today every brain runs
*in-process*: `PlannedBrain` (scripted), the BYO-key LLM brain, the model-over-
portal brain. The cap system gates the tools an action calls *through* the
toolkit, and the lease meters + receipts every admitted turn.

In-process is right for a brain that only ever proposes actions through the seam.
It is **not** enough for an untrusted *body* — a coding-agent subprocess, a BYO
agent binary — which can ignore the cap system entirely and make raw syscalls
(read the operator's keys, open a socket, exec a shell). For that case the grain
needs **ambient OS confinement**: the body runs in a jail that denies everything
but one channel, and its every tool-call arrives back through the grain's
cap-gated seam.

## What is

**`ConfinedBrain`** (crate `grain-jail`) is an `AgentBrain` whose decisions come
from a jailed subprocess instead of in-process code. It bridges two shapes that
already bottom out at the same place:

- The jailed body proposes tool-calls over a minimal line protocol.
- `ConfinedBrain::next_action` reads the next proposal and translates it into an
  `AgentAction` for the grain's drive loop.
- The drive loop cap-gates + meters + receipts the action (unchanged), then hands
  the verdict to `ConfinedBrain::observe`.
- `observe` serializes that `ActionObservation` back to the jailed body, which
  reacts and proposes its next call.

```text
  jailed body (subprocess, OS-sandboxed)        grain drive loop (unchanged)
    │  propose {tool, args}      ─────────▶  next_action ─▶ AgentAction
    │                                          cap-gate · meter · receipt (R2 turn)
    │  ◀───────── observe {admitted, refusal, summary}  ◀── ActionObservation
    └─ react, propose next
```

Because `ConfinedBrain` *is* an `AgentBrain`, the grain's lease, vat lifecycle,
prepaid meter, checkpoint/fork/rewind of the mind-cell, and the R0→R2 attestation
ladder all apply to a confined body **with no change to the drive path**. The
body is jailed; its authority is exactly the grain's caps; its whole session is a
re-witnessable chain of committed turns.

## The jail

The confinement is the firmament process-PD substrate
(`dregg-firmament`, features `process-pd` / `process-pd-sandbox`), the same
primitive the confined-agent bridge uses: `fork()` → close every fd but one
endpoint → self-apply the host OS sandbox (Linux seccomp + landlock; macOS
Seatbelt) before the body runs. `process-pd` is `libc`-only and cheap;
`process-pd-sandbox` adds the default-deny confinement. The body's sole channel
is the one endpoint fd, over which the line protocol runs. The confinement teeth
(`IPC_WORKS · OPEN_DENIED · NET_DENIED · ONLY_ENDPOINT_FD`) are the same ones the
firmament probe asserts.

`grain-jail` depends only on `dregg-agent` (the brain seam) and `dregg-firmament`
(the jail) — never the heavy verified-executor sdk — so it links into the main
workspace cleanly. The `agent-host` bwrap `JailSpec` is a second, Linux-only jail
backend behind the same body-spawn trait.

## The line protocol

A minimal newline-delimited JSON protocol over the endpoint — deliberately
smaller than ACP, and mappable onto it later:

- body → host: `{"propose": {"tool": "<service>", "amount_cents"?: N, ...}}` or
  `{"done": {...}}`.
- host → body: `{"verdict": {"admitted": bool, "refusal"?: "...",
  "tool_ok"?: bool, "summary"?: "..."}}`.

`tool` maps to the grain's cap vocabulary (`invoke:<service>`, the `Spend` rail
for priced calls, `cell-read`/`cell-write`, …); an unmappable proposal is refused
in-band, exactly as an over-budget action is.

## Staging

1. **The seam + protocol** — `ConfinedBrain` + the line protocol, validated
   against a stand-in body over an in-process pipe (proposal→verdict translation
   correct, refusals surfaced, done terminates). No jail yet.
2. **The real jail** — spawn the body under firmament `process-pd[-sandbox]`,
   the endpoint fd carrying the protocol; the confinement teeth asserted.
3. **A real grain, end-to-end** — `agent-platform` rents a grain, drives it with
   a `ConfinedBrain` over a jailed body, meters + receipts each turn, and the
   renter verifies (R2) the whole session — the jailed body's authority never
   exceeds the grain's caps, its spend never exceeds the lease budget.

## Boundaries (what this is not)

- Not a change to the kernel, effect vocabulary, commitment, or the
  grain-turn / grain-verify soundness surface — it is a new brain over the
  existing seam.
- Cross-platform sandbox coverage follows firmament: the Linux
  seccomp+landlock path is validated on a Linux builder; macOS Seatbelt locally.
  The plain `process-pd` (fork + fd-close, no OS sandbox) runs anywhere Unix and
  is the fallback body-spawn.
- R2 is the verifiability ceiling; the whole-history STARK fold (R3) stays the
  named grain gap.
