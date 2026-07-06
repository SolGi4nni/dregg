# Rent a confined, verifiable agent

A grain is a hosted agent: a mind funded by its own lease, driven turn by turn,
every action cap-gated, metered, and receipted. This guide shows the confined
form — a grain whose *body* is OS-jailed, so even an untrusted body (a coding
agent, a bring-your-own binary) can only do what its caps allow, and the renter
can verify exactly what it did against the chain.

## Run the demo

```sh
cargo run -p grain-jail --example rent_a_confined_agent
# OS-jail the body (macOS Seatbelt / Linux seccomp+Landlock):
cargo run -p grain-jail --example rent_a_confined_agent --features real-jail
```

It rents a grain, drives it with a body that proposes two cell-writes, and
prints what the renter can check:

```
rented a confined grain at `demo.agents.dregg`
  caps: cell:notes/1, cell:notes/2  (a raw `shell` would be refused — hosted session)
  the grain admitted 2 action(s) — each cap-gated, metered, and minted as a committed kernel turn
  the lease meter drew down 2 budget unit(s)
  R2: the renter verified 2/2 turns are views over committed kernel turns
  anti-forgery: a manifest naming turns never committed is refused
```

## How it fits together

A body never touches the grain directly. It proposes tool-calls over a small
newline-JSON line protocol; a `ConfinedBrain` translates each proposal into the
grain's action vocabulary at the `AgentBrain` seam; the grain's drive loop
cap-gates, meters, and mints each admitted action as a committed kernel turn, and
feeds the verdict back to the body.

```text
  body (jailed)     ConfinedBrain (the AgentBrain)     grain drive loop
    propose ────────▶ next_action ─▶ AgentAction ─▶ cap-gate · meter · mint (R2 turn)
    ◀──────── observe ◀───────────────────────────── verdict
```

Because a `ConfinedBrain` *is* an `AgentBrain`, the grain is driven exactly as it
is by any other brain — the lease, the prepaid meter, the checkpoint/fork/rewind
of the mind-cell, and the R0→R2 attestation ladder all apply unchanged. The
OS-jail is a swap of the channel's backing transport (an in-process pipe → a
firmament endpoint socket); the seam does not change.

## Drive your own confined body

```rust
use agent_platform::AgentPlatform;
use grain_jail::{ConfinedBrain, LineChannel};

let platform = AgentPlatform::new();
let host = platform.rent(
    "my.agents.dregg", "dga1_me",
    "cell:notes/1",          // the caps — a raw `shell` is refused in a hosted session
    10_000,                  // the budget (the ceiling the body cannot exceed)
    workdir, terms, None,
)?;

// A body that speaks the line protocol over any BufRead + Write pair.
let mut brain = ConfinedBrain::new(my_channel);
let report = platform.drive_serving(&host, "do the work", &mut brain)?;

// The renter verifies every turn is a committed kernel turn.
let r2 = platform.verify_r2(&host)?;
assert_eq!(r2.linked as u64, report.admitted);
```

To OS-jail the body, build the channel with `grain_jail::jail::spawn_confined_body`
(the `real-jail` feature): it forks the body into a firmament process-PD confined
to its socket alone — file, network, and `exec` denied — and hands back the same
kind of channel. See `grain-jail/examples/rent_a_confined_agent.rs`.

## The protocol

Body → host:

```json
{"propose": {"tool": "cell-write", "path": "notes/1", "value": "hi"}}
{"propose": {"tool": "invoke:search"}}
{"propose": {"tool": "stripe_pay", "amount_cents": 250}}
{"done": {}}
```

Host → body (one per proposal):

```json
{"admitted": true, "tool_ok": true, "summary": "..."}
{"admitted": false, "refusal": "no cap: cell-write:forbidden"}
```

`tool` maps to the grain's caps: a bare or `invoke:`-prefixed name is a call
(`invoke:<service>`), a proposal with `amount_cents` is a priced spend (the budget
is the dollar ceiling), and `cell-write` / `cell-read` touch the grain's own
cells. A malformed proposal is refused in-band and costs nothing.

## What the renter is trusting

- **Not the host.** Every admitted action is a committed kernel turn; `verify_r2`
  confirms each receipt is a view over one, and a forged manifest is refused.
- **Not the body.** Its authority is exactly the grain's caps; an ungranted
  action is refused by the braid, and its spend cannot exceed the lease budget.
- **With `--features real-jail`, not the body's syscalls either.** The body runs
  in an OS-jail that denies file, network, and `exec` — so a body that ignores
  the cap system and reaches for raw syscalls is stopped by the kernel.

The whole-session STARK fold (R3) is the remaining verifiability frontier; R2 is
the ceiling today. Running an arbitrary external agent binary as the body needs a
granted exec-door; the confined in-jail harness reaching a model over one granted
egress door is the shape for a language-model-driven agent.
