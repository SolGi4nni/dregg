# dregg — status (code-verified)

This file is **ground truth, derived from code and from commands that actually run** —
not from design narrative. The many `*.md` design/audit documents now under
[`docs-old/`](docs-old/) are mid-development aspirational notes of *unknown current
validity*; do not treat them as authoritative. When this file and a design doc
disagree, the code wins, then this file, then nothing else.

_Last verified against the tree on 2026-05-28. The test population, the MCP tool
count, and the local on-ramp (`init` → `run` → `dregg demo`) were re-measured
against a running node on 2026-07-26; everything else below still carries the May
date and has not been re-checked._

## What builds, right now

- `cargo check -p dregg-types -p dregg-cell -p dregg-turn -p dregg-circuit -p dregg-verifier --tests`
  → **compiles clean** (warnings only; no errors).
- Test population (counts of `#[test]`/`#[tokio::test]` attributes, not
  pass-rate): **4,418 across the core crates** — circuit 1187, turn 903, cell 832,
  node 572, sdk 518, storage 307, verifier 57, types 42. Reproduce with:

  ```sh
  for c in circuit cell turn storage sdk node verifier types; do
    grep -rEc "^[[:space:]]*#\[(tokio::)?test" $c/src $c/tests 2>/dev/null | awk -F: '{s+=$2} END {print s+0}'
  done
  ```

  (Was "roughly 2,500" here since 2026-05-28, with a per-crate breakdown that was
  low by 2–7× in every entry.)

## Run something in ~30 seconds

Two small, **executable** examples exist precisely so the on-ramp can't rot — they
are compiled code, not prose:

### The smallest receipt chain (GitHub issue #3)

```sh
cargo run -p dregg-sdk --example hello_receipt_chain
```

Creates an agent, submits one turn with a single `Effect::SetField`, and prints the
resulting `TurnReceipt` as JSON plus the one-entry receipt chain. The printed JSON is
the canonical receipt shape to pin a dregg-compatible shim against. Source:
[`sdk/examples/hello_receipt_chain.rs`](sdk/examples/hello_receipt_chain.rs).

Honest caveats this example makes visible: on a local, federation-less ledger the
receipt's `federation_id` is all-zero and `executor_signature` is `null` (no executor
attestation in a single-process run).

### The predicate language (GitHub issue #1)

```sh
cargo run -p dregg-cell --example predicate_language
```

Constructs real `CellProgram::Predicate(vec![StateConstraint::…])` programs and runs
them through `CellProgram::evaluate(new, old, ctx)` — the same call the executor makes
before committing — against accepting and rejecting transitions. Includes the
"drop messages whose audience field isn't self" case via `FieldEquals` and `AnyOf`.
Source: [`cell/examples/predicate_language.rs`](cell/examples/predicate_language.rs).

Canonical code locations: `StateConstraint`, `CellProgram`, and `CellProgram::evaluate`
all live in `cell/src/program.rs`; `CellState` (8 state slots) in `cell/src/state.rs`.

### Other real binaries

`dregg-node` (`cargo run -p dregg-node -- run`, plus `init`/`status`/`mcp`/`genesis`/
`register-federation`/`relay`/`join`/`add-validator`/`gen-validator-key`/
`propose-epoch-transition`/`approve-membership`), the `dregg` CLI, `dregg-demo-agent`,
and `dregg-verifier`. The node MCP server (`dregg-node mcp`) registers **54 tools**
(e.g. `dregg_create_agent`, `dregg_submit_turn`, `dregg_get_receipt_chain`) — see
`node/src/mcp/` (a directory since the module was split; this file said
`node/src/mcp.rs`). `tools/list` pages at 20, so count it from the server's own
`_meta.dregg.visible_tool_count` rather than the length of the first page:

```sh
printf '%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"probe","version":"0"}}}' \
  '{"jsonrpc":"2.0","method":"notifications/initialized"}' \
  '{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}' \
  | ./target/debug/dregg-node mcp --data-dir /tmp/mcp-probe 2>/dev/null
```

### The local on-ramp (`init` → `run` → `dregg demo`)

Verified end to end on 2026-07-26 from empty directories: `dregg-node init` mints
a one-validator chain and the committee's key, `dregg-node run` starts it
(`healthy:true`, `consensus_live:true`, `state_producer:"lean"`), and `dregg demo
--passphrase <p>` drives the nameservice lifecycle on both a fresh node and a
second consecutive run. `producer_root_agreeing_effects` (and its deprecated
alias `producer_covered_effects`) reads **18**.

Note for a box already running a node: pass `--gossip-port`. It defaults to 9420,
so a second node cannot bind it. That node used to keep serving HTTP with
`consensus_live:false` and apply nothing; as of 2026-07-26
`blocklace_sync::refuse_to_start_without_consensus` makes it refuse to start
instead, naming the port and the bind error.

## Proof / verification mode (GitHub issue #2 — honest answer)

There is **no `DREGG_PROOF_MODE` env var or config knob today.** What exists in code:

- A `VerificationMode` enum in the SDK (`sdk/src/cipherclerk.rs`: `Trusted`,
  `SelectiveDisclosure { reveal }`, `FullyPrivate`) and a parallel one in `intent`
  (`Trusted`/`Selective`/`Private`). The SDK authorization path dispatches all three.
- The node's MCP path currently uses `VerificationMode::Trusted` (cleartext + trace,
  no STARK). So the README's "Trusted by default" is *behaviorally* true for the node,
  but it is hardcoded, not operator-selectable.

Wiring an explicit, uniformly-honored mode selector is tracked, not done.

## Known gaps (pointers, not promises)

Soundness/correctness debt is tracked in the task list and in `docs-old/SILVER-DEBT.md`
(archived; verify any specific claim against code before relying on it). Active items
include cross-federation attested-root threshold handling, intent-fulfillment
body-membership binding, and queue FIFO completeness.

## On the archived docs

The `docs-old/` and `docs/` trees contain design rationale, audits, and aspirational
plans accumulated across many development sessions and several different authors/models.
They are kept for history (timestamps preserved) and can be genuinely useful as *design
intent*, but they routinely describe things as finished that are partial, and miss
features that already shipped. Trust the code.
