# hello-receipt-chain — the smallest dregg demo

One agent. One turn. One receipt chain.

Where `demo/two-ai-handoff/` shows the full multi-party capability handoff (many
moving parts), this is the minimal shape: a single agent submits one turn and
reads back its own auditable receipt chain. It drives the **real** MCP surface a
live AI process uses — `dregg-node mcp` over newline-delimited JSON-RPC on stdio
— using exactly three tools:

| step | tool                       | what it does                                        |
|------|----------------------------|-----------------------------------------------------|
| 1    | `dregg_create_agent`       | register this node's cipherclerk as a ledger cell (content-addressed `cell_id`) |
| 2    | `dregg_submit_turn`        | submit ONE turn (a `set_field` effect on our own cell) |
| 3    | `dregg_get_receipt_chain`  | read the auditable receipt chain                    |

## Run

```bash
cd demo/hello-receipt-chain
./run.sh
```

`run.sh` builds `dregg-node` if it is not already at
`target/debug/dregg-node`, wipes `./state/` so the node auto-generates a fresh
cipherclerk identity, and runs `hello.py` against it. Or drive it directly:

```bash
python3 hello.py --node-bin ../../target/debug/dregg-node --data-dir ./state
```

## What you see

The last line on stdout is the receipt chain — the smallest agent-to-agent
receipt shape dregg emits:

```json
{
  "chain_length": 1,
  "receipts": [
    {
      "receipt_hash": "8dd68b64…",
      "turn_hash":    "717e781c…",   ← matches the turn we submitted
      "pre_state":    "7463b3b7…",
      "post_state":   "011c2f7c…",   ← differs from pre_state: the turn moved state
      "computrons_used": 100,
      "action_count": 1,
      "has_witness": false,
      "witness_count": 0
    }
  ]
}
```

Each receipt binds `pre_state → post_state` under a `turn_hash`, and links to the
previous receipt by hash — that chain is the audit trail.

## Notes on fidelity

- **`fee` funds the turn's budget.** A bare action costs ~100 computrons; the
  turn passes `fee: 1000`. With `fee: 0` the node correctly rejects the turn
  (`computron budget exceeded: limit=0, used=100`).
- **The `effects` array is passed per the documented `dregg_submit_turn`
  schema.** Note that the current node build's `dregg_submit_turn` handler
  (`node/src/mcp/handlers_act.rs::tool_submit_turn`) submits the turn's action
  with empty effects — the `effects` argument is accepted but not yet wired into
  the action, so the committed receipt is a state-advancing *chaining* receipt
  rather than a proven slot write. The script is written against the tool's
  published signature so it stays correct when that handler wires effects
  through; it deliberately does not claim a field mutation the node did not make.

This demo was run end-to-end against `target/debug/dregg-node`; the JSON above is
real output.
