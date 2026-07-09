# grain-turn

**The R2 kernel-turn weld — the ONE real `GrainTurnMinter`: every admitted agent action
becomes a genuine committed executor turn, so a receipt becomes a VIEW over a kernel
transition and the meter becomes a host-side executor caveat.**

`dregg_agent`'s agent loop is, by default, a parallel universe: a local meter, a `BTreeMap`
heap, a BLAKE3 root, an ed25519 receipt chain — **no executor, no `dregg_cell::Cell`, no kernel
turn**. The `GrainTurnMinter` seam is the bridge; this crate is its one real implementation.
`ToolGatewayMinter` (`src/lib.rs`) turns each admitted action into a real
`dregg_sdk::ToolGateway::invoke` on a cap-gated grain turn-cell and hands back the turn's
`turn_hash`, which the run loop seals into the receipt as its `turn_receipt_hash`.

## The core API (`src/lib.rs`)

| item | what it is |
|---|---|
| `ToolGatewayMinter::open(domain, budget)` | mint a fresh runtime + admit a cap-gated worker under a rate-`budget` `ToolGrant`, installing the `mandate_program` backstop (`FieldLte{calls_made ≤ rate_limit} ∧ Monotonic{calls_made}`) |
| `mint_turn` (impl `GrainTurnMinter`) | run the metered turn: witness `consumed`, `heap_root`, and `action_commit(label,cost)` as committed cell state; `Err` = the executor refused host-side (over-rate / insolvent) |
| `bind_attestation` / `bound_attestation` | witness a zkOracle attestation commitment at `ATTESTATION_SLOT` on subsequent turns (THE FUSION — "driven by a jailed, attested brain") |
| `action_commit(label, cost)` | the canonical length-prefixed BLAKE3 the turn commits at `ACTION_SLOT` — a verifier recomputes it from `(action, cost)` |
| `read_slot` / `calls_made` / `committed_turns` | ground-truth reads off the COMMITTED grain turn-cell + the committed-turn manifest |

The grain turn-cell slots: `calls_made` (=4, the metered counter), `CONSUMED_SLOT` (=5),
`HEAP_ROOT_SLOT` (=6), `ACTION_SLOT` (=7), `ATTESTATION_SLOT` (=8), plus the cell nonce (the
anti-replay link).

## How it fits the economy

`agent-platform::drive_serving` constructs a `ToolGatewayMinter` with its rate ceiling set to
the grain's budget and routes the drive through it, so every hosted action is a genuine
committed turn; `agent-platform::node::NodeMinter` mints the byte-identical witnessed turn onto
a real node ledger. The committed-turn manifest is what `grain_verify::verify_r2` checks each
receipt's link against.

## Honest limits (R2, not R3)

R2 makes the executor's own `calls_made` caveat enforce the meter **host-side** — a session
loop that skipped its local meter still cannot drive the on-ledger counter past the ceiling.
But it **still trusts the executor host** that committed the turn. Removing that — proving the
turn genuinely RAN — is R3's whole-history STARK leg (`grain_verify::WHOLE_HISTORY_GAP`): the
remaining breadstuffs ask is to mint each grain turn's rotated wide-anchored EffectVM leg here,
which this crate does not yet do. For flat cost-1 actions `calls_made ≤ budget` is the exact
call-count meter; for variable-cost `Spend` actions it is a conservative call-count backstop
under the session meter's value bound.

## Tests

```sh
cargo test -p grain-turn
```

Note: `grain-turn` is a workspace `member` but not in `default-members` (it pulls the
kernel-facing `dregg_sdk` half kept out of the std-only `dregg-agent` crate).
