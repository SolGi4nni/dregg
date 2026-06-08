# dregg-discord-bot

Discord bot for the dregg devnet — custodial cipherclerks, transfers,
explorer, presence attestation, CapTP, governance, queues, names,
federation.

This crate was promoted out of `apps/` and now lives at the workspace
toplevel (`/discord-bot`), as a peer of `node/`, `sdk/`, `app-framework/`
etc. — it is not an app, it is a *consumer of* the canonical dregg
SDK surface.

## Cipherclerk handle

Per-user cipherclerks are backed by the canonical
[`dregg_app_framework::AppCipherclerk`](../app-framework/src/cipherclerk.rs) over
[`dregg_sdk::AgentCipherclerk`](../sdk/src/cipherclerk.rs). Each Discord user is
mapped to a deterministic Ed25519 identity:

```
seed = BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret || discord_user_id)
agent = AgentCipherclerk::from_key_bytes(seed)
cclerk = AppCipherclerk::new(agent, federation_id)
```

The old in-crate `DerivedWallet` (BLAKE3-only "public key", bespoke
cell-id domain) is gone. `/send` and `/tip` submit a canonical
Ed25519-signed `SignedTurn` to `POST /api/turns/submit-signed` (postcard
body) — verified end-to-end against a live node (see
`examples/devnet_transfer_smoke.rs`). The `UserCipherclerk::legacy_secret`
/ `sign_legacy` BLAKE3-MAC path remains only for pre-canonical deployments.

**Federation-id signing domain.** Action signatures are bound to the bot's
configured `FEDERATION_ID`, and the node verifies each action against the
target cell's public key under the executor's federation id. On a **solo**
devnet that id is `blake3(node_operator_pubkey)`; on a **full** federated
devnet it is the configured federation id. The operator MUST set the bot's
`FEDERATION_ID` to match the node's, or every transfer is rejected with
"Ed25519 signature verification failed". A faucet-materialized cell also
needs its real public key (`/api/faucet` with `public_key`), which
`/cipherclerk create` already supplies.

## Slash commands

### Active

- **Cipherclerk**: `/cipherclerk create | balance | address | export`
- **Transfer**: `/send <@user> <amount>`, `/tip <@user> <amount>`
- **Gallery** (apps/gallery): `/gallery list | auctions | bid | mybids`
- **Identity** (apps/identity): `/credential issue | verify | list`
- **Presence**: `/presence status | attest | verify | history` — signed
  proof-of-online attestations usable as dischargeable caveats
- **Status**: `/status`, `/proof verify`, `/metrics`
- **Social**: `/faucet`, `/leaderboard`, `/history`
- **Starbridge dashboard**: `/dregg` opens app cards, buttons, an app picker,
  and modal forms for the checked-in Starbridge identity, nameservice,
  governed-namespace, and subscription flows.
- **Explorer**: `/explorer feed | cell | turn | block | note | proof |
  factory | search | stats | recent | watch | unwatch`
- **CapTP** (bot as capability peer): `/cap-share`, `/cap-accept`,
  `/cap-delegate`, `/cap-list`, `/cap-revoke`
- **Queue** (programmable queues mounted under
  `/discord/<guild>/<name>`): `/queue-create | publish | subscribe |
  status | mount`
- **Governance** (apps/governed-namespace): `/gov-propose | vote |
  status | routes`
- **Names** (apps/nameservice): `/name-register | resolve | whois`
- **Bounty board** (starbridge-apps/bounty-board): `/bounty post | claim |
  submit | payout | status` — drives the bounty lifecycle on a factory-born
  bounty cell. Each write is a canonical Ed25519-signed app `Action`
  (`build_post_action`/`build_claim_action`/`build_submit_action`/
  `build_payout_action`) submitted through the signed-turn path. The
  OPEN→CLAIMED→SUBMITTED→PAID state machine is enforced **on-chain** by the
  cell's program (strictly monotone `STATE`), so double-claim / double-payout
  are rejected by the executor. The bounty cell is supplied by the caller
  (born via the Starbridge seed or `/dregg`). `status` reports the cell's real
  on-chain balance/nonce/provenance; per-slot lifecycle state is not exposed
  by the public read API, so it is not fabricated.
- **Federation**: `/setup-federation`, `/link-cipherclerk`, `/unlink-cipherclerk`

External `/link-cipherclerk` records are pending until ownership is proven.
Hosted `/cipherclerk create` identities remain the only identities the bot can
sign transfers and CapTP management commands for.

### Retired (apps deleted from workspace)

The following commands were removed in the post-relocation cleanup
because their target apps (`amm`, `lending`, `orderbook`, `stablecoin`,
`dao-treasury`, `prediction-market`) are no longer workspace members:

- `/swap`, `/pool`, `/lend supply | borrow | status` — AMM/lending
- `/order buy | sell | cancel`, `/book`, `/trades` — orderbook

Per the project's "improve don't degrade" stance these slash names
were deleted outright rather than left as "not yet ported" placeholder
stubs. If/when these apps return as `starbridge-apps/<name>`, the
commands can be reintroduced against the new endpoints.

## Configuration

Environment variables (see `src/config.rs`):

| Var              | Required | Description                                  |
| ---------------- | -------- | -------------------------------------------- |
| `DISCORD_TOKEN`  | yes      | Discord bot token                            |
| `DISCORD_APP_ID` | yes      | Discord application id (u64)                 |
| `BOT_SECRET`     | yes      | 64 hex chars (32 bytes) — master key seed    |
| `DEVNET_URL`     | no       | node base URL; defaults to `https://devnet.dregg.fg-goose.online` |
| `DATABASE_URL`   | no       | defaults to `sqlite:bot.db`                  |
| `DEVNET_API_TOKEN` | no     | operator bearer token; sent on every node call. Needed when the node gates writes behind `require_auth`. |
| `FEDERATION_ID`  | no       | 64 hex chars; the executor signing domain. On a **solo** node this MUST be `blake3(node_pubkey)` or transfers fail (see preflight below). |

### Startup preflight

On boot the bot probes the node's `/status` and logs an operator-facing
summary, catching the two failure modes that otherwise surface as cryptic
per-command errors:

- **node unreachable** — the bot still boots and retries per command, but logs
  a clear warning with the reason (timeout / connection refused / HTTP code)
  and the configured `DEVNET_URL`.
- **`FEDERATION_ID` mismatch** — on a solo node the executor signs under
  `blake3(node_pubkey)`. The preflight computes the expected value from the
  node's reported `public_key` and **warns loudly** if the bot's
  `FEDERATION_ID` differs, printing the exact value to set. (A mismatch makes
  every transfer fail with "Ed25519 signature verification failed".)

### Error UX

Live-node failures are classified into actionable messages instead of raw
node bodies (`devnet::DevnetError::user_message`): HTTP 401/403 → "not
authorized, set `DEVNET_API_TOKEN`"; 404 on a balance → "no on-chain balance
yet, try `/faucet`"; 429 → "rate limited, wait and retry"; 5xx → "node-side
fault"; timeouts/connect-refused → "node busy / offline". The raw status +
body is still preserved in logs via `Display`.

## Build

```bash
cargo build -p dregg-discord-bot
```
