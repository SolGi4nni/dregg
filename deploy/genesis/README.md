# Devnet Genesis Configuration

This directory contains the genesis state for the dregg devnet federation. It defines the initial accounts, deployed applications, route table, and validator set that every connecting node bootstraps from.

## Files

| File | Purpose |
|------|---------|
| `genesis.json` | Complete genesis state (accounts, cells, constitution, routes) |
| `accounts.json` | Pre-funded account manifest with roles and balances |
| `apps.json` | Deployed applications and their cell programs |
| `routes.json` | DFA route table (namespace access control) |
| `generate.sh` | Wrapper around `cargo run --release -p dregg-node -- genesis` |

## Generating Fresh Genesis State

```bash
cd deploy/genesis
./generate.sh          # first time
./generate.sh --force  # regenerate (wipes existing keys)
```

The script will:
1. Run `cargo run --release -p dregg-node -- genesis --validators 4`
2. Generate per-validator keys (`node-{0..3}.key`) — each seed derives BOTH an
   ed25519 AND an ML-DSA-65 (FIPS 204) key, so the committee can furnish the
   HYBRID (ed25519 ∧ ML-DSA-65) finalization quorum the beacon's PQ half needs
3. Write validator env files (`node-{0..3}.env`)
4. Publish the PUBLIC `genesis.json` (committee public keys + enrolled ML-DSA
   roster + threshold) into this tracked directory
5. Refuse to overwrite unless `--force` is passed

Private keys land in `GENESIS_KEYS_DIR` (default `./secrets`, gitignored; point
it at an out-of-tree path such as `~/dregg-secrets` to keep keys entirely
outside the repo). Only the public `genesis.json` is written into the tracked
tree — never a private key. Committee size / host are env-driven:
`FED_VALIDATORS` (default 4), `DREGG_DEPLOY_HOST` (default `demo.dregg.net`).

### Prerequisites

- Rust toolchain (to build `dregg-node`)

### Generation Command

```bash
./deploy/genesis/generate.sh --force
```

## What's In genesis.json

### Accounts (10 pre-funded)

| Account | Balance | Role |
|---------|---------|------|
| alice | 10,000,000 | Power user (CDP, LP positions) |
| bob | 5,000,000 | Trader (open orderbook orders) |
| carol | 1,000,000 | Credential holder (3 VCs) |
| dave | 500,000 | New user (minimal state) |
| eve | 2,000,000 | Creator (NFT auctions) |
| faucet | 100,000,000 | Infrastructure (dispenses computrons) |
| treasury | 50,000,000 | Governance (DAO treasury, app owner) |
| relay | 10,000,000 | Infrastructure (store-and-forward) |
| nameservice | 5,000,000 | Infrastructure (name registry) |
| bridge-operator | 10,000,000 | Infrastructure (cross-chain bridge) |

### Constitution

- 4 validators (node-0 .. node-3) — n>=4 gives one-fault slack (n=3 is
  unanimity-fragile: finality needs all three)
- Threshold: 3 (BFT quorum, 2f+1 for f=1)
- Each validator enrolls an ed25519 key AND an ML-DSA-65 key; `federation_id`
  and each `hybrid_id` commit to BOTH halves (the enrolled PQ roster)
- Epoch length: 100 waves
- Checkpoint interval: 10 waves

### Consensus time flag day

- `consensus_genesis_unix_seconds` is the one shared CTM1 anchor. Every validator
  loads it from this public committee descriptor; a local boot clock is never a
  replay or validation input.
- `consensus_time_mode` is currently `devnet-causal-v1`. This means signed,
  causally bounded deterministic replay time—not a fair federation wall clock.
  A producer can select the allowed `predecessor_frontier + 300s` maximum; a
  future federation policy must replace that choice with an agreed
  round/beacon/median schedule before CTM1 governs real-time expiries.
- This is a flag day. A store containing legacy timestamp-less turn blocks is
  refused on restart; explicitly migrate it or re-genesis instead of silently
  interpreting old history under the new rule.

### Deployed Apps (as cells)

1. **Stablecoin** -- CDP manager + price oracle (2 cells)
2. **AMM** -- ETH/USDC and BTC/USDC constant-product pools (2 cells)
3. **Orderbook** -- Central limit order book (1 cell)
4. **Gallery** -- NFT auction house (1 cell)
5. **Nameservice** -- Human-readable name registry (1 cell)
6. **Governed Namespace** -- Root DFA delegation (1 cell)
7. **Identity Registry** -- Verifiable credential store (1 cell)

### Pre-configured State

- Alice: open CDP (1000 ETH collateral, 500 stablecoin debt)
- Alice: LP shares in ETH/USDC and BTC/USDC pools
- Bob: open limit orders (buy 10 @ 95, sell 5 @ 105)
- Carol: 3 issued credentials (age, country, org-membership)
- Eve: 2 NFTs listed for auction
- AMM pools: seeded with initial liquidity

### Route Table

```
/public/*   -> anonymous     (read)
/services/* -> members       (read, write)
/admin/*    -> admin         (read, write, configure)
/bridges/*  -> bridge-operator (read, write, relay)
/names/*    -> nameservice   (read, write, register)
/faucet/*   -> anonymous     (write, rate-limited)
/oracle/*   -> relay         (write)
```

## Deploying to Devnet

After generating:

The deploy host is env-driven (`DREGG_DEPLOY_HOST`, default `demo.dregg.net` —
the demo/testnet domain; the old `*.fg-goose.online` devnet is retired):

```bash
# Copy the PUBLIC genesis manifest to the running node
scp genesis.json "${DREGG_DEPLOY_HOST:-demo.dregg.net}":/opt/dregg-data/

# Restart the node to load new genesis
ssh "${DREGG_DEPLOY_HOST:-demo.dregg.net}" sudo systemctl restart dregg-gateway
```

Or use the automated deploy:

```bash
./deploy/aws/update.sh
```

## Security Notes

- Private keys (`node-*.key`, `*-well.key`, `agent-*.key`) go to
  `GENESIS_KEYS_DIR` (out-of-tree / gitignored) and must never be committed;
  `deploy/genesis/*.key` and `deploy/genesis/secrets/` are gitignored as a
  backstop
- The checked-in `genesis.json` is the PUBLIC committee manifest (public keys +
  ML-DSA roster + threshold) only — it carries no private material
- These keys are for **testnet only** -- never reuse for production
