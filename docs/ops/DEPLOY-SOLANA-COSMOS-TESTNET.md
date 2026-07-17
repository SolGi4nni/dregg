# DEPLOY-SOLANA-COSMOS-TESTNET — the verifier's one-broadcast runbook

Ready-to-fire deployment of dregg's on-chain Groth16 settlement verifier to **two
public testnets**: **Solana devnet** (`solana-settlement/` — the native SBF
program) and a **CosmWasm testnet** (`cosmos-settlement/` — the Rust→wasm
contract). Both verify the SAME real dregg BN254 Groth16 proof over the SAME
25-lane whole-history statement the EVM `DreggSettlement` settles
(`chain/test/fixtures/settlement_groth16.json` — the 2-turn apex proof that
settled on Base-Sepolia).

**Honest scope up front.** This is throwaway-key, no-real-value testnet
deployment against public devnets. The trusted setup is the **single-party dev
ceremony** (`keccak256("dregg-settlement-vk-dev-setup")`, byte-identical across
EVM/Solana/Cosmos), **not** a production MPC ceremony. Nothing here touches
mainnet or real custody. **The live broadcast is ember-gated** — this document
prepares and verifies; ember pulls the trigger. Every command that spends a
testnet key or writes to a chain is marked `BROADCAST →` and is **not run** by
the prep that produced this doc.

State verified while writing this runbook (2026-07-13, on this mac, arm64):

| Artifact | Verified | Detail |
|---|---|---|
| `solana-settlement` `.so` | ✅ deployable | 95,224 B SBF/eBPF ELF, stripped (`target/deploy/dregg_solana_settlement.so`) |
| `solana-lock` `.so` | ✅ deployable | 164,904 B SBF/eBPF ELF (`target/deploy/dregg_solana_lock.so`) |
| Solana toolchain | ✅ present | `solana-cli 4.0.2`, `cargo-build-sbf` present |
| Cosmos optimized `.wasm` | ✅ built | `cosmwasm/optimizer-arm64:0.17.0` + 2 lockfile pins (see §2.2); **380,916 B**, `cosmwasm-check 2.2.2` **pass** |
| Docker | ✅ present | `29.5.3` |
| Chain CLI (`osmosisd`/`neutrond`) | ❌ **not installed** | blocker B3 — install step given |
| `anchor` | ❌ not installed | **not needed** (native program, `cargo build-sbf`) |

---

## 1. SOLANA DEVNET

The `solana-settlement` program is a **native** (no-Anchor) SBF program. Its
`settle` reproduces `DreggGroth16Verifier25.verifyProof` on the `alt_bn128`
syscalls: a 2-pair Pedersen-commitment pairing + a 26-base public-input MSM + a
4-pair Groth16 pairing, fail-closed. `anchor` is **not** required.

### 1.1 Toolchain check

```bash
which solana cargo-build-sbf          # both must resolve
solana --version                      # solana-cli 4.0.2 (verified)
```

Both are present at `~/.local/share/solana/install/active_release/bin/`.

### 1.2 Build the deployable `.so` (already built; rebuild recipe)

```bash
cd /Users/ember/dev/breadstuffs/solana-settlement
cargo build-sbf                       # → target/deploy/dregg_solana_settlement.so
cd /Users/ember/dev/breadstuffs/solana-lock
cargo build-sbf                       # → target/deploy/dregg_solana_lock.so
```

Verified deployable artifacts (do NOT route SBF through pbuild — `cargo-build-sbf`
is the local Solana platform-tools toolchain, not a persvati cargo lane):

- `solana-settlement/target/deploy/dregg_solana_settlement.so` — **95,224 bytes**,
  `ELF 64-bit LSB shared object, eBPF (arch 0x107), stripped`.
- `solana-lock/target/deploy/dregg_solana_lock.so` — **164,904 bytes**, same class.

`cargo build-sbf` also generated the program keypairs (the program IDs are pinned
by these keypairs — keep them to redeploy to the same ID):

- settlement program id: **`BMH1hAqzm9tV2qB713GN9NsbXdT4AQawKGuAUdaD2Gjs`**
  (`target/deploy/dregg_solana_settlement-keypair.json`)
- lock program id: **`BJGYsj4KyjRkUfDoAusbN9W2bLbVkyMyy8b8retMmSGs`**
  (`target/deploy/dregg_solana_lock-keypair.json`)

### 1.3 Pinned targets

| Field | Value |
|---|---|
| Cluster | **devnet** |
| Public RPC | `https://api.devnet.solana.com` |
| Helius devnet RPC (optional, higher rate limit) | `https://devnet.helius-rpc.com/?api-key=<HELIUS_KEY>` |
| Web faucet (if `solana airdrop` is throttled) | `https://faucet.solana.com` (select **devnet**) |
| Explorer | `https://explorer.solana.com/address/<ID>?cluster=devnet` |

### 1.4 Fund a throwaway devnet key (free)

```bash
mkdir -p ~/dregg-devnet
solana-keygen new --no-bip39-passphrase -o ~/dregg-devnet/payer.json      # throwaway
solana config set --url https://api.devnet.solana.com --keypair ~/dregg-devnet/payer.json

BROADCAST →  solana airdrop 2      # free devnet SOL; repeat once (deploy of a
BROADCAST →  solana airdrop 2      #   ~95 KB upgradeable program needs ~1.3 SOL
                                   #   rent + fees — 4 SOL is comfortable head-room)
solana balance
```

> Airdrop dry-run note: the toolchain is present and `solana config` already points
> at devnet, so `solana airdrop 2` is a free, safe request (it is `BROADCAST →`
> only because it touches the faucet — no value at risk). It is **not** run by this
> prep. If the RPC faucet is rate-limited, use the web faucet above.

### 1.5 Deploy (the one broadcast)

```bash
BROADCAST →  cd /Users/ember/dev/breadstuffs/solana-settlement
BROADCAST →  solana program deploy \
BROADCAST →    target/deploy/dregg_solana_settlement.so \
BROADCAST →    --program-id target/deploy/dregg_solana_settlement-keypair.json \
BROADCAST →    --url https://api.devnet.solana.com
# → "Program Id: BMH1hAqzm9tV2qB713GN9NsbXdT4AQawKGuAUdaD2Gjs"
```

(Deploy the escrow the same way from `solana-lock/` if you want the lock leg too.)

### 1.6 Post-deploy verify

```bash
solana program show BMH1hAqzm9tV2qB713GN9NsbXdT4AQawKGuAUdaD2Gjs --url devnet
# → ProgramData Address, Authority (= your payer), Data Length, Last Deployed Slot
```

That confirms the program is on-chain. Exercising `Init` + `Settle` needs a small
client (below) — there is **no `solana` CLI subcommand for a custom instruction**.

### 1.7 THE COMPUTE-BUDGET STEP (required for `Settle`)

`settle` is the ~27-mul + 2-pairing verify the build lane flagged. Exact
`alt_bn128` syscall costs (pinned from `solana-program-runtime-2.3.13`
`execution_budget.rs`: add=334, mul=3,840, pairing first-pair=36,364,
each-additional-pair=12,121):

| Step (in `groth16::verify`) | Ops | CU |
|---|---|---|
| Pedersen PoK pairing | 2-pair | 48,485 |
| keccak256(commitment) | 128 B | ~213 |
| public-input MSM (`K0+Cm` add, 25×(mul+add), 26th mul+add) | 26 mul, 27 add | 108,858 |
| Groth16 pairing | 4-pair | 72,727 |
| **syscall floor** | | **≈ 230,283** |

Plus deserialization + `find_program_address` (sha256 bump search) + the
`create_account` CPI ≈ 15–25k CU of non-syscall work. **Total `settle` ≈
250–260k CU — it exceeds the 200,000 per-instruction default**, so a settle tx
that does not raise the limit will fail `exceeded CUs`. `Init` and
`AssertProvenRoot` do no pairings and are fine at the default.

**Fix — prepend a `ComputeBudget::set_compute_unit_limit` instruction to the
settle tx.** Pinned recommendation: **600,000 CU** (>2× the floor, well under the
`MAX_COMPUTE_UNIT_LIMIT` of 1,400,000; devnet fee for the bump is negligible).

```rust
use solana_sdk::compute_budget::ComputeBudgetInstruction;
let cu = ComputeBudgetInstruction::set_compute_unit_limit(600_000);
let tx = Transaction::new_with_payer(&[cu, settle_ix], Some(&payer.pubkey()));
```

The raw ComputeBudget instruction (program
`ComputeBudget111111111111111111111111111111`) is `[0x02] ++ u32_le(600000)`.

**Free dry-run to measure the exact CU before broadcasting** — `simulateTransaction`
returns `unitsConsumed` + program logs and writes nothing:

```bash
# Build the settle tx (client below), base64-encode it, then:
curl -s https://api.devnet.solana.com -X POST -H 'content-type: application/json' \
  -d '{"jsonrpc":"2.0","id":1,"method":"simulateTransaction",
       "params":["<BASE64_TX>",{"encoding":"base64","sigVerify":false}]}' | jq '.result.value.unitsConsumed, .result.value.err'
```

Read the actual `unitsConsumed`; if it is under 600,000 (it will be), broadcast.

### 1.8 Settle the fixture (documented; needs a thin client)

There is no CLI for `Settle`. The instruction builder already exists in
`solana-settlement/tests/settle_flow.rs` (`init_ix` L148, `settle_ix` L166) —
lift those into a ~40-line `examples/deploy_settle.rs` binary that:

1. `InitSettlement { genesis_root, vk_hash }` — pin the fixture genesis and the
   dev VK hash. `genesis_root` = the fixture's `genesis_root`
   `[421210617,1637814550,431291584,1953496675,369364366,1006647231,1866996710,48274474]`;
   `vk_hash` = `dregg_solana_settlement::dev_ceremony_vk_hash()`
   (= `keccak256("dregg-settlement-vk-dev-setup")` =
   `0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76`).
   Accounts: payer, settlement PDA `["settlement"]`, genesis marker PDA
   `["proven_root", packLanes(genesis)]`, system program.
2. `Settle { a,b,c,commitment,commitment_pok, inputs:[[u8;32];25] }` — the fixture
   proof + the 25 decimal `inputs`, **with the 600k CU limit prepended** (§1.7).
   Accounts: settlement PDA, payer, final marker PDA
   `["proven_root", packLanes(final)]`, system program.
3. Verify: `AssertProvenRoot { root: packLanes(final_root) }` succeeds (the CPI-able
   `isProvenRoot`), and the state PDA now reads `proven_height = 2`,
   `proven_root = final_root`.

The identical accept/reject is already proven end-to-end in
`solana-settlement/tests/settle_flow.rs` (`real_proof_settles_and_advances_root` /
`forged_proof_rejected_root_unchanged`) on the same `ark-bn254` arithmetic the
on-chain syscalls run — so the on-chain settle is the exercised path, not a new
one.

### 1.9 Solana ready-to-fire sequence

```
1  solana-keygen new -o ~/dregg-devnet/payer.json
2  solana config set --url https://api.devnet.solana.com --keypair ~/dregg-devnet/payer.json
3  solana airdrop 2   (×2)                                             # BROADCAST (faucet)
4  cd solana-settlement && cargo build-sbf                             # (already built)
5  solana program deploy target/deploy/dregg_solana_settlement.so \
     --program-id target/deploy/dregg_solana_settlement-keypair.json  # BROADCAST → Program Id
6  solana program show <PROGRAM_ID> --url devnet                       # verify on-chain
7  cargo run --example deploy_settle   (Init → simulate → Settle 600k) # BROADCAST → root advances
```

---

## 2. COSMOS — CosmWasm testnet

The `cosmos-settlement` contract IS Rust→wasm, so the BN254 Groth16 verify runs
natively (arkworks) inside a CosmWasm runtime — no Cosmos-native circuit needed.

### 2.1 Pinned target — **Osmosis `osmo-test-5`** (recommended)

Chosen because CosmWasm deployment on `osmo-test-5` is **permissionless** (anyone
can `tx wasm store`) and it has a **public web faucet** — the true one-broadcast
path.

| Field | Value |
|---|---|
| Chain id | **`osmo-test-5`** |
| Binary | **`osmosisd`** `v29.0.0` |
| Bech32 prefix | `osmo` |
| Fee/stake denom | `uosmo` |
| RPC | `https://rpc.osmotest5.osmosis.zone:443` |
| REST/LCD | `https://lcd.osmotest5.osmosis.zone` |
| Faucet | `https://faucet.testnet.osmosis.zone` (100 OSMO/day/address) |
| Explorer | `https://celat.one/osmo-test-5` |

**Alternative — Neutron `pion-1`** (only if you want Neutron specifically): binary
`neutrond` `v4.2.2-testnet`, prefix `neutron`, denom `untrn`, RPC
`https://rpc-falcron.pion-1.ntrn.tech`, faucet via the `#testnet-faucet` channel on
Neutron's Discord. **Caveat:** Neutron gates CosmWasm code upload — confirm
`pion-1` permits permissionless `store` before choosing it, or use Osmosis.

### 2.2 Build the OPTIMIZED, deployable wasm

**Do NOT use raw `cargo wasm`.** A plain
`cargo build --target wasm32-unknown-unknown --release` on this mac **fails to
link** (`undefined symbol: db_scan`, `db_remove`) — modern `wasm-ld` errors on the
CosmWasm host imports that the optimizer's pinned toolchain resolves. That is the
"unresolved host symbols" the build lane flagged; those symbols are host functions
the wasmd runtime provides, and the correct build path is the **cosmwasm/optimizer
docker** (which also strips + shrinks arkworks below the chain code-size cap and
gives a reproducible checksum).

The optimizer needed **three fixes** to build this crate (all applied to the build
copy — none change on-chain behavior):

1. **Empty `[workspace]` table** — `cosmos-settlement/Cargo.toml` declares an empty
   `[workspace]` to detach from the parent breadstuffs workspace. The optimizer's
   `bob` then runs workspace-mode and finds **zero members** ("No .wasm file
   built"). Fix: **remove the `[workspace]` table in the build copy** — inside the
   container only the crate is mounted at `/code`, so there is no parent workspace
   to collide with, and `bob`'s single-contract path builds it.
2. **`enum-ordinalize` too new** — the lockfile resolved `enum-ordinalize@4.4.1` +
   `enum-ordinalize-derive@4.4.1` (pulled by `cosmwasm-schema`), which require
   `rustc 1.89`; optimizer `0.17.0` pins `rustc 1.86`. Fix: pin both down —
   `cargo update -p enum-ordinalize --precise 4.3.0` and
   `cargo update -p enum-ordinalize-derive --precise 4.3.0`.
3. **Optimizer image** — use **`cosmwasm/optimizer-arm64:0.17.0`** (rustc 1.86); the
   older `0.16.0` (rustc 1.78) cannot parse `edition2024` manifests in the graph.

Reproducible recipe (a scratch copy keeps the repo tree clean):

```bash
SRC=/Users/ember/dev/breadstuffs/cosmos-settlement
WORK=$(mktemp -d)/cs-opt
rsync -a --exclude target --exclude artifacts "$SRC/" "$WORK/"
cd "$WORK"
# (a) pin the two deps (needs [workspace] present so cargo detaches from /tmp):
printf '\n[workspace]\n' >> Cargo.toml
cargo update -p enum-ordinalize        --precise 4.3.0
cargo update -p enum-ordinalize-derive --precise 4.3.0
# (b) strip the [workspace] table for the single-contract optimizer:
sed -i '' '/^\[workspace\]$/d' Cargo.toml
# (c) build:
docker run --rm -v "$WORK":/code \
  -v cosmos_settlement_cache:/target \
  -v cosmwasm_registry_cache:/usr/local/cargo/registry \
  cosmwasm/optimizer-arm64:0.17.0
# → artifacts/cosmos_settlement.wasm  (+ checksums.txt)
```

> **The clean long-term fix** (so no scratch dance): commit the two `cargo update`
> pins into `cosmos-settlement/Cargo.lock` on the real tree, and restructure the
> crate so the contract is a **subdirectory member** of its workspace
> (`cosmos-settlement/{Cargo.toml [workspace] members=["contract"], contract/…}`) —
> then `docker run … cosmwasm/optimizer-arm64:0.17.0` works directly on the repo
> path with no edits. Same recipe applies to `cosmos-lock` (identical
> empty-`[workspace]` + dep-graph).

Validate the artifact (must pass before deploy) — use a **current** `cosmwasm-check`
(`cargo install cosmwasm-check` — the target chain runs CosmWasm 2.x; an old
`cosmwasm-check 1.x` false-fails on `Unknown opcode 192`, the `i32.extend8_s`
sign-extension op modern chains accept):

```bash
cosmwasm-check artifacts/cosmos_settlement.wasm    # → "All contracts (1) passed checks!"
```

Verified artifact (this build): **380,916 bytes** · sha256
**`072e488ab46d13105a0d79bd71e10e92b194e9b4a3844cb16c2ac25a5c70bb0c`** ·
`cosmwasm-check 2.2.2` **pass** · exports `interface_version_8`/`instantiate`/
`execute`/`query`/`allocate`/`deallocate`, imports only `env` host functions (the
`db_scan`/`db_remove` that fail to link under raw `cargo wasm` are correctly
resolved here as wasm imports). A copy is at
`cosmos-settlement/artifacts/cosmos_settlement.wasm` (gitignored). The wasm is well
under Osmosis's contract code-size cap.

### 2.3 Fund a throwaway account (free)

```bash
osmosisd keys add dregg-devnet                          # throwaway; prints osmo1... addr
# Fund it at the faucet (paste the address):
BROADCAST →  open https://faucet.testnet.osmosis.zone   # 100 OSMO/day
osmosisd query bank balances <osmo1...> --node https://rpc.osmotest5.osmosis.zone:443
```

### 2.4 Store + instantiate (the one broadcast)

```bash
NODE=https://rpc.osmotest5.osmosis.zone:443
TXFLAGS="--chain-id osmo-test-5 --node $NODE --from dregg-devnet \
  --gas auto --gas-adjustment 1.3 --gas-prices 0.025uosmo -y -o json"

# STORE → code_id
BROADCAST →  osmosisd tx wasm store artifacts/cosmos_settlement.wasm $TXFLAGS
#   parse: .logs[0].events[?type==wasm|store_code].attributes[?key==code_id].value
BROADCAST →  osmosisd query wasm list-code --node $NODE -o json   # confirm your code_id

# INSTANTIATE → contract address (init_msg pins genesis + VK-hash commitment)
INIT='{"genesis_root":[421210617,1637814550,431291584,1953496675,369364366,1006647231,1866996710,48274474],"verifying_key_hash":"0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76"}'
BROADCAST →  osmosisd tx wasm instantiate <CODE_ID> "$INIT" \
BROADCAST →    --label dregg-settlement --admin <osmo1...> $TXFLAGS
#   parse the instantiate event → contract address osmo1...
```

`init_msg` shape (`cosmos-settlement/src/msg.rs::InstantiateMsg`): `genesis_root`
= the fixture's 8 genesis lanes (pinned anchor; the first settle must chain from
it); `verifying_key_hash` = a non-zero hex commitment. The contract **stores** the
hash (it does not re-derive it on the settle path — the VK itself is baked into
`vk.rs`), so any non-zero hex accepts, but pin the cross-chain dev value
`keccak256("dregg-settlement-vk-dev-setup")` above for parity with EVM/Solana.

### 2.5 Post-deploy verify — query + settle the fixture

```bash
C=<contract osmo1...>
# genesis anchor recorded as a proven root at instantiate:
osmosisd query wasm contract-state smart $C '{"genesis_anchor":{}}'      --node $NODE
osmosisd query wasm contract-state smart $C '{"proven_height":{}}'       --node $NODE   # 0

# SETTLE the fixture proof (ExecuteMsg::Settle — all values from the fixture):
SETTLE='{"settle":{
  "proof":["0x119d02ca40ded9420e61d11f395886f74ef4472102be4550bf2981d34182a7cf","0x1702db1894a8b14dbdb5eaf2c19b8a93fce6d06fadf1aa785145e6a0b617f1cb","0x28c637617cbc82fb949f71225389f668cc3b64ee3bec7d11ab4c11123e8c26b0","0x23c4575a38a03c3bf2840629bb1249e9858d8799c467b172b7c51c21da3749f6","0x055db749150016c9a1cf773d039e1d8c5212c42cf2ed5cf3d8e86627467d222b","0x1529fa5f259767c5543e4ee48b6a2ca33384f6a039ab455c341c125e8da81620","0x0c5704d885096d54a554e0d86706dedfa8e403e28df25ce9a3f4d13980b08185","0x26f2452ed17f53b5cb545e1094b713b7e1d7ef9da7400952acddec6cb21ba198"],
  "commitments":["0x1ec02e59cb3cece02d5ea559319e44912541cfc89b2a989bd6e44cae642d2991","0x291faa6cc18eaf85261085a0e4a345a4bc7c2e82c1392d0220787d76da7bd563"],
  "commitment_pok":["0x275d173d5d5aa8aaeb538ec547d71edd663c65baae3061b3ea4071268364caf6","0x2486025686025284e5cea091963741a41953be3ba614943d869e5919ed406fb6"],
  "genesis_root":[421210617,1637814550,431291584,1953496675,369364366,1006647231,1866996710,48274474],
  "final_root":[475853519,766719301,209460128,156803433,548349625,139347276,174962960,1721084437],
  "num_turns":2,
  "chain_digest":[1452650278,1371598315,900534217,247034909,1097876273,883942418,247917708,237544049]}}'
BROADCAST →  osmosisd tx wasm execute $C "$SETTLE" $TXFLAGS

# verify it advanced (proven_height → 2; final root is now isProvenRoot):
osmosisd query wasm contract-state smart $C '{"proven_height":{}}'       --node $NODE   # 2
osmosisd query wasm contract-state smart $C '{"proven_root_lanes":{}}'   --node $NODE   # final_root
osmosisd query wasm contract-state smart $C \
  '{"is_proven_root":{"root":"<packLanes(final_root) hex>"}}'            --node $NODE   # true
```

CosmWasm has no per-instruction CU cap like Solana; `--gas auto` sizes the gas
(the arkworks pairing settle is gas-heavy but within a block — `--gas-adjustment
1.3` gives head-room). The accept/reject is already proven in
`cosmos-settlement/tests/settlement.rs` via `cw-multi-test`.

### 2.6 Cosmos ready-to-fire sequence

```
1  install osmosisd v29.0.0 (§Blockers B3)
2  build artifacts/cosmos_settlement.wasm via the optimizer recipe (§2.2)  # done
3  cosmwasm-check artifacts/cosmos_settlement.wasm                         # PASS
4  osmosisd keys add dregg-devnet
5  fund at https://faucet.testnet.osmosis.zone                            # BROADCAST (faucet)
6  osmosisd tx wasm store artifacts/cosmos_settlement.wasm $TXFLAGS       # BROADCAST → code_id
7  osmosisd tx wasm instantiate <code_id> "$INIT" ...                     # BROADCAST → contract
8  osmosisd tx wasm execute <contract> "$SETTLE" $TXFLAGS                 # BROADCAST → root advances
9  query proven_height / is_proven_root                                    # verify
```

---

## 3. HONEST BLOCKERS (what is NOT ready — each with its fix)

- **B1 — Solana settle compute budget (measured, fixable, not yet exercised
  on-chain).** The syscall floor is **≈230k CU** and total settle **≈250–260k >
  200k default**, so a settle tx MUST prepend
  `set_compute_unit_limit(600_000)` (§1.7). This is computed from the pinned cost
  table, **not** yet measured on a live devnet tx. **Do first:** build the settle
  tx, `simulateTransaction` it (free, §1.7), read `unitsConsumed`, confirm < 600k.
  Deploy itself has no such concern.

- **B2 — No CLI for the custom Solana `Settle` instruction.** `solana program
  deploy` puts the program on-chain, but `Init`/`Settle`/`AssertProvenRoot` need a
  ~40-line client. **Do first:** add a `deploy_settle.rs` example under `solana-settlement/examples/`
  lifting the instruction builders from `solana-settlement/tests/settle_flow.rs` (L148–L204) and
  prepending the CU-limit ix. (Deploy alone is one command and needs no client.)

- **B3 — Chain CLI not installed.** `osmosisd` (and `neutrond`) are **not** on this
  box. **Do first:**
  `curl -sL https://get.osmosis.zone/install | bash` (installs `osmosisd`), or build
  `v29.0.0` from `github.com/osmosis-labs/osmosis`, or run it via the official
  docker image. `anchor` is **not** needed. `solana`/`cargo-build-sbf`/`docker`/
  `cosmwasm-check`/`wasm-opt` are all present.

- **B4 — Cosmos optimizer needs the 3 fixes in §2.2 (empty-`[workspace]` + two dep
  pins + image `0.17.0`).** The optimized wasm **does build deployable** with the
  scratch recipe (verified, §2.2). **Do first (clean path):** commit the
  `enum-ordinalize`/`-derive` `4.3.0` pins into `cosmos-settlement/Cargo.lock`
  (and `cosmos-lock`), and optionally restructure the contract into a subdirectory
  member so the optimizer runs on the repo path with no per-build edits.

- **B5 — Funded throwaway keys needed (both chains).** No devnet key is committed
  (Solana `~/dregg-devnet/payer.json` and the `osmosisd` key are created fresh).
  **Do first:** generate them (§1.4, §2.3) and hit the free faucets. No mainnet key,
  no real value, ever.

- **B6 — Dev trusted setup, not MPC.** The VK across all three chains is the
  single-party dev ceremony (`keccak256("dregg-settlement-vk-dev-setup")`). This is
  the standing "verifier is real, ceremony is dev" caveat — a production settlement
  needs the MPC-ceremony VK re-pinned at `Init`/`instantiate`. Not a deploy blocker;
  a trust-scope statement.

---

## What is proven vs. what remains

**Proven (verified while writing this):** both Solana `.so`s build as deployable
SBF ELFs; the optimized CosmWasm `.wasm` builds + passes `cosmwasm-check`; the
targets/faucets/RPCs are pinned to current registry values; the compute-budget CU
is computed from the pinned syscall cost table; the accept/reject of both verifiers
is already tested end-to-end on the real fixture (`settle_flow.rs`,
`settlement.rs`). **Remains (all named above):** install `osmosisd` (B3), commit
the two Cargo.lock pins (B4), add the Solana settle client (B2), measure the settle
CU on a devnet `simulateTransaction` (B1), fund throwaway keys (B5). Then it is
ember's one broadcast per chain.
