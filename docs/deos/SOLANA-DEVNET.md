# The dregg Solana bridge against the real Solana devnet

This is the runbook for driving the bridge against the **public Solana devnet** —
a free, real cluster with real validators. It is the devnet sibling of the local
`solana-test-validator` harness (`scripts/solana-local-harness.sh` +
`bridge/tests/solana_local_e2e.rs`). Devnet proves the path against real
infrastructure; the local validator proves the fully-trustless consensus leg that
devnet cannot expose off-chain (see "trustless vs oracle" below).

`$DREGG` proper lives on Solana **mainnet**. On devnet the harness mints a
stand-in SPL token of the same shape (0 decimals) — devnet is for proving the
plumbing, not for the real asset.

## Proven run (real devnet, 2026-06-28)

The full path ran end-to-end against the real public devnet. The harness minted
a stand-in `$DREGG`, locked an amount into a vault, harvested the real on-chain
artifacts, and the gated `solana_devnet_e2e` test verified all three legs.

| Fact | Value |
| --- | --- |
| Cluster / RPC | devnet / `https://api.devnet.solana.com` |
| Payer wallet | `9zbZqitgHv2G9fYKKvhUujvWEuNkFtA1Z4qCQJsmrN42` (funded with 5 SOL) |
| Stand-in `$DREGG` SPL mint | `BdEF6jxFUtydj3eMRWhSHVD1kSvSW4swBrJ3RxT7dcJ4` (0 decimals, supply 1000) |
| Vault account | `CWVuZdJ5WSMtB7JJSzN7bbLTefhdWPfexxq6rxC8c7MY` |
| Locked amount | **250** `$DREGG` (confirmed on-chain: vault token balance = 250) |
| Slot / epoch | 472650199 / 1094 |

What the gated test proved against those real artifacts:

- **Leg 1 — oracle-attested mirror mint.** The real devnet lock of **250** was
  attested and minted into conserved mirror credit: `live_supply = 250`,
  `currently_locked = 250`, conservation invariant holds. A second mint of the
  same lock id was rejected (replay-safe). The mirror credit then paid an
  execution-lease of **100** (`min(locked, 100)`) through the same `resolve_pay`
  rail — exactly one conserving `Transfer` — and conservation survived the pay.
- **Leg 2 — trustless `StructureOnly` inclusion** over the real devnet vault
  bytes (real lamports `2039280`, owner `Tokenkeg…`, executable/rent_epoch). The
  inclusion + binding machinery accepted the genuine devnet account leaf
  (`LockProofTrust::StructureOnly` — structure, not a counted consensus).
- **Leg 3 — real-byte `VoteState` decode.** A real devnet vote account
  (`vgcDar2pryHvMgPkKaZfh8pQy4BJxv7SpwUG7zinWjG`) was decoded; the bank-state
  decoder recovered authorized voter `dv3qDFk1DTF36Z62bNvrCXe9sKATA6xvVy6A798xxAS`.

Note: devnet accounts are ephemeral; the mint/vault pubkeys above are a snapshot
of this run. Re-running the harness produces a fresh set. The ungated suite still
skips cleanly (no devnet access ever required to keep CI green).

## What you need

- The free Agave/Solana toolchain (`solana`, `solana-keygen`, `spl-token`) and `jq`:

  ```sh
  sh -c "$(curl -sSfL https://release.anza.xyz/stable/install)"
  export PATH="$HOME/.local/share/solana/install/active_release/bin:$PATH"
  ```

- Devnet SOL in a keypair. The harness requests it via `solana airdrop`. The
  public devnet faucet is **rate-limited per IP** and is frequently exhausted; if
  the airdrop loop cannot fund the keypair, the harness prints the keypair pubkey
  and exits with a clear message. Fund it once at <https://faucet.solana.com> (or
  wait for the rate limit to clear) and re-run — nothing else in the harness needs
  the faucet. The proven run above used a keypair funded out-of-band (5 SOL); once
  funded, the harness skips the airdrop loop and runs the whole path.

## How to run it

```sh
# Fund a devnet keypair, mint a stand-in $DREGG, lock it into a vault, harvest
# the real on-chain artifacts into a manifest, and run the gated e2e test:
scripts/solana-devnet-harness.sh --run-test

# Or harvest only, then run the test by hand:
scripts/solana-devnet-harness.sh
SOLANA_DEVNET=1 DREGG_SOLANA_DEVNET_ARTIFACTS=/tmp/dregg-solana-devnet/manifest.json \
  cargo test -p dregg-bridge --test solana_devnet_e2e -- --nocapture
```

The test is **gated on `SOLANA_DEVNET=1`**. Without it (the default `cargo test
-p dregg-bridge` and CI) it skips cleanly, so no devnet access is ever required to
keep the suite green.

The harness does, in order:

1. `solana config set --url https://api.devnet.solana.com`.
2. Create/fund a payer keypair (`airdrop`, with retries; honest exit if rate-limited).
3. Create the stand-in `$DREGG` SPL token (0 decimals) and mint a supply.
4. Lock `LOCK_AMOUNT` (default 250) into a vault account (a second owner's ATA).
5. Harvest the REAL devnet artifacts over RPC: the vault account's
   bytes/lamports/owner, the SPL mint, the slot/epoch/blockhash, the highest-stake
   live vote account, and the `StakeHistory` sysvar.
6. Write `manifest.json` + raw account side-car files.

## Trustless-real vs oracle-attested ON DEVNET

The bridge has two inbound trust models (full background in
`docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`): the **trusted-oracle mirror**
(`mint_against_lock` — an oracle attests the lock) and the **trustless
consensus-anchored proof** (`verify_lock_proof_consensus_anchored` — dregg
verifies Solana's own ≥2/3 stake-weighted votes + accounts-hash inclusion).

The devnet e2e exercises three legs, each named exactly:

| Leg | What is real | What it proves | Trust |
| --- | --- | --- | --- |
| **1. Oracle-attested mirror mint** | The lock: real SPL mint, real vault account, real locked amount, real lamports/owner — all harvested from devnet RPC | A real devnet lock → conserved mirror mint → pays a lease via `resolve_pay` | Oracle's word on the *consensus* |
| **2. Trustless StructureOnly inclusion** | The vault account's real devnet bytes/lamports/owner | The inclusion + binding machinery accepts a genuine devnet account (`LockProofTrust::StructureOnly`) | Structure only — NOT a consensus guarantee |
| **3. Real-byte VoteState decode** | A real devnet vote account's on-chain `VoteState` | The bank-state decoder (`decode_authorized_voter`) handles genuine devnet data | n/a (decode only) |

So on devnet the bridge runs **end-to-end through the trusted-oracle mirror path
against a real devnet lock**, plus the trustless structural and decoder legs over
genuine devnet bytes.

### Why the fully-trustless consensus path can't run against devnet off-chain

`verify_lock_proof_consensus_anchored` needs both:

- **genuine ≥2/3 stake-weighted Ed25519 vote signatures over the real bank
  hash**, and
- **the accounts-hash Merkle inclusion path** the validators committed to.

Devnet RPC exposes neither the bank-hash components nor the accounts-Merkle proofs
(the same limitation the local harness documents), and the real validators'
authorized-voter **private keys** are — correctly — not obtainable off-chain. You
cannot forge their votes, and you cannot reproduce the bank hash they signed. The
local `solana-test-validator` harness *can* run this leg only because the single
bootstrap validator's voter keypair sits in the local ledger directory; a real
multi-validator cluster cannot hand that out.

## The path to mainnet (the real `$DREGG` bridge)

What devnet proves: the bridge accounting, the conservation invariant, the
oracle-attested mint, the inclusion/binding machinery, and the bank-state decoders
all run against real Solana cluster state.

What mainnet additionally requires for the **fully-trustless** path:

1. **A deployed on-chain lock program** — a real Solana program whose vault
   account schema matches the bridge's `encode_lock_record` layout (today the
   record layout is the adapter's deploy-time choice; no lock program is deployed
   on devnet).
2. **A snapshot/geyser pipeline** that surfaces what RPC hides: the bank-hash
   components and the accounts-hash Merkle inclusion proof for the vault account.
   A Solana **geyser plugin** (or the accounts-hash snapshot service) is the
   standard source. With those, the relayer assembles the real inclusion path.
3. **Real harvested vote transactions** carrying the genuine authorized-voter
   signatures over the real bank hash (these are on-chain; the relayer collects
   ≥2/3 of epoch stake) — fed through `ingest_vote_transaction` +
   `verify_lock_proof_consensus_anchored` against a weak-subjectivity-anchored
   stake table (`derive_stake_table` / `WeakSubjectivityAnchor`).
4. The succinct-wrapper option (`docs/deos/SOLANA-SUCCINCT-WRAPPER.md`) folds the
   consensus verify into a constant-cost on-dregg check; the in-process
   `verify_lock_proof_consensus_anchored` is the typed seam it replaces.

### What needs ember (mainnet)

- **A funded mainnet keypair** holding (or able to lock) real `$DREGG`, plus a
  mainnet RPC endpoint, when the mainnet bridge is actually wired.
- **A geyser/snapshot endpoint** for the trustless accounts-inclusion proofs
  (self-hosted geyser plugin, or a provider that exposes accounts-hash proofs).
- A decision on the on-chain lock program deploy (the vault schema) and the
  oracle set for the interim trusted-mirror path on mainnet.
