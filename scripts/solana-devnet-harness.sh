#!/usr/bin/env bash
# solana-devnet-harness.sh — drive the dregg Solana bridge against the REAL
# public Solana **devnet** (free, real cluster, real validators).
#
# This is the devnet sibling of `scripts/solana-local-harness.sh`. Instead of
# booting a private `solana-test-validator`, it talks to `api.devnet.solana.com`:
# it funds a keypair with FREE devnet SOL (airdrop), mints a stand-in `$DREGG`
# SPL token (the real $DREGG lives on mainnet — devnet is for proving the path),
# locks an amount into a vault account, and harvests the REAL on-chain artifacts
# the `solana_devnet_e2e` test (bridge/tests/solana_devnet_e2e.rs, gated on
# SOLANA_DEVNET=1) feeds through the bridge verify + mint.
#
# Usage:
#   scripts/solana-devnet-harness.sh             # fund, lock, harvest, leave manifest
#   scripts/solana-devnet-harness.sh --run-test  # also run the gated e2e test
#
# Output: $ARTIFACTS_DIR/manifest.json (default /tmp/dregg-solana-devnet) + the
# raw account-data side-car files it references.
#
# ── Honest accounting (trustless-real vs oracle-attested on devnet) ──────────
# The REAL lock state is harvested from devnet RPC: the SPL mint, the vault
# account's real bytes/lamports/owner, the locked amount, the slot/epoch/
# blockhash, and a real devnet vote account + the StakeHistory sysvar (so the
# bridge's bank-state DECODERS chew on genuine devnet bytes).
#
# What devnet RPC does NOT expose (same limitation the local harness documents):
#   * the bank-hash-committed accounts-Merkle INCLUSION proofs, and
#   * the real bank hash the validators signed.
# And on devnet you cannot obtain the real validators' authorized-voter PRIVATE
# keys (they are, correctly, private). So the fully-trustless
# `verify_lock_proof_consensus_anchored` path — which needs genuine ≥2/3
# stake-weighted vote signatures over the real bank hash AND the accounts-hash
# inclusion path — CANNOT be assembled off-chain against devnet. That path's real
# home is a Solana snapshot/geyser pipeline (the mainnet route; see
# docs/deos/SOLANA-DEVNET.md).
#
# Therefore on devnet the bridge runs the **trusted-oracle mirror path**
# (`mint_against_lock`) against the REAL harvested devnet lock, plus the
# trustless **StructureOnly** inclusion leg over the REAL vault bytes. Both are
# named precisely in the test and the doc.
set -euo pipefail

ARTIFACTS_DIR="${ARTIFACTS_DIR:-/tmp/dregg-solana-devnet}"
MANIFEST="$ARTIFACTS_DIR/manifest.json"
RPC_URL="${RPC_URL:-https://api.devnet.solana.com}"
LOCK_AMOUNT="${LOCK_AMOUNT:-250}"        # integer token units (token has 0 decimals)
MINT_AMOUNT="${MINT_AMOUNT:-1000}"
AIRDROP_SOL="${AIRDROP_SOL:-2}"
AIRDROP_RETRIES="${AIRDROP_RETRIES:-8}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Make a locally-installed Agave toolchain visible.
export PATH="$HOME/.local/share/solana/install/active_release/bin:$PATH"

note() { printf '\033[36m[devnet]\033[0m %s\n' "$*" >&2; }
fail() { printf '\033[31m[devnet] %s\033[0m\n' "$*" >&2; exit 1; }

# ---- 0. tool check ---------------------------------------------------------
missing=()
for t in solana solana-keygen spl-token jq; do
  command -v "$t" >/dev/null 2>&1 || missing+=("$t")
done
if [ "${#missing[@]}" -ne 0 ]; then
  cat >&2 <<EOF
[devnet] missing tools: ${missing[*]}

Install the free Agave/Solana toolchain (CLI + spl-token):

  sh -c "\$(curl -sSfL https://release.anza.xyz/stable/install)"
  export PATH="\$HOME/.local/share/solana/install/active_release/bin:\$PATH"

(and \`brew install jq\` if jq is missing). Then re-run this script.
EOF
  exit 2
fi

mkdir -p "$ARTIFACTS_DIR"

# ---- 1. point the CLI at devnet --------------------------------------------
note "configuring the CLI for devnet ($RPC_URL) ..."
solana config set --url "$RPC_URL" >/dev/null
solana cluster-version >/dev/null 2>&1 || fail "devnet RPC unreachable ($RPC_URL)"

# ---- 2. fund a keypair with FREE devnet SOL --------------------------------
PAYER="$ARTIFACTS_DIR/payer.json"
[ -f "$PAYER" ] || solana-keygen new --no-bip39-passphrase --force --silent --outfile "$PAYER" >/dev/null
PAYER_PK="$(solana-keygen pubkey "$PAYER")"
solana config set --keypair "$PAYER" >/dev/null
note "payer: $PAYER_PK"

balance_sol() { solana balance "$PAYER_PK" 2>/dev/null | awk '{print $1}'; }
have_funds() { awk -v b="$(balance_sol)" 'BEGIN{exit !(b+0 >= 0.5)}'; }

if ! have_funds; then
  note "requesting a devnet airdrop ($AIRDROP_SOL SOL) — the public faucet is rate-limited ..."
  for i in $(seq 1 "$AIRDROP_RETRIES"); do
    solana airdrop "$AIRDROP_SOL" "$PAYER_PK" >/dev/null 2>&1 || true
    sleep 8
    if have_funds; then note "funded: $(balance_sol) SOL"; break; fi
    note "  airdrop attempt $i: balance still $(balance_sol) SOL (faucet rate-limited); retrying ..."
  done
fi

if ! have_funds; then
  cat >&2 <<EOF
[devnet] could not obtain devnet SOL via the public faucet (rate-limited).
This is a faucet limitation, not a bridge problem. Fund the keypair once and
re-run — the rest of the harness needs no faucet:

  payer pubkey: $PAYER_PK
  keypair file: $PAYER

Options:
  * web faucet:  https://faucet.solana.com  (paste the pubkey above)
  * or wait for the per-IP rate limit to clear, then re-run this script.
EOF
  exit 3
fi

# ---- 3. mint a stand-in \$DREGG SPL token -----------------------------------
ata() { spl-token address --verbose --token "$1" --owner "$2" --output json | jq -r '.associatedTokenAddress'; }

note "creating the stand-in \$DREGG SPL token (0 decimals) on devnet ..."
MINT=$(spl-token create-token --decimals 0 --fee-payer "$PAYER" --mint-authority "$PAYER_PK" \
        --output json 2>/dev/null | jq -r '.commandOutput.address')
[ -n "$MINT" ] && [ "$MINT" != "null" ] || fail "token mint creation failed"

spl-token create-account "$MINT" --fee-payer "$PAYER" --owner "$PAYER_PK" >/dev/null
SRC_ATA="$(ata "$MINT" "$PAYER_PK")"
spl-token mint "$MINT" "$MINT_AMOUNT" "$SRC_ATA" --fee-payer "$PAYER" --mint-authority "$PAYER" >/dev/null

# ---- 4. lock an amount into a vault account --------------------------------
VAULT_OWNER="$ARTIFACTS_DIR/vault-owner.json"
[ -f "$VAULT_OWNER" ] || solana-keygen new --no-bip39-passphrase --force --silent --outfile "$VAULT_OWNER" >/dev/null
VAULT_OWNER_PK="$(solana-keygen pubkey "$VAULT_OWNER")"
spl-token create-account "$MINT" --owner "$VAULT_OWNER_PK" --fee-payer "$PAYER" >/dev/null
VAULT="$(ata "$MINT" "$VAULT_OWNER_PK")"
note "locking $LOCK_AMOUNT \$DREGG into the devnet vault $VAULT ..."
spl-token transfer "$MINT" "$LOCK_AMOUNT" "$VAULT" --fee-payer "$PAYER" --owner "$PAYER" \
  --allow-unfunded-recipient >/dev/null

# ---- 5. harvest the real devnet artifacts ----------------------------------
EPOCH=$(solana epoch-info --output json | jq -r '.epoch')
SLOT=$(solana epoch-info --output json | jq -r '.absoluteSlot')
BLOCKHASH=$(solana block "$SLOT" --output json 2>/dev/null | jq -r '.blockhash // empty')
[ -n "$BLOCKHASH" ] || BLOCKHASH=$(solana epoch-info --output json | jq -r '.blockHeight')

# Dump <pubkey> account data to <file>.bin and emit a JSON object with its real
# on-chain header fields + a pointer to the data file.
harvest() {
  local pubkey="$1" label="$2"
  local bin="$ARTIFACTS_DIR/$label.bin"
  solana account "$pubkey" --output-file "$bin" >/dev/null
  local info; info=$(solana account "$pubkey" --output json)
  jq -n \
    --arg pubkey "$pubkey" \
    --arg data_file "$bin" \
    --argjson lamports "$(jq -r '.account.lamports' <<<"$info")" \
    --arg owner "$(jq -r '.account.owner' <<<"$info")" \
    --argjson executable "$(jq -r '.account.executable' <<<"$info")" \
    --argjson rent_epoch "$(jq -r '.account.rentEpoch | if . > 9223372036854775807 then 0 else . end' <<<"$info")" \
    '{pubkey:$pubkey, lamports:$lamports, owner:$owner, executable:$executable, rent_epoch:$rent_epoch, data_file:$data_file}'
}

note "harvesting real devnet artifacts ..."
VAULT_JSON=$(harvest "$VAULT" vault_account)

# A real devnet vote account (for the bridge's real-byte VoteState decoder) +
# the StakeHistory sysvar. Pick the highest-stake current vote account.
VOTE_ACCT=$(solana validators --output json 2>/dev/null \
  | jq -r '.validators | sort_by(.activatedStake) | reverse | .[0].voteAccountPubkey // empty')
STAKE_HISTORY="SysvarStakeHistory1111111111111111111111111"

if [ -n "$VOTE_ACCT" ]; then
  note "  real devnet vote account: $VOTE_ACCT"
  VOTE_JSON=$(harvest "$VOTE_ACCT" vote_account)
else
  note "  (no vote account listed by RPC; skipping the real-VoteState decode leg)"
  VOTE_JSON=null
fi
SH_JSON=$(harvest "$STAKE_HISTORY" stake_history)

jq -n \
  --arg cluster "devnet" \
  --arg rpc_url "$RPC_URL" \
  --argjson slot "$SLOT" \
  --argjson epoch "$EPOCH" \
  --arg blockhash "$BLOCKHASH" \
  --arg spl_mint "$MINT" \
  --arg vault_account "$VAULT" \
  --argjson locked_amount "$LOCK_AMOUNT" \
  --argjson vault "$VAULT_JSON" \
  --argjson vote_account "$VOTE_JSON" \
  --argjson stake_history "$SH_JSON" \
  '{cluster:$cluster, rpc_url:$rpc_url, slot:$slot, epoch:$epoch, blockhash:$blockhash,
    spl_mint:$spl_mint, vault_account:$vault_account, locked_amount:$locked_amount,
    vault:$vault, vote_account:$vote_account, stake_history:$stake_history}' > "$MANIFEST"

note "manifest written: $MANIFEST"
note "  slot=$SLOT epoch=$EPOCH mint=$MINT vault=$VAULT locked=$LOCK_AMOUNT"

# ---- 6. optionally run the gated e2e test ----------------------------------
if [ "${1:-}" = "--run-test" ]; then
  note "running the gated devnet e2e test against the harvested artifacts ..."
  ( cd "$REPO_ROOT" && \
    SOLANA_DEVNET=1 DREGG_SOLANA_DEVNET_ARTIFACTS="$MANIFEST" \
    cargo test -p dregg-bridge --test solana_devnet_e2e -- --nocapture )
else
  cat >&2 <<EOF
[devnet] to run the e2e test against these artifacts:

  SOLANA_DEVNET=1 DREGG_SOLANA_DEVNET_ARTIFACTS="$MANIFEST" \\
    cargo test -p dregg-bridge --test solana_devnet_e2e -- --nocapture
EOF
fi
