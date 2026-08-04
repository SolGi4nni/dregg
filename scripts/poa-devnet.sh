#!/usr/bin/env bash
# Path of Angels' isolated dregg operator kit.
#
# Protocol objects are always made/read by dregg-node.  This wrapper only binds
# each object to a distinct storage root and port range, pins the resulting
# descriptor, and refuses PoA/main reuse before launching anything.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MANIFEST_TOOL="$SCRIPT_DIR/poa-devnet-manifest.mjs"

POA_ROOT="${POA_ROOT:-${XDG_DATA_HOME:-$HOME/.local/share}/path-of-angels/devnet}"
POA_MAIN_DATA_DIR="${POA_MAIN_DATA_DIR:-$HOME/.dregg}"
POA_VALIDATORS="${POA_VALIDATORS:-3}"
POA_HTTP_BASE="${POA_HTTP_BASE:-8421}"
POA_GOSSIP_BASE="${POA_GOSSIP_BASE:-9421}"
POA_BIND="${POA_BIND:-127.0.0.1}"
POA_NODE_HOSTS="${POA_NODE_HOSTS:-}"

usage() {
  cat <<'EOF'
usage: scripts/poa-devnet.sh COMMAND [ARGS]

Commands:
  genesis                         create a fresh isolated PoA federation bundle
  verify                          re-check descriptor, paths, keys, and ports
  up                              launch every local validator (Lean + proving on)
  health                          probe /status and the pinned membership identity
  readiness                       health plus the objective F-4 admission release gate
  down                            stop only PIDs whose command names their PoA data dir
  operator-command INDEX [HOST]   print one validator's authoritative run command
  follower-init NAME              make a new verifying non-voter and print its pubkey
  follower-command NAME BOOTSTRAP [BIND]
                                  print the follower-first `dregg-node join` command
  follower-run NAME BOOTSTRAP [BIND]
                                  verify isolation, then exec `join` (auto-proposes)
  propose NAME [VALIDATOR_INDEX]  explicitly propose a follower through a live validator
  approve PROPOSAL [VALIDATOR_INDEX]
                                  cast one current validator's approval vote

Environment:
  POA_ROOT              PoA-only root (default: XDG data/path-of-angels/devnet)
  POA_MAIN_DATA_DIR     main dregg data dir to refuse reusing (default: ~/.dregg)
  POA_BIN               Lean-linked dregg-node binary
  POA_VALIDATORS        genesis committee size (default: 3)
  POA_HTTP_BASE         first HTTP port (default: 8421)
  POA_GOSSIP_BASE       first gossip port (default: 9421)
  POA_NODE_HOSTS        comma-separated advertised hosts, one per validator
                        (default: loopback for every node; set for real mesh)
  POA_BIND              local validator HTTP bind (default: 127.0.0.1)

The kit never passes --enable-faucet or --auto-approve-joins, never copies the
genesis bundle's .devnet marker into a serving data dir, and never enables the
unverified consensus escape hatch.  A follower pins genesis.json, verifies the
chain first, and only then auto-proposes membership through the node's live API.
EOF
}

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

find_bin() {
  if [ -n "${POA_BIN:-}" ]; then
    [ -x "$POA_BIN" ] || die "POA_BIN is not executable: $POA_BIN"
    printf '%s\n' "$POA_BIN"
    return
  fi
  local candidate
  for candidate in "$REPO_ROOT/target/release/dregg-node" "$REPO_ROOT/target/debug/dregg-node"; do
    if [ -x "$candidate" ]; then
      printf '%s\n' "$candidate"
      return
    fi
  done
  die "no dregg-node binary found; set POA_BIN to a Lean-linked build"
}

BIN="$(find_bin)"

run_manifest_tool() {
  local command="$1"
  shift
  local hosts="$POA_NODE_HOSTS"
  if [ -z "$hosts" ]; then
    if [ -f "$POA_ROOT/poa-devnet.json" ]; then
      hosts="$(node -e '
const manifest = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8"));
process.stdout.write(manifest.nodes.map((node) => node.gossip.advertised_host).join(","));
' "$POA_ROOT/poa-devnet.json")"
    else
      hosts="$(node -e 'process.stdout.write(Array(Number(process.argv[1])).fill("127.0.0.1").join(","))' "$POA_VALIDATORS")"
    fi
  fi
  "$MANIFEST_TOOL" "$command" \
    --root "$POA_ROOT" \
    --main-data-dir "$POA_MAIN_DATA_DIR" \
    --http-base "$POA_HTTP_BASE" \
    --gossip-base "$POA_GOSSIP_BASE" \
    --hosts "$hosts" \
    "$@"
}

json_field() {
  local path="$1"
  node -e '
const path = process.argv[1].split(".");
let value = JSON.parse(require("fs").readFileSync(0, "utf8"));
for (const part of path) value = value?.[part];
if (value === undefined || value === null) process.exit(2);
process.stdout.write(typeof value === "string" ? value : JSON.stringify(value));
' "$path"
}

manifest_field() {
  json_field "$1" < "$POA_ROOT/poa-devnet.json"
}

manifest_node_field() {
  local index="$1"
  local path="$2"
  node -e '
const manifest = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8"));
let value = manifest.nodes[Number(process.argv[2])];
for (const part of process.argv[3].split(".")) value = value?.[part];
if (value === undefined || value === null) process.exit(2);
process.stdout.write(typeof value === "string" ? value : JSON.stringify(value));
' "$POA_ROOT/poa-devnet.json" "$index" "$path"
}

manifest_node_peers() {
  local index="$1"
  node -e '
const manifest = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8"));
const peers = manifest.nodes[Number(process.argv[2])]?.gossip?.peers;
if (!Array.isArray(peers)) process.exit(2);
process.stdout.write(peers.join(","));
' "$POA_ROOT/poa-devnet.json" "$index"
}

node_dir() {
  printf '%s/nodes/node-%s\n' "$POA_ROOT" "$1"
}

http_port() {
  printf '%s\n' "$((POA_HTTP_BASE + $1))"
}

gossip_port() {
  printf '%s\n' "$((POA_GOSSIP_BASE + $1))"
}

node_count() {
  node -e 'process.stdout.write(String(JSON.parse(require("fs").readFileSync(process.argv[1], "utf8")).nodes.length))' \
    "$POA_ROOT/poa-devnet.json"
}

expected_pubkey() {
  local index="$1"
  node -e '
const manifest = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8"));
const index = Number(process.argv[2]);
const value = manifest.nodes[index]?.public_key;
if (!value) process.exit(2);
process.stdout.write(value);
' "$POA_ROOT/poa-devnet.json" "$index"
}

actual_pubkey() {
  local data_dir="$1"
  "$BIN" gen-validator-key --data-dir "$data_dir" --json | json_field public_key
}

assert_validator_pubkeys() {
  local count index expected actual
  count="$(node_count)"
  for ((index = 0; index < count; index += 1)); do
    expected="$(expected_pubkey "$index")"
    actual="$(actual_pubkey "$(node_dir "$index")")"
    [ "$actual" = "$expected" ] || die \
      "node-$index key derives $actual, but pinned genesis enrolls $expected"
  done
}

cmd_genesis() {
  [[ "$POA_VALIDATORS" =~ ^[1-9][0-9]*$ ]] || die "POA_VALIDATORS must be positive"
  if [ -e "$POA_ROOT" ] && [ -n "$(find "$POA_ROOT" -mindepth 1 -maxdepth 1 -print -quit 2>/dev/null)" ]; then
    die "$POA_ROOT is not empty; a federation root is immutable, so choose a fresh POA_ROOT"
  fi

  # Check path separation before spending the real hybrid-key generation work.
  node --input-type=module -e '
import { assertDisjointRoots } from process.argv[1];
assertDisjointRoots(process.argv[2], process.argv[3]);
' "file://$MANIFEST_TOOL" "$POA_ROOT" "$POA_MAIN_DATA_DIR"

  mkdir -p "$POA_ROOT/bundle" "$POA_ROOT/nodes" "$POA_ROOT/followers"
  "$BIN" genesis \
    --validators "$POA_VALIDATORS" \
    --output "$POA_ROOT/bundle" \
    --deployment-domain pathofangels.network/federation/v1 \
    --no-demo-economy

  local index data_dir
  for ((index = 0; index < POA_VALIDATORS; index += 1)); do
    data_dir="$(node_dir "$index")"
    mkdir -p "$data_dir"
    cp "$POA_ROOT/bundle/genesis.json" "$data_dir/genesis.json"
    cp "$POA_ROOT/bundle/node-$index.key" "$data_dir/node.key"
    chmod 600 "$data_dir/node.key"
    # Do NOT copy bundle/.devnet.  The serving dirs must never inherit its
    # implicit auto-approval policy.
  done

  run_manifest_tool create
  assert_validator_pubkeys
  printf '\nPoA federation ready at %s\n' "$POA_ROOT"
  printf '  federation: %s\n' "$(manifest_field federation_id)"
  printf '  next: POA_ROOT=%q scripts/poa-devnet.sh up\n' "$POA_ROOT"
}

cmd_verify() {
  run_manifest_tool verify
  assert_validator_pubkeys
  printf 'verified all validator seeds against the committee public keys\n'
}

load_node_env() {
  local index="$1"
  local env_path line key value
  env_path="$(node_dir "$index")/operator.env"
  [ -f "$env_path" ] || die "missing operator config: $env_path"
  unset POA_DEPLOYMENT_DOMAIN POA_DEPLOYMENT_ID POA_FEDERATION_ID POA_NODE_INDEX
  unset POA_DATA_DIR POA_HTTP_BIND POA_HTTP_PORT POA_GOSSIP_PORT POA_GOSSIP_HOST
  unset POA_FEDERATION_PEERS POA_PROVE_TURNS POA_ENABLE_FAUCET POA_AUTO_APPROVE_JOINS
  unset DREGG_REQUIRE_LEAN DREGG_STRAND_ADMISSION_GATE DREGG_ALLOW_UNVERIFIED_CONSENSUS
  unset DREGG_STATUS_EXPOSE_COUNTS DREGG_SEED_DEMO_LEASE
  while IFS= read -r line || [ -n "$line" ]; do
    [ -n "$line" ] || continue
    [[ "$line" == *=* ]] || die "malformed operator config line in $env_path"
    key="${line%%=*}"
    value="${line#*=}"
    case "$key" in
      POA_DEPLOYMENT_DOMAIN|POA_DEPLOYMENT_ID|POA_FEDERATION_ID|POA_NODE_INDEX|\
      POA_DATA_DIR|POA_HTTP_BIND|POA_HTTP_PORT|POA_GOSSIP_PORT|POA_GOSSIP_HOST|\
      POA_FEDERATION_PEERS|POA_PROVE_TURNS|POA_ENABLE_FAUCET|POA_AUTO_APPROVE_JOINS|\
      DREGG_REQUIRE_LEAN|DREGG_STRAND_ADMISSION_GATE|DREGG_ALLOW_UNVERIFIED_CONSENSUS|\
      DREGG_STATUS_EXPOSE_COUNTS|DREGG_SEED_DEMO_LEASE)
        printf -v "$key" '%s' "$value"
        ;;
      *) die "unknown operator config key $key in $env_path" ;;
    esac
  done < "$env_path"
}

assert_safe_consensus_environment() {
  case "${DREGG_REQUIRE_LEAN-}" in
    ""|1|true|TRUE|on|ON|yes|YES) ;;
    *) die "DREGG_REQUIRE_LEAN=${DREGG_REQUIRE_LEAN} would weaken the PoA Lean requirement" ;;
  esac
  case "${DREGG_STRAND_ADMISSION_GATE-}" in
    ""|1|true|TRUE|on|ON) ;;
    *) die "DREGG_STRAND_ADMISSION_GATE=${DREGG_STRAND_ADMISSION_GATE} would bypass PoA admission" ;;
  esac
  case "${DREGG_ALLOW_UNVERIFIED_CONSENSUS-}" in
    ""|0|false|FALSE|off|OFF) ;;
    *) die "DREGG_ALLOW_UNVERIFIED_CONSENSUS is forbidden for PoA operators" ;;
  esac
}

run_args_for() {
  local index="$1"
  local bind="${2:-}"
  local expected_data_dir
  assert_safe_consensus_environment
  load_node_env "$index"
  expected_data_dir="$(cd "$(node_dir "$index")" && pwd -P)"
  [ "$POA_NODE_INDEX" = "$index" ] || die "operator.env node index mismatch"
  [ "$POA_DEPLOYMENT_DOMAIN" = "pathofangels.network/federation/v1" ] || die \
    "operator.env deployment domain mismatch"
  [ "$POA_DEPLOYMENT_ID" = "$(manifest_field deployment_id)" ] || die \
    "operator.env deployment id mismatch"
  [ "$POA_FEDERATION_ID" = "$(manifest_field federation_id)" ] || die \
    "operator.env federation id mismatch"
  [ "$POA_GOSSIP_HOST" = "$(manifest_node_field "$index" gossip.advertised_host)" ] || die \
    "operator.env advertised gossip host mismatch"
  [ "$POA_DATA_DIR" = "$expected_data_dir" ] || die "operator.env data dir mismatch"
  [ "$POA_HTTP_BIND" = "$(manifest_node_field "$index" http.bind)" ] || die \
    "operator.env HTTP bind mismatch"
  [ "$POA_HTTP_PORT" = "$(manifest_node_field "$index" http.port)" ] || die \
    "operator.env HTTP port mismatch"
  [ "$POA_GOSSIP_PORT" = "$(manifest_node_field "$index" gossip.port)" ] || die \
    "operator.env gossip port mismatch"
  [ "$POA_FEDERATION_PEERS" = "$(manifest_node_peers "$index")" ] || die \
    "operator.env federation peer set mismatch"
  [ "$POA_PROVE_TURNS" = "1" ] || die "PoA operator config must enable full-turn proving"
  [ "$POA_ENABLE_FAUCET" = "0" ] || die "PoA operator config must disable the faucet"
  [ "$POA_AUTO_APPROVE_JOINS" = "0" ] || die \
    "PoA operator config must disable automatic Join approval"
  [ "$DREGG_REQUIRE_LEAN" = "1" ] || die "PoA operator config must require Lean"
  [ "$DREGG_STRAND_ADMISSION_GATE" = "1" ] || die \
    "PoA operator config must enable strand admission"
  [ "$DREGG_ALLOW_UNVERIFIED_CONSENSUS" = "0" ] || die \
    "PoA operator config must forbid unverified consensus"
  [ "$DREGG_STATUS_EXPOSE_COUNTS" = "0" ] || die \
    "PoA operator config must keep private activity counts private"
  [ "$DREGG_SEED_DEMO_LEASE" = "0" ] || die \
    "PoA operator config must not seed the generic demo lease"
  [ -n "$bind" ] || bind="$POA_HTTP_BIND"
  RUN_ARGS=(
    run
    --data-dir "$POA_DATA_DIR"
    --key-file node.key
    --node-index "$index"
    --federation-size "$(node_count)"
    --bind "$bind"
    --port "$POA_HTTP_PORT"
    --gossip-port "$POA_GOSSIP_PORT"
    --federation-peers "$POA_FEDERATION_PEERS"
    --federation-mode full
    --consensus blocklace
    --prove-turns
    --idle-heartbeat-ms 2000
    --block-cadence-ms 1000
    --min-block-interval-ms 1000
  )
}

cmd_operator_command() {
  local index="${1:?operator-command requires INDEX}"
  local host="${2:-$POA_BIND}"
  local expected actual
  run_manifest_tool verify-public >/dev/null
  expected="$(expected_pubkey "$index")"
  actual="$(actual_pubkey "$(node_dir "$index")")"
  [ "$actual" = "$expected" ] || die \
    "node-$index key derives $actual, but manifest enrolls $expected"
  run_args_for "$index" "$host"
  printf 'DREGG_REQUIRE_LEAN=1 DREGG_STRAND_ADMISSION_GATE=1 '
  printf 'DREGG_ALLOW_UNVERIFIED_CONSENSUS=0 DREGG_STATUS_EXPOSE_COUNTS=0 DREGG_SEED_DEMO_LEASE=0 '
  printf '%q ' "$BIN" "${RUN_ARGS[@]}"
  printf '\n'
}

cmd_up() {
  cmd_verify
  local count index data_dir pid
  count="$(node_count)"
  if node -e '
const m = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8"));
const local = (h) => h === "localhost" || h.startsWith("127.");
process.exit(m.nodes.every((n) => local(n.gossip.advertised_host)) ? 0 : 1);
' "$POA_ROOT/poa-devnet.json"; then
    :
  else
    die "up is the one-host launcher, but manifest advertises multiple hosts; run operator-command on each host"
  fi
  for ((index = 0; index < count; index += 1)); do
    data_dir="$(node_dir "$index")"
    if [ -f "$data_dir/node.pid" ]; then
      pid="$(<"$data_dir/node.pid")"
      if [[ "$pid" =~ ^[0-9]+$ ]] && kill -0 "$pid" 2>/dev/null; then
        die "node-$index already appears live as pid $pid"
      fi
      mv "$data_dir/node.pid" "$data_dir/node.pid.stale-$(date +%s)"
    fi
    run_args_for "$index" "$POA_BIND"
    DREGG_REQUIRE_LEAN=1 DREGG_STRAND_ADMISSION_GATE=1 \
      DREGG_ALLOW_UNVERIFIED_CONSENSUS=0 DREGG_STATUS_EXPOSE_COUNTS=0 DREGG_SEED_DEMO_LEASE=0 \
      nohup "$BIN" "${RUN_ARGS[@]}" > "$data_dir/node.log" 2>&1 &
    pid=$!
    printf '%s\n' "$pid" > "$data_dir/node.pid"
    printf 'started node-%s pid=%s http=%s gossip=%s\n' \
      "$index" "$pid" "$(http_port "$index")" "$(gossip_port "$index")"
  done

  sleep 2
  for ((index = 0; index < count; index += 1)); do
    data_dir="$(node_dir "$index")"
    pid="$(<"$data_dir/node.pid")"
    if ! kill -0 "$pid" 2>/dev/null; then
      tail -n 40 "$data_dir/node.log" >&2 || true
      die "node-$index exited during startup"
    fi
  done
  printf "all PoA validators are running; use \`%s health\`\n" "$0"
}

check_health_json() {
  local expected_federation="$1"
  local index="$2"
  local status_path="$3"
  local membership_path="$4"
  # shellcheck disable=SC2016
  node -e '
const fs = require("fs");
const expected = process.argv[1];
const index = process.argv[2];
const status = JSON.parse(fs.readFileSync(process.argv[3], "utf8"));
const membership = JSON.parse(fs.readFileSync(process.argv[4], "utf8"));
const failures = [];
if (membership.federation_id !== expected) failures.push("wrong federation_id");
if (status.federation_mode !== "full") failures.push("not full consensus mode");
if (status.full_turn_proving !== true) failures.push("full-turn proving is off");
if (status.lean_producer !== true) failures.push("Lean producer is off");
if (Object.hasOwn(status, "note_count") || Object.hasOwn(status, "revocation_count")) {
  failures.push("private activity volume is public");
}
if (failures.length) {
  console.error(`node-${index}: ${failures.join(", ")}`);
  process.exit(1);
}
console.log(`node-${index}: healthy=${status.healthy} peers=${status.peer_count} dag=${status.dag_height} federation=${expected}`);
' "$expected_federation" "$index" "$status_path" "$membership_path"
}

cmd_health() {
  cmd_verify
  local expected count index port status_tmp membership_tmp
  expected="$(manifest_field federation_id)"
  count="$(node_count)"
  for ((index = 0; index < count; index += 1)); do
    port="$(http_port "$index")"
    "$BIN" status --port "$port" >/dev/null
    status_tmp="$(mktemp "${TMPDIR:-/tmp}/poa-status.XXXXXX")"
    membership_tmp="$(mktemp "${TMPDIR:-/tmp}/poa-membership.XXXXXX")"
    curl -fsS --connect-timeout 2 --max-time 10 "http://127.0.0.1:$port/status" > "$status_tmp"
    curl -fsS --connect-timeout 2 --max-time 10 "http://127.0.0.1:$port/api/membership" > "$membership_tmp"
    check_health_json "$expected" "$index" "$status_tmp" "$membership_tmp"
    mv "$status_tmp" "$status_tmp.checked"
    mv "$membership_tmp" "$membership_tmp.checked"
  done
}

cmd_readiness() {
  cmd_health
  local ready admission
  ready="$(manifest_field policy.objective_vouch_admission_ready)"
  admission="$(manifest_field policy.admission)"
  if [ "$ready" != "true" ]; then
    die "PoA trustless-admission readiness is RED: live production still uses $admission; the F-4 gate does not yet receive chain-derived candidate/vouch rows"
  fi
}

cmd_down() {
  cmd_verify
  local count index data_dir pid command_line
  count="$(node_count)"
  for ((index = 0; index < count; index += 1)); do
    data_dir="$(node_dir "$index")"
    [ -f "$data_dir/node.pid" ] || continue
    pid="$(<"$data_dir/node.pid")"
    [[ "$pid" =~ ^[0-9]+$ ]] || die "malformed pid file: $data_dir/node.pid"
    if kill -0 "$pid" 2>/dev/null; then
      command_line="$(ps -p "$pid" -o command=)"
      [[ "$command_line" == *"--data-dir $data_dir"* ]] || die \
        "pid $pid no longer names $data_dir; refusing to kill a reused pid"
      kill "$pid"
      printf 'stopped node-%s pid=%s\n' "$index" "$pid"
    fi
    mv "$data_dir/node.pid" "$data_dir/node.pid.stopped-$(date +%s)"
  done
}

validate_follower_name() {
  [[ "$1" =~ ^[a-zA-Z0-9][a-zA-Z0-9._-]{0,62}$ ]] || die "unsafe follower name: $1"
}

follower_dir() {
  validate_follower_name "$1"
  printf '%s/followers/%s\n' "$POA_ROOT" "$1"
}

verify_follower() {
  run_manifest_tool verify-follower --name "$1" >/dev/null
  local pubkey validator_keys
  pubkey="$(actual_pubkey "$(follower_dir "$1")")"
  validator_keys="$(node -e '
const m = JSON.parse(require("fs").readFileSync(process.argv[1], "utf8"));
process.stdout.write(m.nodes.map((node) => node.public_key).join("\n"));
' "$POA_ROOT/poa-devnet.json")"
  if grep -Fxq "$pubkey" <<< "$validator_keys"; then
    die "follower $1 is already a genesis validator; follower-first admission would be bypassed"
  fi
}

cmd_follower_init() {
  local name="${1:?follower-init requires NAME}"
  local data_dir pubkey ordinal
  run_manifest_tool verify-public
  data_dir="$(follower_dir "$name")"
  [ ! -e "$data_dir" ] || die "follower data dir already exists: $data_dir"
  mkdir -p "$data_dir"
  pubkey="$(actual_pubkey "$data_dir")"
  cp "$POA_ROOT/bundle/genesis.json" "$data_dir/genesis.json"
  ordinal="$(find "$POA_ROOT/followers" -mindepth 1 -maxdepth 1 -type d | wc -l | tr -d ' ')"
  ordinal=$((ordinal - 1))
  {
    printf 'POA_DEPLOYMENT_DOMAIN=%s\n' "$(manifest_field deployment_domain)"
    printf 'POA_DEPLOYMENT_ID=%s\n' "$(manifest_field deployment_id)"
    printf 'POA_FEDERATION_ID=%s\n' "$(manifest_field federation_id)"
    printf 'POA_FOLLOWER_NAME=%s\n' "$name"
    printf 'POA_FOLLOWER_DATA_DIR=%s\n' "$(cd "$data_dir" && pwd -P)"
    printf 'POA_FOLLOWER_HTTP_PORT=%s\n' "$((POA_HTTP_BASE + 100 + ordinal))"
    printf 'POA_FOLLOWER_GOSSIP_PORT=%s\n' "$((POA_GOSSIP_BASE + 100 + ordinal))"
    printf 'DREGG_REQUIRE_LEAN=1\n'
    printf 'DREGG_STRAND_ADMISSION_GATE=1\n'
    printf 'DREGG_ALLOW_UNVERIFIED_CONSENSUS=0\n'
    printf 'DREGG_STATUS_EXPOSE_COUNTS=0\n'
    printf 'DREGG_SEED_DEMO_LEASE=0\n'
  } > "$data_dir/operator.env"
  chmod 600 "$data_dir/operator.env"
  verify_follower "$name"
  printf 'created verifying follower %s\n' "$name"
  printf '  public key: %s\n' "$pubkey"
  printf '  next: %q follower-run %q HOST:%s BIND\n' "$0" "$name" "$POA_GOSSIP_BASE"
}

follower_join_args() {
  local name="$1"
  local bootstrap="$2"
  local bind="$3"
  local data_dir env_path
  assert_safe_consensus_environment
  verify_follower "$name"
  data_dir="$(follower_dir "$name")"
  env_path="$data_dir/operator.env"
  [ -f "$env_path" ] || die "missing restart-stable follower ports: $env_path"
  POA_DEPLOYMENT_DOMAIN=""
  POA_DEPLOYMENT_ID=""
  POA_FEDERATION_ID=""
  POA_FOLLOWER_NAME=""
  POA_FOLLOWER_DATA_DIR=""
  POA_FOLLOWER_HTTP_PORT=""
  POA_FOLLOWER_GOSSIP_PORT=""
  DREGG_REQUIRE_LEAN=""
  DREGG_STRAND_ADMISSION_GATE=""
  DREGG_ALLOW_UNVERIFIED_CONSENSUS=""
  DREGG_STATUS_EXPOSE_COUNTS=""
  DREGG_SEED_DEMO_LEASE=""
  local line key value
  while IFS= read -r line || [ -n "$line" ]; do
    [ -n "$line" ] || continue
    [[ "$line" == *=* ]] || die "malformed follower config line in $env_path"
    key="${line%%=*}"
    value="${line#*=}"
    case "$key" in
      POA_DEPLOYMENT_DOMAIN|POA_DEPLOYMENT_ID|POA_FEDERATION_ID|POA_FOLLOWER_NAME|\
      POA_FOLLOWER_DATA_DIR|POA_FOLLOWER_HTTP_PORT|POA_FOLLOWER_GOSSIP_PORT|\
      DREGG_REQUIRE_LEAN|DREGG_STRAND_ADMISSION_GATE|DREGG_ALLOW_UNVERIFIED_CONSENSUS|\
      DREGG_STATUS_EXPOSE_COUNTS|DREGG_SEED_DEMO_LEASE)
        printf -v "$key" '%s' "$value"
        ;;
      *) die "unknown follower config key $key in $env_path" ;;
    esac
  done < "$env_path"
  [ "$POA_DEPLOYMENT_DOMAIN" = "pathofangels.network/federation/v1" ] || die \
    "follower deployment domain mismatch"
  [ "$POA_DEPLOYMENT_ID" = "$(manifest_field deployment_id)" ] || die \
    "follower deployment id mismatch"
  [ "$POA_FEDERATION_ID" = "$(manifest_field federation_id)" ] || die \
    "follower federation id mismatch"
  [ "$POA_FOLLOWER_NAME" = "$name" ] || die "follower config name mismatch"
  [ "$POA_FOLLOWER_DATA_DIR" = "$(cd "$data_dir" && pwd -P)" ] || die \
    "follower data dir mismatch"
  [[ "$POA_FOLLOWER_HTTP_PORT" =~ ^[0-9]+$ ]] || die "invalid follower HTTP port"
  [[ "$POA_FOLLOWER_GOSSIP_PORT" =~ ^[0-9]+$ ]] || die "invalid follower gossip port"
  [ "$DREGG_REQUIRE_LEAN" = "1" ] || die "follower must require Lean"
  [ "$DREGG_STRAND_ADMISSION_GATE" = "1" ] || die "follower must enable strand admission"
  [ "$DREGG_ALLOW_UNVERIFIED_CONSENSUS" = "0" ] || die \
    "follower must forbid unverified consensus"
  [ "$DREGG_STATUS_EXPOSE_COUNTS" = "0" ] || die \
    "follower must keep private activity counts private"
  [ "$DREGG_SEED_DEMO_LEASE" = "0" ] || die "follower must not seed the generic demo lease"
  FOLLOWER_ARGS=(
    join
    --bootstrap "$bootstrap"
    --data-dir "$data_dir"
    --port "$POA_FOLLOWER_HTTP_PORT"
    --bind "$bind"
    --gossip-port "$POA_FOLLOWER_GOSSIP_PORT"
    --prove-turns
  )
}

cmd_follower_command() {
  local name="${1:?follower-command requires NAME}"
  local bootstrap="${2:?follower-command requires BOOTSTRAP host:port}"
  local bind="${3:-127.0.0.1}"
  follower_join_args "$name" "$bootstrap" "$bind"
  printf 'DREGG_REQUIRE_LEAN=1 DREGG_STRAND_ADMISSION_GATE=1 '
  printf 'DREGG_ALLOW_UNVERIFIED_CONSENSUS=0 DREGG_STATUS_EXPOSE_COUNTS=0 DREGG_SEED_DEMO_LEASE=0 '
  printf '%q ' "$BIN" "${FOLLOWER_ARGS[@]}"
  printf '\n'
}

cmd_follower_run() {
  local name="${1:?follower-run requires NAME}"
  local bootstrap="${2:?follower-run requires BOOTSTRAP host:port}"
  local bind="${3:-127.0.0.1}"
  follower_join_args "$name" "$bootstrap" "$bind"
  DREGG_REQUIRE_LEAN=1 DREGG_STRAND_ADMISSION_GATE=1 \
    DREGG_ALLOW_UNVERIFIED_CONSENSUS=0 DREGG_STATUS_EXPOSE_COUNTS=0 DREGG_SEED_DEMO_LEASE=0 \
    exec "$BIN" "${FOLLOWER_ARGS[@]}"
}

cmd_propose() {
  local name="${1:?propose requires follower NAME}"
  local validator_index="${2:-0}"
  local pubkey
  verify_follower "$name"
  pubkey="$(actual_pubkey "$(follower_dir "$name")")"
  "$BIN" propose-epoch-transition --add "$pubkey" --port "$(http_port "$validator_index")" --json
}

cmd_approve() {
  local proposal="${1:?approve requires PROPOSAL block id}"
  local validator_index="${2:-0}"
  cmd_verify
  "$BIN" approve-membership --proposal "$proposal" --port "$(http_port "$validator_index")" --json
}

case "${1:-}" in
  genesis) shift; cmd_genesis "$@" ;;
  verify) shift; cmd_verify "$@" ;;
  up) shift; cmd_up "$@" ;;
  health) shift; cmd_health "$@" ;;
  readiness) shift; cmd_readiness "$@" ;;
  down) shift; cmd_down "$@" ;;
  operator-command) shift; cmd_operator_command "$@" ;;
  follower-init) shift; cmd_follower_init "$@" ;;
  follower-command) shift; cmd_follower_command "$@" ;;
  follower-run) shift; cmd_follower_run "$@" ;;
  propose) shift; cmd_propose "$@" ;;
  approve) shift; cmd_approve "$@" ;;
  -h|--help|help) usage ;;
  *) usage >&2; exit 2 ;;
esac
