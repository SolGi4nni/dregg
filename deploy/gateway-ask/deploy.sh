#!/usr/bin/env bash
#
# gateway-ask deploy — cross-build locally, ship the binary, stage-then-atomic-swap
# on the box, with a paired cold-backup rollback.
#
# WHY THIS SHAPE. Two patterns are fused here:
#
#  1. CROSS-BUILD + SHIP (the small box never compiles Rust). The gateway-ask
#     binary pulls the whole verified-domain / app-framework closure; a 1–2 GB box
#     OOMs building it. So we `cargo zigbuild` the linux/amd64 binary on this
#     machine, rsync just the binary + config to the box, and run it there. The box
#     builds nothing.
#
#  2. STAGE → ATOMIC SWAP → PAIRED ROLLBACK (never a half-swapped live service).
#     Before the live binary is touched, the candidate is booted on an ALT
#     loopback port and health-probed TWICE (an idempotent restart must report the
#     same health — a candidate that flaps is rejected before it goes live). Only a
#     candidate that passes staging is promoted, and promotion is a SINGLE atomic
#     rename (`mv` on the same filesystem) over the live binary — the service never
#     sees a partially-written file. A cold backup of the previous binary is kept,
#     so rollback is the same atomic rename in reverse. This is the
#     stage/verify/atomic-swap/paired-rollback discipline distilled to one binary.
#
# All host/apex/domain values are ENVIRONMENT — there is no baked-in domain.
#
# Usage:
#   BOX_HOST=<public-dns-or-ip> SSH_KEY=~/.ssh/box.pem deploy.sh all
#
#   deploy.sh build            # cross-build the gateway-ask binary only
#   deploy.sh ship             # rsync the staged binary + config to the box
#   deploy.sh stage            # boot the candidate on the alt port, probe x2 (no swap)
#   deploy.sh swap             # cold-backup + atomic-swap the live binary + restart + gate
#   deploy.sh rollback         # atomic-swap back to the cold backup + restart + gate
#   deploy.sh releases         # list the cold backups kept on the box
#   deploy.sh all              # build + ship + stage + swap  (stage gates the swap)
#
#   deploy.sh swap --auto-rollback   # a failed post-swap gate rolls back by itself
#
set -euo pipefail

# ---- flags ------------------------------------------------------------------
AUTO_ROLLBACK=0
_args=()
for _a in "$@"; do
  case "$_a" in
    --auto-rollback) AUTO_ROLLBACK=1 ;;
    *) _args+=("$_a") ;;
  esac
done
set -- ${_args[@]+"${_args[@]}"}

# ---- config (override via env) ---------------------------------------------
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

# zigbuild pins a baseline glibc so the gnu binary runs on the box's libc. 2.31
# (Ubuntu 20.04 / Debian 11) is a safe floor debian:bookworm-slim satisfies.
TARGET="${TARGET:-x86_64-unknown-linux-gnu.2.31}"
TARGET_DIR="${TARGET%%.*}"

BOX_USER="${BOX_USER:-ubuntu}"
BOX_HOST="${BOX_HOST:-}"
SSH_KEY="${SSH_KEY:-$HOME/.ssh/gateway-ask.pem}"
REMOTE_DIR="${REMOTE_DIR:-/opt/gateway-ask}"      # binary + config live here
SERVICE="${SERVICE:-gateway-ask}"                 # the systemd unit name on the box

# Staging: the candidate is booted here before it goes live. STAGE_PORT must be a
# free loopback port distinct from the live service's port.
STAGE_PORT="${STAGE_PORT:-18799}"
HEALTH_TIMEOUT="${HEALTH_TIMEOUT:-60}"            # seconds a health probe polls
BACKUPS_KEEP="${BACKUPS_KEEP:-5}"                 # cold backups kept for rollback

STAGE_DIR="$HERE/.stage"

ssh_box() { ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new "$BOX_USER@$BOX_HOST" "$@"; }
require_box() { [ -n "$BOX_HOST" ] || { echo "ERROR: set BOX_HOST=<public-dns-or-ip>" >&2; exit 2; }; }

# ---- step 1: cross-build the gateway-ask binary -----------------------------
build() {
  command -v cargo-zigbuild >/dev/null || { echo "ERROR: cargo-zigbuild not installed (cargo install cargo-zigbuild; brew install zig)" >&2; exit 2; }
  rustup target add "$TARGET_DIR" >/dev/null 2>&1 || true
  echo "==> cross-building gateway-ask for $TARGET (the box compiles nothing)"
  ( cd "$HERE" && cargo zigbuild --locked --release --target "$TARGET" -p dregg-gateway-ask )

  echo "==> staging the binary + config into $STAGE_DIR"
  rm -rf "$STAGE_DIR"; mkdir -p "$STAGE_DIR"
  local out="$HERE/target/$TARGET_DIR/release/gateway-ask"
  [ -f "$out" ] || { echo "ERROR: expected binary $out not found" >&2; exit 1; }
  cp -v "$out" "$STAGE_DIR/gateway-ask"
  cp -v "$HERE/Caddyfile.on-demand-tls" "$STAGE_DIR/" 2>/dev/null || true
  [ -f "$HERE/.env" ] && cp "$HERE/.env" "$STAGE_DIR/.env" || cp "$HERE/.env.example" "$STAGE_DIR/.env"
  echo "==> staged:"; ls -la "$STAGE_DIR"
}

# ---- step 2: ship the staged binary + config (NOT over the live binary) -----
# Ships into $REMOTE_DIR/incoming so the live $REMOTE_DIR/gateway-ask is untouched
# until an explicit atomic swap. --delete is scoped to incoming/ only.
ship() {
  require_box
  [ -d "$STAGE_DIR" ] || { echo "ERROR: nothing staged; run 'build' first" >&2; exit 1; }
  echo "==> rsync $STAGE_DIR/ -> $BOX_USER@$BOX_HOST:$REMOTE_DIR/incoming/"
  ssh_box "sudo mkdir -p $REMOTE_DIR/incoming $REMOTE_DIR/backups && sudo chown -R $BOX_USER $REMOTE_DIR"
  rsync -avz --delete -e "ssh -i $SSH_KEY -o StrictHostKeyChecking=accept-new" \
    "$STAGE_DIR/" "$BOX_USER@$BOX_HOST:$REMOTE_DIR/incoming/"
}

# ---- step 3: STAGE — boot the candidate on the alt port, probe TWICE ---------
# The candidate never touches the live service. It is booted on $STAGE_PORT, the
# /healthz probe must pass, it is restarted, and the probe must pass AGAIN with the
# same answer — an idempotent restart that flaps is a bad candidate, rejected here.
stage() {
  require_box
  echo "==> staging the candidate on 127.0.0.1:$STAGE_PORT (probe x2; live service untouched)"
  ssh_box "REMOTE_DIR='$REMOTE_DIR' STAGE_PORT='$STAGE_PORT' HEALTH_TIMEOUT='$HEALTH_TIMEOUT' bash -s" <<'EOSH'
set -euo pipefail
cd "$REMOTE_DIR"
cand="incoming/gateway-ask"
[ -x "$cand" ] || { echo "ERROR: no staged candidate at $REMOTE_DIR/$cand (ship first)" >&2; exit 1; }

probe_once() {
  # Boot the candidate on the alt loopback port, poll /healthz, capture the answer, stop it.
  DREGG_GATEWAY_ASK_BIND="127.0.0.1:$STAGE_PORT" "./$cand" >/tmp/gateway-ask-stage.log 2>&1 &
  local pid=$!
  local deadline=$(( $(date +%s) + HEALTH_TIMEOUT )) body=""
  while :; do
    if body="$(curl -fsS --max-time 3 "http://127.0.0.1:$STAGE_PORT/healthz" 2>/dev/null)"; then
      break
    fi
    if ! kill -0 "$pid" 2>/dev/null; then echo "ERROR: candidate exited during staging" >&2; cat /tmp/gateway-ask-stage.log >&2; return 1; fi
    if [ "$(date +%s)" -ge "$deadline" ]; then echo "ERROR: candidate did not become healthy in ${HEALTH_TIMEOUT}s" >&2; kill "$pid" 2>/dev/null || true; return 1; fi
    sleep 1
  done
  kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true
  printf '%s' "$body"
}

echo "    probe 1…"; first="$(probe_once)"
echo "    probe 2 (idempotent restart)…"; second="$(probe_once)"
[ "$first" = "$second" ] || { echo "ERROR: staged health changed across restart ('$first' != '$second') — candidate flaps, rejected" >&2; exit 1; }
echo "==> staging PASSED (stable health: '$first') — candidate is promotable"
EOSH
}

# ---- step 4: SWAP — cold-backup + atomic rename over the live binary ---------
# The promotion is a single atomic rename (mv on the same filesystem), so the
# running service is never handed a half-written file. The previous binary is
# cold-backed-up first, so rollback is the same rename in reverse.
swap() {
  require_box
  echo "==> promoting the staged candidate (cold-backup + atomic swap + restart)"
  ssh_box "REMOTE_DIR='$REMOTE_DIR' SERVICE='$SERVICE' BACKUPS_KEEP='$BACKUPS_KEEP' bash -s" <<'EOSH'
set -euo pipefail
cd "$REMOTE_DIR"
cand="incoming/gateway-ask"
[ -x "$cand" ] || { echo "ERROR: no staged candidate (ship + stage first)" >&2; exit 1; }
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
# Cold-backup the currently-live binary (if any) BEFORE swapping.
if [ -f gateway-ask ]; then
  cp -a gateway-ask "backups/gateway-ask-$stamp"
  ( cd backups && sha256sum "gateway-ask-$stamp" > "gateway-ask-$stamp.sha256" )
  echo "    cold backup: backups/gateway-ask-$stamp ($(cd backups && cut -c1-16 gateway-ask-$stamp.sha256))"
fi
# ATOMIC SWAP: copy the candidate to a temp on the SAME filesystem, then rename
# over the live path. rename(2) is atomic — no reader sees a partial file.
cp -a "$cand" ".gateway-ask.incoming-$stamp"
mv -f ".gateway-ask.incoming-$stamp" gateway-ask
sync
# Prune old cold backups (keep newest $BACKUPS_KEEP).
ls -1 backups/gateway-ask-*[0-9]Z 2>/dev/null | sort | head -n "-$BACKUPS_KEEP" | while read -r old; do
  echo "    pruning old backup ${old#backups/}"; rm -f "$old" "$old.sha256"
done
echo "==> restarting $SERVICE"
sudo systemctl restart "$SERVICE"
EOSH
  if ! health_gate_live; then
    if [ "$AUTO_ROLLBACK" = 1 ]; then
      echo "==> --auto-rollback: the post-swap gate failed; rolling back" >&2
      rollback
    else
      echo "" >&2
      echo "    the new binary is live but UNHEALTHY. To revert to the previous binary:" >&2
      echo "        $0 rollback         # atomic-swap back to the newest cold backup" >&2
      echo "        $0 releases         # list the cold backups" >&2
    fi
    exit 1
  fi
}

# ---- the live health gate (post-swap) ---------------------------------------
health_gate_live() {
  require_box
  echo "==> health gate: $SERVICE /healthz (timeout ${HEALTH_TIMEOUT}s)"
  local deadline=$(( $(date +%s) + HEALTH_TIMEOUT ))
  local port="${LIVE_PORT:-8799}"
  while :; do
    if ssh_box "curl -fsS --max-time 3 http://127.0.0.1:$port/healthz" >/dev/null 2>&1; then
      echo "==> health gate PASSED — the live service answers"; return 0
    fi
    if [ "$(date +%s)" -ge "$deadline" ]; then break; fi
    echo "    …not healthy yet; re-polling in 5s"; sleep 5
  done
  echo "╳ HEALTH GATE FAILED after ${HEALTH_TIMEOUT}s" >&2
  ssh_box "sudo systemctl status $SERVICE --no-pager | tail -20; journalctl -u $SERVICE --no-pager -n 25" >&2 || true
  return 1
}

# ---- rollback: atomic-swap back to the newest (or named) cold backup ---------
rollback() {
  require_box
  local rel="${1:-}"
  echo "==> rollback: atomic-swap back to ${rel:-the newest cold backup} + restart"
  ssh_box "REMOTE_DIR='$REMOTE_DIR' SERVICE='$SERVICE' REL='$rel' bash -s" <<'EOSH'
set -euo pipefail
cd "$REMOTE_DIR"
[ -d backups ] || { echo "ERROR: no backups/ — nothing was ever recorded" >&2; exit 1; }
if [ -z "$REL" ]; then REL="$(ls -1 backups/gateway-ask-*[0-9]Z 2>/dev/null | sort | tail -1)"; REL="${REL#backups/}"; fi
[ -f "backups/$REL" ] || { echo "ERROR: backups/$REL not found. Recorded:" >&2; ls -1 backups >&2; exit 1; }
# Verify the backup's integrity against its recorded digest before promoting it.
if [ -f "backups/$REL.sha256" ]; then ( cd backups && sha256sum -c "$REL.sha256" >/dev/null ) || { echo "ERROR: backup $REL failed its checksum — refusing to install a corrupt rollback" >&2; exit 1; }; fi
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
cp -a "backups/$REL" ".gateway-ask.rollback-$stamp"
mv -f ".gateway-ask.rollback-$stamp" gateway-ask
sync
echo "    restored backups/$REL over the live binary"
sudo systemctl restart "$SERVICE"
EOSH
  health_gate_live || { echo "ERROR: the rolled-back binary ALSO fails its gate — check the box (disk/mem/unit/logs above)." >&2; exit 1; }
}

releases() {
  require_box
  ssh_box "cd $REMOTE_DIR 2>/dev/null && ls -1 backups/gateway-ask-*[0-9]Z 2>/dev/null | sort || echo '(no backups recorded yet)'"
}

case "${1:-all}" in
  build)     build ;;
  ship)      ship ;;
  stage)     stage ;;
  swap)      swap ;;
  rollback)  rollback "${2:-}" ;;
  releases)  releases ;;
  health)    health_gate_live ;;
  all)       build; ship; stage; swap ;;
  *) echo "usage: $0 {all|build|ship|stage|swap|rollback [backup]|releases|health} [--auto-rollback]" >&2; exit 2 ;;
esac
