#!/bin/bash
# update-gated.sh — health-gated update + versioned rollback WRAPPER around
# ./update.sh, ported from the operated layer's deploy.sh (health_gate /
# record_release / rollback / --auto-revert) and re-grounded on the native
# deploy model (git-ffwd + rebuild-on-box + systemd; deploy/aws/update.sh).
#
# update.sh alone restarts services and hopes; this wrapper makes a bad deploy
# DETECTED and REVERTED:
#
#   1. snapshot the currently-running release (binaries + git rev) into
#      $RELEASES_DIR/<utc-stamp>/ (keeps last $KEEP);
#   2. run ./update.sh (all its knobs pass through: GATEWAY_ONLY, SKIP_SITE);
#   3. health-gate: poll the gateway /health (and every enabled dregg-node@N
#      member's port from /etc/dregg/node-N.env) until healthy or timeout;
#   4. on a failed gate, auto-revert: restore the snapshot binaries into
#      target/release, restart the services, re-gate — the box is back on the
#      release that worked. (The repo stays ffwd'd: the ROLLBACK IS BINARIES,
#      the source state is an operator decision — see the ROLLBACK NOTE below.)
#
# Usage:
#   ./update-gated.sh                 # snapshot -> update -> gate -> auto-revert
#   ./update-gated.sh health          # just run the health gate
#   ./update-gated.sh releases        # list snapshots
#   ./update-gated.sh rollback [S]    # revert to snapshot S (default: newest)
#
# Knobs (env):
#   RELEASES_DIR    where snapshots live       (default /opt/dregg-releases)
#   HEALTH_TIMEOUT  gate timeout, seconds      (default 120)
#   KEEP            snapshots retained         (default 5)
#   AUTO_REVERT     0 disables the auto-revert (default 1)
#   GATEWAY_URL     gateway health base        (default http://127.0.0.1:8420)
#
# ROLLBACK NOTE: a rollback restores the BINARIES that were running, while
# /opt/dregg (the repo) remains at the new rev — `git -C /opt/dregg log
# $(cat $RELEASES_DIR/<S>/GIT_REV)..HEAD` shows exactly what is deployed-but-
# reverted. State in /opt/dregg-data* is NEVER touched (same law as update.sh):
# if the bad deploy was a protocol-semantics bump that already rewrote durable
# state, binary rollback cannot undo that — that is the DISASTER-RECOVERY
# runbook's territory (docs/ops/DISASTER-RECOVERY.md), not this script's.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="${REPO_DIR:-/opt/dregg}"
RELEASES_DIR="${RELEASES_DIR:-/opt/dregg-releases}"
HEALTH_TIMEOUT="${HEALTH_TIMEOUT:-120}"
KEEP="${KEEP:-5}"
AUTO_REVERT="${AUTO_REVERT:-1}"
GATEWAY_URL="${GATEWAY_URL:-http://127.0.0.1:8420}"
BIN_DIR="$REPO_DIR/target/release"
BINARIES=(dregg-node dregg-discord-bot)

log() { echo "[update-gated] $*"; }
die() { echo "[update-gated] FATAL: $*" >&2; exit 1; }

# ── the health gate ─────────────────────────────────────────────────────────
# Healthy = the gateway answers /health 200, plus every ACTIVE dregg-node@N
# unit answers on its DREGG_PORT (read from /etc/dregg/node-N.env).
health_targets() {
  echo "gateway $GATEWAY_URL/health"
  local env_file name port
  for env_file in /etc/dregg/node-*.env; do
    [[ -e "$env_file" ]] || continue
    name="$(basename "$env_file" .env)"           # node-2
    systemctl is-active --quiet "dregg-node@${name#node-}" 2>/dev/null || continue
    port="$(sed -n 's/^DREGG_PORT=//p' "$env_file" | tail -1)"
    [[ -n "$port" ]] && echo "$name http://127.0.0.1:$port/health"
  done
}

health_gate() {
  local deadline=$((SECONDS + HEALTH_TIMEOUT)) all_ok name url
  log "health gate: up to ${HEALTH_TIMEOUT}s ..."
  while ((SECONDS < deadline)); do
    all_ok=1
    while read -r name url; do
      if ! curl -fsS -m 5 "$url" >/dev/null 2>&1; then
        all_ok=0
        log "  waiting: $name ($url) not healthy yet"
        break
      fi
    done < <(health_targets)
    if ((all_ok)); then
      log "health gate PASSED"
      return 0
    fi
    sleep 5
  done
  log "health gate FAILED after ${HEALTH_TIMEOUT}s; recent gateway log:"
  sudo journalctl -u dregg-gateway --no-pager -n 30 || true
  return 1
}

# ── snapshots ────────────────────────────────────────────────────────────────
record_release() {
  local stamp dir b
  stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  dir="$RELEASES_DIR/$stamp"
  sudo install -d "$dir"
  git -C "$REPO_DIR" rev-parse HEAD | sudo tee "$dir/GIT_REV" >/dev/null
  for b in "${BINARIES[@]}"; do
    [[ -x "$BIN_DIR/$b" ]] && sudo cp -p "$BIN_DIR/$b" "$dir/$b"
  done
  # prune to the newest $KEEP
  ls -1 "$RELEASES_DIR" | sort | head -n -"$KEEP" | while read -r old; do
    [[ -n "$old" ]] && sudo rm -rf "${RELEASES_DIR:?}/$old"
  done
  log "recorded release snapshot $stamp (rev $(cat "$dir/GIT_REV" | cut -c1-12))"
  echo "$stamp"
}

list_releases() {
  [[ -d "$RELEASES_DIR" ]] || { log "no releases recorded yet"; return 0; }
  local s
  for s in $(ls -1 "$RELEASES_DIR" | sort); do
    echo "$s  rev=$(cut -c1-12 "$RELEASES_DIR/$s/GIT_REV" 2>/dev/null || echo '?')  $(find "$RELEASES_DIR/$s" -maxdepth 1 -type f ! -name GIT_REV -exec basename {} \; | tr '\n' ' ')"
  done
}

restore_release() {
  local stamp="${1:-}" dir b restarted=0
  [[ -n "$stamp" ]] || stamp="$(ls -1 "$RELEASES_DIR" 2>/dev/null | sort | tail -1)"
  [[ -n "$stamp" ]] || die "no snapshot to roll back to"
  dir="$RELEASES_DIR/$stamp"
  [[ -d "$dir" ]] || die "no such snapshot: $stamp (see: $0 releases)"
  log "rolling back to snapshot $stamp (rev $(cut -c1-12 "$dir/GIT_REV" 2>/dev/null || echo '?'))"
  for b in "${BINARIES[@]}"; do
    if [[ -x "$dir/$b" ]]; then
      sudo cp -p "$dir/$b" "$BIN_DIR/$b"
      log "  restored $b"
    fi
  done
  sudo systemctl restart dregg-gateway; restarted=1
  systemctl is-enabled --quiet dregg-discord-bot 2>/dev/null && sudo systemctl restart dregg-discord-bot || true
  local env_file
  for env_file in /etc/dregg/node-*.env; do
    [[ -e "$env_file" ]] || continue
    local n; n="$(basename "$env_file" .env)"; n="${n#node-}"
    systemctl is-active --quiet "dregg-node@$n" 2>/dev/null && sudo systemctl restart "dregg-node@$n" || true
  done
  ((restarted)) && log "services restarted on snapshot $stamp"
  log "NOTE: /opt/dregg (the repo) is still at its current rev; the deployed"
  log "binaries are from $stamp. Diff: git -C $REPO_DIR log \$(cat $dir/GIT_REV)..HEAD"
}

# ── the gated update ─────────────────────────────────────────────────────────
gated_up() {
  local snap
  snap="$(record_release | tail -1)"
  log "running update.sh ..."
  if ! "$SCRIPT_DIR/update.sh"; then
    log "update.sh itself FAILED (build/merge error) — nothing was restarted beyond its progress point"
    if [[ "$AUTO_REVERT" == "1" ]]; then
      restore_release "$snap"
      health_gate || die "rolled back to $snap but the gate STILL fails — page a human"
      die "update failed; auto-reverted to $snap (box healthy on the old release)"
    fi
    die "update failed (AUTO_REVERT=0; box may be in a mixed state)"
  fi
  if health_gate; then
    log "deploy healthy on the new release"
    return 0
  fi
  if [[ "$AUTO_REVERT" == "1" ]]; then
    log "gate failed — AUTO-REVERTING to $snap"
    restore_release "$snap"
    health_gate || die "rolled back to $snap but the gate STILL fails — page a human"
    die "new release failed the health gate; auto-reverted to $snap (box healthy on the old release)"
  fi
  die "new release failed the health gate (AUTO_REVERT=0; left as-is)"
}

case "${1:-up}" in
  up)        gated_up ;;
  health)    health_gate ;;
  releases)  list_releases ;;
  rollback)  restore_release "${2:-}"; health_gate ;;
  *)         die "unknown subcommand: $1 (up | health | releases | rollback [stamp])" ;;
esac
