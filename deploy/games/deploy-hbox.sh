#!/bin/bash
# deploy-hbox.sh — one-command deploy of the dregg GAMES stack onto hbox.
#
# Real topology (docs/ops/OPS-RUNBOOK.md): DNS -> AWS GATEWAY (public, runs its OWN
# Caddy for *.dregg.fg-goose.online) -> TAILSCALE -> hbox (tailnet node hbox-dregg,
# 100.95.240.73). Caddy lives on the GATEWAY, not hbox. THIS SCRIPT RUNS ON hbox and
# handles ONLY the hbox side: the 2 binaries + the 2 user units. The gateway Caddy
# block is a SEPARATE step (`./deploy-hbox.sh gateway`, run ON THE GATEWAY).
#
# The automated hbox flow: BUILD (dreggnet-web-server + dregg-discord-bot) -> SNAPSHOT
# (rollback point) -> INSTALL (user systemd units) -> RELOAD -> HEALTH-CHECK (/health).
# A failed health gate AUTO-REVERTS to the snapshot. This turns the go-live into a
# small, safe flip, NOT a new build. Caddy on hbox is SKIPPED by default (SKIP_CADDY=1).
#
# Grounded in the existing deploy infra (deploy/aws/update.sh + update-gated.sh):
# the build->install->reload->health->rollback shape is theirs, re-homed onto
# hbox USER units (deploy/hbox/RUNBOOK.md discipline) and the standalone games
# web server (docs/DEPLOY-PLAN.md Phase 0).
#
# ⚠ WHAT THIS SCRIPT DOES NOT DO (ember-gated flips — printed as MANUAL banners,
# never executed):
#   - (0) add the AWS gateway to the TAILNET (the private channel to hbox-dregg) —
#     the currently-missing prerequisite; without it the gateway cannot reach :8790;
#   - place the Discord token / secrets (~/.config/dregg/games.env, chmod 600);
#   - STOP THE OLD BOT FIRST — the GRAVITON bot (deploy/aws/dregg-discord-bot.service)
#     holds the token; two bots on one token double-fire every command;
#   - point DNS games.dregg.fg-goose.online -> the gateway;
#   - add the games site block to the gateway Caddy + reload it (`gateway` step);
#   - flip the demo public (the go-live decision).
#
# Usage (on hbox unless noted):
#   ./deploy-hbox.sh                 # build -> install -> reload -> health (+ auto-revert)
#   ./deploy-hbox.sh --dry-run       # print every step; NO side effects (safe anywhere)
#   ./deploy-hbox.sh gateway         # ON THE GATEWAY: install the games Caddy block + reload
#   ./deploy-hbox.sh health          # just run the health gate
#   ./deploy-hbox.sh releases        # list rollback snapshots
#   ./deploy-hbox.sh rollback [S]    # revert binaries to snapshot S (default newest) + restart
#
# Knobs (env):
#   GAMES_REPO_DIR   repo checkout on hbox        (default $HOME/dev/breadstuffs)
#   GAMES_ENV        the stack env file           (default $HOME/.config/dregg/games.env)
#   STATE_DIR        durable db + snapshots        (default $HOME/.local/state/dregg-games)
#   USER_UNIT_DIR    user systemd unit dir         (default $HOME/.config/systemd/user)
#   HEALTH_URL       web server liveness probe     (default http://100.95.240.73:8790/health)
#                    (the tailnet iface — the server binds hbox-dregg, not localhost)
#   HEALTH_TIMEOUT   gate timeout, seconds         (default 120)
#   KEEP             snapshots retained            (default 5)
#   AUTO_REVERT      0 disables the auto-revert    (default 1)
#   CADDY_FILE       GATEWAY Caddy config (gateway step only)  (default /etc/caddy/Caddyfile)
#   GAMES_BLOCK      the games site block to add to gateway Caddy (default caddy/Caddyfile.games)
#   SKIP_CADDY       DEFAULT 1: no Caddy on hbox (Caddy lives on the gateway). Set 0
#                    only for a legacy all-on-one-box test — NOT the real topology.
#   SKIP_BOT         1 skips the bot leg (web demo only)
set -euo pipefail

# ── flags + config ───────────────────────────────────────────────────────────
DRY_RUN=0
ARGS=()
for a in "$@"; do
  case "$a" in
    --dry-run) DRY_RUN=1 ;;
    *) ARGS+=("$a") ;;
  esac
done
set -- "${ARGS[@]:-up}"

GAMES_REPO_DIR="${GAMES_REPO_DIR:-$HOME/dev/breadstuffs}"
GAMES_ENV="${GAMES_ENV:-$HOME/.config/dregg/games.env}"
STATE_DIR="${STATE_DIR:-$HOME/.local/state/dregg-games}"
USER_UNIT_DIR="${USER_UNIT_DIR:-$HOME/.config/systemd/user}"
# The web server binds the Tailscale iface (hbox-dregg 100.95.240.73:8790), NOT
# localhost — so the on-hbox health probe must hit the tailnet IP, not 127.0.0.1.
HEALTH_URL="${HEALTH_URL:-http://100.95.240.73:8790/health}"
HEALTH_TIMEOUT="${HEALTH_TIMEOUT:-120}"
KEEP="${KEEP:-5}"
AUTO_REVERT="${AUTO_REVERT:-1}"
# CADDY_FILE / GAMES_BLOCK are used ONLY by the `gateway` subcommand (run on the gateway).
CADDY_FILE="${CADDY_FILE:-/etc/caddy/Caddyfile}"
GAMES_BLOCK="${GAMES_BLOCK:-}"
# Caddy on hbox is OFF by default — the real topology puts Caddy on the AWS gateway.
SKIP_CADDY="${SKIP_CADDY:-1}"
SKIP_BOT="${SKIP_BOT:-0}"

RELEASES_DIR="$STATE_DIR/releases"
SRC_DIR="$GAMES_REPO_DIR/deploy/games"
BINARIES=(dreggnet-web-server)
UNITS=(dregg-web-games.service)
if [[ "$SKIP_BOT" != "1" ]]; then
  BINARIES+=(dregg-discord-bot)
  UNITS+=(dregg-games-bot.service)
fi

# Per-binary source path. dreggnet-web is a ROOT-workspace member (built into the
# root target/); dregg-discord-bot is a SEPARATE workspace (excluded from root —
# sqlx/libsqlite3-sys links-conflict; discord-bot/Cargo.toml), so it builds into
# ITS OWN target/. The two live in different dirs — never assume one BIN_DIR.
bin_src() {
  case "$1" in
    dreggnet-web-server) echo "$GAMES_REPO_DIR/target/release/dreggnet-web-server" ;;
    dregg-discord-bot)   echo "$GAMES_REPO_DIR/discord-bot/target/release/dregg-discord-bot" ;;
    *) die "unknown binary: $1" ;;
  esac
}

log()  { echo "[deploy-games] $*"; }
warn() { echo "[deploy-games] ⚠ $*" >&2; }
die()  { echo "[deploy-games] FATAL: $*" >&2; exit 1; }

# run(): the side-effect wrapper. In --dry-run it PRINTS the command and returns 0;
# otherwise it executes it. Every mutating command goes through run().
run() {
  if [[ "$DRY_RUN" == "1" ]]; then
    echo "    [dry-run] $*"
    return 0
  fi
  "$@"
}

# gated(): a step the script REFUSES to automate — it prints the manual banner and
# does nothing, in both dry-run and real mode.
gated() {
  echo "    ── EMBER-GATED (manual) ── $*"
}

# ── the ember-gated banner (printed at the top of every real run) ────────────
gated_banner() {
  cat <<'BANNER'
[deploy-games] ══════════════════════════════════════════════════════════════
[deploy-games]  EMBER-GATED FLIPS this script does NOT perform (do them first /
[deploy-games]  around the run — see deploy/games/RUNBOOK.md):
[deploy-games]    (0) add the AWS GATEWAY to the TAILNET (reach hbox-dregg :8790)
[deploy-games]    (b) place ~/.config/dregg/games.env (tokens) + chmod 600
[deploy-games]    (c) STOP THE OLD BOT FIRST — the GRAVITON bot holds the token
[deploy-games]    (a) DNS: games.dregg.fg-goose.online -> the gateway
[deploy-games]    (caddy) ON THE GATEWAY: ./deploy-hbox.sh gateway (add block + reload)
[deploy-games]    (go-live) flip the demo public
[deploy-games] ══════════════════════════════════════════════════════════════
BANNER
}

# ── preflight ────────────────────────────────────────────────────────────────
preflight() {
  log "preflight"
  [[ -d "$GAMES_REPO_DIR" ]] || die "repo not found: $GAMES_REPO_DIR (set GAMES_REPO_DIR)"
  [[ -d "$SRC_DIR" ]] || die "deploy/games not found under $GAMES_REPO_DIR — is this the right checkout / branch?"
  if [[ ! -f "$GAMES_ENV" ]]; then
    warn "env file $GAMES_ENV MISSING — ember must place it (tokens + bind + DATABASE_URL)."
    gated "place $GAMES_ENV from deploy/games/.env.example, then chmod 600"
    [[ "$DRY_RUN" == "1" ]] || die "cannot start units without $GAMES_ENV; place it and re-run"
  fi
  run mkdir -p "$STATE_DIR" "$USER_UNIT_DIR" "$RELEASES_DIR"
}

# ── build ────────────────────────────────────────────────────────────────────
build() {
  log "build (cargo --release): ${BINARIES[*]}"
  # web server: root workspace member.
  run bash -c "cd '$GAMES_REPO_DIR' && cargo build --release -p dreggnet-web --bin dreggnet-web-server"
  # bot: its OWN workspace — build from within discord-bot/ (NOT `-p` from root,
  # which fails: it is `exclude`d from the root workspace).
  if [[ "$SKIP_BOT" != "1" ]]; then
    run bash -c "cd '$GAMES_REPO_DIR/discord-bot' && cargo build --release --bin dregg-discord-bot"
  fi
}

# ── snapshots (rollback point) ───────────────────────────────────────────────
record_release() {
  local stamp dir b src
  stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  dir="$RELEASES_DIR/$stamp"
  run mkdir -p "$dir"
  if [[ "$DRY_RUN" != "1" ]]; then
    git -C "$GAMES_REPO_DIR" rev-parse HEAD > "$dir/GIT_REV" 2>/dev/null || echo "unknown" > "$dir/GIT_REV"
  fi
  for b in "${BINARIES[@]}"; do
    src="$(bin_src "$b")"
    [[ -x "$src" ]] && run cp -p "$src" "$dir/$b"
  done
  # prune to newest $KEEP
  if [[ "$DRY_RUN" != "1" ]]; then
    ls -1 "$RELEASES_DIR" 2>/dev/null | sort | head -n -"$KEEP" | while read -r old; do
      [[ -n "$old" ]] && rm -rf "${RELEASES_DIR:?}/$old"
    done
  fi
  log "snapshot recorded: $stamp"
  echo "$stamp"
}

list_releases() {
  [[ -d "$RELEASES_DIR" ]] || { log "no snapshots yet"; return 0; }
  local s
  for s in $(ls -1 "$RELEASES_DIR" | sort); do
    echo "  $s  rev=$(cut -c1-12 "$RELEASES_DIR/$s/GIT_REV" 2>/dev/null || echo '?')"
  done
}

restore_release() {
  local stamp="${1:-}" dir b
  [[ -n "$stamp" ]] || stamp="$(ls -1 "$RELEASES_DIR" 2>/dev/null | sort | tail -1)"
  [[ -n "$stamp" ]] || die "no snapshot to roll back to"
  dir="$RELEASES_DIR/$stamp"
  [[ -d "$dir" || "$DRY_RUN" == "1" ]] || die "no such snapshot: $stamp"
  log "rolling back binaries to snapshot $stamp"
  for b in "${BINARIES[@]}"; do
    [[ -x "$dir/$b" || "$DRY_RUN" == "1" ]] && run cp -p "$dir/$b" "$(bin_src "$b")"
  done
  restart_units
  log "NOTE: the repo stays at its current rev; only the BINARIES reverted to $stamp."
}

# ── install units + caddy ────────────────────────────────────────────────────
install_units() {
  log "install user systemd units: ${UNITS[*]}"
  local u
  for u in "${UNITS[@]}"; do
    run cp "$SRC_DIR/$u" "$USER_UNIT_DIR/$u"
  done
  run systemctl --user daemon-reload
  # survive logout so the user units keep running (deploy/hbox/RUNBOOK.md).
  run loginctl enable-linger "$USER"
  for u in "${UNITS[@]}"; do
    run systemctl --user enable "$u"
  done
}

install_caddy() {
  # Default topology: Caddy lives on the AWS GATEWAY, NOT hbox. SKIP_CADDY defaults 1,
  # so this hbox leg is a no-op — the games site block is installed by the separate
  # `gateway` subcommand (run ON THE GATEWAY, gateway_install below).
  if [[ "$SKIP_CADDY" == "1" ]]; then
    log "SKIP_CADDY=1 (default) — no Caddy on hbox; the gateway holds Caddy."
    log "  add the games block ON THE GATEWAY: ./deploy-hbox.sh gateway (see RUNBOOK step d)"
    return 0
  fi
  # SKIP_CADDY=0 is a LEGACY all-on-one-box path (Caddy on hbox); NOT the real topology.
  log "install Caddyfile -> $CADDY_FILE (LEGACY on-hbox Caddy; needs sudo + hbox :80/:443 open)"
  run bash -c "caddy validate --adapter caddyfile --config '$SRC_DIR/caddy/Caddyfile.games'"
  run sudo cp "$SRC_DIR/caddy/Caddyfile.games" "$CADDY_FILE"
  run sudo systemctl reload caddy
  warn "SKIP_CADDY=0 puts Caddy on hbox — NOT the gateway<->Tailscale<->hbox topology."
}

# gateway_install(): the SEPARATE gateway step. Run this ON THE AWS GATEWAY (not hbox),
# AFTER the gateway is on the tailnet (step 0). It validates the games site block,
# appends it to the gateway's Caddy config, and reloads caddy THERE. The block reverse-
# proxies over Tailscale to hbox-dregg (100.95.240.73:8790); nothing is installed on hbox.
gateway_install() {
  local block dst
  block="${GAMES_BLOCK:-$SRC_DIR/caddy/Caddyfile.games}"
  dst="$CADDY_FILE"
  log "GATEWAY STEP — add the games site block to the gateway Caddy ($dst) + reload"
  [[ -f "$block" ]] || die "games block not found: $block (set GAMES_BLOCK, or run from a repo checkout)"
  # Validate the block standalone first (a self-contained site block adapts on its own).
  run bash -c "caddy validate --adapter caddyfile --config '$block'"
  gated "the gateway must be ON THE TAILNET (step 0) so it can reach 100.95.240.73:8790"
  gated "APPEND the block to $dst (next to the devnet.dregg.fg-goose.online block):"
  gated "    sudo sh -c 'cat \"$block\" >> \"$dst\"'   # or paste it in by hand"
  gated "then validate the WHOLE merged config + reload:"
  gated "    sudo caddy validate --adapter caddyfile --config \"$dst\""
  gated "    sudo systemctl reload caddy"
  gated "DNS games.dregg.fg-goose.online -> the gateway must resolve for Let's Encrypt to issue"
  log "block validated; the append+reload are ember-gated manual steps above."
}

restart_units() {
  local u
  for u in "${UNITS[@]}"; do
    run systemctl --user restart "$u"
  done
}

start_units() {
  local u
  for u in "${UNITS[@]}"; do
    run systemctl --user enable --now "$u"
  done
}

# ── health gate (mirrors deploy/aws/update-gated.sh) ─────────────────────────
health_gate() {
  if [[ "$DRY_RUN" == "1" ]]; then
    echo "    [dry-run] curl -fsS -m 5 $HEALTH_URL  (poll up to ${HEALTH_TIMEOUT}s; expect 200 {\"status\":\"ok\"})"
    return 0
  fi
  local deadline=$((SECONDS + HEALTH_TIMEOUT))
  log "health gate: $HEALTH_URL (up to ${HEALTH_TIMEOUT}s)"
  while ((SECONDS < deadline)); do
    if curl -fsS -m 5 "$HEALTH_URL" >/dev/null 2>&1; then
      log "health gate PASSED"
      return 0
    fi
    log "  waiting for $HEALTH_URL ..."
    sleep 5
  done
  log "health gate FAILED after ${HEALTH_TIMEOUT}s; recent log:"
  journalctl --user -u dregg-web-games --no-pager -n 30 2>/dev/null || true
  return 1
}

# ── the gated deploy ─────────────────────────────────────────────────────────
deploy_up() {
  gated_banner
  preflight
  local snap
  snap="$(record_release | tail -1)"
  build
  install_units
  install_caddy
  start_units
  if health_gate; then
    log "games stack HEALTHY on the new release ($snap was the rollback point)"
    log "smoke test next (deploy/games/RUNBOOK.md step e): open the URL, play a game, /descent in Discord."
    return 0
  fi
  if [[ "$AUTO_REVERT" == "1" ]]; then
    warn "health gate failed — AUTO-REVERTING to $snap"
    restore_release "$snap"
    health_gate || die "rolled back to $snap but the gate STILL fails — page ember"
    die "new release failed the health gate; auto-reverted to $snap"
  fi
  die "new release failed the health gate (AUTO_REVERT=0; left as-is)"
}

case "${1:-up}" in
  up)        deploy_up ;;
  gateway)   gateway_install ;;
  health)    health_gate ;;
  releases)  list_releases ;;
  rollback)  restore_release "${2:-}"; health_gate ;;
  *)         die "unknown subcommand: $1 (up | gateway | health | releases | rollback [stamp] | --dry-run)" ;;
esac
