#!/usr/bin/env bash
#
# keep-mac-awake.sh — keep a macOS machine awake and network-reachable so
# long-running CLI sessions (e.g. Claude Code) are not killed when the lid
# closes, the screen locks, or the machine tries to idle-sleep — and so you
# can keep driving those sessions from outside the house.
#
# This is a convenience wrapper around macOS' own `caffeinate` and `pmset`.
# Nothing here is dregg-specific; it just stops the box the sessions run on
# from going to sleep or dropping its network.
#
# Quick start (run ON THE MAC, not in a remote container):
#
#   ./scripts/keep-mac-awake.sh start        # keep awake until you stop it
#   ./scripts/keep-mac-awake.sh start -- claude   # keep awake only while `claude` runs
#   ./scripts/keep-mac-awake.sh status       # what's keeping it awake right now
#   ./scripts/keep-mac-awake.sh stop         # release the wake lock
#
# Persist across reboots / logins (installs a LaunchAgent):
#
#   ./scripts/keep-mac-awake.sh install
#   ./scripts/keep-mac-awake.sh uninstall
#
# Stronger, system-level power settings (needs sudo; survives lid close):
#
#   ./scripts/keep-mac-awake.sh harden       # snapshot + disable sleep, keep net alive
#   ./scripts/keep-mac-awake.sh restore      # undo `harden` from the snapshot
#
set -euo pipefail

SCRIPT_NAME="$(basename "$0")"
LABEL="systems.rbg.dregg.keepawake"
PLIST="$HOME/Library/LaunchAgents/${LABEL}.plist"
STATE_DIR="${XDG_STATE_HOME:-$HOME/.local/state}/keep-mac-awake"
PID_FILE="$STATE_DIR/caffeinate.pid"
PMSET_SNAPSHOT="$STATE_DIR/pmset-before-harden.txt"

# caffeinate assertion flags:
#   -d  prevent the DISPLAY from sleeping
#   -i  prevent the system from IDLE sleeping
#   -m  prevent the DISK from idle sleeping
#   -s  prevent the SYSTEM from sleeping (honored on AC power)
#   -u  declare the USER is active (also wakes/keeps the display on)
CAFFEINATE_FLAGS="-dimsu"

log()  { printf '\033[1;36m[keep-awake]\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33m[keep-awake]\033[0m %s\n' "$*" >&2; }
die()  { printf '\033[1;31m[keep-awake]\033[0m %s\n' "$*" >&2; exit 1; }

require_macos() {
  [ "$(uname -s)" = "Darwin" ] || die "This script only does anything on macOS (found $(uname -s)).
Run it on the Mac that hosts your sessions, not inside a remote/Linux container."
}

usage() {
  sed -n '2,28p' "$0" | sed 's/^# \{0,1\}//'
  cat <<EOF

Commands:
  start [-- CMD ...]   Take a wake lock. With a trailing '-- CMD', stay awake
                       only while CMD runs (e.g. 'start -- claude'); otherwise
                       stay awake in the background until 'stop'.
  stop                 Release the background wake lock started by 'start'.
  status               Show what is currently asserting wakefulness + power/net settings.
  install              Install a LaunchAgent so the wake lock is re-taken at every login.
  uninstall            Remove the LaunchAgent.
  harden               (sudo) Snapshot power settings, then disable sleep even with the
                       lid closed and keep the network reachable while "asleep".
  restore              (sudo) Restore the power settings snapshotted by 'harden'.
  remote-help          Print how to reach these sessions from outside (SSH + tmux).
  help                 This message.
EOF
}

# ---------------------------------------------------------------------------

cmd_start() {
  require_macos
  mkdir -p "$STATE_DIR"

  # Everything after a literal `--` is a command to wrap.
  local wrap=()
  local saw_sep=0
  for arg in "$@"; do
    if [ "$saw_sep" = 1 ]; then
      wrap+=("$arg")
    elif [ "$arg" = "--" ]; then
      saw_sep=1
    fi
  done

  if [ "${#wrap[@]}" -gt 0 ]; then
    log "Staying awake only while: ${wrap[*]}"
    log "(caffeinate exits automatically when that command finishes)"
    exec caffeinate "$CAFFEINATE_FLAGS" "${wrap[@]}"
  fi

  # Background/indefinite mode. Refuse to stack duplicates.
  if [ -f "$PID_FILE" ] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null; then
    log "Already awake (caffeinate pid $(cat "$PID_FILE")). Nothing to do."
    return 0
  fi

  caffeinate "$CAFFEINATE_FLAGS" &
  local pid=$!
  echo "$pid" > "$PID_FILE"
  disown "$pid" 2>/dev/null || true
  log "Wake lock held by caffeinate pid $pid. The Mac will not idle/display/disk/system sleep."
  log "Release it later with:  $SCRIPT_NAME stop"
  warn "Note: with the LID CLOSED on battery, macOS may still sleep. Use 'harden' for that."
}

cmd_stop() {
  require_macos
  if [ -f "$PID_FILE" ]; then
    local pid; pid="$(cat "$PID_FILE")"
    if kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
      log "Released wake lock (killed caffeinate pid $pid)."
    else
      log "No live wake lock for recorded pid $pid."
    fi
    rm -f "$PID_FILE"
  else
    log "No background wake lock recorded."
  fi
  # Belt and suspenders: reap any strays we may have spawned.
  pkill -x caffeinate 2>/dev/null && log "Also cleared stray caffeinate processes." || true
}

cmd_status() {
  require_macos
  log "Active power assertions (who is keeping this Mac awake):"
  pmset -g assertions | sed 's/^/    /'
  echo
  log "Sleep / wake power settings:"
  pmset -g custom | sed 's/^/    /'
  echo
  if [ -f "$PID_FILE" ] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null; then
    log "This script holds a background wake lock (caffeinate pid $(cat "$PID_FILE"))."
  else
    log "This script is NOT holding a background wake lock right now."
  fi
  if [ -f "$PLIST" ]; then
    log "LaunchAgent installed at $PLIST (wake lock re-taken at each login)."
  fi
}

cmd_install() {
  require_macos
  mkdir -p "$(dirname "$PLIST")"
  local self; self="$(cd "$(dirname "$0")" && pwd)/$(basename "$0")"
  cat > "$PLIST" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"
  "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>Label</key>
    <string>${LABEL}</string>
    <key>ProgramArguments</key>
    <array>
        <string>/usr/bin/caffeinate</string>
        <string>${CAFFEINATE_FLAGS}</string>
    </array>
    <key>RunAtLoad</key>
    <true/>
    <key>KeepAlive</key>
    <true/>
</dict>
</plist>
EOF
  # bootout is a no-op if not loaded; ignore its failure.
  launchctl bootout "gui/$(id -u)/${LABEL}" 2>/dev/null || true
  launchctl bootstrap "gui/$(id -u)" "$PLIST"
  log "Installed LaunchAgent → $PLIST"
  log "A caffeinate wake lock is now taken at every login and restarted if it dies."
  log "Remove it with:  $SCRIPT_NAME uninstall"
}

cmd_uninstall() {
  require_macos
  launchctl bootout "gui/$(id -u)/${LABEL}" 2>/dev/null || true
  rm -f "$PLIST"
  log "Removed LaunchAgent (${LABEL})."
}

cmd_harden() {
  require_macos
  [ "$(id -u)" = "0" ] || exec sudo "$0" harden
  mkdir -p "$STATE_DIR"
  # Snapshot current settings so 'restore' can put them back verbatim.
  pmset -g custom > "$PMSET_SNAPSHOT"
  chown "$(logname 2>/dev/null || echo "$SUDO_USER")" "$PMSET_SNAPSHOT" 2>/dev/null || true
  log "Snapshotted current power settings → $PMSET_SNAPSHOT"

  # Keep the machine awake even with the lid closed.
  pmset -a disablesleep 1
  # Never idle-sleep the system or disks (displaysleep is cosmetic; leave 10 min).
  pmset -c sleep 0 disksleep 0
  # Stay reachable over the network: wake on magic packet + keep TCP alive.
  pmset -a womp 1 2>/dev/null || warn "womp (wake-on-LAN) not settable on this hardware; skipping."
  pmset -a tcpkeepalive 1 2>/dev/null || true

  log "Hardened: sleep disabled (incl. lid closed), network kept reachable."
  warn "This WILL drain the battery faster and keeps the CPU/network live. Undo with:  $SCRIPT_NAME restore"
}

cmd_restore() {
  require_macos
  [ "$(id -u)" = "0" ] || exec sudo "$0" restore
  # Re-enable normal sleep behavior.
  pmset -a disablesleep 0
  if [ -f "$PMSET_SNAPSHOT" ]; then
    log "A snapshot of your prior settings is here — reapply any values you care about:"
    sed 's/^/    /' "$PMSET_SNAPSHOT"
  else
    warn "No snapshot found at $PMSET_SNAPSHOT; only re-enabled sleep (disablesleep 0)."
  fi
  log "Restored: normal sleep re-enabled."
}

cmd_remote_help() {
  cat <<'EOF'
Driving these sessions from OUTSIDE the house
=============================================

Keeping the Mac awake solves half the problem — you also need a way in, and
sessions that survive your terminal disconnecting. Recommended setup:

1) Run each Claude Code session inside tmux so it keeps running even if your
   SSH connection drops:

       tmux new -s work        # start / name a session
       claude                  # run your session inside it
       # detach any time with:  Ctrl-b  then  d
       tmux attach -t work     # re-attach later, from anywhere

2) Turn on Remote Login (SSH) on the Mac:
       System Settings → General → Sharing → Remote Login  (toggle on)
   or from a terminal:
       sudo systemsetup -setremotelogin on

3) From outside, reach the Mac over SSH (via your router's port-forward, a VPN,
   or a tunnel like Tailscale / `cloudflared` — a tunnel avoids opening ports):
       ssh you@your-mac
       tmux attach -t work

With the Mac kept awake (this script) + tmux + SSH, a dropped Wi-Fi or a closed
laptop lid no longer kills the work: you just reconnect and re-attach.
EOF
}

# ---------------------------------------------------------------------------

main() {
  local sub="${1:-help}"
  [ "$#" -gt 0 ] && shift || true
  case "$sub" in
    start)        cmd_start "$@" ;;
    stop)         cmd_stop ;;
    status)       cmd_status ;;
    install)      cmd_install ;;
    uninstall)    cmd_uninstall ;;
    harden)       cmd_harden ;;
    restore)      cmd_restore ;;
    remote-help)  cmd_remote_help ;;
    help|-h|--help) usage ;;
    *) usage; die "Unknown command: $sub" ;;
  esac
}

main "$@"
