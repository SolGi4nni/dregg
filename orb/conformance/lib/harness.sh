#!/usr/bin/env bash
# Shared conformance harness helpers: swarm-safe serve launch, readiness wait,
# and two-layer reap. SOURCE this from a runner (do NOT execute it):
#
#   HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
#   source "$HERE/../lib/harness.sh"   # adjust ../ to reach conformance/lib
#
# The hazards these primitives close — all learned on a shared, concurrently
# rebuilt worktree with co-tenant processes:
#
#   * Driving a SIBLING's serve. If a runner blindly launches on a port another
#     lane already owns, its own bind fails silently and it drives the wrong
#     process — a false, contaminated result. harness_require_free refuses up
#     front so a runner only ever drives the serve it launched.
#   * Orphaned serves. The serve reparents to init if the launching subshell
#     exits first, so a PID-only kill can leave a daemonized serve on the port.
#     harness_reap sweeps BOTH the tracked PID and a port-EXACT command-line
#     match, escalating TERM -> KILL until the match is gone.
#   * Killing a co-tenant. A global `pkill -f dataplane` kills every sibling and
#     co-tenant serve on the box. Every sweep here is keyed to the exact
#     `--bind HOST:PORT` (or an explicit caller pattern), so it can only ever
#     hit THIS runner's serve.
#   * setsid detaching the child out of reap reach. Never used here; a launched
#     serve is a plain background job whose PID the runner holds.

# Idempotent: safe to source more than once (a runner and a helper it calls).
[ -n "${_HARNESS_SH_LOADED:-}" ] && return 0
_HARNESS_SH_LOADED=1

_HARNESS_PIDS=()
_HARNESS_PATTERNS=()

# harness_tcp_open HOST PORT [tries]
#   Return 0 as soon as a TCP connect to HOST:PORT succeeds, else 1 after `tries`
#   attempts (0.1s apart). Pure bash /dev/tcp; no external client needed.
harness_tcp_open() {
  local host="$1" port="$2" tries="${3:-1}" i
  for ((i = 0; i < tries; i++)); do
    if (exec 3<>"/dev/tcp/$host/$port") 2>/dev/null; then
      exec 3>&- 3<&- 2>/dev/null || true
      return 0
    fi
    sleep 0.1
  done
  return 1
}

# harness_require_free HOST PORT
#   Return 0 if nothing is listening on HOST:PORT; 1 (with a diagnostic) if the
#   port is already taken. A runner MUST abort on nonzero rather than squat on a
#   port a sibling owns — otherwise it would drive the sibling's serve.
harness_require_free() {
  local host="$1" port="$2"
  if harness_tcp_open "$host" "$port" 1; then
    echo "HARNESS ERROR: $host:$port already in use (a sibling serve?)." >&2
    echo "  pick a free port so this runner owns its own listener." >&2
    return 1
  fi
  return 0
}

# harness_track PID [PATTERN]
#   Register a launched PID (and optionally a port-exact command-line pattern for
#   pgrep/pkill -f) for harness_reap to clean up. Call once per launched serve.
#   The PATTERN should be specific enough to match ONLY this runner's serve —
#   e.g. "release/dataplane --bind 127.0.0.1:18962 " (trailing space matters so
#   :1896 does not also match :18962).
harness_track() {
  local pid="${1:-}" pattern="${2:-}"
  [ -n "$pid" ] && _HARNESS_PIDS+=("$pid")
  [ -n "$pattern" ] && _HARNESS_PATTERNS+=("$pattern")
  return 0
}

# harness_reap
#   Two-layer, swarm-safe teardown of everything harness_track registered: kill
#   tracked PIDs (TERM, wait up to 2s, then KILL), then sweep any process still
#   matching a tracked port-exact pattern (TERM, loop, KILL) to catch a serve
#   that reparented to init. Idempotent; safe as an EXIT trap.
harness_reap() {
  local pid p _
  for pid in "${_HARNESS_PIDS[@]:-}"; do
    [ -n "${pid:-}" ] || continue
    if kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
      for _ in $(seq 1 20); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
      kill -9 "$pid" 2>/dev/null || true
    fi
  done
  for p in "${_HARNESS_PATTERNS[@]:-}"; do
    [ -n "${p:-}" ] || continue
    pkill -TERM -f "$p" 2>/dev/null || true
    for _ in $(seq 1 15); do pgrep -f "$p" >/dev/null 2>&1 || break; sleep 0.2; done
    pkill -KILL -f "$p" 2>/dev/null || true
    for _ in $(seq 1 10); do pgrep -f "$p" >/dev/null 2>&1 || break; sleep 0.2; done
  done
  _HARNESS_PIDS=()
  _HARNESS_PATTERNS=()
  return 0
}

# harness_wait_listen_tcp HOST PORT PID [tries]
#   Wait until HOST:PORT accepts a TCP connection, checking each poll that the
#   launched PID is still alive so a serve that dies on startup fails fast and
#   loudly instead of after the whole timeout. Returns:
#     0  listener up
#     2  the launched serve died before it bound
#     1  timed out (tries * 0.1s; default 8s)
harness_wait_listen_tcp() {
  local host="$1" port="$2" pid="${3:-}" tries="${4:-80}" i
  for ((i = 0; i < tries; i++)); do
    if harness_tcp_open "$host" "$port" 1; then return 0; fi
    if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then return 2; fi
    sleep 0.1
  done
  return 1
}

# harness_wait_log LOGFILE REGEX PID [tries]
#   Wait until REGEX (grep -E) appears in LOGFILE — for readiness signals that
#   are not a TCP listen, e.g. a UDP/QUIC "listening on .../udp" startup line.
#   Fails fast (rc 2) if PID dies first. Returns 0 ready / 2 died / 1 timeout
#   (tries * 0.2s; default 8s).
harness_wait_log() {
  local log="$1" regex="$2" pid="${3:-}" tries="${4:-40}" i
  for ((i = 0; i < tries; i++)); do
    if grep -Eq "$regex" "$log" 2>/dev/null; then return 0; fi
    if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then return 2; fi
    sleep 0.2
  done
  return 1
}
