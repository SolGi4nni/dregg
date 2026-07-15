#!/usr/bin/env bash
# Dual-path conformance runner.
#
# Runs the key conformance suites TWICE against the same serve binary — once with
# the effect/continuation seam enabled (DRORB_EFFECT_SEAM=1) and once against the
# bare default conformantServe path (seam UNSET) — and reports BOTH results side
# by side. It FAILS (nonzero exit) if EITHER path has any failing check or leak.
#
# The point is to surface PATH-DIVERGENT bugs: a gap or leak that shows up on one
# serve path but not the other, so a defect cannot hide behind a single env var.
# A suite that passes clean on the seam path but fails a check on the bare default
# is exactly the class of finding this runner exists to catch.
#
# Suites driven (per path):
#   rfc_conformance.py       core HTTP/1.1 message-syntax/semantics probe
#   rfc_conformance_ext.py   extended edge-case probe
#   rfc_conformance_full.py  full catalogue probe
#   leak_scan.py             information-disclosure leak gate (--target mode)
#
# This runner OWNS launching the serve on its own dedicated ports so it controls
# the seam env precisely; it does NOT edit any suite. The suites read the target
# from CONF_HTTP_HOST/CONF_HTTP_PORT (rfc probes) or --target (leak_scan). Each
# suite's fixed output JSON is copied to a per-path file after each run.
#
#   conformance/dual_path.sh
#
# Environment:
#   DUAL_BASE_PORT  base TCP port (default 18990). Seam path uses BASE, bare path
#                   uses BASE+1. Both are dedicated to this runner.
#   HACL_DIST       HACL*/EverCrypt gcc-compatible dist (default
#                   $HOME/src/hacl-star/dist/gcc-compatible).
#   DUAL_IO         reactor io backend for the serve (default: blocking).
#   DUAL_GZIP       set to 0 to drop the rust-gzip seam from BOTH paths (default
#                   1: gzip on for both, so the only A/B variable is the effect
#                   seam itself).
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="$HACL_DIST:${LIBRARY_PATH:-}"
export LD_LIBRARY_PATH="$HACL_DIST:${LD_LIBRARY_PATH:-}"
export DYLD_LIBRARY_PATH="$HACL_DIST:${DYLD_LIBRARY_PATH:-}"

DATAPLANE="$ROOT/target/release/dataplane"
BASE_PORT="${DUAL_BASE_PORT:-18990}"
IO="${DUAL_IO:-blocking}"
GZIP="${DUAL_GZIP:-1}"
HOST="127.0.0.1"

OUT="$HERE/dual_path_out"
mkdir -p "$OUT"

if [ ! -x "$DATAPLANE" ]; then
  echo "HARNESS ERROR: dataplane binary missing at $DATAPLANE" >&2
  echo "  build it first (conformance/run.sh does this) or point ROOT at a built tree." >&2
  exit 2
fi

# --- proc reaping: only the serves THIS runner launches ---------------------- #
# Two-layer, swarm-safe:
#   1. kill the tracked launch PIDs, and
#   2. sweep any serve still bound to a port THIS runner owns, matched by the
#      exact `--bind HOST:port` command line. dataplane reparents to init if the
#      launching subshell exits first, so a PID-only reap can orphan it; the
#      port-exact sweep catches that without ever touching a sibling's port.
LAUNCHED_PIDS=()
OWNED_PORTS=()
reap_launched() {
  for pid in "${LAUNCHED_PIDS[@]:-}"; do
    [ -n "${pid:-}" ] || continue
    if kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
      for _ in $(seq 1 20); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
      kill -9 "$pid" 2>/dev/null || true
    fi
  done
  for p in "${OWNED_PORTS[@]:-}"; do
    [ -n "${p:-}" ] || continue
    local pat="release/dataplane --bind $HOST:$p "
    pkill -TERM -f "$pat" 2>/dev/null || true
    # dataplane does a graceful SIGTERM shutdown that can outlast a short grace;
    # escalate to SIGKILL and loop until the port-exact match is gone so we never
    # leave a daemonized (ppid=1) serve behind.
    for _ in $(seq 1 15); do
      pgrep -f "$pat" >/dev/null 2>&1 || break
      sleep 0.2
    done
    pkill -KILL -f "$pat" 2>/dev/null || true
    for _ in $(seq 1 10); do
      pgrep -f "$pat" >/dev/null 2>&1 || break
      sleep 0.2
    done
  done
  LAUNCHED_PIDS=()
}
trap reap_launched EXIT

wait_tcp() { # host port tries
  local h="$1" p="$2" tries="${3:-80}"
  for _ in $(seq 1 "$tries"); do
    if (exec 3<>"/dev/tcp/$h/$p") 2>/dev/null; then exec 3>&- 3<&- ; return 0; fi
    sleep 0.1
  done
  return 1
}

launch_serve() { # port seam(0|1)  -> returns 0 on up; records pid+port for reap
  # MUST be called directly (not via $(...)) so its appends to the global
  # LAUNCHED_PIDS / OWNED_PORTS land in THIS shell, not a command-substitution
  # subshell that would discard them and leave the reap arrays empty (orphans).
  local port="$1" seam="$2"
  # SWARM SAFETY: the shared worktree may already have a sibling serve on this
  # port. If we blindly launched and then wait_tcp'd, we would connect to the
  # SIBLING's serve (our own bind having silently failed) and drive the suites
  # against the wrong process — a false, path-contaminated result. So refuse to
  # start if the port is already listening; the caller must pick a free base.
  if wait_tcp "$HOST" "$port" 1; then
    echo "HARNESS ERROR: $HOST:$port is already in use (a sibling serve?)." >&2
    echo "  set DUAL_BASE_PORT to a free base so this runner owns its own ports." >&2
    return 1
  fi
  # The port was free — only NOW do we claim it, so the port-exact reap can never
  # target a sibling that happened to be on a port we merely probed.
  OWNED_PORTS+=("$port")
  # Inherit the current environment (locale, HOME, etc.) and toggle ONLY the two
  # deployment seam vars, so the effect seam is the single A/B variable between
  # the two paths. Launch in a subshell so these exports do not leak upward.
  (
    unset DRORB_EFFECT_SEAM
    [ "$GZIP" = "1" ] && export DRORB_RUST_GZIP=1 || unset DRORB_RUST_GZIP
    [ "$seam" = "1" ] && export DRORB_EFFECT_SEAM=1
    exec "$DATAPLANE" --bind "$HOST:$port" --no-udp --io "$IO"
  ) >"$OUT/serve-$port.log" 2>&1 &
  local pid=$!
  LAUNCHED_PIDS+=("$pid")
  if ! wait_tcp "$HOST" "$port" 80; then
    echo "HARNESS ERROR: serve did not come up on $HOST:$port (seam=$seam)" >&2
    cat "$OUT/serve-$port.log" >&2 || true
    return 1
  fi
  # The listen socket is up — confirm it is OURS, not a race with a sibling that
  # grabbed the port after our pre-check: the child we launched must still live.
  if ! kill -0 "$pid" 2>/dev/null; then
    echo "HARNESS ERROR: our serve on $HOST:$port died (bind lost to a race?)." >&2
    cat "$OUT/serve-$port.log" >&2 || true
    return 1
  fi
  echo "  serve up: pid=$pid on $HOST:$port (seam=$seam)"
}

run_path() { # label seam port
  local label="$1" seam="$2" port="$3"
  echo
  echo "########################################################################"
  echo "## PATH: $label   (DRORB_EFFECT_SEAM=$([ "$seam" = 1 ] && echo 1 || echo unset), port $port)"
  echo "########################################################################"

  # Direct call (NOT $(...)) so pid/port tracking lands in this shell for the reap.
  launch_serve "$port" "$seam" || return 1

  export CONF_HTTP_HOST="$HOST"
  export CONF_HTTP_PORT="$port"

  echo
  echo "-- [$label] rfc_conformance.py (core HTTP/1.1) --"
  python3 "$HERE/rfc_conformance.py" || true
  cp -f "$HERE/results_rfc.json" "$OUT/results_rfc.$label.json" 2>/dev/null || true

  echo
  echo "-- [$label] rfc_conformance_ext.py (extended) --"
  python3 "$HERE/rfc_conformance_ext.py" || true
  cp -f "$HERE/results_rfc_ext.json" "$OUT/results_rfc_ext.$label.json" 2>/dev/null || true

  echo
  echo "-- [$label] rfc_conformance_full.py (full catalogue) --"
  python3 "$HERE/rfc_conformance_full.py" || true
  cp -f "$HERE/results_rfc_full.json" "$OUT/results_rfc_full.$label.json" 2>/dev/null || true

  echo
  echo "-- [$label] leak_scan.py (info-disclosure gate, --target) --"
  # --target scans an already-listening serve, so the seam env is exactly what
  # THIS runner launched with (the suite does not re-launch/override it).
  python3 "$HERE/leak_scan.py" --target "$HOST:$port" \
      --json "$OUT/results_leak.$label.json" || true

  # tear down this path's serve before the next path binds
  reap_launched
  unset CONF_HTTP_HOST CONF_HTTP_PORT
}

SEAM_PORT="$BASE_PORT"
BARE_PORT="$((BASE_PORT + 1))"

run_path "seam" 1 "$SEAM_PORT"
run_path "bare" 0 "$BARE_PORT"

# --------------------------------------------------------------------------- #
# Cross-path comparison + gate
# --------------------------------------------------------------------------- #
echo
echo "########################################################################"
echo "## DUAL-PATH COMPARISON"
echo "########################################################################"

python3 - "$OUT" <<'PYEOF'
import json, os, sys
out = sys.argv[1]

def load(path):
    try:
        with open(path) as f: return json.load(f)
    except Exception:
        return None

RFC = [
    ("rfc-core", "results_rfc"),
    ("rfc-ext",  "results_rfc_ext"),
    ("rfc-full", "results_rfc_full"),
]

def is_fail(v):   return v == "FAIL"
def is_pass(v):   return v == "PASS"

any_path_fail = False
divergences = []   # (suite, check_id, seam_verdict, bare_verdict, criterion, observed_seam, observed_bare)
missing = []

print()
print(f"{'SUITE':<10} {'PASS(seam)':>11} {'FAIL(seam)':>11} {'PASS(bare)':>11} {'FAIL(bare)':>11}  {'DIVERGE':>8}")
print("-" * 78)

for label, base in RFC:
    s = load(os.path.join(out, f"{base}.seam.json"))
    b = load(os.path.join(out, f"{base}.bare.json"))
    if s is None or b is None:
        missing.append(label)
        print(f"{label:<10} {'--':>11} {'--':>11} {'--':>11} {'--':>11}  {'MISSING':>8}")
        any_path_fail = True
        continue
    sc = {c["id"]: c for c in s["checks"]}
    bc = {c["id"]: c for c in b["checks"]}
    s_pass = sum(1 for c in s["checks"] if is_pass(c["verdict"]))
    s_fail = sum(1 for c in s["checks"] if is_fail(c["verdict"]))
    b_pass = sum(1 for c in b["checks"] if is_pass(c["verdict"]))
    b_fail = sum(1 for c in b["checks"] if is_fail(c["verdict"]))
    if s_fail: any_path_fail = True
    if b_fail: any_path_fail = True
    ndiv = 0
    for cid in sorted(set(sc) | set(bc)):
        sv = sc.get(cid, {}).get("verdict", "MISSING")
        bv = bc.get(cid, {}).get("verdict", "MISSING")
        # divergence = pass/fail disagreement between the two paths
        s_f, b_f = is_fail(sv), is_fail(bv)
        if s_f != b_f:
            ndiv += 1
            crit = (sc.get(cid) or bc.get(cid)).get("criterion", "")
            divergences.append((
                label, cid, sv, bv, crit,
                sc.get(cid, {}).get("observed", ""),
                bc.get(cid, {}).get("observed", ""),
            ))
    print(f"{label:<10} {s_pass:>11} {s_fail:>11} {b_pass:>11} {b_fail:>11}  {ndiv:>8}")

# leak scan
ls = load(os.path.join(out, "results_leak.seam.json"))
lb = load(os.path.join(out, "results_leak.bare.json"))
def leak_verdict(d):
    if d is None: return "MISSING"
    return d.get("verdict", "MISSING")
lv_s, lv_b = leak_verdict(ls), leak_verdict(lb)
def leaks_of(d):
    if d is None: return {}
    return {r["route"]: r.get("leaks", {}) for r in d.get("results", []) if r.get("leaks")}
lk_s, lk_b = leaks_of(ls), leaks_of(lb)
if lv_s == "FAIL" or lv_b == "FAIL": any_path_fail = True
if lv_s == "MISSING" or lv_b == "MISSING": any_path_fail = True
print(f"{'leak-scan':<10} {('LEAK' if lk_s else 'clean'):>11} {'':>11} {('LEAK' if lk_b else 'clean'):>11} {'':>11}  "
      f"{('DIVERGE' if set(lk_s) != set(lk_b) else '.'):>8}")
print("-" * 78)

# --- itemized divergences: THE finding ------------------------------------- #
print()
if divergences:
    print(f"PATH-DIVERGENT CHECKS ({len(divergences)}) — fail on one serve path, not the other:")
    print()
    for label, cid, sv, bv, crit, obs_s, obs_b in divergences:
        worse = "bare" if is_fail(bv) and not is_fail(sv) else ("seam" if is_fail(sv) and not is_fail(bv) else "?")
        print(f"  [{label}] {cid}")
        print(f"      seam={sv}   bare={bv}   (fails on: {worse} path)")
        print(f"      criterion: {crit}")
        if is_fail(sv): print(f"      observed(seam): {obs_s}")
        if is_fail(bv): print(f"      observed(bare): {obs_b}")
        print()
else:
    print("no path-divergent RFC checks: both serve paths agree check-for-check.")

# leak divergence detail
lk_div = set(lk_s) ^ set(lk_b)
if lk_div:
    print()
    print(f"PATH-DIVERGENT LEAKS ({len(lk_div)} route(s)) — disclose on one path, not the other:")
    for route in sorted(lk_div):
        where = "seam" if route in lk_s else "bare"
        detail = (lk_s if route in lk_s else lk_b)[route]
        print(f"  [{route}] leaks only on {where} path: {detail}")

# --- gate ------------------------------------------------------------------ #
print()
print("=" * 78)
if missing:
    print(f"GATE: FAIL — missing per-path result(s): {', '.join(missing)}")
elif any_path_fail:
    print("GATE: FAIL — at least one serve path has a failing check or leak "
          "(see per-path tables + divergences above).")
else:
    print("GATE: PASS — both serve paths clean, check-for-check, with no leaks.")
print("=" * 78)

sys.exit(1 if (any_path_fail or missing) else 0)
PYEOF
GATE=$?

echo
echo "per-path artifacts under: $OUT"
exit "$GATE"
