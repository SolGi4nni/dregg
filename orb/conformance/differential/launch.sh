#!/usr/bin/env bash
# Launch the three processes of the differential lane:
#   backend  127.0.0.1:$BACKEND_PORT  (shared upstream both proxies forward to)
#   sut      127.0.0.1:$SUT_PORT      (the drorb dataplane, static + proxy wired)
#   ref      127.0.0.1:$REF_PORT      (stock reference server, same site + route)
#
#   conformance/differential/launch.sh          # start (idempotent: restarts)
#   conformance/differential/launch.sh stop     # stop this lane's processes only
#
# Ports are lane-dedicated; override with SUT_PORT/REF_PORT/BACKEND_PORT.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"

SUT_PORT="${SUT_PORT:-18930}"
REF_PORT="${REF_PORT:-18931}"
BACKEND_PORT="${BACKEND_PORT:-18932}"
# The `--io` reactor for the SUT. Default `auto` = the mode the shipped binary
# picks (io_uring on Linux, kqueue on macOS/BSD), so the differential compares
# the reactor production runs against the reference origin. It used to default
# to `blocking` on the claim that the static-file lane is blocking-only; that is
# stale — the static docroot serves on io_uring. SUT_IO=blocking still selects
# the portable fallback explicitly.
SUT_IO="${SUT_IO:-auto}"

stop_lane() {
    # Kill only THIS lane's processes (matched by our ports / pid files), never
    # the whole binary family — other lanes run the same binaries.
    if [ -f "$HERE/ref/ref.pid" ]; then
        kill "$(cat "$HERE/ref/ref.pid")" 2>/dev/null || true
        rm -f "$HERE/ref/ref.pid"
    fi
    for f in "$HERE/sut.pid" "$HERE/backend.pid"; do
        if [ -f "$f" ]; then
            kill "$(cat "$f")" 2>/dev/null || true
            rm -f "$f"
        fi
    done
    sleep 0.3
}

if [ "${1:-}" = "stop" ]; then
    stop_lane
    echo "lane stopped"
    exit 0
fi

stop_lane

[ -d "$HERE/site" ] || bash "$HERE/mksite.sh"
mkdir -p "$HERE/ref/tmp"

# --- shared upstream backend ---------------------------------------------
BACKEND_BIN="$REPO/target/release/examples/proxy_backend"
if [ ! -x "$BACKEND_BIN" ]; then
    echo "FATAL: $BACKEND_BIN missing (build: cargo build --release --example proxy_backend)"
    exit 1
fi
"$BACKEND_BIN" "127.0.0.1:${BACKEND_PORT}" b0 >"$HERE/backend.log" 2>&1 &
echo $! > "$HERE/backend.pid"

# --- system under test: the dataplane with static root + proxy fleet -----
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LD_LIBRARY_PATH="${HACL_DIST}:${LD_LIBRARY_PATH:-}"
# NOTE: DRORB_EFFECT_SEAM is deliberately UNSET. With the effect seam on,
# interp::should_handle claims every cacheable-shape GET before the host static
# lane and before the proxy_hook, so /static/* would never reach the file lane.
# Seam off: GET /static/* falls to the static lane, and /api falls to the proxy
# hook (which forwards to the fleet). Both are what this harness maps.
DRORB_RUST_GZIP=1 \
DRORB_STATIC_ROOT="$HERE/site" DRORB_STATIC_PREFIX=/static/ \
DRORB_PROXY_BACKENDS="0=127.0.0.1:${BACKEND_PORT}" \
  "$REPO/target/release/dataplane" --bind "127.0.0.1:${SUT_PORT}" --no-udp --io "$SUT_IO" \
  >"$HERE/sut.log" 2>&1 &
echo $! > "$HERE/sut.pid"

# --- reference server ------------------------------------------------------
sed -e "s|@ROOT@|$HERE|g" -e "s|@SITE@|$HERE/site|g" \
    -e "s|@REF_PORT@|$REF_PORT|g" -e "s|@BACKEND_PORT@|$BACKEND_PORT|g" \
    "$HERE/reference.conf.in" > "$HERE/ref/ref.conf"
/usr/sbin/nginx -p "$HERE/ref" -c "$HERE/ref/ref.conf"

# --- wait for all three listeners -----------------------------------------
for port in "$BACKEND_PORT" "$SUT_PORT" "$REF_PORT"; do
    ok=0
    for _ in $(seq 1 50); do
        if ss -ltn 2>/dev/null | grep -q ":${port} "; then ok=1; break; fi
        sleep 0.1
    done
    if [ "$ok" = 1 ]; then
        echo "listening: 127.0.0.1:${port}"
    else
        echo "FAILED to listen: 127.0.0.1:${port}"
        [ "$port" = "$SUT_PORT" ] && tail -5 "$HERE/sut.log"
        exit 1
    fi
done
echo "lane up: sut=$SUT_PORT ref=$REF_PORT backend=$BACKEND_PORT"
# diff.py reads $SUT_PORT/$REF_PORT as its defaults, so the launcher's knob and
# the differ's knob are the same knob. Print the exact command including the
# resolved ports: driving the differ at the wrong ports used to score a silent
# clean run (both sides unreachable = no divergence). It now fails loud, but
# the point is not to get there.
echo "run the differ: SUT_PORT=$SUT_PORT REF_PORT=$REF_PORT python3 $HERE/diff.py"
