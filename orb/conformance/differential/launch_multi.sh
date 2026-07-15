#!/usr/bin/env bash
# Launch the FOUR processes of the multi-reference differential lane:
#   backend  127.0.0.1:$BACKEND_PORT  (shared upstream all servers proxy to)
#   sut      127.0.0.1:$SUT_PORT      (the target serve, static + proxy wired)
#   caddy    127.0.0.1:$CADDY_PORT    (reference A: stock caddy, same site+route)
#   h2o      127.0.0.1:$H2O_PORT      (reference B: stock h2o, same site+route)
#
#   launch_multi.sh            # start (idempotent: restarts this lane only)
#   launch_multi.sh stop       # stop this lane's processes only
#
# Ports are lane-dedicated; override with SUT_PORT/CADDY_PORT/H2O_PORT/BACKEND_PORT.
# The static docroot + escape sibling are SHARED with the two-way lane (mksite.sh),
# so both references serve byte-identical files with pinned mtimes.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SITE="$HERE/site"

SUT_PORT="${SUT_PORT:-18950}"
CADDY_PORT="${CADDY_PORT:-18951}"
H2O_PORT="${H2O_PORT:-18952}"
BACKEND_PORT="${BACKEND_PORT:-18953}"
SUT_IO="${SUT_IO:-blocking}"

CADDY_BIN="${CADDY_BIN:-$HOME/diff-multi/bin/caddy}"
H2O_BIN="${H2O_BIN:-$(command -v h2o || echo /usr/bin/h2o)}"
RUN="$HERE/multi-run"
mkdir -p "$RUN"

stop_lane() {
    for f in "$RUN/sut.pid" "$RUN/caddy.pid" "$RUN/h2o.pid" "$RUN/backend.pid"; do
        if [ -f "$f" ]; then
            kill "$(cat "$f")" 2>/dev/null || true
            rm -f "$f"
        fi
    done
    sleep 0.3
}

if [ "${1:-}" = "stop" ]; then
    stop_lane
    echo "multi lane stopped"
    exit 0
fi

stop_lane
[ -d "$SITE" ] || bash "$HERE/mksite.sh"

# --- shared upstream backend ---------------------------------------------
BACKEND_BIN="$REPO/target/release/examples/proxy_backend"
if [ ! -x "$BACKEND_BIN" ]; then
    echo "FATAL: $BACKEND_BIN missing (build: cargo build --release --example proxy_backend)"
    exit 1
fi
"$BACKEND_BIN" "127.0.0.1:${BACKEND_PORT}" b0 >"$RUN/backend.log" 2>&1 &
echo $! > "$RUN/backend.pid"

# --- system under test: the target serve ---------------------------------
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LD_LIBRARY_PATH="${HACL_DIST}:${LD_LIBRARY_PATH:-}"
# Effect seam deliberately UNSET so GET /static/* reaches the file lane and
# /api reaches the proxy hook (mirrors the two-way lane's wiring).
DRORB_RUST_GZIP=1 \
DRORB_STATIC_ROOT="$SITE" DRORB_STATIC_PREFIX=/static/ \
DRORB_PROXY_BACKENDS="0=127.0.0.1:${BACKEND_PORT}" \
  "$REPO/target/release/dataplane" --bind "127.0.0.1:${SUT_PORT}" --no-udp --io "$SUT_IO" \
  >"$RUN/sut.log" 2>&1 &
echo $! > "$RUN/sut.pid"

# --- reference A: caddy ---------------------------------------------------
# Stock behaviour: static under /static/ (prefix stripped to docroot), one
# reverse-proxy route at /api, on-the-fly gzip. No tuning.
cat > "$RUN/Caddyfile" <<EOF
{
	admin off
	auto_https off
	http_port ${CADDY_PORT}
	log {
		output file $RUN/caddy-access.log
		level ERROR
	}
}

:${CADDY_PORT} {
	encode gzip

	handle_path /static/* {
		root * ${SITE}
		file_server
	}

	handle /api* {
		reverse_proxy 127.0.0.1:${BACKEND_PORT}
	}

	handle {
		respond 404
	}
}
EOF
"$CADDY_BIN" run --config "$RUN/Caddyfile" --adapter caddyfile >"$RUN/caddy.log" 2>&1 &
echo $! > "$RUN/caddy.pid"

# --- reference B: h2o -----------------------------------------------------
cat > "$RUN/h2o.conf" <<EOF
listen:
  host: 127.0.0.1
  port: ${H2O_PORT}
error-log: $RUN/h2o-error.log
access-log: $RUN/h2o-access.log
compress: ON
hosts:
  "default":
    paths:
      "/static":
        file.dir: ${SITE}
      "/api":
        proxy.reverse.url: "http://127.0.0.1:${BACKEND_PORT}/"
EOF
"$H2O_BIN" -c "$RUN/h2o.conf" >"$RUN/h2o.log" 2>&1 &
echo $! > "$RUN/h2o.pid"

# --- wait for all four listeners -----------------------------------------
for port in "$BACKEND_PORT" "$SUT_PORT" "$CADDY_PORT" "$H2O_PORT"; do
    ok=0
    for _ in $(seq 1 60); do
        if ss -ltn 2>/dev/null | grep -q ":${port} "; then ok=1; break; fi
        sleep 0.1
    done
    if [ "$ok" = 1 ]; then
        echo "listening: 127.0.0.1:${port}"
    else
        echo "FAILED to listen: 127.0.0.1:${port}"
        case "$port" in
            "$SUT_PORT") tail -8 "$RUN/sut.log" ;;
            "$CADDY_PORT") tail -8 "$RUN/caddy.log" ;;
            "$H2O_PORT") tail -8 "$RUN/h2o.log" ;;
        esac
        exit 1
    fi
done
echo "multi lane up: sut=$SUT_PORT caddy=$CADDY_PORT h2o=$H2O_PORT backend=$BACKEND_PORT"
