#!/usr/bin/env bash
# Response-body construction scaling: how orb per-request latency grows with the
# response body size, vs nginx serving a byte-matched file.
#
# The orb answers a config route `route /big respond 200 <body>` where <body> is
# `sz` bytes. Every request re-runs the proven serve, which builds the response
# over a cons-list (List UInt8); this probes whether that cost is linear or worse
# in the body length. nginx serves the same-size static file (sendfile) as the
# flat reference. Single-request min-of-N wall time — the ratio ACROSS sizes is
# robust to a busy machine (both sizes see the same contention).
#
# Usage:  conformance/perf/body-scaling.sh
set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/orb-body.XXXXXX")"
NGINX="${NGINX:-$(command -v nginx || echo /opt/homebrew/bin/nginx)}"
DP_BIN="$ROOT/target/release/dataplane"
ORB_PORT=8091
NGINX_PORT=8092
REPS="${REPS:-8}"

export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-$HACL_DIST}"

cleanup() {
  [ -n "${ORB_PID:-}" ] && kill "$ORB_PID" 2>/dev/null
  "$NGINX" -p "$WORK/nginx" -c "$WORK/nginx/nginx.conf" -s quit 2>/dev/null
  rm -rf "$WORK"
}
trap cleanup EXIT

mkdir -p "$WORK/nginx/www" "$WORK/nginx/logs" "$WORK/nginx/tmp"
cat > "$WORK/nginx/nginx.conf" <<EOF
worker_processes auto; daemon on;
error_log $WORK/nginx/logs/error.log crit; pid $WORK/nginx/nginx.pid;
events { worker_connections 1024; }
http { access_log off; sendfile on; tcp_nodelay on;
  client_body_temp_path $WORK/nginx/tmp; proxy_temp_path $WORK/nginx/tmp;
  fastcgi_temp_path $WORK/nginx/tmp; uwsgi_temp_path $WORK/nginx/tmp; scgi_temp_path $WORK/nginx/tmp;
  server { listen 127.0.0.1:$NGINX_PORT; root $WORK/nginx/www; }
}
EOF
"$NGINX" -p "$WORK/nginx" -c "$WORK/nginx/nginx.conf"

mintime() { local url="$1" m=99 t; for _ in $(seq 1 "$REPS"); do
  t=$(curl -s -o /dev/null -w "%{time_total}" "$url"); awk "BEGIN{exit !($t<$m)}" && m=$t; done; echo "$m"; }

printf '%-8s %12s %10s | %12s\n' "body" "orb_min(s)" "orb_bytes" "nginx_min(s)"
for sz in 1024 4096 8192 16384; do
  body="$(head -c "$sz" /dev/zero | tr '\0' 'a')"
  printf 'listener 127.0.0.1 %s\npool api roundRobin\nl4 none\ntls no0rtt\nroute /big respond 200 %s\n' \
    "$ORB_PORT" "$body" > "$WORK/orb.conf"
  head -c "$sz" /dev/urandom > "$WORK/nginx/www/sz.bin"
  [ -n "${ORB_PID:-}" ] && kill "$ORB_PID" 2>/dev/null; sleep 0.4
  DRORB_CONFIG="$WORK/orb.conf" "$DP_BIN" --bind 127.0.0.1:$ORB_PORT --no-udp >"$WORK/orb.log" 2>&1 &
  ORB_PID=$!; sleep 1.5
  ob="$(curl -s -o /dev/null -w '%{size_download}' http://127.0.0.1:$ORB_PORT/big)"
  om="$(mintime http://127.0.0.1:$ORB_PORT/big)"
  nm="$(mintime http://127.0.0.1:$NGINX_PORT/sz.bin)"
  printf '%-8s %12s %10s | %12s\n' "$sz" "$om" "$ob" "$nm"
done
echo "(orb_bytes 0 => the inline-respond config exceeded the parser's line budget"
echo " and fell back to the default serve; another symptom of the cons-list cost.)"
