#!/usr/bin/env bash
# Reproducible dataplane throughput/latency bench: the orb vs a matched nginx
# reference, across the scenarios in PERF-AUDIT.md.
#
# Measures the CURRENT native host (crates/dataplane) end to end over a real
# loopback TCP socket, so every number includes the whole path: accept, recv,
# HTTP/1.1 framing, the seam crossing into the leanc-compiled proven serve, and
# send. nginx serves a byte-matched tiny reply, a 1 MiB file, and a reverse
# proxy to the same origin, so the two columns are apples to apples.
#
# The load generator is ApacheBench (ab). Each cell runs REPS times; the median
# req/s and the worst-observed p99 are reported. Kill every other load source
# before running: a busy machine inflates latency and depresses req/s for both.
#
# Usage:  conformance/perf/bench.sh            # full matrix
#         REPS=5 DURATION_REQS=100000 conformance/perf/bench.sh
#
# Requires: ab, nginx, curl, and a release dataplane binary + libdrorb archive
# (build: ffi/build-dataplane-lib.sh && (cd crates/dataplane && cargo build --release)).
set -u

# ---- config -----------------------------------------------------------------
REPS="${REPS:-3}"
N="${DURATION_REQS:-50000}"          # requests per ab cell (small-body)
N_BIG="${N_BIG:-5000}"               # requests per ab cell (1 MiB body)
ORB_PORT="${ORB_PORT:-8080}"
NGINX_PORT="${NGINX_PORT:-8081}"
ORIGIN_PORT="${ORIGIN_PORT:-9400}"   # reverse-proxy origin (nginx return 200)
ORB_PROXY_PORT="${ORB_PROXY_PORT:-8090}"

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/orb-perf.XXXXXX")"
AB="${AB:-$(command -v ab || echo /usr/sbin/ab)}"
NGINX="${NGINX:-$(command -v nginx || echo /opt/homebrew/bin/nginx)}"

# Crypto backend the archive links (harmless if already exported).
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-$HACL_DIST}"

DP_BIN="$ROOT/target/release/dataplane"

cleanup() {
  [ -n "${ORB_PID:-}" ] && kill "$ORB_PID" 2>/dev/null
  [ -n "${ORB_PROXY_PID:-}" ] && kill "$ORB_PROXY_PID" 2>/dev/null
  "$NGINX" -p "$WORK/nginx" -c "$WORK/nginx/nginx.conf" -s quit 2>/dev/null
  sleep 0.3
  rm -rf "$WORK"
}
trap cleanup EXIT

# ---- reference (nginx) ------------------------------------------------------
mkdir -p "$WORK/nginx/www" "$WORK/nginx/logs" "$WORK/nginx/tmp"
head -c 1048576 /dev/urandom > "$WORK/nginx/www/1mb.bin"
cat > "$WORK/nginx/nginx.conf" <<EOF
worker_processes auto;
daemon on;
error_log $WORK/nginx/logs/error.log crit;
pid $WORK/nginx/nginx.pid;
events { worker_connections 4096; }
http {
  access_log off; sendfile on; tcp_nodelay on; keepalive_timeout 60s;
  default_type application/octet-stream;
  client_body_temp_path $WORK/nginx/tmp; proxy_temp_path $WORK/nginx/tmp;
  fastcgi_temp_path $WORK/nginx/tmp; uwsgi_temp_path $WORK/nginx/tmp; scgi_temp_path $WORK/nginx/tmp;
  server { listen 127.0.0.1:$ORIGIN_PORT reuseport; location / { return 200 'ok'; } }
  server {
    listen 127.0.0.1:$NGINX_PORT reuseport; root $WORK/nginx/www;
    location = /health { return 200 'ok'; }
    location = /1mb.bin { }
    location /api { proxy_pass http://127.0.0.1:$ORIGIN_PORT; proxy_http_version 1.1; proxy_set_header Connection ""; }
  }
}
EOF
"$NGINX" -p "$WORK/nginx" -c "$WORK/nginx/nginx.conf"

# ---- subject (orb) ----------------------------------------------------------
"$DP_BIN" --bind 127.0.0.1:$ORB_PORT --no-udp >"$WORK/orb.log" 2>&1 &
ORB_PID=$!
DRORB_PROXY_BACKENDS="0=127.0.0.1:$ORIGIN_PORT" \
  "$DP_BIN" --bind 127.0.0.1:$ORB_PROXY_PORT --no-udp >"$WORK/orb-proxy.log" 2>&1 &
ORB_PROXY_PID=$!
sleep 2

# ---- ab helpers -------------------------------------------------------------
# Run ab once; echo "rps p50 p99". KA=1 sets keep-alive. -r keeps ab going on a
# socket reset (a contended proxy origin can reset a kept-alive connection).
ab_one() {
  local url="$1" c="$2" n="$3" ka="$4" ka_flag=""
  [ "$ka" = "1" ] && ka_flag="-k"
  local out; out="$($AB -q -r $ka_flag -c "$c" -n "$n" "$url" 2>/dev/null)"
  local rps p50 p99
  rps="$(awk '/Requests per second/{print $4}' <<<"$out")"
  p50="$(awk '/^ *50%/{print $2}' <<<"$out")"
  p99="$(awk '/^ *99%/{print $2}' <<<"$out")"
  echo "${rps:-NA} ${p50:-NA} ${p99:-NA}"
}

# Median rps + worst p99 over REPS runs.
cell() {
  local url="$1" c="$2" n="$3" ka="$4"
  local rpss=() p99s=() p50s=()
  for _ in $(seq 1 "$REPS"); do
    read -r rps p50 p99 < <(ab_one "$url" "$c" "$n" "$ka")
    rpss+=("$rps"); p50s+=("$p50"); p99s+=("$p99")
    sleep 0.5
  done
  local mrps mp50 wp99
  mrps="$(printf '%s\n' "${rpss[@]}" | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')"
  mp50="$(printf '%s\n' "${p50s[@]}" | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')"
  wp99="$(printf '%s\n' "${p99s[@]}" | sort -n | tail -1)"
  printf '%s %s %s' "$mrps" "$mp50" "$wp99"
}

row() { # label orb_url nginx_url c n ka
  local label="$1" ourl="$2" nurl="$3" c="$4" n="$5" ka="$6"
  read -r orps op50 op99 < <(echo "$(cell "$ourl" "$c" "$n" "$ka")")
  read -r nrps np50 np99 < <(echo "$(cell "$nurl" "$c" "$n" "$ka")")
  printf '%-34s | %10s %5s %6s | %10s %5s %6s\n' \
    "$label" "$orps" "$op50" "$op99" "$nrps" "$np50" "$np99"
}

echo "load at start: $(uptime | sed 's/.*load/load/')"
printf '%-34s | %-24s | %-24s\n' "scenario (c, n)" "ORB  rps  p50  p99(ms)" "NGINX rps p50 p99(ms)"
printf '%s\n' "--------------------------------------------------------------------------------------"
row "small conn-per-req (c10)"     "http://127.0.0.1:$ORB_PORT/health"  "http://127.0.0.1:$NGINX_PORT/health" 10  "$N" 0
row "small keep-alive (c10)"       "http://127.0.0.1:$ORB_PORT/health"  "http://127.0.0.1:$NGINX_PORT/health" 10  "$N" 1
# reverse-proxy: conn-per-request on both sides for parity (a kept-alive proxied
# connection to a contended origin resets, which skews keep-alive proxy numbers).
row "reverse-proxy conn-per-req (c10)" "http://127.0.0.1:$ORB_PROXY_PORT/api" "http://127.0.0.1:$NGINX_PORT/api" 10 "$N" 0
for c in 1 10 50 100; do
  row "conc sweep keep-alive (c$c)" "http://127.0.0.1:$ORB_PORT/health" "http://127.0.0.1:$NGINX_PORT/health" "$c" "$N" 1
done
echo "load at end:   $(uptime | sed 's/.*load/load/')"
echo
echo "Notes:"
echo " - The default serve has no large-body route; the orb's 1 MiB column is not"
echo "   at parity. Response-body construction is the O(N*len) cons-list — measure"
echo "   it with body-scaling.sh (config 'route /big respond 200 <body>')."
echo " - ORB rps plateauing as c rises = the single serve-thread ceiling (serialized);"
echo "   nginx keeps scaling (parallel workers). See PERF-AUDIT.md."
