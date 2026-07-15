#!/usr/bin/env bash
# Dense-FOLD A/B: the genuinely-dense multi-stage serve (drorb_serve_dense, DRORB_SPAN=8)
# vs its byte-identical List twin (drorb_serve_dense_list, DRORB_SPAN=9) vs the deployed
# metered/List serves. Both dense/list serves ECHO the request bytes into the response
# body, so a large POST body flows through the fold — the dense path carries it as a
# ByteArray, the List twin materializes input.data.toList (the K2 body cons). Same box,
# io_uring. The SPAN=8-vs-9 curl-diff MUST be byte-identical; the large-body req/s ratio
# is the dense-fold win.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DP_BIN="$ROOT/target/release/dataplane"
PORT="${PORT:-8080}"
SHARDS="${SHARDS:-8}"
N="${N:-200000}"          # tiny requests per cell
NB="${NB:-40000}"         # large-body requests per cell
BODY_KB="${BODY_KB:-256}" # large body size (KB)
WORK="$(mktemp -d /tmp/dense-ab.XXXXXX)"
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$HACL_DIST}"

head -c $((BODY_KB*1024)) /dev/zero | tr '\0' 'A' > "$WORK/big.bin"

reqs() { awk '/Requests per second/{print $4}'; }
p99()  { awk '/^ *99%/{print $2}'; }
fail() { awk '/Failed requests/{print $3}'; }

runcell() {  # desc concurrency n url extra...
  local desc="$1" c="$2" n="$3" url="$4"; shift 4
  local out; out="$(ab -k -q -n "$n" -c "$c" "$@" "$url" 2>/dev/null)"
  printf '  %-14s c=%-4s  %12s req/s   p99=%sms   failed=%s\n' \
    "$desc" "$c" "$(printf '%s' "$out" | reqs)" "$(printf '%s' "$out" | p99)" "$(printf '%s' "$out" | fail)"
}

for mode in 4 8 9; do
  case "$mode" in
    4) label="SPAN=4 deployed drorbServe (14-stage /health, List)";;
    8) label="SPAN=8 DENSE multi-stage fold (HdrBlock + ByteArray body)";;
    9) label="SPAN=9 LIST twin (cons-full, byte-identical to SPAN=8)";;
  esac
  echo "================================================================"
  echo "$label"
  echo "================================================================"
  DRORB_SPAN="$mode" "$DP_BIN" --bind 127.0.0.1:$PORT --io uring --shards "$SHARDS" >"$WORK/dp.$mode.log" 2>&1 &
  DP_PID=$!
  for _ in $(seq 1 60); do curl -s -o /dev/null "http://127.0.0.1:$PORT/health" && break; sleep 0.1; done
  curl -s "http://127.0.0.1:$PORT/health" -o "$WORK/tiny.$mode.out"
  curl -s --data-binary @"$WORK/big.bin" -H 'Content-Type: text/plain' \
       "http://127.0.0.1:$PORT/echo" -o "$WORK/big.$mode.out"
  echo "-- tiny GET /health --"
  runcell "tiny-GET" 64  "$N"  "http://127.0.0.1:$PORT/health"
  echo "-- ${BODY_KB}KB POST /echo --"
  runcell "big-POST" 64  "$NB" "http://127.0.0.1:$PORT/echo" -p "$WORK/big.bin" -T text/plain
  runcell "big-POST" 128 "$NB" "http://127.0.0.1:$PORT/echo" -p "$WORK/big.bin" -T text/plain
  kill "$DP_PID" 2>/dev/null; wait "$DP_PID" 2>/dev/null
  sleep 0.5
done

echo "================================================================"
echo "BYTE-IDENTITY (dense SPAN=8 vs List twin SPAN=9)"
echo "================================================================"
echo -n "tiny:  "; cmp -s "$WORK/tiny.8.out" "$WORK/tiny.9.out" && echo "IDENTICAL ($(wc -c <"$WORK/tiny.8.out") bytes)" || echo "DIFFER"
echo -n "${BODY_KB}KB: "; cmp -s "$WORK/big.8.out"  "$WORK/big.9.out"  && echo "IDENTICAL ($(wc -c <"$WORK/big.8.out") bytes)" || echo "DIFFER"
echo "sizes: dense=$(wc -c <"$WORK/big.8.out") list=$(wc -c <"$WORK/big.9.out") deployed=$(wc -c <"$WORK/big.4.out")"
echo "(SPAN=4 deployed serves a DIFFERENT response — the 14-stage /health route, not the echo — so it is the perf reference, not a byte-match target.)"
echo "workdir: $WORK"
