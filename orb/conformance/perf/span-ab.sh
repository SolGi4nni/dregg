#!/usr/bin/env bash
# Cons-list-removal A/B: the assembled flat serve (drorb_serve_span, DRORB_SPAN=1)
# vs its byte-identical List twin (drorb_serve_span_list, DRORB_SPAN=2) vs the
# deployed metered List serve (DRORB_SPAN unset). Same box, io_uring.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DP_BIN="$ROOT/target/release/dataplane"
PORT="${PORT:-8080}"
SHARDS="${SHARDS:-8}"
N="${N:-200000}"          # tiny requests per cell
N8="${N8:-60000}"         # 8KB requests per cell
WORK="$(mktemp -d /tmp/span-ab.XXXXXX)"
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$HACL_DIST}"

# 8KB POST payload
head -c 8192 /dev/zero | tr '\0' 'A' > "$WORK/8k.bin"

reqs() { awk '/Requests per second/{print $4}'; }
p99()  { awk '/^ *99%/{print $2}'; }
fail() { awk '/Failed requests/{print $3}'; }

runcell() {  # mode desc concurrency n url extra...
  local mode="$1" desc="$2" c="$3" n="$4" url="$5"; shift 5
  local out; out="$(ab -k -q -n "$n" -c "$c" "$@" "$url" 2>/dev/null)"
  printf '  %-14s c=%-4s  %10s req/s   p99=%sms   failed=%s\n' \
    "$desc" "$c" "$(printf '%s' "$out" | reqs)" "$(printf '%s' "$out" | p99)" "$(printf '%s' "$out" | fail)"
}

for mode in unset 1 2; do
  case "$mode" in
    unset) label="SPAN=0 deployed metered List serve"; env_span="";;
    1)     label="SPAN=1 FLAT assembled serve (cons-free)"; env_span="1";;
    2)     label="SPAN=2 LIST twin (cons-full, byte-identical to SPAN=1)"; env_span="2";;
  esac
  echo "================================================================"
  echo "$label"
  echo "================================================================"
  DRORB_SPAN="$env_span" "$DP_BIN" --bind 127.0.0.1:$PORT --io uring --shards "$SHARDS" >"$WORK/dp.$mode.log" 2>&1 &
  DP_PID=$!
  # wait for listen
  for _ in $(seq 1 50); do curl -s -o /dev/null "http://127.0.0.1:$PORT/health" && break; sleep 0.1; done
  # capture the served bytes for the byte-identity diff (tiny GET and 8KB POST)
  curl -s "http://127.0.0.1:$PORT/health" -o "$WORK/tiny.$mode.out"
  curl -s --data-binary @"$WORK/8k.bin" -H 'Content-Type: text/plain' \
       "http://127.0.0.1:$PORT/echo" -o "$WORK/big.$mode.out"
  echo "-- tiny GET /health --"
  runcell "$mode" "tiny-GET" 64  "$N"  "http://127.0.0.1:$PORT/health"
  runcell "$mode" "tiny-GET" 256 "$N"  "http://127.0.0.1:$PORT/health"
  echo "-- 8KB POST /echo --"
  runcell "$mode" "8KB-POST" 64  "$N8" "http://127.0.0.1:$PORT/echo" -p "$WORK/8k.bin" -T text/plain
  runcell "$mode" "8KB-POST" 256 "$N8" "http://127.0.0.1:$PORT/echo" -p "$WORK/8k.bin" -T text/plain
  kill "$DP_PID" 2>/dev/null; wait "$DP_PID" 2>/dev/null
  sleep 0.5
done

echo "================================================================"
echo "BYTE-IDENTITY (flat SPAN=1 vs List twin SPAN=2)"
echo "================================================================"
echo -n "tiny:  "; cmp -s "$WORK/tiny.1.out" "$WORK/tiny.2.out" && echo "IDENTICAL ($(wc -c <"$WORK/tiny.1.out") bytes)" || echo "DIFFER"
echo -n "8KB:   "; cmp -s "$WORK/big.1.out"  "$WORK/big.2.out"  && echo "IDENTICAL ($(wc -c <"$WORK/big.1.out") bytes)" || echo "DIFFER"
echo "(SPAN=0 deployed serves a DIFFERENT response — 14-stage route, not the echo exemplar — so it is the reference baseline, not a byte-match target.)"
echo "workdir: $WORK"
