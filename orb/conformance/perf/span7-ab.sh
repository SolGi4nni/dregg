#!/usr/bin/env bash
# Full-poly cons-list A/B. Measures the REAL deployed serve across spans:
#   4 = drorb_serve         (deployed non-metered List serve; the byte-identical baseline)
#   3 = drorb_serve_full    (egress-flat, byte-identical to deployed)
#   7 = drorb_serve_poly    (FULL POLY serve; byte-identical to deployed)  [when built]
#   5 = drorb_serve_bodypoly       (body-dense exemplar)
#   6 = drorb_serve_bodypoly_list  (body-dense List twin)
#   0 = deployed metered
# Same box, io_uring. reqs/sec + p50/p99 at c=64 on a REAL route + 8KB body.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DP_BIN="$ROOT/target/release/dataplane"
PORT="${PORT:-8137}"
SHARDS="${SHARDS:-8}"
N="${N:-150000}"
N8="${N8:-50000}"
SPANS="${SPANS:-4 3 7 5 6}"
WORK="$(mktemp -d /tmp/span7.XXXXXX)"
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$HACL_DIST}"

head -c 8192 /dev/zero | tr '\0' 'A' > "$WORK/8k.bin"

reqs() { awk '/Requests per second/{print $4}'; }
p50()  { awk '/^ *50%/{print $2}'; }
p99()  { awk '/^ *99%/{print $2}'; }
fail() { awk '/Failed requests/{print $3}'; }
n2xx() { awk '/Non-2xx responses/{print $4}'; }

runcell() {  # desc concurrency n url extra...
  local desc="$1" c="$2" n="$3" url="$4"; shift 4
  local out; out="$(ab -k -q -n "$n" -c "$c" "$@" "$url" 2>/dev/null)"
  printf '  %-12s c=%-4s  %10s req/s   p50=%sms p99=%sms   failed=%s non2xx=%s\n' \
    "$desc" "$c" "$(printf '%s' "$out" | reqs)" "$(printf '%s' "$out" | p50)" \
    "$(printf '%s' "$out" | p99)" "$(printf '%s' "$out" | fail)" "$(printf '%s' "$out" | n2xx)"
}

for mode in $SPANS; do
  case "$mode" in
    0) label="SPAN=0 deployed metered List serve"; env_span="";;
    *) label="SPAN=$mode"; env_span="$mode";;
  esac
  echo "================================================================"
  echo "$label"
  echo "================================================================"
  DRORB_SPAN="$env_span" "$DP_BIN" --bind 127.0.0.1:$PORT --io uring --shards "$SHARDS" >"$WORK/dp.$mode.log" 2>&1 &
  DP_PID=$!
  ok=0
  for _ in $(seq 1 60); do curl -s -o /dev/null "http://127.0.0.1:$PORT/health" && { ok=1; break; }; sleep 0.1; done
  if [ "$ok" != 1 ]; then echo "  [FAILED TO LISTEN]"; head -5 "$WORK/dp.$mode.log"; kill "$DP_PID" 2>/dev/null; wait "$DP_PID" 2>/dev/null; continue; fi
  curl -s "http://127.0.0.1:$PORT/health" -o "$WORK/tiny.$mode.out"
  curl -s --data-binary @"$WORK/8k.bin" -H 'Content-Type: text/plain' \
       "http://127.0.0.1:$PORT/echo" -o "$WORK/big.$mode.out"
  echo "  tiny bytes=$(wc -c <"$WORK/tiny.$mode.out")  8kb-resp bytes=$(wc -c <"$WORK/big.$mode.out")"
  runcell "tiny-GET"  64 "$N"  "http://127.0.0.1:$PORT/health"
  runcell "8KB-POST"  64 "$N8" "http://127.0.0.1:$PORT/echo" -p "$WORK/8k.bin" -T text/plain
  kill "$DP_PID" 2>/dev/null; wait "$DP_PID" 2>/dev/null
  sleep 0.4
done

echo "================================================================"
echo "BYTE-IDENTITY vs SPAN=4 (deployed List serve)"
echo "================================================================"
for mode in $SPANS; do
  [ "$mode" = 4 ] && continue
  [ -f "$WORK/tiny.$mode.out" ] || continue
  printf 'SPAN=%s  tiny: ' "$mode"
  cmp -s "$WORK/tiny.4.out" "$WORK/tiny.$mode.out" && printf 'IDENTICAL' || printf 'DIFFER'
  printf '   8KB: '
  cmp -s "$WORK/big.4.out" "$WORK/big.$mode.out" && echo 'IDENTICAL' || echo 'DIFFER'
done
echo "workdir: $WORK"
