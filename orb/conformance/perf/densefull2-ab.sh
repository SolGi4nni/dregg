#!/usr/bin/env bash
# FULLY-DENSE-TOKENIZER A/B: the deployed html-rewrite body transform run three ways
# on a large HTML body echoed through /echo:
#   DRORB_SPAN=11  the List twin  (deployed rewriteBytes: cons-list tokenizer + body cons)
#   DRORB_SPAN=10  input/output dense, token-List still consed (rewriteBytesDense, ~2.35x)
#   DRORB_SPAN=12  FULLY dense tokenizer (rewriteBytesDense2, NO token cons)
# All three are proven byte-identical (serveDenseFull_refines / serveDenseFull2_refines),
# so the req/s ratio isolates the body-transform representation cost. io_uring.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DP_BIN="$ROOT/target/release/dataplane"
PORT="${PORT:-8080}"
SHARDS="${SHARDS:-8}"
NB="${NB:-60000}"           # large-body requests per cell
BODY_KB="${BODY_KB:-16}"    # HTML body size (KB)
WORK="$(mktemp -d /tmp/densefull2-ab.XXXXXX)"
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$HACL_DIST}"

# A realistic ~BODY_KB HTML body: markup the tokenizer must scan tag/text spans of.
python3 - "$WORK/body.html" "$BODY_KB" <<'PY'
import sys
path, kb = sys.argv[1], int(sys.argv[2])
target = kb * 1024
chunk = '<div class="row"><span id="a">Hello, world.</span> some text run here <b>bold</b> and more.</div>\n'
buf = []
n = 0
while n < target:
    buf.append(chunk); n += len(chunk)
open(path, "w").write("".join(buf)[:target])
PY
echo "body: $(wc -c <"$WORK/body.html") bytes HTML"

reqs() { awk '/Requests per second/{print $4}'; }
p99()  { awk '/^ *99%/{print $2}'; }
fail() { awk '/Failed requests/{print $3}'; }

declare -A RPS
for mode in 11 10 12; do
  case "$mode" in
    11) label="SPAN=11 List twin (deployed rewriteBytes: cons tokenizer + body cons)";;
    10) label="SPAN=10 input/output dense, token-List consed (rewriteBytesDense)";;
    12) label="SPAN=12 FULLY-DENSE tokenizer (rewriteBytesDense2, no token cons)";;
  esac
  echo "================================================================"
  echo "$label"
  echo "================================================================"
  DRORB_SPAN="$mode" "$DP_BIN" --bind 127.0.0.1:$PORT --io uring --shards "$SHARDS" >"$WORK/dp.$mode.log" 2>&1 &
  DP_PID=$!
  for _ in $(seq 1 80); do curl -s -o /dev/null "http://127.0.0.1:$PORT/health" && break; sleep 0.1; done
  curl -s --data-binary @"$WORK/body.html" -H 'Content-Type: text/html' \
       "http://127.0.0.1:$PORT/echo" -o "$WORK/out.$mode.bin"
  best=0
  for c in 64 128; do
    out="$(ab -k -q -n "$NB" -c "$c" -p "$WORK/body.html" -T text/html "http://127.0.0.1:$PORT/echo" 2>/dev/null)"
    r="$(printf '%s' "$out" | reqs)"; p="$(printf '%s' "$out" | p99)"; f="$(printf '%s' "$out" | fail)"
    printf '  big-POST c=%-4s  %12s req/s   p99=%sms   failed=%s\n' "$c" "${r:-NA}" "${p:-NA}" "${f:-NA}"
    awk "BEGIN{exit !(${r:-0} > ${best:-0})}" && best="$r"
  done
  RPS[$mode]="$best"
  kill "$DP_PID" 2>/dev/null; wait "$DP_PID" 2>/dev/null
  sleep 0.5
done

echo "================================================================"
echo "BYTE-IDENTITY (all three must be identical — proven, curl-verified)"
echo "================================================================"
echo -n "12 vs 11: "; cmp -s "$WORK/out.12.bin" "$WORK/out.11.bin" && echo "IDENTICAL ($(wc -c <"$WORK/out.12.bin") bytes)" || echo "DIFFER"
echo -n "12 vs 10: "; cmp -s "$WORK/out.12.bin" "$WORK/out.10.bin" && echo "IDENTICAL" || echo "DIFFER"
echo -n "10 vs 11: "; cmp -s "$WORK/out.10.bin" "$WORK/out.11.bin" && echo "IDENTICAL" || echo "DIFFER"

echo "================================================================"
echo "RATIOS (best-of-c req/s)"
echo "================================================================"
printf '  SPAN=11 (List twin)          : %s req/s\n' "${RPS[11]}"
printf '  SPAN=10 (in/out dense)       : %s req/s\n' "${RPS[10]}"
printf '  SPAN=12 (fully dense token)  : %s req/s\n' "${RPS[12]}"
awk -v a="${RPS[10]}" -v b="${RPS[11]}" 'BEGIN{if(b>0)printf "  10/11 (the ~2.35x prior)     : %.2fx\n", a/b}'
awk -v a="${RPS[12]}" -v b="${RPS[11]}" 'BEGIN{if(b>0)printf "  12/11 (HEADLINE, token-List killed): %.2fx\n", a/b}'
awk -v a="${RPS[12]}" -v b="${RPS[10]}" 'BEGIN{if(b>0)printf "  12/10 (token-List increment) : %.2fx\n", a/b}'
echo "workdir: $WORK"
