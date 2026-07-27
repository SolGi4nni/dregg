#!/usr/bin/env bash
# CONTENT-TYPE-GATED body-passthrough A/B. The SAME large body (with `<`/`>` bytes)
# echoed through /echo as a NON-HTML (application/octet-stream) request, three ways:
#   DRORB_SPAN=11  the List twin  (deployed unconditional rewriteBytes: tokenizes EVERY body)
#   DRORB_SPAN=10  input/output dense unconditional tokenizer (rewriteBytesDense, ~2.35x cap)
#   DRORB_SPAN=13  the GATED serve (non-HTML => ZERO-COPY passthrough, body never tokenized)
# The gated serve is proven byte-identical to its own List twin (=14); on a non-HTML body it
# is DELIBERATELY not byte-identical to =10/=11 (it PRESERVES `<`/`>` the deployed corrupts).
# io_uring.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
DP_BIN="$ROOT/target/release/dataplane"
PORT="${PORT:-8080}"
SHARDS="${SHARDS:-8}"
NB="${NB:-60000}"           # large-body requests per cell
BODY_KB="${BODY_KB:-16}"    # body size (KB)
CT="${CT:-application/octet-stream}"
WORK="$(mktemp -d /tmp/gated-ab.XXXXXX)"
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$HACL_DIST}"

# A ~BODY_KB NON-HTML body that nonetheless CONTAINS markup-looking `<...>` spans, so the
# deployed unconditional tokenizer would STRIP them (corruption) while the gate passes through.
python3 - "$WORK/body.bin" "$BODY_KB" <<'PY'
import sys
path, kb = sys.argv[1], int(sys.argv[2])
target = kb * 1024
chunk = '{"k":"<b>value</b>","n":"a<i>x</i>b","note":"1 < 2 and 3 > 2"}\n'
buf = []; n = 0
while n < target:
    buf.append(chunk); n += len(chunk)
open(path, "w").write("".join(buf)[:target])
PY
echo "body: $(wc -c <"$WORK/body.bin") bytes (Content-Type: $CT), contains < and > bytes"

reqs() { awk '/Requests per second/{print $4}'; }
p99()  { awk '/^ *99%/{print $2}'; }
fail() { awk '/Failed requests/{print $3}'; }

declare -A RPS
for mode in 11 10 13; do
  case "$mode" in
    11) label="SPAN=11 List twin (deployed UNCONDITIONAL rewriteBytes: tokenizes body)";;
    10) label="SPAN=10 dense UNCONDITIONAL tokenizer (rewriteBytesDense, ~2.35x cap)";;
    13) label="SPAN=13 GATED (non-HTML => ZERO-COPY passthrough, body NEVER tokenized)";;
  esac
  echo "================================================================"
  echo "$label"
  echo "================================================================"
  DRORB_SPAN="$mode" "$DP_BIN" --bind 127.0.0.1:$PORT --io uring --shards "$SHARDS" >"$WORK/dp.$mode.log" 2>&1 &
  DP_PID=$!
  for _ in $(seq 1 80); do curl -s -o /dev/null "http://127.0.0.1:$PORT/health" && break; sleep 0.1; done
  curl -s --data-binary @"$WORK/body.bin" -H "Content-Type: $CT" \
       "http://127.0.0.1:$PORT/echo" -o "$WORK/out.$mode.bin"
  best=0
  for c in 64 128; do
    out="$(ab -k -q -n "$NB" -c "$c" -p "$WORK/body.bin" -T "$CT" "http://127.0.0.1:$PORT/echo" 2>/dev/null)"
    r="$(printf '%s' "$out" | reqs)"; p="$(printf '%s' "$out" | p99)"; f="$(printf '%s' "$out" | fail)"
    printf '  big-POST c=%-4s  %12s req/s   p99=%sms   failed=%s\n' "$c" "${r:-NA}" "${p:-NA}" "${f:-NA}"
    awk "BEGIN{exit !(${r:-0} > ${best:-0})}" && best="$r"
  done
  RPS[$mode]="$best"
  kill "$DP_PID" 2>/dev/null; wait "$DP_PID" 2>/dev/null
  sleep 0.5
done

echo "================================================================"
echo "CORRECTNESS (curl-diff): does the served body PRESERVE the < and > bytes?"
echo "================================================================"
for mode in 11 10 13; do
  lt=$(grep -c $'<' "$WORK/out.$mode.bin" 2>/dev/null; true)
  n_lt=$(tr -cd '<' <"$WORK/out.$mode.bin" | wc -c)
  n_gt=$(tr -cd '>' <"$WORK/out.$mode.bin" | wc -c)
  printf '  SPAN=%-3s served body: %6s "<"  %6s ">"   %s\n' "$mode" "$n_lt" "$n_gt" \
    "$([ "$n_lt" -gt 0 ] && echo 'PRESERVED (correct)' || echo 'STRIPPED (corrupted)')"
done
echo -n "  gated(=13) vs deployed(=11): "; cmp -s "$WORK/out.13.bin" "$WORK/out.11.bin" \
  && echo "IDENTICAL" || echo "DIFFER (expected: gated preserves markup, deployed strips it)"

echo "================================================================"
echo "RATIOS (best-of-c req/s) — the common-case zero-copy passthrough win"
echo "================================================================"
printf '  SPAN=11 (List, tokenize-every-body)   : %s req/s\n' "${RPS[11]}"
printf '  SPAN=10 (dense, tokenize-every-body)  : %s req/s\n' "${RPS[10]}"
printf '  SPAN=13 (GATED zero-copy passthrough) : %s req/s\n' "${RPS[13]}"
awk -v a="${RPS[10]}" -v b="${RPS[11]}" 'BEGIN{if(b>0)printf "  10/11 (dense tokenizer vs List)       : %.2fx\n", a/b}'
awk -v a="${RPS[13]}" -v b="${RPS[11]}" 'BEGIN{if(b>0)printf "  ★ 13/11 (GATED vs deployed List)      : %.2fx\n", a/b}'
awk -v a="${RPS[13]}" -v b="${RPS[10]}" 'BEGIN{if(b>0)printf "  ★ 13/10 (GATED vs dense tokenizer)    : %.2fx\n", a/b}'
echo "workdir: $WORK"
