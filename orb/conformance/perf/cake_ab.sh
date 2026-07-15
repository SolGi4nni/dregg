#!/usr/bin/env bash
# A/B: compiled machine-code serve vs the leanc-compiled serve, SAME binary,
# SAME route (GET /), SAME box, SAME load. Toggled by DRORB_CAKE_SERVE.
#
#   (a) leanc serve  : DRORB_CAKE_SERVE unset  -> the deployed leanc pipeline
#   (b) cake serve   : DRORB_CAKE_SERVE=1      -> the compiled export-function
#                      machine code answers GET / in-process
#
# HONEST FRAMING (read before trusting a number):
#  * Loopback lies for ABSOLUTE req/s. Only the RATIO (cake/leanc) and the
#    allocation deltas are reported, never a headline req/s.
#  * The two paths are NOT byte-identical on GET /: the leanc pipeline has no
#    "/" route so it returns a full-header 404; the compiled path returns a
#    308 redirect. So the req/s ratio reflects BOTH the serve-machinery delta
#    AND a response-shape difference (leanc writes ~13 headers, cake ~3). It is
#    a directional "not slower" check, not a clean isolate. The robust,
#    load-independent signal is the STATIC allocation contrast printed at the end.
#  * Single route, single owner thread, 9/14 fused stages. See residuals.
set -u

ROOT="${ROOT:-$HOME/dev/drorb}"
BIN="$ROOT/target/release/dataplane"
CAKE_DIR="$ROOT/crates/dataplane/ffi/cake"
PORT="${PORT:-18990}"
SHARDS="${SHARDS:-4}"
N="${N:-300000}"     # requests per ab cell
C="${C:-64}"         # concurrency
ROUTE="/"
URL="http://127.0.0.1:$PORT$ROUTE"

export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="${LIBRARY_PATH:-$HACL_DIST}"
LEAN_LIB="$(echo $HOME/.elan/toolchains/*/lib/lean 2>/dev/null | awk '{print $1}')"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$HACL_DIST}:$LEAN_LIB"

WORK="$(mktemp -d /tmp/cake-ab.XXXXXX)"
echo "workdir: $WORK"
echo "binary : $BIN"
echo "route  : GET $ROUTE   load: -k -n $N -c $C   shards: $SHARDS   port: $PORT"
echo

reqs() { awk '/Requests per second/{print $4}'; }
p99()  { awk '/^ *99%/{print $2}'; }
fail() { awk '/Failed requests/{print $3}'; }
comp() { awk '/Complete requests/{print $3}'; }
non2() { awk '/Non-2xx responses/{print $3}'; }
perfval() { awk -v k="$1" '$0 ~ k {gsub(/,/,"",$1); print $1; exit}' "$2"; }

declare -A RPS P99 INSN MINF TCLK PROV COMP NON2 CLEN CONN WELLFORMED

runmode() {  # tag  envassign
  local tag="$1" envassign="$2"
  echo "================================================================"
  echo "MODE: $tag   ($envassign)"
  echo "================================================================"
  env $envassign "$BIN" --bind 127.0.0.1:$PORT --io uring --shards "$SHARDS" \
      >"$WORK/dp.$tag.log" 2>&1 &
  local pid=$!
  # wait for readiness
  local up=0
  for _ in $(seq 1 100); do
    curl -s -o /dev/null "http://127.0.0.1:$PORT/health" && { up=1; break; }
    sleep 0.1
  done
  if [ "$up" != 1 ]; then echo "  FAILED to come up; log:"; tail -5 "$WORK/dp.$tag.log"; kill $pid 2>/dev/null; return 1; fi

  # capture the exact served response for the route
  curl -s -D "$WORK/hdr.$tag" "$URL" -o "$WORK/body.$tag"
  local status; status="$(head -1 "$WORK/hdr.$tag" | tr -d '\r')"
  local nresp; nresp="$(( $(wc -c <"$WORK/hdr.$tag") + $(wc -c <"$WORK/body.$tag") ))"
  echo "  served: $status   (~$nresp bytes over the wire: $(wc -c <"$WORK/hdr.$tag") hdr + $(wc -c <"$WORK/body.$tag") body)"

  # FRAMING validity: a well-formed keep-alive HTTP response needs a length
  # delimiter (Content-Length or chunked) and must not force Connection: close.
  CLEN[$tag]="$(grep -ic 'content-length' "$WORK/hdr.$tag")"
  CONN[$tag]="$(grep -i '^connection:' "$WORK/hdr.$tag" | tr -d '\r' | awk '{print $2}' | head -1)"
  if [ "${CLEN[$tag]}" -ge 1 ] && [ "${CONN[$tag]}" != "close" ]; then
    WELLFORMED[$tag]="yes"
  else
    WELLFORMED[$tag]="NO (Content-Length present=${CLEN[$tag]}, Connection=${CONN[$tag]:-none})"
  fi
  echo "  framing: keep-alive-benchmarkable = ${WELLFORMED[$tag]}"

  # warmup
  ab -k -q -n 20000 -c "$C" "$URL" >/dev/null 2>&1

  # measured run under perf stat attached to the SERVER pid for the ab window
  local perfout="$WORK/perf.$tag"
  perf stat -p "$pid" -e instructions,minor-faults,task-clock -o "$perfout" -- \
     ab -k -q -n "$N" -c "$C" "$URL" >"$WORK/ab.$tag" 2>/dev/null

  RPS[$tag]="$(reqs <"$WORK/ab.$tag")"; RPS[$tag]="${RPS[$tag]:-ABORTED}"
  P99[$tag]="$(p99 <"$WORK/ab.$tag")"
  COMP[$tag]="$(comp <"$WORK/ab.$tag")"; COMP[$tag]="${COMP[$tag]:-?}"
  NON2[$tag]="$(non2 <"$WORK/ab.$tag")"; NON2[$tag]="${NON2[$tag]:-0}"
  local nf; nf="$(fail <"$WORK/ab.$tag")"
  INSN[$tag]="$(perfval instructions "$perfout")"
  MINF[$tag]="$(perfval minor-faults "$perfout")"
  TCLK[$tag]="$(perfval task-clock "$perfout")"
  PROV[$tag]="$(grep -c 'certified export-function machine' "$WORK/dp.$tag.log" 2>/dev/null || echo 0)"

  printf '  req/s=%s  p99=%sms  completed=%s  non-2xx=%s  length-failed=%s\n' \
     "${RPS[$tag]}" "${P99[$tag]}" "${COMP[$tag]}" "${NON2[$tag]}" "$nf"
  printf '  server-side over the ab window: instructions=%s  minor-faults=%s  task-clock(ms)=%s\n' \
     "${INSN[$tag]}" "${MINF[$tag]}" "${TCLK[$tag]}"
  # per-request derived
  awk -v i="${INSN[$tag]}" -v n="$N" 'BEGIN{if(n>0)printf "  -> instructions/request = %.0f\n", i/n}'
  awk -v m="${MINF[$tag]}" -v n="$N" 'BEGIN{if(n>0)printf "  -> minor-faults/request = %.5f\n", m/n}'
  echo "  cake-provenance lines in server log: ${PROV[$tag]}"
  echo

  kill "$pid" 2>/dev/null; wait "$pid" 2>/dev/null
  sleep 0.5
}

runmode leanc ""
runmode cake  "DRORB_CAKE_SERVE=1"

echo "================================================================"
echo "RESPONSE DIVERGENCE (the honesty caveat, made loud)"
echo "================================================================"
echo -n "  leanc GET / : "; head -1 "$WORK/hdr.leanc" | tr -d '\r'
echo -n "  cake  GET / : "; head -1 "$WORK/hdr.cake"  | tr -d '\r'
if cmp -s "$WORK/hdr.leanc" "$WORK/hdr.cake"; then echo "  headers: IDENTICAL"; else echo "  headers: DIFFER (leanc 404 full-header vs cake 308 redirect) -> req/s ratio is confounded by response shape"; fi
echo

echo "================================================================"
echo "DYNAMIC A/B RATIO (loopback: ratio only, never absolute)"
echo "================================================================"
if [ "${RPS[leanc]}" = "ABORTED" ] || [ "${RPS[cake]}" = "ABORTED" ]; then
  echo "  req/s ratio: UNAVAILABLE — one side ab-aborted (socket reset under flood)."
else
  awk -v a="${RPS[cake]}" -v b="${RPS[leanc]}" 'BEGIN{if(b>0)printf "  cake/leanc req/s (RAW, confounded): %.3fx\n", a/b}'
fi
awk -v a="${INSN[cake]:-0}" -v b="${INSN[leanc]:-0}" 'BEGIN{if(a>0)printf "  leanc/cake instr over ab window   : %.3fx  (confounded: response shape + Conn:close TCP churn)\n", b/a}'
echo "  minor-faults over ab window: cake=${MINF[cake]:-?}  leanc=${MINF[leanc]:-?}"
echo

echo "================================================================"
echo "GATE VERDICT: is the cake serve <= leanc?  (HONEST)"
echo "================================================================"
gate_block=0
[ "${WELLFORMED[cake]}" != "yes" ] && { echo "  BLOCKED: cake response is not keep-alive-benchmarkable (${WELLFORMED[cake]})."; gate_block=1; }
[ "${NON2[leanc]:-0}" -gt 1000 ] 2>/dev/null && { echo "  BLOCKED: leanc comparand rate-limited/reset the flood (non-2xx=${NON2[leanc]})."; gate_block=1; }
cmp -s "$WORK/hdr.leanc" "$WORK/hdr.cake" || { echo "  CAVEAT: leanc and cake produce DIFFERENT responses on GET / — not a byte-isolated A/B."; }
if [ "$gate_block" = 1 ]; then
  echo
  echo "  ==> The DYNAMIC gate CANNOT be certified yet. The req/s figures above"
  echo "      measure connection churn + framing failures + rate-limiting, NOT the"
  echo "      allocation thesis. Fix the serve-integration residuals (R1-R4 below),"
  echo "      then re-run for a fair keep-alive, byte-equal A/B."
  echo
  echo "  ==> The STATIC leg of the thesis DOES hold: the emitted serve is"
  echo "      allocation-free by construction (see contrast below)."
fi
echo

echo "================================================================"
echo "STATIC by-construction allocation contrast (load-INDEPENDENT truth)"
echo "================================================================"
echo "  compiled serve object ($CAKE_DIR/serve.o):"
echo -n "    external symbol deps (U): "; nm "$CAKE_DIR/serve.o" | awk '/ U /{printf "%s ", $2}'; echo
echo -n "    malloc/free/lean_* refs : "; nm "$CAKE_DIR/serve.o" | grep -icE "alloc|malloc|lean_|free" ;
echo "    -> the emitted machine code touches NO allocator: the response bytes"
echo "       are produced by the compiled fold, not heap objects."
echo
echo "  leanc serve (libdrorb.a, whole lib):"
echo -n "    lean_alloc/lean_dec/lean_inc undefined refs: "; nm "$ROOT/.lake/build/lib/libdrorb.a" 2>/dev/null | grep -cE "U lean_(alloc|dec|inc)"
echo "    -> the leanc pipeline threads reference-counted lean_object* through"
echo "       the fold: lean_alloc on construct, lean_dec_ref/lean_free on drop."
echo
echo "  RESIDUAL (measured, not swept): the per-request C DRIVER"
echo "  ($CAKE_DIR/cake_serve_ffi.c) currently calloc()s 32KB+4KB+4KB scratch"
echo "  and free()s it PER CALL:"
grep -nE "calloc|free\(" "$CAKE_DIR/cake_serve_ffi.c" | sed 's/^/      /'
echo
echo "================================================================"
echo "RESIDUALS to close before the DYNAMIC perf story can start"
echo "================================================================"
echo "  R1  serialize: GET / returns a MALFORMED response (308, no Content-Length,"
echo "      ~140 trailing scratch-ramp bytes past the ~93-byte head; n=233 too long)."
echo "      Fix serialize_stage length + the driver out-length so the response is"
echo "      well-formed."
echo "  R2  connection: the response forces Connection: close -> no keep-alive."
echo "      Emit/inherit keep-alive so sustained load is possible."
echo "  R3  driver alloc: latch ctrl/rbuf/obuf ONCE on the owner thread (like the"
echo "      process-global heap region g_region) -> kill the per-request calloc so"
echo "      the path is allocation-free END-TO-END, not just in the emitted code."
echo "  R4  comparand: provide a byte-EQUAL, non-metered leanc serve for GET / and"
echo "      run it with the rate-limiter bypassed, so the A/B isolates serve"
echo "      MACHINERY instead of comparing a 404 vs a malformed 308."
echo
echo "workdir: $WORK  (logs, headers, bodies, perf.* kept)"
