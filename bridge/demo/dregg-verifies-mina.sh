#!/usr/bin/env bash
# dregg-verifies-mina.sh — ONE COMMAND: dregg verifies Mina.
#
#   bridge/demo/dregg-verifies-mina.sh          # live wire + offline gates
#   bridge/demo/dregg-verifies-mina.sh --live-pair   # + capture a FRESH consecutive
#                                                    #   pair off the network (up to 25 min)
#   bridge/demo/dregg-verifies-mina.sh --offline     # no network at all
#
# The direction: dregg reads Mina's real protocol — not a block explorer's JSON,
# not a `bestChain` query answered by a server that could lie. Bytes come off the
# peer-to-peer wire; the decode, the chain-selection rule and the head ratchet
# are the LEAN artifact's, and Rust only hex-encodes and reads a verdict string.
#
# ── THE REGISTER ───────────────────────────────────────────────────────────
#   PASS     it ran and the thing it checks held.
#   FAIL     it ran and did not hold. The run stops.
#   BLOCKED  an INPUT or an ARTIFACT is absent — named, never defaulted.
#
# ── WHAT IT TOUCHES ────────────────────────────────────────────────────────
# Read-only. It opens a TCP connection to a public Mina devnet seed and speaks
# the protocol; it sends no transaction, holds no key, and spends nothing. There
# is no `--broadcast` here because there is nothing to broadcast: this direction
# is a client READING a chain.
#
# ⚑ NO CREDENTIAL EXISTS FOR ANY STEP. The chain-id pre-shared key the p2p
# handshake needs is a public devnet constant, and the helper mints ephemeral
# session keys per run.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
TOOLS="$ROOT/bridge/tools"

LIVE_PAIR=0
OFFLINE=0
for a in "$@"; do
  case "$a" in
    --live-pair) LIVE_PAIR=1 ;;
    --offline)   OFFLINE=1 ;;
    -h|--help)
      sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *) echo "unknown flag: $a (see --help)" >&2; exit 2 ;;
  esac
done

LOGDIR="${DEMO_LOGDIR:-$(mktemp -d "${TMPDIR:-/tmp}/dregg-verifies-mina.XXXXXX")}"
mkdir -p "$LOGDIR"

STEPS=()
say()  { printf '\n\033[1m── %s\033[0m\n' "$*"; }
pass() { STEPS+=("PASS|$1"); printf '   \033[32mPASS\033[0m  %s\n' "$1"; }
fail() { STEPS+=("FAIL|$1"); printf '   \033[31mFAIL\033[0m  %s\n' "$1"; }
blok() { STEPS+=("BLOCKED|$1"); printf '   \033[33mBLOCKED\033[0m  %s\n' "$1"; }
summary() {
  printf '\n\033[1m════ DREGG VERIFIES MINA — SUMMARY ════\033[0m\n'
  for s in "${STEPS[@]}"; do printf '  %-10s %s\n' "${s%%|*}" "${s#*|}"; done
  printf '\n  transcripts: %s\n\n' "$LOGDIR"
}
die() { fail "$1"; summary; exit 1; }

CARGO_FLAGS=(--release -p dregg-bridge)

# ===========================================================================
say "0 · PREFLIGHT"

command -v python3 >/dev/null || die "python3 is not on PATH"
if python3 -c 'import cryptography' 2>/dev/null; then
  pass "python3 $(python3 -c 'import platform;print(platform.python_version())') with cryptography $(python3 -c 'import cryptography;print(cryptography.__version__)')"
else
  die "python3 has no \`cryptography\` — the Noise XX handshake needs it. pip install cryptography"
fi

# The Lean archive is what the decode, the selection rule and the ratchet ARE.
# Absent, the Rust side fails closed and every gated step below is BLOCKED, not
# skipped — a client that cannot run the rule must not report that it ran.
ARCHIVE="$ROOT/dregg-lean-ffi/libdregg_lean.a"
if [ -f "$ARCHIVE" ]; then
  pass "Lean archive present ($(du -h "$ARCHIVE" | cut -f1)) — the decode and the selection rule are the VERIFIED ones"
  HAVE_ARCHIVE=1
else
  blok "dregg-lean-ffi/libdregg_lean.a absent. Without it \`dregg_mina_head_advance\`/\`dregg_mina_better_tip\` are not linked, the client fails closed, and the Rust steps below cannot be attributable. Build with: scripts/fetch-lean-seed.sh"
  HAVE_ARCHIVE=0
fi

# ===========================================================================
say "1 · THE LIVE WIRE — a best tip off Mina devnet's peer-to-peer stack"
# ⚑ NOT AN API. TCP -> pnet (XSalsa20 under the chain-id PSK) -> multistream
# -> Noise_XX_25519_ChaChaPoly_SHA256 -> /coda/yamux/1.0.0 -> coda/rpcs/0.0.1
# -> get_best_tip v2. What comes back is a block header a validator signed, not
# a JSON document a server composed.
TIP="$LOGDIR/tip.bin"
if [ "$OFFLINE" = 1 ]; then
  blok "--offline: the live tip was not fetched"
elif MINA_BESTTIP_OUTDIR="$LOGDIR" timeout 240 python3 "$TOOLS/mina-besttip.py" --emit-protocol-state \
       > "$TIP" 2> "$LOGDIR/besttip.err"; then
  SZ=$(wc -c < "$TIP" | tr -d ' ')
  PEER=$(grep -o 'remote ed25519 identity=[0-9a-f]*' "$LOGDIR/besttip.err" | head -1 | cut -d= -f2)
  pass "$SZ bytes of Protocol_state.Value from a live devnet seed (peer ${PEER:0:16}…)"
else
  blok "the p2p fetch did not complete — devnet seeds may be unreachable from here. See $LOGDIR/besttip.err"
fi

# ===========================================================================
say "2 · THE TRANSCRIPTION — do we read those bytes the way Mina hashes them?"
# Offline, no oracle, seconds. Walks a real captured block's 38 field elements
# and ~819 packed chunks and recomputes its state hash. A typo tripwire over the
# packing, which is where a hand transcription of another protocol's hash goes
# wrong silently.
if timeout 600 python3 "$TOOLS/mina-state-hash-crosscheck.py" > "$LOGDIR/crosscheck.log" 2>&1; then
  H=$(grep -m1 'state_hash(' "$LOGDIR/crosscheck.log" | sed 's/  */ /g')
  pass "state-hash transcription reproduces the pinned block  [$H]"
  grep -E 'blockchain_length|field elements|max packed chunk' "$LOGDIR/crosscheck.log" | sed 's/^/     /'
else
  fail "the state-hash crosscheck did not reproduce the pinned values — see $LOGDIR/crosscheck.log"
  tail -20 "$LOGDIR/crosscheck.log"; summary; exit 1
fi

# ===========================================================================
say "3 · THE LINK — the strongest gate available, and it takes no oracle"
# `derive_state_hash(block N) == block N+1's previous_state_hash`, with BOTH
# sides read off the daemon's own wire. Nothing is asked of any server: the
# child block itself is the answer key.
PAIRSRC="$ROOT/metatheory/Dregg2/Bridge/MinaStateHashRealBlock.lean"
if [ "$LIVE_PAIR" = 1 ] && [ "$OFFLINE" = 0 ]; then
  echo "   capturing a FRESH pair off the network (devnet blocks are ~3 min apart; up to 25 min)"
  if timeout 1800 python3 "$TOOLS/mina-consecutive-pair.py" --out "$LOGDIR/pair.lean" \
       > "$LOGDIR/pair.log" 2>&1; then
    pass "$(grep -m1 'CONSECUTIVE PAIR' "$LOGDIR/pair.log" | sed 's/\[pair\] //')  — $(grep -m1 'python rendering says' "$LOGDIR/pair.log" | sed 's/.*says: //')"
  else
    blok "no consecutive pair within the budget — devnet block cadence. See $LOGDIR/pair.log"
  fi
elif [ -f "$PAIRSRC" ]; then
  if timeout 600 python3 "$TOOLS/mina-consecutive-pair.py" --from-lean "$PAIRSRC" \
       --out "$LOGDIR/pair-replay.lean" > "$LOGDIR/pair.log" 2>&1; then
    pass "$(grep -m1 'CONSECUTIVE PAIR' "$LOGDIR/pair.log" | sed 's/\[pair\] //')  — $(grep -m1 'python rendering says' "$LOGDIR/pair.log" | sed 's/.*says: //')  (replayed from the captured pair; --live-pair captures a fresh one)"
  else
    fail "the captured pair did not re-derive — see $LOGDIR/pair.log"
    tail -20 "$LOGDIR/pair.log"; summary; exit 1
  fi
else
  blok "no captured pair at $PAIRSRC and --live-pair not given"
fi

# ===========================================================================
say "4 · FORK CHOICE AND THE RATCHET — Samasika's rule, and it is Lean's"
# ⚑ PAIRWISE, NEVER A FOLD. `beats_not_transitive` proves genuine 3-cycles at
# real Mina constants, so a `max_by` over a candidate set is order-dependent and
# therefore exploitable. `MinaVerifiedHead::offer` presents ONE candidate against
# the CURRENT head, and the finalized height is a ratchet Rust re-checks.
if command -v cargo >/dev/null; then
  if timeout 3600 cargo test "${CARGO_FLAGS[@]}" --lib mina_head > "$LOGDIR/mina_head.log" 2>&1; then
    R=$(grep -m1 'test result' "$LOGDIR/mina_head.log" || echo '')
    pass "mina_head — $R"
  else
    fail "mina_head tests — see $LOGDIR/mina_head.log"
    tail -30 "$LOGDIR/mina_head.log"; summary; exit 1
  fi
else
  blok "cargo is not on PATH"
fi

# ===========================================================================
say "5 · THE OPENING CHECK — a real devnet block's Wrap proof, in dregg's AIR"
# The header binding runs FIRST and is a verified Lean gate: public-input words
# 11 and 12 are recomputed from the SERVED stateHash and the served proof bytes,
# so a proof re-labelled under a foreign header is refused BEFORE any prover
# runs. Then the opening check itself proves and verifies.
if [ "$HAVE_ARCHIVE" = 0 ]; then
  blok "needs the Lean archive (the example exits 2 without \`mina_state_hash_word_ok\`)"
elif command -v cargo >/dev/null; then
  if timeout 5400 cargo run "${CARGO_FLAGS[@]}" --example mina_opening_check --features test-utils \
       > "$LOGDIR/opening.log" 2>&1; then
    pass "opening check proved and verified on a real devnet block"
    grep -E '^(ok|OK|PASS|===|  )' "$LOGDIR/opening.log" | tail -12 | sed 's/^/     /'
  else
    fail "the opening check did not complete — see $LOGDIR/opening.log"
    tail -30 "$LOGDIR/opening.log"; summary; exit 1
  fi
else
  blok "cargo is not on PATH"
fi

# ===========================================================================
summary
cat <<'EOF'
  ⚑ WHAT THIS DIRECTION ESTABLISHES:
      bytes taken off Mina's own peer-to-peer stack decode under a Lean-verified
      binprot decoder, hash to the state hash the NEXT block names as its parent,
      and drive a chain-selection rule and a finalized-height ratchet that are
      machine-checked theorems rather than a hand-written `select`.

  ⚑ AND WHAT IT DOES NOT:
      * the opening check accepts an anchored SEGMENT — "this exhibited segment
        is anchored, linked, canonical and k deep" — not "and it is the chain
        the network selected". Two k-deep segments under different anchors are
        indistinguishable to it; `mina_head` is the object that distinguishes
        them, and it does not read `bestChain`.
      * the p2p helper is TRUSTED FOR AVAILABILITY ONLY. Every byte it produces
        goes through the Lean decoder's refusals; the worst a malicious helper
        achieves is to be refused, or to withhold — and withholding is the one
        thing no light client can be defended against.
      * the helper is a small dependency-light Python client, not audited crypto
        and not a production path. openmina is the maintained Rust
        implementation of the same stack and is what to link when this leaves
        `bridge/tools/`.
EOF
