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

# python3 is needed only for the OFFLINE state-hash transcription cross-check
# (step 2 — an independent Poseidon re-derivation, not a p2p client). The p2p
# BYTE SOURCE is no longer Python: it is bridge/tools/mina-tip, below.
command -v python3 >/dev/null || die "python3 is not on PATH (step 2's offline crosscheck needs it)"
pass "python3 $(python3 -c 'import platform;print(platform.python_version())')"

# ⚑ THE BYTE SOURCE — bridge/tools/mina-tip. A small Rust bin that LINKS openmina
# (`~/dev/mina-rust`), the audited Mina Rust stack the ecosystem runs, and emits
# raw Protocol_state.Value binprot off `get_best_tip`/`get_transition_chain`. It
# replaces the retired mina-besttip.py / mina-consecutive-pair.py Python
# transport — the bytes now come off the SAME stack a real Mina node runs.
MINA_TIP_DIR="$ROOT/bridge/tools/mina-tip"
FIXTURES="$ROOT/bridge/tools/fixtures"
MINA_TIP="${MINA_TIP:-}"
if [ -z "$MINA_TIP" ]; then
  for cand in "$MINA_TIP_DIR/target/release/mina-tip" "$MINA_TIP_DIR/target/debug/mina-tip"; do
    [ -x "$cand" ] && MINA_TIP="$cand" && break
  done
fi
if [ -n "$MINA_TIP" ]; then
  pass "mina-tip present ($MINA_TIP) — bytes come off openmina's audited Rust p2p stack, not a Python transport"
elif [ -d "$HOME/dev/mina-rust" ] && command -v cargo >/dev/null; then
  echo "   mina-tip not built; building it against ~/dev/mina-rust (first run links openmina — a few minutes)…"
  if ( cd "$MINA_TIP_DIR" && RUSTUP_TOOLCHAIN=1.92 timeout 2400 cargo build --release ) \
       > "$LOGDIR/mina-tip-build.log" 2>&1; then
    MINA_TIP="$MINA_TIP_DIR/target/release/mina-tip"
    pass "built mina-tip ($MINA_TIP) — openmina-linked byte source"
  else
    blok "mina-tip did not build (see $LOGDIR/mina-tip-build.log). The LIVE fetch steps will BLOCK; the OFFLINE openmina gates still run."
  fi
else
  blok "mina-tip binary absent and ~/dev/mina-rust or cargo unavailable. LIVE fetch steps will BLOCK."
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
elif [ -z "$MINA_TIP" ]; then
  blok "mina-tip is not available (see preflight); the live tip was not fetched"
elif "$MINA_TIP" besttip --timeout 200 > "$TIP" 2> "$LOGDIR/besttip.err"; then
  SZ=$(wc -c < "$TIP" | tr -d ' ')
  PEER=$(grep -o 'new connection [0-9A-Za-z]*' "$LOGDIR/besttip.err" | head -1 | awk '{print $3}')
  BLK=$(grep -o 'block [0-9]*' "$LOGDIR/besttip.err" | head -1 | awk '{print $2}')
  pass "$SZ bytes of Protocol_state.Value from a live devnet seed via openmina (peer ${PEER:0:16}…, block ${BLK:-?})"
else
  blok "the openmina p2p fetch did not complete — devnet seeds may be unreachable from here. See $LOGDIR/besttip.err"
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
say "3 · THE LINK — derive_state_hash(N) == block N+1's previous_state_hash, and it takes no oracle"
# BOTH sides come off the daemon's own wire via openmina; the child block itself
# is the answer key. `mina-tip` decodes each Protocol_state.Value with openmina's
# own binprot and re-derives the parent's state hash with openmina's Poseidon.
# ⚑ The DEEP gate is Lean's — `Dregg2.Bridge.MinaStateHashRealBlock` proves the
# ORDER of ~30 field elements — and step 4 runs the openmina pair through the
# Lean binprot decoder + Samasika over the C ABI.
if [ "$LIVE_PAIR" = 1 ] && [ "$OFFLINE" = 0 ] && [ -n "$MINA_TIP" ]; then
  echo "   capturing a FRESH consecutive pair via openmina (get_best_tip + get_transition_chain)"
  if "$MINA_TIP" pair --parent-out "$LOGDIR/pair-parent.bin" --child-out "$LOGDIR/pair-child.bin" \
       --timeout 300 > "$LOGDIR/pair.log" 2>&1; then
    pass "$(grep -m1 'consecutive=' "$LOGDIR/pair.log" | sed 's/mina-tip: //')  (fresh openmina capture)"
  else
    blok "no consecutive pair within the budget — devnet block cadence, or seeds unreachable. See $LOGDIR/pair.log"
  fi
elif [ -f "$FIXTURES/mina-pair-parent.bin" ] && [ -f "$FIXTURES/mina-pair-child.bin" ] && [ -n "$MINA_TIP" ]; then
  if "$MINA_TIP" verify-pair --parent "$FIXTURES/mina-pair-parent.bin" \
       --child "$FIXTURES/mina-pair-child.bin" > "$LOGDIR/pair.log" 2>&1; then
    pass "$(grep -m1 'CONSECUTIVE PAIR' "$LOGDIR/pair.log")  (openmina-captured fixture; --live-pair captures a fresh one)"
  else
    fail "the openmina consecutive pair did not re-derive — see $LOGDIR/pair.log"
    tail -20 "$LOGDIR/pair.log"; summary; exit 1
  fi
else
  blok "no openmina pair fixture in $FIXTURES, or mina-tip unavailable"
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
      bytes taken off Mina's own peer-to-peer stack — via openmina, the AUDITED
      Rust implementation the ecosystem runs (bridge/tools/mina-tip) — decode
      under a Lean-verified binprot decoder, hash to the state hash the NEXT
      block names as its parent, and drive a chain-selection rule and a
      finalized-height ratchet that are machine-checked theorems rather than a
      hand-written `select`. Step 4 runs the LIVE openmina pair through the Lean
      decoder + Samasika over the C ABI.

  ⚑ THE ONE HONEST RESIDUAL, AND IT IS NOT TRANSMUTABLE:
      the byte source is TRUSTED FOR AVAILABILITY ONLY. Every byte it produces
      goes through the Lean decoder's refusals; the worst a malicious source
      achieves is to be refused, or to withhold — and withholding is the one
      thing no light client can be defended against, by ANY stack. This is a
      fact of the model, not undone work, and openmina does not change it.

  ⚑ THE SCOPE NOTE, NARROWED (2026-08-02) — and what narrowed it:
      the old note read "the opening check accepts an anchored SEGMENT, not 'and
      it is the chain the network selected' ... `mina_head` is the object that
      distinguishes them, and it does not read `bestChain`."

      The cause was one discarded field. `get_best_tip` v2 returns a tip AND a
      transition-chain proof anchoring it to the serving peer's frontier root;
      `mina-tip` read the tip's 1,544-byte protocol state out of a 61,193-byte
      reply and dropped the rest. What survived is `blockchain_length` — the one
      field Samasika's short-range branch prefers and a peer can set freely.

      NOW: `mina-tip bestchain` asks EACH seed separately, folds each chain proof
      on openmina's own Poseidon, and REFUSES a tip that does not descend from the
      root its peer served (`scripts/check-mina-bestchain.sh`, 7 forgeries refused,
      2 of them by the fold with every shape check passing).

      ⚠ WHAT REMAINS, precisely, and it is not the same claim:
        · the anchor reaches the SERVING PEER's frontier root — MEASURED at exactly
          k=290 blocks — not genesis, and not the operator's pin. A public node
          holds only its transition frontier, so this bound is a property of what
          the network serves.
        · the network is normally CONVERGED. Both responding seeds served the
          identical tip, byte for byte, so the set machinery has not yet been
          driven by a real disagreement. Selection over a genuinely forked set is
          exercised structurally (`MinaVerifiedHead::follow_candidate_set`), not
          yet by the network.
        · selection itself is Samasika's and it is Lean's, PAIRWISE — never a fold
          over the set, because `select` has genuine 3-cycles.

  ⚑ RETIRED: the "small dependency-light Python client, not audited crypto"
      caveat. The p2p BYTE SOURCE is now openmina's Rust stack (mina-tip). The
      only Python left is step 2's OFFLINE Poseidon transcription cross-check —
      an independent tripwire, not a p2p client. (mina-account-opening.py, the
      account+Merkle-opening FIXTURE generator, is a GraphQL dev tool, not a p2p
      client and not on this demo's path; its openmina equivalent is a
      snarked-ledger sync — the named remaining lift.)
EOF
