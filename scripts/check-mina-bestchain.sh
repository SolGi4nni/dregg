#!/usr/bin/env bash
# check-mina-bestchain.sh — the light client reads THE CHAIN, not a tip.
#
# ── WHAT THIS CLOSES ───────────────────────────────────────────────────────────
# The scope note this repo has been reciting since 2026-07-30 (`bridge/demo/
# dregg-verifies-mina.sh:236-241`, `bridge/src/mina_observer.rs:46`):
#
#     "the opening check accepts an anchored SEGMENT ... not 'and it is the chain
#      the network selected'. Two k-deep segments under different anchors are
#      indistinguishable to it; `mina_head` is the object that distinguishes
#      them, and it does not read `bestChain`."
#
# The hole under that note was concrete and it was in `mina-tip`. `get_best_tip`
# v2 returns `ProofCarryingDataStableV1<Block, (List<StateBodyHash>, Block)>` —
# a tip AND a merkle-list proof anchoring it to the root of the serving peer's
# transition frontier. `main.rs` read `tip.data.header.protocol_state` and threw
# `tip.proof` away. MEASURED on devnet 2026-08-02: the reply is 87,870 bytes and
# the protocol state is 1,544 of them, so 98.2% of the evidence was discarded.
#
# What was left is the one thing a liar controls for free. Samasika's short-range
# branch prefers the longer `blockchain_length`; a peer can put any number there.
# The anchor is what costs something to forge, and it was not being read.
#
# ── WHAT THIS GATE CHECKS ──────────────────────────────────────────────────────
#   1. the committed bundle is git-TRACKED (a green on a working tree says
#      nothing about the commit)
#   2. `verify-bestchain` — every candidate's transition-chain proof folds, on
#      openmina's own Poseidon, from that peer's frontier root to the tip it
#      claims; the manifest is re-derived from the bytes and refused if it
#      disagrees; each `.ps` is the tip's own re-encoding
#   3. `verify-bestchain --self-test` — SEVEN forgeries, each of which must be
#      REFUSED, with a control (the untouched bundle must verify) and a
#      CATCHER DISCIPLINE: at least two legs must die on the POSEIDON FOLD with
#      every cheap shape check passing. A red suite whose every leg dies on an
#      integer comparison would stay green if the fold were deleted.
#
# ⚑ NO SKIPS. A missing binary that cannot be built is a FAILURE, not a BLOCKED.
# This repo has a name for gates that log and proceed and this is not one.
#
#   bash scripts/check-mina-bestchain.sh
#   bash scripts/check-mina-bestchain.sh --self-test   # the red path, on its own
#   bash scripts/check-mina-bestchain.sh --live        # + fetch a fresh set (network)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TIP_DIR="$ROOT/bridge/tools/mina-tip"
BUNDLE="$ROOT/bridge/tools/fixtures/mina-bestchain"

die() { echo "FAIL: $*" >&2; exit 1; }

SELF_TEST=0
LIVE=0
for a in "$@"; do
  case "$a" in
    --self-test) SELF_TEST=1 ;;
    --live) LIVE=1 ;;
    *) die "unknown flag: $a" ;;
  esac
done

# ── the binary ────────────────────────────────────────────────────────────────
MINA_TIP="${MINA_TIP:-}"
if [ -z "$MINA_TIP" ]; then
  for cand in "$TIP_DIR/target/release/mina-tip" "$TIP_DIR/target/debug/mina-tip"; do
    [ -x "$cand" ] && MINA_TIP="$cand" && break
  done
fi
if [ -z "$MINA_TIP" ]; then
  command -v cargo >/dev/null 2>&1 || die "no mina-tip binary and cargo is not on PATH"
  echo "  mina-tip not built; building (links openmina — a few minutes cold)…"
  ( cd "$TIP_DIR" && RUSTUP_TOOLCHAIN=1.92 timeout 2400 cargo build --release ) \
    || die "mina-tip did not build. This gate does not skip: the anchor check is the thing under test."
  MINA_TIP="$TIP_DIR/target/release/mina-tip"
fi
[ -x "$MINA_TIP" ] || die "$MINA_TIP is not executable"

# ── 1. the fixture is committed ───────────────────────────────────────────────
[ -d "$BUNDLE" ] || die "$BUNDLE does not exist — regenerate with: mina-tip bestchain --dir $BUNDLE"
[ -f "$BUNDLE/candidates.tsv" ] || die "$BUNDLE has no manifest"
untracked=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if ! git -C "$ROOT" ls-files --error-unmatch "$f" >/dev/null 2>&1; then
    echo "  ✗ $f is NOT git-tracked — a green on it proves nothing about the commit"
    untracked=$((untracked + 1))
  fi
done < <(find "$BUNDLE" -type f | sed "s|^$ROOT/||" | sort)
[ "$untracked" -eq 0 ] || die "$untracked bundle file(s) are untracked"
n_cand=$(( $(wc -l < "$BUNDLE/candidates.tsv") - 1 ))
[ "$n_cand" -ge 1 ] || die "the committed bundle holds no candidates"
echo "  ✓ committed bundle: $n_cand candidate(s), all git-tracked"

# ── 2. the anchors hold ───────────────────────────────────────────────────────
if [ "$SELF_TEST" -eq 0 ]; then
  out="$("$MINA_TIP" verify-bestchain --dir "$BUNDLE" 2>&1)" \
    || { echo "$out"; die "the committed bundle's anchors do not verify"; }
  echo "$out" | sed 's/^/    /'
fi

# ── 3. the red path ───────────────────────────────────────────────────────────
# Run ALWAYS, not only under --self-test: the headline in step 2 is a NEGATIVE
# assertion ("no candidate is unanchored"), which passes just as happily when the
# checker is broken.
out="$("$MINA_TIP" verify-bestchain --dir "$BUNDLE" --self-test 2>&1)" \
  || { echo "$out"; die "the red suite did not hold — a forgery was admitted, a leg died on the wrong check, or the control failed"; }
echo "$out" | sed 's/^/    /'

fold_legs=$(printf '%s\n' "$out" | grep -c 'REFUSED by the FOLD')
[ "$fold_legs" -ge 2 ] || die "only $fold_legs leg(s) reached the Poseidon fold; the binary's own floor is 2 and this is the second reader of it"
echo "  ✓ red suite: every forgery refused, $fold_legs of them by the Poseidon merkle-list fold"

# ── 3b. THE COVERAGE MAP ──────────────────────────────────────────────────────
# The `--self-test` run above also probes what the anchor binds AT THE BYTE LEVEL:
# it flips one bit at eight evenly-spaced offsets in each region of the encoded
# reply, re-decodes, and re-runs the anchor. A region declared BOUND must refuse
# every sample; a region declared UNBOUND must accept at least one, so "unbound"
# is a measurement rather than a region nobody probed.
#
# ⚑ Offsets are DERIVED from the binprot layout inside the binary, never
# hardcoded here. The first version of this map WAS hardcoded and broke the moment
# a block with a smaller body arrived (87,870 -> 61,193 bytes), silently pointing
# its "merkle list" probe at a Pickles proof and reporting the anchor had lost
# coverage it had never lost.
#
# ⚑ AND THE UNBOUND HALF IS CORRECT, NOT A HOLE. Mina's state hash is over the
# protocol state alone, so a merkle-list chain proof cannot bind a block body or
# its Pickles proof and does not claim to. It is surfaced because the alternative
# is a reader assuming a 61 KB object is 61 KB of evidence. Whether the tip's
# Pickles proof is valid is `mina_opening_check`'s question; whether its body is
# the ledger's is a staged-ledger sync's.
cov_lines=$(printf '%s\n' "$out" | grep -c 'COV  ' || true)
[ "$cov_lines" -ge 6 ] || die "the coverage map did not run (only $cov_lines lines) — the byte-level probe is not optional"
printf '%s\n' "$out" | grep 'COV  ' | sed 's/^mina-tip:   /    /'
echo "  ✓ coverage map: every BOUND region refused every sampled bit-flip; every UNBOUND region admitted one"

# ── 4. optional: a fresh set off the live network ─────────────────────────────
if [ "$LIVE" -eq 1 ]; then
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  if "$MINA_TIP" bestchain --dir "$tmp/set" --timeout 300 > "$tmp/live.log" 2>&1; then
    grep -E '^(CANDIDATE SET|  cand-)' "$tmp/live.log" | sed 's/^/    /'
    "$MINA_TIP" verify-bestchain --dir "$tmp/set" --self-test > "$tmp/live-red.log" 2>&1 \
      || { cat "$tmp/live-red.log"; die "the FRESH set did not survive its own red suite"; }
    echo "  ✓ live: a fresh candidate set was fetched, anchored and survived the red suite"
  else
    tail -5 "$tmp/live.log"
    die "the live fetch produced no anchor-verified candidate (devnet seeds unreachable, or every peer served an unanchored tip)"
  fi
fi

echo
echo "== MINA BESTCHAIN: the candidate set is ANCHORED, and the anchor can go RED =="
echo "   ⚠ SCOPE, and it is a property of what the network serves, not of this code:"
echo "     each anchor reaches the SERVING PEER's frontier root — MEASURED at exactly"
echo "     k=290 blocks on devnet — not genesis. 'This tip descends from a block this"
echo "     peer also serves' is what an anchor buys. Reaching the operator's"
echo "     weak-subjectivity pin needs more than one hop, and a public node does not"
echo "     hold more than its transition frontier."
exit 0
