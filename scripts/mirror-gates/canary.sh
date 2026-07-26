#!/usr/bin/env bash
# canary.sh — PROVE THE GATES CAN BARK.
#
# The map's §3.1 mechanism (4) is "verification apparatus is exempt from the verification standard —
# nobody audits the auditor, so the auditor drifts furthest." `check-descriptor-drift.sh` states the
# self-consistency fallacy correctly in its own header AND commits it in its by-name leg (M14). A
# mirror-gate that silently stopped firing would be that exact failure at one more level, and it
# would be invisible: a gate that reports GREEN is indistinguishable from a gate that is broken.
#
# So: for every gate, reintroduce a KNOWN mirror and require the gate to go RED naming both sites;
# remove it and require GREEN. A falsifier that was never red proves nothing.
#
# The fixtures under `canary/clean/` are a miniature of the real tree — an emitted artifact, its
# production loader, the WELDED emit gate (the compliant exemplar), a LABELED off-live-path double,
# and a single-constructor program deployed by an external crate. `canary/clean/` must be GREEN: that
# half is the false-positive test, and it is the half that decides whether this gate survives contact
# with the iterative method. Each file under `canary/mirrors/` reintroduces one real finding's shape.
#
# Runs in seconds, needs no cargo, and touches nothing outside its own temp dir — safe on a shared
# tree with other lanes live.
#
#   ./scripts/mirror-gates/canary.sh          # all gates
#   ./scripts/mirror-gates/canary.sh A1 D3    # named canaries only

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GATE="$HERE/mirror_gates.py"
CLEAN="$HERE/canary/clean"
MIRRORS="$HERE/canary/mirrors"
EMPTY_BASELINE="$(mktemp)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP" "$EMPTY_BASELINE"' EXIT

pass=0; fail=0
ok()   { printf '  \033[32mPASS\033[0m %s\n' "$1"; pass=$((pass+1)); }
bad()  { printf '  \033[31mFAIL\033[0m %s\n' "$1"; fail=$((fail+1)); }

run_gate() { # <root> <gate>  -> stdout=report, exit=gate's
  python3 "$GATE" --root "$1" --gate "$2" --baseline "$EMPTY_BASELINE" 2>&1
}

echo "mirror-gates canary — a gate that cannot bark is worse than none"
echo

# ── 0. THE FIXTURES MUST SURVIVE A FRESH CLONE ───────────────────────────────────────────────
#
# G2's fixture models an oracle directory whose `.gitignore` is a single `*` — and that `.gitignore`
# IGNORES ITSELF, so a plain `git add` never staged it. The files sat on the author's disk, the
# canary passed 20/20 locally, and CI (a fresh checkout with no `pkg/` at all) reported `G2 DID NOT
# BARK — the gate is asleep` for ten days. The gate was fine; the fixture it needed was not there.
#
# So: a fixture file that is not TRACKED does not exist as far as CI is concerned. Check it here,
# where the files are still on disk and the divergence is still visible — in CI the file is simply
# absent and there is nothing left to notice. Local-green/CI-red is the shape this closes.
if git -C "$HERE" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  untracked="$(find "$HERE/canary" -type f -print0 \
    | xargs -0 git -C "$HERE" ls-files --others --ignored --exclude-standard -- 2>/dev/null)"
  if [ -n "$untracked" ]; then
    printf '\033[31mFAIL\033[0m fixture files exist on disk but are NOT TRACKED — CI will never see them,\n'
    printf '     so the gates they arm will report "asleep" for a reason that is not the gate:\n'
    printf '%s\n' "$untracked" | sed 's/^/       /'
    printf '     Fix: git add -f the paths above (their own .gitignore may be ignoring them).\n'
    exit 1
  fi
fi

# The gate id of a mirror fixture (`A1`, `A2`, `D1`, … `G1`, `G2`) maps to the GATE to run: A1/A2
# collapse onto gate A; every other id IS its gate.
gate_of() { case "$1" in A1|A2) echo "A" ;; *) echo "$1" ;; esac; }

# ── 1. THE CLEAN TREE MUST BE GREEN (the false-positive half) ────────────────────────────────
echo "clean fixture (welded exemplar + labeled double + one constructor + welded local golden + rebuilt oracle):"
for g in A D1 D2 D3 G1 G2; do
  out="$(run_gate "$CLEAN" "$g")"; rc=$?
  if [ "$rc" -eq 0 ]; then
    ok "$g GREEN on the clean tree — no false positive"
  else
    bad "$g FALSE POSITIVE on the clean tree:"; echo "$out" | sed 's/^/        /'
  fi
done
echo

# ── 2. EACH REINTRODUCED MIRROR MUST GO RED, NAMING BOTH SITES ───────────────────────────────
#
# A mirror fixture is either a SINGLE `.rs` file (`mirrors/A1__a__b.rs` -> dropped at a/b.rs) or a
# DIRECTORY overlay (`mirrors/G1__.../` -> its whole tree copied over the clean root). The directory
# form is what G1 (a .rs golden PLUS its .json) and G2 (a whole npm package) need — a mirror is not
# always one file.
want=("${@:-}")

# expand to a newline-list of "gate_id<TAB>fixture_path<TAB>kind"
fixtures="$(
  for m in "$MIRRORS"/*.rs;  do [ -e "$m" ] && printf '%s\t%s\t%s\n' "$(basename "$m" .rs)"  "$m" file; done
  for d in "$MIRRORS"/*/;    do [ -d "$d" ] && printf '%s\t%s\t%s\n' "$(basename "$d")"       "$d" dir;  done
)"

while IFS=$'\t' read -r base m kind; do
  [ -z "$base" ] && continue
  gate_id="${base%%__*}"                 # A1 / A2 / D1 / D2 / D3 / G1 / G2
  gate="$(gate_of "$gate_id")"

  if [ -n "${1:-}" ] && ! printf '%s\n' "${want[@]}" | grep -qx "$gate_id"; then continue; fi

  root="$TMP/$base"; rm -rf "$root"; cp -R "$CLEAN" "$root"
  overlaid=()
  if [ "$kind" = file ]; then
    rel="${base#*__}"; rel="${rel//__//}.rs"
    mkdir -p "$(dirname "$root/$rel")"; cp "$m" "$root/$rel"; overlaid=("$rel")
    label="$rel"
  else
    while IFS= read -r f; do
      rel="${f#"$m"}"
      mkdir -p "$(dirname "$root/$rel")"; cp "$f" "$root/$rel"; overlaid+=("$rel")
    done < <(find "$m" -type f)
    label="$base/"
  fi

  out="$(run_gate "$root" "$gate")"; rc=$?
  if [ "$rc" -ne 0 ]; then
    # A finding must NAME BOTH SITES — the mirror and the thing it mirrors. A bark with one site is
    # a bark the reader cannot act on.
    sites="$(echo "$out" | grep -cE '^        [^ ].*:[0-9]+')"
    if [ "$sites" -ge 2 ]; then
      ok "$gate_id RED on the reintroduced mirror ($label), naming $sites sites"
      echo "$out" | grep -E '^  \[' | head -1 | cut -c1-118 | sed 's/^/        /'
      echo "$out" | grep -E '^        [^ ].*:[0-9]+' | head -3 | sed 's/^/      /'
    else
      bad "$gate_id RED but named only $sites site(s) — a finding must name the mirror AND its peer"
      echo "$out" | sed 's/^/        /'
    fi
  else
    bad "$gate_id DID NOT BARK on $label — the gate is asleep"
    echo "$out" | sed 's/^/        /'
  fi

  # ── 3. REMOVE IT: BACK TO GREEN (proves the bark is caused by the mirror, not by the fixture) ──
  for rel in "${overlaid[@]}"; do rm -f "$root/$rel"; done
  out="$(run_gate "$root" "$gate")"; rc=$?
  if [ "$rc" -eq 0 ]; then
    ok "$gate_id GREEN again once the mirror is removed"
  else
    bad "$gate_id still RED after removing the mirror — the bark was not caused by the mirror"
    echo "$out" | sed 's/^/        /'
  fi
  echo
done <<< "$fixtures"

echo "canary: $pass passed, $fail failed"
[ "$fail" -eq 0 ] || exit 1
