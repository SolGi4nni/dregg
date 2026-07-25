#!/usr/bin/env bash
# CI: materialise the PINNED mathlib as PREBUILT oleans, in the ONE directory `lake` reads.
#
# ── WHY THIS SCRIPT EXISTS (2026-07-25) ──────────────────────────────────────────────
# Three ci.yml jobs (metatheory-no-sorry, metatheory-pq-apex, descriptor-drift) each carried a
# VERBATIM copy of a "Fetch pinned mathlib4" step that cloned mathlib to
# `$GITHUB_WORKSPACE/../../src/mathlib4` (= /home/runner/work/src/mathlib4) and ran
# `lake exe cache get` THERE. That was correct only while metatheory/lakefile.toml pinned
# mathlib as `path = "../../../src/mathlib4"`, which resolved to exactly that directory.
#
# `4ccee5bd71` (2026-07-05, "make the Lean-seed cold-bootstrap portable") replaced the pin with
# a PORTABLE `git` + `rev` require. Lake resolves a git require into
# `<package>/.lake/packages/<name>` — confirmed empirically on lake 5.0.0 with a scratch package
# (`.lake/packages/Cli`) and in CI's own build log, which shows lake CLONING MATHLIB ITSELF:
#
#     info: mathlib: cloning https://github.com/leanprover-community/mathlib4
#     info: mathlib: checking out revision '1c2b90b13009c65b090d95a83c98e248deafb6f1'
#
# From that day the cache landed in a directory NOTHING READS, and every Lean CI job compiled
# the mathlib subset from source. That commit fixed scripts/bootstrap.sh for the new pin (it
# already uses the `$META/.lake/packages/mathlib` path this script uses) and did NOT touch
# ci.yml — the drift is exactly that one omission.
#
# MEASURED COST, at the boundary commit (GitHub step timings, "Zero-sorry guard"):
#     the five runs before the pin   20.9 / 23.6 / 21.9 / 21.1 / 31.0 min
#     the pin commit's OWN run       115.1 min   ← 4ccee5bd71
#     the next day's runs            106.1 / 102.2 / 99.4 / 106.4 / 111.3 min
# `4ccee5bd71` touched the pin + the seed/bootstrap scripts and NO Lean proofs, so the ~84 min
# jump is the from-source mathlib compile and nothing else. It ran on every Lean job for 20 days.
#
# ── WHAT IT DOES ─────────────────────────────────────────────────────────────────────
# Runs `lake exe cache get` FROM `metatheory/`, so lake itself decides where mathlib lives and
# mathlib's own `cache` tool extracts into THAT checkout — no path is restated here, so there is
# nothing left to drift from the lakefile. Then it asserts the two things a silent cache failure
# would hide: the oleans are present, and lake checked out the pinned rev.
#
# GREEN OR BUST: a cache miss FAILS this script. It must not fall through to a from-source
# mathlib compile that burns 90 minutes and then trips the job's step timeout.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
META="$ROOT/metatheory"
MATHLIB_DIR="$META/.lake/packages/mathlib"
MATHLIB_OLEAN="$MATHLIB_DIR/.lake/build/lib/lean/Mathlib.olean"

# Locate lake the same way scripts/axiom-hygiene-guard.sh does: CI puts elan on PATH via
# GITHUB_PATH (which only takes effect in LATER steps), dev boxes have it under ~/.elan.
if command -v lake >/dev/null 2>&1; then
    LAKE="$(command -v lake)"
elif [ -x "$HOME/.elan/bin/lake" ]; then
    LAKE="$HOME/.elan/bin/lake"
    export PATH="$HOME/.elan/bin:$PATH"
else
    echo "ci-mathlib-cache.sh: FATAL — could not find \`lake\`."
    echo "  Install elan (the metatheory/lean-toolchain toolchain) or put lake on PATH."
    exit 2
fi
echo "ci-mathlib-cache.sh: using lake at $LAKE"

# The pin's single source of truth is the 40-hex `rev` in metatheory/lakefile.toml.
WANT_REV="$(grep -oE '[0-9a-f]{40}' "$META/lakefile.toml" | head -1)"
if [ -z "$WANT_REV" ]; then
    echo "ci-mathlib-cache.sh: FATAL — no 40-hex mathlib rev found in $META/lakefile.toml."
    echo "  The mathlib require must keep an explicit \`rev = \"<sha>\"\`; a floating pin makes"
    echo "  the prebuilt-olean cache unfindable and silently reverts CI to a from-source compile."
    exit 2
fi
echo "ci-mathlib-cache.sh: lakefile mathlib pin: $WANT_REV"

# When a caller also declares MATHLIB_REV (ci.yml does, per job), require it to AGREE with the
# lakefile. Otherwise that env var is decoration: it would keep naming a rev after the lakefile
# moved, and read as a pin while pinning nothing.
if [ -n "${MATHLIB_REV:-}" ] && [ "$MATHLIB_REV" != "$WANT_REV" ]; then
    echo "ci-mathlib-cache.sh: FATAL — MATHLIB_REV disagrees with metatheory/lakefile.toml."
    echo "    MATHLIB_REV (caller):  $MATHLIB_REV"
    echo "    lakefile.toml (truth): $WANT_REV"
    echo "  Update the workflow's MATHLIB_REV, or the lakefile — they must name one rev."
    exit 1
fi

# THE FETCH. `lake exe cache get` from the metatheory package: lake resolves the git+rev
# require (cloning mathlib into .lake/packages/mathlib on a cold runner), builds mathlib's
# `cache` exe, and extracts the prebuilt oleans into that same checkout's .lake/build — the
# exact tree `lake build` then reads. Verified on lake 5.0.0 that the cache keys are
# CWD-independent: `lake exe cache lookup Mathlib.Deprecated.Aliases` names the SAME
# `<hash>.ltar` from `metatheory/` as from a mathlib checkout root.
#
# The output is STREAMED (tee), not swallowed: mathlib's own "Attempting to download N file(s)"
# / "Decompressed N file(s)" lines in the job log are the evidence that the cache was consumed.
# The whole reason this went unnoticed for 20 days is that the guard script captures `lake
# build` output to a temp file and prints only the tail on failure, so the mathlib recompile
# left NO trace in any job log.
echo "ci-mathlib-cache.sh: lake exe cache get (from $META) ..."
GETLOG="$(mktemp -t mathlib-cache-get.XXXXXX.log)"
trap 'rm -f "$GETLOG"' EXIT
( cd "$META" && "$LAKE" exe cache get ) 2>&1 | tee "$GETLOG"
get_status="${PIPESTATUS[0]}"

if [ "$get_status" -ne 0 ]; then
    echo
    echo "ci-mathlib-cache.sh: FAILED — \`lake exe cache get\` exited $get_status."
    echo "  Not proceeding: the next \`lake build\` would compile mathlib FROM SOURCE."
    exit 1
fi

# A PARTIAL miss is still a from-source compile of the missing modules, and `cache get` reports
# it as a warning with exit 0 — i.e. it is exactly the silent-degradation shape this script is
# here to refuse. Verified wording at the pinned rev, Cache/Requests.lean.
if grep -q "some files were not found in the cache" "$GETLOG"; then
    echo
    echo "ci-mathlib-cache.sh: FAILED — \`cache get\` could not find every mathlib olean for the"
    echo "  pinned rev, and it reports that as a WARNING with exit 0. The missing modules would be"
    echo "  compiled from source. Re-pin to a rev mathlib CI has fully built."
    exit 1
fi

if [ ! -f "$MATHLIB_OLEAN" ]; then
    echo
    echo "ci-mathlib-cache.sh: FAILED — no prebuilt mathlib oleans after \`cache get\`."
    echo "  expected: $MATHLIB_OLEAN"
    echo
    echo "  This is a HARD FAILURE on purpose. Without the cache, the next \`lake build\` compiles"
    echo "  the mathlib subset FROM SOURCE (~84 min measured on a hosted runner, and the Lean jobs"
    echo "  are already at their step timeout). A green-but-uncached run is the failure mode this"
    echo "  script exists to make impossible."
    echo
    echo "  Likely causes: no published cache for the pinned rev (a non-release mathlib commit),"
    echo "  or the download was blocked. Re-pin to a rev mathlib CI has built, or retry."
    exit 1
fi

GOT_REV="$(git -C "$MATHLIB_DIR" rev-parse HEAD 2>/dev/null || echo "<not a git checkout>")"
if [ "$GOT_REV" != "$WANT_REV" ]; then
    echo
    echo "ci-mathlib-cache.sh: FAILED — lake resolved mathlib to the WRONG revision."
    echo "    want: $WANT_REV  (metatheory/lakefile.toml)"
    echo "    got:  $GOT_REV   ($MATHLIB_DIR)"
    echo "  A stale packages dir or an edited lake-manifest.json will do this. The proofs would"
    echo "  then be checked against a mathlib nobody pinned."
    exit 1
fi

echo "ci-mathlib-cache.sh: ok — prebuilt mathlib oleans present at the pinned rev."
echo "  $MATHLIB_OLEAN"
exit 0
