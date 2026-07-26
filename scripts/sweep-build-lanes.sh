#!/usr/bin/env bash
# sweep-build-lanes.sh — reclaim SUPERSEDED cargo artifacts from remote build lanes,
# PER LANE, without ever needing the swarm to be quiet.
#
# ── WHY THIS EXISTS, AND WHY IT IS NOT reclaim-space.sh ────────────────────────
# `scripts/reclaim-space.sh --clean` deletes whole `target/` dirs, so its own header
# warns: "RACES ACTIVE BUILDS: Run it when the swarms are quiet." Measured 2026-07-25,
# that precondition is unsatisfiable — ~10 concurrent terminals driving ~420 subagents
# means no moment exists when every lane is idle. So the one cleanup tool in the repo
# could never legitimately run, and persvati's `~/dregg-build` reached **611 GB across
# 18 lanes** (crewbraid 293G + darkpool 248G = 88% of it) on a disk that had already
# hit 100% once, taking a lane down with `couldn't create a temp dir: No space left on
# device`.
#
# Two changes make cleanup routine instead of heroic:
#
#   1. PER-LANE LIVENESS, not global quiescence. Each lane dir is independent, so a
#      lane with no build running can be swept while every other lane builds. That
#      turns "wait for a quiet box" (never) into "wait for a quiet lane" (often).
#
#   2. DELETE SUPERSEDED GENERATIONS, not whole targets. cargo names artifacts
#      `<crate>-<16 hex>` where the hash keys package+features+profile+deps. When
#      Cargo.lock or a feature set moves — 30 times in the week to 2026-07-25 — the
#      old hash is orphaned FOREVER: never reused, never collected. Deleting an
#      orphan generation cannot produce a wrong build; a fingerprint miss is a
#      rebuild, never a silent stale link. Verified on darkpool: swept 171.7 GB /
#      14,323 files, then `cargo check -p dregg-types` finished in 8.55s.
#
# Measured orphan share (2026-07-25, correct two-phase classification):
#   darkpool   KEEP  57.0 GB /  6,053 files   ORPHAN 171.7 GB / 14,323 files
#   crewbraid  KEEP 114.2 GB /  6,134 files   ORPHAN 166.8 GB / 25,642 files
# i.e. roughly THREE QUARTERS of a mature lane is superseded generations.
#
#   scripts/sweep-build-lanes.sh                      # report every lane, delete nothing
#   scripts/sweep-build-lanes.sh --apply              # sweep every IDLE lane
#   scripts/sweep-build-lanes.sh --lane crewbraid --apply
#   scripts/sweep-build-lanes.sh --host hbox --apply
#
# ⚠⚠ KNOWN GAP, FOUND BY DOING IT TO MYSELF (2026-07-25): PROCESS-ABSENCE IS NOT LANE-OWNERSHIP.
# `live_count` looks for cargo/rustc/lake/lean/cc/ld attributed to the lane. An agent that OWNS a
# lane spends most of its wall-clock *not compiling* — reading files, thinking, writing a report. In
# that window the lane reads idle and this script will sweep it. I swept `darkpool` and
# `native-anchor` out from under two of my own live agents exactly that way.
#
# It is not corruption — a fingerprint miss is a rebuild, never a stale link (that is the whole
# safety argument of this tool). But it makes the owning agent pay a rebuild it did not expect, and
# if the sweep lands during a LINK the failure surfaces inside that agent as an unexplained error it
# may well misdiagnose as its own bug. That is the expensive kind of wrong.
#
# THE FIX IS A LEASE, NOT A BETTER PROBE. No amount of process sniffing can see intent. A lane
# should carry a claim file (`<lane>/.pbuild-lease` with owner + expiry, refreshed by pbuild on each
# call) and this script should refuse any lane holding an unexpired lease, regardless of what is
# running. `cv board claim` already implements exactly this shape for tasks and is unused here.
# Until that exists: pass --lane explicitly for lanes you know are unowned, rather than trusting a
# bare --apply to leave live agents alone.
#
# ⚠ A LIVE LANE IS SKIPPED, NOT SWEPT, and the reason is not politeness. Two builds
#   of DIFFERENT configs in one lane (e.g. `cargo test -p X --lib` beside
#   `cargo check -p Y --all-targets`) legitimately hold DIFFERENT hashes of the same
#   crate at the same time. "Keep the newest hash per crate" would delete the other
#   one's live input. So liveness is a correctness precondition for this rule, not a
#   courtesy — which is exactly why the guard below is written to fail CLOSED.
set -euo pipefail

HOST="${SWEEP_HOST:-persvati}"
APPLY=0
LANES=()
MIN_GB="${SWEEP_MIN_GB:-1}"

while [ $# -gt 0 ]; do
  case "$1" in
    --host)   HOST="$2"; shift 2 ;;
    --lane)   LANES+=("$2"); shift 2 ;;
    --apply)  APPLY=1; shift ;;
    --min-gb) MIN_GB="$2"; shift 2 ;;
    -h|--help) sed -n '2,48p' "$0"; exit 0 ;;
    *) echo "sweep-build-lanes: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

case "$MIN_GB" in ''|*[!0-9]*) echo "sweep-build-lanes: --min-gb must be an integer" >&2; exit 2 ;; esac

if ! ssh -o BatchMode=yes -o ConnectTimeout=8 "$HOST" true 2>/dev/null; then
  echo "sweep-build-lanes: cannot reach '$HOST'." >&2
  exit 2
fi

LANE_FILTER=""
if [ "${#LANES[@]}" -gt 0 ]; then LANE_FILTER="$(printf '%s\n' "${LANES[@]}")"; fi

# Everything below runs on the remote in ONE shell, so liveness is checked in the same
# process that does the deleting — no window between the check and the rm.
# shellcheck disable=SC2087 # APPLY/MIN_GB/LANE_FILTER are locally owned and validated.
ssh "$HOST" "bash -s" <<REMOTE
set -uo pipefail
APPLY=${APPLY}
MIN_BYTES=\$(( ${MIN_GB} * 1073741824 ))
LANE_FILTER='${LANE_FILTER}'

# ── LIVENESS, FAIL-CLOSED ─────────────────────────────────────────────────────
# Counts only REAL build processes (cargo/rustc/lake/lean/cc/ld) attributed to the
# lane by cwd or by cmdline. Deliberately NOT \`pgrep -f "dregg-build/\$L"\`: that
# form matches the probing shell's OWN command line (it contains the lane name), so
# it both false-positives and — paired with \`pgrep -c || echo 0\`, which prints "0"
# twice because pgrep exits 1 on an empty match — silently FAILS OPEN. That bug was
# live in the first version of this sweep on 2026-07-25 and only did no damage
# because the lane really was idle. A guard that cannot say no is not a guard.
live_count() {
  L="\$1"; c=0
  for p in \$(pgrep -x cargo 2>/dev/null; pgrep -x rustc 2>/dev/null; \
              pgrep -x lake 2>/dev/null; pgrep -x lean 2>/dev/null; \
              pgrep -x cc 2>/dev/null; pgrep -x ld 2>/dev/null); do
    d=\$(readlink -f "/proc/\$p/cwd" 2>/dev/null || true)
    case "\$d" in *"dregg-build/\$L"*) c=\$((c+1)); continue ;; esac
    # A process can exit between pgrep and this read. The failure is then reported by
    # the SHELL (a redirect on a vanished path), so \`tr … 2>/dev/null\` cannot mute it —
    # the whole compound needs the redirect. Guard with -r as well so the common case
    # never enters an error path at all.
    [ -r "/proc/\$p/cmdline" ] || continue
    if { tr '\0' ' ' < "/proc/\$p/cmdline" || true; } 2>/dev/null | grep -q "dregg-build/\$L"; then
      c=\$((c+1))
    fi
  done
  echo "\$c"
}

cat > /tmp/sweep-orphans.awk <<'AWK'
# TWO-PHASE. Classification happens only in END, after every hash for every crate
# has been seen. A streaming "is this the newest so far" test is order-dependent and
# gets the answer wrong in BOTH directions — it over-counted orphans by 4x and
# under-counted by 9x on two passes over the same tree before this was fixed.
{ ts=\$1+0; sz=\$2+0; p=\$3; f=\$4;
  stem=f; sub(/\.(d|rlib|rmeta|so|a|dylib)\$/,"",stem);
  if (!match(stem,/-[0-9a-f]{16}\$/)) next;   # not a fingerprinted artifact; leave it
  h=substr(stem,RSTART+1); stem=substr(stem,1,RSTART-1);
  key=stem "|" h;
  if (ts>hts[key]) hts[key]=ts;
  hsz[key]+=sz; hn[key]++; stemof[key]=stem; paths[key]=paths[key] p "\n";
}
END {
  for (k in hsz) { s=stemof[k]; if (!(s in smax) || hts[k]>smax[s]) smax[s]=hts[k] }
  for (k in hsz) {
    s=stemof[k];
    if (hts[k] < smax[s]) { osz+=hsz[k]; on+=hn[k]; if (LIST) printf "%s", paths[k] }
    else { ksz+=hsz[k]; kn+=hn[k] }
  }
  printf "%d %d %d %d\n", ksz, kn, osz, on > "/dev/stderr"
}
AWK

printf '%-24s %10s %10s %10s   %s\n' LANE KEEP ORPHAN TOTAL STATUS
swept_total=0
for dir in ~/dregg-build/*/; do
  [ -d "\$dir" ] || continue
  L=\$(basename "\$dir")
  if [ -n "\$LANE_FILTER" ] && ! printf '%s\n' "\$LANE_FILTER" | grep -qx "\$L"; then continue; fi

  found=0
  for prof in debug release; do
    for sub in deps examples; do
      [ -d "\$dir/target/\$prof/\$sub" ] && found=1
    done
  done
  [ "\$found" -eq 1 ] || continue

  {
    for prof in debug release; do
      for sub in deps examples; do
        d="\$dir/target/\$prof/\$sub"; [ -d "\$d" ] || continue
        find "\$d" -maxdepth 1 -type f -printf '%T@\t%s\t%p\t%f\n' 2>/dev/null
      done
    done
  } | awk -F'\t' -v LIST=0 -f /tmp/sweep-orphans.awk 2>/tmp/sweep-stat.txt >/dev/null || true

  read -r ksz kn osz on < /tmp/sweep-stat.txt 2>/dev/null || { ksz=0; kn=0; osz=0; on=0; }
  tot=\$(( ksz + osz ))
  gb() { awk -v b="\$1" 'BEGIN{printf "%.1f GB", b/1073741824}'; }

  if [ "\$osz" -lt "\$MIN_BYTES" ]; then
    printf '%-24s %10s %10s %10s   below --min-gb, skipped\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)"
    continue
  fi

  n=\$(live_count "\$L")
  if [ "\$n" -ne 0 ]; then
    printf '%-24s %10s %10s %10s   LIVE (%s build procs) — SKIPPED\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$n"
    continue
  fi

  if [ "\$APPLY" -ne 1 ]; then
    printf '%-24s %10s %10s %10s   idle — would sweep %s files\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$on"
    continue
  fi

  {
    for prof in debug release; do
      for sub in deps examples; do
        d="\$dir/target/\$prof/\$sub"; [ -d "\$d" ] || continue
        find "\$d" -maxdepth 1 -type f -printf '%T@\t%s\t%p\t%f\n' 2>/dev/null
      done
    done
  } | awk -F'\t' -v LIST=1 -f /tmp/sweep-orphans.awk 2>/dev/null > /tmp/sweep-\$L.list || true

  # Re-check liveness immediately before deleting: the listing walk takes time, and a
  # lane can wake up during it. Same process, so there is no ssh round-trip window.
  n2=\$(live_count "\$L")
  if [ "\$n2" -ne 0 ]; then
    printf '%-24s %10s %10s %10s   woke up mid-scan (%s procs) — ABORTED, nothing deleted\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$n2"
    continue
  fi

  xargs -a /tmp/sweep-\$L.list -d '\n' -r rm -f
  swept_total=\$(( swept_total + osz ))
  printf '%-24s %10s %10s %10s   SWEPT %s files\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$on"
done

echo
if [ "\$APPLY" -eq 1 ]; then
  awk -v b="\$swept_total" 'BEGIN{printf "reclaimed: %.1f GB\n", b/1073741824}'
else
  echo "(report only — pass --apply to sweep idle lanes)"
fi
df -h / | tail -1
REMOTE
