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
# Measured orphan share, TWO SNAPSHOTS — read them together, the pair is the point:
#   2026-07-25, mature lanes that had never been swept:
#     darkpool   KEEP  57.0 GB /  6,053 files   ORPHAN 171.7 GB / 14,323 files
#     crewbraid  KEEP 114.2 GB /  6,134 files   ORPHAN 166.8 GB / 25,642 files
#   2026-07-26, the SAME lanes one sweep and one day of rebuilding later:
#     crewbraid      KEEP  53.8 GB   ORPHAN 22.4 GB /  5,947 files
#     darkpool       KEEP 152.7 GB   ORPHAN 17.2 GB /  5,381 files
#     native-anchor  KEEP  52.0 GB   ORPHAN  8.2 GB /  2,037 files
# So "three quarters of a lane is superseded" is the STEADY-STATE-OF-NEGLECT number, not a
# constant: on a swept lane the orphan share falls to ~10-30% and KEEP grows as the lane
# rebuilds what it actually needs. Run this OFTEN and each run is small; run it never and it
# is the difference between 414 GB and 611 GB. (darkpool's KEEP going 57.0 → 152.7 GB is the
# rebuild that ember's mis-timed sweep paid for; see the LEASE block below.)
#
#   scripts/sweep-build-lanes.sh                      # report every lane, delete nothing
#   scripts/sweep-build-lanes.sh --apply              # sweep every IDLE, UNLEASED lane
#   scripts/sweep-build-lanes.sh --lane crewbraid --apply
#   scripts/sweep-build-lanes.sh --host hbox --apply
#
# ── OWNERSHIP IS DECLARED, NOT SNIFFED: THE LEASE (added 2026-07-26) ───────────
# THE GAP THIS CLOSES, found by ember doing it to her own agents (2026-07-25): PROCESS-ABSENCE
# IS NOT LANE-OWNERSHIP. `live_count` looks for cargo/rustc/lake/lean/cc/ld attributed to the
# lane, which answers "is this lane COMPILING". The question that matters is "does this lane
# BELONG to someone", and the difference is most of an agent's wall clock — it reads, thinks and
# writes a report, and compiles in bursts. In one of those windows `darkpool` and `native-anchor`
# were swept out from under two live agents. Measured: persvati went 497 GB free → 414 GB as
# those lanes rebuilt what had been deleted.
#
# Not corruption — a fingerprint miss is a rebuild, never a stale link, which is this tool's whole
# safety argument. But the owning agent pays a rebuild it did not expect, and a sweep landing
# during a LINK surfaces inside that agent as an unexplained error it may well misdiagnose as its
# own bug. That is the expensive kind of wrong.
#
# NO BETTER PROBE FIXES IT — no amount of process sniffing can see intent. So a lane now carries
# a CLAIM, and this script refuses any lane holding an unexpired one, whatever is or is not
# running. `scripts/lane-lease.sh` writes and clears them; the contract is:
#
#   <lane dir>/.pbuild-lease   +   <root>/.leases/<lane>.lease   (rsync-immune mirror)
#   one line: owner=<string> pid=<int> host=<string> expires=<unix-seconds>
#   held ⟺ min(expires, mtime + SWEEP_LEASE_MAX_AGE) > now, over EITHER copy
#
#   scripts/lane-lease.sh acquire --lane crewbraid --owner agent:me   # before you use a lane
#   scripts/lane-lease.sh release --lane crewbraid --owner agent:me   # when you are done
#
# BELT AND BRACES, DELIBERATELY: the process check STAYS. A lease catches an owner who is not
# compiling; the process probe catches a build nobody declared (a bare `ssh persvati cargo …`,
# or an agent that never learned about leases). They fail in opposite directions and neither
# subsumes the other.
#
# THE LEASE IS A HINT WITH AN EXPIRY, NOT A LOCK, and there is deliberately NO --ignore-leases
# flag: a knob like that is what an agent reaches for reflexively, and then the guard cannot say
# no. Three things keep a stale lease from wedging a lane instead:
#   1. it EXPIRES (TTL 3600s), so a dead agent stops mattering within the hour;
#   2. `scripts/lane-lease.sh reap-expired` clears expired AND unparseable leases;
#   3. the effective-expiry CEILING of mtime + SWEEP_LEASE_MAX_AGE (default 86400) binds every
#      lease no matter what its `expires=` field claims, so a writer that stamps
#      `expires=9999999999` buys 24 hours rather than 250 years.
# To take a lane from an owner you know is gone: `lane-lease.sh release --lane X --force`, or
# `acquire --force` to claim it. That is two deliberate steps, which is the right price.
#
# A TORN LEASE FAILS CLOSED. An unparseable line is read as `mtime + SWEEP_LEASE_TTL_FALLBACK`
# and reported with ⚠unparseable-line: a write interrupted mid-rename must not cost an agent its
# lane, and it still expires, so it cannot wedge one either.
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
# Lease reading knobs. MAX_AGE is the ceiling that makes "cannot wedge a lane" structural;
# TTL_FALLBACK is how long an unparseable lease is honoured from its mtime. Both are read here
# and passed to the remote shell, so the two sides can never disagree about the numbers.
LEASE_MAX_AGE="${SWEEP_LEASE_MAX_AGE:-86400}"
LEASE_TTL_FALLBACK="${SWEEP_LEASE_TTL_FALLBACK:-3600}"

while [ $# -gt 0 ]; do
  case "$1" in
    --host)   HOST="$2"; shift 2 ;;
    --lane)   LANES+=("$2"); shift 2 ;;
    --apply)  APPLY=1; shift ;;
    --min-gb) MIN_GB="$2"; shift 2 ;;
    -h|--help) sed -n '2,98p' "$0"; exit 0 ;;
    *) echo "sweep-build-lanes: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

case "$MIN_GB" in ''|*[!0-9]*) echo "sweep-build-lanes: --min-gb must be an integer" >&2; exit 2 ;; esac
for _n in LEASE_MAX_AGE LEASE_TTL_FALLBACK; do
  case "${!_n}" in ''|*[!0-9]*) echo "sweep-build-lanes: $_n must be a non-negative integer" >&2; exit 2 ;; esac
done

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
LEASE_MAX_AGE=${LEASE_MAX_AGE}
LEASE_TTL_FALLBACK=${LEASE_TTL_FALLBACK}
LEASE_ROOT="\$HOME/dregg-build"

# ── THE LEASE READER (see the OWNERSHIP block at the top) ─────────────────────
# Reads the DECLARED claim. Two copies are consulted and the LATER effective expiry wins,
# because the contract path \`<lane>/.pbuild-lease\` sits at the root of pbuild's rsync
# destination and \`rsync --delete\` will remove it (MEASURED 2026-07-26 on the real command;
# the repo .gitignore entry protects it only once the RECEIVER's copy of .gitignore carries the
# rule, since a per-directory merge file is read by each side from its own tree). The sidecar
# under \`.leases/\` is outside every lane dir and therefore outside every rsync destination.
#
# All variables are LL_-prefixed on purpose: this runs in the same shell as the sweep loop,
# which owns \$L, \$d, \$n and friends, and a helper that clobbers the caller's loop variable is
# a bug that shows up as a lane being skipped or swept at random.
LL_STATE=absent; LL_OWNER=-; LL_PID=-; LL_CHOST=-; LL_REM=0; LL_MAL=0; LL_WHERE=none
lease_read_one() {
  LR_STATE=absent; LR_OWNER=-; LR_PID=-; LR_CHOST=-; LR_EFF=0; LR_MAL=0
  lf="\$1"
  [ -f "\$lf" ] || return 0
  lline=\$(head -n 1 "\$lf" 2>/dev/null || true)
  lo=""; lp=""; lh=""; le=""
  for ltok in \$lline; do
    case "\$ltok" in
      owner=*)   lo="\${ltok#owner=}" ;;
      pid=*)     lp="\${ltok#pid=}" ;;
      host=*)    lh="\${ltok#host=}" ;;
      expires=*) le="\${ltok#expires=}" ;;
    esac
  done
  lmt=\$(stat -c %Y "\$lf" 2>/dev/null || echo 0)
  case "\$lmt" in ''|*[!0-9]*) lmt=0 ;; esac
  case "\$le" in
    ''|*[!0-9]*) LR_MAL=1; leff=\$(( lmt + LEASE_TTL_FALLBACK )) ;;
    *)           leff="\$le" ;;
  esac
  # THE CEILING: no lease outlives mtime + LEASE_MAX_AGE, whatever it claims.
  lceil=\$(( lmt + LEASE_MAX_AGE ))
  [ "\$leff" -gt "\$lceil" ] && leff="\$lceil"
  LR_EFF="\$leff"; LR_OWNER="\${lo:--}"; LR_PID="\${lp:--}"; LR_CHOST="\${lh:--}"
  lnow=\$(date +%s)
  if [ "\$leff" -gt "\$lnow" ]; then LR_STATE=held; else LR_STATE=expired; fi
}
lease_state() {
  LSN="\$1"
  LL_STATE=absent; LL_OWNER=-; LL_PID=-; LL_CHOST=-; LL_REM=0; LL_MAL=0; LL_WHERE=none
  lbest=-1
  for lfile in "\$LEASE_ROOT/\$LSN/.pbuild-lease" "\$LEASE_ROOT/.leases/\$LSN.lease"; do
    lease_read_one "\$lfile"
    [ "\$LR_STATE" = absent ] && continue
    if [ "\$LR_EFF" -gt "\$lbest" ]; then
      lbest="\$LR_EFF"
      LL_STATE="\$LR_STATE"; LL_OWNER="\$LR_OWNER"; LL_PID="\$LR_PID"
      LL_CHOST="\$LR_CHOST"; LL_MAL="\$LR_MAL"
      case "\$lfile" in *"/.leases/"*) LL_WHERE=sidecar ;; *) LL_WHERE=contract ;; esac
    fi
  done
  if [ "\$lbest" -ge 0 ]; then LL_REM=\$(( lbest - \$(date +%s) )); fi
}

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
n_acted=0; n_lease=0; n_live=0; n_minGB=0; n_expired=0
for dir in ~/dregg-build/*/; do
  [ -d "\$dir" ] || continue
  L=\$(basename "\$dir")
  # The lease SIDECAR directory is not a lane. The dot in \`.leases\` is what actually keeps it
  # out of this glob (and out of pbuild's warm-lane enumeration, which is the same \`*/\` shape)
  # — VERIFIED: bash \`*/\` does not match a leading dot without dotglob. This line is the
  # belt to that brace, for a future caller that sets dotglob or moves the root.
  [ "\$L" = ".leases" ] && continue
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

  # ── LEASE FIRST. A leased lane is never described as "would sweep" or "below threshold":
  # the declaration outranks both, and an operator reading this report needs to see WHO holds
  # it, not a size verdict on a lane that is not available.
  lease_state "\$L"
  if [ "\$LL_STATE" = held ]; then
    n_lease=\$(( n_lease + 1 ))
    lextra=""
    [ "\$LL_MAL" -eq 1 ] && lextra=" ⚠unparseable-line, honoured for one TTL"
    printf '%-24s %10s %10s %10s   LEASED by %s (pid %s on %s, %ss left, %s)%s — SKIPPED\n' \
      "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" \
      "\$LL_OWNER" "\$LL_PID" "\$LL_CHOST" "\$LL_REM" "\$LL_WHERE" "\$lextra"
    continue
  fi
  if [ "\$LL_STATE" = expired ]; then n_expired=\$(( n_expired + 1 )); fi

  if [ "\$osz" -lt "\$MIN_BYTES" ]; then
    n_minGB=\$(( n_minGB + 1 ))
    printf '%-24s %10s %10s %10s   below --min-gb, skipped\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)"
    continue
  fi

  n=\$(live_count "\$L")
  if [ "\$n" -ne 0 ]; then
    n_live=\$(( n_live + 1 ))
    printf '%-24s %10s %10s %10s   LIVE (%s build procs) — SKIPPED\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$n"
    continue
  fi

  if [ "\$APPLY" -ne 1 ]; then
    n_acted=\$(( n_acted + 1 ))
    printf '%-24s %10s %10s %10s   idle, unleased — would sweep %s files\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$on"
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

  # Re-check BOTH signals immediately before deleting: the listing walk takes time, and a lane
  # can wake up or be CLAIMED during it. Same process, so there is no ssh round-trip window.
  # The lease re-check matters most in exactly the case this whole block exists for — an agent
  # that starts work on a lane the sweep has already decided to empty.
  lease_state "\$L"
  if [ "\$LL_STATE" = held ]; then
    n_lease=\$(( n_lease + 1 ))
    printf '%-24s %10s %10s %10s   CLAIMED mid-scan by %s (%ss left) — ABORTED, nothing deleted\n' \
      "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$LL_OWNER" "\$LL_REM"
    continue
  fi
  n2=\$(live_count "\$L")
  if [ "\$n2" -ne 0 ]; then
    n_live=\$(( n_live + 1 ))
    printf '%-24s %10s %10s %10s   woke up mid-scan (%s procs) — ABORTED, nothing deleted\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$n2"
    continue
  fi

  xargs -a /tmp/sweep-\$L.list -d '\n' -r rm -f
  swept_total=\$(( swept_total + osz ))
  n_acted=\$(( n_acted + 1 ))
  printf '%-24s %10s %10s %10s   SWEPT %s files\n' "\$L" "\$(gb \$ksz)" "\$(gb \$osz)" "\$(gb \$tot)" "\$on"
done

echo
# WHY THE SKIP REASONS ARE COUNTED SEPARATELY: "3 lanes skipped" is the report that let the
# 2026-07-25 mis-sweep look normal. A LEASE skip means someone said the lane is theirs; a LIVE
# skip means a build is running that nobody declared. They call for opposite responses — wait
# vs go look at what is compiling — so a report that merges them has thrown away the actionable
# half. Both are stated even when zero, so a reader can tell "no leases were consulted" from
# "no lanes were leased".
if [ "\$APPLY" -eq 1 ]; then
  printf 'lanes: %s swept | %s skipped for an unexpired LEASE | %s skipped for live build procs | %s below --min-gb\n' \
    "\$n_acted" "\$n_lease" "\$n_live" "\$n_minGB"
  awk -v b="\$swept_total" 'BEGIN{printf "reclaimed: %.1f GB\n", b/1073741824}'
else
  printf 'lanes: %s would be swept | %s skipped for an unexpired LEASE | %s skipped for live build procs | %s below --min-gb\n' \
    "\$n_acted" "\$n_lease" "\$n_live" "\$n_minGB"
  echo "(report only — pass --apply to sweep idle, unleased lanes)"
fi
if [ "\$n_expired" -gt 0 ]; then
  printf '%s lane(s) carried an EXPIRED lease (ignored, as designed). Clear them with:\n' "\$n_expired"
  printf '  scripts/lane-lease.sh reap-expired --host %s\n' "\$(hostname -s 2>/dev/null || echo \$HOSTNAME)"
fi
df -h / | tail -1
REMOTE
