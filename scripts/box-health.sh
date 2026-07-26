#!/usr/bin/env bash
# box-health.sh — ONE read-only heartbeat for the remote build boxes, that can go RED.
#
# ── WHY THIS EXISTS ───────────────────────────────────────────────────────────────
# Nothing watched the boxes, so they rotted in ways only ever discovered by a build
# failing. Every item here was MEASURED on 2026-07-25/26, not imagined:
#
#   * persvati's `~/dregg-build` reached **611 GB across 18 lanes** with nothing ever
#     collecting it, on a disk that had already hit 100% once and took a lane down with
#     `No space left on device`. One sweep reclaimed 332.5 GB. Nothing scheduled it.
#   * two test runs were HUNG for **9d23h and 8d12h** holding ~15 GB of swap, with
#     persvati's swap 100% full. One was deadlocked in `futex_do_wait` on a Mesa llvmpipe
#     fallback on a headless box; its lane directory had been deleted days earlier.
#   * hbox's `swarm.slice` shows **oom_kill=86** and hit its 96 GiB ceiling **13,476**
#     times, with 202 OOM-kill events in the user journal for 07-17..07-25. From inside a
#     lane an OOM-kill is indistinguishable from a proof error, so lanes burned hours
#     debugging the box as if it were their own code.
#   * hbox's `/tmp` is a **62 GiB tmpfs**: anything written there is RAM, charged against
#     the same 96 GiB cap the build runs under. 12.4 GB was reclaimed from inside that cap.
#   * the 5-minutely `gauntlet-watch.sh` cron on BOTH boxes had been a total no-op since
#     2026-07-03 / 07-08 — dead machinery wearing the costume of a gate.
#
# So: a heartbeat that MEASURES and can FAIL. One command for both boxes, read-only by
# default (one documented exception, below), nonzero exit on anything worth waking someone
# for — which is what lets it be a scheduled gate instead of a wall of numbers.
#
# ── IT REPORTS EVERY CHECK BY NAME ───────────────────────────────────────────────
# A COUNT IS NOT COVERAGE. This never prints "9 checks passed"; it prints each check's NAME
# and verdict, so a reader sees exactly which conditions were evaluated. A probe that could
# not be evaluated reads UNKNOWN, and UNKNOWN IS AN ALARM — a health check that silently
# skips a probe is the same failure as a guard that cannot go red. N/A is reserved for
# checks genuinely inapplicable to a host, and it is DERIVED, never a hostname table: the
# swarm.slice check is N/A exactly when `swarm-build` is absent, because swarm-build is the
# thing that creates that slice. If swarm-build IS installed and the slice is missing, that
# is UNKNOWN, i.e. red.
#
# ── SCOPE, SAID OUT LOUD ─────────────────────────────────────────────────────────
# The process probe covers processes owned by THIS user only, so root-owned system units are
# outside it entirely. Within that scope, "old" alone is not rot — a deployed service is
# SUPPOSED to run forever. The two are separated by asking systemd what it is supervising:
# a process whose cgroup leaf is a `*.service` is SUPERVISED and does not gate; one adrift in
# a `session-<n>.scope` is an orphaned manual run and does. That distinction was measured,
# not guessed, and it cuts exactly the wrong way from intuition — hbox's 2-day-old
# `dreggnet-web-server` running out of a BUILD LANE is `dregg-web-games-funnel.service`,
# i.e. deliberate, while persvati's 8-day `dregg-node --enable-faucet` is in
# `session-12645.scope` with ppid 1, i.e. nobody's. `--allow-proc` remains for an orphan
# somebody has decided to keep; allowlisted processes are still PRINTED, never hidden.
#
# ── USAGE ────────────────────────────────────────────────────────────────────────
#   scripts/box-health.sh                          # survey persvati + hbox from here
#   scripts/box-health.sh --host hbox              # one box
#   scripts/box-health.sh --local                  # run ON a box; no ssh at all
#   scripts/box-health.sh --disk-pct 1             # force red, to prove it can
#   scripts/box-health.sh --record                 # advance the OOM watermark (see below)
#
# EXIT: 0 = every check OK/INFO/N-A.  1 = at least one ALARM or UNKNOWN.  2 = usage error.
# One greppable line per host, in the same shape the repo already reads for pbuild:
#   box-health: VERDICT host=<h> outcome=OK|ALARM|UNREACHABLE alarms=<n> ...
#
# ── HOW THE BOXES ARE SCHEDULED, AND HOW TO RE-INSTALL A COPY ────────────────────
# Each box runs a byte-identical COPY of this script and of sweep-build-lanes.sh out of
# `~/bin`, because neither box has a live checkout to run them from (their `~/dev/breadstuffs`
# is a June clone of a since-renamed remote). Copies drift, so the drift is a CHECK
# (`sweep-copy`, `box-health-copy`) rather than a comment. To refresh a box after either
# script changes — which is required, or the box keeps gating on the old rules:
#
#   scp scripts/box-health.sh scripts/sweep-build-lanes.sh <box>:bin/
#   ssh <box> 'git -C /dev/null true; :'   # then re-stamp provenance:
#   ssh <box> "printf '%s\n' '<git-sha> <date>' > bin/box-health.provenance"
#   ssh <box> "printf '%s\n' '<git-sha> <date>' > bin/sweep-build-lanes.provenance"
#
# persvati is driven by cron (it already had a crontab); hbox by systemd user timers (it
# already uses them, and has Linger=yes so they fire with nobody logged in). The schedule
# writes the full report to `~/box-health.latest` (overwritten, so it is always the current
# state) and appends only the VERDICT lines to `~/box-health.log` (bounded growth, and the
# one line worth grepping). The nightly reclaim logs to `~/box-sweep.log`.
#
# The sweep runs THROUGH scripts/sweep-build-lanes.sh with SWEEP_HOST=localhost — it is never
# reimplemented on the box. That script reaches its target over ssh, which is why each box
# has a loopback-only key (`~/.ssh/id_boxlocal`, authorized `from="127.0.0.1,::1"`); it grants
# no privilege the cron job did not already have as that user.
#
# ── THE ONE PLACE IT IS NOT READ-ONLY ────────────────────────────────────────────
# swarm.slice's `memory.events` oom_kill counter is CUMULATIVE since the slice was created,
# so "oom_kill > 0" is permanently true and therefore worthless as an alarm. The useful
# question is "were there NEW kills since I last looked", which needs a watermark. Default
# behaviour reads the watermark and does not move it (still read-only; repeated runs keep
# reporting the same delta). `--record` writes it. The installed timer passes --record; a
# human poking at the box does not, and so cannot accidentally acknowledge kills nobody has
# seen. A stateless second opinion is computed regardless: OOM events in the journal within
# --oom-since, plus earlyoom kills in the same window.
set -uo pipefail
# NOT `set -e`: an unreachable first host must not abandon the second, and a host that
# cannot be read has to be REPORTED as red, not turned into a silent early exit.

HOSTS=()
LOCAL=0
DISK_PCT=90
SWAP_PCT=50
# 611 GB across 18 lanes was the measured disaster that took a lane down with "No space left
# on device"; ~470 GB is the post-sweep steady state, of which only ~40 GB is reclaimable
# orphan at any moment. So a 400 GB threshold could never be satisfied BY THE REMEDY — it
# would sit permanently red and train everyone to ignore it. 550 sits between the steady
# state and the disaster: it fires while there is still ~1.3 TB of runway, and it goes quiet
# when the sweep has done its job. `disk-usage` is the backstop for the volume itself.
LANES_GB=550
TMPFS_GB=8
PROC_AGE_DAYS=1
OOM_SINCE="24 hours ago"
OOM_MAX=0
RECORD=0
DO_LANES=1
ALLOW_PROC=()

die() { echo "box-health: $*" >&2; exit 2; }
need_int() { case "$2" in ''|*[!0-9]*) die "$1 must be a non-negative integer (got '$2')";; esac; }

while [ $# -gt 0 ]; do
  case "$1" in
    --host)          [ $# -ge 2 ] || die "--host needs a value"; HOSTS+=("$2"); shift 2 ;;
    --local)         LOCAL=1; shift ;;
    --disk-pct)      need_int --disk-pct "${2:-}";      DISK_PCT="$2"; shift 2 ;;
    --swap-pct)      need_int --swap-pct "${2:-}";      SWAP_PCT="$2"; shift 2 ;;
    --lanes-gb)      need_int --lanes-gb "${2:-}";      LANES_GB="$2"; shift 2 ;;
    --tmpfs-gb)      need_int --tmpfs-gb "${2:-}";      TMPFS_GB="$2"; shift 2 ;;
    --proc-age-days) need_int --proc-age-days "${2:-}"; PROC_AGE_DAYS="$2"; shift 2 ;;
    --oom-max)       need_int --oom-max "${2:-}";       OOM_MAX="$2"; shift 2 ;;
    --oom-since)     [ $# -ge 2 ] || die "--oom-since needs a value"; OOM_SINCE="$2"; shift 2 ;;
    --allow-proc)    [ $# -ge 2 ] || die "--allow-proc needs a value"; ALLOW_PROC+=("$2"); shift 2 ;;
    --record)        RECORD=1; shift ;;
    --no-lanes)      DO_LANES=0; shift ;;
    -h|--help)       sed -n '2,92p' "$0"; exit 0 ;;
    *) die "unknown argument '$1' (try --help)" ;;
  esac
done

# --oom-since ends up inside a remote command line, so it is restricted to the characters
# systemd's timestamp grammar actually needs. This is a VALIDATION, not an escape: anything
# outside the set is refused rather than quoted and hoped for. In particular no quote
# characters can survive, which is what makes the single-quoting below sound.
case "$OOM_SINCE" in
  *[!A-Za-z0-9\ :,.+-]*) die "--oom-since may only contain letters, digits, space, and : , . + -" ;;
esac

if [ "$LOCAL" -eq 1 ]; then
  [ "${#HOSTS[@]}" -eq 0 ] || die "--local and --host are mutually exclusive"
  HOSTS=(LOCAL)
elif [ "${#HOSTS[@]}" -eq 0 ]; then
  HOSTS=(persvati hbox)
fi

SELF_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_SWEEP="${SELF_DIR}/sweep-build-lanes.sh"

sha_of() { # portable sha256 of a file, empty if it cannot be hashed
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" 2>/dev/null | awk '{print $1}'
  else shasum -a 256 "$1" 2>/dev/null | awk '{print $1}'; fi
}

# ── THE MEASUREMENT PAYLOAD ──────────────────────────────────────────────────────
# Runs on the box, in ONE shell, and takes NO thresholds: it only measures, and prints
# `KEY=value` and tab-separated records. Every judgement happens locally, below. That split
# is deliberate — it is what lets `--disk-pct 1` turn this red without touching the remote,
# and it keeps interpolated policy out of the remote command line entirely.
#   $1 = --oom-since window   $2 = 1 to advance the OOM watermark   $3 = 1 to size lanes
read -r -d '' PAYLOAD <<'PAYLOAD_EOF'
set -uo pipefail
OOM_SINCE="${1:-24 hours ago}"
RECORD="${2:-0}"
LANES="${3:-1}"
# Everything the payload needs is copied into named variables HERE, because the /proc walk
# below uses `set --` and will clobber the positional parameters.

emit() { printf '%s\n' "$*"; }

emit "HOSTNAME=$(hostname)"
emit "KERNEL=$(uname -r)"
emit "NPROC=$(nproc 2>/dev/null || echo 0)"
NOW=$(date +%s)
emit "NOW=$NOW"

read -r l1 l5 l15 _ < /proc/loadavg
emit "LOAD1=$l1"; emit "LOAD5=$l5"; emit "LOAD15=$l15"

# Memory and swap from /proc/meminfo — never by parsing `free(1)`, whose columns move
# between versions.
mt=0; ma=0; st=0; sf=0
while read -r k v _; do
  case "$k" in
    MemTotal:)     mt=$v ;;
    MemAvailable:) ma=$v ;;
    SwapTotal:)    st=$v ;;
    SwapFree:)     sf=$v ;;
  esac
done < /proc/meminfo
emit "MEM_TOTAL_KB=$mt"; emit "MEM_AVAIL_KB=$ma"
emit "SWAP_TOTAL_KB=$st"; emit "SWAP_FREE_KB=$sf"

# Disk for the filesystem that actually holds the build lanes, not blindly `/` — if the
# lanes ever move to their own volume the check has to follow the lanes.
BUILD_ROOT="$HOME/dregg-build"
[ -d "$BUILD_ROOT" ] || BUILD_ROOT="$HOME"
emit "BUILD_ROOT=$BUILD_ROOT"
df -Pk "$BUILD_ROOT" 2>/dev/null | awk 'NR==2{
  printf "DISK_FS=%s\nDISK_TOTAL_KB=%d\nDISK_USED_KB=%d\nDISK_AVAIL_KB=%d\nDISK_MNT=%s\n",$1,$2,$3,$4,$6}'

# tmpfs — every tmpfs mount IS RAM. hbox's /tmp is a 62 GiB tmpfs, so a build that spills
# there is charged against the very cap it is running under.
while read -r _dev mnt fstype _rest; do
  [ "$fstype" = tmpfs ] || continue
  df -Pk "$mnt" 2>/dev/null | awk -v m="$mnt" 'NR==2 && $3>0 {printf "TMPFS\t%s\t%d\t%d\n",m,$3,$2}'
done < /proc/mounts

# ── LANES ───────────────────────────────────────────────────────────────────────
# size, Lean archive presence, warmth, lease state. The warmth probe is the SAME rule
# pbuild refuses cold lanes by (mathlib under <lane>/metatheory/.lake, or >=100 artifacts
# in target/{release,debug}/deps), so "warm" here means "pbuild will accept this lane"
# rather than a second, quietly different opinion.
lane_total=0; lane_count=0
if [ -d "$BUILD_ROOT" ]; then
  for d in "$BUILD_ROOT"/*/; do
    [ -d "$d" ] || continue
    L=$(basename "$d"); lane_count=$((lane_count+1))

    sz=-1
    if [ "$LANES" = 1 ]; then
      sz=$(timeout 300 du -sk "$d" 2>/dev/null | awk 'END{print $1+0}')
      case "${sz:-}" in ''|*[!0-9]*) sz=-1 ;; esac
      [ "$sz" -ge 0 ] && lane_total=$((lane_total+sz))
    fi

    ar=no; [ -f "${d}dregg-lean-ffi/libdregg_lean.a" ] && ar=yes

    # WARMTH IS TWO INDEPENDENT AXES, reported separately. pbuild collapses them to one
    # "warm" (either axis suffices for it to accept a lane), but collapsing them here would
    # hide the case that actually matters when choosing a lane: Lean-warm and cargo-COLD.
    # Every large lane on both boxes has mathlib, so a single field would have printed
    # "warm" for lanes whose cargo cache is empty.
    lean=cold
    if [ -d "${d}metatheory/.lake/packages/mathlib" ] || [ -d "${d}.lake/packages/mathlib" ]; then
      lean=mathlib
    fi
    ndeps=$(ls "${d}target/release/deps" "${d}target/debug/deps" 2>/dev/null | wc -l | tr -d ' ')
    ndeps=${ndeps:-0}
    if [ "$ndeps" -ge 100 ]; then cargo=warm; else cargo=cold; fi

    # Lease contract: ONE line, exactly `owner=<s> pid=<int> host=<s> expires=<unix>`.
    # Anything else is a CONTRACT VIOLATION, not a missing lease, and is reported as one —
    # a malformed lease is worse than none, because the sweep cannot reason about it.
    lease=none; lowner=-; lexp=0
    if [ -f "${d}.pbuild-lease" ]; then
      lease=malformed
      nl=$(wc -l < "${d}.pbuild-lease" 2>/dev/null | tr -d ' ')
      first=$(head -1 "${d}.pbuild-lease" 2>/dev/null)
      if [ "${nl:-9}" -le 1 ]; then
        o=""; p=""; h=""; e=""
        for kvp in $first; do
          case "$kvp" in
            owner=*)   o=${kvp#owner=} ;;
            pid=*)     p=${kvp#pid=} ;;
            host=*)    h=${kvp#host=} ;;
            expires=*) e=${kvp#expires=} ;;
          esac
        done
        case "$p" in ''|*[!0-9]*) p="" ;; esac
        case "$e" in ''|*[!0-9]*) e="" ;; esac
        if [ -n "$o" ] && [ -n "$p" ] && [ -n "$h" ] && [ -n "$e" ]; then
          lowner="$o"; lexp="$e"
          if [ "$e" -gt "$NOW" ]; then lease=held; else lease=expired; fi
        fi
      fi
    fi
    printf 'LANE\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$L" "$sz" "$ar" "$lean" "$cargo" "$ndeps" "$lease" "$lowner" "$lexp"
  done
fi
emit "LANE_COUNT=$lane_count"
emit "LANE_TOTAL_KB=$lane_total"

# ── LONG-LIVED PROCESSES, WITHOUT THE SELF-MATCH FOOTGUN ────────────────────────
# This walks /proc and matches with a bash regex held in a VARIABLE. It deliberately does
# NOT pipe `ps` into `grep`, and does not use `pgrep -f`, because the matcher's own command
# line contains the pattern and matches itself. That is not hypothetical: persvati is
# carrying FOUR immortal shells shaped like
#     bash -c 'until ! pgrep -f "cargo install wasm-bindgen"; do sleep 10; done'
# aged 4 to 11 days, which can never exit — the `pgrep` finds the enclosing `bash`, whose
# own cmdline contains the pattern. Those leaked spin-loops are exactly what the WATCHER
# class exists to surface, so the probe that hunts them must not commit their bug.
# Kernel threads are excluded for free: their /proc/<pid>/cmdline is empty.
BUILDISH='(^|/)(cargo|rustc|rustdoc|lake|lean|leanc|nextest|Holmake|poly|cc1|cc1plus|ld|lld|swarm-build)( |$)|cargo-nextest|dregg-|dreggnet-|fhegg|circuit-prove|lake build|--test '
WATCHER='pgrep -f|tail -f|until ! |while pgrep'
HZ=$(getconf CLK_TCK 2>/dev/null || echo 100)
PGSZ_KB=$(( $(getconf PAGESIZE 2>/dev/null || echo 4096) / 1024 ))
read -r UPS _ < /proc/uptime
UPS=${UPS%%.*}
SELF=$$

for d in /proc/[0-9]*; do
  pid=${d#/proc/}
  [ "$pid" = "$SELF" ] && continue
  [ -O "$d" ] || continue                       # our uid only; no fork, no `stat`
  parts=()
  mapfile -d '' -t parts < "$d/cmdline" 2>/dev/null || continue
  cmd="${parts[*]-}"
  [ -n "$cmd" ] || continue                     # empty cmdline == kernel thread
  st=""
  { read -r st < "$d/stat"; } 2>/dev/null || continue
  st=${st#*") "}                                # drop pid and (comm), which may hold spaces
  [ -n "$st" ] || continue
  set -- $st                                    # $1 is now field 3 (state); starttime is field 22 => ${20}
  [ $# -ge 20 ] || continue
  start=${20}
  case "$start" in ''|*[!0-9]*) continue ;; esac
  age=$(( UPS - start / HZ ))
  [ "$age" -ge 0 ] || age=0
  rss=0
  if r=$( { read -r _ x _ < "$d/statm" && echo "$x"; } 2>/dev/null ); then
    case "${r:-}" in ''|*[!0-9]*) r=0 ;; esac
    rss=$(( r * PGSZ_KB ))
  fi
  cls=""
  if [[ $cmd =~ $BUILDISH ]]; then cls=BUILD
  elif [[ $cmd =~ $WATCHER ]]; then cls=WATCHER
  fi
  [ -n "$cls" ] || continue

  # ── SUPERVISED vs ORPHANED, DERIVED FROM THE CGROUP ────────────────────────────
  # A long-lived process is only rot if NOBODY MEANT IT. systemd already records that
  # intent: a managed service sits in a leaf named `<something>.service`, while a manual
  # run that outlived the ssh session that started it is reparented to init inside a
  # `session-<n>.scope`. Both look identical to `ps`, which is why this needed measuring
  # rather than guessing — on hbox, `dreggnet-web-server` aged 2d5h out of the
  # `games-deploy` BUILD LANE reads exactly like leaked build debris and is in fact
  # `dregg-web-games-funnel.service`, a deliberate deploy. Meanwhile persvati's 8-day
  # `dregg-node --enable-faucet` sits in `session-12645.scope` with ppid 1: nobody is
  # supervising it, it is a manual run that got orphaned.
  # So the exemption is DERIVED from systemd's own record, not from a hostname table or a
  # list of blessed binary names that would rot the moment a service was renamed.
  unit="-"
  cg=""
  { read -r cg < "$d/cgroup"; } 2>/dev/null || cg=""
  leaf=${cg##*/}
  case "$leaf" in
    *.service) cls=SERVICE; unit="$leaf" ;;
    *)         [ -n "$leaf" ] && unit="$leaf" ;;
  esac
  printf 'PROC\t%s\t%s\t%s\t%s\t%s\t%s\n' "$cls" "$pid" "$age" "$rss" "$unit" "$cmd"
done

# ── OUR CGROUPS' OOM KILLS ──────────────────────────────────────────────────────
# swarm.slice is EXPECTED exactly when swarm-build is installed, because swarm-build is what
# creates it; missing-but-expected becomes UNKNOWN (red) locally, never a quiet skip. Its
# cap/peak/ceiling detail is reported because that is the build cap lanes actually run under.
#
# But the count must NOT be scoped to swarm.slice alone. Measured 2026-07-26: hbox's
# user manager carried oom_kill=108, of which swarm.slice held 86 and **app.slice held 22** —
# and app.slice has NO cap of its own, so those kills came from transient `systemd-run`
# scopes (one was `run-u4163.scope`) that vanished, leaving the count attributed upward. A
# swarm.slice-only probe reported a flat 86 while six kill notifications had fired one minute
# earlier. So the total is summed over every cgroup under the user manager that reports a
# nonzero count, and the watermark tracks THAT.
if command -v swarm-build >/dev/null 2>&1; then emit "SWARM_BUILD=yes"; else emit "SWARM_BUILD=no"; fi
CG=$(find /sys/fs/cgroup -maxdepth 6 -type d -name 'swarm.slice' 2>/dev/null | head -1)
if [ -n "$CG" ]; then
  emit "CGROUP=$CG"
  if [ -r "$CG/memory.events" ]; then
    while read -r k v; do
      case "$k" in
        oom)      emit "CG_OOM=$v" ;;
        max)      emit "CG_MAX_HIT=$v" ;;
      esac
    done < "$CG/memory.events"
  fi
  emit "CG_MEM_MAX=$(cat "$CG/memory.max" 2>/dev/null || echo 0)"
  emit "CG_MEM_CUR=$(cat "$CG/memory.current" 2>/dev/null || echo 0)"
  emit "CG_MEM_PEAK=$(cat "$CG/memory.peak" 2>/dev/null || echo 0)"
else
  emit "CGROUP=absent"
fi

# Sum oom_kill over our whole user-manager subtree. Leaf counters are cumulative and a
# PARENT's counter already includes its children's, so summing every level would multiply-
# count; only cgroups whose count EXCEEDS the sum of their children contribute. Simpler and
# exact: take the count at the top of our subtree, which by construction includes all of it,
# and list the nonzero descendants for attribution.
UROOT=$(dirname "$CG" 2>/dev/null)
case "$UROOT" in ''|.|/) UROOT="" ;; esac
if [ -z "$UROOT" ]; then
  for c in /sys/fs/cgroup/user.slice/user-$(id -u).slice/user@$(id -u).service \
           /sys/fs/cgroup/user.slice/user-$(id -u).slice; do
    [ -r "$c/memory.events" ] && { UROOT="$c"; break; }
  done
fi
if [ -n "$UROOT" ] && [ -r "$UROOT/memory.events" ]; then
  emit "CG_OOM_ROOT=$UROOT"
  emit "CG_OOM_TOTAL=$(awk '$1=="oom_kill"{print $2}' "$UROOT/memory.events")"
  while IFS= read -r f; do
    n=$(awk '$1=="oom_kill"{print $2}' "$f" 2>/dev/null)
    [ "${n:-0}" -gt 0 ] && printf 'CGOOM\t%s\t%s\n' "$n" "$(basename "$(dirname "$f")")"
  done < <(find "$UROOT" -maxdepth 3 -name memory.events 2>/dev/null)
else
  emit "CG_OOM_TOTAL=unknown"
  emit "CG_OOM_ROOT=unknown"
fi

WM_DIR="$HOME/.cache/box-health"
WM="$WM_DIR/oom-watermark"
if [ -f "$WM" ]; then
  w=$(head -1 "$WM" 2>/dev/null | tr -dc '0-9')
  emit "CG_OOM_WATERMARK=${w:-unset}"
else
  emit "CG_OOM_WATERMARK=unset"
fi
if [ "$RECORD" = 1 ] && [ -n "$UROOT" ] && [ -r "$UROOT/memory.events" ]; then
  cur=$(awk '$1=="oom_kill"{print $2}' "$UROOT/memory.events" 2>/dev/null)
  case "${cur:-}" in
    ''|*[!0-9]*) : ;;
    *) mkdir -p "$WM_DIR" && printf '%s\n' "$cur" > "$WM" && emit "CG_OOM_WATERMARK_WROTE=$cur" ;;
  esac
fi

# ── STATELESS SECOND OPINIONS ───────────────────────────────────────────────────
# A window needs no watermark. UNKNOWN when the journal cannot be read OR the window is not
# a timestamp journalctl accepts — because "no kills" and "I could not look" must never
# print the same thing. The probe below is the SAME invocation as the count, with -n 1, so
# it validates readability and the window together; an earlier version validated only
# readability and happily reported "0 kills" from a journalctl that had exited 1 on a
# malformed --since. `grep -c` on an empty stream is 0, so a failed command reads as clean
# unless its status is checked. It is checked.
if journalctl --user --since "$OOM_SINCE" -n 1 >/dev/null 2>&1; then
  emit "OOMJ=$(journalctl --user --since "$OOM_SINCE" 2>/dev/null | grep -c 'killed by the OOM killer')"
else
  emit "OOMJ=unknown"
fi
if journalctl -u earlyoom --since "$OOM_SINCE" -n 1 >/dev/null 2>&1; then
  emit "EARLYOOM_ACTIVE=$(systemctl is-active earlyoom 2>/dev/null || echo unknown)"
  emit "EARLYOOM_KILLS=$(journalctl -u earlyoom --since "$OOM_SINCE" 2>/dev/null | grep -c 'sending SIGTERM to process')"
else
  emit "EARLYOOM_ACTIVE=unknown"
  emit "EARLYOOM_KILLS=unknown"
fi

# ── THE BOX'S PINNED COPIES ─────────────────────────────────────────────────────
# The schedules on the box run COPIES of two repo scripts, because the box has no live
# checkout to run them from (its `~/dev/breadstuffs` is a June clone of a renamed remote).
# A copy is drift waiting to happen, so the copy is DETECTED rather than commented: the box
# reports each copy's sha256 and the laptop compares it to the repo file.
#
# Provenance therefore lives in a SIDECAR, never stamped into the script. An earlier plan
# appended an `# INSTALLED-FROM:` line to the installed copy — which changes its bytes, so
# its sha256 could never match the repo file again and the drift check would have been
# permanently, uselessly red. The copies are installed BYTE-IDENTICAL; `<name>.provenance`
# beside them records which commit they came from.
for _n in sweep-build-lanes box-health; do
  _f="$HOME/bin/${_n}.sh"
  _k=$(printf '%s' "$_n" | tr 'a-z-' 'A-Z_')
  if [ -f "$_f" ]; then
    emit "${_k}_SHA=$(sha256sum "$_f" 2>/dev/null | awk '{print $1}')"
    emit "${_k}_FROM=$(head -1 "$HOME/bin/${_n}.provenance" 2>/dev/null || true)"
  else
    emit "${_k}_SHA=absent"
    emit "${_k}_FROM="
  fi
done

# Scheduling, so "is anything actually going to run" is part of the health report and not a
# thing a human has to remember to check separately.
# COMMENT LINES ARE EXCLUDED. Counting them made a COMMENTED-OUT schedule read as
# "scheduled" — a gate blind to its own disablement, which is the whole failure class this
# script exists for. The crontab installed on persvati explains itself in comments that
# mention both job names, so without this filter it reported 3 active health lines when
# there is 1.
emit "CRON_HEALTH=$(crontab -l 2>/dev/null | grep -v '^[[:space:]]*#' | grep -c 'box-health\.sh' || true)"
emit "CRON_SWEEP=$(crontab -l 2>/dev/null | grep -v '^[[:space:]]*#' | grep -c 'sweep-build-lanes\.sh' || true)"
emit "TIMER_HEALTH=$(systemctl --user is-enabled box-health.timer 2>/dev/null || echo none)"
emit "TIMER_SWEEP=$(systemctl --user is-enabled box-sweep.timer 2>/dev/null || echo none)"
emit "PAYLOAD_OK=1"
PAYLOAD_EOF

# ── LOCAL RENDERING AND JUDGEMENT ────────────────────────────────────────────────
TMP="$(mktemp -d "${TMPDIR:-/tmp}/box-health.XXXXXX")" || die "cannot create temp dir"
trap 'rm -rf "$TMP"' EXIT INT TERM

kv()  { awk -F= -v k="$2" '$1==k{sub(/^[^=]*=/,""); print; exit}' "$1"; }
gib() { awk -v k="${1:-0}" 'BEGIN{ if (k+0 < 0) {print "?"; exit} printf "%.1f", k/1048576 }'; }
pct() { awk -v a="${1:-0}" -v b="${2:-0}" 'BEGIN{ if (b+0==0) {print 0; exit} printf "%d", (a*100)/b }'; }

ALARMS_TOTAL=0
UNREACHABLE=0
CHECK_ROWS=""
HOST_ALARMS=0

# One row of the CHECKS table. Verdicts: OK | INFO | N/A | ALARM | UNKNOWN.
# ALARM and UNKNOWN both count: "I could not evaluate this" is not a pass.
check() { # check <name> <verdict> <detail...>
  local name="$1" verdict="$2"; shift 2
  CHECK_ROWS="${CHECK_ROWS}    $(printf '%-20s %-7s %s' "$name" "$verdict" "$*")
"
  case "$verdict" in ALARM|UNKNOWN) HOST_ALARMS=$((HOST_ALARMS+1)) ;; esac
}

allowed_proc() {
  local cmd="$1" pat
  for pat in ${ALLOW_PROC+"${ALLOW_PROC[@]}"}; do
    [[ $cmd =~ $pat ]] && return 0
  done
  return 1
}

echo "box-health $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "thresholds: disk>=${DISK_PCT}% swap>=${SWAP_PCT}% lanes>=${LANES_GB}G tmpfs>=${TMPFS_GB}G proc-age>=${PROC_AGE_DAYS}d oom-since=\"${OOM_SINCE}\" oom-max=${OOM_MAX}"
[ "${#ALLOW_PROC[@]}" -gt 0 ] && echo "allow-proc: ${ALLOW_PROC[*]}   (allowlisted procs still PRINTED, never hidden)"

for H in "${HOSTS[@]}"; do
  OUT="$TMP/out"; ERR="$TMP/err"
  CHECK_ROWS=""; HOST_ALARMS=0

  if [ "$LOCAL" -eq 1 ]; then
    LABEL="$(hostname) (--local)"
    bash -c "$PAYLOAD" box-health-payload "$OOM_SINCE" "$RECORD" "$DO_LANES" >"$OUT" 2>"$ERR"
    rc=$?
  else
    LABEL="$H"
    if ! ssh -o BatchMode=yes -o ConnectTimeout=10 "$H" true 2>/dev/null; then
      echo
      echo "=== $H ==================================================================="
      echo "  UNREACHABLE — 'ssh -o BatchMode=yes $H true' failed"
      echo "box-health: VERDICT host=$H outcome=UNREACHABLE alarms=1"
      UNREACHABLE=1; ALARMS_TOTAL=$((ALARMS_TOTAL+1))
      continue
    fi
    # OOM_SINCE was validated to a quote-free charset above, which is what makes this
    # single-quoting sound rather than hopeful.
    # `bash -s -- a b c` puts a,b,c at $1,$2,$3 — there is NO $0 slot the way there is for
    # `bash -c script name args…`. Passing a name here silently shifted every argument by
    # one: --oom-since arrived as the literal "box-health-payload", journalctl rejected it,
    # and journal-oom then reported "OK, 0 events" WITHOUT EVER LOOKING. That is the exact
    # class of failure this script exists to catch, so it is also guarded downstream — the
    # window is now validated against journalctl before any count is believed.
    ssh -o BatchMode=yes -o ConnectTimeout=10 "$H" \
        "bash -s -- '$OOM_SINCE' '$RECORD' '$DO_LANES'" \
        <<<"$PAYLOAD" >"$OUT" 2>"$ERR"
    rc=$?
  fi

  # A payload that died halfway would otherwise render as a box with lovely numbers and
  # quietly missing checks. The sentinel makes a truncated measurement loud.
  if [ "$(kv "$OUT" PAYLOAD_OK)" != 1 ]; then
    echo
    echo "=== $LABEL ==================================================================="
    echo "  PROBE FAILED (rc=$rc, no PAYLOAD_OK sentinel) — measurement INCOMPLETE, treat as red"
    sed 's/^/  stderr: /' "$ERR" 2>/dev/null | head -10
    echo "box-health: VERDICT host=$H outcome=ALARM alarms=1 reason=probe-failed"
    ALARMS_TOTAL=$((ALARMS_TOTAL+1))
    continue
  fi

  HN=$(kv "$OUT" HOSTNAME);      KERN=$(kv "$OUT" KERNEL);      NP=$(kv "$OUT" NPROC)
  NOWS=$(kv "$OUT" NOW)
  L1=$(kv "$OUT" LOAD1);         L5=$(kv "$OUT" LOAD5);         L15=$(kv "$OUT" LOAD15)
  MT=$(kv "$OUT" MEM_TOTAL_KB);  MA=$(kv "$OUT" MEM_AVAIL_KB)
  ST=$(kv "$OUT" SWAP_TOTAL_KB); SF=$(kv "$OUT" SWAP_FREE_KB)
  DT=$(kv "$OUT" DISK_TOTAL_KB); DU=$(kv "$OUT" DISK_USED_KB);  DA=$(kv "$OUT" DISK_AVAIL_KB)
  DMNT=$(kv "$OUT" DISK_MNT);    BROOT=$(kv "$OUT" BUILD_ROOT)
  LC=$(kv "$OUT" LANE_COUNT);    LTK=$(kv "$OUT" LANE_TOTAL_KB)
  SWB=$(kv "$OUT" SWARM_BUILD);  CG=$(kv "$OUT" CGROUP)

  SU=$(( ${ST:-0} - ${SF:-0} ))
  MU=$(( ${MT:-0} - ${MA:-0} ))
  DPCT=$(pct "${DU:-0}" "${DT:-0}")
  SPCT=$(pct "$SU" "${ST:-0}")

  echo
  echo "=== $LABEL ==================================================================="
  printf '  host        %s, kernel %s, %s cores, %s GiB RAM\n' "$HN" "$KERN" "$NP" "$(gib "$MT")"
  printf '  load        %s / %s / %s   (over %s cores)\n' "$L1" "$L5" "$L15" "$NP"
  printf '  disk        %s  %s of %s GiB used (%s%%), %s GiB free   [holds %s]\n' \
         "$DMNT" "$(gib "$DU")" "$(gib "$DT")" "$DPCT" "$(gib "$DA")" "$BROOT"
  printf '  memory      %s GiB used, %s GiB available\n' "$(gib "$MU")" "$(gib "$MA")"
  printf '  swap        %s of %s GiB (%s%%)\n' "$(gib "$SU")" "$(gib "$ST")" "$SPCT"
  if [ "$DO_LANES" -eq 1 ]; then
    printf '  lanes       %s lanes, %s GiB total\n' "$LC" "$(gib "$LTK")"
  else
    printf '  lanes       %s lanes (sizes skipped: --no-lanes)\n' "$LC"
  fi

  # Records are selected on FIELD 1, never with `grep '^LANE'` — the key/value line
  # `LANE_COUNT=19` also starts with "LANE", and matching by prefix injected two phantom
  # lanes into the table (and, worse, made them look like real 0-byte lanes).
  rec() { awk -F'\t' -v t="$2" '$1==t' "$1"; }

  TMPFS_MAX_KB=0; TMPFS_WORST="-"
  if [ -n "$(rec "$OUT" TMPFS)" ]; then
    echo "  tmpfs       (RAM-backed: anything written here is charged as memory)"
    while IFS=$'\t' read -r _ mnt used size; do
      printf '                %-20s %8s of %8s GiB\n' "$mnt" "$(gib "$used")" "$(gib "$size")"
      if [ "${used:-0}" -gt "$TMPFS_MAX_KB" ]; then TMPFS_MAX_KB=$used; TMPFS_WORST=$mnt; fi
    done < <(rec "$OUT" TMPFS)
  fi

  NMAL=0; NHELD=0; NEXP=0; N_NOARCHIVE=0
  if [ "${LC:-0}" -gt 0 ]; then
    echo
    printf '  %-40s %11s  %-8s %-8s %-11s %s\n' LANE SIZE LEAN-AR MATHLIB "CARGO/deps" LEASE
    while IFS=$'\t' read -r _ name sz ar lean cargo ndeps lease lowner lexp; do
      if [ "${sz:-0}" -ge 0 ] 2>/dev/null; then szs="$(gib "$sz") GiB"; else szs="(skipped)"; fi
      case "$lease" in
        held)      lst="held by ${lowner}, $(( (lexp - NOWS) / 60 ))m left"; NHELD=$((NHELD+1)) ;;
        expired)   lst="expired (${lowner})"; NEXP=$((NEXP+1)) ;;
        malformed) lst="MALFORMED"; NMAL=$((NMAL+1)) ;;
        *)         lst="-" ;;
      esac
      [ "$ar" = no ] && N_NOARCHIVE=$((N_NOARCHIVE+1))
      printf '  %-40s %11s  %-8s %-8s %-11s %s\n' \
        "$name" "$szs" "$ar" "$lean" "${cargo}/${ndeps}" "$lst"
    done < <(rec "$OUT" LANE | sort -t$'\t' -k3,3rn)
  fi

  AGE_SECS=$(( PROC_AGE_DAYS * 86400 ))
  N_BUILD=0; N_WATCH=0; N_ALLOWED=0; N_SERVICE=0; PROC_TXT=""
  while IFS=$'\t' read -r _ cls pid age rss unit cmd; do
    [ "${age:-0}" -ge "$AGE_SECS" ] || continue
    dd=$(( age / 86400 )); hh=$(( (age % 86400) / 3600 ))
    if [ "$cls" = SERVICE ]; then
      N_SERVICE=$((N_SERVICE+1))
    elif allowed_proc "$cmd"; then
      N_ALLOWED=$((N_ALLOWED+1)); cls=ALLOWED
    else
      case "$cls" in BUILD) N_BUILD=$((N_BUILD+1)) ;; WATCHER) N_WATCH=$((N_WATCH+1)) ;; esac
    fi
    PROC_TXT="${PROC_TXT}    $(printf '%-7s %-8s %3sd%2sh %7s MiB  %-34s %s' \
      "$cls" "$pid" "$dd" "$hh" "$(( rss / 1024 ))" "${unit:0:34}" "${cmd:0:88}")
"
  done < <(rec "$OUT" PROC | sort -t$'\t' -k4,4rn)
  if [ -n "$PROC_TXT" ]; then
    echo
    echo "  OUR PROCESSES OLDER THAN ${PROC_AGE_DAYS}d — SERVICE = supervised by a systemd unit and"
    echo "  therefore meant to run forever; BUILD/WATCHER = orphaned in a session scope, i.e. rot"
    printf '  %-7s %-8s %6s %11s  %-34s %s\n' CLASS PID AGE RSS CGROUP-LEAF COMMAND
    printf '%s' "$PROC_TXT"
  fi

  echo
  echo "  CHECKS"

  if [ "${DPCT:-0}" -ge "$DISK_PCT" ]; then
    check disk-usage ALARM "${DPCT}% >= ${DISK_PCT}% on ${DMNT} ($(gib "$DA") GiB free)"
  else
    check disk-usage OK "${DPCT}% < ${DISK_PCT}% on ${DMNT} ($(gib "$DA") GiB free)"
  fi

  if [ "${SPCT:-0}" -ge "$SWAP_PCT" ]; then
    check swap-usage ALARM "${SPCT}% >= ${SWAP_PCT}% ($(gib "$SU") of $(gib "$ST") GiB)"
  else
    check swap-usage OK "${SPCT}% < ${SWAP_PCT}% ($(gib "$SU") of $(gib "$ST") GiB)"
  fi

  if [ "$DO_LANES" -eq 0 ]; then
    check lane-total INFO "not measured (--no-lanes); disk-usage still covers the volume"
  else
    LGB=$(awk -v k="${LTK:-0}" 'BEGIN{printf "%d", k/1048576}')
    if [ "$LGB" -ge "$LANES_GB" ]; then
      check lane-total ALARM "$(gib "$LTK") GiB >= ${LANES_GB} GiB over ${LC} lanes — the sweep is behind"
    else
      check lane-total OK "$(gib "$LTK") GiB < ${LANES_GB} GiB over ${LC} lanes"
    fi
  fi

  if [ "$N_BUILD" -gt 0 ]; then
    check stale-build-procs ALARM "${N_BUILD} of our build/test proc(s) older than ${PROC_AGE_DAYS}d (listed above)"
  else
    check stale-build-procs OK "none of ours older than ${PROC_AGE_DAYS}d"
  fi

  if [ "$N_WATCH" -gt 0 ]; then
    check leaked-watchers ALARM "${N_WATCH} watcher shell(s) older than ${PROC_AGE_DAYS}d — pgrep self-match spin-loops never exit"
  else
    check leaked-watchers OK "none older than ${PROC_AGE_DAYS}d"
  fi

  [ "$N_ALLOWED" -gt 0 ] && check allowlisted-procs INFO "${N_ALLOWED} matched --allow-proc, did not gate (still printed above)"
  [ "$N_SERVICE" -gt 0 ] && check supervised-services INFO "${N_SERVICE} long-lived process(es) are systemd units, so they do not gate (named above)"

  # swarm.slice's cap detail, reported separately from the kill count so a box with a healthy
  # count but a ceiling being hit thousands of times still says so out loud.
  if [ "$SWB" != yes ]; then
    check swarm-slice-cap "N/A" "swarm-build is not installed here, so no swarm.slice is expected"
  elif [ "$CG" = absent ]; then
    check swarm-slice-cap UNKNOWN "swarm-build IS installed but no swarm.slice exists — the shared build cap is NOT in force"
  else
    CGMH=$(kv "$OUT" CG_MAX_HIT)
    CGMAX=$(kv "$OUT" CG_MEM_MAX); CGCUR=$(kv "$OUT" CG_MEM_CUR); CGPK=$(kv "$OUT" CG_MEM_PEAK)
    check swarm-slice-cap INFO "cap $(awk -v b="${CGMAX:-0}" 'BEGIN{printf "%.0f", b/1073741824}')G, now $(awk -v b="${CGCUR:-0}" 'BEGIN{printf "%.1f", b/1073741824}')G, peak $(awk -v b="${CGPK:-0}" 'BEGIN{printf "%.1f", b/1073741824}')G, ceiling hit ${CGMH}x since boot"
  fi

  CGTOT=$(kv "$OUT" CG_OOM_TOTAL); WMK=$(kv "$OUT" CG_OOM_WATERMARK)
  ATTRIB=$(rec "$OUT" CGOOM | awk -F'\t' '{printf "%s=%s ", $3, $2}')
  if [ "$CGTOT" = unknown ]; then
    check cgroup-oom-new UNKNOWN "cannot read our user-manager cgroup's memory.events — OOM kills are uncountable"
  elif [ "$WMK" = unset ]; then
    check cgroup-oom-new INFO "cumulative=${CGTOT} [${ATTRIB}] — no watermark yet; --record arms the new-kill alarm"
  else
    DELTA=$(( ${CGTOT:-0} - ${WMK:-0} ))
    if [ "$DELTA" -gt "$OOM_MAX" ]; then
      check cgroup-oom-new ALARM "${DELTA} NEW oom_kill(s) since watermark ${WMK} (cumulative ${CGTOT}) [${ATTRIB}] — something died for ENVIRONMENT reasons, not its own"
    else
      check cgroup-oom-new OK "${DELTA} new since watermark ${WMK} (cumulative ${CGTOT}) [${ATTRIB}]"
    fi
  fi

  OOMJ=$(kv "$OUT" OOMJ)
  if [ "$OOMJ" = unknown ]; then
    check journal-oom UNKNOWN "user journal unreadable — cannot tell 'no kills' from 'did not look'"
  elif [ "${OOMJ:-0}" -gt "$OOM_MAX" ]; then
    check journal-oom ALARM "${OOMJ} OOM-kill event(s) in the journal since \"${OOM_SINCE}\" (> ${OOM_MAX})"
  else
    check journal-oom OK "${OOMJ} OOM-kill event(s) since \"${OOM_SINCE}\""
  fi

  EOK=$(kv "$OUT" EARLYOOM_KILLS); EOA=$(kv "$OUT" EARLYOOM_ACTIVE)
  if [ "$EOK" = unknown ]; then
    check earlyoom UNKNOWN "earlyoom journal unreadable"
  elif [ "$EOA" != active ]; then
    check earlyoom ALARM "earlyoom is '${EOA}', not active — the box has no last-resort killer"
  elif [ "${EOK:-0}" -gt "$OOM_MAX" ]; then
    check earlyoom ALARM "${EOK} earlyoom kill(s) since \"${OOM_SINCE}\"; it prefers cargo/rustc as the victim"
  else
    check earlyoom OK "active, ${EOK} kill(s) since \"${OOM_SINCE}\""
  fi

  TGB=$(awk -v k="${TMPFS_MAX_KB:-0}" 'BEGIN{printf "%d", k/1048576}')
  if [ "$TGB" -ge "$TMPFS_GB" ]; then
    check tmpfs-ram ALARM "$(gib "$TMPFS_MAX_KB") GiB on ${TMPFS_WORST} >= ${TMPFS_GB} GiB — that is RAM, charged against the build cap"
  else
    check tmpfs-ram OK "worst tmpfs $(gib "$TMPFS_MAX_KB") GiB (${TMPFS_WORST}) < ${TMPFS_GB} GiB"
  fi

  # Leases: an EXPIRED lease is BY DESIGN (a hint with an expiry must never wedge a lane),
  # so it is reported and does not gate. A MALFORMED one is a contract violation and gates.
  # The counts come from the same pass that rendered the table, so the table and the check
  # can never disagree about what was seen.
  if [ "$NMAL" -gt 0 ]; then
    check lease-contract ALARM "${NMAL} lease file(s) violate 'owner=<s> pid=<int> host=<s> expires=<unix>'"
  else
    check lease-contract OK "${NHELD} held, ${NEXP} expired, 0 malformed (expiry is the design, not rot)"
  fi

  # Both pinned copies get the same treatment. The sweep copy is load-bearing for the
  # nightly reclaim; the box-health copy is what the schedule actually executes, so a stale
  # one means the box is gating on yesterday's rules.
  copy_check() { # copy_check <check-name> <KEY prefix> <repo path>
    local nm="$1" pre="$2" repo="$3" bsha bfrom rsha
    bsha=$(kv "$OUT" "${pre}_SHA"); bfrom=$(kv "$OUT" "${pre}_FROM")
    if [ "$bsha" = absent ]; then
      check "$nm" ALARM "not installed on the box — the schedule that needs it cannot run"
    elif [ "$LOCAL" -eq 1 ] || [ ! -f "$repo" ]; then
      check "$nm" INFO "installed ${bsha:0:12}, provenance '${bfrom:-unknown}' (drift vs repo is only checkable from a checkout)"
    else
      rsha=$(sha_of "$repo")
      if [ "$bsha" = "$rsha" ]; then
        check "$nm" OK "byte-identical to the repo (${bsha:0:12}), provenance '${bfrom:-unknown}'"
      else
        check "$nm" ALARM "DRIFTED: box ${bsha:0:12} vs repo ${rsha:0:12} — re-install with 'scp' before trusting the schedule (see --help)"
      fi
    fi
  }
  copy_check sweep-copy      SWEEP_BUILD_LANES "$REPO_SWEEP"
  copy_check box-health-copy BOX_HEALTH        "${SELF_DIR}/box-health.sh"

  CH=$(kv "$OUT" CRON_HEALTH); CS=$(kv "$OUT" CRON_SWEEP)
  TH=$(kv "$OUT" TIMER_HEALTH); TS=$(kv "$OUT" TIMER_SWEEP)
  if [ "${CH:-0}" -gt 0 ] || [ "$TH" = enabled ]; then
    check schedule-health OK "scheduled (cron lines=${CH}, timer=${TH})"
  else
    check schedule-health ALARM "NOT scheduled (cron lines=${CH}, timer=${TH}) — nothing runs this check unattended"
  fi
  if [ "${CS:-0}" -gt 0 ] || [ "$TS" = enabled ]; then
    check schedule-sweep OK "scheduled (cron lines=${CS}, timer=${TS})"
  else
    check schedule-sweep ALARM "idle-lane sweep NOT scheduled (cron lines=${CS}, timer=${TS}) — lanes will grow unbounded again"
  fi

  printf '%s' "$CHECK_ROWS"

  if [ "$HOST_ALARMS" -eq 0 ]; then OUTCOME=OK; else OUTCOME=ALARM; fi
  ALARMS_TOTAL=$(( ALARMS_TOTAL + HOST_ALARMS ))
  echo
  printf 'box-health: VERDICT host=%s outcome=%s alarms=%s disk=%s%% swap=%s%% lanes=%sG lane_count=%s stale_procs=%s watchers=%s oomj=%s tmpfs=%sG\n' \
    "${HN:-$H}" "$OUTCOME" "$HOST_ALARMS" "$DPCT" "$SPCT" "$(gib "$LTK")" "$LC" "$N_BUILD" "$N_WATCH" "$OOMJ" "$(gib "$TMPFS_MAX_KB")"
done

echo
if [ "$ALARMS_TOTAL" -eq 0 ]; then
  echo "box-health: all checks OK across ${#HOSTS[@]} host(s)."
  exit 0
fi
echo "box-health: ${ALARMS_TOTAL} alarm(s) across ${#HOSTS[@]} host(s) — see the CHECKS tables above."
[ "$UNREACHABLE" -eq 1 ] && echo "box-health: at least one host was UNREACHABLE, which is itself the alarm."
exit 1
