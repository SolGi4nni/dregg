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
#   scripts/sweep-build-lanes.sh --root sweep-sandbox --min-gb 0   # a throwaway root, for
#                                                                 # testing the GUARD itself
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
# NO BETTER PROBE FIXES IT — no amount of process sniffing can see intent. So a lane carries a
# CLAIM, and this script refuses any lane whose claim is HELD, whatever is or is not running.
#
# ── THE MIRROR-IMAGE BUG, AND WHY THE LEASE IS NO LONGER A DURATION (2026-07-26) ──
# The first version of the lease was a DURATION — `expires = now + 3600`, honoured until that
# clock ran out — and that failed as hard in the other direction, measured the same night:
#
#   * pbuild stamps a lease on EVERY invocation with TTL 3600, so a two-minute `cargo check`
#     blocked this sweep for an hour. A 30× over-claim per build, per lane.
#   * A holder that EXITS never released. SIX lanes (crewbraid, darkpool, fnsp-v3-state,
#     native-anchor, packed-merkle, proof-backend-seam) were held by leases whose owner pids
#     were ALL DEAD, with 900-2800s still on the clock. `lane-lease.sh reap-expired` could not
#     help: they were not EXPIRED, they were ORPHANED, and nothing had a word for that. Its
#     report — "0 cleared, 6 still held" — was true and useless.
#   * Net: ~500 GB accumulated to 95% of persvati's disk while only ~12 GB was collectable.
#     A guard built so cleanup would stop deleting under live agents had become a guard under
#     which cleanup could essentially never run.
#
# So the primary signal is LIVENESS and duration is a BACKSTOP. Per HOLDER RECORD:
#
#   pid ALIVE on its host   →  HOLDS, whatever `expires` says (bounded by the ceiling below)
#   pid DEAD on its host    →  does NOT hold, whatever `expires` says, past a short GRACE of
#                              `mtime + SWEEP_ORPHAN_GRACE` (default 300s)
#   liveness UNDETERMINABLE →  the TTL BACKSTOP decides: `expires`, under the ceiling. That is
#                              `pid=0` (the anchorless sentinel), a torn record, or a `host=`
#                              which is neither this box nor the client running this sweep.
#
# ── WHERE LIVENESS CAN BE EVALUATED, WHICH IS THE WHOLE STRUCTURAL PROBLEM ─────
# Every lease in the wild read `host=nextop`: the holders are pids on the CLIENT, and the lease
# file lives on the BOX. The old reader ran entirely inside this script's remote heredoc, so it
# COULD NOT check whether a nextop pid was alive and had nothing but the clock to go on. The
# duration model was not a choice, it was a consequence of where the check ran.
#
# The fix is to give the box the one fact it cannot obtain: THE CLIENT'S LIVENESS SNAPSHOT.
# `ps -A -o pid=` is taken on the client immediately before the ssh and passed as data; the box
# resolves each record as
#
#   host == the box's own hostname     →  check it locally (`/proc/<pid>`)
#   host == this client's hostname     →  member of the snapshot ⟺ alive
#   anything else                      →  undeterminable → TTL backstop
#
# SOUND BECAUSE DEADNESS IS MONOTONE. A snapshot can only go stale in the direction of "reports
# alive, has since died", which makes this guard MORE conservative — it never frees a lane it
# should have kept. The opposite staleness — a holder that registered AFTER the snapshot, which
# is precisely the agent this whole block exists to protect — is covered by the grace, and that
# is the grace's main job. Pid REUSE can make a corpse read alive, which again fails closed.
#
# It also keeps read → decide → delete inside ONE remote shell, so the mid-scan re-check below
# still runs in the same process as the `rm`. A dump-to-client / decide / act-remote round trip
# would have re-opened exactly that window to buy no extra information.
#
#   THE CONTRACT (with scripts/pbuild, scripts/lane-lease.sh, scripts/box-health.sh):
#     <root>/.leases/<lane>.lease   the holder SET, one record per line, AUTHORITATIVE
#     <lane dir>/.pbuild-lease      a SINGLE-LINE interop mirror (pbuild writes it, box-health
#                                   reads it), rsync-exposed, which is why the set is elsewhere
#     record: owner=<string> pid=<int> host=<string> expires=<unix-seconds>   (pid=0 = anchorless)
#     read the UNION of both files, keyed by (owner, host); HELD ⟺ ANY record holds
#
#   scripts/lane-lease.sh acquire       --lane crewbraid --owner agent:me   # before you use a lane
#   scripts/lane-lease.sh release       --lane crewbraid --owner agent:me   # when you are done
#   scripts/lane-lease.sh reap-orphaned                                     # clear the corpses
#
# BELT AND BRACES, DELIBERATELY: the process check STAYS. A lease catches an owner who is not
# compiling; the process probe catches a build nobody declared (a bare `ssh persvati cargo …`,
# or an agent that never learned about leases). They fail in opposite directions and neither
# subsumes the other — and the probe is now also what covers a build whose declaring session
# died mid-compile.
#
# THERE IS DELIBERATELY NO --ignore-leases FLAG: a knob like that is what an agent reaches for
# reflexively, and then the guard cannot say no. Three things keep a stale lease from wedging a
# lane instead, and the first is what the 2026-07-26 rework added:
#   1. a DEAD holder stops counting after SWEEP_ORPHAN_GRACE, whatever its clock claims — an
#      ORPHANED lane is SWEPT and the report says whose corpse held it;
#   2. `lane-lease.sh reap-expired` clears expired, unparseable AND orphaned records;
#      `reap-orphaned` clears only the corpses;
#   3. the effective-expiry CEILING of mtime + SWEEP_LEASE_MAX_AGE (default 86400) binds every
#      record no matter what `expires=` claims AND no matter how alive its pid is, so neither a
#      writer that stamps `expires=9999999999` nor a holder anchored to an immortal process can
#      hold a lane for more than a day.
# To take a lane from an owner you know is gone: `lane-lease.sh release --lane X --force`, or
# `acquire --force` to claim it. That is two deliberate steps, which is the right price.
#
# A TORN RECORD FAILS CLOSED. An unparseable line is read as `mtime + SWEEP_LEASE_TTL_FALLBACK`
# with liveness forced to UNKNOWN — a half-written record's `pid` could be a truncated number
# naming an unrelated process, so it is not trusted either. It is reported ⚠unparseable, and it
# still expires, so a write interrupted mid-rename costs an agent nothing and wedges nothing.
#
# THIS SCRIPT NEVER DELETES A LEASE FILE, not even an orphaned one. Reaping records is
# `lane-lease.sh`'s job and reporting is this one's; a cleanup tool that also rewrites the
# ownership records it consults is a tool whose two failure modes multiply.
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
ROOT_REL="${SWEEP_ROOT:-dregg-build}"
# Lease reading knobs. MAX_AGE is the ceiling that makes "cannot wedge a lane" structural;
# TTL_FALLBACK is how long an unparseable record is honoured from its mtime; ORPHAN_GRACE is how
# long a record whose anchor pid is DEAD is still honoured, which is what makes the client's
# liveness snapshot race fail closed. All three are read here and passed to the remote shell, so
# the two sides can never disagree about the numbers.
LEASE_MAX_AGE="${SWEEP_LEASE_MAX_AGE:-86400}"
LEASE_TTL_FALLBACK="${SWEEP_LEASE_TTL_FALLBACK:-3600}"
ORPHAN_GRACE="${SWEEP_ORPHAN_GRACE:-300}"

while [ $# -gt 0 ]; do
  case "$1" in
    --host)   HOST="$2"; shift 2 ;;
    --lane)   LANES+=("$2"); shift 2 ;;
    --root)   ROOT_REL="$2"; shift 2 ;;
    --apply)  APPLY=1; shift ;;
    --min-gb) MIN_GB="$2"; shift 2 ;;
    -h|--help) awk 'NR>1 && /^set -euo pipefail$/{exit} NR>1{print}' "$0"; exit 0 ;;
    *) echo "sweep-build-lanes: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

case "$MIN_GB" in ''|*[!0-9]*) echo "sweep-build-lanes: --min-gb must be an integer" >&2; exit 2 ;; esac
for _n in LEASE_MAX_AGE LEASE_TTL_FALLBACK ORPHAN_GRACE; do
  case "${!_n}" in ''|*[!0-9]*) echo "sweep-build-lanes: $_n must be a non-negative integer" >&2; exit 2 ;; esac
done
case "$ROOT_REL" in *[[:space:]]*) echo "sweep-build-lanes: --root must not contain whitespace" >&2; exit 2 ;; esac

if ! ssh -o BatchMode=yes -o ConnectTimeout=8 "$HOST" true 2>/dev/null; then
  echo "sweep-build-lanes: cannot reach '$HOST'." >&2
  exit 2
fi

LANE_FILTER=""
if [ "${#LANES[@]}" -gt 0 ]; then LANE_FILTER="$(printf '%s\n' "${LANES[@]}")"; fi

# ── THE CLIENT'S LIVENESS SNAPSHOT ─────────────────────────────────────────────
# The one fact the box cannot obtain for itself (see the structural note in the header). Taken
# HERE, immediately before dispatch. Comma-delimited with sentinel commas at both ends so the
# box's membership test is a plain `case` glob and needs no loop.
#
# If it comes back empty the box gets NO client oracle and falls back to the TTL for every
# client-hosted record — i.e. it fails CLOSED to the pre-2026-07-26 behaviour rather than
# concluding that every holder is dead and sweeping the fleet.
CLIENT_HOST="$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo unknown)"
CLIENT_PIDS="$( { ps -A -o pid= 2>/dev/null || ps -eo pid= 2>/dev/null || true; } | tr -cd '0-9\n' | tr '\n' ',' )"
case "$CLIENT_PIDS" in
  ''|*[!0-9,]*) CLIENT_PIDS="" ;;
  *) CLIENT_PIDS=",${CLIENT_PIDS}" ;;
esac
if [ -z "$CLIENT_PIDS" ]; then
  echo "sweep-build-lanes: ⚠ could not snapshot this client's pids — every host=$CLIENT_HOST" >&2
  echo "                   record will fall back to its TTL, as it did before 2026-07-26." >&2
fi

# ── the remote program ────────────────────────────────────────────────────────
# ONE quoted heredoc into a variable, dispatched with %q-quoted positional arguments. The
# previous form was an UNQUOTED `<<REMOTE`, which meant every `$` in ~240 lines of remote shell
# needed a `\$` and one missed escape would have been evaluated on the client. The lease reader
# below is far too much code to write through that.
#
# Everything runs on the remote in ONE shell, so liveness is checked in the same process that
# does the deleting — no window between the check and the rm.
SWEEP_PROGRAM_BODY=$(cat <<'PROGRAM'
set -uo pipefail
APPLY="$1"; MIN_BYTES="$2"; LANE_FILTER="$3"; LEASE_MAX_AGE="$4"; LEASE_TTL_FALLBACK="$5"
ORPHAN_GRACE="$6"; ROOT_REL="$7"; CLIENT_HOST="$8"; CLIENT_PIDS="$9"

case "$ROOT_REL" in /*) ROOT="$ROOT_REL" ;; *) ROOT="$HOME/$ROOT_REL" ;; esac
RBASE="$(basename "$ROOT")"
BOX_HOST="$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo unknown)"
TAB="$(printf '\t')"

# Per-run temp dir. The previous version used fixed `/tmp/sweep-orphans.awk` and
# `/tmp/sweep-<lane>.list`, which two concurrent sweeps — entirely normal with ~10 terminals —
# would have written over each other, one of them deleting from the other's file list.
TMPD="$(mktemp -d "${TMPDIR:-/tmp}/sweep-lanes.XXXXXX")" || exit 2
trap 'rm -rf "$TMPD"' EXIT

# ══ THE LEASE READER ══════════════════════════════════════════════════════════
# Reads the DECLARED claim as a SET of holder records, and decides each one by LIVENESS first
# and the clock second (see the header). Two files are unioned because the mirror path
# `<lane>/.pbuild-lease` sits at the root of pbuild's rsync destination and `rsync --delete`
# will remove it (MEASURED 2026-07-26 on the real command; the repo .gitignore entry protects it
# only once the RECEIVER's copy of .gitignore carries the rule, since a per-directory merge file
# is read by each side from its own tree). The sidecar under `.leases/` is outside every lane dir
# and therefore outside every rsync destination.
#
# ⚠ THIS IS A SECOND IMPLEMENTATION of the rules in scripts/lane-lease.sh, and that is a real
# drift risk, not a tidy separation: it lives here because the verdict is needed INSIDE the
# remote shell (for the mid-scan re-check, in the same process as the rm), and shelling out to
# lane-lease.sh would be one ssh per lane from the client and would not be re-checkable
# mid-scan. The fix is to extract the reader into a single shared include that both scripts
# inline at dispatch time; until then, any change to the liveness table must be made in BOTH.
#
# All names are LL_/LR_-prefixed on purpose: this runs in the same shell as the sweep loop,
# which owns $L, $d, $n and friends, and a helper that clobbers the caller's loop variable is a
# bug that shows up as a lane being skipped or swept at random.
LL_live_verdict() {                      # LL_live_verdict <pid> <host> -> alive|dead|anchorless|unknown
  LR_p="$1"; LR_h="$2"
  case "$LR_p" in ''|*[!0-9]*) echo unknown; return ;; esac
  [ "$LR_p" = 0 ] && { echo anchorless; return; }
  if [ "$LR_h" = "$BOX_HOST" ]; then
    # /proc is owner-independent; `kill -0` reports EPERM as failure and would call another
    # user's live process dead.
    if [ -d /proc ]; then
      if [ -d "/proc/$LR_p" ]; then echo alive; else echo dead; fi
    elif kill -0 "$LR_p" 2>/dev/null || ps -p "$LR_p" >/dev/null 2>&1; then echo alive
    else echo dead
    fi
    return
  fi
  if [ -n "$CLIENT_HOST" ] && [ "$LR_h" = "$CLIENT_HOST" ]; then
    case "$CLIENT_PIDS" in
      '')           echo unknown ;;
      *",$LR_p,"*)  echo alive ;;
      *)            echo dead ;;
    esac
    return
  fi
  echo unknown
}

LL_RECS=""
LL_read_file() {                         # LL_read_file <file> <where-tag>
  LR_f="$1"; LR_tag="$2"
  [ -f "$LR_f" ] || return 0
  LR_mt="$(stat -c %Y "$LR_f" 2>/dev/null || stat -f %m "$LR_f" 2>/dev/null || echo 0)"
  case "$LR_mt" in ''|*[!0-9]*) LR_mt=0 ;; esac
  while IFS= read -r LR_line || [ -n "$LR_line" ]; do
    case "$LR_line" in '') continue ;; esac
    LR_o=""; LR_pp=""; LR_hh=""; LR_e=""
    for LR_tok in $LR_line; do
      case "$LR_tok" in
        owner=*)   LR_o="${LR_tok#owner=}" ;;
        pid=*)     LR_pp="${LR_tok#pid=}" ;;
        host=*)    LR_hh="${LR_tok#host=}" ;;
        expires=*) LR_e="${LR_tok#expires=}" ;;
      esac
    done
    LR_mal=0
    case "$LR_e" in ''|*[!0-9]*) LR_mal=1; LR_e=0 ;; esac
    case "$LR_pp" in ''|*[!0-9]*) LR_mal=1; LR_pp=0 ;; esac
    [ -n "$LR_o" ] || { LR_o="-"; LR_mal=1; }
    [ -n "$LR_hh" ] || { LR_hh="-"; LR_mal=1; }
    LL_RECS="${LL_RECS}${LR_o}${TAB}${LR_pp}${TAB}${LR_hh}${TAB}${LR_e}${TAB}${LR_mt}${TAB}${LR_mal}${TAB}${LR_tag}
"
  done < "$LR_f"
}

# A record is IDENTIFIED by (owner, host): one claimant on one machine has one claim. Merged in
# awk because the merge needs a keyed map.
LL_STATE=absent; LL_OWNER=-; LL_PID=-; LL_CHOST=-; LL_REM=0; LL_MAL=0; LL_WHERE=none
LL_N=0; LL_HELD=0; LL_LIVE=-; LL_WHY=-; LL_CORPSE=0; LL_CORPSE_OWNER=-; LL_CORPSE_PID=-
lease_state() {
  LR_lane="$1"
  LL_STATE=absent; LL_OWNER=-; LL_PID=-; LL_CHOST=-; LL_REM=0; LL_MAL=0; LL_WHERE=none
  LL_N=0; LL_HELD=0; LL_LIVE=-; LL_WHY=-; LL_CORPSE=0; LL_CORPSE_OWNER=-; LL_CORPSE_PID=-
  LL_RECS=""
  LL_read_file "$ROOT/$LR_lane/.pbuild-lease" contract
  LL_read_file "$ROOT/.leases/$LR_lane.lease" sidecar
  [ -n "$LL_RECS" ] || return 0
  LL_RECS="$(printf '%s' "$LL_RECS" | awk -F'\t' '
    NF < 7 { next }
    { k = $1 "|" $3
      if (k in SEEN) { if (W[k] != $7) W[k] = "both" } else { SEEN[k] = 1; W[k] = $7 }
      if (!(k in E) || ($4+0) > (E[k]+0) || (($4+0) == (E[k]+0) && ($5+0) > (M[k]+0))) {
        O[k]=$1; P[k]=$2; H[k]=$3; E[k]=$4; M[k]=$5; L[k]=$6
      }
    }
    END { for (k in SEEN) printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n", O[k],P[k],H[k],E[k],M[k],L[k],W[k] }
  ' | sort)"
  LR_now="$(date +%s)"
  LR_brank=-1; LR_best=-1
  while IFS="$TAB" read -r LR_o LR_pp LR_hh LR_e LR_mt LR_mal LR_wh; do
    [ -n "${LR_o:-}" ] || continue
    LL_N=$(( LL_N + 1 ))
    LR_v="$(LL_live_verdict "$LR_pp" "$LR_hh")"
    [ "$LR_mal" -eq 1 ] && LR_v=unknown
    LR_ceil=$(( LR_mt + LEASE_MAX_AGE ))
    if [ "$LR_mal" -eq 1 ]; then LR_eff=$(( LR_mt + LEASE_TTL_FALLBACK )); else LR_eff="$LR_e"; fi
    [ "$LR_eff" -gt "$LR_ceil" ] && LR_eff="$LR_ceil"
    LR_rem=$(( LR_eff - LR_now ))
    case "$LR_v" in
      alive)
        # LIVENESS DOMINATES THE CLOCK IN BOTH DIRECTIONS, bounded only by the ceiling.
        if [ "$LR_ceil" -gt "$LR_now" ]; then LR_hold=1; LR_why=live; else LR_hold=0; LR_why=ceiling; fi ;;
      dead)
        if [ $(( LR_mt + ORPHAN_GRACE )) -gt "$LR_now" ]; then LR_hold=1; LR_why=grace; else LR_hold=0; LR_why=corpse; fi ;;
      *)
        if [ "$LR_rem" -gt 0 ]; then LR_hold=1; LR_why=ttl; else LR_hold=0; LR_why=expired; fi ;;
    esac
    if [ "$LR_hold" -eq 1 ]; then
      LL_HELD=$(( LL_HELD + 1 ))
    elif [ "$LR_why" = corpse ]; then
      LL_CORPSE=$(( LL_CORPSE + 1 ))
      [ "$LL_CORPSE_OWNER" = "-" ] && { LL_CORPSE_OWNER="$LR_o"; LL_CORPSE_PID="$LR_pp@$LR_hh"; }
    fi
    # PRINCIPAL: a holding record always outranks a stale one, then the later effective expiry.
    LR_rank=$(( LR_hold * 2 ))
    if [ "$LR_rank" -gt "$LR_brank" ] || { [ "$LR_rank" -eq "$LR_brank" ] && [ "$LR_eff" -gt "$LR_best" ]; }; then
      LR_brank="$LR_rank"; LR_best="$LR_eff"
      LL_OWNER="$LR_o"; LL_PID="$LR_pp"; LL_CHOST="$LR_hh"; LL_REM="$LR_rem"
      LL_MAL="$LR_mal"; LL_WHERE="$LR_wh"; LL_LIVE="$LR_v"; LL_WHY="$LR_why"
    fi
  done <<EOF
$LL_RECS
EOF
  if   [ "$LL_HELD" -gt 0 ];  then LL_STATE=held
  elif [ "$LL_CORPSE" -gt 0 ]; then LL_STATE=orphaned
  else LL_STATE=expired
  fi
}

# ══ LIVENESS OF BUILDS, FAIL-CLOSED ══════════════════════════════════════════
# Counts only REAL build processes (cargo/rustc/lake/lean/cc/ld) attributed to the
# lane by cwd or by cmdline. Deliberately NOT `pgrep -f "<root>/$L"`: that form
# matches the probing shell's OWN command line (it contains the lane name), so it
# both false-positives and — paired with `pgrep -c || echo 0`, which prints "0"
# twice because pgrep exits 1 on an empty match — silently FAILS OPEN. That bug was
# live in the first version of this sweep on 2026-07-25 and only did no damage
# because the lane really was idle. A guard that cannot say no is not a guard.
#
# The match is `<root basename>/<lane>` rather than a hardcoded `dregg-build/<lane>` so that
# --root actually changes what the probe looks at; for the default root the string is identical
# to what it always was.
live_count() {
  L="$1"; c=0
  for p in $(pgrep -x cargo 2>/dev/null; pgrep -x rustc 2>/dev/null; \
             pgrep -x lake 2>/dev/null; pgrep -x lean 2>/dev/null; \
             pgrep -x cc 2>/dev/null; pgrep -x ld 2>/dev/null); do
    d=$(readlink -f "/proc/$p/cwd" 2>/dev/null || true)
    case "$d" in *"$RBASE/$L"*) c=$((c+1)); continue ;; esac
    # A process can exit between pgrep and this read. The failure is then reported by
    # the SHELL (a redirect on a vanished path), so `tr … 2>/dev/null` cannot mute it —
    # the whole compound needs the redirect. Guard with -r as well so the common case
    # never enters an error path at all.
    [ -r "/proc/$p/cmdline" ] || continue
    if { tr '\0' ' ' < "/proc/$p/cmdline" || true; } 2>/dev/null | grep -q "$RBASE/$L"; then
      c=$((c+1))
    fi
  done
  echo "$c"
}

cat > "$TMPD/orphans.awk" <<'AWK'
# TWO-PHASE. Classification happens only in END, after every hash for every crate
# has been seen. A streaming "is this the newest so far" test is order-dependent and
# gets the answer wrong in BOTH directions — it over-counted orphans by 4x and
# under-counted by 9x on two passes over the same tree before this was fixed.
{ ts=$1+0; sz=$2+0; p=$3; f=$4;
  stem=f; sub(/\.(d|rlib|rmeta|so|a|dylib)$/,"",stem);
  if (!match(stem,/-[0-9a-f]{16}$/)) next;   # not a fingerprinted artifact; leave it
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

# Adaptive unit. A fixed "%.1f GB" renders every sandbox and every freshly-swept lane as
# "0.0 GB", which is the column silently refusing to answer the question it exists for.
gb() { awk -v b="$1" 'BEGIN{ if (b < 1073741824) printf "%.1f MB", b/1048576; else printf "%.1f GB", b/1073741824 }'; }

printf '%-24s %10s %10s %10s   %s\n' LANE KEEP ORPHAN TOTAL STATUS
swept_total=0
n_acted=0; n_lease=0; n_live=0; n_minGB=0; n_expired=0; n_orphaned=0
for dir in "$ROOT"/*/; do
  [ -d "$dir" ] || continue
  L=$(basename "$dir")
  # The lease SIDECAR directory is not a lane. The dot in `.leases` is what actually keeps it
  # out of this glob (and out of pbuild's warm-lane enumeration, which is the same `*/` shape)
  # — VERIFIED: bash `*/` does not match a leading dot without dotglob. This line is the
  # belt to that brace, for a future caller that sets dotglob or moves the root.
  [ "$L" = ".leases" ] && continue
  if [ -n "$LANE_FILTER" ] && ! printf '%s\n' "$LANE_FILTER" | grep -qx "$L"; then continue; fi

  found=0
  for prof in debug release; do
    for sub in deps examples; do
      [ -d "$dir/target/$prof/$sub" ] && found=1
    done
  done
  [ "$found" -eq 1 ] || continue

  {
    for prof in debug release; do
      for sub in deps examples; do
        d="$dir/target/$prof/$sub"; [ -d "$d" ] || continue
        find "$d" -maxdepth 1 -type f -printf '%T@\t%s\t%p\t%f\n' 2>/dev/null
      done
    done
  } | awk -F'\t' -v LIST=0 -f "$TMPD/orphans.awk" 2>"$TMPD/stat.txt" >/dev/null || true

  read -r ksz kn osz on < "$TMPD/stat.txt" 2>/dev/null || { ksz=0; kn=0; osz=0; on=0; }
  tot=$(( ksz + osz ))

  # ── LEASE FIRST. A leased lane is never described as "would sweep" or "below threshold":
  # the declaration outranks both, and an operator reading this report needs to see WHO holds
  # it, not a size verdict on a lane that is not available.
  lease_state "$L"
  if [ "$LL_STATE" = held ]; then
    n_lease=$(( n_lease + 1 ))
    lextra=""
    [ "$LL_MAL" -eq 1 ] && lextra=" ⚠unparseable-record, honoured for one TTL"
    [ "$LL_CORPSE" -gt 0 ] && lextra="$lextra ⚠${LL_CORPSE} dead holder(s) alongside"
    # `live=<verdict>/<rule>` is printed rather than just the rule, because the two together are
    # what answers "is the TTL still deciding this, and why": alive/live and dead/grace are
    # liveness doing the work, while unknown/ttl and anchorless/ttl are the BACKSTOP deciding —
    # and if a fleet's rows are mostly the latter, the client oracle is not reaching those hosts.
    printf '%-24s %10s %10s %10s   LEASED by %s (pid %s on %s, live=%s/%s, ttl_left %ss, %s of %s holder(s), %s)%s — SKIPPED\n' \
      "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" \
      "$LL_OWNER" "$LL_PID" "$LL_CHOST" "$LL_LIVE" "$LL_WHY" "$LL_REM" "$LL_HELD" "$LL_N" "$LL_WHERE" "$lextra"
    continue
  fi
  # NOT held. Say WHICH kind of not-held, because they call for different responses: an ORPHANED
  # lane means a holder died without releasing and the sweep is about to do what the old
  # duration-based reader could not, while an EXPIRED one merely ran out of clock. This rides on
  # the SAME row as the eventual verdict rather than printing its own — a second row per lane
  # reads as a duplicate lane, and the whole argument for this report is that a reader can tell
  # its skip reasons apart at a glance.
  lpre=""
  if [ "$LL_STATE" = orphaned ]; then
    n_orphaned=$(( n_orphaned + 1 ))
    lpre="$(printf 'ORPHANED lease (%s, anchor %s is DEAD, %s record(s)) — ' "$LL_CORPSE_OWNER" "$LL_CORPSE_PID" "$LL_CORPSE")"
  elif [ "$LL_STATE" = expired ]; then
    n_expired=$(( n_expired + 1 ))
    lpre="$(printf 'EXPIRED lease (%s) — ' "$LL_OWNER")"
  fi

  if [ "$osz" -lt "$MIN_BYTES" ]; then
    n_minGB=$(( n_minGB + 1 ))
    printf '%-24s %10s %10s %10s   %sbelow --min-gb, skipped\n' "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" "$lpre"
    continue
  fi

  n=$(live_count "$L")
  if [ "$n" -ne 0 ]; then
    n_live=$(( n_live + 1 ))
    printf '%-24s %10s %10s %10s   %sLIVE (%s build procs) — SKIPPED\n' "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" "$lpre" "$n"
    continue
  fi

  if [ "$APPLY" -ne 1 ]; then
    n_acted=$(( n_acted + 1 ))
    printf '%-24s %10s %10s %10s   %sidle, unleased — would sweep %s files\n' "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" "$lpre" "$on"
    continue
  fi

  {
    for prof in debug release; do
      for sub in deps examples; do
        d="$dir/target/$prof/$sub"; [ -d "$d" ] || continue
        find "$d" -maxdepth 1 -type f -printf '%T@\t%s\t%p\t%f\n' 2>/dev/null
      done
    done
  } | awk -F'\t' -v LIST=1 -f "$TMPD/orphans.awk" 2>/dev/null > "$TMPD/list.$L" || true

  # Re-check BOTH signals immediately before deleting: the listing walk takes time, and a lane
  # can wake up or be CLAIMED during it. Same process, so there is no ssh round-trip window.
  # The lease re-check matters most in exactly the case this whole block exists for — an agent
  # that starts work on a lane the sweep has already decided to empty. Note that such an agent's
  # pid is NOT in the client snapshot taken before this ssh, so it reads as `dead`; the
  # ORPHAN_GRACE is what makes that read HOLD the lane instead of losing the race.
  lease_state "$L"
  if [ "$LL_STATE" = held ]; then
    n_lease=$(( n_lease + 1 ))
    printf '%-24s %10s %10s %10s   CLAIMED mid-scan by %s (%s, ttl_left %ss) — ABORTED, nothing deleted\n' \
      "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" "$LL_OWNER" "$LL_LIVE/$LL_WHY" "$LL_REM"
    continue
  fi
  n2=$(live_count "$L")
  if [ "$n2" -ne 0 ]; then
    n_live=$(( n_live + 1 ))
    printf '%-24s %10s %10s %10s   woke up mid-scan (%s procs) — ABORTED, nothing deleted\n' "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" "$n2"
    continue
  fi

  xargs -a "$TMPD/list.$L" -d '\n' -r rm -f
  swept_total=$(( swept_total + osz ))
  n_acted=$(( n_acted + 1 ))
  printf '%-24s %10s %10s %10s   %sSWEPT %s files\n' "$L" "$(gb $ksz)" "$(gb $osz)" "$(gb $tot)" "$lpre" "$on"
done

echo
# WHY THE SKIP REASONS ARE COUNTED SEPARATELY: "3 lanes skipped" is the report that let the
# 2026-07-25 mis-sweep look normal. A LEASE skip means someone said the lane is theirs; a LIVE
# skip means a build is running that nobody declared; an ORPHANED lease means someone SAID it was
# theirs and then died. They call for opposite responses — wait, go look at what is compiling, or
# reap the corpse — so a report that merges them has thrown away the actionable half. All are
# stated even when zero, so a reader can tell "no leases were consulted" from "no lanes were
# leased".
if [ "$APPLY" -eq 1 ]; then
  printf 'lanes: %s swept | %s skipped for a HELD lease | %s skipped for live build procs | %s below --min-gb\n' \
    "$n_acted" "$n_lease" "$n_live" "$n_minGB"
  printf 'reclaimed: %s\n' "$(gb "$swept_total")"
else
  printf 'lanes: %s would be swept | %s skipped for a HELD lease | %s skipped for live build procs | %s below --min-gb\n' \
    "$n_acted" "$n_lease" "$n_live" "$n_minGB"
  echo "(report only — pass --apply to sweep idle, unleased lanes)"
fi
if [ -z "$CLIENT_PIDS" ]; then
  printf '⚠ NO client liveness oracle this run: every host=%s record fell back to its TTL.\n' "$CLIENT_HOST"
fi
if [ "$n_orphaned" -gt 0 ]; then
  printf '%s lane(s) were held by a CORPSE — a holder that exited without releasing. Swept as\n' "$n_orphaned"
  printf 'unleased (that is the 2026-07-26 fix). The stale records are left in place for you to see;\n'
  printf 'clear them with:\n'
  printf '  scripts/lane-lease.sh reap-orphaned --host %s\n' "$BOX_HOST"
fi
if [ "$n_expired" -gt 0 ]; then
  printf '%s lane(s) carried an EXPIRED lease (ignored, as designed). Clear them with:\n' "$n_expired"
  printf '  scripts/lane-lease.sh reap-expired --host %s\n' "$BOX_HOST"
fi
df -h / | tail -1
PROGRAM
)

MIN_BYTES=$(( MIN_GB * 1073741824 ))
sweep_args=("$APPLY" "$MIN_BYTES" "$LANE_FILTER" "$LEASE_MAX_AGE" "$LEASE_TTL_FALLBACK" \
            "$ORPHAN_GRACE" "$ROOT_REL" "$CLIENT_HOST" "$CLIENT_PIDS")
_q=()
for _a in "${sweep_args[@]}"; do _q+=("$(printf '%q' "$_a")"); done
# shellcheck disable=SC2029 # every argument is %q-quoted immediately above.
printf '%s\n' "$SWEEP_PROGRAM_BODY" | ssh "$HOST" "bash -s -- ${_q[*]}"
