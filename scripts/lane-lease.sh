#!/usr/bin/env bash
# lane-lease.sh — declare that a remote build lane is OWNED, so cleanup tools leave it alone.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# `scripts/sweep-build-lanes.sh` decided a lane was free to sweep by looking for build
# processes (cargo/rustc/lake/lean/cc/ld) attributed to it. That probe answers "is this lane
# COMPILING right now", and the question that matters is "does this lane belong to someone".
# They are different questions and the gap between them is most of an agent's wall clock: an
# agent that owns a lane spends its time reading, thinking and writing a report, and compiles
# in bursts. On 2026-07-25 ember swept `darkpool` and `native-anchor` out from under two live
# agents in exactly that window. Measured cost: persvati went 497 GB free → 414 GB as those
# lanes rebuilt what had been deleted.
#
# The damage is bounded — a fingerprint miss is a REBUILD, never a stale link, which is the
# whole safety argument of the sweep — but the owning agent pays a rebuild it did not ask for,
# and a sweep landing during a LINK surfaces inside that agent as an unexplained error it may
# well misdiagnose as its own bug. That is the expensive kind of wrong.
#
# NO BETTER PROBE FIXES THIS. No amount of process sniffing can see intent. Ownership has to
# be DECLARED. This script is that declaration.
#
# ── THE MIRROR-IMAGE BUG, AND WHY THE MODEL CHANGED (2026-07-26) ───────────────
# The first version of this file made a lease a DURATION: `expires = now + 3600`, and a reader
# honoured it until that clock ran out. That is the wrong primitive, and the cost was measured
# the same night:
#
#   * pbuild stamps a lease on EVERY invocation with TTL 3600. A two-minute `cargo check`
#     therefore blocked cleanup for an hour — a 30× over-claim, per build, per lane.
#   * A holder that EXITS never releases. Six lanes (crewbraid, darkpool, fnsp-v3-state,
#     native-anchor, packed-merkle, proof-backend-seam) were found held by leases whose owner
#     pids were ALL DEAD, with 900–2800s still on the clock. `reap-expired` could not help:
#     those leases were not EXPIRED, they were ORPHANED, and the tool had no word for that.
#     Its report — "0 cleared, 6 still held" — was true and useless.
#   * Net effect on persvati: ~500 GB accumulated to 95% of the disk while only ~12 GB of it
#     was collectable orphan generations. A guard built so cleanup would stop deleting under
#     live agents had become a guard under which cleanup could essentially never run.
#
# So the primary signal is now LIVENESS, and duration is only a BACKSTOP. Per HOLDER RECORD:
#
#   pid ALIVE on its host   →  HOLDS, whatever `expires` says (bounded by the ceiling below).
#                              A 90-minute build no longer loses its claim at minute 60, and
#                              nothing has to refresh anything.
#   pid DEAD on its host    →  does NOT hold, whatever `expires` says — past a short GRACE of
#                              `mtime + LANE_LEASE_ORPHAN_GRACE` (default 300s). That is the
#                              corpse case above: an hour of phantom claim becomes ~5 minutes.
#   liveness UNDETERMINABLE →  the TTL BACKSTOP decides: `expires`, under the ceiling. This is
#                              `pid=0` (the explicit anchorless sentinel), a torn record, or a
#                              `host=` that is neither the box nor the calling client.
#
# WHY THE GRACE EXISTS, since "dead is dead" would be simpler: the client's liveness snapshot
# (below) is taken microseconds before the ssh, so a holder that registers DURING the call is
# not in it and reads as dead. The grace is what makes that race fail CLOSED instead of
# swallowing a brand-new claim. It is also the reason a claim anchored to a short-lived wrapper
# degrades to "5 minutes" rather than "instantly worthless".
#
# WHY THE COUNT IS DERIVED, NOT MAINTAINED: an incremented/decremented refcount is exactly what
# failed — a crashed holder never decrements. `holders=N held=M` is recomputed from liveness on
# every read, so a corpse cannot inflate it.
#
# ── WHERE LIVENESS CAN BE EVALUATED, WHICH IS THE WHOLE STRUCTURAL PROBLEM ─────
# Every lease in the wild read `host=nextop`: the holders are pids on the CLIENT, and the lease
# file lives on the BOX. The box cannot check whether a nextop pid is alive, so a reader running
# only on the box has nothing but the clock to go on. That is why the old design was
# duration-based — not a choice, a consequence of where the check ran.
#
# The fix is to give the box the one fact it cannot obtain: the CLIENT'S LIVENESS SNAPSHOT. The
# client takes `ps -A -o pid=` immediately before the call and passes the set; the box then
# resolves each record as
#
#   host == the box's own hostname     →  check it locally (`/proc/<pid>` or `kill -0`)
#   host == the calling client's host  →  member of the snapshot ⟺ alive
#   anything else                      →  undeterminable → TTL backstop
#
# THIS IS SOUND BECAUSE DEADNESS IS MONOTONE. A snapshot can only go stale in the direction of
# "reports alive, has since died", which makes the guard MORE conservative — it never frees a
# lane it should have kept. The opposite staleness (a holder born after the snapshot) is covered
# by the grace. Pid REUSE can make a corpse read alive, which again fails closed, and the
# ceiling below bounds it.
#
# It also keeps read → decide → write inside ONE shell on the box, so there is still no window
# between deciding a lease is stale and replacing it. A dump-then-decide-then-act round trip
# would have opened exactly that window to buy no extra information.
#
# ── THE CONTRACT (shared with scripts/pbuild, scripts/sweep-build-lanes.sh, box-health.sh) ──
#   record  ONE line, exactly, UNCHANGED from the original contract:
#             owner=<string> pid=<int> host=<string> expires=<unix-seconds>
#           `pid=0` is the ANCHORLESS sentinel: "my lifetime is not observable, use the TTL".
#
#   sidecar <root>/.leases/<lane>.lease   — the AUTHORITATIVE holder SET, one record per line
#   mirror  <lane dir>/.pbuild-lease      — a SINGLE-LINE interop mirror (the longest-lived
#                                           record), because pbuild writes this path and
#                                           box-health.sh reads it as exactly one line
#   reader  the UNION of both files, records keyed by (owner, host); a lane is HELD ⟺ ANY
#           record holds it, by the liveness table above
#   writer  pbuild writes the mirror only, unlocked, clobbering. That is harmless: this script
#           ABSORBS whatever it finds in the mirror into the set before writing, so pbuild's
#           record survives and an agent's record is not destroyed by a build.
#
# `host=` is the host where `pid` lives — the CLAIMANT, not the box the lane is on (the lane's
# box is implied by where the file sits). It is now LOAD-BEARING, not informational: it selects
# which liveness oracle applies.
#
# THREE THINGS STILL KEEP A STALE LEASE FROM WEDGING A LANE, and the first is new:
#   1. a DEAD holder stops counting after the grace, whatever its clock says;
#   2. `reap-expired` clears expired AND unparseable AND ORPHANED records; `reap-orphaned`
#      clears only the corpses, which is a different operator intent;
#   3. an effective-expiry CEILING of `mtime + LANE_LEASE_MAX_AGE` (default 86400) applies to
#      every record no matter what `expires=` claims AND no matter how alive its pid is — so a
#      bad writer that stamps `expires=9999999999` buys 24 hours, not 250 years, and a holder
#      anchored to an immortal process cannot hold a lane forever either. Structural, not a
#      promise.
#
# ── THE SIDECAR, AND WHY IT IS NOT BELT-AND-BRACES PARANOIA ────────────────────
# The mirror path sits at the ROOT of pbuild's rsync destination, and pbuild syncs with
# `rsync -az --delete --filter=':- .gitignore'`. MEASURED 2026-07-26 on the real tree with the
# real command:
#
#   receiver's .gitignore lacks `.pbuild-lease`  →  *deleting   .pbuild-lease
#   receiver's .gitignore has it                 →  not mentioned; survives a real --delete run
#
# An rsync exclude is a receiver-side PROTECT rule as well as a sender-side hide — but a
# per-directory merge file (`:- .gitignore`) is read by each side from ITS OWN copy. So the
# repo's `.gitignore` entry (added 2026-07-26) protects the lease from the SECOND sync onward,
# and the sync that first ships the new rule still deletes it. Isolated proof, 5 variants, in
# that session's log: variant A (stale receiver rule) deletes, variant B (rule present both
# sides) protects, `--exclude=` and `--filter='P …'` on the command line protect
# unconditionally.
#
# So the interop path is structurally exposed to its own transport, which is the second reason
# the SET lives in `<root>/.leases/<lane>.lease` — outside every lane dir and therefore outside
# every rsync destination, where no `--delete` can reach it. pbuild's own `--filter='P
# /.pbuild-lease'` (added 2026-07-26) closes the mirror's window as well.
#
# ── USAGE ─────────────────────────────────────────────────────────────────────
#   scripts/lane-lease.sh acquire       --lane crewbraid --owner agent:lease
#   scripts/lane-lease.sh refresh       --lane crewbraid              # what pbuild should call
#   scripts/lane-lease.sh show          --lane crewbraid              # per-holder liveness
#   scripts/lane-lease.sh release       --lane crewbraid --owner agent:lease
#   scripts/lane-lease.sh reap-expired                                # every lane on the host
#   scripts/lane-lease.sh reap-expired  --lane crewbraid --dry-run
#   scripts/lane-lease.sh reap-orphaned --dry-run                     # ONLY dead-holder records
#
#   --host <h>        box the lane lives on (default $LANE_LEASE_HOST, else persvati).
#                     The literal `local` is a reserved sentinel: operate on THIS machine
#                     with no ssh. That is not a convenience — it is how this script's own
#                     state machine gets tested without a box in the loop.
#   --owner <s>       claimant identity (default $LANE_LEASE_OWNER, else <user>@<host>).
#                     No whitespace: the format is one space-separated line. A record is
#                     IDENTIFIED by (owner, host), so re-acquiring updates in place and
#                     `release` needs only the owner, not the pid it happened to claim with.
#   --ttl <n>         backstop seconds (default $PBUILD_LEASE_TTL, else 3600)
#   --pid <n>         LIVENESS ANCHOR: the pid whose life is this claim's life.
#                     Default $PPID — the process that INVOKED this script, which outlives it.
#                     `--pid 0` means "no anchor, TTL only".
#   --claim-host <s>  value for `host=` (default this machine's short hostname)
#   --force           acquire: TAKE the lane, dropping every existing record.
#                     release: drop every record, not just your own.
#   --share           acquire: JOIN the lane — register ALONGSIDE the existing holders instead
#                     of refusing them. This is the verb for two agents deliberately working one
#                     lane: both records stand, and the lane stays held until the LAST live
#                     holder is gone. It is separate from --force because they are opposite
#                     intents — "make room for me" versus "that owner is gone, take it".
#   --dry-run         reap-*: say what it would clear, clear nothing
#
# WHY THE DEFAULT ANCHOR IS $PPID AND NOT $$, MEASURED 2026-07-26 on this laptop: a tool-call
# shell is gone by the next call (`$$`=91299 → DEAD one command later), while its parent — the
# `claude` session process, pid 60019 — stayed ALIVE across calls. `$$` is therefore a
# corpse-by-construction anchor: defaulting to it would make every agent's claim expire into the
# grace within seconds, which is the ORIGINAL bug. `$PPID` is the claiming session, so a lane is
# held exactly as long as whoever claimed it is still around, and frees itself when they are not.
# Pass `--pid 0` if you genuinely have no such process and want the clock to be the only signal.
#
# ACQUIRE vs REFRESH is the whole ergonomic distinction, and it is deliberate:
#   acquire  REFUSES (exit 3) if another owner HOLDS the lane. That is the agent-facing claim —
#            two agents in one lane is the target-lock contention this machinery exists to
#            avoid, and it should be said out loud. Note that "holds" now means a LIVE holder:
#            a lane whose only records are corpses is acquirable with no --force at all.
#   refresh  NEVER refuses. With a live foreign holder it EXTENDS that holder's record rather
#            than adding its own, because pbuild builds ON BEHALF of whoever owns the lane —
#            a second record for the build tool would double-count one principal, and renaming
#            the lane's owner to whoever last ran a build makes `owner=` a lie exactly when
#            someone is reading it to find out who to ask.
#
# MULTIPLE HOLDERS ARE NORMAL, and the set is what makes them safe: pbuild's record and an
# agent's record coexist, `release` removes only the caller's own, and the lane stays held until
# the last live holder is gone. Before the set existed, pbuild's single-line write DESTROYED an
# agent's declared claim in the mirror on every build.
#
# THERE IS DELIBERATELY NO --ignore-leases ANYWHERE IN THIS MACHINERY: a knob like that is what
# an agent reaches for reflexively, and then the guard cannot say no. `release --force` and
# `acquire --force` are the two-step way to take a lane on purpose.
#
# EXIT CODES (3 is REFUSED, matching pbuild's convention — the action did NOT happen):
#   0 ok / lease held      2 usage error or host unreachable      3 refused
#   4 show: records present but NOT HELD (expired and/or orphaned — read `state=`)
#   5 show: no records at all
set -euo pipefail

HOST="${LANE_LEASE_HOST:-persvati}"
ROOT_REL="${LANE_LEASE_ROOT:-dregg-build}"
TTL="${PBUILD_LEASE_TTL:-3600}"
MAX_AGE="${LANE_LEASE_MAX_AGE:-86400}"
GRACE="${LANE_LEASE_ORPHAN_GRACE:-300}"
OWNER="${LANE_LEASE_OWNER:-}"
# The default anchor is the process that INVOKED this script — see the USAGE note above for the
# measurement that rules out `$$`. PPID 0/1 means we were orphaned or run from init: fall back
# to `$$` rather than claiming pid 1, which is immortal and would never release.
CLAIM_PID="$PPID"
case "$CLAIM_PID" in ''|0|1) CLAIM_PID="$$" ;; esac
CLAIM_HOST=""
FORCE=0
SHARE=0
DRY_RUN=0
LANE=""

show_help() { awk 'NR>1 && /^set -euo pipefail$/{exit} NR>1{print}' "$0"; }

VERB="${1:-}"
case "$VERB" in
  acquire|refresh|release|show|reap-expired|reap-orphaned) shift ;;
  -h|--help|help|'') show_help; exit 0 ;;
  *) echo "lane-lease: unknown verb '$VERB' (acquire|refresh|release|show|reap-expired|reap-orphaned)" >&2; exit 2 ;;
esac

while [ $# -gt 0 ]; do
  case "$1" in
    --lane)       LANE="${2:?--lane needs a value}"; shift 2 ;;
    --host)       HOST="${2:?--host needs a value}"; shift 2 ;;
    --owner)      OWNER="${2:?--owner needs a value}"; shift 2 ;;
    --ttl)        TTL="${2:?--ttl needs a value}"; shift 2 ;;
    --pid)        CLAIM_PID="${2:?--pid needs a value}"; shift 2 ;;
    --claim-host) CLAIM_HOST="${2:?--claim-host needs a value}"; shift 2 ;;
    --root)       ROOT_REL="${2:?--root needs a value}"; shift 2 ;;
    --grace)      GRACE="${2:?--grace needs a value}"; shift 2 ;;
    --force)      FORCE=1; shift ;;
    --share)      SHARE=1; shift ;;
    --dry-run)    DRY_RUN=1; shift ;;
    -h|--help)    show_help; exit 0 ;;
    *) echo "lane-lease: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[ -n "$CLAIM_HOST" ] || CLAIM_HOST="$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo unknown)"
[ -n "$OWNER" ] || OWNER="${USER:-unknown}@${CLAIM_HOST}"

for n in TTL MAX_AGE GRACE CLAIM_PID; do
  case "${!n}" in ''|*[!0-9]*) echo "lane-lease: $n must be a non-negative integer" >&2; exit 2 ;; esac
done
# The line format is space-separated, so a value carrying whitespace does not merely look
# untidy — it silently shifts every field after it and a reader picks up the wrong expiry.
# Refuse rather than sanitize: a mangled owner name is a worse debugging story than an error.
for n in OWNER CLAIM_HOST LANE; do
  case "${!n}" in *[[:space:]]*) echo "lane-lease: $n must not contain whitespace ('${!n}')" >&2; exit 2 ;; esac
done
case "$VERB" in
  reap-expired|reap-orphaned) ;;
  *) [ -n "$LANE" ] || { echo "lane-lease: $VERB needs --lane <name>" >&2; exit 2; } ;;
esac
case "$LANE" in */*|.|..) echo "lane-lease: --lane must be a bare lane name, not a path" >&2; exit 2 ;; esac

# ── THE CLIENT'S LIVENESS SNAPSHOT ─────────────────────────────────────────────
# The one fact the box cannot obtain for itself (see the structural note in the header). Taken
# HERE, immediately before dispatch, and passed as data. Comma-delimited with sentinel commas at
# both ends so the box's membership test is a plain `case` glob and needs no loop.
#
# If this comes back empty the box gets NO client oracle and falls back to the TTL for every
# client-hosted record — i.e. it fails CLOSED to the old behaviour rather than concluding that
# every holder is dead.
CLIENT_HOST="$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo unknown)"
CLIENT_PIDS="$( { ps -A -o pid= 2>/dev/null || ps -eo pid= 2>/dev/null || true; } | tr -cd '0-9\n' | tr '\n' ',' )"
case "$CLIENT_PIDS" in
  ''|*[!0-9,]*) CLIENT_PIDS="" ;;
  *) CLIENT_PIDS=",${CLIENT_PIDS}" ;;
esac

# ── the one program, run identically on a box or on this machine ───────────────
# All read-decide-write happens inside ONE shell on the box that owns the file, so there is no
# ssh round trip between deciding a lease is stale and replacing it.
#
# The body lives in ONE variable rather than in two heredocs, and that is not style: two copies
# WILL drift, and a lease tool whose local test path differs from its remote path tests
# nothing. `dispatch` (below) feeds this identical text to the identical `bash -s` either way,
# with every parameter arriving as a %q-quoted positional argument — no local expansion, no
# `\$` escaping, and nothing an owner string could smuggle into the remote shell.
LEASE_PROGRAM_BODY=$(cat <<'PROGRAM'
set -uo pipefail
VERB="$1"; ROOT_REL="$2"; LANE="$3"; OWNER="$4"; CPID="$5"; CHOST="$6"
TTL="$7"; MAX_AGE="$8"; FORCE="$9"; DRY_RUN="${10}"; GRACE="${11}"
CLIENT_HOST="${12}"; CLIENT_PIDS="${13}"; SHARE="${14}"

case "$ROOT_REL" in /*) ROOT="$ROOT_REL" ;; *) ROOT="$HOME/$ROOT_REL" ;; esac
SIDE_DIR="$ROOT/.leases"
NOW="$(date +%s)"
BOX_HOST="$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo unknown)"
TAB="$(printf '\t')"

mirror_path()  { printf '%s/%s/.pbuild-lease\n' "$ROOT" "$1"; }
sidecar_path() { printf '%s/%s.lease\n' "$SIDE_DIR" "$1"; }
mtime_of()     { stat -c %Y "$1" 2>/dev/null || stat -f %m "$1" 2>/dev/null || echo 0; }

# ── LIVENESS: the oracle, and the ONLY place it is decided ─────────────────────
# alive / dead / anchorless / unknown. `anchorless` and `unknown` both route to the TTL
# backstop, but they are reported apart because they mean different things to a human: one is a
# holder that told us it has no observable lifetime, the other is a holder we cannot see.
live_verdict() {
  local p="$1" h="$2"
  case "$p" in ''|*[!0-9]*) echo unknown; return ;; esac
  [ "$p" = 0 ] && { echo anchorless; return; }
  if [ "$h" = "$BOX_HOST" ]; then
    # /proc is owner-independent; `kill -0` reports EPERM as failure and would call another
    # user's live process dead. Prefer /proc where it exists, and back `kill -0` with `ps`.
    if [ -d /proc ]; then
      if [ -d "/proc/$p" ]; then echo alive; else echo dead; fi
    elif kill -0 "$p" 2>/dev/null || ps -p "$p" >/dev/null 2>&1; then echo alive
    else echo dead
    fi
    return
  fi
  if [ -n "$CLIENT_HOST" ] && [ "$h" = "$CLIENT_HOST" ]; then
    case "$CLIENT_PIDS" in
      '')       echo unknown ;;
      *",$p,"*) echo alive ;;
      *)        echo dead ;;
    esac
    return
  fi
  echo unknown
}

# ── READING THE SET ───────────────────────────────────────────────────────────
# RECS is one record per line: owner TAB pid TAB host TAB expires TAB mtime TAB malformed TAB where
RECS=""
read_file_recs() {                    # read_file_recs <file> <where-tag>
  local f="$1" tag="$2" mt line o p h e mal tok
  [ -f "$f" ] || return 0
  mt="$(mtime_of "$f")"
  case "$mt" in ''|*[!0-9]*) mt=0 ;; esac
  while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in '') continue ;; esac
    o=""; p=""; h=""; e=""
    # shellcheck disable=SC2086 # deliberate word split: a record is one space-separated line.
    for tok in $line; do
      case "$tok" in
        owner=*)   o="${tok#owner=}" ;;
        pid=*)     p="${tok#pid=}" ;;
        host=*)    h="${tok#host=}" ;;
        expires=*) e="${tok#expires=}" ;;
      esac
    done
    # A TORN OR FOREIGN-FORMAT RECORD FAILS CLOSED, BUT NOT FOREVER. Treating it as absent
    # would let a write interrupted mid-`mv` cost an agent its lane; treating it as permanently
    # held would wedge the lane, which the contract forbids. mtime + TTL is the honest reading:
    # someone wrote something here recently, so respect it for one TTL. Its `pid` is not
    # trusted either — a half-written record's anchor could be a truncated number naming an
    # unrelated process, so liveness is forced to `unknown` for it downstream.
    mal=0
    case "$e" in ''|*[!0-9]*) mal=1; e=0 ;; esac
    case "$p" in ''|*[!0-9]*) mal=1; p=0 ;; esac
    [ -n "$o" ] || { o="-"; mal=1; }
    [ -n "$h" ] || { h="-"; mal=1; }
    RECS="${RECS}${o}${TAB}${p}${TAB}${h}${TAB}${e}${TAB}${mt}${TAB}${mal}${TAB}${tag}
"
  done < "$f"
}

# A record is IDENTIFIED by (owner, host): one claimant on one machine has one claim. Merging in
# awk rather than in shell because the merge needs a keyed map, and macOS still ships bash 3.2
# with no associative arrays — the local test arm must run the same text as the box.
merge_recs() {
  printf '%s' "$RECS" | awk -F'\t' '
    NF < 7 { next }
    { k = $1 "|" $3
      if (k in SEEN) { if (W[k] != $7) W[k] = "both" } else { SEEN[k] = 1; W[k] = $7 }
      if (!(k in E) || ($4+0) > (E[k]+0) || (($4+0) == (E[k]+0) && ($5+0) > (M[k]+0))) {
        O[k]=$1; P[k]=$2; H[k]=$3; E[k]=$4; M[k]=$5; L[k]=$6
      }
    }
    END { for (k in SEEN) printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n", O[k],P[k],H[k],E[k],M[k],L[k],W[k] }
  ' | sort -t "$TAB" -k1,1 -k3,3
}

load_recs() {                         # load_recs <lane>
  RECS=""
  read_file_recs "$(mirror_path "$1")" contract
  read_file_recs "$(sidecar_path "$1")" sidecar
  RECS="$(merge_recs)"
  [ -z "$RECS" ] || RECS="$RECS
"
}

# ── CLASSIFY ONE RECORD ───────────────────────────────────────────────────────
# R_HOLD is the verdict that matters; R_WHY says which of the three rules produced it.
classify_rec() {                      # classify_rec <pid> <host> <expires> <mtime> <malformed>
  local p="$1" h="$2" e="$3" mt="$4" mal="$5" ceil
  R_LIVE="$(live_verdict "$p" "$h")"
  [ "$mal" -eq 1 ] && R_LIVE=unknown
  ceil=$(( mt + MAX_AGE ))
  if [ "$mal" -eq 1 ]; then R_EFF=$(( mt + TTL )); else R_EFF="$e"; fi
  R_CLAMP=0
  if [ "$R_EFF" -gt "$ceil" ]; then R_EFF="$ceil"; R_CLAMP=1; fi
  R_REM=$(( R_EFF - NOW ))
  case "$R_LIVE" in
    alive)
      # LIVENESS DOMINATES THE CLOCK IN BOTH DIRECTIONS, bounded only by the ceiling — which is
      # what keeps "a live holder cannot wedge a lane forever" a property of the reader.
      if [ "$ceil" -gt "$NOW" ]; then R_HOLD=1; R_WHY=live; else R_HOLD=0; R_WHY=ceiling; fi ;;
    dead)
      if [ $(( mt + GRACE )) -gt "$NOW" ]; then R_HOLD=1; R_WHY=grace; else R_HOLD=0; R_WHY=corpse; fi ;;
    *)
      if [ "$R_REM" -gt 0 ]; then R_HOLD=1; R_WHY=ttl; else R_HOLD=0; R_WHY=expired; fi ;;
  esac
}

# ── SCAN A LANE ───────────────────────────────────────────────────────────────
# Sets the lane verdict, the PRINCIPAL record (the one a one-line report should name), a
# human-readable per-holder block, and the KEEP/DROP partitions the reap verbs need.
LS_STATE=absent; LS_N=0; LS_HELD=0
LS_OWNER=-; LS_PID=-; LS_HOST=-; LS_EXP=0; LS_EFF=0; LS_REM=0
LS_WHERE=none; LS_MAL=0; LS_CLAMP=0; LS_LIVE=-; LS_WHY=-
LS_REPORT=""; LS_KEEP=""; LS_DROP=""; LS_HAS_CORPSE=0
lane_scan() {
  local lane="$1" o p h e mt mal wh best=-1 rank brank=-1
  load_recs "$lane"
  LS_STATE=absent; LS_N=0; LS_HELD=0
  LS_OWNER=-; LS_PID=-; LS_HOST=-; LS_EXP=0; LS_EFF=0; LS_REM=0
  LS_WHERE=none; LS_MAL=0; LS_CLAMP=0; LS_LIVE=-; LS_WHY=-
  LS_REPORT=""; LS_KEEP=""; LS_DROP=""; LS_HAS_CORPSE=0
  [ -n "$RECS" ] || return 0
  while IFS="$TAB" read -r o p h e mt mal wh; do
    [ -n "${o:-}" ] || continue
    LS_N=$(( LS_N + 1 ))
    classify_rec "$p" "$h" "$e" "$mt" "$mal"
    if [ "$R_HOLD" -eq 1 ]; then
      LS_HELD=$(( LS_HELD + 1 ))
      LS_KEEP="${LS_KEEP}${o}${TAB}${p}${TAB}${h}${TAB}${e}${TAB}${mt}${TAB}${mal}${TAB}${wh}
"
    else
      LS_DROP="${LS_DROP}${o}${TAB}${p}${TAB}${h}${TAB}${e}${TAB}${mt}${TAB}${mal}${TAB}${wh}
"
      [ "$R_WHY" = corpse ] && LS_HAS_CORPSE=1
    fi
    # `ttl_left`, not `ttl_remaining`: a per-holder field ending in `remaining=` would collide
    # with the machine line's `remaining=` under any grep/sed a caller writes against this
    # output, and it did — the selftest's ceiling assertion picked up two values at once.
    LS_REPORT="${LS_REPORT}$(printf '  %-7s owner=%-28s pid=%-8s host=%-10s live=%-11s ttl_left=%ss  where=%s  → %s' \
      "$( [ "$R_HOLD" -eq 1 ] && echo HOLDER || echo STALE )" \
      "$o" "$p" "$h" "$R_LIVE" "$R_REM" "$wh" \
      "$( case "$R_WHY" in
            live)    echo 'HOLDS (live anchor)' ;;
            grace)   echo "HOLDS (anchor dead, inside ${GRACE}s grace)" ;;
            ttl)     echo 'HOLDS (TTL backstop)' ;;
            corpse)  echo "CORPSE — anchor is dead, grace ended $(( NOW - mt - GRACE ))s ago" ;;
            expired) echo 'EXPIRED (TTL backstop lapsed)' ;;
            ceiling) echo "CEILING — live anchor, but past mtime+${MAX_AGE}s" ;;
          esac )")"
    LS_REPORT="${LS_REPORT}
"
    # PRINCIPAL: a holding record always outranks a stale one, then the later effective expiry.
    rank=$(( R_HOLD * 2 ))
    if [ "$rank" -gt "$brank" ] || { [ "$rank" -eq "$brank" ] && [ "$R_EFF" -gt "$best" ]; }; then
      brank="$rank"; best="$R_EFF"
      LS_OWNER="$o"; LS_PID="$p"; LS_HOST="$h"; LS_EXP="$e"; LS_EFF="$R_EFF"; LS_REM="$R_REM"
      LS_WHERE="$wh"; LS_MAL="$mal"; LS_CLAMP="$R_CLAMP"; LS_LIVE="$R_LIVE"; LS_WHY="$R_WHY"
    fi
  done <<EOF
$RECS
EOF
  if   [ "$LS_HELD" -gt 0 ];      then LS_STATE=held
  elif [ "$LS_HAS_CORPSE" -eq 1 ]; then LS_STATE=orphaned
  else LS_STATE=expired
  fi
}

report_state() {                      # report_state <lane> — the machine line
  printf 'state=%s lane=%s owner=%s pid=%s host=%s expires=%s effective=%s remaining=%s where=%s malformed=%s clamped=%s live=%s reason=%s holders=%s held=%s\n' \
    "$LS_STATE" "$1" "$LS_OWNER" "$LS_PID" "$LS_HOST" "$LS_EXP" "$LS_EFF" "$LS_REM" \
    "$LS_WHERE" "$LS_MAL" "$LS_CLAMP" "$LS_LIVE" "$LS_WHY" "$LS_N" "$LS_HELD"
}

# ── WRITING THE SET ───────────────────────────────────────────────────────────
# A per-lane mkdir mutex. Two agents acquiring the same lane in the same millisecond would
# otherwise read-modify-write over each other and one declaration would vanish silently — which
# is the exact class of failure this file exists to remove. It CANNOT wedge: a lock older than
# 60s is broken, and after 5s of waiting the write proceeds unlocked with a warning, so the
# worst case is the status quo before the lock existed.
LOCK=""
lock_take() {
  local lane="$1" i=0 lmt
  LOCK="$SIDE_DIR/.lock.$lane"
  mkdir -p "$SIDE_DIR" 2>/dev/null || true
  while [ "$i" -lt 50 ]; do
    if mkdir "$LOCK" 2>/dev/null; then return 0; fi
    lmt="$(mtime_of "$LOCK")"
    case "$lmt" in ''|*[!0-9]*) lmt=0 ;; esac
    if [ $(( NOW - lmt )) -gt 60 ]; then
      echo "lane-lease: breaking a stale write lock on '$lane' ($(( NOW - lmt ))s old)" >&2
      rmdir "$LOCK" 2>/dev/null || true
    fi
    i=$(( i + 1 )); sleep 0.1 2>/dev/null || sleep 1
  done
  echo "lane-lease: could not take the write lock on '$lane' after 5s — writing unlocked" >&2
  LOCK=""
  return 0
}
lock_free() { [ -n "$LOCK" ] && rmdir "$LOCK" 2>/dev/null; LOCK=""; return 0; }

atomic_put() {                        # atomic_put <file> <content-on-stdin>
  local f="$1" d tmp
  d="$(dirname "$f")"; mkdir -p "$d" || return 1
  tmp="$f.tmp.$$"
  cat > "$tmp" || return 1
  mv -f "$tmp" "$f"
}

# write_set <lane> — SET is the record list. The sidecar takes every record; the mirror takes
# the single longest-lived one, because pbuild writes that path and box-health.sh reads it as
# exactly one line. Empty set ⇒ both files go away.
SET=""
write_set() {
  local lane="$1" mf sf rc=0 line
  mf="$(mirror_path "$lane")"; sf="$(sidecar_path "$lane")"
  if [ -z "$SET" ]; then
    rm -f "$mf" "$sf"
    return 0
  fi
  printf '%s' "$SET" | awk -F'\t' 'NF>=4 { printf "owner=%s pid=%s host=%s expires=%s\n", $1,$2,$3,$4 }' \
    | atomic_put "$sf" || rc=1
  # A lane that has never been synced has no dir yet, and that is not a reason to fail — the
  # sidecar carries the claim either way, and it is the copy no transport can delete.
  if [ -d "$ROOT/$lane" ]; then
    line="$(printf '%s' "$SET" | awk -F'\t' 'NF>=4 { if ($4+0 > best+0) { best=$4; out=sprintf("owner=%s pid=%s host=%s expires=%s", $1,$2,$3,$4) } } END { if (out != "") print out }')"
    printf '%s\n' "$line" | atomic_put "$mf" || rc=1
  fi
  return "$rc"
}

# ABSORB then PRUNE. Absorb: whatever is in the set now (including a record pbuild clobbered
# into the mirror) is carried forward, so a build never destroys an agent's claim and an agent
# never destroys a build's. Prune: records that no longer hold are dropped on every mutation,
# which is what keeps the set bounded — pbuild's pid changes every run, so without this the
# sidecar would grow a corpse per build forever.
set_from_keep() { SET="$LS_KEEP"; }
set_upsert_self() {                   # replace-or-append the caller's own (owner, host) record
  local exp="$1" out=""
  out="$(printf '%s' "$SET" | awk -F'\t' -v o="$OWNER" -v h="$CHOST" '!($1 == o && $3 == h)')"
  [ -z "$out" ] || out="$out
"
  SET="${out}${OWNER}${TAB}${CPID}${TAB}${CHOST}${TAB}${exp}${TAB}${NOW}${TAB}0${TAB}sidecar
"
}
set_bump_owner() {                    # extend an EXISTING record's expiry, keeping its anchor
  local who="$1" wh="$2" exp="$3"
  SET="$(printf '%s' "$SET" | awk -F'\t' -v OFS='\t' -v o="$who" -v h="$wh" -v e="$exp" -v n="$NOW" \
        '{ if ($1 == o && $3 == h && e+0 > $4+0) { $4 = e; $5 = n } print }')"
  [ -z "$SET" ] || SET="$SET
"
}
set_drop_owner() {                    # release: only the caller's own records
  SET="$(printf '%s' "$SET" | awk -F'\t' -v o="$OWNER" '$1 != o')"
  [ -z "$SET" ] || SET="$SET
"
}
set_count() { printf '%s' "$SET" | grep -c . 2>/dev/null || echo 0; }

enumerate_lanes() {                   # every lane on the host that could carry a record
  local d b s out=""
  for d in "$ROOT"/*/; do
    [ -d "$d" ] || continue
    b="$(basename "$d")"
    [ "$b" = ".leases" ] && continue
    out="$out $b"
  done
  # A sidecar can outlive its lane dir (the dir was reclaimed, the claim was not). Those are
  # exactly the records nobody would ever look at again, so enumerate them too.
  for s in "$SIDE_DIR"/*.lease; do
    [ -f "$s" ] || continue
    b="$(basename "$s" .lease)"
    case " $out " in *" $b "*) ;; *) out="$out $b" ;; esac
  done
  printf '%s' "$out"
}

case "$VERB" in
  acquire)
    lane_scan "$LANE"
    # "Held by someone else" now means a LIVE holder, so a lane whose only records are corpses
    # is acquirable with no --force at all — which is the whole point of the rework.
    foreign_held=0
    if [ "$LS_HELD" -gt 0 ]; then
      foreign_held="$(printf '%s' "$LS_KEEP" | awk -F'\t' -v o="$OWNER" '$1 != o' | grep -c . || true)"
      case "$foreign_held" in ''|*[!0-9]*) foreign_held=0 ;; esac
    fi
    if [ "$foreign_held" -gt 0 ] && [ "$SHARE" -eq 1 ]; then
      echo "lane-lease: --share — joining lane '$LANE' alongside $foreign_held existing live holder(s)." >&2
    elif [ "$foreign_held" -gt 0 ] && [ "$FORCE" -ne 1 ]; then
      report_state "$LANE"
      printf '%s' "$LS_REPORT"
      echo "lane-lease: REFUSED — lane '$LANE' is held by '$LS_OWNER' (pid $LS_PID on $LS_HOST, $LS_WHY)." >&2
      echo "            Two agents in one lane is the target-lock contention this exists to prevent." >&2
      echo "            Use a different lane, wait for that holder to exit, --share to work it" >&2
      echo "            together, or --force if you know that owner is gone." >&2
      exit 3
    fi
    lock_take "$LANE"
    lane_scan "$LANE"
    if [ "$FORCE" -eq 1 ] && [ "$SHARE" -ne 1 ] && [ "$LS_HELD" -gt 0 ]; then
      echo "lane-lease: --force — taking lane '$LANE' from $LS_HELD live holder(s), starting with '$LS_OWNER'." >&2
      SET=""
    else
      set_from_keep
    fi
    set_upsert_self "$(( NOW + TTL ))"
    write_set "$LANE"; rc=$?
    lock_free
    lane_scan "$LANE"
    printf 'state=held lane=%s owner=%s pid=%s host=%s expires=%s remaining=%s holders=%s\n' \
      "$LANE" "$OWNER" "$CPID" "$CHOST" "$(( NOW + TTL ))" "$TTL" "$LS_N"
    printf '%s' "$LS_REPORT"
    [ -f "$(mirror_path "$LANE")" ] && printf '  mirror   %s\n' "$(mirror_path "$LANE")"
    printf '  sidecar  %s   (the SET; outside every rsync destination)\n' "$(sidecar_path "$LANE")"
    exit "$rc"
    ;;
  refresh)
    lock_take "$LANE"
    lane_scan "$LANE"
    # A live FOREIGN holder gets its own record extended (see ACQUIRE vs REFRESH in the header).
    other=""; other_host=""
    if [ "$LS_HELD" -gt 0 ]; then
      other="$(printf '%s' "$LS_KEEP" | awk -F'\t' -v o="$OWNER" '$1 != o { print $1 "\t" $3; exit }')"
    fi
    set_from_keep
    if [ -n "$other" ]; then
      other_host="${other#*"$TAB"}"; other="${other%%"$TAB"*}"
      echo "lane-lease: extending '$other' lease on '$LANE' (refresh never steals; use acquire --force to take it)" >&2
      set_bump_owner "$other" "$other_host" "$(( NOW + TTL ))"
      write_set "$LANE"; rc=$?
      lock_free
      lane_scan "$LANE"
      printf 'state=held lane=%s owner=%s pid=%s host=%s expires=%s remaining=%s holders=%s\n' \
        "$LANE" "$LS_OWNER" "$LS_PID" "$LS_HOST" "$LS_EXP" "$LS_REM" "$LS_N"
    else
      set_upsert_self "$(( NOW + TTL ))"
      write_set "$LANE"; rc=$?
      lock_free
      lane_scan "$LANE"
      printf 'state=held lane=%s owner=%s pid=%s host=%s expires=%s remaining=%s holders=%s\n' \
        "$LANE" "$OWNER" "$CPID" "$CHOST" "$(( NOW + TTL ))" "$TTL" "$LS_N"
    fi
    printf '%s' "$LS_REPORT"
    exit "$rc"
    ;;
  release)
    lock_take "$LANE"
    lane_scan "$LANE"
    if [ "$LS_N" -eq 0 ]; then
      lock_free
      echo "state=absent lane=$LANE (nothing to release)"
      exit 0
    fi
    mine="$(printf '%s' "$RECS" | awk -F'\t' -v o="$OWNER" '$1 == o' | grep -c . || true)"
    case "$mine" in ''|*[!0-9]*) mine=0 ;; esac
    if [ "$mine" -eq 0 ] && [ "$FORCE" -ne 1 ]; then
      lock_free
      report_state "$LANE"
      printf '%s' "$LS_REPORT"
      echo "lane-lease: REFUSED — '$OWNER' holds no record on lane '$LANE' (principal is '$LS_OWNER'). Use --force." >&2
      exit 3
    fi
    if [ "$FORCE" -eq 1 ]; then
      SET=""
    else
      SET="$RECS"; set_drop_owner
      # A release is also the natural moment to drop what no longer holds.
      SET="$(printf '%s' "$SET" | awk -F'\t' 'NF>=7')"
      [ -z "$SET" ] || SET="$SET
"
      keepset=""
      while IFS="$TAB" read -r o p h e mt mal wh; do
        [ -n "${o:-}" ] || continue
        classify_rec "$p" "$h" "$e" "$mt" "$mal"
        [ "$R_HOLD" -eq 1 ] && keepset="${keepset}${o}${TAB}${p}${TAB}${h}${TAB}${e}${TAB}${mt}${TAB}${mal}${TAB}${wh}
"
      done <<EOF
$SET
EOF
      SET="$keepset"
    fi
    write_set "$LANE"; rc=$?
    lock_free
    lane_scan "$LANE"
    printf 'state=released lane=%s owner=%s holders_remaining=%s\n' "$LANE" "$OWNER" "$LS_HELD"
    printf '%s' "$LS_REPORT"
    if [ "$LS_HELD" -gt 0 ]; then
      echo "lane-lease: lane '$LANE' is STILL HELD by '$LS_OWNER' — a lease is a SET, and it is" >&2
      echo "            released only when the last live holder is gone." >&2
    fi
    exit "$rc"
    ;;
  show)
    lane_scan "$LANE"
    report_state "$LANE"
    printf '%s' "$LS_REPORT"
    [ -f "$(mirror_path "$LANE")" ]  && printf '  mirror   %s\n' "$(mirror_path "$LANE")"
    [ -f "$(sidecar_path "$LANE")" ] && printf '  sidecar  %s\n' "$(sidecar_path "$LANE")"
    [ "$LS_MAL" -eq 1 ]   && echo "  ⚠ unparseable record — read as mtime+${TTL}s with liveness UNKNOWN (fails CLOSED, but expires)" >&2
    [ "$LS_CLAMP" -eq 1 ] && echo "  ⚠ expires= exceeded mtime+${MAX_AGE}s and was CLAMPED to the ceiling" >&2
    [ "$LS_STATE" = orphaned ] && echo "  ⚠ THIS LANE IS HELD BY A CORPSE — clear it with: lane-lease.sh reap-orphaned --lane $LANE" >&2
    case "$LS_STATE" in held) exit 0 ;; absent) exit 5 ;; *) exit 4 ;; esac
    ;;
  reap-expired|reap-orphaned)
    ONLY_CORPSE=0
    [ "$VERB" = reap-orphaned ] && ONLY_CORPSE=1
    if [ -n "$LANE" ]; then lanes="$LANE"; else lanes="$(enumerate_lanes)"; fi
    reaped=0; kept=0; none=0; recs_dropped=0
    for l in $lanes; do
      [ -n "$l" ] || continue
      lock_take "$l"
      lane_scan "$l"
      if [ "$LS_N" -eq 0 ]; then lock_free; none=$(( none + 1 )); continue; fi
      # Partition. reap-expired drops everything that does not hold; reap-orphaned drops ONLY
      # dead-anchor records, leaving a merely-lapsed TTL alone — different operator intent.
      drop=""; keepset=""
      while IFS="$TAB" read -r o p h e mt mal wh; do
        [ -n "${o:-}" ] || continue
        classify_rec "$p" "$h" "$e" "$mt" "$mal"
        if [ "$R_HOLD" -eq 0 ] && { [ "$ONLY_CORPSE" -eq 0 ] || [ "$R_WHY" = corpse ]; }; then
          drop="${drop}${o}${TAB}${p}${TAB}${h}${TAB}${e}${TAB}${mal}${TAB}${R_WHY}${TAB}${R_REM}
"
        else
          keepset="${keepset}${o}${TAB}${p}${TAB}${h}${TAB}${e}${TAB}${mt}${TAB}${mal}${TAB}${wh}
"
        fi
      done <<EOF
$RECS
EOF
      ndrop="$(printf '%s' "$drop" | grep -c . || true)"; case "$ndrop" in ''|*[!0-9]*) ndrop=0 ;; esac
      if [ "$ndrop" -eq 0 ]; then
        lock_free
        kept=$(( kept + 1 ))
        printf 'HELD    %-24s owner=%s live=%s reason=%s holders=%s\n' "$l" "$LS_OWNER" "$LS_LIVE" "$LS_WHY" "$LS_N"
        continue
      fi
      while IFS="$TAB" read -r o p h e mal why rem; do
        [ -n "${o:-}" ] || continue
        recs_dropped=$(( recs_dropped + 1 ))
        if [ "$DRY_RUN" -eq 1 ]; then verb="WOULD-REAP"; else verb="REAPED    "; fi
        printf '%s %-21s owner=%-28s pid=%-8s host=%-10s %s (malformed=%s, ttl_left=%ss)\n' \
          "$verb" "$l" "$o" "$p" "$h" \
          "$( [ "$why" = corpse ] && echo 'ORPHANED — the anchor pid is DEAD' || echo 'EXPIRED — the TTL backstop lapsed' )" \
          "$mal" "$rem"
      done <<EOF
$drop
EOF
      if [ "$DRY_RUN" -eq 1 ]; then
        lock_free
      else
        SET="$keepset"
        write_set "$l" || true
        lock_free
      fi
      nkeep="$(printf '%s' "$keepset" | grep -c . || true)"; case "$nkeep" in ''|*[!0-9]*) nkeep=0 ;; esac
      if [ "$nkeep" -gt 0 ]; then
        kept=$(( kept + 1 ))
        printf 'HELD    %-24s (%s record(s) survive the reap)\n' "$l" "$nkeep"
      else
        reaped=$(( reaped + 1 ))
      fi
    done
    if [ "$DRY_RUN" -eq 1 ]; then
      printf '%s: %s would be cleared, %s still held, %s unleased — %s record(s) affected (dry run)\n' \
        "$VERB" "$reaped" "$kept" "$none" "$recs_dropped"
    else
      printf '%s: %s cleared, %s still held, %s unleased — %s record(s) removed\n' \
        "$VERB" "$reaped" "$kept" "$none" "$recs_dropped"
    fi
    ;;
esac
PROGRAM
)

# One text, two transports: the body variable is fed to whichever `bash -s` applies, with every
# parameter arriving as a %q-quoted positional argument.
dispatch() {
  local args=("$@") q=() a
  if [ "$HOST" = local ]; then
    printf '%s\n' "$LEASE_PROGRAM_BODY" | bash -s -- "${args[@]}"
  else
    if ! ssh -o BatchMode=yes -o ConnectTimeout=8 "$HOST" true 2>/dev/null; then
      echo "lane-lease: cannot reach '$HOST'. (Use --host local to operate on this machine.)" >&2
      exit 2
    fi
    for a in "${args[@]}"; do q+=("$(printf '%q' "$a")"); done
    # shellcheck disable=SC2029 # every argument is %q-quoted immediately above.
    printf '%s\n' "$LEASE_PROGRAM_BODY" | ssh -o BatchMode=yes "$HOST" "bash -s -- ${q[*]}"
  fi
}

dispatch "$VERB" "$ROOT_REL" "$LANE" "$OWNER" "$CLAIM_PID" "$CLAIM_HOST" "$TTL" "$MAX_AGE" \
         "$FORCE" "$DRY_RUN" "$GRACE" "$CLIENT_HOST" "$CLIENT_PIDS" "$SHARE"
