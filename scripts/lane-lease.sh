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
# ── THE CONTRACT (shared with scripts/pbuild and scripts/sweep-build-lanes.sh) ──
#   path    <lane dir>/.pbuild-lease            e.g. ~/dregg-build/crewbraid/.pbuild-lease
#   format  ONE line, exactly:
#             owner=<string> pid=<int> host=<string> expires=<unix-seconds>
#   writer  pbuild, on every invocation (`lane-lease.sh refresh`), expires = now + TTL
#   reader  sweep-build-lanes.sh REFUSES any lane whose lease exists AND expires > now
#   TTL     3600s, override with PBUILD_LEASE_TTL
#
# It is a HINT WITH AN EXPIRY, NEVER A LOCK. Three properties keep it from wedging a lane:
#   1. it EXPIRES, so a dead agent stops mattering after TTL seconds;
#   2. `reap-expired` clears expired and unparseable leases;
#   3. an effective-expiry CEILING of `mtime + LANE_LEASE_MAX_AGE` (default 86400) applies to
#      every lease no matter what the `expires=` field claims — so a bad writer that stamps
#      `expires=9999999999` buys 24 hours, not 250 years. Structural, not a promise.
#
# `host=` is the host where `pid` lives — the CLAIMANT, not the box the lane is on (the lane's
# box is implied by where the file sits). Readers must treat it as informational: only
# `expires` is load-bearing, so the two sides cannot disagree about anything that matters.
#
# ── THE SIDECAR, AND WHY IT IS NOT BELT-AND-BRACES PARANOIA ────────────────────
# The contract path sits at the ROOT of pbuild's rsync destination, and pbuild syncs with
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
# this session's log: variant A (stale receiver rule) deletes, variant B (rule present both
# sides) protects, `--exclude=` and `--filter='P …'` on the command line protect
# unconditionally.
#
# So the contract path is structurally exposed to its own transport. This script therefore
# writes a SECOND copy at
#
#   <root>/.leases/<lane>.lease        e.g. ~/dregg-build/.leases/crewbraid.lease
#
# which is OUTSIDE `~/dregg-build/<lane>/` and therefore outside every rsync destination — no
# `--delete` can reach it. Both files carry the identical line; a reader takes the LATER
# effective expiry of the two. The contract path stays authoritative for interop (pbuild
# writes it, the sweep reads it); the sidecar is what makes the guarantee unconditional.
#
# UNMET, and it is a HANDOFF not a residual to shrug at: the durable fix belongs on pbuild's
# rsync line, which this lane does not own —
#     rsync -az --delete --filter='P /.pbuild-lease' …    (protect rule, receiver-side)
# one word, and the flag-day window closes for the contract path too.
#
# ── USAGE ─────────────────────────────────────────────────────────────────────
#   scripts/lane-lease.sh acquire      --lane crewbraid --owner agent:lease
#   scripts/lane-lease.sh refresh      --lane crewbraid              # what pbuild should call
#   scripts/lane-lease.sh show         --lane crewbraid
#   scripts/lane-lease.sh release      --lane crewbraid --owner agent:lease
#   scripts/lane-lease.sh reap-expired                               # every lane on the host
#   scripts/lane-lease.sh reap-expired --lane crewbraid --dry-run
#
#   --host <h>        box the lane lives on (default $LANE_LEASE_HOST, else persvati).
#                     The literal `local` is a reserved sentinel: operate on THIS machine
#                     with no ssh. That is not a convenience — it is how this script's own
#                     state machine gets tested without a box in the loop.
#   --owner <s>       claimant identity (default $LANE_LEASE_OWNER, else <user>@<host>).
#                     No whitespace: the format is one space-separated line.
#   --ttl <n>         seconds (default $PBUILD_LEASE_TTL, else 3600)
#   --pid <n>         claimant pid (default $$)
#   --claim-host <s>  value for `host=` (default this machine's short hostname)
#   --force           acquire over a live foreign lease / release one you do not own
#   --dry-run         reap-expired only: say what it would clear, clear nothing
#
# ACQUIRE vs REFRESH is the whole ergonomic distinction, and it is deliberate:
#   acquire  REFUSES (exit 3) if another owner holds an unexpired lease. That is the
#            agent-facing claim — two agents in one lane is the target-lock contention this
#            machinery exists to avoid, and it should be said out loud.
#   refresh  NEVER refuses. It stamps a fresh expiry, keeping the existing owner if one holds
#            the lane. That is the pbuild-facing verb: a build tool that can be REFUSED by a
#            hint has turned the hint into a lock, and the contract says it is not one.
#
# EXIT CODES (3 is REFUSED, matching pbuild's convention — the action did NOT happen):
#   0 ok / lease held      2 usage error or host unreachable      3 refused
#   4 show: lease present but EXPIRED                             5 show: no lease at all
set -euo pipefail

HOST="${LANE_LEASE_HOST:-persvati}"
ROOT_REL="${LANE_LEASE_ROOT:-dregg-build}"
TTL="${PBUILD_LEASE_TTL:-3600}"
MAX_AGE="${LANE_LEASE_MAX_AGE:-86400}"
OWNER="${LANE_LEASE_OWNER:-}"
CLAIM_PID="$$"
CLAIM_HOST=""
FORCE=0
DRY_RUN=0
LANE=""

VERB="${1:-}"
case "$VERB" in
  acquire|refresh|release|show|reap-expired) shift ;;
  -h|--help|help|'') sed -n '2,105p' "$0"; exit 0 ;;
  *) echo "lane-lease: unknown verb '$VERB' (acquire|refresh|release|show|reap-expired)" >&2; exit 2 ;;
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
    --force)      FORCE=1; shift ;;
    --dry-run)    DRY_RUN=1; shift ;;
    -h|--help)    sed -n '2,105p' "$0"; exit 0 ;;
    *) echo "lane-lease: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[ -n "$CLAIM_HOST" ] || CLAIM_HOST="$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo unknown)"
[ -n "$OWNER" ] || OWNER="${USER:-unknown}@${CLAIM_HOST}"

for n in TTL MAX_AGE CLAIM_PID; do
  case "${!n}" in ''|*[!0-9]*) echo "lane-lease: $n must be a non-negative integer" >&2; exit 2 ;; esac
done
# The line format is space-separated, so a value carrying whitespace does not merely look
# untidy — it silently shifts every field after it and a reader picks up the wrong expiry.
# Refuse rather than sanitize: a mangled owner name is a worse debugging story than an error.
for n in OWNER CLAIM_HOST LANE; do
  case "${!n}" in *[[:space:]]*) echo "lane-lease: $n must not contain whitespace ('${!n}')" >&2; exit 2 ;; esac
done
if [ "$VERB" != reap-expired ] && [ -z "$LANE" ]; then
  echo "lane-lease: $VERB needs --lane <name>" >&2; exit 2
fi
case "$LANE" in */*|.|..) echo "lane-lease: --lane must be a bare lane name, not a path" >&2; exit 2 ;; esac

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
TTL="$7"; MAX_AGE="$8"; FORCE="$9"; DRY_RUN="${10}"

case "$ROOT_REL" in /*) ROOT="$ROOT_REL" ;; *) ROOT="$HOME/$ROOT_REL" ;; esac
SIDE_DIR="$ROOT/.leases"
NOW="$(date +%s)"

contract_path() { printf '%s/%s/.pbuild-lease\n' "$ROOT" "$1"; }
sidecar_path()  { printf '%s/%s.lease\n' "$SIDE_DIR" "$1"; }

mtime_of() { stat -c %Y "$1" 2>/dev/null || stat -f %m "$1" 2>/dev/null || echo 0; }

# read_one <file> -> "state owner pid host expires eff remaining malformed clamped"
# state ∈ absent|held|expired.  Every field is a single token so the caller can `read` it.
read_one() {
  local f="$1" line o p h e mal mt eff ceil rem st
  if [ ! -f "$f" ]; then echo "absent - - - 0 0 0 0 0"; return; fi
  line="$(head -n 1 "$f" 2>/dev/null || true)"
  o=""; p=""; h=""; e=""
  # shellcheck disable=SC2086 # deliberate word split: the format is one space-separated line.
  for tok in $line; do
    case "$tok" in
      owner=*)   o="${tok#owner=}" ;;
      pid=*)     p="${tok#pid=}" ;;
      host=*)    h="${tok#host=}" ;;
      expires=*) e="${tok#expires=}" ;;
    esac
  done
  mal=0
  case "$e" in ''|*[!0-9]*) mal=1 ;; esac
  mt="$(mtime_of "$f")"
  case "$mt" in ''|*[!0-9]*) mt=0 ;; esac
  if [ "$mal" -eq 1 ]; then
    # A TORN OR FOREIGN-FORMAT LEASE FAILS CLOSED, BUT NOT FOREVER. Treating it as absent
    # would let a write interrupted mid-`mv` cost an agent its lane; treating it as
    # permanently held would wedge the lane, which the contract forbids. mtime + TTL is the
    # honest reading: someone wrote something here recently, so respect it for one TTL.
    e=0; eff=$(( mt + TTL ))
  else
    eff="$e"
  fi
  # THE CEILING. No lease outlives mtime + MAX_AGE, whatever it claims. This is what makes
  # "a stale lease can never wedge a lane permanently" a property of the reader rather than a
  # promise about every future writer.
  ceil=$(( mt + MAX_AGE )); clamped=0
  if [ "$eff" -gt "$ceil" ]; then eff="$ceil"; clamped=1; fi
  rem=$(( eff - NOW ))
  if [ "$rem" -gt 0 ]; then st=held; else st=expired; fi
  printf '%s %s %s %s %s %s %s %s %s\n' "$st" "${o:--}" "${p:--}" "${h:--}" "$e" "$eff" "$rem" "$mal" "$clamped"
}

# combined_state <lane> -> the same 9 fields, for whichever copy expires LATER, plus which.
# Either copy holding the lane holds the lane: the sidecar exists precisely because the
# contract copy can be deleted by a transport that knows nothing about leases.
COMB_STATE=""; COMB_OWNER=""; COMB_PID=""; COMB_HOST=""
COMB_EXP=0; COMB_EFF=0; COMB_REM=0; COMB_MAL=0; COMB_CLAMP=0; COMB_WHERE=""
combined_state() {
  local lane="$1" cf sf best_eff=-1
  cf="$(contract_path "$lane")"; sf="$(sidecar_path "$lane")"
  COMB_STATE=absent; COMB_OWNER="-"; COMB_PID="-"; COMB_HOST="-"
  COMB_EXP=0; COMB_EFF=0; COMB_REM=0; COMB_MAL=0; COMB_CLAMP=0; COMB_WHERE="none"
  local tag f st o p h e eff rem mal cl
  for tag in contract sidecar; do
    if [ "$tag" = contract ]; then f="$cf"; else f="$sf"; fi
    read -r st o p h e eff rem mal cl <<<"$(read_one "$f")"
    [ "$st" = absent ] && continue
    if [ "$eff" -gt "$best_eff" ]; then
      best_eff="$eff"
      COMB_STATE="$st"; COMB_OWNER="$o"; COMB_PID="$p"; COMB_HOST="$h"
      COMB_EXP="$e"; COMB_EFF="$eff"; COMB_REM="$rem"; COMB_MAL="$mal"; COMB_CLAMP="$cl"
      COMB_WHERE="$tag"
    elif [ "$COMB_WHERE" != none ]; then
      COMB_WHERE="both"
    fi
  done
}

# Atomic within a directory: write a temp beside the target, then rename. A concurrent reader
# sees the old line or the new line, never half of either.
write_one() {
  local f="$1" exp="$2" d tmp
  d="$(dirname "$f")"; mkdir -p "$d" || return 1
  tmp="$f.tmp.$$"
  printf 'owner=%s pid=%s host=%s expires=%s\n' "$OWNER" "$CPID" "$CHOST" "$exp" > "$tmp" || return 1
  mv -f "$tmp" "$f"
}

stamp() {                     # stamp <lane> <owner-to-record>
  local lane="$1" o="$2" exp cf sf rc=0
  exp=$(( NOW + TTL ))
  OWNER="$o"
  cf="$(contract_path "$lane")"; sf="$(sidecar_path "$lane")"
  # The contract copy needs the lane dir to exist; a lane that has never been synced has no
  # dir yet, and that is not a reason to fail — the sidecar carries the claim either way.
  if [ -d "$ROOT/$lane" ]; then
    write_one "$cf" "$exp" || rc=1
  else
    echo "lane-lease: note — $ROOT/$lane does not exist yet; sidecar only" >&2
  fi
  write_one "$sf" "$exp" || rc=1
  printf 'state=held lane=%s owner=%s pid=%s host=%s expires=%s remaining=%s\n' \
    "$lane" "$OWNER" "$CPID" "$CHOST" "$exp" "$TTL"
  [ -f "$cf" ] && printf '  contract %s\n' "$cf"
  printf '  sidecar  %s   (outside every rsync destination)\n' "$sf"
  return "$rc"
}

report_state() {              # report_state <lane>  — the machine line, then detail
  printf 'state=%s lane=%s owner=%s pid=%s host=%s expires=%s effective=%s remaining=%s where=%s malformed=%s clamped=%s\n' \
    "$COMB_STATE" "$1" "$COMB_OWNER" "$COMB_PID" "$COMB_HOST" \
    "$COMB_EXP" "$COMB_EFF" "$COMB_REM" "$COMB_WHERE" "$COMB_MAL" "$COMB_CLAMP"
}

case "$VERB" in
  acquire)
    combined_state "$LANE"
    if [ "$COMB_STATE" = held ] && [ "$COMB_OWNER" != "$OWNER" ] && [ "$FORCE" -ne 1 ]; then
      report_state "$LANE"
      echo "lane-lease: REFUSED — lane '$LANE' is held by '$COMB_OWNER' (pid $COMB_PID on $COMB_HOST) for another ${COMB_REM}s." >&2
      echo "            Two agents in one lane is the target-lock contention this exists to prevent." >&2
      echo "            Use a different lane, wait ${COMB_REM}s, or --force if you know that owner is gone." >&2
      exit 3
    fi
    if [ "$COMB_STATE" = held ] && [ "$COMB_OWNER" != "$OWNER" ]; then
      echo "lane-lease: --force — taking lane '$LANE' from '$COMB_OWNER' with ${COMB_REM}s left." >&2
    fi
    stamp "$LANE" "$OWNER"
    ;;
  refresh)
    combined_state "$LANE"
    # Keep a LIVE foreign owner's name and extend it. The alternative — silently renaming the
    # lane's owner to whoever last ran a build — makes the `owner=` field a lie exactly when
    # someone is reading it to find out who to ask.
    if [ "$COMB_STATE" = held ] && [ "$COMB_OWNER" != "-" ] && [ "$COMB_OWNER" != "$OWNER" ]; then
      echo "lane-lease: extending '$COMB_OWNER' lease on '$LANE' (refresh never steals; use acquire --force to take it)" >&2
      stamp "$LANE" "$COMB_OWNER"
    else
      stamp "$LANE" "$OWNER"
    fi
    ;;
  release)
    combined_state "$LANE"
    if [ "$COMB_STATE" = absent ]; then
      echo "state=absent lane=$LANE (nothing to release)"
      exit 0
    fi
    if [ "$COMB_STATE" = held ] && [ "$COMB_OWNER" != "$OWNER" ] && [ "$FORCE" -ne 1 ]; then
      report_state "$LANE"
      echo "lane-lease: REFUSED — lane '$LANE' is held by '$COMB_OWNER', not '$OWNER'. Use --force." >&2
      exit 3
    fi
    rm -f "$(contract_path "$LANE")" "$(sidecar_path "$LANE")"
    echo "state=released lane=$LANE owner=$COMB_OWNER"
    ;;
  show)
    combined_state "$LANE"
    report_state "$LANE"
    [ -f "$(contract_path "$LANE")" ] && printf '  contract %s\n' "$(contract_path "$LANE")"
    [ -f "$(sidecar_path "$LANE")" ]  && printf '  sidecar  %s\n' "$(sidecar_path "$LANE")"
    [ "$COMB_MAL" -eq 1 ] && echo "  ⚠ unparseable line — read as mtime+${TTL}s (fails CLOSED, but expires)" >&2
    [ "$COMB_CLAMP" -eq 1 ] && echo "  ⚠ expires= exceeded mtime+${MAX_AGE}s and was CLAMPED to the ceiling" >&2
    case "$COMB_STATE" in held) exit 0 ;; expired) exit 4 ;; *) exit 5 ;; esac
    ;;
  reap-expired)
    lanes=""
    if [ -n "$LANE" ]; then
      lanes="$LANE"
    else
      for d in "$ROOT"/*/; do
        [ -d "$d" ] || continue
        b="$(basename "$d")"
        [ "$b" = ".leases" ] && continue
        lanes="$lanes $b"
      done
      # A sidecar can outlive its lane dir (the dir was reclaimed, the claim was not). Those
      # are exactly the leases nobody would ever look at again, so enumerate them too.
      for s in "$SIDE_DIR"/*.lease; do
        [ -f "$s" ] || continue
        b="$(basename "$s" .lease)"
        case " $lanes " in *" $b "*) ;; *) lanes="$lanes $b" ;; esac
      done
    fi
    reaped=0; kept=0; none=0
    for l in $lanes; do
      [ -n "$l" ] || continue
      combined_state "$l"
      case "$COMB_STATE" in
        absent) none=$(( none + 1 )); continue ;;
        held)
          kept=$(( kept + 1 ))
          printf 'HELD    %-24s owner=%s remaining=%ss\n' "$l" "$COMB_OWNER" "$COMB_REM"
          continue ;;
      esac
      if [ "$DRY_RUN" -eq 1 ]; then
        printf 'WOULD-REAP %-21s owner=%s expired %ss ago (malformed=%s)\n' "$l" "$COMB_OWNER" "$(( -COMB_REM ))" "$COMB_MAL"
      else
        rm -f "$(contract_path "$l")" "$(sidecar_path "$l")"
        printf 'REAPED  %-24s owner=%s expired %ss ago (malformed=%s)\n' "$l" "$COMB_OWNER" "$(( -COMB_REM ))" "$COMB_MAL"
      fi
      reaped=$(( reaped + 1 ))
    done
    if [ "$DRY_RUN" -eq 1 ]; then
      printf 'reap-expired: %s would be cleared, %s still held, %s unleased (dry run)\n' "$reaped" "$kept" "$none"
    else
      printf 'reap-expired: %s cleared, %s still held, %s unleased\n' "$reaped" "$kept" "$none"
    fi
    ;;
esac
PROGRAM
)

# One text, two transports. `run_lease_program` above documents the shape; the placeholder
# heredocs in it exist only so the function reads correctly — the real dispatch is here, where
# the body variable is fed to whichever `bash -s` applies.
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

dispatch "$VERB" "$ROOT_REL" "$LANE" "$OWNER" "$CLAIM_PID" "$CLAIM_HOST" "$TTL" "$MAX_AGE" "$FORCE" "$DRY_RUN"
