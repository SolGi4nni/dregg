#!/usr/bin/env bash
# check-deploy-drift.sh — compare DEPLOYED state against the repo's deploy/ sources.
#
# WHAT IT CHECKS
#   • hbox systemd USER units: every deploy/**/*.service (excluding aws/SUPERSEDED/)
#     is fetched from hbox's ~/.config/systemd/user/<name>.service and byte-diffed
#     against the repo file. Each unit reports MATCH / DRIFT (with the diff) /
#     NOT-INSTALLED, plus `systemctl --user is-active` / `is-enabled`, so a
#     drifted-but-running unit is loud. The repo file is the source of truth
#     (deploy/PRACTICES.md §4: when box and tree disagree, fix the tree in the
#     same breath — this script is how you notice the disagreement).
#   • the REVERSE direction: installed user units on hbox that have NO source in
#     deploy/ (a hand-authored unit never landed in the tree) are listed as
#     UNTRACKED warnings.
#   • linger (deploy/PRACTICES.md §2): reports whether `loginctl enable-linger`
#     is on for the hbox user.
#   • optional, READ-ONLY edge section (--edge): `docker compose ps` + container
#     image ages on the AWS edge, if reachable. The edge uses EC2 Instance
#     Connect ephemeral keys (deploy/aws/README.md), so this usually skips
#     gracefully — it NEVER fails the run and NEVER mutates the box.
#
# WHAT IT DELIBERATELY DOES NOT DO
#   • It is a drift DETECTOR, not a deployer. It never writes to any box, never
#     restarts/installs/enables anything, never runs `docker compose` verbs other
#     than `ps`. All remote commands are read-only (cat / systemctl is-* / ls).
#   • It does not decide which copy is right — it reports the diff. Reconciling
#     (usually: reinstall the repo unit, or land the box's truth in the repo) is
#     an operator action.
#   • It does not check the edge's compose file against the repo — that file is
#     not in the repo yet (deploy/README.md TODO-4). When TODO-4 lands, extend
#     the edge section to diff /opt/dreggnet/docker-compose.yml the same way.
#
# EXIT CODES
#   0  every installed unit matches its repo source (NOT-INSTALLED and UNTRACKED
#      are warnings — a unit may legitimately not be deployed yet)
#   1  at least one INSTALLED unit differs from its repo source (the wound)
#   2  hbox unreachable — the check could not run (a scheduled gate should treat
#      this as loud, not green)
#
# USAGE
#   scripts/check-deploy-drift.sh [--verbose] [--edge] [--help]
#     --verbose   full untruncated diffs + per-unit detail for matches too
#     --edge      also probe the AWS edge (read-only; skips if unreachable)
#   Env overrides: DRIFT_HBOX_HOST (default: hbox),
#                  DRIFT_EDGE_SSH  (default: ssh -i /tmp/eic ubuntu@34.224.208.52)
#
# SHARED-MACHINE REALITY
#   hbox is a co-tenant box: this repo is not the only thing deployed on it.
#   Units whose SOURCE lives in a DIFFERENT repo are legitimately here and must
#   not read as mysterious UNTRACKED noise — they are reported as EXTERNAL with
#   their owning repo named. Add prefixes to KNOWN_EXTERNAL below as more repos
#   share the box. A truly unrecognized unit still lands as UNTRACKED (the wound:
#   a live service no repo claims at all).
#
# KNOWN LIMITATION (v1)
#   Some deploy/**/*.service files are TEMPLATES that deploy-hbox.sh renders (it
#   rewrites ExecStart to the deploy dir, etc.), so a rendered-vs-template diff
#   flags those templated lines even when nothing is wrong. Read the diff and
#   judge; a v2 should compare against the rendered template or ignore known
#   templated fields (ExecStart path, WorkingDirectory).
#
# Meant to become a scheduled gate (cron / CI-adjacent) once it has a place to
# report to; today it is run by hand after any box-touching session.
set -euo pipefail

# Units owned by a DIFFERENT repo on this shared box (prefix -> owning repo).
# Reported as EXTERNAL, not UNTRACKED. Extend as more repos co-tenant hbox.
declare -A KNOWN_EXTERNAL=(
  ["dreggcloud-"]="~/dev/DreggCloud"
)

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEPLOY_DIR="$REPO_ROOT/deploy"
HBOX_HOST="${DRIFT_HBOX_HOST:-hbox}"
# Edge access is EC2 Instance Connect with an ephemeral (~60s) key, per
# deploy/aws/README.md — so this default only works right after send-ssh-public-key.
EDGE_SSH_DEFAULT="ssh -i /tmp/eic -o BatchMode=yes -o ConnectTimeout=8 -o StrictHostKeyChecking=accept-new ubuntu@34.224.208.52"
EDGE_SSH="${DRIFT_EDGE_SSH:-$EDGE_SSH_DEFAULT}"
SSH_OPTS=(-o BatchMode=yes -o ConnectTimeout=10)
DIFF_TRUNC_LINES=60

VERBOSE=0
CHECK_EDGE=0

usage() {
  sed -n '2,50p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

for arg in "$@"; do
  case "$arg" in
    --verbose|-v) VERBOSE=1 ;;
    --edge)       CHECK_EDGE=1 ;;
    --help|-h)    usage; exit 0 ;;
    *) echo "unknown flag: $arg (try --help)" >&2; exit 2 ;;
  esac
done

TMPDIR_LOCAL="$(mktemp -d "${TMPDIR:-/tmp}/deploy-drift.XXXXXX")"
trap 'rm -rf "$TMPDIR_LOCAL"' EXIT

# ---------------------------------------------------------------- repo units
# Every non-SUPERSEDED unit under deploy/ is "meant for hbox": the box topology
# (deploy/README.md) has exactly one systemd host — hbox user units. The edge is
# docker-compose, persvati runs no services. New units are picked up automatically.
repo_units=()   # basenames
declare -a repo_paths=()  # parallel: absolute repo path
while IFS= read -r f; do
  repo_units+=("$(basename "$f")")
  repo_paths+=("$f")
done < <(find "$DEPLOY_DIR" -name '*.service' -not -path '*/SUPERSEDED/*' | sort)

if [ "${#repo_units[@]}" -eq 0 ]; then
  echo "no unit sources found under $DEPLOY_DIR — nothing to check" >&2
  exit 2
fi

echo "== deploy drift check =="
echo "repo:  $REPO_ROOT"
echo "hbox:  $HBOX_HOST (systemd user units)"
echo "units: ${#repo_units[@]} sources under deploy/ (SUPERSEDED excluded)"
echo

# ------------------------------------------------------------- reach hbox
probe_hbox() { ssh "${SSH_OPTS[@]}" "$HBOX_HOST" true 2>/dev/null; }
if ! probe_hbox; then
  echo "hbox: first probe failed, retrying once..." >&2
  sleep 3
  if ! probe_hbox; then
    echo "ERROR: hbox not reachable over ssh ('ssh $HBOX_HOST'). Cannot check drift." >&2
    echo "       (host down, network, or ssh config — the check did NOT run)" >&2
    exit 2
  fi
fi

# --------------------------------------------- one batched remote status call
# Emits: LINGER line, one STATUS line per unit (union of repo + installed),
# and the installed-unit listing. All read-only.
names_str="${repo_units[*]}"
remote_cmd='
UD="$HOME/.config/systemd/user"
printf "LINGER\t%s\n" "$(loginctl show-user "$USER" --property=Linger --value 2>/dev/null || echo unknown)"
installed=$(ls -1 "$UD" 2>/dev/null | grep "\.service$" || true)
for n in '"$names_str"' $installed; do
  case " $seen " in *" $n "*) continue;; esac
  seen="${seen-} $n"
  if [ -f "$UD/$n" ]; then inst=yes; else inst=no; fi
  a=$(systemctl --user is-active -- "$n" 2>/dev/null || true)
  e=$(systemctl --user is-enabled -- "$n" 2>/dev/null || true)
  printf "STATUS\t%s\t%s\t%s\t%s\n" "$n" "$inst" "${a:-unknown}" "${e:-unknown}"
done
'
status_blob="$(ssh "${SSH_OPTS[@]}" "$HBOX_HOST" "$remote_cmd" 2>/dev/null)" || {
  echo "ERROR: hbox status query failed mid-run (load or network). Re-run the check." >&2
  exit 2
}

linger="unknown"
declare -a st_names=() st_inst=() st_active=() st_enabled=()
while IFS=$'\t' read -r tag f1 f2 f3 f4; do
  case "$tag" in
    LINGER) linger="$f1" ;;
    STATUS) st_names+=("$f1"); st_inst+=("$f2"); st_active+=("$f3"); st_enabled+=("$f4") ;;
  esac
done <<<"$status_blob"

lookup() { # lookup <name> <array-prefix> -> echoes field, empty if absent
  local n="$1" p="$2" i
  for i in "${!st_names[@]}"; do
    if [ "${st_names[$i]}" = "$n" ]; then
      case "$p" in
        inst)    echo "${st_inst[$i]}" ;;
        active)  echo "${st_active[$i]}" ;;
        enabled) echo "${st_enabled[$i]}" ;;
      esac
      return 0
    fi
  done
  echo ""
}

echo "hbox linger: $linger  (must be 'yes' — deploy/PRACTICES.md §2)"
echo

# ------------------------------------------------------------ per-unit diff
drift_count=0
missing_count=0
declare -a summary_rows=()

for i in "${!repo_units[@]}"; do
  name="${repo_units[$i]}"
  repo_file="${repo_paths[$i]}"
  rel="${repo_file#"$REPO_ROOT"/}"
  inst="$(lookup "$name" inst)"
  active="$(lookup "$name" active)"
  enabled="$(lookup "$name" enabled)"

  if [ "$inst" != "yes" ]; then
    missing_count=$((missing_count + 1))
    summary_rows+=("$name"$'\t'"no"$'\t'"-"$'\t'"-"$'\t'"NOT-INSTALLED")
    [ "$VERBOSE" -eq 1 ] && echo "[NOT-INSTALLED] $name  (repo: $rel)"
    continue
  fi

  installed_copy="$TMPDIR_LOCAL/$name"
  if ! ssh "${SSH_OPTS[@]}" "$HBOX_HOST" "cat \"\$HOME/.config/systemd/user/$name\"" >"$installed_copy" 2>/dev/null; then
    echo "WARN: could not fetch installed copy of $name (transient?) — marking DRIFT-UNKNOWN" >&2
    summary_rows+=("$name"$'\t'"yes"$'\t'"$active"$'\t'"$enabled"$'\t'"FETCH-FAILED")
    continue
  fi

  if diff_out="$(diff -u -L "repo:$rel" -L "hbox:~/.config/systemd/user/$name" "$repo_file" "$installed_copy")"; then
    summary_rows+=("$name"$'\t'"yes"$'\t'"$active"$'\t'"$enabled"$'\t'"MATCH")
    [ "$VERBOSE" -eq 1 ] && echo "[MATCH] $name  (active=$active enabled=$enabled)"
  else
    drift_count=$((drift_count + 1))
    summary_rows+=("$name"$'\t'"yes"$'\t'"$active"$'\t'"$enabled"$'\t'"DRIFT")
    echo "[DRIFT] $name  — installed unit differs from $rel  (active=$active!)"
    if [ "$VERBOSE" -eq 1 ]; then
      printf '%s\n' "$diff_out"
    else
      printf '%s\n' "$diff_out" | head -n "$DIFF_TRUNC_LINES"
      total_lines=$(printf '%s\n' "$diff_out" | wc -l | tr -d ' ')
      if [ "$total_lines" -gt "$DIFF_TRUNC_LINES" ]; then
        echo "  ... diff truncated ($total_lines lines; --verbose for full)"
      fi
    fi
    echo
  fi
done

# -------------------------------------------- untracked / external units on the box
untracked=()
external=()
for i in "${!st_names[@]}"; do
  n="${st_names[$i]}"
  [ "${st_inst[$i]}" = "yes" ] || continue
  found=0
  for r in "${repo_units[@]}"; do [ "$r" = "$n" ] && { found=1; break; }; done
  [ "$found" -eq 1 ] && continue
  # Not in this repo — is it a known-external (a co-tenant repo's unit)?
  ext_repo=""
  for pfx in "${!KNOWN_EXTERNAL[@]}"; do
    case "$n" in "$pfx"*) ext_repo="${KNOWN_EXTERNAL[$pfx]}"; break ;; esac
  done
  if [ -n "$ext_repo" ]; then
    external+=("$n ($ext_repo)")
    summary_rows+=("$n"$'\t'"yes"$'\t'"${st_active[$i]}"$'\t'"${st_enabled[$i]}"$'\t'"EXTERNAL")
  else
    untracked+=("$n")
    summary_rows+=("$n"$'\t'"yes"$'\t'"${st_active[$i]}"$'\t'"${st_enabled[$i]}"$'\t'"UNTRACKED")
  fi
done

# ------------------------------------------------------------------ summary
echo
echo "== summary: unit -> installed / active / enabled / repo-match =="
{
  printf 'UNIT\tINSTALLED\tACTIVE\tENABLED\tVERDICT\n'
  printf '%s\n' "${summary_rows[@]}"
} | column -t -s $'\t'
echo

if [ "${#external[@]}" -gt 0 ]; then
  echo "note: ${#external[@]} EXTERNAL unit(s) on hbox (owned by a co-tenant repo, not a wound):"
  printf '      %s\n' "${external[@]}"
  echo
fi
if [ "${#untracked[@]}" -gt 0 ]; then
  echo "WARN: ${#untracked[@]} installed unit(s) on hbox have NO source in ANY known repo (land them or add to KNOWN_EXTERNAL):"
  printf '      %s\n' "${untracked[@]}"
  echo
fi
if [ "$missing_count" -gt 0 ]; then
  echo "note: $missing_count repo unit(s) not installed on hbox (warning only — may be aspirational/undeployed)"
fi

# ----------------------------------------------------------------- edge
if [ "$CHECK_EDGE" -eq 1 ]; then
  echo
  echo "== edge (read-only; AWS docker-compose stack) =="
  if $EDGE_SSH true 2>/dev/null; then
    # READ-ONLY. Never a mutating compose verb; never stop the instance
    # (it is the tailnet's public exit — deploy/README.md).
    $EDGE_SSH 'cd /opt/dreggnet 2>/dev/null && docker compose ps 2>/dev/null; echo; docker ps --format "table {{.Names}}\t{{.Image}}\t{{.CreatedAt}}\t{{.Status}}" 2>/dev/null' \
      || echo "edge reachable but docker query failed (permissions?)"
  else
    echo "edge not reachable (skipped) — EC2 Instance Connect key is ephemeral; see deploy/aws/README.md"
  fi
else
  echo "edge: skipped (pass --edge for the read-only edge probe)"
fi

# ------------------------------------------------------------------- verdict
echo
if [ "$drift_count" -gt 0 ]; then
  echo "RESULT: DRIFT — $drift_count installed unit(s) differ from their repo source. Reconcile per deploy/PRACTICES.md §4."
  exit 1
fi
echo "RESULT: clean — every installed unit matches its repo source."
exit 0
