#!/usr/bin/env bash
# check-nightly-verdict.sh — mirror the last scheduled armed-teeth run onto the path work TAKES.
#
# ═══ THE WOUND THIS CLOSES ══════════════════════════════════════════════════════════════
# `armed-teeth.yml` carries the adversarial suite, and its design is deliberate and good: three
# heavy jobs on `schedule`, guarded off `pull_request` because they cost real time, plus a
# cheap `nightly-verdict` job that runs no folds and mirrors the last scheduled run's
# conclusion onto a PR. That mirror goes red on two things — the last nightly FAILED, and the
# schedule STOPPED FIRING (no completed run in 48h), the latter being the failure that "no
# issue and no annotation can ever report, because the thing that would report it is the thing
# that died."
#
# ⚑ AND IT ONLY TRIGGERS ON `pull_request`. Work in this repo lands on `main` DIRECTLY at a
# ~92-second median, and `main` is not branch-protected. So the mirror is correct, cheap, and
# fires on a path almost nothing takes. Measured 2026-07-28: `scripts/test-gauntlet.sh` — which
# owns the `--ignored` profiles — is invoked by NOTHING; all four `.github/` mentions and the
# one in `local-gates.sh` are comments.
#
# So this puts the same verdict on `pre-push`, which IS the path. It runs no tests and costs one
# API call. It does not add a `push` trigger to the heavy jobs: that would be the cost decision
# ember already made in the other direction for `lean-seed.yml`, and re-making it here would be
# overturning a decision rather than fixing a gap.
#
# ═══ WHAT IT DOES NOT DO ════════════════════════════════════════════════════════════════
# It does not run the adversarial suite. A green here means "the last NIGHTLY was green", which
# is a claim about a run that happened up to 24h ago on a different tree. That is strictly more
# than nothing and strictly less than a gate, and saying so is the point — this repo has spent a
# day deleting things that claimed more than they checked.
#
# Usage:  scripts/check-nightly-verdict.sh
# Exit:   0 last scheduled run succeeded · 1 it failed, or the schedule has stopped · 2 unusable
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2

REPO="${DREGG_REPO:-emberian/dregg}"
MAX_AGE_H="${DREGG_NIGHTLY_MAX_AGE_H:-48}"

command -v gh >/dev/null 2>&1 || {
  echo "check-nightly-verdict: SKIPPED — no \`gh\` on PATH, so the nightly's verdict cannot be read." >&2
  echo "  This is NOT a pass. Install gh, or read it by hand:" >&2
  echo "    gh run list --workflow armed-teeth.yml --event schedule --limit 1" >&2
  exit 0
}

runs="$(gh api "repos/${REPO}/actions/workflows/armed-teeth.yml/runs?event=schedule&status=completed&per_page=1" 2>/dev/null)" || {
  echo "check-nightly-verdict: SKIPPED — the API call failed (offline, or no token)." >&2
  echo "  Not a pass; the adversarial suite's last verdict is simply unread." >&2
  exit 0
}

count="$(printf '%s' "$runs" | python3 -c 'import sys,json;print(json.load(sys.stdin).get("total_count",0))' 2>/dev/null || echo 0)"
if [ "${count:-0}" -eq 0 ]; then
  cat >&2 <<EOF
⛔ check-nightly-verdict: NO COMPLETED SCHEDULED RUN AT ALL.

The adversarial suite has never finished on a schedule, or GitHub has disabled the trigger.
GitHub silently disables \`schedule\` on repositories it considers inactive — and this is the
failure no annotation can report, because the reporter is what died.

  gh workflow run armed-teeth.yml
EOF
  exit 1
fi

read -r concl when < <(printf '%s' "$runs" | python3 -c '
import sys, json
r = json.load(sys.stdin)["workflow_runs"][0]
print(r.get("conclusion") or "none", r.get("updated_at") or "")' 2>/dev/null)

age_h="?"
if [ -n "${when:-}" ]; then
  now=$(date -u +%s)
  then_=$(date -u -j -f "%Y-%m-%dT%H:%M:%SZ" "$when" +%s 2>/dev/null || date -u -d "$when" +%s 2>/dev/null || echo "")
  [ -n "$then_" ] && age_h=$(( (now - then_) / 3600 ))
fi

if [ "$concl" != "success" ]; then
  cat >&2 <<EOF
⛔ check-nightly-verdict: THE LAST NIGHTLY ADVERSARIAL RUN CONCLUDED "$concl" (${age_h}h ago).

A tree should not be pushed against a green wall while the deployed binding teeth are known
broken. The escape is to fix the teeth, not to route around the report:

  gh run list --workflow armed-teeth.yml --event schedule --limit 3
EOF
  exit 1
fi

if [ "$age_h" != "?" ] && [ "$age_h" -gt "$MAX_AGE_H" ]; then
  cat >&2 <<EOF
⛔ check-nightly-verdict: THE SCHEDULE HAS STOPPED FIRING — last completed run was ${age_h}h ago
(threshold ${MAX_AGE_H}h), and it succeeded.

A nightly nobody can tell has stopped is worth exactly as much as a tooth nobody runs.

  gh workflow run armed-teeth.yml
EOF
  exit 1
fi

echo "check-nightly-verdict: last scheduled armed-teeth run SUCCEEDED (${age_h}h ago)."
echo "  ⚠ This is a claim about THAT run, not about this tree. It ran no folds here."
