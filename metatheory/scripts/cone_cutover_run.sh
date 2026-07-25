#!/bin/bash
# cone_cutover_run.sh — the TRANSACTIONAL orchestrator for a ConeCutover application.
#
#   1. generate the semantic check module from the (still-present) cone;
#   2. STAGE (dry): every edit verified against the real tree, nothing written;
#   3. file-level backups of every touched/retired file;
#   4. APPLY (the Lean tool's own all-or-nothing transaction, with its own backups too);
#   5. BUILD the affected closure — the completeness gate: names were kept, signatures changed,
#      so any consumer the spec missed FAILS TO ELABORATE here;
#   6. on ANY red: RESTORE every backup byte-for-byte and report REFUSED. A half-cutover (a
#      deleted floor theorem without a working, imported replacement) is structurally unreachable.
#
# Run from metatheory/:  bash scripts/cone_cutover_run.sh [build-target ...]
set -u
cd "$(dirname "$0")/.." || exit 1

SCRATCH="${CONE_CUTOVER_SCRATCH:-/tmp/cone-cutover-$$}"
BACKUP="$SCRATCH/backup"
mkdir -p "$BACKUP"

SPEC_MODULE="Dregg2/Tools/ConeCutoverListCommit.lean"
# every file the spec edits or deletes (kept in sync with the spec; the stage step re-verifies).
FILES=(
  "Dregg2/Circuit/RotatedKernelRefinementNotes.lean"
  "Dregg2/Circuit/RotatedKernelRefinementMisc.lean"
  "Dregg2/Circuit/RotatedKernelRefinementLifecycleDisc.lean"
  "Dregg2/Circuit/RotatedKernelRefinementProgram.lean"
  "Dregg2/Circuit/RotatedKernelRefinementCellSeal.lean"
  "Dregg2/Circuit/RotatedKernelRefinementBirth.lean"
  "Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean"
  "Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean"
  "Dregg2/Exec/FieldsMap.lean"
  "Dregg2/Exec/RecordCommit.lean"
  "Dregg2/Tools/ConePortListCommitRun.lean"
  "Dregg2.lean"
  "Dregg2/Circuit/ListCommitPortedCone.lean"
)

restore() {
  echo "── ROLLBACK: restoring every backed-up file byte-for-byte ──"
  for f in "${FILES[@]}"; do
    flat="${f//\//__}"
    if [ -f "$BACKUP/$flat" ]; then
      cp "$BACKUP/$flat" "$f"
    fi
  done
  echo "── rollback complete; the tree is back at its pre-cutover state ──"
}

echo "══ [1/6] generating the semantic check module from the cone ══"
python3 scripts/gen_cutover_check.py || { echo "REFUSED at check-module generation."; exit 1; }

echo "══ [2/6] building the ConeCutover tool ══"
lake build Dregg2.Tools.ConeCutover || { echo "REFUSED: the cutover tool itself does not build."; exit 1; }

echo "══ [3/6] STAGE (dry run — every edit verified, nothing written) ══"
CONE_CUTOVER_STAGE=1 lake env lean "$SPEC_MODULE" || { echo "REFUSED at stage; nothing was touched."; exit 1; }

echo "══ [4/6] backups → $BACKUP ══"
for f in "${FILES[@]}"; do
  cp "$f" "$BACKUP/${f//\//__}" || { echo "REFUSED: cannot back up $f."; exit 1; }
done

echo "══ [5/6] APPLY (the Lean tool's all-or-nothing transaction) ══"
if ! CONE_CUTOVER_WRITE=1 CONE_CUTOVER_BACKUP_DIR="$SCRATCH/tool-backup" lake env lean "$SPEC_MODULE"; then
  echo "REFUSED at apply."
  restore
  exit 1
fi

echo "══ [6/6] closure build (the completeness gate) ══"
TARGETS=("$@")
if [ ${#TARGETS[@]} -eq 0 ]; then TARGETS=(Dregg2); fi
if ! lake build "${TARGETS[@]}"; then
  echo "══ CLOSURE BUILD RED — the cutover is REFUSED ══"
  restore
  exit 1
fi

echo "══ CUTOVER APPLIED AND VERIFIED (backups retained at $BACKUP) ══"
