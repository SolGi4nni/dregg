#!/usr/bin/env bash
# ⚑ Materialise `circuit/descriptors/` AS OF A GIT REV into a scratch directory, so a gate can be
# asked its question about HEAD rather than about a shared working tree.
#
# In this repo several lanes edit `circuit/descriptors/` at once. A gate run against the working
# tree therefore reports a fact about *whatever the other lanes have half-landed*, and that fact
# expires as soon as they commit. The repo has already paid for this: a carrier-binding test recorded
# a real divergence as "a sibling lane's uncommitted re-emit … not this file's to chase", the batch
# landed, and nothing re-asked the question.
#
# ⚠ This exists because `git stash` is NOT swarm-safe — it mutates the shared working tree that every
# parallel lane is building in. `git cat-file` reads the object store and touches nothing.
#
#   scripts/materialise-descriptors-at.sh [REV] [DEST]
#
# REV defaults to HEAD, DEST to a mktemp dir. Prints DEST on stdout.
set -euo pipefail

REV="${1:-HEAD}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEST="${2:-$(mktemp -d "${TMPDIR:-/tmp}/dregg-descriptors-XXXXXX")}"

mkdir -p "$DEST"

# `git ls-tree -r --name-only` lists the paths the rev HAS, which is the point: a file added only in
# the working tree must NOT appear, or the materialised tree is not the rev's.
count=0
while IFS= read -r path; do
    rel="${path#circuit/descriptors/}"
    mkdir -p "$DEST/$(dirname "$rel")"
    git -C "$ROOT" cat-file blob "$REV:$path" > "$DEST/$rel"
    count=$((count + 1))
done < <(git -C "$ROOT" ls-tree -r --name-only "$REV" -- circuit/descriptors)

if [ "$count" -eq 0 ]; then
    echo "materialise-descriptors-at: $REV has no circuit/descriptors — refusing to hand back an" \
         "empty tree, which every gate would pass vacuously" >&2
    exit 1
fi

echo "materialise-descriptors-at: $count files from $(git -C "$ROOT" rev-parse --short "$REV") -> $DEST" >&2
echo "$DEST"
