#!/usr/bin/env sh
# install-git-hooks.sh — install this repo's tracked git hooks (secret-scan pre-commit + pre-push,
# plus the rustfmt pre-commit) so any clone/operator gets the guardrail. Run once after cloning:
#
#     sh scripts/install-git-hooks.sh
#
# breadstuffs uses the DEFAULT hooks dir (.git/hooks) because git-lfs owns the post-checkout /
# post-commit / post-merge hooks there — switching core.hooksPath would silently DISABLE LFS. So we
# SYMLINK our tracked hooks into .git/hooks alongside LFS's (our pre-push re-invokes `git lfs pre-push`,
# so LFS keeps working). Symlinks (not copies) mean edits to scripts/git-hooks/* take effect live.
# Idempotent.
set -eu
repo_root="$(git rev-parse --show-toplevel)"
src="$repo_root/scripts/git-hooks"
dst="$repo_root/.git/hooks"
mkdir -p "$dst"

chmod +x "$src"/secret-scan.sh "$src"/pre-commit "$src"/pre-push 2>/dev/null || true

# Only symlink real git-hook names (never the shared secret-scan.sh library).
for name in pre-commit pre-push; do
  [ -f "$src/$name" ] || continue
  ln -sf "../../scripts/git-hooks/$name" "$dst/$name"
  echo "installed hook: .git/hooks/$name -> scripts/git-hooks/$name"
done

echo "done. (git-lfs's post-* hooks left intact; core.hooksPath unchanged — see docs/PUBLISHING-SAFETY.md)"
