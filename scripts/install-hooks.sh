#!/usr/bin/env bash
# Install this repo's tracked git hooks into .git/hooks — WITHOUT touching core.hooksPath (git-lfs
# sets it and owns the post-*/pre-push hooks there; we only ADD a pre-commit alongside them).
# Symlinks (not copies) so edits to scripts/git-hooks/* take effect immediately. Idempotent.
# Run once after cloning: `bash scripts/install-hooks.sh`.
set -euo pipefail
repo_root="$(git rev-parse --show-toplevel)"
src="$repo_root/scripts/git-hooks"
dst="$repo_root/.git/hooks"
mkdir -p "$dst"
for hook in "$src"/*; do
  [ -f "$hook" ] || continue
  name="$(basename "$hook")"
  chmod +x "$hook"
  # relative symlink from .git/hooks/<name> → ../../scripts/git-hooks/<name> (moves with the repo)
  ln -sf "../../scripts/git-hooks/$name" "$dst/$name"
  echo "installed hook: .git/hooks/$name -> scripts/git-hooks/$name"
done

# ── VERIFY THE HOOKS ARE ACTUALLY REACHABLE ──────────────────────────────────────────────────
# git honours core.hooksPath and, when it is set, IGNORES .git/hooks COMPLETELY. ember's global
# config carries core.hooksPath=~/.git-hooks, so on a fresh clone the symlinks above are written
# and then never run — silently. This repo only works today because someone hand-set a repo-LOCAL
# override; nothing in this script did it, so the next clone would install dead hooks.
# That matters more than what the hooks check: an uninstalled guard is decoration. So assert it.
effective="$(git config --get core.hooksPath || true)"
[ -n "$effective" ] || effective="$dst"
case "$effective" in /*) ;; *) effective="$repo_root/$effective" ;; esac
if [ "$effective" != "$dst" ]; then
  echo "core.hooksPath is $effective — git would IGNORE $dst and never run these hooks."
  # Preserve whatever the foreign dir was contributing (git-lfs / 1Password / …): copy across any
  # hook we are not already providing, so redirecting hooksPath does not silently drop them.
  if [ -d "$effective" ]; then
    for foreign in "$effective"/*; do
      [ -f "$foreign" ] || continue
      fname="$(basename "$foreign")"
      case "$fname" in *.sample|*.old) continue ;; esac
      if [ ! -e "$dst/$fname" ]; then
        cp "$foreign" "$dst/$fname"; chmod +x "$dst/$fname"
        echo "  carried over pre-existing hook: $fname (was in $effective)"
      else
        echo "  NOTE: $effective/$fname is SHADOWED by this repo's $fname — merge by hand if you need both"
      fi
    done
  fi
  git config --local core.hooksPath "$dst"     # repo-LOCAL only; never touches global config
  echo "  set repo-local core.hooksPath=$dst"
fi
echo "verified: core.hooksPath resolves to $dst, so .git/hooks/pre-commit really runs."
echo "done. (git-lfs's hooks left intact; global core.hooksPath untouched)"
