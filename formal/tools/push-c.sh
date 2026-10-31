#!/usr/bin/env bash
# Push the lead's local commits on claude/formal while probes keep editing tracked
# files in the main tree (git pull --rebase refuses a dirty tree, and git stash is
# banned in a shared tree). Rebases in a side worktree, pushes, then moves the main
# tree's HEAD to the pushed commit and refreshes only the files other shards changed
# (those are never edited in this tree, so no local work is touched).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
B=claude/formal; WT=/tmp/formal-push-wt-c
git fetch -q origin $B
old=$(git rev-parse HEAD); up=$(git rev-parse origin/$B)
if git merge-base --is-ancestor "$up" "$old"; then git push -q origin HEAD:$B; echo "[push] fast-forward $old"; exit 0; fi
base=$(git merge-base "$old" "$up")
[ -d $WT ] || git worktree add -q --detach $WT "$old"
git -C $WT checkout -q --detach "$old"
git -C $WT rebase -q "$up" || { git -C $WT rebase --abort; echo "[push] REBASE CONFLICT: you touched a file you do not own"; exit 1; }
new=$(git -C $WT rev-parse HEAD)
git -C $WT push -q origin "$new":$B
mapfile -t theirs < <(git diff --name-only "$base" "$up")
git reset -q --mixed "$new"
for f in "${theirs[@]}"; do
  if git cat-file -e "$new:$f" 2>/dev/null; then git checkout -q "$new" -- "$f"; else rm -f "$f"; fi
done
echo "[push] rebased onto $up, pushed $new (${#theirs[@]} files from others refreshed)"
