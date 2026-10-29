#!/usr/bin/env bash
# Lead's WIP snapshot: refresh the lock, copy probes' unreviewed Formal/Core files into
# Wip/_snapA (so they survive a dead session without being claimed), commit notes,
# tools-A and Wip (no .vvp, nothing > 5 MB), push via push.sh. Nothing here is claimed.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
S=${SESSION_ID:-session_01HC49Fwiv93CFgTH6CuFfLh}
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $S" > formal/LOCK
L=formal/lean
# unreviewed: untracked or modified files under Formal/Core and Formal.lean-owned dirs
git ls-files -mo --exclude-standard $L/Formal/Core | while read -r f; do
  d=$L/Wip/_snapA/${f#$L/}; mkdir -p "$(dirname "$d")"; cp "$f" "$d"; done
git add formal/LOCK
git ls-files -mo --exclude-standard formal/notes formal/tools-A $L/Wip formal/out/FOR-RESEARCH.md formal/out/HOWTO-new-kernel.md | grep -vE '\.vvp$|/\.lake/|formal/notes/[BC]-' | while read -r f; do
  [ -f "$f" ] && [ "$(stat -c %s "$f")" -lt 5000000 ] && git add "$f"; done
git ls-files -d formal/tools-A formal/lean/Wip formal/notes | grep -vE "_snap[BC]/|formal/notes/[BC]-" | xargs -r git rm -q --cached --
git commit -qm "formal A: WIP snapshot of running probes (notes, tools-A, Wip/_snapA copies of unreviewed Core files; nothing claimed), lock

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01HC49Fwiv93CFgTH6CuFfLh" || true
bash formal/tools-A/push.sh
