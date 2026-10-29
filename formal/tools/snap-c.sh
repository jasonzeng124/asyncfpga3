#!/usr/bin/env bash
# Shard C lead's WIP snapshot: refresh LOCK-C, copy probes' unreviewed Formal/{Net,Timing,Gen}
# files into Wip/_snapC (they survive a dead session without being claimed: Wip is not built),
# commit shard-C notes, formal/tools and Wip (nothing > 5 MB), push via push-c.sh. Nothing claimed.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
S=${SID:?set SID}
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $S" > formal/LOCK-C
L=formal/lean
git ls-files -mo --exclude-standard $L/Formal/Net $L/Formal/Timing $L/Formal/Gen | while read -r f; do
  d=$L/Wip/_snapC/${f#$L/}; mkdir -p "$(dirname "$d")"; cp "$f" "$d"; done
git add formal/LOCK-C
{ git ls-files -mo --exclude-standard formal/notes | grep 'formal/notes/C-'
  git ls-files -mo --exclude-standard formal/tools $L/Wip | grep -vE '\.vvp$|/\.lake/|^formal/lean/Wip/_snap[AB]/|^formal/lean/Wip/(Cells|[AB])'; } |
while read -r f; do [ -f "$f" ] && [ "$(stat -c %s "$f")" -lt 5000000 ] && git add "$f"; done
git commit -qm "formal C: WIP snapshot of running probes (notes, tools, Wip/_snapC copies of unreviewed Formal files; nothing claimed), lock

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01HC49FxxmMQBqxSJkm4VEDZ" || true
bash formal/tools/push-c.sh
