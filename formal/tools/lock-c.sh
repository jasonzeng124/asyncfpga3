#!/usr/bin/env bash
# Shard C: refresh formal/LOCK-C, commit only it, and push via push-c.sh
# (works while probes keep the tree dirty; never stashes).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
SID=${SID:?set SID to this session id}
date -u +"%Y-%m-%dT%H:%M:%SZ $SID" > formal/LOCK-C
git add formal/LOCK-C
git commit -qm "${1:-formal C: lock refresh}" -- formal/LOCK-C
formal/tools/push-c.sh
