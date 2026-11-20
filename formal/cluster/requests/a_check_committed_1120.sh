#!/bin/bash
#CLUSTER array=1 cores=16 mem=64G time=240
# Shard A, 2026-11-20: the full check.sh over every committed Formal module (all Rewrite/ modules since 11-15: Steps, Width, ScriptRF, ExitCond, Auto*RF).
set -uo pipefail
key=$(cat formal/lean/lean-toolchain formal/lean/lake-manifest.json | md5sum | cut -c1-12)
[ -f "$SHARED/lake/$key.tar" ] && tar -C formal/lean -xf "$SHARED/lake/$key.tar"
echo "lake cache key $key present=$([ -f "$SHARED/lake/$key.tar" ] && echo yes || echo no)" > "$OUT/env.txt"
git log -1 --format='%H %ci' >> "$OUT/env.txt"
(cd formal && ./check.sh --committed) > "$OUT/check.txt" 2>&1
rc=$?
tail -40 "$OUT/check.txt" > "$OUT/check_tail.txt"
echo "rc=$rc" >> "$OUT/env.txt"
exit $rc
