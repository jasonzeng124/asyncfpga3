#!/bin/bash
#CLUSTER array=1 cores=16 mem=64G time=240
# Shard A, 2026-11-16: a copy of lean_prime.sh, continued from the saved .lake (fm_lean_prime saved 3582 of 7113 oleans, then
# OUT_OF_MEMORY at 64G with 15 Lean slots). Here at most 8 slots, so that memory holds; reruns are safe (starts from the tar).
export FORMAL_SLOTS=8
# Installs Lean (once, under $HOME/.elan), gets Mathlib, builds this project for at most 200
# minutes, and leaves formal/lean/.lake as one tar file where later tasks can take it
# (formal/cluster/README.md, "Lean"). Starts from the saved file if there is one.
set -uo pipefail
key=$(cat formal/lean/lean-toolchain formal/lean/lake-manifest.json | md5sum | cut -c1-12)
L=$SHARED/lake/$key.tar
{ echo "key $key"; echo "cores $(nproc), JOBS $JOBS, slots ${FORMAL_SLOTS:-unset}"; free -g | sed -n 2p; df -h /tmp | tail -1; } > "$OUT/env.txt" 2>&1
if [ -f "$L" ]; then tar -C formal/lean -xf "$L" && echo "started from the saved .lake" >> "$OUT/env.txt"; fi
t0=$(date +%s)
timeout 12000 formal/setup.sh > "$OUT/setup.txt" 2>&1; rc=$?
{ echo "setup.sh exit $rc after $(( $(date +%s) - t0 )) s"; lean --version
  du -sh formal/lean/.lake formal/lean/.lake/build formal/lean/.lake/packages
  echo "oleans of this project: $(find formal/lean/.lake/build -name '*.olean' 2>/dev/null | wc -l), sources under Formal/: $(find formal/lean/Formal formal/lean/Formal.lean -name '*.lean' | wc -l)"; } >> "$OUT/env.txt" 2>&1
if [ -d formal/lean/.lake/packages/mathlib ]; then
    mkdir -p "$SHARED/lake" && tar -C formal/lean -cf "$L.tmp.$TASK" .lake && mv "$L.tmp.$TASK" "$L" && ls -l "$L" >> "$OUT/env.txt" 2>&1
fi
exit $rc
