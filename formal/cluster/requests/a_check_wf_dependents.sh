#!/bin/bash
#CLUSTER array=1 cores=16 mem=64G time=240
# Shard A, 2026-11-16: Assembly/CertRun now take EnvWF (SpecWF.lean); PlanRPS's two calls pass envWF_of_env.
# Build and check every file that imports them (too heavy for the cloud sandbox: they import the decoded target net).
set -uo pipefail
key=$(cat formal/lean/lean-toolchain formal/lean/lake-manifest.json | md5sum | cut -c1-12)
[ -f "$SHARED/lake/$key.tar" ] && tar -C formal/lean -xf "$SHARED/lake/$key.tar"
echo "lake cache key $key present=$([ -f "$SHARED/lake/$key.tar" ] && echo yes || echo no)" > "$OUT/env.txt"
git log -1 --format='%H %ci' >> "$OUT/env.txt"
export FORMAL_SLOTS=8
(cd formal/lean && ../slot.sh lake build Formal.Target.AssemblyPS Formal.Target.PlanPS Formal.Target.PlanRPS Formal.Target.CertN1 Formal.Target.CertRun) > "$OUT/build.txt" 2>&1
echo "build rc=$?" >> "$OUT/env.txt"
(cd formal && ./check.sh Formal/Target/SpecWF.lean Formal/Target/Assembly.lean Formal/Target/CertRun.lean Formal/Target/AssemblyPS.lean Formal/Target/PlanPS.lean Formal/Target/PlanRPS.lean Formal/Target/CertN1.lean) > "$OUT/check.txt" 2>&1
rc=$?; echo "check rc=$rc" >> "$OUT/env.txt"; tail -30 "$OUT/build.txt" > "$OUT/build_tail.txt"
exit $rc
