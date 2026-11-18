#!/usr/bin/env bash
# run_one.sh TREE(wt_rw|wt_norw) KERNEL SEED -- suite4's per-task command (research/cluster/requests/suite4.sh) minus draws:
# suite_one.sh K S 0 4 with AUTO_FINISH=3 PNR_TIMEOUT=3600, RUNS private per tree, toolchain /root/audit-tc.
set -uo pipefail
T=$1; K=$2; S=$3
export RUNS=/root/agentD/runs_${T#wt_} TC=/root/audit-tc
export CA_JOBS=${CA_JOBS:-1} DRAW_JOBS=2 PNR_TIMEOUT=3600 AUTO_FINISH=3
mkdir -p "$RUNS/wt"
source $TC/openxc7/export.sh > /dev/null
cd /root/agentD/$T
echo "start $(date -u +%FT%TZ) $T $K $S"
nice -n 15 research/tools/suite/suite_one.sh "$K" "$S" 0 4
echo "end $(date -u +%FT%TZ)"
