#!/usr/bin/env bash
# queue.sh QUEUEFILE -- run1.sh on each line "KERNEL X Y TAG [VECFILE]", one at a time (start one queue per core you
# may use). A line whose log ($RUNS/bandfit/logs/KERNEL_TAG.log) exists is skipped. Each run starts only while the
# job's RSS (memory.stat total_rss: page cache is reclaimed, so usage_in_bytes, which counts it, over-blocks) is below
# BANDFIT_RSS_GB (default 30; a GLS compile adds 2-5 GB, gcd's 9.4).
H=$(cd "$(dirname "$0")" && pwd); B=${RUNS:?RUNS must be set}/bandfit
MS=${BANDFIT_MEMSTAT:-/sys/fs/cgroup/memory/slurm/uid_259286/job_29466208/memory.stat}
rssgb() { [ -r "$MS" ] && awk '/^total_rss /{print int($2/1073741824)}' "$MS" || echo 0; }
while read -r K X Y TAG VEC; do
  [ -z "$K" ] && continue
  case $K in \#*) continue;; esac
  [ -f "$B/logs/${K}_$TAG.log" ] && { echo "skip $K $TAG"; continue; }
  case $VEC in ""|/*) ;; *) VEC=$H/$VEC;; esac      # a relative VECFILE is relative to this directory
  until [ "$(rssgb)" -lt "${BANDFIT_RSS_GB:-30}" ]; do sleep 20; done
  echo "$(date +%T) start $K $X $Y $TAG"
  "$H/run1.sh" "$K" "$X" "$Y" "$TAG" ${VEC:+"$VEC"} || echo "FAILED $K $TAG"
done < "${1:?queue file}"
echo "queue finished $(date +%T)"
