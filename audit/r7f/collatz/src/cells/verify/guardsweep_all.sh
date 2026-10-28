#!/usr/bin/env bash
# Run verify/guardsweep.py over all 24 rloc SDFs (2 designs x 3 variants x 4
# seeds), unattended, saving each run's raw stdout to a file so nothing has to
# be re-run. Meant to be launched with run_in_background / nohup since the
# full sweep is on the order of an hour.
set -u
cd "$(dirname "$0")/.." || exit 2
OUT=build/rloc/guardsweep

sdfs=(
  gcd_ps.base:build/rloc/gcd_ps.base/gcd_ps.sdf
  gcd_ps.v1:build/rloc/gcd_ps.v1/gcd_ps.sdf
  gcd_ps.v2:build/rloc/gcd_ps.v2/gcd_ps.sdf
  ipow_ps.base:build/rloc/ipow_ps.base/ipow_ps.sdf
  ipow_ps.v1:build/rloc/ipow_ps.v1/ipow_ps.sdf
  ipow_ps.v2:build/rloc/ipow_ps.v2/ipow_ps.sdf
  seed1_gcd_ps.base:build/rloc/seed1/gcd_ps.base/gcd_ps.sdf
  seed1_gcd_ps.v1:build/rloc/seed1/gcd_ps.v1/gcd_ps.sdf
  seed1_gcd_ps.v2:build/rloc/seed1/gcd_ps.v2/gcd_ps.sdf
  seed1_ipow_ps.base:build/rloc/seed1/ipow_ps.base/ipow_ps.sdf
  seed1_ipow_ps.v1:build/rloc/seed1/ipow_ps.v1/ipow_ps.sdf
  seed1_ipow_ps.v2:build/rloc/seed1/ipow_ps.v2/ipow_ps.sdf
  seed2_gcd_ps.base:build/rloc/seed2/gcd_ps.base/gcd_ps.sdf
  seed2_gcd_ps.v1:build/rloc/seed2/gcd_ps.v1/gcd_ps.sdf
  seed2_gcd_ps.v2:build/rloc/seed2/gcd_ps.v2/gcd_ps.sdf
  seed2_ipow_ps.base:build/rloc/seed2/ipow_ps.base/ipow_ps.sdf
  seed2_ipow_ps.v1:build/rloc/seed2/ipow_ps.v1/ipow_ps.sdf
  seed2_ipow_ps.v2:build/rloc/seed2/ipow_ps.v2/ipow_ps.sdf
  seed3_gcd_ps.base:build/rloc/seed3/gcd_ps.base/gcd_ps.sdf
  seed3_gcd_ps.v1:build/rloc/seed3/gcd_ps.v1/gcd_ps.sdf
  seed3_gcd_ps.v2:build/rloc/seed3/gcd_ps.v2/gcd_ps.sdf
  seed3_ipow_ps.base:build/rloc/seed3/ipow_ps.base/ipow_ps.sdf
  seed3_ipow_ps.v1:build/rloc/seed3/ipow_ps.v1/ipow_ps.sdf
  seed3_ipow_ps.v2:build/rloc/seed3/ipow_ps.v2/ipow_ps.sdf
)

for entry in "${sdfs[@]}"; do
  name="${entry%%:*}"
  sdf="${entry#*:}"
  dst="$OUT/${name}.txt"
  if [ -s "$dst" ] && grep -q "^guardband" "$dst" 2>/dev/null; then
    echo "skip $name (already done)"
    continue
  fi
  echo "=== $name ($(date)) ==="
  python3 verify/guardsweep.py "$sdf" > "$dst.tmp" 2>&1
  mv "$dst.tmp" "$dst"
  echo "--- $name done ($(date)) ---"
done
echo "ALL DONE $(date)"
