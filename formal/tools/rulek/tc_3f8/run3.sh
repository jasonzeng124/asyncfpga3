#!/usr/bin/env bash
# Probe C-10g: the two obligations no project rule checks (W = 8e latch open width,
# R = RT_FB), per seed:  run3.sh SEED...  -> build/obl3_SEED.tc, build/t3_SEED.out
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
for s in ${*:-d 2 3 4}; do
  O=build/tree_$s/cells/build/hw/gcd_hw
  python3 extract.py "$O" gcd_hw --cells "build/tree_$s/cells" --osc dhk --osc invhk --no-hi --rules2 WR \
      --out build/obl3_$s.tc --json build/obl3_$s.json 2> build/extract3_$s.log || { tail build/extract3_$s.log; continue; }
  .lake/build/bin/tcheck build/obl3_$s.tc > build/t3_$s.out 2> build/t3_$s.err
  echo "seed $s: $(tail -1 build/extract3_$s.log) / $(tail -1 build/t3_$s.err)"
done
