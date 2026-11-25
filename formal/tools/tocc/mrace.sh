#!/bin/bash
cd /tmp/claude-0/tocc
mkdir -p mr
SLOW='[["SLICE_X15Y19.B6","SLICE_X17Y18.B6"],["SLICE_X11Y53.A6","SLICE_X10Y53.D6"],["SLICE_X6Y47.B6","SLICE_X6Y47.A6"],["SLICE_X7Y50.D5","SLICE_X6Y51.A6"],["SLICE_X6Y33.D5","SLICE_X6Y34.A6"],["SLICE_X10Y31.B6","SLICE_X10Y31.A6"],["SLICE_X10Y28.A6","SLICE_X10Y26.B6"],["SLICE_X10Y28.A5","SLICE_X10Y26.B6"],["SLICE_X17Y18.B6","SLICE_X17Y19.B6"],["SLICE_X17Y18.B6","SLICE_X16Y18.A6"]]'
FAST='[["SLICE_X15Y19.B6","SLICE_X16Y18.A6"],["SLICE_X11Y53.A6","SLICE_X15Y19.B6"],["SLICE_X6Y47.B6","SLICE_X11Y53.A6"],["SLICE_X7Y63.A5","SLICE_X6Y47.B6"],["SLICE_X7Y50.D5","SLICE_X7Y63.A5"],["SLICE_X6Y33.D5","SLICE_X7Y50.D5"],["SLICE_X10Y42.D5","SLICE_X6Y33.D5"],["SLICE_X10Y31.B6","SLICE_X10Y42.D5"],["SLICE_X16Y18.A6","SLICE_X15Y19.C5"],["SLICE_X16Y18.A6","SLICE_X14Y18.A6"]]'
for c in 0 1; do for pr in 12,18 8,12 17,5; do a=${pr%,*}; b=${pr#*,}
  for mode in mid allfast; do
    if [ $mode = mid ]; then ADV="{\"slowpins\": $SLOW, \"fastpins\": $FAST}"; else ADV="{\"slowpins\": $SLOW, \"allfast\": true}"; fi
    f=mr/m_c${c}_${a}_${b}_$mode.pkl
    ADV="$ADV" OUT=$f timeout 900 python3 simx.py $c $a $b > /dev/null 2>&1
    python3 hazchk.py $f >> mr/res.txt 2>&1
  done; done; done
echo done > mr/done
