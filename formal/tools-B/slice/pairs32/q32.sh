#!/bin/bash
# usage: q32.sh : (17,5) slices [i/32,(i+1)/32], i=0..11, at most 2 at once (skips DONE)
for i in 00 01 02 03 04 05 06 07 08 09 10 11; do j=$((10#$i)); D=/tmp/claude-0/slice3/p32_$i
  [ -f $D/model.pkl ] || /tmp/claude-0/slice3/mk3.sh p32_$i $j/32 $((j+1))/32; done
for i in 00 01 02 03 04 05 06 07 08 09 10 11; do [ -f /tmp/claude-0/slice3/p32_$i/DONE ] || echo "p32_$i 17 5"; done | xargs -P 2 -L 1 /tmp/claude-0/slice3/run3.sh
echo done > /tmp/claude-0/slice3/Q.done
