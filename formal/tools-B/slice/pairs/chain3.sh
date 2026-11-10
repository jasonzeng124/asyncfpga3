#!/bin/bash
# after the (17,5) queue: (17,5) [0,0] sanity slice + the 16 (8,12) slices (2 at once), then (1071,462)
until [ -f /tmp/claude-0/slice2/Q_p175.done ]; do sleep 30; done
for i in 00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15; do [ -d /tmp/claude-0/slice2/p812_$i ] || /tmp/claude-0/slice2/mk2.sh p812_$i $i; done
{ [ -f /tmp/claude-0/slice2/s175_00/DONE ] || echo "s175_00 17 5"; for i in 00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15; do [ -f /tmp/claude-0/slice2/p812_$i/DONE ] || echo "p812_$i 8 12"; done; } | xargs -P 2 -L 1 /tmp/claude-0/slice2/run3.sh
echo done > /tmp/claude-0/slice2/Q_p812.done
/tmp/claude-0/slice2/q3.sh 1071 462 p1071
