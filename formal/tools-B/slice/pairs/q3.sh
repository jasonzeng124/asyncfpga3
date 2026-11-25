#!/bin/bash
# usage: q3.sh A B PREFIX : 16 uniform slices for pair (A,B) (skips slices with DONE), at most 2 at once
A=$1; B=$2; P=$3
for i in 00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15; do [ -d /tmp/claude-0/slice2/${P}_$i ] || /tmp/claude-0/slice2/mk2.sh ${P}_$i $i; done
for i in 00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15; do [ -f /tmp/claude-0/slice2/${P}_$i/DONE ] || echo "${P}_$i $A $B"; done | xargs -P 2 -L 1 /tmp/claude-0/slice2/run3.sh
echo done > /tmp/claude-0/slice2/Q_$P.done
