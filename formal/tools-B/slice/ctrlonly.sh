#!/bin/bash
# control-only prescan: sim, data.py, ao.py for each named slice (sequential)
for s in "$@"; do D=/tmp/claude-0/slice/$s; cd $D
  [ -f sim.log ] || python3 sim.py 0 12 18 > sim.log 2>&1
  [ -f data_c0.pkl ] || python3 data.py 0 > data.log 2>&1
  [ -f AODONE ] || { python3 ao.py 0 > ao.log 2>&1; echo done > AODONE; }
done
echo done > /tmp/claude-0/slice/CTRL_$1.done
