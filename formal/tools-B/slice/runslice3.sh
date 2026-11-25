#!/bin/bash
# usage: runslice3.sh NAME : like runslice2.sh, but waits for free memory before the data layer and retries it
# (up to 3 times) if it was killed (OOM) before finishing
D=/tmp/claude-0/slice/$1; cd $D
[ -f data_c0.pkl ] || { python3 sim.py 0 12 18 > sim.log 2>&1; python3 data.py 0 > data.log 2>&1; }
[ -f AODONE ] || { python3 ao.py 0 > ao.log 2>&1; echo done > AODONE; }
E="CRELUP=1 REL=1 RELD=99 RELK=16 RELTRY=64 UPJOIN=1 JOINANC=1 LGTOPOFF=1 COVUP=1 COVMEET=1 MUXX=1 XOPT=1 ESPLIT=1 ENDFIX=2 LCHK=1 NPASS=10"
for try in 1 2 3; do
  while [ $(awk '/MemAvailable/{print int($2/1e6)}' /proc/meminfo) -lt ${MEMGB:-6} ]; do sleep 60; done
  env $E OUTP=$D/dl_c0.pkl python3 rundt.py 0 > datal.log 2>&1
  grep -q "relative-clause stats" datal.log && break
  cp datal.log datal_killed$try.log; sleep 120
done
/tmp/claude-0/slice/diag.sh $1
echo done > $D/DONE
