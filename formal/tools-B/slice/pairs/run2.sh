#!/bin/bash
# usage: run2.sh NAME A B : sim (pair A,B) -> data -> ao (control) -> data layer (B final config) -> diag.
# Waits for >= MEMGB (6) GB available before each step and retries the data layer (up to 3x) if killed.
D=/tmp/claude-0/slice2/$1; cd $D
memw() { while [ $(awk '/MemAvailable/{print int($2/1e6)}' /proc/meminfo) -lt ${MEMGB:-6} ]; do sleep 60; done; }
[ -f data_c0.pkl ] || { memw; python3 sim.py 0 $2 $3 > sim.log 2>&1; python3 data.py 0 > data.log 2>&1; }
[ -f AODONE ] || { memw; python3 ao.py 0 > ao.log 2>&1; grep -q "round" ao.log && echo done > AODONE; }
E="CRELUP=1 REL=1 RELD=99 RELK=16 RELTRY=64 UPJOIN=1 JOINANC=1 LGTOPOFF=1 COVUP=1 COVMEET=1 MUXX=1 XOPT=1 ESPLIT=1 ENDFIX=2 LCHK=1 NPASS=10"
for try in 1 2 3; do
  grep -q "relative-clause stats" datal.log 2>/dev/null && break
  memw; date +%s > T0
  env $E OUTP=$D/dl_c0.pkl python3 rundt.py 0 > datal.log 2>&1
  date +%s > T1
  grep -q "relative-clause stats" datal.log && break
  cp datal.log datal_killed$try.log; sleep 120
done
for f in obl ana2; do sed -e "s#/tmp/claude-0/bsub1/tocc#$D#g" -e "s#/tmp/claude-0/bsub1/chains_#$D/chains_#g" /tmp/claude-0/slice/src/$f.py > $D/$f.py; done
python3 obl.py $D/dl_c0.pkl 0 $1 > obl.log 2>&1
python3 ana2.py 0 $D/dl_c0.pkl > ana2.log 2>&1
python3 /tmp/claude-0/slice/src/gsum.py $D > gsum.log 2>&1
echo done > $D/DONE
