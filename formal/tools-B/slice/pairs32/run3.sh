#!/bin/bash
# usage: run3.sh NAME A B : like run2.sh, plus disk hygiene. sim -> data -> ao -> data layer (B final config) -> diag.
# Waits for >= MEMGB (6) GB available memory and >= 4 GB free disk before each heavy step; redoes data.py if it did not
# finish (Traceback / missing marker); retries the data layer up to 3x. After the diag files are written and the
# datal log ends with its lchk lines, deletes data_c0.pkl (1.6-1.9 GB); deletes ao/dl pickles of fully passing slices.
D=/tmp/claude-0/slice3/$1; cd $D
memw() { while [ $(awk '/MemAvailable/{print int($2/1e6)}' /proc/meminfo) -lt ${MEMGB:-6} ] || [ $(df --output=avail -BG /tmp | tail -1 | tr -dc 0-9) -lt 6 ]; do sleep 60; done; }
dataok() { [ -f data_c0.pkl ] && grep -q "margin distribution" data.log && ! grep -q Traceback data.log; }
for t in 1 2 3; do dataok && break; memw; python3 sim.py 0 $2 $3 > sim.log 2>&1; python3 data.py 0 > data.log 2>&1; done
dataok || { echo "data.py failed" > FAILED; exit 1; }
for t in 1 2; do [ -f AODONE ] && break; memw; python3 ao.py 0 > ao.log 2>&1; grep -q "round 3\]" ao.log && ! grep -q Traceback ao.log && echo done > AODONE; done
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
if grep -q "upFormB failures" datal.log && grep -q "\[lchk\] GuardTime" datal.log && ! grep -q Traceback obl.log gsum.log; then
  rm -f data_c0.pkl
  if grep -q "guards failed 0$" datal.log && grep -q "upFormB failures 0, sepFormB failures 0" datal.log && grep -q "round 3\].*failures 0 " ao.log; then rm -f ao_c0_*.pkl dl_c0.pkl; fi
fi
rm -f data_c*.pkl; find $D -maxdepth 1 -name "*.pkl" -size +50M -delete   # slice3: task hygiene, after logs
echo done > $D/DONE
