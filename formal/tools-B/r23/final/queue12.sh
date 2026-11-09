#!/bin/bash
E="CRELUP=1 REL=1 RELD=99 RELK=16 RELTRY=64 UPJOIN=1 JOINANC=1 LGTOPOFF=1 COVUP=1 COVMEET=1 MUXX=1 XOPT=1 ESPLIT=1 ENDFIX=2 LCHK=1 NPASS=10"
cd /tmp/claude-0/bsub1/tocc175; env $E OUTP=/tmp/claude-0/bsub1/tocc175/ef3_c0.pkl python3 rundt_es.py 0 > ef3_c0.log 2>&1 &
cd /tmp/claude-0/bsub1/tocc; env $E OUTP=/tmp/claude-0/bsub1/tocc/ef3_c0.pkl python3 rundt.py 0 > ef3_c0.log 2>&1; wait
until [ -f /tmp/claude-0/bsub1/prep.done ]; do sleep 30; done
cd /tmp/claude-0/bsub1/tocc812; env $E OUTP=/tmp/claude-0/bsub1/tocc812/ef3_c1.pkl python3 rundt.py 1 > ef3_c1.log 2>&1 &
cd /tmp/claude-0/bsub1/tocc1071; env $E OUTP=/tmp/claude-0/bsub1/tocc1071/ef3_c1.pkl python3 rundt.py 1 > ef3_c1.log 2>&1; wait
echo done > /tmp/claude-0/bsub1/queue12.done
