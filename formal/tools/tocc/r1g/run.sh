#!/bin/bash
cd /tmp/claude-0/r1g
export ARTFIX=1 ARTFIX2=1 REL=1 RELD=99 RELK=16 RELTRY=64 SEPIV1=1 NPASS=12 CTXAFTER=1 UPMOVE=1 TAG=${TAG:-_g}
exec python3 rundatal.py $1 > datal_c$1${TAG}.log 2>&1
