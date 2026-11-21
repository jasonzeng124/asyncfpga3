#!/bin/bash
# usage: mk3.sh NAME C1 C2 : /tmp/claude-0/slice3/NAME with path-patched copies of slice/src/*.py and a FRESH slice model
set -e
N=$1; D=/tmp/claude-0/slice3/$N; mkdir -p $D
for f in /tmp/claude-0/slice/src/*.py; do
  sed -e "s#/tmp/claude-0/bsub1/tocc#$D#g" -e "s#/tmp/claude-0/tocc#$D#g" $f > $D/$(basename $f); done
cd $D; C1=$2 C2=$3 python3 build.py /tmp/claude-0/slice/base/net.json /tmp/claude-0/slice/base/bnd.json model.pkl > build.log 2>&1
