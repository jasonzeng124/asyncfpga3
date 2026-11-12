#!/bin/bash
# usage: mk2.sh NAME II : /tmp/claude-0/slice2/NAME with path-patched copies of slice/src/*.py and the slice model
# of /tmp/claude-0/slice/k16_II (model.pkl is pair-independent: build.py only reads net.json/bnd.json and C1/C2)
set -e
N=$1; D=/tmp/claude-0/slice2/$N; mkdir -p $D
for f in /tmp/claude-0/slice/src/*.py; do
  sed -e "s#/tmp/claude-0/bsub1/tocc#$D#g" -e "s#/tmp/claude-0/tocc#$D#g" $f > $D/$(basename $f); done
cp /tmp/claude-0/slice/k16_$2/model.pkl /tmp/claude-0/slice/k16_$2/build.log $D/
