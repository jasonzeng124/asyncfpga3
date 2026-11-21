#!/bin/bash
# per-slice data-layer diagnostics: obl.py (failing items by kind, loop covers) + ana2.py (claim-end roots of failing guards)
D=/tmp/claude-0/slice/$1; cd $D
for f in obl ana2; do sed -e "s#/tmp/claude-0/bsub1/tocc#$D#g" -e "s#/tmp/claude-0/bsub1/chains_#$D/chains_#g" /tmp/claude-0/slice/src/$f.py > $D/$f.py; done
python3 obl.py $D/dl_c0.pkl 0 $1 > obl.log 2>&1
python3 ana2.py 0 $D/dl_c0.pkl > ana2.log 2>&1
python3 /tmp/claude-0/slice/src/gsum.py $D > gsum.log 2>&1
