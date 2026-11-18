#!/bin/sh
# Gate-level vs stage-level liveness on the real cells.
#   RESULTS.md  : run.py  (fork / join / bd_mux / cond_br / rings; explore.py)
#   RESULTS2.md : run2.py (arbitrated loop header, bdc_muxn, wide bd_ctree,
#                 FASTFALL; explore2.py) -- QUICK=1 is its default size here
#   muxglitch.txt: muxglitch.py, the bd_mux select-change hazard (SI, early fall, runt)
# QUICK=1 for the smaller sweeps; ONLY=1 or ONLY=2 to run one part.
set -e
cd "$(dirname "$0")"
[ "${ONLY:-1}" = 1 ] || [ -z "$ONLY" ] && python3 -B run.py
if [ -z "$ONLY" ] || [ "$ONLY" = 2 ]; then
    QUICK=${QUICK2:-1} python3 -B run2.py
    python3 -B muxglitch.py | tee muxglitch.txt
fi
