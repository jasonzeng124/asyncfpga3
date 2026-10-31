#!/usr/bin/env bash
# glsq rerun with the corrected monitors (after audit P15a): 4 seeds without scatter, then seed 4 with scatter.
G="$(cd "$(dirname "$0")" && pwd)"
for s in d 3 4 5; do bash $G/run_seed.sh $s; done
bash $G/run_seed.sh 4 > /dev/null   # leave seed 4's route built for the scatter runs
SIG=0.05 DRAWS="1 2 3" bash $G/run_scatter.sh seed4
SIG=0.10 DRAWS="1 2" bash $G/run_scatter.sh seed4
echo ALLDONE
