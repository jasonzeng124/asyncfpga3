#!/bin/bash
#CLUSTER array=1-1 cores=1 mem=1G time=5
# Shard C (c_mem23): SUPERSEDED by c_mem24..c_mem31 (the same 126 routes in 16-task parts). As filed, 126 tasks x 2 cores
# ran 100 at a time = the farm's whole 200 cores, so it would have waited for every other request. No-op.
echo "superseded by c_mem24..31" > $OUT/task.txt
exit 0
