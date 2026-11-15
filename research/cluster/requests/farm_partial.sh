#!/bin/bash
#CLUSTER array=1-3 cores=1 mem=1G time=20
# Farm self-test (2026-11-15): tasks 1 and 3 finish at once, task 2 takes 13 minutes. The results of
# 1 and 3 must appear on claude/cluster while 2 is still running (state "running (2 of 3 ...)").
echo "task $TASK at $(date -u +%FT%TZ)" > "$OUT/hello.txt"
[ "$TASK" = 2 ] && sleep 780
exit 0
