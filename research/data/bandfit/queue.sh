#!/usr/bin/env bash
# sequential: one sim at a time
B=/tmp/claude-0/bandfit
while read K X Y TAG VEC; do
  [ -z "$K" ] && continue
  [ -f $B/logs/${K}_$TAG.log ] && { echo "skip $K $TAG"; continue; }
  while [ $(free -g | awk '/Mem:/{print $7}') -lt 4 ]; do sleep 30; done
  echo "$(date +%T) start $K $X $Y $TAG"
  $B/run1.sh $K $X $Y $TAG $VEC || echo "FAILED $K $TAG"
done < ${1:-$B/queue.txt}
echo "queue finished $(date +%T)"
