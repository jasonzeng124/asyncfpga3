#!/usr/bin/env bash
# usage: peak.sh FILE.lean  -- runs lean via slot.sh, prints wall time and peak RSS of lean (kills at 3.8 GB)
cd /home/user/asyncfpga3/formal/lean
export PATH=$HOME/.elan/bin:$PATH; export LEAN_PATH=$PWD/.lake/build/lib/lean
s=$(date +%s)
../slot.sh lean "$@" > /tmp/claude-0/peak.$$.log 2>&1 &
pk=0
while kill -0 $! 2>/dev/null; do
  for p in $(pgrep -f "lean $*" ); do
    r=$(awk '/VmRSS/{print $2}' /proc/$p/status 2>/dev/null); [ -n "$r" ] && [ "$r" -gt "$pk" ] && pk=$r
    if [ -n "$r" ] && [ "$r" -gt 3800000 ]; then kill $p; echo "KILLED at ${r}KB"; fi
  done
  sleep 1
done
grep -v "^Hint\|^Note" /tmp/claude-0/peak.$$.log | head -30
echo "time $(( $(date +%s) - s ))s peak ${pk}KB"
