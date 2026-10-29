#!/usr/bin/env bash
# C-wit (copy of Wip/C8t/peak.sh): usage peak.sh [-o OLEAN] FILE.lean
# runs lean via slot.sh, prints wall time and peak RSS (kills the process above 3.8 GB)
cd /home/user/asyncfpga3/formal/lean
export PATH=$HOME/.elan/bin:$PATH; export LEAN_PATH=$PWD/.lake/build/lib/lean
LOG=${TMPDIR:-/tmp}/cwit-peak.$$.log
s=$(date +%s)
../slot.sh lean "$@" > $LOG 2>&1 &
pk=0
while kill -0 $! 2>/dev/null; do
  for p in $(pgrep -f "lean $*" ); do
    r=$(awk '/VmRSS/{print $2}' /proc/$p/status 2>/dev/null); [ -n "$r" ] && [ "$r" -gt "$pk" ] && pk=$r
    if [ -n "$r" ] && [ "$r" -gt 3800000 ]; then kill $p; echo "KILLED at ${r}KB"; fi
  done
  sleep 1
done
wait $!; rc=$?
grep -v "^Hint\|^Note" $LOG | head -40
echo "rc $rc time $(( $(date +%s) - s ))s peak ${pk}KB"
rm -f $LOG
