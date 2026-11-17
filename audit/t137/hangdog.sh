#!/usr/bin/env bash
# T137 watchdog: a gate run whose log gains no BENCHRES line for 8 wall minutes (a batch takes seconds) is a hang; stop its vvp.
while [ ! -f /root/t137.done ]; do
  for p in $(pgrep -f "^vvp run_baked"); do
    d=$(readlink /proc/$p/cwd); t=${d#/root/t65/work_}; L=/root/t65/$t.log; [ -f $L ] || continue
    n=$(grep -c BENCHRES $L); k=/root/t137_hd_$t
    if [ "$(cat $k 2>/dev/null)" = "$n" ] && [ $(( $(date +%s) - $(stat -c %Y $k) )) -ge 480 ]; then
      kill $p; echo "$(date -u +%H:%M) hangdog: stopped $t after $n BENCHRES" >> /root/t137.log
    elif [ "$(cat $k 2>/dev/null)" != "$n" ]; then echo $n > $k; fi
  done; sleep 30
done
