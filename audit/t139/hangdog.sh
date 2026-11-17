#!/usr/bin/env bash
# T139 watchdog (copy of t137): a gate run whose log gains no BENCHRES line for 8 wall minutes (a batch takes seconds) is a hang; stop its vvp.
while [ ! -f /root/t139.done ]; do
  for p in $(pgrep -f "^vvp run_baked"); do
    d=$(readlink /proc/$p/cwd); t=${d#/root/t65/work_}; L=/root/t65/$t.log; [ -f $L ] || continue
    n=$(grep -c BENCHRES $L); k=/root/t139_hd_$t
    if [ "$(cat $k 2>/dev/null)" = "$n" ] && [ $(( $(date +%s) - $(stat -c %Y $k) )) -ge 480 ]; then
      kill $p; echo "$(date -u +%H:%M) hangdog: stopped $t after $n BENCHRES" >> /root/t139.log
    elif [ "$(cat $k 2>/dev/null)" != "$n" ]; then echo $n > $k; fi
  done; sleep 30
done
