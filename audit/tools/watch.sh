#!/usr/bin/env bash
# audit watcher: fetch every 10 min; exit when a board item / headline / SIM-VS-BOARD / formal target / audit PROGRAM
# changes, or after ${1:-110} minutes. Prints what changed.
cd /home/user/asyncfpga3
F="research/BOARD-QUEUE.md research/data/fifteen/README.md research/SIM-VS-BOARD.md"
snap() { for f in $F; do git show origin/claude/research:$f 2>/dev/null | md5sum; done
         git ls-tree -r origin/claude/formal formal/target formal/lean/Formal/Target/Spec.lean | grep -v MARGINS | md5sum
         git show origin/claude/audit:audit/PROGRAM.md | md5sum; }
git fetch -q origin 2>/dev/null; A=$(snap); end=$(( $(date +%s) + ${1:-110}*60 ))
while [ $(date +%s) -lt $end ]; do sleep 600; git fetch -q origin 2>/dev/null; B=$(snap)
  [ "$A" != "$B" ] && { echo "CHANGED $(date -u)"; diff <(echo "$A") <(echo "$B"); exit 0; }; done
echo "QUIET $(date -u)"
