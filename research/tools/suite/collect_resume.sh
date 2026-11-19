#!/usr/bin/env bash
# collect_resume.sh REQ -- copy each unfinished task's returned loop state (results/REQ/T/auto/) into
# Usage: research/tools/suite/collect_resume.sh REQ, then commit research/data/suite/resume/REQ/ and file a resume request
# (see research/cluster/requests/suite9r3.sh or norw1r2.sh: AUTO_RESUME at a copy of the state, the same suite_one.sh call).
# research/data/suite/resume/REQ/K_S/: tasks that hit the time limit, and tasks whose loop died on a missed bench clock.
# Prints one line per task.
R=$(cd "$(dirname "$0")/../../.." && pwd); Q=$1; cd "$R" && git fetch -q origin claude/cluster
X=${FARMRES:-/tmp/farmres}/$Q; rm -rf $X; mkdir -p $X; git archive origin/claude/cluster results/$Q | tar -x -C $X --strip-components=2
git show origin/claude/cluster:results/$Q/status.txt | awk 'NR>8 && $1 ~ /^[0-9]+$/ {print $1, $2}' | while read t st; do
  read -r _ _ k _ s _ <<< "$(head -1 $X/$t/task.txt 2>/dev/null)"
  res=$(grep -h "status=" $X/$t/result.txt 2>/dev/null | head -1)
  why=""
  case "$st" in TIMEOUT) why=timeout;; esac
  echo "$res" | grep -q "TIMING FAILED" && why=benchclock
  [ -z "$why" ] && { echo "t$t $k s$s $st: done ($(echo "$res" | grep -o 'status=[A-Z-]*'))"; continue; }
  [ -f $X/$t/auto/sizes_1.vh ] || { echo "t$t $k s$s $st: $why, NO STATE"; continue; }
  D=$R/research/data/suite/resume/$Q/${k}_$s; rm -rf $D; mkdir -p $D
  cp $X/$t/auto/*.txt $X/$t/auto/*.vh $D/ 2>/dev/null; rm -f $D/result.txt; rm -f $D/ca_*_0.*.txt
  echo "t$t $k s$s $st: $why, state $(ls $D/ratchet_*.txt 2>/dev/null | wc -l) ratchets"
done
