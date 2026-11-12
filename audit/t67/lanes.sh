#!/usr/bin/env bash
# T67: run the period runs as their builds finish, two lanes
lane() { for r in "$@"; do until grep -q BUILDDONE build_$r.log 2>/dev/null; do sleep 20; done; bash run.sh $r; done; }
lane x50_3 x50_4 x50_5 & lane pmf_3 pmf_4 pmf_5 & wait; echo LANESDONE > lanes.done
