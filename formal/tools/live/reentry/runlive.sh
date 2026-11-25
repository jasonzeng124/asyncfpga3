#!/bin/sh
# runlive.sh -- live.py (floor on, 1 invocation) on every non-refused fixture x {def, auto} that fixtures/results.jsonl
# lacks (nest3 skipped: exhaustive search exceeds the budget, see fixtures/validation.jsonl); one process at a time;
# appends to live_extra.jsonl.
HERE=$(cd "$(dirname "$0")" && pwd)
F=/home/user/rs/cloud/fixtures/frontend
for row in $(python3 -c "
import json
have={(r['fixture'],r['flow']) for r in map(json.loads,open('$HERE/../fixtures/results.jsonl')) if r.get('floor')=='on'}
try: have|={(r['fixture'],r['flow']) for r in map(json.loads,open('$HERE/live_extra.jsonl'))}
except FileNotFoundError: pass
for r in map(json.loads,open('$HERE/sweep.jsonl')):
    if r['label']=='' and r['reentry']!='REFUSED' and (r['fixture'],r['flow']) not in have and r['fixture']!='nest3': print(r['fixture']+':'+r['flow'])
"); do
  fx=${row%:*}; fl=${row#*:}
  if [ "$fl" = auto ]; then A="BDC_AUTO=1"; else A="BDC_X=0"; fi
  env $A LIVE_MEM_GB=2.5 timeout 700 python3 -B $HERE/../fixtures/live.py $F/$fx/comp/handshake_transformed.mlir --inv 1 --max-states 1500000 2>/dev/null \
    | grep '^{' | python3 -c "import json,sys; l=sys.stdin.read().strip(); r=json.loads(l) if l else {'verdict':'TIMEOUT'}; r.update(fixture='$fx',flow='$fl',floor='on'); print(json.dumps(r))" >> $HERE/live_extra.jsonl
  tail -1 $HERE/live_extra.jsonl | cut -c1-200
done
