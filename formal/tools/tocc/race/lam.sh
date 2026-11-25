#!/bin/bash
c=$1; lam=$2
ADV=$(python3 -c "import json;s=json.load(open('/tmp/claude-0/race/sets_c$c.json'));print(json.dumps(dict(hiG=s['hiG'],loG=s['loG'],lam=$lam)))")
OUT=/tmp/claude-0/race/runs/lam_c${c}_$lam.pkl ADV="$ADV" python3 /tmp/claude-0/race/simk.py $c 12 18 >/dev/null
python3 -c "
import sys; sys.path.insert(0,'/tmp/claude-0/race'); from chk import run
r=run('/tmp/claude-0/race/runs/lam_c${c}_$lam.pkl'); print('c=$c lam=$lam skew(A-B)', r['skew'], 'ok', r['ok'], 'hz', r['hz'], 'D', r['D'])"
