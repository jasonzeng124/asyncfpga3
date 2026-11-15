#!/usr/bin/env bash
# formal/tools/margin/verify.sh OUT/  (shard C, UNTRUSTED): independent checks of the quiet witness margin.py wrote.
# For OUT/witness/dump_quiet.json(.xz) (the binding race's first quiet failure): shard A's gatecheck_runt.py (every gate
# relation of SpecRunt.GateOKRunt w, every delay inside Spec.Adm at the run's corner and kappa) and shard C's
# envcheck.py (Spec.Env + SeqEnv, the smallest T for ArbOK, out0 liveness). Writes OUT/verify.txt.
set -uo pipefail
O=$(cd "$1" && pwd); H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); W=$O/witness
[ -f "$W/dump_quiet.json" ] || { [ -f "$W/dump_quiet.json.xz" ] && xz -dkf "$W/dump_quiet.json.xz"; }
[ -f "$W/dump_quiet.json" ] || { echo "no quiet witness dump: nothing to verify" | tee "$O/verify.txt"; exit 0; }
cmd=$(grep -- '--dump' "$W/command.txt" | tail -1)
k=$(echo "$cmd" | sed -n 's/.*--kappa \([0-9.]*\).*/\1/p'); c=$(echo "$cmd" | sed -n 's/.*--corner \([0-9.]*\).*/\1/p')
w=$(echo "$cmd" | sed -n 's/.*--w \([0-9]*\).*/\1/p'); w=${w:-0}
pairs=$(echo "$cmd" | python3 -c 'import sys;a=sys.stdin.read().split();i=a.index("--pairs")+1;r=[]
while i < len(a) and not a[i].startswith("--"): r.append(a[i]); i += 1
print(" ".join(r))')
python3 -c "import json,sys;b=json.load(open(sys.argv[1]));b['arbs']=json.load(open(sys.argv[2]));json.dump(b,open(sys.argv[3],'w'))" \
  "$O/bnd.json" "$O/arbs.json" "$O/bnd_arbs.json"
{ echo "# witness: kappa $k corner $c w $w pairs $pairs"
  echo "## gatecheck_runt.py (shard A): every gate relation, every delay in Adm"
  python3 "$F/tools-A/target/gatecheck_runt.py" "$O/net.json" "$O/bnd.json" "$W/dump_quiet.json" "$c" "$k" "$w" "@$W/classes.json" 2>&1 | tail -3
  echo "## envcheck.py (shard C): Env + SeqEnv, ArbOK T, out0"
  python3 "$F/tools/huff/envcheck.py" "$O/net.json" "$O/bnd_arbs.json" "$W/dump_quiet.json" 400000 1000 3000 $pairs 2>&1 | tail -4
} | tee "$O/verify.txt"
