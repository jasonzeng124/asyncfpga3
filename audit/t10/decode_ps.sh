#!/usr/bin/env bash
# T10: shard A's decoder (formal b9f69327, git archive in /root/t10/fx, read-only) run by the auditor on the
# auditor's OWN read-back of the target bit (/root/t10/fromBit.fasm, md5 740cc6bf = committed), then own checks.
set -u
W=/root/t10/dec; H=/root/t10/fx/formal/tools-A/target; T=/root/t10/fx/formal/target; A=/home/user/asyncfpga3/audit
export TC=/root/audit-tc
mkdir -p $W; cd $W; ulimit -v 4500000
cp /root/t10/fromBit.fasm fromBit.fasm
python3 -B $H/decode_base.py fromBit.fasm $T/gcd_ps_e6bb4aec.xdc --json d0.json 2> decode.log; echo "decode_base exit $?"
python3 -B $H/build_net.py d0.json fromBit.fasm - net.json 2> build.log; echo "build_net exit $?"
python3 -I -c "
import json,hashlib; j=json.load(open('net.json')); print('nodes',len(j['nodes']),'gates',len(j['gates'])); j['fasm']=''; print('net md5 (fasm field blanked)', hashlib.md5(json.dumps(j).encode()).hexdigest())"
md5sum net.json
xz -dc $T/gcd_ps_e6bb4aec.json.xz > synth.json; xz -dc $T/gcd_ps_e6bb4aec.routed.json.xz > routed.json
python3 -B $H/boundary_ps.py synth.json routed.json net.json bnd.json > boundary.log 2>&1; echo "boundary exit $?"
cmp bnd.json $H/out/boundary_e6bb4aec.json && echo "boundary json IDENTICAL to committed"
python3 -I $A/t4/rt_own.py net.json /root/t10/fromBit.fasm rt_own > rt_own.txt 2>&1; echo "rt_own exit $?"
echo DECODE_DONE
