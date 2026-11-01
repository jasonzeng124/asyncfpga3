#!/usr/bin/env bash
# audit T4: the exact commands run (2026-11-01) on formal 88c74e3c (/root/wt-f14, read-only) in /root/t4work.
# Their pipeline = formal/tools-A/target/make_net.sh, run step by step (make_net.sh itself needs XDC/ROUTED env vars).
set -u
W=${W:-/root/t4work}; A=/home/user/asyncfpga3/audit/t4
H=/root/wt-f14/formal/tools-A/target; T=/root/wt-f14/formal/target
export TC=/root/audit-tc          # their scripts read prjxray-db from $TC/openxc7/share/nextpnr/prjxray-db/zynq7
mkdir -p "$W"; cd "$W"
ulimit -v 4500000
# --- their decoder, round trip, boundary, Lean generator
xz -dc $T/gcd_hw_03e82630.fromBit.fasm.xz > fromBit.fasm                       # md5 418f36ae
python3 -B $H/decode_base.py fromBit.fasm $T/gcd_hw_03e82630.xdc --json d0.json 2> decode.log; echo "decode_base exit $?"
python3 -B $H/build_net.py d0.json fromBit.fasm - net.json 2> build.log; echo "build_net exit $?"
python3 -B $H/roundtrip.py net.json fromBit.fasm > roundtrip.txt 2> roundtrip.err; echo "roundtrip exit $?"
xz -dc $T/gcd_hw_03e82630.json.xz > synth.json
xz -dc $T/gcd_hw_03e82630.routed.json.xz > routed.json
python3 -B $H/boundary.py synth.json routed.json net.json bnd.json > boundary.log 2>&1; echo "boundary exit $?"
cmp bnd.json $H/out/boundary_03e82630.json && echo "boundary json IDENTICAL to committed"
python3 -B $H/gen_lean.py net.json bnd.json leannet > genlean.log 2>&1; echo "gen_lean exit $?"
# --- auditor's own checks (no formal/ imports)
python3 -I $A/rt_own.py net.json /root/tgt/own_readback.fasm rt_own > rt_own.txt 2>&1; echo "rt_own exit $?"
python3 -I $A/ctx.py net.json bnd.json /root/tgt/own_readback.fasm routed.json > ctx.txt 2>&1; echo "ctx exit $?"
python3 -I $A/spot.py net.json bnd.json /root/tgt/own_readback.fasm routed.json leannet 30 4 > spot30.txt 2>&1; echo "spot30 exit $?"
python3 -I $A/spot.py net.json bnd.json /root/tgt/own_readback.fasm routed.json leannet 7167 1 > spotall.txt 2>&1; echo "spotall exit $?"
python3 -I $A/muxf.py net.json routed.json > muxf.txt 2>&1; echo "muxf exit $?"
python3 -I $A/widen.py net.json /root/tgt/own_readback.fasm > widen.txt 2>&1; echo "widen exit $?"
python3 -I $A/lean_cmp.py net.json leannet > lean_cmp.txt 2>&1; echo "lean_cmp exit $?"
# determinism: a second decode in another directory gives the same d0.json and the same net.json up to the
# embedded absolute FASM path (net.json's "fasm" field)
mkdir -p rerun && cp fromBit.fasm rerun/
python3 -B $H/decode_base.py rerun/fromBit.fasm $T/gcd_hw_03e82630.xdc --json rerun/d0.json 2>/dev/null
python3 -B $H/build_net.py rerun/d0.json rerun/fromBit.fasm - rerun/net.json 2>/dev/null
md5sum d0.json rerun/d0.json
python3 -I -c "
import json,hashlib
for p in ['net.json','rerun/net.json']:
    j=json.load(open(p)); j['fasm']=''; print(p, hashlib.md5(json.dumps(j).encode()).hexdigest())"
