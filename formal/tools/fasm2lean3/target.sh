#!/usr/bin/env bash
# C-11g on THE TARGET (formal/target/gcd_hw_03e82630): decode the read-back FASM and nextpnr's FASM,
# compare, pair with the target's yosys netlist (gen3, namespace GcdT), check3, rhoinj; then write the
# generated Lean into formal/lean (Formal/Net/FasmDesign/GcdT/*, Formal/Net/FasmRhoT*.lean).
# Needs prjxray-db ($TC, e.g. via cloud/toolchain-cache.sh fetch).   formal/tools/fasm2lean3/target.sh WORKDIR
set -euo pipefail
H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); W=${1:?workdir}; mkdir -p "$W"
X=$F/target/gcd_hw_03e82630
xz -dc $X.fromBit.fasm.xz > $W/fb.fasm; xz -dc $X.fasm.xz > $W/n.fasm
xz -dc $X.json.xz > $W/s.json; xz -dc $X.routed.json.xz > $W/r.json
python3 $H/fasm2lean3.py $W/fb.fasm $X.xdc --json $W/phys.json > $W/x.log
python3 $H/fasm2lean3.py $W/n.fasm $X.xdc --json $W/physn.json > $W/y.log
python3 - $W/phys.json $W/physn.json <<'PY'
import json, sys
a, b = (json.load(open(f)) for f in sys.argv[1:])
key = lambda r: (sorted((c["name"], c["kind"], c["init"], sorted((k, json.dumps(v, sort_keys=True)) for k, v in c["conn"].items()), c["inv"]) for c in r["cells"]), sorted(r["outputs"].items()))
print("same physical netlist from .bit and nextpnr FASM:", key(a) == key(b)); sys.exit(0 if key(a) == key(b) else 1)
PY
python3 $H/gen3.py $W/phys.json $W/s.json $W/r.json $W/lean_t GcdT --report $W/report.json | grep '^gen3: [0-9]'
python3 $H/check3.py $W/lean_t | tail -1
mkdir -p $W/rho_t; python3 $H/rhoinj.py $W/lean_t GcdT $W/rho_t
if [ "${WRITE:-0}" = 1 ]; then
  mkdir -p $F/lean/Formal/Net/FasmDesign/GcdT; cp $W/lean_t/*.lean $F/lean/Formal/Net/FasmDesign/GcdT/; cp $W/rho_t/*.lean $F/lean/Formal/Net/
fi
