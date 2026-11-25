#!/usr/bin/env bash
# Shard C: GLS of the TARGET route (formal/target/gcd_hw_03e82630: nextpnr routed JSON + SDF) under
# a pipelined environment at the kernel boundary (tb_pipe.v), with research's cells/gls generators
# (read-only; nothing is written under cells/).
#
#   formal/tools/pipe/gls/run.sh WORKDIR [vvp plusargs...]     e.g. +PIPE=1 +V1=9 +V2=4
#
# Needs iverilog 12 (apt-get install iverilog). The generated netlist is ~1 GB in WORKDIR.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../../../.." && pwd)
W=${1:?workdir}; shift
mkdir -p "$W"; cd "$W"
if [ ! -f pipe_baked.vvp ]; then
  xz -dc "$ROOT/formal/target/gcd_hw_03e82630.routed.json.xz" > routed.json
  xz -dc "$ROOT/formal/target/gcd_hw_03e82630.sdf.xz" > routed.sdf
  echo "routed.sdf md5 $(md5sum < routed.sdf | cut -d' ' -f1) (target README: 6f8b99e6c49bb7ef8855c881cecabe5c)"
  export GLS_WORK=$W
  python3 "$ROOT/cells/gls/gen.py"
  python3 "$ROOT/cells/gls/gen_probe.py" urig.
  python3 "$ROOT/cells/gls/gen_chan.py"
  python3 "$ROOT/cells/gls/gen_signals.py"
  grep -q '^n144588 urig.in_ack$' nets.map || { echo "in_ack is not n144588 on this route: fix tb_pipe.v"; exit 1; }
  iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o pipe_baked.vvp "$ROOT/formal/tools/pipe/gls/tb_pipe.v" \
    netlist_baked.v "$ROOT/cells/gls/prims.v" 2>&1 | grep -v 'procedural continuous' || true
fi
vvp pipe_baked.vvp "$@" | grep -v '^# t=.*\(in_ack\|env_c\)='
