#!/bin/bash
# twoband.sh MDIR KERNEL BR BC BL P1:I1 P2:I2 -> per-iteration ns at routing BR, CARRY/MUXF BC, LUT BL (scale_net.py)
S=${S:-$(mktemp -d)}
M=$1; K=$2; BR=$3; BC=$4; BL=$5; shift 5
D=$S/tb_$(basename $M)_${BR}_${BC}_${BL}; mkdir -p $D; cp $M/bnd.json $M/simx $D/
python3 /home/user/asyncfpga3/formal/tools-A/board/scale_net.py $M/net.json $D/net.json $BR $BC $BL
python3 /home/user/asyncfpga3/formal/tools/margin/simx_conv.py $D/net.json $D/bnd.json $D/net.simx > /dev/null 2>&1
echo '{"S":[],"F":[]}' > $D/e.json
python3 - "$D" "$K" "$@" <<'PY'
import sys, json, subprocess, os
D, K = sys.argv[1], sys.argv[2]; pts = [(p.split(":")[0], int(p.split(":")[1])) for p in sys.argv[3:]]
B = json.load(open(D + "/bnd.json"))["boundary"]; N = json.load(open(D + "/net.json"))["nodes"]; idx = {n: i for i, n in enumerate(N)}
L = []
sys.path.insert(0, "/home/user/asyncfpga3/formal/tools/margin"); import kernels
for p, it in pts:
    w = ",".join(str(v) for v in kernels.want(K, [p]))
    subprocess.run([D + "/simx", D + "/net.simx", "--maxev", "2000000000", "--want", w, "--pairs", p, "--kernel", K, "--corner", "0", "--kappa", "0",
                    "--classes", D + "/e.json", "--cdefault", "F", "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange", "broad",
                    "--nextreq", "seq", "--tmax", "100000000", "--dump", D + "/d.json"], capture_output=True, env=dict(os.environ, KDEN="100"))
    d = json.load(open(D + "/d.json"))["nodes"]
    L.append((it, (d[str(idx[B["out0_req"]])][1][0] - d[str(idx[B["req"]])][1][0]) / 1000))
(i1, l1), (i2, l2) = L[0], L[-1]
print("%s %s: per-iteration %.2f ns" % (K, os.path.basename(D), (l2 - l1) / (i2 - i1)))
PY
