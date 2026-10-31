#!/bin/bash
# sample.sh BANDS MODE N VEC  -> per sample: answer, ok, per-period signature hash
B=$1; M=$2; N=$3; V=$4
echo "{\"horizon_ps\": 3000000, \"init\": {\"rig_rst\": 1, \"idx\": $V}, \"events\": [{\"t_ps\": 20000, \"set\": {\"rig_rst\": 0}}]}" > /tmp/gcdx/samp_$V.stim.json
for s in $(seq 1 $N); do
  out=$(python3 -I /home/user/asyncfpga3/formal/tools-A/xaudit/gcd/csim.py ${NET:-/tmp/gcdx/d/net.json} $B --stim /tmp/gcdx/samp_$V.stim.json --mode $M --seed $s --watch rig_ok rig_err --strobe rig_lap --bus rig_res_data --stop-after 3 --sig /tmp/gcdx/sig_${V}_${M}_${TAG:-d}${B##*/}_${s}.json)
  res=$(echo "$out" | grep -o "rise #[0-9]*  rig_res_data=0x[0-9a-f]*" | awk '{print $3}' | tr '\n' ' ')
  nerr=$(echo "$out" | grep -c "rig_err = 1")
  nok=$(echo "$out" | grep -c "rig_ok = 1")
  t1=$(echo "$out" | grep "rise #1" | awk '{print $1}')
  sig=$(python3 -c "import json,hashlib;d=json.load(open('/tmp/gcdx/sig_${V}_${M}_${TAG:-d}${B##*/}_${s}.json'));print(hashlib.md5(json.dumps(sorted(d['counts'].items())).encode()).hexdigest()[:8], sum(d['counts'].values()))")
  echo "seed $s lap1 ${t1}ps res [$res] ok_rises $nok err_rises $nerr sig $sig"
done
