#!/usr/bin/env bash
# T180: research 5efcd77855 counts digitsum s2 / digitdiv s2 / video_filter s1 as flow v10 PASS, finished locally.
# Own rebuild of the shipped route (it 7) from the farm's saved state (origin/claude/cluster
# results/suite13t_s5a_v10_2a_r1_r2/<task>/auto: sizes_7.vh, seed_7.txt, trim_7.txt), at research 97c98a411e (no flow-code
# diff from the farm's last head 94f40ad2), patched toolchain /root/audit-tc2, flow v10 knobs as lane2 passes them; sdf vs
# the result line; trims by the flow's trim_lines.py --partial, own INIT-only diff; own bitstream / FF scan; own GLS with
# own oracle (t180/oracle_digitsum.py) on own vectors (research's 18 operand pairs + 8 own) at 5 corners.
# gls.sh K TASK SDF: the GLS part of run.sh only (first run hit a full disk: run_baked.vvp truncated)
set -u
A=/home/user/asyncfpga3/audit; RC=97c98a411e; K=$1; TASKN=$2; SDFX=$3; W=/root/wt-t180; L=/root/t180_$K.log; T=${K}_bench_gen; H=v10loc_${K}_s2
TC=/root/audit-tc2; PDB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
CP=results/suite13t_s5a_v10_2a_r1_r2/$TASKN/auto
echo "GLS rerun after disk-full truncation $(date -u)" >> $L
sed -e 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' -e "s#^R=/root/wt-r90#R=$W#" $A/t142/gate.sh > /root/t180_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t180/vec_own.hex
one() { local TG=$1 FLD=$2 C=${3:-0.21} RR=${4:-0.288} X=${5:-1} SC=${6:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 14000 bash /root/t180_gate.sh $K $TG
  python3 $A/t180/oracle_digitsum.py check $V /root/t65/${H}_$TG.log 2 > /root/t90/${H}_${TG}_oracle.txt 2>&1
  echo "$TG: $(grep agreement /root/t90/${H}_${TG}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log); min steer $(grep STEERMON /root/t65/${H}_$TG.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol $(grep LATCHMON /root/t65/${H}_$TG.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$TG/*.json /root/t65/work_${H}_$TG/*.tsv; }
one fastmin min & one advA_ns band 0.20 0.31 1.0 0 & wait
one advC_ns band 0.20 0.20 1.0 0 & one worst band & wait
one slowmax max
echo GLSDONE >> $L
