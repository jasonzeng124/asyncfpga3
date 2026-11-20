#!/usr/bin/env bash
# T172 part 2: trimmed lfsrfind s1 -- research's trimmed FASM (md5 checked) -> own bitstream; own GLS (fid model, own
# prjxray SDF, GLS tools of the route's own commit dbf7af1fa), own oracle (oracle_lfsrfind.py, own 22 vectors incl. 0,
# 254, 255, 256 trips), own steer / latch monitors; trimmed at FAST_MIN, advA (chains 0.20, rest 0.31, CARRY 1.0) no
# scatter, worst (+scatter), SLOW_MAX; untrimmed at advA no scatter as the control.
set -u
A=/home/user/asyncfpga3/audit; W=/root/wt-t172; L=/root/t172.log; K=lfsrfind; D=$W/cells/build/hw/${K}_bench_gen; T=${K}_bench_gen
FF=$W/research/data/for-formal/trim_lfsrfind_s1
TC=/root/audit-tc2; PDB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
for H in trim_lfs_u trim_lfs_t; do rm -rf /root/t65/$H; mkdir -p /root/t65/$H; cp $D/$T.sdf $D/${T}_routed.json /root/t65/$H/; done
cp $D/$T.bit $D/$T.fasm /root/t65/trim_lfs_u/
xz -dc $FF/$T.trimmed.fasm.xz > /root/t65/trim_lfs_t/$T.fasm; xz -dc $FF/$T.untrimmed.fasm.xz > /root/t172_untrimmed_research.fasm
echo "research trimmed fasm $(md5sum < /root/t65/trim_lfs_t/$T.fasm | cut -c1-8) (md5.txt 8caf765e); research untrimmed $(md5sum < /root/t172_untrimmed_research.fasm | cut -c1-8) (a00bfe63); own fasm $(md5sum < $D/$T.fasm | cut -c1-8)" >> $L
echo "trimmed vs own untrimmed fasm, differing lines: $(diff <(sort $D/$T.fasm) <(sort /root/t65/trim_lfs_t/$T.fasm) | grep -c '^[<>]'), non-INIT: $(diff <(sort $D/$T.fasm) <(sort /root/t65/trim_lfs_t/$T.fasm) | grep '^[<>]' | grep -vc 'INIT')" >> $L
PYTHONPATH=$TC/openxc7-src/prjxray:$TC/openxc7/lib/python python3 $TC/openxc7-src/prjxray/utils/fasm2frames.py --db-root $PDB --part $PART /root/t65/trim_lfs_t/$T.fasm > /root/t172.frames 2>/root/t172_frames.log
$TC/openxc7/bin/xc7frames2bit --part_file $PDB/$PART/part.yaml --part_name $PART --frm_file /root/t172.frames --output_file /root/t65/trim_lfs_t/$T.bit > /root/t172_bit.log 2>&1
echo "trimmed bit $(ls -la /root/t65/trim_lfs_t/$T.bit | awk '{print $5}') bytes" >> $L
python3 $A/t67/scan_ff_own.py /root/t65/trim_lfs_t/$T.fasm > /root/t172_ff.txt 2>&1; echo "ff (trimmed): $(tail -1 /root/t172_ff.txt | sed 's/.*flops/flops/')" >> $L
sed -e 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' -e 's#^R=/root/wt-r90#R=/root/wt-t172#' $A/t142/gate.sh > /root/t172_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t172/lfs_own.hex
one() { local H=$1 TG=$2 FLD=$3 C=${4:-0.21} RR=${5:-0.288} X=${6:-1} SC=${7:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 9000 bash /root/t172_gate.sh $K $TG
  python3 $A/t172/oracle_lfsrfind.py check $V /root/t65/${H}_$TG.log 2 > /root/t90/${H}_${TG}_oracle.txt 2>&1
  echo "$H $TG: $(grep agreement /root/t90/${H}_${TG}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log); min steer $(grep STEERMON /root/t65/${H}_$TG.log | grep -v VIOLATION | sed 's/.*udut.\(ucond_br[0-9]*\).*min_rise_margin_ps=\([0-9-]*\).*/\2 \1/' | sort -n | head -1); latch viol $(grep LATCHMON /root/t65/${H}_$TG.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$TG/*.json /root/t65/work_${H}_$TG/*.tsv; }
one trim_lfs_t fastmin min & one trim_lfs_t advA_ns band 0.20 0.31 1.0 0 & wait
one trim_lfs_t worst band & one trim_lfs_u advA_ns band 0.20 0.31 1.0 0 & wait
one trim_lfs_t slowmax max
echo GLSDONE >> $L
