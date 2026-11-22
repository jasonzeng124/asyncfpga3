#!/usr/bin/env bash
# T182 split-band replay of formal B36's race (ucond_br14 latch-fed steer, test_flatten_array s2):
# condition side (the link's data latch ulink_n101_folink.lat.*: G->Q IOPATH + wires into it) at band CB,
# request side (ulink_n101_folink.rdly chain + the steer's join ucond_br14_j) at band RB; everything else as the
# 'band' corner (chains 0.21, rest 0.288, CARRY4/F7F8/FF 1), no scatter.  usage: split.sh HALF TAG CB RB
set -u
HALF=$1; TG=$2; CB=$3; RB=$4; A=/home/user/asyncfpga3/audit; K=test_flatten_array; H=t182_$HALF
export RWT=/root/wt-t182-$HALF; RJ=/root/t65/$H/${K}_bench_gen_routed.json; E=/root/t65/${H}_${TG}_extra.band
python3 $RWT/research/tools/band_inst_list.py $RJ 'udut\.ulink_n101_folink\.lat\.' $CB $E.c
python3 $RWT/research/tools/band_inst_list.py $RJ 'udut\.(ulink_n101_folink\.rdly\.|ucond_br14_j\.)' $RB $E.r
cat $E.c $E.r > $E; cp $E $A/t182/${HALF}_${TG}_extra.band
export PS_MON_GEN=$A/t104/mon_both1.py; V=$A/t182/vec_own.hex
HWD=$H EXTRA_BAND=$E GLS_SDF_FIELD=band VECF=$V BAND_CHAIN=0.21 BAND_REST=0.288 BAND_CELLX=1 SCAT=0 TBATCH=4000000 timeout 20000 bash $A/t182/gate_split.sh $K $TG
python3 $A/t182/vec_oracle.py check $V /root/t65/${H}_$TG.log > $A/t182/${H}_${TG}_oracle.txt 2>&1
echo "$HALF $TG cond=$CB req=$RB: $(grep agreement $A/t182/${H}_${TG}_oracle.txt); hang $(grep -c HANG /root/t65/${H}_$TG.log); br14 min margin $(grep STEERMON /root/t65/${H}_$TG.log | grep 'ucond_br14 ' | sed 's/.*min_rise_margin_ps=\([0-9-]*\).*/\1/' | sort -n | head -1); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$TG.log)" >> $A/t182/split.log
grep 'GLS_SDF_BAND_INST' /root/t65/${H}_$TG.log | head -2 >> $A/t182/split.log
