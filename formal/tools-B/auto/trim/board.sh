P=/home/user/asyncfpga3/formal/tools-B/auto; RS=/home/user/rsb; cd /home/user/b
while read K S SZ M EV; do O=/home/user/b/board_${K}_$S; rm -rf $O
  env $EV RS=$RS JOBS=1 bash $P/suite/task.sh $K $S /home/user/rs/research/data/suite/board/$SZ $M $O 2 > /dev/null 2>&1
  echo "$K s$S $(grep -o 'sdf [0-9a-f]* ([^)]*) [A-Z]*' $O/summary.txt) $(grep -o 'PASS [0-9]* FAIL [0-9]*' $O/summary.txt | tr '\n' ' ') | $(timeout 2400 python3 $P/steersafe.py $O/w/m --auto 2>&1 | tee $O/steersafe.txt | grep -o '^steers.*')" >> board.txt
  bash $P/ctlsweep.sh $O $K >> board.txt 2>&1
done <<'L'
xorshift 8 xorshift_v3_s8_sizes.vh 3497ca67 BDC_AUTO_REWRITES=1 BDC_RING_FUSE=0
collatz 6 collatz_v3_s6_sizes.vh c56def07 BDC_AUTO_REWRITES=1 BDC_RING_FUSE=0
ipow 2 ipow_v3_s2_sizes.vh 81bbe268 BDC_RING_FUSE=0
collatz64 5 collatz64_v3_s5_sizes.vh 9585dde4 BDC_AUTO_REWRITES=1 BDC_RING_FUSE=0
L
