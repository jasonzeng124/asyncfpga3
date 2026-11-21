END=$(( $(date +%s) + 12*3600 ))
KEEP="exit1_varshift_1 exit1_brhash_2 exit1_brhash_4 exit1_quadrec_3 exit1_twoloops_2 exit1_fold64_1 exit1_xorshift_1"
while [ $(date +%s) -lt $END ]; do
  cd /home/user/b/suite13t
  for n in */; do n=${n%/}
    grep -q "^$n " ../xtol13.txt 2>/dev/null && grep -q "^$n " ../outsafe13.txt 2>/dev/null || continue
    case "$n" in xorshift_1|brhash_1|ipow_1) continue;; esac     # cited in B25 / B28
    rm -rf $n/hw0 $n/t/hw $n/u/w $n/t/j/w $n/u/d1* $n/t/j/d1* 2>/dev/null
  done
  cd /home/user/b
  for d in exit1_*_[0-9]; do echo " $KEEP " | grep -q " $d " && continue; grep -q "^$d " xtol.txt ctlall.txt 2>/dev/null || continue; rm -rf $d/w $d/d1* 2>/dev/null; done
  sleep 900
done
