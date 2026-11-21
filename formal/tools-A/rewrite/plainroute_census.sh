#!/bin/bash
# census: ring_dec_route.py (applied repeatedly, one test per pass) + tv_gate.sh on every research fixture
RS=/tmp/claude-0/rs; T=/home/user/asyncfpga3/formal/tools-A/rewrite; W=/tmp/claude-0/rrc; mkdir -p $W
export BDC_AUTO=1 PATH=$HOME/.elan/bin:$PATH
out=$W/census.tsv; : > $out
for d in $RS/cloud/fixtures/frontend/*/; do
  k=$(basename $d); f=$d/comp/handshake_transformed.mlir; [ -f $f ] || continue
  fm=$(md5sum < $f | cut -c1-32); cur=$f; n=0; msgs=""
  for p in 1 2 3 4; do
    o=$W/$k.p$p.mlir; m=$(python3 $T/ring_dec_route.py $cur $o 2>&1); rc=$?
    msgs="$msgs $(echo "$m" | tr '\n' '|')"
    [ $rc = 0 ] || break
    cur=$o; n=$((n+1))
  done
  if [ $n = 0 ]; then
    r=$(echo "$msgs" | grep -o "refused [^|]*" | head -3 | tr '\n' ';'); printf "%s\t%s\tno edit\t%s\t-\n" "$fm" "$k" "${r:-no candidate test}" >> $out; continue
  fi
  om=$(md5sum < $cur | cut -c1-32); cp $cur $W/$k.final.mlir
  g=$(timeout 3600 $T/tv_gate.sh $RS $k $cur $W/tv_$k 2>&1 | tail -1)
  if echo "$g" | grep -q PROVED; then st="PROVED"; else st="not proved"; fi
  printf "%s\t%s\t%s (%d edit(s))\t%s\t%s\n" "$fm" "$k" "$st" "$n" "$(echo "$g" | cut -c1-120)" "$om" >> $out
done
echo DONE >> $out
