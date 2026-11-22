#!/bin/bash
# kdc/run.sh: per v10 search structure, the links it would make shallower than the base structure (AUTO_SEARCH_KEEPDEPTH's pins)
cd /tmp/bot/repo
while IFS=$'\t' read -r k s envs rw; do
  W=/tmp/bot/kdc/$k; mkdir -p $W
  FX=build/frontend/$k/comp/handshake_transformed.mlir
  im=$(md5sum < $FX | cut -c1-32); row=$(awk -F'\t' -v m="$im" '$1 == m' research/data/autorw/cache.tsv | head -1)
  of=$(echo "$row" | cut -f4); [ -n "$of" ] && [ "$(echo "$row" | cut -f3)" != none ] && FX=$of
  if [ ! -f $W/base.v ]; then
    python3 bdc/auto.py $FX $W/auto.mlir > $W/log 2>&1 && BDC_AUTO=1 BDC_AUTO_REWRITES=0 python3 bdc/emit.py $W/auto.mlir --no-top -o $W/base.v >> $W/log 2>&1
  fi
  env $envs BDC_AUTO=1 BDC_AUTO_REWRITES=0 python3 bdc/emit.py $W/auto.mlir --no-top -o $W/s$s.v >> $W/log 2>&1 || { echo -e "$k\t$s\tEMIT-FAILED"; continue; }
  out=$(python3 /tmp/bot/qr/kd.py $W/base.v $W/s$s.v "$envs" | cut -f2)
  echo -e "$k\t$s\t${out:-none}\t$envs"
done < /tmp/bot/kdc/list.tsv
