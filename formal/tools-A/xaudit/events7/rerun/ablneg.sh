#!/usr/bin/env bash
# E7r: ../abl7.sh and ../neg7.sh with outputs in events7/rerun/ (same certificates, same
# injections; the NEG certificate edits are ../neg7.sh's python block, run from there), and a
# comparison with the committed ../xe7_d_slow_{ABL,NEG}*.txt ([slot] lines stripped).
set -u
R="$(cd "$(dirname "$0")" && pwd)"; E="$R/.."
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events7/out}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
s=d; c=slow
one() { "$E/xe7.sh" "$1" "$2" "$3" 2>&1 | grep -v '^\[slot\]' > "$4"; }
for t in "all3:--no-u3 --no-nary --no-gline" "nou3:--no-u3" "nonary:--no-nary" "nogline:--no-gline"; do
  tag=${t%%:*}; fl=${t#*:}
  python3 "$E/cert7.py" $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_${c}_ABL$tag.json $fl > "$R/cert7_d_slow_ABL$tag.txt" 2>&1
  one $I/$s/skel.json $I/$s/skel_$c.bands.json $O/$s/cert_${c}_ABL$tag.json "$R/xe7_d_slow_ABL$tag.txt" &
done
wait
# negative controls: the certificate edits exactly as ../neg7.sh (its python block, extracted)
python3 "$E/../events4/negctl.py" $I/$s/skel_slow.bands.json $O/$s/skel_slow_NEGfb.bands.json fb
python3 "$E/cert7.py" $I/$s/skel.json $O/$s/skel_slow_NEGfb.bands.json $O/$s/cert_NEGfb.json > /dev/null
sed -n "/^python3 - \$O\/\$s\/cert_slow.json \$O\/\$s <<'PY'/,/^PY$/p" "$E/neg7.sh" | sed '1d;$d' > /tmp/events7/negedit.py
python3 /tmp/events7/negedit.py $O/$s/cert_slow.json $O/$s
one $I/$s/skel.json $O/$s/skel_slow_NEGfb.bands.json $O/$s/cert_NEGfb.json "$R/xe7_d_slow_NEGfb.txt" &
for f in NEGu3 NEGnary NEGnarx NEGgline NEGcasc; do
  one $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_$f.json "$R/xe7_d_slow_$f.txt" &
  while [ "$(jobs -rp | wc -l)" -ge 3 ]; do sleep 1; done
done
wait
for f in ABLall3 ABLnou3 ABLnonary ABLnogline NEGfb NEGu3 NEGnary NEGnarx NEGgline NEGcasc; do
  if cmp -s "$R/xe7_d_slow_$f.txt" "$E/xe7_d_slow_$f.txt"; then st=IDENTICAL; else st=DIFFERS; fi
  echo "$f: $st | $(grep -c 'RESIDUAL Back' $R/xe7_d_slow_$f.txt) Back, $(grep -c 'RESIDUAL Excl' $R/xe7_d_slow_$f.txt) Excl, $(grep -c 'RESIDUAL Line' $R/xe7_d_slow_$f.txt) Line | $(tail -1 $R/xe7_d_slow_$f.txt | cut -c1-40)"
done
