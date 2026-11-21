#!/usr/bin/env bash
# Probe C-11f: turn a mutant's generated chunk into a Wip negative-control file that
# states the check FAILS (decide), against the unmutated route's renaming (the
# mutations used here leave Rho.lean unchanged; mkmut checks that).
#   mkmut.sh KIND CHUNK   (KIND in init pips ffinit clkinv; CHUNK e.g. C000)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$(cd "$HERE/../../lean" && pwd)
k=$1; c=$2; M=$HERE/build/mut/lean_$k; N=Mut$(echo ${k^})
diff <(sed -E 's/GcdDMut[A-Za-z]*/GcdD/g; s/Physical side: [^ ]+/P/' "$M/Rho.lean") \
     <(sed -E 's/Physical side: [^ ]+/P/' "$LEAN/Formal/Net/FasmDesign/GcdD/Rho.lean") > /dev/null \
  || { echo "mkmut: $k changes the renaming; not handled"; exit 1; }
mkdir -p "$LEAN/Wip/C11f"
python3 - "$M/$c.lean" "$LEAN/Wip/C11f/$N.lean" "$c" "$N" <<'PY'
import re, sys
src, dst, c, n = sys.argv[1:]
t = open(src).read()
t = re.sub(r"^import Formal\.Net\.FasmDesign\.GcdDMut[A-Za-z]*\.Rho", "import Formal.Net.FasmDesign.GcdD.Rho", t, flags=re.M)
t = re.sub(r"Formal\.Net\.FasmDesign\.GcdDMut[A-Za-z]*\.%s\b" % c, "Formal.Net.FasmDesign.GcdD.%s" % n, t)
# keep the data, replace every theorem (and the bindings) by the one negative statement
head = t[:t.index("theorem ok0 ")]
tail = t[t.index("end Formal.Net.FasmDesign.GcdD.%s" % n):]
open(dst, "w").write(head + "/-- Negative control: the mutated chunk FAILS the check. -/\n"
                     "theorem caught : checkAll rho insts = false := by decide +kernel\n\n" + tail)
PY
echo "wrote Wip/C11f/$N.lean"
