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
sed -E "s/^import Formal\.Net\.FasmDesign\.GcdDMut[A-Za-z]*\.Rho/import Formal.Net.FasmDesign.GcdD.Rho/;
        s/namespace Formal\.Net\.FasmDesign\.GcdDMut[A-Za-z]*\.$c/namespace Formal.Net.FasmDesign.GcdD.$N/;
        s/end Formal\.Net\.FasmDesign\.GcdDMut[A-Za-z]*\.$c/end Formal.Net.FasmDesign.GcdD.$N/;
        s/^theorem ok : checkAll rho insts = true/theorem caught : checkAll rho insts = false/;
        /^\/-- H_CELLS/d; /^def binds/d; /^theorem binds_ok/d" "$M/$c.lean" > "$LEAN/Wip/C11f/$N.lean"
echo "wrote Wip/C11f/$N.lean"
