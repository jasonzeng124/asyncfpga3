#!/usr/bin/env bash
# All sixteen vectors of a build_fid.sh (or any gls) work dir.
#     cells/gls/fid/run_fid.sh WORK [-j N]       env TEND, QUIET as cells/gls/run.sh
set -euo pipefail
WORK=$(cd "$1" && pwd); shift
PAR=2
while [ $# -gt 0 ]; do [ "$1" = "-j" ] && { PAR=$2; shift 2; continue; }; shift; done
TEND=${TEND:-150000}; QUIET=${QUIET:-200000}
cd "$WORK"; mkdir -p sweep
echo "== provenance =="; cat provenance.txt; echo "TEND=${TEND} ns  QUIET=${QUIET} ns  -j${PAR}"
for v in $(seq 0 15); do
    while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do sleep 2; done
    ( vvp run_baked.vvp "+VEC=$v" "+TEND=$TEND" "+QUIET=$QUIET" > "sweep/v$v.log" 2>&1 ) &
done
wait
echo "== result =="
for v in $(seq 0 15); do
    printf "  vector %2d  %s\n" "$v" "$(grep -m1 -E 'RESULT' "sweep/v$v.log" || echo 'no verdict line')"
done
