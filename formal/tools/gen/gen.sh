#!/usr/bin/env bash
# formal/tools/gen/gen.sh -- import EVERY module of cells/rtl/*.v into Lean.
#
#   formal/tools/gen/gen.sh            synthesize every target of targets.txt
#                                      (and test/prims.v), write json/*.json and
#                                      formal/lean/Formal/Gen/Cells.lean
#   formal/tools/gen/gen.sh --check    drift check: re-synthesize into a temp
#                                      dir, regenerate, FAIL (exit 1) if the
#                                      JSON or the Lean differs from what is
#                                      committed, or if yosys lists a module of
#                                      cells/rtl/ that no target imports
#   formal/tools/gen/gen.sh --check-json
#                                      regenerate the Lean from the committed
#                                      JSON only (no yosys); checks the generator
#
# Synthesis per target is cells/flow.sh's, out of context:
#   read_verilog -lib -specify cells_sim.v
#   read_verilog [-DDEF] cells/rtl/*.v
#   chparam -set P V <top>                      (parameterized targets)
#   synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -noiopad -top <top>
#   write_json
# -noiopad is the one difference from flow.sh: a library cell is never a top
# level, so the IBUF/OBUF pads synth_xilinx would add do not exist in any real
# design (11a imported them and modelled them as identity; here they are gone).
# Exit 2 if yosys is not found.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"
TC="${TC:-$HOME/dev2/lib/fpgatoolchain}"
YOSYS="${YOSYS:-$TC/openxc7/bin/yosys}"
CELLS_SIM="$TC/openxc7/share/yosys/xilinx/cells_sim.v"
LEAN_OUT="$REPO/formal/lean/Formal/Gen/Cells.lean"
JSON_DIR="$HERE/json"
MODE="${1:-write}"
JOBS="${JOBS:-4}"

targets() { grep -v '^\s*#' "$HERE/targets.txt" | grep -v '^\s*$'; }

need_yosys() {
  [ -x "$YOSYS" ] || { echo "gen.sh: yosys not found at $YOSYS; set TC= or YOSYS=" >&2; exit 2; }
}

# synth_one OUTDIR NAME TOP [P=V ...] [+DEF ...]
synth_one() {
  local out=$1 name=$2 top=$3; shift 3
  local cp="" defs="" src kv
  for kv in "$@"; do
    case "$kv" in
      +*) defs+=" -D${kv#+}" ;;
      *=*) cp+="chparam -set ${kv%%=*} ${kv#*=} $top; " ;;
      *) echo "gen.sh: bad target token '$kv' for $name" >&2; return 1 ;;
    esac
  done
  case "$top" in prims_*) src="$HERE/test/prims.v" ;; *) src="rtl/*.v" ;; esac
  ( cd "$REPO/cells" && "$YOSYS" -q -l "$out/$name.log" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog$defs $src
$cp
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -noiopad -top $top
write_json $out/$name.json" >/dev/null ) || { echo "gen.sh: SYNTH FAILED for $name (log $out/$name.log)" >&2; return 1; }
  # Keep only the synthesized top module (write_json also dumps the ~420
  # blackbox primitive declarations of cells_sim.v), and record the target.
  python3 -I - "$out/$name.json" "$name $top $*" <<'PY'
import json, sys
p, tgt = sys.argv[1], sys.argv[2]
d = json.load(open(p))
d["modules"] = {n: m for n, m in d["modules"].items()
                if str(m.get("attributes", {}).get("top", "0")).strip("0")}
d["target"] = tgt
json.dump(d, open(p, "w"), indent=1)
PY
  rm -f "$out/$name.log"
}

synth_all() {  # outdir
  local out=$1
  need_yosys
  echo "[gen] $("$YOSYS" -V) ($YOSYS)" >&2
  local line fail=0 pids=()
  while read -r line; do
    # shellcheck disable=SC2086
    synth_one "$out" $line &
    pids+=($!)
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 0.2; done
  done < <(targets)
  for p in "${pids[@]}"; do wait "$p" || fail=1; done
  [ "$fail" = 0 ] || { echo "gen.sh: synthesis failed (see above)" >&2; exit 1; }
}

# Every module yosys sees in cells/rtl must be the top of some target.
check_coverage() {
  need_yosys
  local mods tops missing=0 m
  mods=$(cd "$REPO/cells" && "$YOSYS" -p "read_verilog rtl/*.v; ls" 2>/dev/null |
         sed -n '/modules:/,/^$/p' | grep '^  ' | awk '{print $1}' | sort -u)
  tops=$(targets | awk '{print $2}' | sort -u)
  for m in $mods; do
    grep -qx "$m" <<<"$tops" || { echo "gen.sh: module $m of cells/rtl is not imported by any target" >&2; missing=1; }
  done
  [ "$missing" = 0 ] && echo "[gen] coverage: all $(wc -w <<<"$mods") modules of cells/rtl/*.v have a target" >&2
  return $missing
}

generate() {  # jsondir outlean
  local jd=$1 out=$2 files=() n
  for n in $(targets | awk '{print $1}'); do files+=("$jd/$n.json"); done
  python3 -I "$HERE/yosys2lean.py" "$out" "${files[@]}"
}

case "$MODE" in
  write)
    mkdir -p "$JSON_DIR"
    rm -f "$JSON_DIR"/*.json
    synth_all "$JSON_DIR"
    check_coverage
    generate "$JSON_DIR" "$LEAN_OUT"
    echo "[gen] wrote $LEAN_OUT and $JSON_DIR/*.json" ;;
  --check|--check-json)
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    rc=0
    if [ "$MODE" = --check ]; then
      check_coverage || rc=1
      synth_all "$tmp"; jd=$tmp
      if ! diff -r -q "$JSON_DIR" "$tmp" --exclude=Cells.lean >/dev/null; then
        diff -r -q "$JSON_DIR" "$tmp" --exclude=Cells.lean || true
        echo "gen.sh: DRIFT: yosys output differs from the committed json/" >&2; rc=1
      fi
    else jd=$JSON_DIR; fi
    generate "$jd" "$tmp/Cells.lean"
    if ! diff -u "$LEAN_OUT" "$tmp/Cells.lean"; then
      echo "gen.sh: DRIFT: regenerated Lean differs from $LEAN_OUT" >&2
      echo "gen.sh: the proofs in Formal/Gen/ are about the committed netlists, not these." >&2
      rc=1
    fi
    [ "$rc" = 0 ] && echo "[gen] no drift ($MODE)"
    exit $rc ;;
  --synth-only)   # debugging: gen.sh --synth-only DIR
    mkdir -p "$2"; synth_all "$2" ;;
  *) echo "usage: $0 [--check|--check-json]" >&2; exit 2 ;;
esac
