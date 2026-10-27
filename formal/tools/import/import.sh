#!/usr/bin/env bash
# Import the library cells into Lean from the project's own yosys flow.
#
#   formal/tools/import/import.sh            # synthesize, write JSON + Lean
#   formal/tools/import/import.sh --check    # drift check: re-synthesize into a
#                                            # temp dir, regenerate, and FAIL
#                                            # (exit 1) if the Lean differs from
#                                            # the committed file
#   formal/tools/import/import.sh --check-json
#                                            # same, from the committed JSON
#                                            # only (no yosys needed); checks
#                                            # the generator, not synthesis
#
# Synthesis is exactly cells/flow.sh's / cells/verify/lutcost.py's:
#   read_verilog -lib -specify cells_sim.v ; read_verilog cells/rtl/*.v ;
#   synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top T
# (flow.sh adds -nodsp only with BD_DSP=0; irrelevant for LUT-only cells).
# Exit 2 if yosys is not where TC says.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"
TC="${TC:-$HOME/dev2/lib/fpgatoolchain}"
YOSYS="$TC/openxc7/bin/yosys"
CELLS_SIM="$TC/openxc7/share/yosys/xilinx/cells_sim.v"
LEAN_OUT="$REPO/formal/lean/Formal/Net/Import/Cells.lean"
JSON_DIR="$HERE/json"
MODE="${1:-write}"

# name  top  [param=value ...]
TARGETS=(
  "bd_c2 bd_c2"
  "bd_c2_set bd_c2_set"
  "bd_c2n bd_c2n"
  "bd_c2n_set bd_c2n_set"
  "bd_c3 bd_c3"
  "bd_c4 bd_c4"
  "bd_latch_W2 bd_latch W=2"
  "bd_latch_W3 bd_latch W=3"
  "bd_latch_rst_W1 bd_latch_rst W=1"
  "bd_arbcell bd_arbcell"
  "bd_arbiter bd_arbiter"
)

script_for() {  # top [W=..]
  local top=$1; shift
  echo "read_verilog -lib -specify \$TC/openxc7/share/yosys/xilinx/cells_sim.v"
  echo "read_verilog cells/rtl/*.v"
  echo "chparam -set <param> <value> $top    (parameterized cells only, see TARGETS)"
  echo "synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top $top"
  echo "write_json <name>.json"
}

synth_all() {  # outdir
  local out=$1
  [ -x "$YOSYS" ] || { echo "import.sh: yosys not found at $YOSYS; set TC=" >&2; exit 2; }
  local ver; ver=$("$YOSYS" -V)
  echo "[import] $ver ($YOSYS)" >&2
  for t in "${TARGETS[@]}"; do
    set -- $t; local name=$1 top=$2; shift 2
    local cp=""
    for kv in "$@"; do cp+="chparam -set ${kv%%=*} ${kv#*=} $top; "; done
    ( cd "$REPO/cells" && "$YOSYS" -q -l "$out/$name.log" -p "
read_verilog -lib -specify $CELLS_SIM
read_verilog rtl/*.v
$cp
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top $top
write_json $out/$name.json" >/dev/null ) || { echo "import.sh: SYNTH FAILED for $name (log $out/$name.log)" >&2; exit 1; }
  done
}

generate() {  # jsondir outlean
  local jd=$1 out=$2 files=() t
  for t in "${TARGETS[@]}"; do set -- $t; files+=("$jd/$1.json"); done
  YOSYS2LEAN_SCRIPT="$(script_for '<top>')" \
    python3 -I "$HERE/yosys2lean.py" "$out" "${files[@]}"
}

case "$MODE" in
  write)
    mkdir -p "$JSON_DIR"
    synth_all "$JSON_DIR"
    rm -f "$JSON_DIR"/*.log
    generate "$JSON_DIR" "$LEAN_OUT"
    echo "[import] wrote $LEAN_OUT and $JSON_DIR/*.json" ;;
  --check|--check-json)
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    if [ "$MODE" = --check ]; then synth_all "$tmp"; jd=$tmp; else jd=$JSON_DIR; fi
    generate "$jd" "$tmp/Cells.lean"
    if ! diff -u "$LEAN_OUT" "$tmp/Cells.lean"; then
      echo "import.sh: DRIFT: regenerated Lean differs from $LEAN_OUT" >&2
      echo "import.sh: the proofs in Formal/Net/Import/ are about the committed netlist, not this one." >&2
      exit 1
    fi
    echo "[import] no drift ($MODE): $LEAN_OUT matches a fresh import" ;;
  *) echo "usage: $0 [--check|--check-json]" >&2; exit 2 ;;
esac
