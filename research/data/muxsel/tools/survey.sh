#!/usr/bin/env bash
# survey.sh REPO OUT NAME=ROUTE_CA_DIR... -- rule E's bdc_muxnN rows (BD_SKEW_MUXN=1) on each route, at the two corners
# auto_size.sh's rule() uses (0.20 / 0.31: --band C, chains at 0.20), report only (--no-size), in auto_size.sh's
# environment (ca_run.sh).  ROUTE_CA_DIR holds seed1/pnr/{soak_xray.sdf, soak_routed.json, sizes.vh} (an auto_size.sh
# $RUNS/ca/NAME_I directory).  Writes OUT/NAME_C/ (corner_audit's outputs) and appends to OUT/rows.tsv one line per
# decode LUT: name corner mux decode_lut guarded raw t_req t_sel launch, and to OUT/lines.tsv the select links' sizes.
R=$1; O=$2; shift 2; mkdir -p "$O"; T=$(dirname "$0")
for nr in "$@"; do
  n=${nr%%=*}; rd=${nr#*=}
  for c in ${SURVEY_CORNERS:-0.20 0.31}; do
    [ -f "$O/${n}_$c/report.txt" ] || BD_SKEW_MUXN=1 bash "$T/ca_run.sh" "$R" "$rd/seed1" "$c" "$O/${n}_$c" --no-size
    python3 - "$O/${n}_$c/report.txt" "$n" "$c" >> "$O/rows.tsv" <<'PY'
import re, sys
rep, n, c = sys.argv[1:4]
for ln in open(rep):
    m = re.match(r"^  E\s+([+-]\d+)\s+bdc_muxn (\S+) req (\S+) (\d+) ps \(\d+ x\) sel (\S+) (\d+) ps \(\d+ x\) launch (\S+) tc (-?\d+) raw ([+-]\d+) guarded", ln)
    if m:
        g, mux, rp, tr, sp, ts, la, tc, raw = m.groups()
        print("\t".join([n, c, mux.split(".udut.")[-1], rp.split("$")[-1], g, raw, tr, ts, la.split(".udut.")[-1]]))
PY
  done
  grep -h "INDEX\|_UMUX[0-9]" "$rd/seed1/pnr/sizes.vh" | sed "s/^/$n\t/" >> "$O/lines.tsv"
done
