#!/usr/bin/env bash
# ca_run.sh REPO ROUTE_DIR(seed1) CORNER OUT [extra corner_audit args...] -- auto_size.sh's rule() environment, one corner
R=$1; RD=$2; C=$3; O=$4; shift 4
mkdir -p "$(dirname "$O")"
/usr/bin/time -f "%e s wall %U s user %M KB" env BD_SKEW_E_JOIN= BD_SKEW_E_JOIN_DEPTH=1 PYTHONHASHSEED=1 CA_FAST=${CA_FAST:-1} \
  BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 \
  python3 "$R/research/tools/corner_audit.py" "$RD" --prefix bridge_i.udut. --band "$C" \
  --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --out "$O" "$@" > "$O.txt" 2>&1
echo "rc $? $(tail -1 "$O.txt")" >> "$O.txt"
