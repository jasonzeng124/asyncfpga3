#!/bin/bash
# audit_route.sh SDF [tighten args...] -- the post-route rule audits a BOARD-QUEUE claim quotes
# ("rules A/E/F/H/I/J 0"), on one routed SDF, from cells/.  Rule D is a screen (tighten.py says
# so) and is counted separately, never as a violation.  Prints one summary line:
#   AUDIT <sdf> tighten_violations_nonD=<n> ruleD=<n> ruleE_violated=<n> ruleJ_rc=<rc>
set -u
SDF=$1; shift
OUT=${AUDIT_OUT:-$(dirname "$SDF")}
python3 verify/tighten.py "$SDF" "$@" > "$OUT/audit_tighten.log" 2>&1
python3 verify/skew.py "$SDF" > "$OUT/audit_skew.log" 2>&1
python3 verify/arb_fork.py "$SDF" > "$OUT/audit_arb.log" 2>&1; rj=$?
nd=$(awk '/^[A-Za-z]/{sec=$0} /VIOLATION/ && sec !~ /^D\./{n++} END{print n+0}' "$OUT/audit_tighten.log")
d=$(awk '/^[A-Za-z]/{sec=$0} /VIOLATION/ && sec ~ /^D\./{n++} END{print n+0}' "$OUT/audit_tighten.log")
ab=$(grep -c "ABORT" "$OUT/audit_tighten.log")
e=$(grep -oE "[0-9]+ violated" "$OUT/audit_skew.log" | awk '{s+=$1} END{print s+0}')
echo "AUDIT $SDF tighten_violations_nonD=$nd ruleD=$d tighten_abort=$ab ruleE_violated=$e ruleJ_rc=$rj"
