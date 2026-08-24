#!/usr/bin/env bash
# mem_modes.sh -- run tb_bdc_memseq's four modes and check each got the
# verdict it is supposed to get.
#
# Three of the four are EXPECTED TO FAIL, which is exactly why they need a
# runner: a negative control nobody runs is not a control, and a negative
# control that quietly starts passing is worse than no control at all.  So
# this script fails if EAGER passes, or if the one-hot monitor stops firing
# under BOTH, just as loudly as if the real modes break.
#
#   default   PASS      release on a_ack falling, plain port
#   EAGER     FAIL      release on p_ack falling -- the questioned rule
#   BOTH      monitor   both stations at once, plain port; the port's
#                       `ifndef SYNTHESIS one-hot check must fire
#   TOKEN     PASS      program-order token + arbitrated port
#
# See cells/tb/tb_bdc_memseq.v and bdc/AUDIT.md section 7.
set -u
cd "$(dirname "$0")/.."

LOG=build/sim/tb_bdc_memseq.log
fails=0

run() {  # run <defs> <label>
    BD_SIM_DEFS="$1" ./run_sim.sh tb_bdc_memseq >/dev/null 2>&1
}
bad() { echo "  BAD  $1"; fails=$((fails + 1)); }

run "" default
if grep -q "^tb_bdc_memseq PASS" $LOG; then echo "  ok   default: PASS"
else bad "default: expected PASS"; fi

run "-DBDC_SEQ_EAGER" eager
if grep -q "^tb_bdc_memseq FAIL" $LOG; then
    echo "  ok   EAGER: FAIL as expected ($(grep -c 'live acknowledge\|still high' $LOG) report line(s))"
else bad "EAGER: expected FAIL -- the p_ack release rule has stopped being detectable"; fi

run "-DBDC_SEQ_BOTH" both
if grep -q "FAIL bdc_memport.*one-hot" $LOG; then echo "  ok   BOTH: port one-hot monitor fired"
else bad "BOTH: the port's one-hot monitor did not fire -- it is no longer a control"; fi

run "-DBDC_SEQ_TOKEN" token
if grep -q "^tb_bdc_memseq PASS" $LOG && grep -q "24 accesses issued, 24 manufactured" $LOG; then
    echo "  ok   TOKEN: PASS, 24 edges for 24 accesses"
else bad "TOKEN: expected PASS with one RAM edge per access"; fi

if [ $fails -eq 0 ]; then echo "mem_modes: 4 ok"; else echo "mem_modes: $fails wrong"; fi
exit $fails
