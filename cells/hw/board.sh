#!/usr/bin/env bash
# Serialise access to the one EBAZ4205.  Wrap any xsdb session in this.
#
#   hw/board.sh xsdb hw/xsdb_whatever.tcl
#   hw/board.sh bash -c 'xsdb a.tcl && xsdb b.tcl'
#
# There is one board, one JTAG cable and one hw_server, and `fpga -f` plus
# `rst -system` are global: a second session programming the device mid-run
# does not produce a confusing result, it produces a plausible WRONG one, on
# somebody else's bitstream.  Two agents running concurrently is the normal
# case here, so the interlock is a lock rather than a convention.
#
# Holds an exclusive flock for the whole command.  BOARD_WAIT (default 3600 s)
# bounds the wait; timing out is reported as such rather than proceeding
# unlocked, because proceeding unlocked is the failure this exists to prevent.
set -u
LOCK=${BOARD_LOCK:-/tmp/asyncfpga3-board.lock}
WAIT=${BOARD_WAIT:-3600}
[ -e "$LOCK" ] || : > "$LOCK"
exec 9>"$LOCK"
if ! flock -w "$WAIT" 9; then
    echo "board.sh: another session has held the board for over ${WAIT}s." >&2
    echo "board.sh: NOT proceeding unlocked -- check who, or raise BOARD_WAIT." >&2
    exit 75
fi
echo "board.sh: holding $LOCK (pid $$)" >&2
"$@"
