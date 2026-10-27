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
[ -e "$LOCK" ] || : > "$LOCK" 2>/dev/null || true

# Opening the lock and CONTENDING for it are different failures and must not
# report the same way.  jtag_watch.sh runs as root and creates this file; if it
# leaves it root-owned and unwritable, `exec 9>` fails, flock then fails with
# "Bad file descriptor", and the old code blamed a nonexistent other session --
# a 3600-second wait message for what is really a chmod.
if ! exec 9>"$LOCK" 2>/dev/null; then
    echo "board.sh: cannot open $LOCK for writing." >&2
    ls -l "$LOCK" >&2 2>/dev/null || true
    echo "board.sh: this is a PERMISSIONS problem, not contention." >&2
    echo "board.sh: fix with  sudo chmod 666 $LOCK  (or restart hw/jtag_watch.sh," >&2
    echo "board.sh: which now does this itself at startup)." >&2
    exit 77
fi

if ! flock -w "$WAIT" 9; then
    echo "board.sh: another session has held the board for over ${WAIT}s." >&2
    echo "board.sh: NOT proceeding unlocked -- check who, or raise BOARD_WAIT." >&2
    exit 75
fi
echo "board.sh: holding $LOCK (pid $$)" >&2
"$@"
