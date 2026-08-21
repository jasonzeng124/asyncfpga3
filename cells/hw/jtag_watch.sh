#!/usr/bin/env bash
# jtag_watch.sh -- keep the Platform Cable USB II attached, without a human.
#
#     sudo -b cells/hw/jtag_watch.sh          # start it, once, and walk away
#     tail -f /tmp/asyncfpga3-jtag-watch.log  # what it has been doing
#     sudo pkill -f jtag_watch.sh             # stop it
#
# WHY.  hw/jtag_attach.sh already knows how to bring the cable back: usbipd
# attach, chmod the node, reload the volatile firmware.  What it cannot do is
# notice that it needs to run.  There is no udev in this WSL instance, so
# nothing fires on re-enumeration and the cable simply goes quiet until
# somebody types a sudo password.  This is that somebody.
#
# ROOT, ONCE.  The chmod needs root and sudo needs a terminal, so the watcher
# itself is what you elevate -- one password at the start of the day instead
# of one per unplug.  It re-execs nothing and elevates nothing later; if you
# would rather not leave a root loop running, the alternative is a NOPASSWD
# sudoers line for jtag_attach.sh alone, which is a smaller grant but a
# permanent one.  Pick whichever you dislike less; this script does not
# install either.
#
# IT TAKES THE BOARD LOCK.  hw/jtag_attach.sh kills hw_server and rewrites the
# cable's firmware, which would turn somebody's in-flight run into a plausible
# wrong answer rather than an obvious failure.  So a re-attach waits for the
# same flock hw/board.sh uses.  If the cable vanished mid-session that session
# is already dead, but the lock is what makes "already dead" true rather than
# "half dead".
set -u

HERE=$(cd "$(dirname "$0")" && pwd)
POLL=${POLL:-5}
LOCK=${BOARD_LOCK:-/tmp/asyncfpga3-board.lock}
LOG=${JTAG_WATCH_LOG:-/tmp/asyncfpga3-jtag-watch.log}
MAX_BACKOFF=${MAX_BACKOFF:-300}

if [ "$(id -u)" != 0 ]; then
    echo "jtag_watch.sh: needs root -- the chmod does, and sudo needs a tty." >&2
    echo "    sudo -b $0" >&2
    exit 2
fi

say() { printf '%s %s\n' "$(date -Is)" "$*" | tee -a "$LOG" >&2; }

# The cable's identity, not just its presence: a re-enumeration gives the same
# vendor id at a NEW device number, and the firmware went with the old one.
ident() {
    lsusb 2>/dev/null | awk '/03fd:00/ {printf "%s/%s\n", $2, substr($4,1,3)}' | head -1
}
node() {
    local i; i=$(ident); [ -n "$i" ] && printf '/dev/bus/usb/%s\n' "$i"
}

say "jtag_watch: started (poll ${POLL}s, lock $LOCK)"
trap 'say "jtag_watch: stopping"; exit 0' INT TERM

known=""
backoff=0
while :; do
    now=$(ident)
    dev=$(node)

    if [ -n "$now" ] && [ "$now" = "$known" ] && [ -w "$dev" ]; then
        backoff=0                      # steady state: say nothing, do nothing
        sleep "$POLL"
        continue
    fi

    if [ -z "$now" ]; then
        say "jtag_watch: no cable in WSL -- trying to attach it"
    elif [ "$now" != "$known" ]; then
        say "jtag_watch: cable re-enumerated at $dev (was ${known:-nothing}) -- firmware is gone with the old device number"
    else
        say "jtag_watch: $dev is not writable -- no udev here to fix it"
    fi

    # Wait for whoever is on the board rather than yanking the cable out from
    # under them.  -w, not -n: a re-attach that gives up is a cable that stays
    # down, which is the thing this exists to prevent.
    exec 9>"$LOCK"
    if flock -w 900 9; then
        if "$HERE/jtag_attach.sh" >>"$LOG" 2>&1; then
            known=$(ident)
            say "jtag_watch: cable up at $(node)"
            backoff=0
        else
            # Physically unplugged, or not shared in usbipd -- either way a
            # human has to move something, and retrying every 5 s just fills
            # the log and spawns a usbipd.exe per tick.
            backoff=$(( backoff == 0 ? POLL * 2 : backoff * 2 ))
            [ "$backoff" -gt "$MAX_BACKOFF" ] && backoff=$MAX_BACKOFF
            say "jtag_attach failed -- needs a human; retrying in ${backoff}s"
        fi
        flock -u 9
    else
        say "jtag_watch: board locked for over 900s -- leaving the cable alone"
    fi
    exec 9>&-

    sleep "$(( backoff > 0 ? backoff : POLL ))"
done
