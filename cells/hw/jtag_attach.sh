#!/usr/bin/env bash
# Get the Platform Cable USB II talking, under WSL2, from cold.
#
#     cells/hw/jtag_attach.sh          # if the device node is already 0666
#     sudo cells/hw/jtag_attach.sh     # if it is not (it says which)
#
# Then read the board with the tool that self-reports:
#
#     python3 cells/hw/arb_prot_measure.py
#
# WHY THIS EXISTS.  On an ordinary Linux box udev does all of this and nobody
# thinks about it.  This WSL2 instance runs no udev at all -- PID 1 is
# `init(Ubuntu)`, not systemd, and there is no udevd process -- so neither
# /etc/udev/rules.d/99-xilinx-jtag.rules nor Xilinx's own
# 52-xilinx-pcusb.rules ever fires.  Two things therefore do not happen by
# themselves: the node does not get MODE=0666, and the cable does not get its
# firmware.
#
# The firmware is VOLATILE.  It lives in the cable's RAM and is gone on
# unplug, on a usbipd detach, and on anything that resets the device -- a
# plain `lsusb -v` is enough.  So this is not one-time setup; it is what you
# run whenever the cable comes back.
#
# Nothing here configures the FPGA.  No bitstream is written.
set -u

FW=/home/jayjay/dev2/lib/vivado/2026.1/data/xicom/xusb_xp2.hex
LAB=/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab
BUSID=${BUSID:-3-2}

node() {
    lsusb 2>/dev/null \
        | awk '/03fd:00/ {printf "/dev/bus/usb/%s/%s\n", $2, substr($4,1,3)}' \
        | head -1
}

# --- 1. the cable has to be in WSL at all -----------------------------------
if [ -z "$(node)" ]; then
    echo "== attaching $BUSID to WSL =="
    usbipd.exe attach --wsl --busid "$BUSID" 2>&1 | grep -v "^usbipd: info" || true
    sleep 4
fi
D=$(node)
if [ -z "$D" ]; then
    echo "no 03fd:* device in WSL.  Check 'usbipd.exe list':"
    echo "  Not shared -> needs 'usbipd bind --busid $BUSID' in an admin shell"
    echo "  Shared     -> this script's attach should have worked; try again"
    echo "  Attached   -> it is here and lsusb disagrees, which is a WSL bug"
    exit 1
fi
echo "== cable at $D =="

# --- 2. and it has to be writable -------------------------------------------
if [ ! -w "$D" ]; then
    if [ "$(id -u)" != 0 ]; then
        echo "$D is not writable by you and there is no udev here to fix it."
        echo "Re-run with sudo:  sudo $0"
        exit 2
    fi
    chmod 666 "$D"
fi

# --- 3. nothing else may hold the cable while fxload writes to it -----------
#
# pkill -x, NOT pkill -f.  With -f the pattern is matched against every
# process's full command line, and that includes the shell running THIS
# script, whose command line contains the word hw_server -- so `pkill -f
# hw_server` kills the script, and it does it before anything useful happens.
# -x matches the executable name only.
pkill -x hw_server 2>/dev/null
sleep 2

# --- 4. firmware ------------------------------------------------------------
#
# -t fx2lp, not -t fx2.  Single-stage fx2 only reaches 8 KB of on-chip RAM and
# this image does not fit: it dies with "can't write 31 bytes external memory
# at 0x2022" and leaves the cable unusable.  fx2lp has 16 KB and loads the
# same image in 102 segments, 8605 bytes.
#
# Loaded unconditionally, and deliberately NOT guarded by a "is it already
# loaded?" check.  The obvious probe is bcdDevice, and it is wrong twice over:
# reading it with `lsusb -v` RESETS the device and discards the firmware, and
# the value never updates over usbip anyway -- after a load that demonstrably
# works, sysfs still reports 0000, because the FX2 renumerates and usbip does
# not propagate the new descriptor.  Reloading costs two seconds; pay it.
echo "== loading $(basename $FW) =="
/usr/sbin/fxload -t fx2lp -I "$FW" -D "$D" || {
    echo "fxload failed.  If it says 'external memory', the -t is wrong."
    exit 1
}
sleep 4
D=$(node)
[ -n "$D" ] || { echo "the cable vanished after fxload"; exit 1; }

# chmod again, UNCONDITIONALLY, and never behind a `-w` test.  fxload
# renumerates the FX2, so the kernel tears the node down and makes a new one
# at the default 0600 root:root -- step 2's chmod applied to a node that no
# longer exists.  The `-w` guard this used to carry was worse than useless:
# root passes -w on any mode, so the check said "already writable" precisely
# when running as the only user who could fix it, and skipped.  The failure is
# silent and looks exactly like a dead board -- hw_server runs as you, cannot
# open a 0600 node, and reports an EMPTY JTAG CHAIN rather than a permission
# error, which is the same symptom as an unpowered FPGA.
chmod 666 "$D" 2>/dev/null || {
    echo "cannot chmod $D -- re-run with sudo"; exit 2; }
echo "== cable now at $D ($(stat -c%a "$D")) =="

# --- 5. hw_server -----------------------------------------------------------
echo "== starting hw_server =="
AS=${SUDO_USER:-$(id -un)}
if [ "$(id -u)" = 0 ] && [ "$AS" != root ]; then
    su - "$AS" -c "nohup $LAB/bin/hw_server -d -s tcp::3121 >/dev/null 2>&1 &"
else
    nohup "$LAB/bin/hw_server" -d -s tcp::3121 >/dev/null 2>&1 &
fi
sleep 8

# --- 6. say whether it worked -----------------------------------------------
#
# This script used to end by printing instructions and leaving the user to
# find out.  It cannot: every way this fails produces the SAME symptom from
# the measure script -- "available targets: none" -- whether the cable is
# missing from hw_server, the node is unreadable, or the FPGA is unpowered.
# Two of those three are this script's own job and it should name them.
#
# The distinction is between the two levels hw_server reports.  A cable it can
# open appears as a jtag target of its own; the FPGA appears BELOW it.  So:
#   nothing at all      -> hw_server never opened the cable.  Permissions or
#                          firmware, i.e. a bug here, not a board problem.
#   cable but no device -> the cable is fine and the chain is empty.  That one
#                          really is the board: power, or the JTAG header.
#
# `connect -url` is the same server the measure scripts talk to.  The warning
# below is about a BARE `connect`, which starts a private server instead.
CHAIN=$("$LAB/bin/xsdb" -eval \
    'connect -url tcp:localhost:3121; puts [jtag targets]; exit' 2>&1 || true)
if echo "$CHAIN" | grep -qi "xc7z\|arm_dap"; then
    echo "== chain OK -- the FPGA is on it =="
elif echo "$CHAIN" | grep -qi "platform cable\|digilent\|jtag-smt"; then
    echo "== the cable is up but the CHAIN IS EMPTY =="
    echo "   Nothing above is at fault: hw_server has the cable and sees no"
    echo "   device on it.  Check board power and the JTAG ribbon."
else
    echo "== hw_server does not see the cable =="
    echo "   $D is $(stat -c%a "$D" 2>/dev/null || echo gone); hw_server runs"
    echo "   as $AS.  A 0600 node reads back as an empty chain, not as an"
    echo "   error, so check that first."
fi

echo
echo "Now read the board:"
echo "    python3 cells/hw/arb_prot_measure.py"
echo
echo "Do NOT use a hand-rolled 'xsdb; connect; jtag targets' to check this."
echo "A bare 'connect' does not reach the same server arb_prot_measure.py"
echo "talks to (it uses 'connect -url tcp:localhost:3121'), so it reports an"
echo "empty chain while the board is perfectly reachable -- which is exactly"
echo "the false alarm that sent this whole investigation after the board's"
echo "power supply.  The measure script is the diagnostic.
"
