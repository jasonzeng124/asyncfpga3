#!/usr/bin/env bash
# Get the Platform Cable USB II working under WSL2.  Run with sudo.
#
#     sudo cells/hw/jtag_attach.sh
#
# WHY THIS EXISTS.  On an ordinary Linux box udev does all of this and nobody
# thinks about it.  This WSL2 instance runs no udev at all -- PID 1 is
# `init(Ubuntu)`, not systemd, and no udevd process exists -- so
# /etc/udev/rules.d/99-xilinx-jtag.rules never fires and neither does Xilinx's
# own 52-xilinx-pcusb.rules.  Two separate things therefore do not happen:
#
#   1. The device node comes up crw------- root:root, so hw_server (running as
#      you) cannot open the cable at all.
#
#   2. The cable never gets its firmware.  A Platform Cable USB II is a
#      Cypress FX2: out of reset it enumerates as 03fd:0008 with bcdDevice
#      0.00 and NO usable interface.  `lsusb` shows it, which is what makes
#      this confusing -- the cable looks present and hw_server still reports
#      "available targets: none", because what it is looking for is a cable
#      that has been given xusb_xp2.hex.  An empty `jtag targets` list means
#      no CABLE, not an unpowered board.
#
# Loading the firmware is volatile: it lives in the cable's RAM and is gone on
# unplug, on a usbipd detach, and on anything that resets the device (a plain
# `lsusb -v` is enough).  So this is not a one-time setup, it is what you run
# every time the cable comes back.
#
# The FPGA is not touched by any of this.  Nothing here configures the device.
set -u

FW=/home/jayjay/dev2/lib/vivado/2026.1/data/xicom/xusb_xp2.hex
BUSID=${BUSID:-3-2}

if [ "$(id -u)" != 0 ]; then
    echo "run me with sudo -- the device node is root-owned and there is no"
    echo "udev here to fix that:  sudo $0"
    exit 2
fi

node() {
    lsusb | awk '/03fd:00/ {printf "/dev/bus/usb/%s/%s\n", $2, substr($4,1,3)}' \
        | head -1
}

if [ -z "$(node)" ]; then
    echo "== attaching $BUSID to WSL =="
    usbipd.exe attach --wsl --busid "$BUSID" 2>&1 | grep -v "^usbipd: info" || true
    sleep 4
fi

D=$(node)
if [ -z "$D" ]; then
    echo "no 03fd:* device in WSL.  Check 'usbipd.exe list' -- the cable must"
    echo "read Shared before it can be attached, and Attached after."
    exit 1
fi
echo "== cable at $D =="
chmod 666 "$D"

# bcdDevice 0.00 is the unprogrammed FX2.  Anything else already has firmware
# and re-loading it would only bounce the device for no reason.
if lsusb -v -d 03fd: 2>/dev/null | grep -q "bcdDevice *0\.00"; then
    echo "== downloading $(basename $FW) =="
    /usr/sbin/fxload -t fx2 -I "$FW" -D "$D" || exit 1
    sleep 4
    D=$(node)
    [ -n "$D" ] && chmod 666 "$D" && echo "== re-enumerated at $D =="
else
    echo "== firmware already present =="
fi

echo "== restarting hw_server =="
pkill -f hw_server
sleep 2
su - "${SUDO_USER:-jayjay}" -c \
   "nohup /home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/hw_server -d -s tcp::3121 >/dev/null 2>&1 &"
sleep 5

echo
echo "Now check the chain as your normal user:"
echo "  python3 cells/hw/arb_prot_measure.py"
echo "If 'available targets: none' persists with the firmware loaded, the"
echo "cable is talking and the JTAG chain itself is empty -- that IS a board"
echo "or ribbon problem, and only then."
