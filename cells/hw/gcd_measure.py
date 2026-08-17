#!/usr/bin/env python3
"""Read hw/gcd_hw.v -- the compiled gcd kernel, swept across its whole vector
table by the on-die window sequencer.

    python3 hw/gcd_measure.py --program       # first run: load and start
    python3 hw/gcd_measure.py                # read everything, judge it
    python3 hw/gcd_measure.py --pin 7         # pin the sweep to vector 7
    python3 hw/gcd_measure.py --light         # fewer liveness samples

WHY --program IS NOT THE DEFAULT, and it is not the same reason as in
arb_prot_measure.py.  There, reconfiguring erased an exposure that had been
accumulating on silicon for days with nobody watching.  Here the sweep restarts
from vector 0 every time the sequencer wraps, so this design loses nothing of
its own by being reloaded -- but the DEVICE IS SHARED, and whatever is on it
belongs to whoever put it there.  Loading gcd_hw destroys that, and destroys it
silently: the next poll of the other design reports an empty or misaligned scan
rather than "someone took your board".  So it stays opt-in and it says what it
is doing before it does it.

If the die is not running gcd_hw at all, the scan-alignment check below (the
DEADBEEF/5A5A1234 constants and the TAG) catches it and every result is
refused, so a read without --program can never be a read of the wrong design.

WHAT THIS MEASURES.  gcd_hw.v wraps hw/gcd_rig.v -- the compiled gcd kernel --
in the same BSCANE2 instrumentation as arb_prot.v: a housekeeping ring for the
only clock on the part, a power-on reset, an arming delay, and a 48-bit
capture word.  What is new here is the window sequencer: every 65536
housekeeping cycles it resets the rig and advances idx to the next of sixteen
vectors, so err_sticky/ok_sticky accumulate a verdict for every vector in the
table without this script ever writing idx itself.

THE PAIR IS THE RESULT, NOT THE ZERO.  Both stickies are built from the same
LUT3, the same INIT and the same arm gate, so a vector that never sets ok_sticky
has not proved anything, and err_sticky staying 0 for it means nothing --
gcd_rig never produced a checkable answer to be wrong.  Reporting err==0 alone
would hide that vector's silence as if it were a pass; this script calls a
(ok=0, err=0) vector "never checked" and fails on it exactly as loudly as it
fails on a wrong answer.

PINNING.  gcd_hw's hold register carries hold_pin/hold_vec (arb_prot's does
not -- it has no vector to pin).  --pin freezes idx at one vector for the
whole poll, which is what turns hk_cnt/lap_cnt into a per-vector latency
figure instead of a table-wide throughput number.  Latency is reported in raw
housekeeping CYCLES per completed gcd, not seconds: converting the ring's own
period to time is a separate calibration that hw/ro_measure.py already does,
and guessing at it here would just be a second, unchecked copy of that
number.
"""

import argparse
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "build/hw/gcd_hw"
BIT = OUT / "gcd_hw.bit"

VIVADO_LAB = pathlib.Path(os.environ.get(
    "VIVADO_LAB", "/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab"))
XSDB = VIVADO_LAB / "bin/xsdb"
HW_SERVER = VIVADO_LAB / "bin/hw_server"

# Must match gcd_hw.v.
NVEC = 16
TAG = 0x6D
CONSTS = {2: 0xDEAD_BEEF, 3: 0x5A5A_1234}
HOLD_PIN_BIT = 1 << 10          # hold[10]
HOLD_VEC_SHIFT = 6              # hold[9:6]
HOLD_CLR_BIT = 1 << 11          # hold[11], clears err_sticky/ok_sticky

WINDOW_MS = int(os.environ.get("GCD_WINDOW_MS", "3000"))
REPEATS = 2                      # window 0 is a baseline read, see below

TCL_PROGRAM = r"""
fpga -f {bit}
"""

TCL = r"""
connect -url tcp:localhost:3121
targets -set -filter {{name =~ "xc7z010*"}}
{program}
jtag targets -set -filter {{name =~ "xc7z010*"}}

jtag lock 600000

set seq [jtag sequence]
set ctrl {ctrl_idle}

proc u1 {{addr}} {{
    global seq ctrl
    $seq clear
    $seq irshift -state IDLE -integer 6 0x02
    $seq drshift -capture -state IDLE -integer 48 [expr {{$addr | $ctrl}}]
    return [$seq run -hex]
}}

proc rd {{addr}} {{
    u1 $addr
    return [u1 $addr]
}}

foreach a {{2 3}} {{
    puts "CONST $a [rd $a]"
}}
puts "CFG [rd 4]"

# Zero the sticky array before anything is measured.  Without this the words
# read back are a cumulative record since configuration -- including the
# free-running sweeps that always happen between the FPGA coming up and this
# script's pin write landing -- rather than a verdict on this run.  Held for a
# few scan updates so the clear reaches all thirty-two latches, then released
# so they can accumulate again.
# The readback happens WHILE hold[11] is still asserted, and that ordering is
# the whole point.  Releasing first and then reading proves nothing: the rig
# keeps running, and a fast vector re-sets its own sticky in the microseconds
# between release and scan.  Measured -- pinned to vector 0, which completes a
# gcd every 3.5 housekeeping cycles, the array read back 0x0001 immediately
# after a clear that had in fact worked.
set ctrl {ctrl_clr}
u1 0
u1 0
u1 0
puts "CLRERR [rd 8]"
puts "CLROK [rd 9]"
puts "CLRABSN [rd 10]"
puts "CLRABSS [rd 11]"
puts "CLRCMPB [rd 14]"
puts "CLRCMPS [rd 15]"
puts "CLRCMPB0 [rd 20]"
set ctrl {ctrl_idle}
u1 0

puts "STATUS [rd 5]"
for {{set k 0}} {{$k < {samples}}} {{incr k}} {{
    puts "SAMPLE 0 [rd 6]"
}}

for {{set rep 0}} {{$rep < {reps}}} {{incr rep}} {{
    set ctrl {ctrl_run}
    u1 0
    set t0 [clock microseconds]
    after {window_ms}
    set ctrl {ctrl_idle}
    u1 0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {{$t1 - $t0}}]"
    puts "HKCOUNT $rep [rd 0]"
    puts "LAPCOUNT $rep [rd 1]"
}}

puts "ERR [rd 8]"
puts "OK [rd 9]"
puts "ABSN [rd 10]"
puts "ABSS [rd 11]"
puts "ABSV [rd 12]"
puts "ABSI [rd 13]"
puts "CMPB [rd 14]"
puts "CMPS [rd 15]"
puts "CMPV [rd 16]"
puts "CMPI [rd 17]"
puts "ERRV [rd 18]"
puts "ERRI [rd 19]"
puts "CMPB0 [rd 20]"

jtag unlock
puts "DONE"
exit
"""


def decode(hexstr):
    """xsdb -hex gives bytes least-significant first, LSB shifted first."""
    return int.from_bytes(bytes.fromhex(hexstr), "little")


def field(word):
    return dict(data=word & 0xFFFFFFFF,
                addr=(word >> 32) & 0x1F,
                run=(word >> 37) & 1,
                ovf=(word >> 38) & 1,
                tag=(word >> 40) & 0xFF)


def ensure_hw_server():
    def up():
        r = subprocess.run(["bash", "-c",
                            "exec 3<>/dev/tcp/127.0.0.1/3121 && echo up"],
                           capture_output=True, text=True)
        return "up" in r.stdout
    if up():
        return True
    subprocess.Popen([str(HW_SERVER), "-d", "-s", "tcp::3121"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(30):
        if up():
            return True
        subprocess.run(["sleep", "1"])
    return False


def run_board(pin_bits, samples, reps=REPEATS, program=False):
    OUT.mkdir(parents=True, exist_ok=True)
    script = OUT / "measure.tcl"
    ctrl_idle = f"0x{pin_bits:03X}"
    ctrl_run = f"0x{(pin_bits | 0x20):03X}"
    ctrl_clr = f"0x{(pin_bits | HOLD_CLR_BIT):03X}"
    script.write_text(TCL.format(
        program=TCL_PROGRAM.format(bit=BIT) if program else "",
        ctrl_idle=ctrl_idle, ctrl_run=ctrl_run, ctrl_clr=ctrl_clr,
        samples=samples, reps=reps, window_ms=WINDOW_MS))
    r = subprocess.run([str(XSDB), str(script)], capture_output=True,
                       text=True, timeout=120 + reps * (WINDOW_MS / 1000 + 30))
    return r.stdout + r.stderr


# WINDOW carries a plain decimal microsecond count from Tcl's clock, not a
# 48-bit scan word -- see arb_prot_measure.py, which is where this convention
# and its comment come from.
DECIMAL_TAGS = {"WINDOW"}


def parse(out):
    """tag -> list of (index, value); values are decoded scan words except
    for DECIMAL_TAGS, which are plain integers."""
    got = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3 and p[0] in DECIMAL_TAGS and p[1].lstrip("-").isdigit():
            got.setdefault(p[0], []).append((int(p[1]), int(p[2])))
        elif len(p) == 2 and p[0].isupper():
            got.setdefault(p[0], []).append((0, decode(p[1])))
        elif len(p) == 3 and p[0].isupper() and p[1].lstrip("-").isdigit():
            got.setdefault(p[0], []).append((int(p[1]), decode(p[2])))
    return got


def report_abs(got, err, okb):
    """The abs probe: what bb10's |a-b| actually looked like on the die.

    This is not part of the pass/fail verdict and deliberately does not change
    the exit code.  It is a measurement of ONE INTERNAL SIGNAL, taken to settle
    a disagreement between a gate-level simulation of the routed netlist and the
    board -- see gcd_rig.v's header for the full argument.  A run can be a
    perfectly good PASS and still print something interesting here.

    Read it as a three-way:

      absn bit set              bb10 delivered a NEGATIVE |a-b| on that vector.
                                |x| < 0 is impossible, so this is a real fault
                                inside the kernel and the simulation was right
                                about the silicon.
      absn clear, abss set      bb10 ran and every abs it delivered was
                                non-negative.  Whatever breaks the failing
                                vectors is NOT this, and the gate model's
                                stuck-at-0 comparator is an artifact of the
                                model.
      absn clear, abss clear    bb10 was never reached at all.  Says nothing
                                about the comparator either way.
    """
    if "ABSN" not in got or "ABSS" not in got:
        print("\n  abs probe: NOT READ BACK (stale bitstream? this script "
              "expects addr 10-13)")
        return
    absn = field(got["ABSN"][-1][1])["data"] & 0xFFFF
    abss = field(got["ABSS"][-1][1])["data"] & 0xFFFF

    print("\nTHE ABS PROBE -- bb10's |a-b|, measured on the die")
    print("-" * 78)
    print(f"  absn_sticky = 0x{absn:04X}  (a set bit is a NEGATIVE abs -- "
          f"impossible; want 0x0000)")
    print(f"  abss_sticky = 0x{abss:04X}  (bb10 reached at all; a zero in "
          f"absn is void unless this is one)")

    neg = [v for v in range(NVEC) if (absn >> v) & 1]
    unseen = [v for v in range(NVEC) if not ((abss >> v) & 1)]
    failing = [v for v in range(NVEC) if not ((okb >> v) & 1) or ((err >> v) & 1)]

    if neg:
        print(f"  NEGATIVE abs on vector(s): {neg}")
    if unseen:
        print(f"  bb10 never reached on vector(s): {unseen}")

    # A check on the PROBE, not on the kernel.  Vectors 0 and 1 are the C
    # source's two early returns (a==0 and b==0), so they never enter the main
    # loop and bb10 is genuinely unreachable for them.  Every other vector
    # re-runs continuously for the whole window, so its abs fires thousands of
    # times.  abss reading anything other than 0xFFFC means the probe is not
    # sampling what this script thinks it is, and nothing above is safe to read.
    if abss != 0xFFFC:
        print(f"  PROBE SANITY: abss=0x{abss:04X}, expected 0xFFFC -- vectors "
              f"0 and 1 take the C source's early returns and never reach "
              f"bb10, every other vector runs the loop all window.  A "
              f"different word means the probe is not measuring what is "
              f"assumed here; treat the verdict below with suspicion.")

    if "ABSV" in got and "ABSI" in got:
        absv = field(got["ABSV"][-1][1])["data"]
        absi = field(got["ABSI"][-1][1])["data"]
        if (absi >> 4) & 1:
            signed = absv - (1 << 32) if absv >> 31 else absv
            print(f"  first negative abs: 0x{absv:08X} ({signed}) on vector "
                  f"{absi & 0xF}")
        else:
            print("  first negative abs: none captured")

    # -- the comparator, against its own sign bit -----------------------------
    cmpb = cmps = None
    if "CMPB" in got and "CMPS" in got:
        cmpb = field(got["CMPB"][-1][1])["data"] & 0xFFFF
        cmps = field(got["CMPS"][-1][1])["data"] & 0xFFFF
        print(f"\n  cmpb_sticky = 0x{cmpb:04X}  (ucmpi11 disagreed with "
              f"x[31]; want 0x0000)")
        print(f"  cmps_sticky = 0x{cmps:04X}  (ucmpi11 answered at all)")
        bad = [v for v in range(NVEC) if (cmpb >> v) & 1]
        if bad:
            print(f"  WRONG SIGN DECISION on vector(s): {bad}")
        # The control.  Same detector, same route, sampled on the UNPADDED
        # z_req.  bd_join drives a_ack from z_ack, so a padded sample can land
        # after the operand was released and report a mismatch the comparator
        # never made.  This one cannot: at z_req the cell's own matched delay
        # guarantees both operand and answer.
        if "CMPB0" in got:
            cmpb0 = field(got["CMPB0"][-1][1])["data"] & 0xFFFF
            print(f"  cmpb0_sticky = 0x{cmpb0:04X}  (same check on the "
                  f"UNPADDED z_req -- the control for probe over-padding)")
            if cmpb0 and cmpb:
                print("  -> both detectors agree: the comparator is wrong on "
                      "the die, and the pad is not the explanation.")
            elif cmpb and not cmpb0:
                print("  -> ONLY the padded detector fires.  The pad is the "
                      "artifact: it samples the operand after bd_join has "
                      "released it.  The comparator is NOT at fault; discount "
                      "cmpb entirely and look downstream.")
            elif cmpb0 and not cmpb:
                print("  -> only the UNPADDED detector fires, which is the one "
                      "ordering neither pad explains.  Suspect routing skew "
                      "between the three probe nets; raise PRBD and re-run.")
        if "CMPV" in got and "CMPI" in got:
            cmpv = field(got["CMPV"][-1][1])["data"]
            cmpi = field(got["CMPI"][-1][1])["data"]
            if (cmpi >> 4) & 1:
                s = cmpv - (1 << 32) if cmpv >> 31 else cmpv
                print(f"  first mis-compared operand: 0x{cmpv:08X} ({s}) on "
                      f"vector {cmpi & 0xF} -- sgt(x,-1) should be "
                      f"{int(s >= 0)} here")
            else:
                print("  first mis-compared operand: none captured")

    # The comparison that actually settles the question.
    if neg:
        same = set(neg) == set(failing)
        print(f"\n  VERDICT: the die really does deliver a negative abs. "
              f"{'The set matches' if same else 'The set does NOT match'} the "
              f"failing vectors {failing}.")
    elif set(failing) - set(unseen):
        print(f"\n  VERDICT: no negative abs anywhere, and bb10 WAS reached on "
              f"{sorted(set(failing) - set(unseen))} of the failing vectors. "
              f"The gate model's stuck-at-0 comparator is not what the silicon "
              f"does; look elsewhere.")
    elif failing:
        print(f"\n  VERDICT: inconclusive -- every failing vector "
              f"({failing}) never reached bb10, so the probe had nothing to "
              f"measure on exactly the vectors in question.")
    else:
        print("\n  VERDICT: no negative abs, and nothing failed.")

    # Where on the path the damage is.  The two probes bracket it: cmpb accuses
    # the comparator, and cmpb clear with absn set acquits it and points at the
    # subtract or the select downstream.
    if cmpb is None:
        return

    # SELF-CHECK ON THE DETECTOR, BEFORE ANY CONCLUSION IS DRAWN FROM IT.
    # A vector that delivers correct gcds cannot also be getting its sign
    # decisions wrong -- the loop would not terminate.  So a cmpb bit set on a
    # PASSING vector is a false positive, and if there are any, the whole word
    # is uninterpretable and must not be used to localise anything.
    #
    # The known mechanism, and it applies to both samplers.  bd_join drives
    # a_ack from z_ack, so the operand is released as soon as the consumer
    # acknowledges -- while z_req is still high.  The level-gated detector stays
    # sensitive for that entire window, and the capture flop sits behind a BUFG
    # worth about two nanoseconds of insertion delay.  Both can therefore read
    # an operand that has already advanced past the answer beside it.
    passing = [v for v in range(NVEC) if ((okb >> v) & 1) and not ((err >> v) & 1)]
    false_pos = [v for v in passing if (cmpb >> v) & 1]
    if false_pos:
        print(f"\n  DETECTOR UNRELIABLE: cmpb is set on vector(s) {false_pos}, "
              f"which delivered CORRECT gcds.  A wrong sign decision would stop "
              f"those terminating, so these are false positives and the whole "
              f"cmpb/cmpb0 word cannot localise anything.  Both samplers land "
              f"after bd_join releases the operand; fix the sampling before "
              f"reading this field again.  The abs probe above is unaffected -- "
              f"it is a one-channel invariant with no operand to go stale.")
        return

    if cmpb and neg:
        print("  LOCALISED: the comparator itself.  ucmpi11 returns the wrong "
              "sign for operands whose sign bit says otherwise, and the "
              "negative abs is downstream of that.  The captured operand above "
              "is a test case -- replay it against bdc/test_compute.py and "
              "against the post-synthesis netlist.")
    elif neg and not cmpb:
        print("  LOCALISED: NOT the comparator.  ucmpi11 agreed with x[31] "
              "every time it answered, so the sign decision is right and the "
              "damage is downstream: the subtract that negates (%137), or the "
              "select that chooses between it and %135 (%138).")
    elif cmpb and not neg:
        print("  ANOMALY: the comparator answered wrongly but no negative abs "
              "reached bb10's output.  Something downstream is masking it; "
              "neither probe alone explains that.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pin", type=int, choices=range(NVEC), default=None,
                    metavar="0-15",
                    help="pin the sweep to one vector via hold_pin/hold_vec "
                         "instead of letting idx auto-advance every window; "
                         "turns the window measurement into a per-vector "
                         "latency figure")
    ap.add_argument("--light", action="store_true",
                    help="fewer liveness samples; for routine polling")
    ap.add_argument("--program", action="store_true",
                    help="load gcd_hw.bit first -- REPLACES whatever design is "
                         "on the device")
    args = ap.parse_args()

    samples = 4 if args.light else 24

    if args.program and not BIT.exists():
        print(f"missing {BIT} -- run ./hw/build_hw.sh gcd_hw first",
              file=sys.stderr)
        return 2
    if not ensure_hw_server():
        print("hw_server did not come up", file=sys.stderr)
        return 2

    if args.program:
        print(f"--program given: loading {BIT.name}, which REPLACES whatever "
              f"design is currently configured on the device.")

    pin_bits = 0
    if args.pin is not None:
        pin_bits = HOLD_PIN_BIT | (args.pin << HOLD_VEC_SHIFT)

    out = run_board(pin_bits, samples, program=args.program)
    if "DONE" not in out:
        print("board scan did not complete:\n" + out[-3000:], file=sys.stderr)
        return 2

    got = parse(out)

    print("=" * 78)
    title = "gcd_hw -- compiled gcd kernel under the window sequencer"
    if args.pin is not None:
        title += f", pinned to vector {args.pin}"
    print(title)
    print("=" * 78)

    # -- 1. is the scan path telling the truth? ------------------------------
    ok = True
    for a, want in CONSTS.items():
        rows = [w for i, w in got.get("CONST", []) if field(w)["addr"] == a]
        if not rows:
            print(f"  constant at {a}: NOT READ BACK")
            ok = False
            continue
        f = field(rows[-1])
        good = f["data"] == want and f["tag"] == TAG
        print(f"  constant at {a}: 0x{f['data']:08X} "
              f"(want 0x{want:08X}), tag 0x{f['tag']:02X}  "
              f"{'ok' if good else 'MISMATCH'}")
        ok = ok and good
    if not ok:
        print("\nthe scan path does not read back what the design holds; "
              "every number below is meaningless.  Stop here.")
        return 1

    # -- 2. is this the bitstream we think it is? ----------------------------
    if "CFG" not in got:
        print("  CFG: NOT READ BACK -- stop.")
        return 1
    cfg = field(got["CFG"][-1][1])["data"]
    nvec = (cfg >> 24) & 0xFF
    cmpd = (cfg >> 16) & 0xFF
    hklen = (cfg >> 12) & 0xF
    wfilt = (cfg >> 8) & 0xF
    print(f"\n  build config: NVEC={nvec} CMPD={cmpd} HKLEN={hklen} "
          f"WFILT={wfilt}")
    if nvec != NVEC:
        print(f"  NVEC on the die is {nvec}, this script expects {NVEC} -- "
              f"stale bitstream or stale script.  Stop.")
        return 1

    # -- 3. is the rig armed? -------------------------------------------------
    if "STATUS" not in got:
        print("  STATUS: NOT READ BACK -- stop.")
        return 1
    stat = field(got["STATUS"][-1][1])["data"]
    hold_run = stat & 1
    por_done = (stat >> 1) & 1
    armed = (stat >> 2) & 1
    idx = (stat >> 3) & 0xF
    hold_vec = (stat >> 7) & 0xF
    hold_pin_rb = (stat >> 11) & 1
    print(f"  status: hold_run={hold_run} por_done={por_done} armed={armed} "
          f"idx={idx} hold_vec={hold_vec} hold_pin={hold_pin_rb}")
    if not armed:
        print("  NOT ARMED yet -- the sticky latches are still disabled and "
              "every bit below is meaningless.  Poll again shortly.")
        return 1
    if args.pin is not None and (hold_pin_rb != 1 or hold_vec != args.pin):
        print(f"  requested --pin {args.pin} but the die reports "
              f"hold_pin={hold_pin_rb} hold_vec={hold_vec} -- the pin write "
              f"did not take; treat the latency figure below as untrustworthy.")

    # -- 3b. the sticky clear has to prove it happened -----------------------
    # A clear that silently does nothing puts every verdict below back to being
    # a cumulative record since configuration, which is the exact failure this
    # bit was added to end.  So read the words back with the clear still applied
    # and require both to be zero.  Nothing downstream is worth printing if they
    # are not.
    if "CLRERR" not in got or "CLROK" not in got:
        print("  sticky clear: NOT READ BACK -- stop.  Without proof the array "
              "was zeroed, the per-vector verdict is a record of every sweep "
              "since configuration, not of this run.")
        return 2
    clr = {}
    for tag in ("CLRERR", "CLROK", "CLRABSN", "CLRABSS", "CLRCMPB", "CLRCMPS", "CLRCMPB0"):
        clr[tag] = field(got[tag][-1][1])["data"] & 0xFFFF if tag in got else None
    if any(v is None for v in clr.values()):
        print("  sticky clear: NOT READ BACK for "
              + ", ".join(t for t, v in clr.items() if v is None)
              + " -- stop.")
        return 2
    if any(clr.values()):
        print("  sticky clear FAILED: after asserting hold[11] the arrays still "
              "read " + " ".join(f"{t[3:].lower()}=0x{v:04X}"
                                 for t, v in clr.items())
              + ", want all 0x0000.  Stopping -- the verdict below would be "
                "stale.")
        return 2
    print("  sticky clear: err/ok/absn/abss/cmpb/cmps all 0x0000 confirmed, "
          "the arrays start this run empty")

    # -- 4. is the silicon actually running? ---------------------------------
    live = {field(w)["data"] for _, w in got.get("SAMPLE", [])}
    print(f"\n  liveness: {len(live)} distinct value(s) across {samples} "
          f"async samples of probe/lap/hk/por")
    if len(live) < 2:
        print("  the sampled bus never changed -- the rig is NOT running.  "
              "Every zero below is a dead rig, not a clean result.")
        return 1

    # -- 5. is the rig completing gcds? ---------------------------------------
    # Window 0 is a BASELINE READ, not a measurement -- both counters are
    # free-running and never cleared, so window 0's delta would be taken
    # against whatever an earlier poll (or the settling transient) left
    # behind.  Only window 1's delta, against window 0's own end value over
    # window 1's own known duration, is trustworthy.  Same reasoning as
    # arb_prot_measure.py's SVCCOUNT handling.
    prev_hk = prev_lap = None
    hk_delta = lap_delta = None
    for rep, us in sorted(got.get("WINDOW", [])):
        hk = [field(w) for i, w in got.get("HKCOUNT", []) if i == rep]
        lap = [field(w) for i, w in got.get("LAPCOUNT", []) if i == rep]
        if not hk or not lap:
            continue
        if hk[-1]["data"] == 0xFFFFFFFF or lap[-1]["data"] == 0xFFFFFFFF:
            print(f"  window {rep}: counter read while running, poisoned")
            continue
        cur_hk, cur_lap = hk[-1]["data"], lap[-1]["data"]
        if prev_hk is None:
            prev_hk, prev_lap = cur_hk, cur_lap
            print(f"  window {rep}: baseline read (hk={cur_hk}, "
                  f"lap={cur_lap}), not a rate")
            continue
        d_hk = cur_hk - prev_hk
        d_lap = cur_lap - prev_lap
        if d_hk < 0:
            d_hk += 1 << 32       # 32-bit wrap
        if d_lap < 0:
            d_lap += 1 << 32
        secs = us / 1e6
        print(f"  window {rep}: {secs:.3f} s wall, {d_hk} housekeeping "
              f"cycles, {d_lap} completed gcd(s)")
        hk_delta, lap_delta = d_hk, d_lap
        prev_hk, prev_lap = cur_hk, cur_lap

    # A dead rig is a RESULT, not a reason to stop reading.  This used to
    # `return 1` right here, and that suppressed the stickies -- which are the
    # only thing that separates the two ways a rig can show lap_delta == 0:
    #
    #   stickies also clear  -> the ring genuinely never completes a gcd
    #   ok_sticky SET        -> it completes them and the lap counter is lying,
    #                           or the completion is being credited elsewhere
    #
    # Those want opposite fixes, and the early return made them look identical.
    # So print the caveat, remember the verdict, and read on.
    dead = not lap_delta
    if dead:
        print("\n  lap counter did not advance across the window -- the rig "
              "completed NO gcd.  The stickies are still read below, because "
              "an ok_sticky set on a rig with no completions is a different "
              "bug from a rig that is simply stopped.")
    else:
        print(f"\n  lap counter advanced by {lap_delta} in the measurement "
              f"window -- the rig is running.")
    if args.pin is not None and not dead:
        cyc_per_gcd = hk_delta / lap_delta
        print(f"  vector {args.pin} pinned: {cyc_per_gcd:.1f} housekeeping "
              f"cycles/gcd averaged over {lap_delta} completion(s) (raw "
              f"cycles -- convert to seconds with hw/ro_measure.py's "
              f"calibration of this ring's period; not done here)")

    # -- 6. the per-vector verdict --------------------------------------------
    if "ERR" not in got or "OK" not in got:
        print("\n  ERR/OK sticky words: NOT READ BACK -- stop.")
        return 1
    err = field(got["ERR"][-1][1])["data"] & 0xFFFF
    okb = field(got["OK"][-1][1])["data"] & 0xFFFF

    print(f"\nTHE RESULT -- per-vector verdict from err_sticky/ok_sticky")
    print("-" * 78)
    print(f"  err_sticky = 0x{err:04X}  (want 0x0000)")
    if "ERRV" in got and "ERRI" in got:
        ev = field(got["ERRV"][-1][1])["data"]
        ei = field(got["ERRI"][-1][1])["data"]
        if (ei >> 4) & 1:
            print(f"  first wrong answer: 0x{ev:08X} ({ev}) on vector "
                  f"{ei & 0xF} -- what was DELIVERED, not what was expected")
    print(f"  ok_sticky  = 0x{okb:04X}  (want 0xFFFF)")

    n_correct = n_wrong = n_never = 0
    for v in range(NVEC):
        e = (err >> v) & 1
        o = (okb >> v) & 1
        if e:
            n_wrong += 1
            verdict = "WRONG ANSWER"
            if o:
                verdict += "  (ANOMALY: ok_sticky also set on this vector)"
        elif o:
            n_correct += 1
            verdict = "correct"
        else:
            # ok=0 and err=0: the rig never produced a checkable answer for
            # this vector.  A bare "err stayed 0" would read this as clean --
            # it is not.  Reported exactly as loudly as a wrong answer.
            n_never += 1
            verdict = ("never checked -- no gcd completed on this vector "
                       "since arming; the zero above proves nothing")
        print(f"  vector {v:2d}: {verdict}")

    print(f"\n  {n_correct}/{NVEC} correct, {n_wrong}/{NVEC} WRONG, "
          f"{n_never}/{NVEC} never checked")

    report_abs(got, err, okb)

    if n_wrong or n_never:
        print("\n  FAIL -- not every vector proved correct.")
        return 1

    # Reachable only if every sticky says correct while the lap counter never
    # moved.  That is not a pass, it is a contradiction: the stickies were set
    # by something other than a completion counted in this window -- a stale
    # result surviving the window reset, or a completion credited to the wrong
    # index.  Never let it print PASS.
    if dead:
        print("\n  FAIL -- every vector reads correct but the rig completed "
              "no gcd in the window.  The stickies were not set by anything "
              "this run counted; suspect cross-window credit, not success.")
        return 1

    print("\n  PASS -- all vectors correct, err_sticky=0x0000, "
          "ok_sticky=0xFFFF.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
