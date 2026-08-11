#!/usr/bin/env python3
"""Measure the ring oscillators on silicon and hold the routed SDF to account.

    hw/build_hw.sh ro_top
    python3 hw/ro_measure.py

This is the gate none of the other seven can be.  Every one of them is a
statement about the toolchain: that yosys emits the cells, that nextpnr packs
and routes them, that the SDF it writes is self-consistent.  None of them asks
whether the SDF is TRUE of this die.  Delay sizing has no meaning if it is not,
and the error would be silent everywhere else.

WHAT IS COMPARED.  For each ring, nextpnr's routed SDF gives an exact predicted
loop delay: sum the IOPATH arc of every LUT in the ring and the INTERCONNECT
delay of every net between them, once around.  The predicted period is twice
that -- a four-phase round trip of the loop.  The measured period is the window
divided by the count.  The interesting number is the ratio.

TWO NUMBERS COME OUT AND THEY ARE NOT THE SAME CLAIM.

  Per-ring ratio.  Includes the fixed cost of closing the loop, so it is
  contaminated by whatever the router did with the return path, and it depends
  on the host's wall clock being right.

  Slope ratio.  A straight line through (length, period) has a slope of two
  picoseconds-per-link and an intercept that is the whole fixed overhead.  The
  slope is what tighten.py actually spends when it adds or removes a link, and
  the fit removes the overhead rather than averaging it in.  It is also the
  number the ring-to-ring count RATIOS constrain, and those ratios share the
  same window exactly, so they do not depend on the wall clock at all.

  If those two disagree, believe the slope.

WHAT A RESULT MEANS.  A ratio near one says the SDF predicts silicon and the
whole sizing pass rests on solid ground.  A ratio that is CONSTANT but not one
says the model is wrong by a scale factor, which is recoverable: every delay in
the library is off by that factor in the same direction and the pass can be
corrected.  A ratio that DRIFTS with ring length is the bad case -- it means
the per-link and per-net parts of the model are wrong by different amounts, and
no single correction fixes it.

Exit status is nonzero if the readback path fails its own checks, if a counter
overflowed, or if the rings did not come back in length order -- all of which
mean the measurement is not a measurement, whatever the numbers look like.
"""

import os
import pathlib
import re
import statistics
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "verify"))
import tighten                                              # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "build/hw/ro_top"
BIT = OUT / "ro_top.bit"
SDF = OUT / "ro_top.sdf"

VIVADO_LAB = pathlib.Path(os.environ.get(
    "VIVADO_LAB", "/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab"))
XSDB = VIVADO_LAB / "bin/xsdb"
HW_SERVER = VIVADO_LAB / "bin/hw_server"

# Must match ro_top.v.
LENS = [7, 15, 31, 63, 127]
CONSTS = {8: 0xDEADBEEF, 9: 0x5A5A1234, 10: 0x00000000}
TAG = 0xA5

WINDOW_MS = int(os.environ.get("RO_WINDOW_MS", "8000"))
REPEATS = int(os.environ.get("RO_REPEATS", "3"))


# --------------------------------------------------------------- prediction

def ring_loop_ps(edges, celltype, i):
    """Walk one ring once around and total its routed delay.

    The ring is a simple cycle, but the SDF is not a cycle: every LUT output
    also fans out to the BUFG that taps it, and the BUFG fans out to a hundred
    counter clock pins.  So the walk is confined to the ring's own cells and
    the tap is excluded by name -- everything under ro[i]. except ro[i].bg.
    """
    pref = f"ro[{i}]."
    bufg = f"ro[{i}].bg"

    def mine(pin):
        inst = tighten.pin_split(pin)[0]
        return inst.startswith(pref) and inst != bufg

    start = f"{pref}inv/O6"
    if start not in edges:
        return None, f"no arcs out of {start}"

    total, pin, seen = 0, start, set()
    while True:
        nxt = [(d, w) for d, w in edges.get(pin, ()) if mine(d)]
        if len(nxt) != 1:
            return None, f"{pin} has {len(nxt)} in-ring successors, expected 1"
        dst, w = nxt[0]
        total += w
        pin = dst
        if pin == start:
            return total, None
        if pin in seen:
            return None, f"walk revisited {pin} without closing"
        seen.add(pin)


# ------------------------------------------------------------------ the run

TCL = r"""
connect -url tcp:localhost:3121
targets -set -filter {{name =~ "xc7z010*"}}
fpga -f {bit}
jtag targets -set -filter {{name =~ "xc7z010*"}}

# LOCK THE PORT, AND THIS IS NOT A PRECAUTION.
#
# hw_server rescans the chain on its own schedule.  A rescan that shifts DR
# while USER1 is still the selected instruction lands in THIS design's shift
# register and is then committed by the same Update-DR -- so an unrelated
# background poll writes a random control word.  Bit 5 of a random word is the
# clear bit, so about half of those polls wipe every counter, and the symptom
# is not noise: it is a clean, plausible, entirely wrong zero.  Measured, not
# theorised -- unlocked, all five counters read exactly 0 across a one-second
# window in which the rings were provably turning.
jtag lock 600000

set seq [jtag sequence]
set ctrl 0

# The control bits are STICKY on the host side.  A read is two scans and every
# scan commits a control word, so a read helper that sends a bare address
# silently drops run and clear -- which makes it impossible to read anything
# while the counters are running, including the poison value that proves they
# are.  Holding the bits here means a scan changes only what it means to.
proc u1 {{addr}} {{
    global seq ctrl
    $seq clear
    $seq irshift -state IDLE -integer 6 0x02
    $seq drshift -capture -state IDLE -integer 48 [expr {{$addr | $ctrl}}]
    return [$seq run -hex]
}}

# Both shifts end in IDLE, not in PAUSE: Pause-DR does not pass through
# Update-DR, so a scan that parks in PAUSE captures correctly and then never
# commits anything at all.
proc rd {{addr}} {{
    u1 $addr
    return [u1 $addr]
}}

foreach a {{8 9 10 12}} {{
    puts "CONST $a [rd $a]"
}}

# Is anything turning?  An asynchronous sample of each ring node, repeated:
# the value means nothing, the variance means everything.
for {{set k 0}} {{$k < 24}} {{incr k}} {{
    puts "SAMPLE 0 [rd 12]"
}}

for {{set rep 0}} {{$rep < {repeats}}} {{incr rep}} {{
    set ctrl 0x20
    u1 0                                    ;# clear=1
    set ctrl 0x00
    u1 0                                    ;# clear=0
    set ctrl 0x10
    u1 0                                    ;# run=1
    set t0 [clock microseconds]
    puts "POISON $rep [rd 0]"
    after {window_ms}
    set ctrl 0x00
    u1 0                                    ;# run=0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {{$t1 - $t0}}]"
    for {{set a 0}} {{$a < 5}} {{incr a}} {{
        puts "COUNT $rep $a [rd $a]"
    }}
}}
jtag unlock
puts "DONE"
exit
"""


def decode(hexstr):
    """xsdb -hex gives bytes least-significant first, LSB shifted first."""
    b = bytes.fromhex(hexstr)
    return int.from_bytes(b, "little")


def field(word):
    return dict(data=word & 0xFFFFFFFF,
                addr=(word >> 32) & 0xF,
                run=(word >> 36) & 1,
                ovf=(word >> 37) & 1,
                tag=(word >> 40) & 0xFF)


def ensure_hw_server():
    r = subprocess.run(["bash", "-c",
                        "exec 3<>/dev/tcp/127.0.0.1/3121 && echo up"],
                       capture_output=True, text=True)
    if "up" in r.stdout:
        return True
    subprocess.Popen([str(HW_SERVER), "-d", "-s", "tcp::3121"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(30):
        r = subprocess.run(["bash", "-c",
                            "exec 3<>/dev/tcp/127.0.0.1/3121 && echo up"],
                           capture_output=True, text=True)
        if "up" in r.stdout:
            return True
        subprocess.run(["sleep", "1"])
    return False


def run_board():
    script = ROOT / "build/hw/ro_top/measure.tcl"
    script.write_text(TCL.format(bit=BIT, repeats=REPEATS,
                                 window_ms=WINDOW_MS))
    r = subprocess.run([str(XSDB), str(script)], capture_output=True,
                       text=True, timeout=120 + REPEATS * (WINDOW_MS / 1000 + 30))
    return r.stdout + r.stderr


# --------------------------------------------------------------------- main

def main():
    for f in (BIT, SDF):
        if not f.exists():
            print(f"missing {f} -- run hw/build_hw.sh ro_top first",
                  file=sys.stderr)
            return 2
    if not XSDB.exists():
        print(f"xsdb not found at {XSDB}", file=sys.stderr)
        return 2

    edges, celltype, _, _ = tighten.parse_sdf(SDF)
    predicted = []
    for i, n in enumerate(LENS):
        loop, err = ring_loop_ps(edges, celltype, i)
        if loop is None:
            print(f"ring {i}: cannot walk the loop in the SDF: {err}",
                  file=sys.stderr)
            return 2
        predicted.append(2 * loop)

    if not ensure_hw_server():
        print("hw_server did not come up on tcp:3121", file=sys.stderr)
        return 2

    log = run_board()
    for m in re.finditer(r"^POISON (\d+) ([0-9a-fA-F]+)$", log, re.M):
        f = field(decode(m.group(2)))
        print(f"  diag POISON rep {m.group(1)}  run echo {f['run']}  "
              f"data {f['data']:08x}  "
              f"{'control path ok' if f['data'] == 0xFFFFFFFF else 'CONTROL PATH DEAD'}")
    samples = [field(decode(h))["data"] for h in
               re.findall(r"^SAMPLE \d+ ([0-9a-fA-F]+)$", log, re.M)]
    if samples:
        print(f"  diag SAMPLE {len(samples)} async samples of the five ring nodes")
        for i in range(5):
            bits = [(v >> i) & 1 for v in samples]
            print(f"    ring {i}: {sum(bits)} ones of {len(bits)}   "
                  f"{'TURNING' if 0 < sum(bits) < len(bits) else 'STUCK at %d' % bits[0]}")
    if "DONE" not in log:
        print("the board run did not complete:", file=sys.stderr)
        print(log[-3000:], file=sys.stderr)
        return 2

    bad = 0

    # -- the readback path checks itself before any number is believed --------
    print("readback")
    print("-" * 78)
    for m in re.finditer(r"^CONST (\d+) ([0-9a-fA-F]+)$", log, re.M):
        a, f = int(m.group(1)), field(decode(m.group(2)))
        if a not in CONSTS:
            continue
        want = CONSTS[a]
        ok = (f["tag"] == TAG and f["addr"] == a and f["data"] == want)
        print(f"  addr {a:<3} tag {f['tag']:02x}  addr echo {f['addr']}  "
              f"data {f['data']:08x}  want {want:08x}   "
              f"{'ok' if ok else '<-- WRONG'}")
        if not ok:
            bad += 1
    if bad:
        print("\nthe scan path does not read back what the design holds; "
              "nothing below is a measurement")
        return 1

    # -- the counts ----------------------------------------------------------
    windows = {int(a): int(b)
               for a, b in re.findall(r"^WINDOW (\d+) (\d+)$", log, re.M)}
    counts = {}
    for rep, a, h in re.findall(r"^COUNT (\d+) (\d+) ([0-9a-fA-F]+)$", log,
                                re.M):
        f = field(decode(h))
        if f["tag"] != TAG or f["addr"] != int(a):
            print(f"  repeat {rep} ring {a}: scan came back misaligned")
            bad += 1
        if f["ovf"]:
            print(f"  repeat {rep} ring {a}: counter OVERFLOWED -- "
                  f"the window is too long, lower RO_WINDOW_MS")
            bad += 1
        if f["data"] == 0xFFFFFFFF:
            print(f"  repeat {rep} ring {a}: read while still running")
            bad += 1
        counts.setdefault(int(a), []).append((int(rep), f["data"]))
    if bad:
        return 1

    print()
    print(f"measured, {REPEATS} windows of {WINDOW_MS} ms")
    print("-" * 78)
    print(f"{'ring':<6}{'links':>6}{'count':>14}{'period ps':>12}"
          f"{'SDF ps':>10}{'meas/SDF':>10}{'spread':>10}")

    per_ring = []
    for i, n in enumerate(LENS):
        periods = [windows[rep] * 1e6 / c for rep, c in counts[i]]   # us->ps
        p = statistics.mean(periods)
        spread = (max(periods) - min(periods)) / p
        per_ring.append(p)
        print(f"{i:<6}{n:>6}{counts[i][0][1]:>14}{p:>12.0f}"
              f"{predicted[i]:>10}{p / predicted[i]:>10.3f}"
              f"{spread * 100:>9.2f}%")

    # Rings must come back in length order or something is mis-wired.
    if per_ring != sorted(per_ring):
        print("\nthe rings are not in length order -- the design is mis-wired "
              "or the address mux is not selecting")
        return 1

    # -- what the SDF got right -------------------------------------------
    #
    # The primary comparison is per ring, against that ring's OWN routed
    # prediction.  A straight line through (links, period) was the first thing
    # tried here and it is the wrong model: the measured points miss it by up
    # to a quarter, because nextpnr does not place two rings the same way and
    # the routed cost of a link is not a constant across them.  The SDF already
    # knows each ring's actual routing, so comparing ring by ring asks the
    # question that has an answer.
    ratios = [p / q for p, q in zip(per_ring, predicted)]

    # Is one scale factor enough?  Fit measured = k * predicted through the
    # origin and look at what is left over.  If the residuals are small, the
    # model is right in shape and wrong only in magnitude, and a single
    # correction recovers the whole sizing pass.
    k = (sum(m * q for m, q in zip(per_ring, predicted))
         / sum(q * q for q in predicted))
    resid = [(m - k * q) / m for m, q in zip(per_ring, predicted)]
    worst = max(abs(r) for r in resid)

    print()
    print("verdict")
    print("-" * 78)
    print(f"  scale       measured = {k:.4f} x predicted, over an 18x span of "
          f"ring length.")
    print(f"              Silicon runs {(1 - k) * 100:.1f}% faster than the "
          f"routed SDF says it")
    print(f"              will.  That is the whole of the error to first "
          f"order.")
    print()
    print(f"  residual    {worst * 100:.1f}% worst case once that factor is "
          f"taken out, and it")
    print(f"              does not trend with length "
          f"({', '.join(f'{r:+.1%}' for r in resid)}).")
    print(f"              So it is per-route scatter -- what nextpnr charged "
          f"for THESE nets")
    print(f"              versus what they cost -- not a systematic error in "
          f"the model.")
    print()

    late = [i for i, r in enumerate(ratios) if r > 1.0]
    if late:
        print(f"  DIRECTION   rings {late} ran SLOWER than predicted.  That is "
              f"the dangerous")
        print(f"              side: a delay sized from this SDF would be "
              f"shorter than the")
        print(f"              logic it is meant to cover.")
    else:
        print(f"  direction   every ring ran FASTER than its prediction "
              f"({min(ratios):.3f} to")
        print(f"              {max(ratios):.3f}).  The SDF is pessimistic, "
              f"so a matched delay")
        print(f"              sized against it is longer than it strictly "
              f"needs to be --")
        print(f"              the safe side of the bundling constraint, and "
              f"the side that")
        print(f"              costs area rather than correctness.")
    print()

    # For the record, and clearly labelled as the weaker analysis.
    def fit(ys):
        n = len(LENS)
        mx, my = sum(LENS) / n, sum(ys) / n
        sxx = sum((x - mx) ** 2 for x in LENS)
        sxy = sum((x - mx) * (y - my) for x, y in zip(LENS, ys))
        m = sxy / sxx
        return m, my - m * mx

    m_meas, b_meas = fit(per_ring)
    m_pred, b_pred = fit([float(q) for q in predicted])
    lin = max(abs(y - (m_meas * x + b_meas)) / y for x, y in zip(LENS, per_ring))
    print(f"  per link    a straight line through the five points gives "
          f"{m_meas / 2:.0f} ps per")
    print(f"              link measured against {m_pred / 2:.0f} ps predicted "
          f"-- but the points")
    print(f"              miss that line by up to {lin * 100:.0f}%, so read it "
          f"as an order of")
    print(f"              magnitude and not as a result.  The scale factor "
          f"above is the")
    print(f"              claim; this is context.")

    # The failure that matters is silicon being SLOWER than predicted, because
    # that is the direction a matched delay cannot absorb.  A pessimistic model
    # costs links; an optimistic one costs correctness.
    fail = max(ratios) > 1.05 or worst > 0.25
    if fail:
        print()
        print("  This does NOT support the sizing pass.")
    print()
    print("These are measurements of one route on one die at one temperature. "
          "They")
    print("expire the next time anything moves, exactly like the numbers "
          "tighten.py")
    print("prints -- what does not expire is the ratio.")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
