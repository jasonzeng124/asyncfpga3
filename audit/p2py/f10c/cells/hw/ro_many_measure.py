#!/usr/bin/env python3
"""Measure 128 ring oscillators on silicon and turn the guardband into a percentile.

    BD_RLOC=none hw/build_hw.sh ro_many_top
    python3 hw/ro_many_measure.py

WHAT THIS ADDS TO hw/ro_measure.py.  That script measures five rings against
their own routed SDF and reports the worst residual.  verify/tighten.py spends
8.5% as its guardband and 8.5% is where that number came from -- one route, one
build, five samples, a max.  A rebuild of the same RTL then produced 30.7%, and
the residual trended with length (Spearman rho -0.90), driven almost entirely
by ring 0, the shortest.

Five points cannot say whether that is one badly-placed ring or a systematic
error on short chains, because five points have no distribution.  This script
measures 128, thirty-two at each of four lengths, and asks:

  WHAT PERCENTILE DOES 8.5% BUY.  Not "is the worst case under the band" -- the
  worst case of a 128-sample draw is a different quantity from the worst case
  of a 5-sample draw, and comparing them is the mistake that produced the
  original number.  The band covers some fraction of the population; that
  fraction is the answer, and it is reported per length and overall.

  DOES THE ERROR TREND WITH LENGTH once there are 32 samples per length.  With
  five points only rank correlation was available.  With 32 per length the
  DISTRIBUTIONS can be compared -- a Mann-Whitney U between the shortest and
  the longest, and the overlap between them -- which is a statement five points
  could not make in either direction.

  IS IT PLACEMENT OR IS IT REGION.  Ring lengths rotate by both group and slot
  (see hw/ro_many_top.v), so length is decorrelated from both.  That makes it
  possible to ask separately whether high-ratio rings cluster by SLOT (a slow
  counter, a slow BUFG, one unlucky corner of the readback logic) or by GROUP
  (a batch effect, or a region of the die), and a permutation test answers it
  rather than an eyeball over a table.

HOW THE RINGS ARE REACHED.  The design time-multiplexes eight counters over
sixteen groups, so a full sweep is sixteen separate windows.  Each group is a
SEPARATE xsdb session with its own short jtag lock, and each group's raw scan
output is written to build/hw/ro_many_top/raw/gNN.log the moment it comes back.
A session that dies takes its own group with it and nothing else; re-running
picks up the groups that are already on disk unless RO_FORCE=1.  This is not
tidiness -- a 30-window single-lock run has been observed to die at ~63 s, and
a sweep sixteen times longer than anything ro_measure ever did cannot be one
transaction.

EXIT STATUS is nonzero if the readback fails its own checks, if the group echo
does not match what was requested, if a counter overflowed, if the rings within
a group did not come back in length order, if a liveness sample says a selected
ring was not turning, or if a ring's loop could not be walked in the SDF.  All
of those mean the numbers are not measurements, whatever they look like.

ENVIRONMENT
    RO_WINDOW_MS    counting window per repeat, default 4000
    RO_REPEATS      windows per group, default 2
    RO_GROUPS       comma/dash list of groups to sweep, default 0-15
    RO_FORCE        1 to re-measure groups already on disk
    RO_GUARDBAND_PCT  the band under test, default 8.5
"""

import os
import pathlib
import re
import random
import statistics
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "verify"))
import tighten                                              # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "build/hw/ro_many_top"
BIT = OUT / "ro_many_top.bit"
SDF = OUT / "ro_many_top.sdf"
RAW = OUT / "raw"

VIVADO_LAB = pathlib.Path(os.environ.get(
    "VIVADO_LAB", "/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab"))
XSDB = VIVADO_LAB / "bin/xsdb"
HW_SERVER = VIVADO_LAB / "bin/hw_server"

# Must match hw/ro_many_top.v.
B = 8                       # measurement slots (BUFGs, counters)
G = 16                      # groups
LENS = [7, 15, 31, 63]
CONSTS = {8: 0xDEADBEEF, 9: 0x5A5A1234, 10: 0x00000000}
TAG = 0xA5


def ring_len(g, b):
    return LENS[(g + b) % 4]


WINDOW_MS = int(os.environ.get("RO_WINDOW_MS", "4000"))
REPEATS = int(os.environ.get("RO_REPEATS", "2"))
FORCE = os.environ.get("RO_FORCE", "0") == "1"
GUARDBAND_PCT = float(os.environ.get("RO_GUARDBAND_PCT", "8.5"))
# 24 async samples per group, same count ro_measure uses.  The probability a
# turning ring returns 24 identical bits is 2^-23 if the sampler is fair; the
# check is deliberately crude because it only has to separate "moving" from
# "nailed to a rail".
N_SAMPLES = 24


def parse_groups(spec):
    out = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, _, b_ = part.partition("-")
            out.extend(range(int(a), int(b_) + 1))
        else:
            out.append(int(part))
    return [g for g in out if 0 <= g < G]


GROUPS = parse_groups(os.environ.get("RO_GROUPS", f"0-{G - 1}"))


# --------------------------------------------------------------- prediction

def ring_loop_ps(edges, g, b):
    """Walk ring (g, b) once around and total its routed delay.

    The ring is a simple cycle but the SDF is not: the NAND output also fans
    out to the slot mux, and its enable input comes in from outside.  Confining
    the walk to instances under grp[g].ro[b]. excludes both -- the mux legs and
    the BUFG live under slot[b]., and the enable comparator under grp[g].
    directly.  Nothing needs excluding by name the way ro_measure.py has to
    exclude the BUFG, because in this design the tap is not inside the ring's
    own scope.
    """
    pref = f"grp[{g}].ro[{b}]."
    start = f"{pref}inv/O6"
    if start not in edges:
        return None, f"no arcs out of {start}"

    total, pin, seen = 0, start, set()
    while True:
        nxt = [(d, w) for d, w in edges.get(pin, ())
               if tighten.pin_split(d)[0].startswith(pref)]
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
#
# One session per group.  ctrl carries the group in [9:6] for every scan in the
# session, because the control bits are STICKY on the host side -- every scan
# commits a control word, so a helper that sends a bare address silently drops
# the group as well as run and clear, and the counters would then be clocked by
# whichever group the last write happened to name.

TCL = r"""
connect -url tcp:localhost:3121
targets -set -filter {{name =~ "xc7z010*"}}
{prog}
jtag targets -set -filter {{name =~ "xc7z010*"}}

# LOCK THE PORT, AND THIS IS NOT A PRECAUTION.  hw_server rescans the chain on
# its own schedule, and a rescan that shifts DR while USER1 is selected lands in
# THIS design's shift register and is committed by the same Update-DR -- an
# unrelated background poll writing a random control word.  Bit 5 of a random
# word is clear, so about half of them wipe every counter, and the symptom is a
# clean, plausible, entirely wrong zero.  Measured on ro_top, not theorised.
#
# The lock is taken PER GROUP and released at the end of the group, so the
# longest it is ever held is one group's windows.  A sweep is not one
# transaction; see the module docstring.
jtag lock 600000

set seq [jtag sequence]
set ctrl {grpbits}

proc u1 {{addr}} {{
    global seq ctrl
    $seq clear
    $seq irshift -state IDLE -integer 6 0x02
    $seq drshift -capture -state IDLE -integer 48 [expr {{$addr | $ctrl}}]
    return [$seq run -hex]
}}

# Both shifts end in IDLE, not PAUSE: Pause-DR does not pass through Update-DR,
# so a scan that parks in PAUSE captures correctly and never commits anything.
proc rd {{addr}} {{
    u1 $addr
    return [u1 $addr]
}}

foreach a {{8 9 10}} {{
    puts "CONST {g} $a [rd $a]"
}}

# Did the group actually latch?  Without this a wrong group is invisible: the
# counts are all real measurements, of the wrong eight rings.
puts "ECHO {g} [rd 13]"

# Is anything turning?  Asynchronous samples of the eight POST-MUX nodes -- the
# very signals the counters are clocked by.  The value means nothing, the
# variance means everything.
for {{set k 0}} {{$k < {nsamples}}} {{incr k}} {{
    puts "SAMPLE {g} [rd 12]"
}}

for {{set rep 0}} {{$rep < {repeats}}} {{incr rep}} {{
    set ctrl [expr {{{grpbits} | 0x20}}]
    u1 0                                    ;# clear=1
    set ctrl {grpbits}
    u1 0                                    ;# clear=0
    set ctrl [expr {{{grpbits} | 0x10}}]
    u1 0                                    ;# run=1
    set t0 [clock microseconds]
    puts "POISON {g} $rep [rd 0]"
    after {window_ms}
    set ctrl {grpbits}
    u1 0                                    ;# run=0
    set t1 [clock microseconds]
    puts "WINDOW {g} $rep [expr {{$t1 - $t0}}]"
    for {{set a 0}} {{$a < 8}} {{incr a}} {{
        puts "COUNT {g} $rep $a [rd $a]"
    }}
}}
jtag unlock
puts "GROUPDONE {g}"
exit
"""


def decode(hexstr):
    """xsdb -hex gives bytes least-significant first, LSB shifted first."""
    b_ = bytes.fromhex(hexstr)
    return int.from_bytes(b_, "little")


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


def run_group(g, program):
    RAW.mkdir(parents=True, exist_ok=True)
    script = OUT / f"measure_g{g:02d}.tcl"
    script.write_text(TCL.format(
        prog=f"fpga -f {BIT}" if program else "# already configured",
        g=g, grpbits=hex(g << 6), repeats=REPEATS, window_ms=WINDOW_MS,
        nsamples=N_SAMPLES))
    try:
        r = subprocess.run(
            [str(XSDB), str(script)], capture_output=True, text=True,
            timeout=180 + REPEATS * (WINDOW_MS / 1000 + 20))
        log = r.stdout + r.stderr
    except subprocess.TimeoutExpired as e:
        log = ((e.stdout or b"").decode(errors="replace")
               + (e.stderr or b"").decode(errors="replace")
               + "\nTIMEOUT\n")
    # Written whatever happened.  A partial group log is still evidence about
    # what the board did before it stopped answering.
    (RAW / f"g{g:02d}.log").write_text(log)
    return log


# ----------------------------------------------------------------- analysis

def pct(sorted_vals, p):
    """Percentile by nearest rank on an already-sorted list."""
    if not sorted_vals:
        return float("nan")
    k = max(0, min(len(sorted_vals) - 1,
                   int(round(p / 100.0 * len(sorted_vals) + 0.5)) - 1))
    return sorted_vals[k]


def frac_at_or_below(vals, thresh):
    if not vals:
        return float("nan")
    return sum(1 for v in vals if v <= thresh) / len(vals)


def spearman(xs, ys):
    def rank(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j + 1]] == v[order[i]]:
                j += 1
            avg = (i + j) / 2.0 + 1.0
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r
    rx, ry = rank(xs), rank(ys)
    n = len(xs)
    mx, my = sum(rx) / n, sum(ry) / n
    sxy = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    sxx = sum((a - mx) ** 2 for a in rx)
    syy = sum((b - my) ** 2 for b in ry)
    if sxx == 0 or syy == 0:
        return 0.0
    return sxy / (sxx * syy) ** 0.5


def mannwhitney(a, b_):
    """U test with tie correction, normal approximation.  Returns (U, z, p).

    Written out rather than imported because this tree has no scipy and adding
    one for a two-sample rank test would be a dependency bought with someone
    else's build.  n = 32 per side, which is comfortably inside the range where
    the normal approximation is the standard recommendation.
    """
    import math
    n1, n2 = len(a), len(b_)
    if n1 == 0 or n2 == 0:
        return float("nan"), float("nan"), float("nan")
    allv = sorted([(v, 0) for v in a] + [(v, 1) for v in b_])
    ranks = [0.0] * len(allv)
    i = 0
    while i < len(allv):
        j = i
        while j + 1 < len(allv) and allv[j + 1][0] == allv[i][0]:
            j += 1
        avg = (i + j) / 2.0 + 1.0
        for k in range(i, j + 1):
            ranks[k] = avg
        i = j + 1
    r1 = sum(r for r, (_, grp) in zip(ranks, allv) if grp == 0)
    u1 = r1 - n1 * (n1 + 1) / 2.0
    u = min(u1, n1 * n2 - u1)
    mu = n1 * n2 / 2.0
    # tie correction
    ties = 0.0
    i = 0
    while i < len(allv):
        j = i
        while j + 1 < len(allv) and allv[j + 1][0] == allv[i][0]:
            j += 1
        t = j - i + 1
        ties += t ** 3 - t
        i = j + 1
    n = n1 + n2
    sd = ((n1 * n2 / 12.0) * ((n + 1) - ties / (n * (n - 1)))) ** 0.5
    if sd == 0:
        return u, 0.0, 1.0
    z = (u - mu) / sd
    p = math.erfc(abs(z) / 2 ** 0.5)
    return u, z, p


def overlap_fraction(a, b_):
    """Fraction of the union that lies inside the range both samples span."""
    lo = max(min(a), min(b_))
    hi = min(max(a), max(b_))
    if hi < lo:
        return 0.0
    both = a + b_
    return sum(1 for v in both if lo <= v <= hi) / len(both)


def cluster_test(values, labels, n_labels, trials=4000, seed=12345):
    """Do `values` cluster by `labels`?  Permutation test on the spread of
    per-label medians.

    A table of sixteen medians always has a biggest and a smallest, and the gap
    between them is not evidence on its own -- the question is whether it is
    bigger than the gap a random relabelling of the same numbers produces.  So
    the statistic is max(median) - min(median) over the labels, and the null is
    built by shuffling the label assignment, which preserves both the value
    distribution and the label counts exactly.
    """
    def stat(lab):
        buckets = [[] for _ in range(n_labels)]
        for v, l in zip(values, lab):
            buckets[l].append(v)
        meds = [statistics.median(x) for x in buckets if x]
        return (max(meds) - min(meds)), meds

    obs, meds = stat(labels)
    rng = random.Random(seed)
    shuf = list(labels)
    hits = 0
    for _ in range(trials):
        rng.shuffle(shuf)
        if stat(shuf)[0] >= obs:
            hits += 1
    return obs, (hits + 1) / (trials + 1), meds


# --------------------------------------------------------------------- main

def main():
    for f in (BIT, SDF):
        if not f.exists():
            print(f"missing {f} -- run BD_RLOC=none hw/build_hw.sh ro_many_top "
                  f"first", file=sys.stderr)
            return 2
    if not XSDB.exists():
        print(f"xsdb not found at {XSDB}", file=sys.stderr)
        return 2

    stamp = OUT / "toolchain.txt"
    if stamp.exists():
        first = stamp.read_text().splitlines()[0]
        print(f"toolchain    {first}")
    else:
        print("toolchain    UNSTAMPED -- build/hw/ro_many_top/toolchain.txt is "
              "missing; a margin quoted without its build is a fact about a "
              "build, not about the design", file=sys.stderr)
        return 2

    # ---- predictions, from the routed SDF ---------------------------------
    edges, _celltype, _n_io, _n_ic = tighten.parse_sdf(SDF)
    predicted = {}
    walk_fail = []
    for g in range(G):
        for b in range(B):
            loop, err = ring_loop_ps(edges, g, b)
            if loop is None:
                walk_fail.append((g, b, err))
            else:
                predicted[(g, b)] = 2 * loop
    if walk_fail:
        print(f"\n{len(walk_fail)} of {G * B} rings could not be walked in the "
              f"SDF; first few:")
        for g, b, err in walk_fail[:5]:
            print(f"    grp[{g}].ro[{b}]: {err}")

    # ---- the sweep ---------------------------------------------------------
    if not ensure_hw_server():
        print("hw_server did not come up on tcp:3121", file=sys.stderr)
        return 2

    RAW.mkdir(parents=True, exist_ok=True)
    logs = {}
    programmed = False
    for g in GROUPS:
        cached = RAW / f"g{g:02d}.log"
        if cached.exists() and not FORCE and f"GROUPDONE {g}" in cached.read_text():
            logs[g] = cached.read_text()
            print(f"group {g:2d}   cached")
            continue
        # Configure once, on the first group actually measured.  Re-loading the
        # bitstream between groups would be sixteen configurations of the same
        # image and would reset the counters anyway.
        log = run_group(g, program=not programmed)
        programmed = True
        ok = f"GROUPDONE {g}" in log
        logs[g] = log
        print(f"group {g:2d}   {'ok' if ok else 'SESSION DID NOT COMPLETE'}")
        if not ok:
            print(f"           see {cached}; the sweep continues with the "
                  f"next group")

    done = [g for g in GROUPS if f"GROUPDONE {g}" in logs.get(g, "")]
    if not done:
        print("\nno group completed; nothing below is a measurement",
              file=sys.stderr)
        tail = logs.get(GROUPS[0], "")[-3000:]
        print(tail, file=sys.stderr)
        return 2

    bad = 0
    warn = 0

    # ---- the readback checks itself before any number is believed ----------
    print()
    print("readback")
    print("-" * 78)
    const_bad = 0
    for g in done:
        for m in re.finditer(r"^CONST (\d+) (\d+) ([0-9a-fA-F]+)$", logs[g],
                             re.M):
            a, f = int(m.group(2)), field(decode(m.group(3)))
            if a not in CONSTS:
                continue
            if not (f["tag"] == TAG and f["addr"] == a
                    and f["data"] == CONSTS[a]):
                print(f"  group {g} addr {a}: tag {f['tag']:02x} addr echo "
                      f"{f['addr']} data {f['data']:08x} want "
                      f"{CONSTS[a]:08x}   <-- WRONG")
                const_bad += 1
    print(f"  constants   {len(done) * 3 - const_bad} of {len(done) * 3} "
          f"reads of 0xDEADBEEF / 0x5A5A1234 / 0x00000000 correct")
    bad += const_bad

    echo_bad = 0
    for g in done:
        m = re.search(r"^ECHO (\d+) ([0-9a-fA-F]+)$", logs[g], re.M)
        if not m:
            print(f"  group {g}: no group echo came back   <-- WRONG")
            echo_bad += 1
            continue
        f = field(decode(m.group(2)))
        if f["tag"] != TAG or f["addr"] != 13 or f["data"] != g:
            print(f"  group {g}: echo read back {f['data']} at addr "
                  f"{f['addr']} (tag {f['tag']:02x})   <-- WRONG GROUP")
            echo_bad += 1
    print(f"  group echo  {len(done) - echo_bad} of {len(done)} groups "
          f"confirmed the group they were asked for (addr 13)")
    bad += echo_bad

    # ---- liveness ----------------------------------------------------------
    dead = []
    for g in done:
        samples = [field(decode(h))["data"] for h in
                   re.findall(r"^SAMPLE \d+ ([0-9a-fA-F]+)$", logs[g], re.M)]
        for b in range(B):
            bits = [(v >> b) & 1 for v in samples]
            if not bits:
                dead.append((g, b, "no samples"))
            elif not (0 < sum(bits) < len(bits)):
                dead.append((g, b, f"stuck at {bits[0]}"))
    print(f"  liveness    {len(done) * B - len(dead)} of {len(done) * B} selected "
          f"ring nodes returned a mixture over {N_SAMPLES} async samples")
    for g, b, why in dead[:10]:
        print(f"    grp[{g}].ro[{b}] (len {ring_len(g, b)}): {why}")
    bad += len(dead)

    # ---- poison ------------------------------------------------------------
    poison_bad = 0
    for g in done:
        for m in re.finditer(r"^POISON (\d+) (\d+) ([0-9a-fA-F]+)$", logs[g],
                             re.M):
            f = field(decode(m.group(3)))
            if f["data"] != 0xFFFFFFFF:
                poison_bad += 1
    print(f"  control     {'ok' if poison_bad == 0 else 'DEAD'} -- a counter "
          f"read while run was high returned the poison "
          f"({poison_bad} of {len(done) * REPEATS} did not)")
    bad += poison_bad

    if bad:
        print("\nthe scan path does not read back what the design holds; "
              "nothing below is a measurement")
        return 1

    # ---- the counts --------------------------------------------------------
    meas = {}
    for g in done:
        windows = {int(r): int(us) for _gg, r, us in
                   re.findall(r"^WINDOW (\d+) (\d+) (\d+)$", logs[g], re.M)}
        counts = {}
        for _gg, rep, a, h in re.findall(
                r"^COUNT (\d+) (\d+) (\d+) ([0-9a-fA-F]+)$", logs[g], re.M):
            f = field(decode(h))
            a = int(a)
            if f["tag"] != TAG or f["addr"] != a:
                print(f"  group {g} rep {rep} slot {a}: scan came back "
                      f"misaligned")
                bad += 1
            if f["ovf"]:
                print(f"  group {g} rep {rep} slot {a}: counter OVERFLOWED -- "
                      f"the window is too long, lower RO_WINDOW_MS")
                bad += 1
            if f["data"] == 0xFFFFFFFF:
                print(f"  group {g} rep {rep} slot {a}: read while still "
                      f"running")
                bad += 1
            if f["data"] == 0:
                print(f"  group {g} rep {rep} slot {a}: counted ZERO over the "
                      f"window while its node sampled as turning")
                bad += 1
            counts.setdefault(a, []).append((int(rep), f["data"]))
        for b in range(B):
            if b not in counts:
                continue
            periods = [windows[rep] * 1e6 / c for rep, c in counts[b] if c]
            if not periods:
                continue
            meas[(g, b)] = dict(period=statistics.mean(periods),
                                spread=(max(periods) - min(periods))
                                / statistics.mean(periods),
                                count=counts[b][0][1])
    if bad:
        return 1

    # ---- within-group length order ----------------------------------------
    #
    # Each group holds two rings of each length.  A group whose 63-link rings
    # do not out-run its 7-link rings is not reporting what it was asked for --
    # the mux selected wrong, or a slot is clocked by something else.  This is
    # the same check ro_measure.py makes across its five rings, done per group
    # because that is where the mux can go wrong.
    order_bad = []
    for g in done:
        by_len = {}
        for b in range(B):
            if (g, b) in meas:
                by_len.setdefault(ring_len(g, b), []).append(
                    meas[(g, b)]["period"])
        meds = [statistics.median(by_len[n]) for n in LENS if n in by_len]
        if meds != sorted(meds):
            order_bad.append((g, meds))
    print(f"  order       {len(done) - len(order_bad)} of {len(done)} groups "
          f"returned their four lengths in increasing period order")
    for g, meds in order_bad:
        print(f"    group {g}: {['%.0f' % m for m in meds]} ps")
    bad += len(order_bad)
    if bad:
        print("\nthe design is mis-wired or the mux is not selecting")
        return 1

    # ---- the population ----------------------------------------------------
    have = [(g, b) for (g, b) in sorted(meas) if (g, b) in predicted]
    missing_pred = [k for k in sorted(meas) if k not in predicted]
    print()
    print(f"population   {len(meas)} rings measured over {len(done)} groups, "
          f"{REPEATS} window(s) of {WINDOW_MS} ms each")
    if missing_pred:
        print(f"             {len(missing_pred)} of them have no SDF "
              f"prediction and are excluded from every ratio below")
        warn += len(missing_pred)

    ratios = {k: meas[k]["period"] / predicted[k] for k in have}

    # One scale factor over the whole population, exactly as ro_measure.py
    # fits it: measured = k * predicted through the origin.  With 128 points
    # this is a real regression rather than five points and a slope.
    kfit = (sum(meas[k]["period"] * predicted[k] for k in have)
            / sum(predicted[k] ** 2 for k in have))
    resid = {k: (meas[k]["period"] - kfit * predicted[k]) / meas[k]["period"]
             for k in have}

    print()
    print("per length -- measured / predicted, and the residual after one "
          "global scale")
    print("-" * 78)
    print(f"{'links':>6}{'n':>5}{'med ratio':>11}{'p90':>9}{'p99':>9}"
          f"{'max':>9}   {'|resid| med':>11}{'p90':>8}{'p99':>8}{'max':>8}")
    per_len_ratio, per_len_absres, per_len_res = {}, {}, {}
    for n in LENS:
        ks = [k for k in have if ring_len(*k) == n]
        rr = sorted(ratios[k] for k in ks)
        ar = sorted(abs(resid[k]) for k in ks)
        per_len_ratio[n] = rr
        per_len_absres[n] = ar
        per_len_res[n] = [resid[k] for k in ks]
        print(f"{n:>6}{len(rr):>5}{statistics.median(rr):>11.3f}"
              f"{pct(rr, 90):>9.3f}{pct(rr, 99):>9.3f}{max(rr):>9.3f}   "
              f"{statistics.median(ar) * 100:>10.1f}%{pct(ar, 90) * 100:>7.1f}%"
              f"{pct(ar, 99) * 100:>7.1f}%{max(ar) * 100:>7.1f}%")
    all_abs = sorted(abs(resid[k]) for k in have)
    all_ratio = sorted(ratios[k] for k in have)
    print(f"{'all':>6}{len(all_abs):>5}{statistics.median(all_ratio):>11.3f}"
          f"{pct(all_ratio, 90):>9.3f}{pct(all_ratio, 99):>9.3f}"
          f"{max(all_ratio):>9.3f}   "
          f"{statistics.median(all_abs) * 100:>10.1f}%"
          f"{pct(all_abs, 90) * 100:>7.1f}%{pct(all_abs, 99) * 100:>7.1f}%"
          f"{max(all_abs) * 100:>7.1f}%")
    print()
    print(f"  scale       measured = {kfit:.4f} x predicted over the whole "
          f"population.")

    # ---- THE HEADLINE ------------------------------------------------------
    print()
    print(f"what the {GUARDBAND_PCT:.1f}% guardband actually buys")
    print("-" * 78)
    print("  tighten.py holds back this fraction of every delay it sizes.  The")
    print("  question is not whether the worst of 128 rings fits inside it --")
    print("  the worst of a large sample is a different quantity from the worst")
    print("  of five, and treating them as the same is how 8.5% was minted.")
    print("  The question is what FRACTION OF THE POPULATION it covers.")
    print()
    gb = GUARDBAND_PCT / 100.0
    print(f"{'links':>6}{'n':>5}{'covered':>10}   "
          f"{'band needed for p90':>21}{'p99':>9}{'p100':>9}")
    for n in LENS:
        ar = per_len_absres[n]
        cov = frac_at_or_below(ar, gb)
        print(f"{n:>6}{len(ar):>5}{cov * 100:>9.1f}%   "
              f"{pct(ar, 90) * 100:>20.1f}%{pct(ar, 99) * 100:>8.1f}%"
              f"{max(ar) * 100:>8.1f}%")
    cov_all = frac_at_or_below(all_abs, gb)
    print(f"{'all':>6}{len(all_abs):>5}{cov_all * 100:>9.1f}%   "
          f"{pct(all_abs, 90) * 100:>20.1f}%{pct(all_abs, 99) * 100:>8.1f}%"
          f"{max(all_abs) * 100:>8.1f}%")
    print()
    print(f"  HEADLINE    {GUARDBAND_PCT:.1f}% covers the "
          f"{cov_all * 100:.0f}th percentile of {len(have)} rings.")
    if cov_all >= 0.99:
        print(f"              As a population statement the band holds: fewer "
              f"than one ring")
        print(f"              in a hundred needs more than it. ")
    elif cov_all >= 0.9:
        print(f"              The band is a p{cov_all * 100:.0f} statement, "
              f"not a bound.  About")
        print(f"              {(1 - cov_all) * 100:.0f} rings in a hundred "
              f"need more than it, and the delays")
        print(f"              tighten.py sizes are not sampled independently "
              f"from this")
        print(f"              population -- a kernel has hundreds of them.")
    else:
        print(f"              That is NOT a guardband, it is a median.  "
              f"{(1 - cov_all) * 100:.0f}% of rings")
        print(f"              exceed it.  A p99 band would have to be "
              f"{pct(all_abs, 99) * 100:.1f}%.")

    # The dangerous side, separately: silicon SLOWER than the model.  A
    # pessimistic model costs area; an optimistic one costs correctness, and
    # only one of those is a bug.
    slow = sorted(r for r in (resid[k] for k in have) if r > 0)
    n_slow = len(slow)
    print()
    print(f"  direction   {n_slow} of {len(have)} rings ran SLOWER than the "
          f"scaled model")
    if n_slow:
        one_sided = sorted(max(0.0, resid[k]) for k in have)
        print(f"              (the side a matched delay cannot absorb).  On "
              f"that side alone,")
        print(f"              {GUARDBAND_PCT:.1f}% covers "
              f"{frac_at_or_below(one_sided, gb) * 100:.0f}% of the population "
              f"and p99 needs "
              f"{pct(one_sided, 99) * 100:.1f}%.")
        print(f"              Worst single ring {max(slow) * 100:+.1f}%.")
    else:
        print(f"              -- every ring was faster than predicted, which "
              f"is the safe side.")

    # ---- does it still trend with length? ---------------------------------
    print()
    print("does the error trend with length, at n = 32 per length?")
    print("-" * 78)
    med_res = [statistics.median(per_len_res[n]) for n in LENS]
    rho = spearman(LENS, med_res)
    print(f"  medians     {', '.join(f'{n}:{m * 100:+.1f}%' for n, m in zip(LENS, med_res))}")
    print(f"              Spearman rho across the four medians "
          f"{rho:+.2f} (n = 4, which on its")
    print(f"              own says almost nothing -- 4 points reach |rho| = 1 "
          f"by chance once")
    print(f"              in twelve).  The distributions are the real test:")
    print()
    short, long_ = per_len_res[LENS[0]], per_len_res[LENS[-1]]
    u, z, p = mannwhitney(short, long_)
    ov = overlap_fraction(short, long_)
    print(f"  {LENS[0]} vs {LENS[-1]}    Mann-Whitney U = {u:.0f}, z = {z:+.2f}, "
          f"p = {p:.3g}")
    print(f"              overlap {ov * 100:.0f}% of both samples lie in the "
          f"range they share")
    trend = p < 0.01
    if trend:
        print(f"              The two lengths are drawn from DIFFERENT "
              f"distributions.  A single")
        print(f"              scale factor cannot fix that: correcting one "
              f"length mis-sizes")
        print(f"              the others, and short chains are most of what "
              f"tighten.py emits.")
    else:
        print(f"              No separation at p < 0.01.  With 32 per length "
              f"this is a real")
        print(f"              negative -- five points could not have said it "
              f"-- so the rho of")
        print(f"              -0.90 that ro_measure.py failed on was five "
              f"samples of one")
        print(f"              scatter distribution, not a length effect.")

    # ---- is the length trend a SLOPE error or an OFFSET error? -------------
    #
    # "Short chains are mispredicted" and "the model is missing a fixed
    # per-loop overhead" produce the SAME per-length ratio table, because a
    # constant time is a large fraction of a short ring and a negligible one of
    # a long ring.  They are completely different bugs with completely
    # different fixes -- a percentage correction versus an additive one -- and
    # the ratio table cannot tell them apart.  A two-parameter fit can:
    #
    #   measured = k * predicted            forces the line through the origin,
    #                                       so any fixed overhead is smeared
    #                                       across every length as a slope
    #                                       error, worst where the ring is
    #                                       shortest.
    #
    #   measured = k * predicted + delta    lets the fixed part be fixed.  If
    #                                       the length trend disappears here,
    #                                       the per-link cost was never wrong;
    #                                       the model is short by a constant.
    #
    # This is the same slope-versus-intercept separation ro_measure.py's
    # docstring describes, but it needs a well-conditioned fit to mean
    # anything: with five rings, one short point sets the intercept by itself.
    # 32 rings at each of four lengths is what makes it answerable.
    print()
    print("slope error or offset error?")
    print("-" * 78)
    n_ = len(have)
    mp = sum(predicted[k] for k in have) / n_
    mm = sum(meas[k]["period"] for k in have) / n_
    sxx = sum((predicted[k] - mp) ** 2 for k in have)
    sxy = sum((predicted[k] - mp) * (meas[k]["period"] - mm) for k in have)
    k2 = sxy / sxx
    d2 = mm - k2 * mp
    resid2 = {k: (meas[k]["period"] - (k2 * predicted[k] + d2))
              / meas[k]["period"] for k in have}
    med2 = [statistics.median([resid2[k] for k in have if ring_len(*k) == n])
            for n in LENS]
    abs2 = sorted(abs(resid2[k]) for k in have)
    u2, z2, p2 = mannwhitney([resid2[k] for k in have if ring_len(*k) == LENS[0]],
                             [resid2[k] for k in have if ring_len(*k) == LENS[-1]])
    print(f"  one param   measured = {kfit:.4f} x predicted")
    print(f"              per-length median residual "
          f"{', '.join(f'{n}:{m * 100:+.1f}%' for n, m in zip(LENS, med_res))}"
          f", {LENS[0]} vs {LENS[-1]} p = {p:.3g}")
    print(f"  two param   measured = {k2:.4f} x predicted {d2:+.0f} ps")
    print(f"              per-length median residual "
          f"{', '.join(f'{n}:{m * 100:+.1f}%' for n, m in zip(LENS, med2))}"
          f", {LENS[0]} vs {LENS[-1]} p = {p2:.3g}")
    print(f"              |resid| median {statistics.median(abs2) * 100:.1f}%, "
          f"p90 {pct(abs2, 90) * 100:.1f}%, "
          f"{GUARDBAND_PCT:.1f}% covers "
          f"{frac_at_or_below(abs2, gb) * 100:.0f}%")
    print()
    if trend and p2 >= 0.01:
        print(f"  THE TREND IS AN OFFSET, NOT A SLOPE.  Allowing one fixed "
              f"{d2:+.0f} ps per")
        print(f"  loop removes the length dependence entirely (p {p:.2g} -> "
              f"{p2:.2g}) and takes the")
        print(f"  {LENS[0]}-link median from {med_res[0] * 100:+.1f}% to "
              f"{med2[0] * 100:+.1f}%.  So the per-link cost -- the number")
        print(f"  tighten.py actually spends when it adds or removes a link -- "
              f"is not the")
        print(f"  thing that is wrong.  What is wrong is a constant the model "
              f"does not")
        print(f"  charge, and a constant is a large fraction of a short chain "
              f"and nothing")
        print(f"  at all of a long one.  That is the whole of the "
              f"'short chains are worse'")
        print(f"  effect, and it argues for an ADDITIVE correction rather than "
              f"a wider")
        print(f"  percentage band.")
        print()
        print(f"  IT DOES NOT RESCUE THE BAND.  Coverage moves only "
              f"{cov_all * 100:.0f}% -> "
              f"{frac_at_or_below(abs2, gb) * 100:.0f}%, because")
        print(f"  the residual scatter that is left is per-route and it is "
              f"genuinely wide.")
        print()
        print(f"  WHAT THIS RIG CANNOT SETTLE.  Whether that {d2:+.0f} ps is a "
              f"property of the")
        print(f"  fabric, of this route, or partly of this rig.  Each ring "
              f"node here feeds")
        print(f"  a mux leg as well as its own chain, and an under-charged "
              f"extra sink")
        print(f"  would be per-loop -- exactly the shape of delta.  ro_top's "
              f"rings tap a")
        print(f"  BUFG instead, which is also one extra sink, so the two rigs "
              f"are alike in")
        print(f"  kind; but ro_top has five rings, and fitting an intercept to "
              f"five points")
        print(f"  where one of them is short gives an answer that flips sign "
          f"between its")
        print(f"  two published routes (-1596 ps and +2303 ps).  Neither "
              f"confirms nor")
        print(f"  refutes this.  Settling it needs a second ro_many route, or "
              f"a variant")
        print(f"  with the mux tap moved off the ring node.")
    elif trend:
        print(f"  The trend survives the offset ({LENS[0]} vs {LENS[-1]} still "
              f"p = {p2:.2g}), so it is a")
        print(f"  genuine per-link error and not a missing constant.  An "
              f"additive")
        print(f"  correction will not fix it.")
    else:
        print(f"  No length trend to explain under either model.")

    # ---- placement or region? ---------------------------------------------
    print()
    print("is the scatter placement (slot) or region (group)?")
    print("-" * 78)
    vals = [abs(resid[k]) for k in have]
    slot_lab = [k[1] for k in have]
    grp_lab = [k[0] for k in have]
    s_obs, s_p, s_meds = cluster_test(vals, slot_lab, B)
    g_obs, g_p, g_meds = cluster_test(vals, grp_lab, G)
    print(f"  by slot     spread of the {B} slot medians "
          f"{s_obs * 100:.1f} points, permutation p = {s_p:.3f}")
    print(f"  by group    spread of the {G} group medians "
          f"{g_obs * 100:.1f} points, permutation p = {g_p:.3f}")
    print()
    top = sorted(have, key=lambda k: -abs(resid[k]))[:max(1, len(have) // 10)]
    from collections import Counter
    cs, cg = Counter(k[1] for k in top), Counter(k[0] for k in top)
    print(f"  worst decile ({len(top)} rings) by slot  "
          f"{dict(sorted(cs.items()))}")
    print(f"  worst decile ({len(top)} rings) by group "
          f"{dict(sorted(cg.items()))}")
    verdicts = []
    if s_p < 0.05:
        verdicts.append("SLOT -- a measurement-side effect (a counter, a BUFG, "
                        "a mux leg), not the fabric under test")
    if g_p < 0.05:
        verdicts.append("GROUP -- a batch or region effect")
    print()
    if verdicts:
        for v in verdicts:
            print(f"  clusters by {v}")
    else:
        print(f"  no clustering by either at p < 0.05.  The scatter is "
              f"per-ring, which is")
        print(f"  what 'nextpnr placed this one badly' looks like -- it is a "
              f"property of")
        print(f"  the individual route, not of where on the die it sits or "
              f"which counter")
        print(f"  read it.")

    # ---- the outlier that started this ------------------------------------
    print()
    print("the 1.346 outlier")
    print("-" * 78)
    print(f"  ro_top's rebuilt ring 0 (7 links) measured 1.346 x its "
          f"prediction.")
    short_ratios = sorted(ratios[k] for k in have if ring_len(*k) == LENS[0])
    n_above = sum(1 for r in short_ratios if r >= 1.346)
    print(f"  Among the {len(short_ratios)} 7-link rings here the ratio runs "
          f"{min(short_ratios):.3f} to {max(short_ratios):.3f},")
    print(f"  median {statistics.median(short_ratios):.3f}, and "
          f"{n_above} of them reach 1.346 or worse.")
    if n_above == 0 and max(short_ratios) < 1.2:
        print(f"  Nothing in this population comes close to it, so it is "
              f"neither a typical")
        print(f"  short chain nor an ordinary tail draw from this "
              f"distribution -- it is")
        print(f"  something about THAT route that this rig does not reproduce.")
    elif n_above == 0:
        print(f"  No ring here reaches it, but the tail runs close enough that "
              f"a draw of")
        print(f"  five could plausibly produce it.  A TAIL SAMPLE, not a "
              f"short-chain law.")
    else:
        print(f"  {n_above / len(short_ratios) * 100:.0f}% of 7-link rings are "
              f"at least that bad, so it is an ordinary")
        print(f"  member of the short-chain population and not an outlier at "
          f"all.")

    print()
    print(f"reproducibility: the widest per-ring spread across the "
          f"{REPEATS} window(s) was "
          f"{max(meas[k]['spread'] for k in meas) * 100:.3f}%")
    print()
    print("These are measurements of one route on one die at one temperature, "
          "and they")
    print("expire the next time anything moves -- exactly like the numbers "
          "tighten.py")
    print("prints.  What does not expire is that the guardband now has a "
          "denominator.")

    return 1 if (bad or warn or len(done) < len(GROUPS)) else 0


if __name__ == "__main__":
    sys.exit(main())
