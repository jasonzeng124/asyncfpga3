#!/usr/bin/env python3
"""Run and poll verify/MTBF.md's hardware measurement.

    hw/build_hw.sh arb_mtbf
    python3 hw/check_fracture.py                  # must pass before anything below
    python3 hw/arb_mtbf_measure.py --program       # first run: load, baseline, start
    python3 hw/arb_mtbf_measure.py                 # every later run: poll, do not reload

WHY --program IS NOT THE DEFAULT.  xsdb's `fpga -f` reconfigures the device,
and reconfiguration clears every flip-flop back to its power-up value -- which
means the sticky anomaly bits this whole experiment exists to accumulate would
be wiped on every single poll if the bitstream were reloaded each time.  The
entire point of running this from a recurring, hours-apart /loop is that the
silicon keeps counting between invocations with nobody watching; --program is
the one-time act of starting that clock, and every default-mode invocation
after it only reads.

WHAT A POLL DOES, IN ORDER.

  1. Bring-up: the three constants and the async liveness sampler, exactly as
     ro_measure.py checks them, because a sticky bit that never fires proves
     nothing if the readback path is not proven first.

  2. Detector floor: read the six threshold-probe sticky bits (th[0..5],
     pulse widths 1,2,3,4,6,8 links).  These exist because the anomaly sticky
     latch is a routed LUT2 feedback loop, not an ideal comparator, so it has
     its own unmeasured minimum capturable pulse width -- and an all-zero
     anomaly result below that floor proves "no anomaly wider than the floor",
     not "no anomaly".  The smallest width that trips its latch, converted to
     ps from THIS build's own routed SDF (scaled by the 0.975 silicon-vs-SDF
     factor ro_measure.py already established), is that floor.  It only needs
     measuring once -- these pulses fire in microseconds, not hours -- but
     costs nothing to reconfirm every poll.

  3. A short calibration window (default 8 s x 3 repeats, same technique as
     ro_top) on the r1/r2 exposure counters.  Not run continuously: a 32-bit
     counter at these rates wraps in about a minute, so what is measured is a
     RATE, and total exposure between two polls -- possibly hours apart -- is
     that rate times the host's wall clock.  The three repeats also serve as
     an injection-lock check: if r1's and r2's measured periods sit on a
     suspiciously clean ratio, the two rings may have locked and parked at a
     fixed relative phase, which is exactly the "safe part of the window for
     hours" failure the two-independent-oscillator design exists to avoid.

  4. Read the six anomaly sticky bits (ch[0..5], depths 0,1,2,4,8,16).  Each
     is monotonic for the life of the bitstream -- there is no clear anywhere
     in this design, see arb_mtbf.v's header for why.

  5. Update build/hw/arb_mtbf/state.json: cumulative exposure per poll,
     first-seen wall time for any bit that turned on since the last poll, and
     print a verdict table.

Exit status is nonzero only for a broken MEASUREMENT (bring-up failure, a
stuck liveness signal, a counter overflow, a suspected frequency lock, or
check_fracture.py failing).  A channel's sticky bit being 1 is a RESULT, not a
script failure, and never changes the exit code by itself.
"""

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import time
from collections import defaultdict

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "verify"))
import tighten                                              # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "build/hw/arb_mtbf"
BIT = OUT / "arb_mtbf.bit"
SDF = OUT / "arb_mtbf.sdf"
STATE = OUT / "state.json"

VIVADO_LAB = pathlib.Path(os.environ.get(
    "VIVADO_LAB", "/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab"))
XSDB = VIVADO_LAB / "bin/xsdb"
HW_SERVER = VIVADO_LAB / "bin/hw_server"

# Must match arb_mtbf.v.
DEPTHS = [0, 1, 2, 4, 8, 16]
WIDTHS = [1, 2, 3, 4, 6, 8]
NCH = len(DEPTHS)
NPOP = 24
CONSTS = {8: 0xDEAD_BEEF, 9: 0x5A5A_1234, 10: 0x0000_0000}
TAG = 0x55
SILICON_FACTOR = 0.975     # measured, hw/README.md -- silicon runs this fast vs SDF

WINDOW_MS = int(os.environ.get("ARB_WINDOW_MS", "8000"))
REPEATS = int(os.environ.get("ARB_REPEATS", "3"))


# ---------------------------------------------------------------- SDF lookup
#
# bd_delay's ports (a, z) do not survive as SDF pins -- module boundaries
# disappear once the design is flattened, and only the internal LUT1 chain
# instances (base.chain.g[i].u) keep their hierarchical names.  tighten.py's
# own find_chains() already groups those by base instance for exactly this
# reason (it is what the sizing pass itself walks), so it is reused rather
# than re-derived: the delay reported here is the sum of each link's IOPATH
# plus the interconnect between consecutive links, i.e. exactly the quantity
# "N links of bd_delay cost this many ps", the same thing tighten.py sizes
# against.  N=0 has no chain instances at all and costs zero by construction.
#
# The routed SDF does NOT name these links' pins "I0"/"O" -- that is the
# *behavioural* LUT1 model's naming.  Once placed, each link is a real SLICE
# LUT6 primitive and the packer free-permutes which physical pin (A1..A6)
# carries the one real input; the output is typically O6 but is whatever the
# packer actually wired.  So this does not guess a pin name: it reuses
# tighten.py's own chain_endpoints() (find the pin inside link 0 that a REAL
# net drives, i.e. appears as a destination in `back`; find the pin inside
# the last link that REALLY drives something onward) and tighten.py's own
# walk() to sum delay along the one real path between them.  `stops` matters
# here too -- these chains feed into a real combinational loop a few hops
# downstream (the sticky latch, sometimes the C-element itself), and without
# marking loop pins as stops an unconfined walk() spins on that loop until it
# hits its own runaway guard.

def chain_ps(edges, back, stops, chains, base):
    links = chains.get(base)
    if not links:
        return 0, None
    head, tail = tighten.chain_endpoints(edges, back, links)
    if head is None:
        return None, f"no real driven input pin found inside {links[0]}"
    if tail is None:
        return None, f"no real driven output pin found inside {links[-1]}"
    best = tighten.walk(edges, head, stops, longest=True)
    if tail not in best:
        return None, f"walk from {head} never reached {tail}"
    return best[tail], None


def detector_floor(edges, back, stops, chains):
    """ps of the narrowest threshold pulse, from this build's own SDF."""
    return {w: chain_ps(edges, back, stops, chains, f"th[{i}].ud")
            for i, w in enumerate(WIDTHS)}


def depth_ps(edges, back, stops, chains):
    return {d: chain_ps(edges, back, stops, chains, f"ch[{i}].udly")
            for i, d in enumerate(DEPTHS)}


# ------------------------------------------------------------------ the run

TCL_PROGRAM = r"""
fpga -f {bit}
"""

TCL = r"""
connect -url tcp:localhost:3121
targets -set -filter {{name =~ "xc7z010*"}}
{program}
jtag targets -set -filter {{name =~ "xc7z010*"}}

# See ro_measure.py / hw/README.md: a background hw_server chain poll can
# shift a stray control word into this design between scans.  Nothing here
# can be erased by one (no clear bit exists), but an address glitch mid-scan
# is still a nuisance, so lock for the duration regardless.
jtag lock 600000

set seq [jtag sequence]
set ctrl 0

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

foreach a {{8 9 10}} {{
    puts "CONST $a [rd $a]"
}}
for {{set k 0}} {{$k < 24}} {{incr k}} {{
    puts "SAMPLE 0 [rd 12]"
}}

puts "THRESH [rd 3]"
puts "CTRL [rd 4]"

for {{set rep 0}} {{$rep < {repeats}}} {{incr rep}} {{
    set ctrl 0x20                           ;# hold_run moved to bit 5 when
                                             ;# hold_addr widened to 5 bits
    u1 0                                    ;# run=1
    set t0 [clock microseconds]
    after {window_ms}
    set ctrl 0x00
    u1 0                                    ;# run=0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {{$t1 - $t0}}]"
    puts "R1COUNT $rep [rd 0]"
    puts "R2COUNT $rep [rd 1]"
}}

puts "ANOM [rd 2]"
puts "FLT [rd 19]"
puts "POP [rd 5]"
puts "HITCNT0 [rd 6]"
puts "HITCNT1 [rd 7]"
puts "HITCNT2 [rd 11]"
puts "HITCNT3 [rd 13]"
puts "HITCNT4 [rd 14]"
puts "HITCNT5 [rd 15]"
puts "WINCTRL [rd 16]"
puts "DIAG16 [rd 17]"
puts "DIAG8 [rd 18]"

jtag unlock
puts "DONE"
exit
"""


def decode(hexstr):
    """xsdb -hex gives bytes least-significant first, LSB shifted first."""
    return int.from_bytes(bytes.fromhex(hexstr), "little")


def field(word):
    # Layout widened from a 4-bit to a 5-bit address field when the Phase 2
    # window-latch negative control needed a 17th mux address (see
    # arb_mtbf.v's hold_addr declaration) -- run/ovf shifted down one bit,
    # the reserved field shrank from 2 bits to 1, TAG and total width (48)
    # unchanged.
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


def run_board(program):
    script = OUT / "measure.tcl"
    script.write_text(TCL.format(
        program=TCL_PROGRAM.format(bit=BIT) if program else "",
        repeats=REPEATS, window_ms=WINDOW_MS))
    r = subprocess.run([str(XSDB), str(script)], capture_output=True,
                       text=True, timeout=120 + REPEATS * (WINDOW_MS / 1000 + 30))
    return r.stdout + r.stderr


# --------------------------------------------------------------- state file

def load_state():
    if STATE.exists():
        return json.loads(STATE.read_text())
    return dict(loaded_at=None, last_poll_at=None, poll_count=0,
                r1_rate_hz=None, r2_rate_hz=None,
                cumulative_r1_edges=0.0, cumulative_r2_edges=0.0,
                anomaly_sticky={}, anomaly_first_seen={},
                flt_sticky={}, flt_first_seen={},
                threshold_sticky={}, threshold_first_seen={},
                pop_sticky={}, pop_first_seen={},
                hitcnt={}, hitcnt_ovf={}, winctrl_hitcnt=None,
                diag16_captured=False, diag16_first_seen=None,
                diag8_captured=False, diag8_first_seen=None)


def save_state(st):
    STATE.write_text(json.dumps(st, indent=2, sort_keys=True))


def report_diag(label, ch_label, n_taps, raw, st, now):
    """Print + update state for one chain-tap spatial-snapshot diagnostic.

    raw layout: bits [0, n_taps] inclusive = chain taps s[0..n_taps] (n_taps+1
    values), bit n_taps+1 = frozen r1, bit n_taps+2 = frozen r2, bit
    n_taps+3 = captured flag.
    """
    print()
    print(f"Diagnostic: depth-{n_taps} chain spatial snapshot (a twin of "
          f"{ch_label}, own decision node, taps exposed)")
    print("-" * 78)
    if raw is None:
        print(f"  no {label.upper()} line in the log")
        return
    captured = bool((raw >> (n_taps + 3)) & 1)
    key_captured = f"{label}_captured"
    key_first_seen = f"{label}_first_seen"
    if not captured:
        print("  not yet captured -- no anomaly has fired on this instance "
              "since load; the bits below are live noise, not a snapshot")
        return
    taps = [(raw >> i) & 1 for i in range(n_taps + 1)]
    r1_snap = (raw >> (n_taps + 1)) & 1
    r2_snap = (raw >> (n_taps + 2)) & 1
    was = st.get(key_captured, False)
    if not was:
        st[key_first_seen] = now
    st[key_captured] = True
    first_seen = st.get(key_first_seen)
    when = time.strftime("%Y-%m-%d %H:%M", time.localtime(first_seen)) \
        if first_seen else "before this poll history"
    print(f"  captured at first anomaly, first seen {when}")
    print(f"  r1={r1_snap} r2={r2_snap}")
    print(f"  s[0] (raw q) .. s[{n_taps}] (what {ch_label} reads):")
    print("  " + "".join(str(b) for b in taps))
    # Each LUT1 stage is an inverter (INIT=2'h2, O=~I0), so a chain that has
    # been stable for a while (no recent transition) should ALTERNATE every
    # single stage -- adjacent taps being EQUAL is the anomaly, not adjacent
    # taps differing.  alternations counts how many of the n_taps adjacent
    # pairs correctly flip; the maximum, n_taps, is what a fully-settled
    # chain looks like.
    alternations = sum(1 for i in range(n_taps) if taps[i] != taps[i + 1])
    stuck_runs = n_taps - alternations
    if alternations == n_taps:
        print(f"  all {n_taps} adjacent pairs alternate -- the chain had "
              f"already fully settled; whatever tripped the grant decoder "
              f"came from q itself, not chain propagation")
    else:
        print(f"  only {alternations}/{n_taps} adjacent pairs alternate as "
              f"a settled chain should -- {stuck_runs} stage(s) failed to "
              f"invert, consistent with the wavefront still mid-chain at "
              f"capture time (propagation glitch), though this diagnostic's "
              f"own capture is NOT a true synchronous snapshot -- each tap "
              f"latch freezes independently on its own routed delay to "
              f"diag_captured, so some of this could be capture skew rather "
              f"than the chain itself; treat as suggestive, not conclusive, "
              f"until corroborated by more samples")


# --------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--program", action="store_true",
                     help="reconfigure the device and reset state.json -- "
                          "does on-chip history.  Use only to (re)start a run.")
    args = ap.parse_args()

    for f in (BIT, SDF):
        if not f.exists():
            print(f"missing {f} -- run hw/build_hw.sh arb_mtbf first",
                  file=sys.stderr)
            return 2
    if not XSDB.exists():
        print(f"xsdb not found at {XSDB}", file=sys.stderr)
        return 2

    fc = subprocess.run([sys.executable, str(ROOT / "hw/check_fracture.py"),
                         str(OUT / "arb_mtbf_routed.json")])
    if fc.returncode != 0:
        print("\ncheck_fracture.py did not pass -- refusing to run the "
              "measurement.", file=sys.stderr)
        return 1

    edges, celltype, _, _ = tighten.parse_sdf(SDF)
    chains = tighten.find_chains(edges)
    back = defaultdict(set)
    for src, lst in edges.items():
        for dst, _ in lst:
            back[dst].add(src)
    stops = {p for p in tighten.state_nodes(edges) if tighten.is_output(p)}
    floor_ps = detector_floor(edges, back, stops, chains)
    ch_ps = depth_ps(edges, back, stops, chains)

    if args.program and STATE.exists():
        print("--program given: this reconfigures the device and erases "
              "every sticky bit accumulated so far.  Delete state.json "
              "yourself first if that is really what you want.",
              file=sys.stderr)
        return 2

    if not args.program and not STATE.exists():
        print("no state.json and --program not given -- the device may not "
              "be running this bitstream yet.  Run with --program first.",
              file=sys.stderr)
        return 2

    if not ensure_hw_server():
        print("hw_server did not come up on tcp:3121", file=sys.stderr)
        return 2

    now = time.time()
    log = run_board(program=args.program)

    if "DONE" not in log:
        print("the board run did not complete:", file=sys.stderr)
        print(log[-3000:], file=sys.stderr)
        return 2

    bad = 0

    # -- bring-up: three constants, one of them zero ------------------------
    print("bring-up")
    print("-" * 78)
    for m in re.finditer(r"^CONST (\d+) ([0-9a-fA-F]+)$", log, re.M):
        a, f = int(m.group(1)), field(decode(m.group(2)))
        want = CONSTS[a]
        ok = (f["tag"] == TAG and f["addr"] == a and f["data"] == want)
        print(f"  addr {a:<3} tag {f['tag']:02x}  addr echo {f['addr']}  "
              f"data {f['data']:08x}  want {want:08x}   "
              f"{'ok' if ok else '<-- WRONG'}")
        if not ok:
            bad += 1
    if bad:
        print("\nthe scan path does not read back what the design holds; "
              "nothing below means anything")
        return 1

    # -- control channel: a sticky latch identical to every anomaly/threshold
    # channel, but wired so nothing can ever set it (I0 tied to 0).  A
    # combinational OR-self-latch has no defined power-on state; this is the
    # only way to tell "a real pulse was captured" apart from "the latch
    # raced itself at configuration and came up set".  If this reads 1, every
    # FIRED bit reported below -- anomaly or threshold -- is not trustworthy,
    # regardless of how plausible any individual one looks. ------------------
    ctrl = None
    m = re.search(r"^CTRL ([0-9a-fA-F]+)$", log, re.M)
    if m:
        ctrl = field(decode(m.group(1)))["data"] & 1
    print()
    print("control channel (sticky latch that nothing can ever set)")
    print("-" * 78)
    if ctrl is None:
        print("  no CTRL line in the log -- cannot tell whether the sticky "
              "construction itself is trustworthy")
        bad += 1
    elif ctrl:
        print("  ctrl_sticky = 1  <-- the latch set with NOTHING driving it. "
              "Every FIRED bit below,")
        print("  anomaly or threshold, is that latch racing itself at "
              "configuration, not a")
        print("  captured event.  Nothing past this point measures "
              "anything until the sticky")
        print("  construction has a real known-good start state.")
        bad += 1
    else:
        print("  ctrl_sticky = 0  -- this construction powered up clean on "
              "this die, this bitstream.")
        print("  That does not prove any given FIRED bit below is real, "
              "only that a clean")
        print("  power-up is possible; it is not the same claim.")
    if bad:
        return 1

    # -- liveness: r1, r2, ring3 must show variance; q_dly/pulse are allowed
    # to be stuck (a channel that never once toggled is what "MTBF is very
    # good" looks like at shallow depth, not necessarily a bug) but are
    # reported so a genuinely dead channel is visible rather than silent. ----
    samples = [field(decode(h))["data"] for h in
               re.findall(r"^SAMPLE \d+ ([0-9a-fA-F]+)$", log, re.M)]
    if not samples:
        print("no SAMPLE lines in the log", file=sys.stderr)
        return 2

    def variance(bit):
        vals = [(v >> bit) & 1 for v in samples]
        return sum(vals), len(vals)

    print()
    print("liveness (async sample, TCK domain -- value is meaningless, "
          "variance is the proof)")
    print("-" * 78)
    names = ["r1", "r2", "ring3"] + [f"q_dly[{d}]" for d in DEPTHS] + \
            [f"pulse[{w}]" for w in WIDTHS]
    for i, name in enumerate(names):
        ones, n = variance(i)
        turning = 0 < ones < n
        must = name in ("r1", "r2", "ring3")
        mark = "TURNING" if turning else f"STUCK at {1 if ones == n else 0}"
        print(f"  {name:<10} {ones:>3} ones of {n:<3} {mark}"
              f"{'  <-- MUST turn, stimulus is dead' if must and not turning else ''}")
        if must and not turning:
            bad += 1
    if bad:
        print("\na stimulus ring is not toggling; nothing below is exposure "
              "to anything")
        return 1

    # -- detector floor -------------------------------------------------------
    thresh = None
    m = re.search(r"^THRESH ([0-9a-fA-F]+)$", log, re.M)
    if m:
        thresh = field(decode(m.group(1)))["data"] & 0x3F

    print()
    print("detector floor (threshold-probe sticky bits, widths in bd_delay "
          "links)")
    print("-" * 78)
    floor_width = None
    for i, w in enumerate(WIDTHS):
        fired = bool((thresh >> i) & 1) if thresh is not None else None
        ps, err = floor_ps[w]
        ps_txt = f"{ps * SILICON_FACTOR:.0f} ps (silicon-scaled)" if ps is not None else f"? ({err})"
        print(f"  width {w:<3} links  {ps_txt:<28} "
              f"{'FIRED' if fired else 'not yet'}")
        if fired and floor_width is None:
            floor_width = w
    if floor_width is None:
        print("  no width up to 8 links has ever tripped its latch -- the "
              "detector floor is not")
        print("  yet bounded by this probe set; treat every all-zero "
              "anomaly result below as")
        print("  'no anomaly wider than the widest untested pulse', not as "
              "a clean zero.")
    else:
        ps, _ = floor_ps[floor_width]
        print(f"  detector floor: {floor_width} links "
              f"(~{ps * SILICON_FACTOR:.0f} ps) is the narrowest pulse "
              f"proven captured.")
        print("  Any all-zero anomaly channel below should be read as 'no "
              "anomaly wider than this'.")

    # -- calibration windows: rate + injection-lock check ---------------------
    windows = {int(a): int(b)
               for a, b in re.findall(r"^WINDOW (\d+) (\d+)$", log, re.M)}
    r1counts, r2counts = {}, {}
    for rep, h in re.findall(r"^R1COUNT (\d+) ([0-9a-fA-F]+)$", log, re.M):
        r1counts[int(rep)] = field(decode(h))
    for rep, h in re.findall(r"^R2COUNT (\d+) ([0-9a-fA-F]+)$", log, re.M):
        r2counts[int(rep)] = field(decode(h))

    print()
    print(f"calibration, {REPEATS} windows of {WINDOW_MS} ms")
    print("-" * 78)
    r1_rates, r2_rates = [], []
    for rep in range(REPEATS):
        f1, f2 = r1counts.get(rep), r2counts.get(rep)
        w = windows.get(rep)
        if f1 is None or f2 is None or w is None:
            print(f"  rep {rep}: missing data")
            bad += 1
            continue
        if f1["tag"] != TAG or f2["tag"] != TAG or f1["addr"] != 0 or f2["addr"] != 1:
            print(f"  rep {rep}: scan misaligned")
            bad += 1
            continue
        if f1["ovf"] or f2["ovf"]:
            print(f"  rep {rep}: counter OVERFLOWED -- lower ARB_WINDOW_MS")
            bad += 1
            continue
        if f1["data"] == 0xFFFFFFFF or f2["data"] == 0xFFFFFFFF:
            print(f"  rep {rep}: read while still running")
            bad += 1
            continue
        r1hz = f1["data"] * 1e6 / w
        r2hz = f2["data"] * 1e6 / w
        r1_rates.append(r1hz)
        r2_rates.append(r2hz)
        print(f"  rep {rep}: r1 {f1['data']:>10} edges  {r1hz/1e6:6.2f} MHz   "
              f"r2 {f2['data']:>10} edges  {r2hz/1e6:6.2f} MHz   "
              f"ratio {r1hz/r2hz:.6f}")
    if bad:
        return 1

    r1_rate = sum(r1_rates) / len(r1_rates)
    r2_rate = sum(r2_rates) / len(r2_rates)
    ratio = r1_rate / r2_rate
    ratio_spread = (max(r1_rates[i] / r2_rates[i] for i in range(len(r1_rates)))
                     - min(r1_rates[i] / r2_rates[i] for i in range(len(r1_rates))))
    nearest_int_ratio = min(
        abs(ratio - p / q) for p in range(1, 6) for q in range(1, 6))
    print()
    print(f"  r1 {r1_rate/1e6:.3f} MHz, r2 {r2_rate/1e6:.3f} MHz, "
          f"ratio {ratio:.6f}, spread across repeats {ratio_spread:.2e}")
    if nearest_int_ratio < 1e-4:
        print(f"  WARNING: ratio is within 1e-4 of a small integer fraction -- "
              f"possible injection lock.")
        print(f"  If this persists across polls, the phase may not be "
              f"sweeping and the exposure below is not what it claims to be.")
        bad += 1
    if bad:
        return 1

    # -- anomaly sticky bits ---------------------------------------------------
    anom = None
    m = re.search(r"^ANOM ([0-9a-fA-F]+)$", log, re.M)
    if m:
        anom = field(decode(m.group(1)))["data"] & 0x3F

    # -- width-discriminated twins of the anomaly sticky bits ------------------
    # Same construction as ANOM above, fed by raw & bd_delay(WFILT)(raw)
    # instead of raw.  A structural g1/g2 overlap is a fixed ~16 ps arc
    # delta and cannot survive the filter; a real metastable excursion lasts
    # on the order of the resolution constant and does.  See arb_mtbf.v.
    flt = None
    m = re.search(r"^FLT ([0-9a-fA-F]+)$", log, re.M)
    if m:
        flt = field(decode(m.group(1)))["data"] & 0x3F

    # -- Phase 1: depth-0 population (raw, unaggregated, 24 instances) --------
    pop = None
    m = re.search(r"^POP ([0-9a-fA-F]+)$", log, re.M)
    if m:
        pop = field(decode(m.group(1)))["data"] & 0x00FF_FFFF

    # -- Phase 2: per-channel windowed hit-rate counters -----------------------
    hitcnt = [None] * NCH
    hitcnt_ovf = [None] * NCH
    for i in range(NCH):
        m = re.search(rf"^HITCNT{i} ([0-9a-fA-F]+)$", log, re.M)
        if m:
            d = field(decode(m.group(1)))["data"]
            hitcnt[i] = d & 0x00FF_FFFF
            hitcnt_ovf[i] = bool((d >> 24) & 1)

    # -- negative control for the Phase 2 chain itself, I0 tied to 0 --------
    winctrl_cnt = None
    m = re.search(r"^WINCTRL ([0-9a-fA-F]+)$", log, re.M)
    if m:
        winctrl_cnt = field(decode(m.group(1)))["data"] & 0x00FF_FFFF

    # -- diagnostic: depth-16 and depth-8 chain spatial snapshots -----------
    diag16 = None
    m = re.search(r"^DIAG16 ([0-9a-fA-F]+)$", log, re.M)
    if m:
        diag16 = field(decode(m.group(1)))["data"] & 0x000F_FFFF

    diag8 = None
    m = re.search(r"^DIAG8 ([0-9a-fA-F]+)$", log, re.M)
    if m:
        diag8 = field(decode(m.group(1)))["data"] & 0x0FFF

    # -- state update ------------------------------------------------------
    st = load_state()
    first_poll = st["loaded_at"] is None
    if args.program or first_poll:
        st["loaded_at"] = now
        st["cumulative_r1_edges"] = 0.0
        st["cumulative_r2_edges"] = 0.0
        elapsed = 0.0
    else:
        elapsed = now - st["last_poll_at"]
        prev_r1 = st["r1_rate_hz"] or r1_rate
        prev_r2 = st["r2_rate_hz"] or r2_rate
        st["cumulative_r1_edges"] += prev_r1 * elapsed
        st["cumulative_r2_edges"] += prev_r2 * elapsed

    st["last_poll_at"] = now
    st["r1_rate_hz"] = r1_rate
    st["r2_rate_hz"] = r2_rate
    st["poll_count"] = st["poll_count"] + 1

    print()
    print("anomaly sticky bits (depths in bd_delay links after q)")
    print("-" * 78)
    print(f"  cumulative exposure since load: {st['cumulative_r1_edges']:.3e} "
          f"r1 edges, {st['cumulative_r2_edges']:.3e} r2 edges "
          f"({(now - st['loaded_at'])/3600:.2f} h)")
    any_fired = False
    for i, d in enumerate(DEPTHS):
        fired = bool((anom >> i) & 1) if anom is not None else None
        key = str(d)
        was = st["anomaly_sticky"].get(key, False)
        if fired and not was:
            st["anomaly_first_seen"][key] = now
        st["anomaly_sticky"][key] = bool(fired)
        ps, err = ch_ps[d]
        ps_txt = f"{ps * SILICON_FACTOR:.0f} ps" if ps is not None else "0 ps (bypass)"
        first_seen = st["anomaly_first_seen"].get(key)
        note = ""
        if fired:
            any_fired = True
            when = time.strftime("%Y-%m-%d %H:%M", time.localtime(first_seen)) \
                if first_seen else "before this poll history"
            note = f"  <-- FIRED, first seen {when}"
        fl = bool((flt >> i) & 1) if flt is not None else None
        fkey = str(d)
        fwas = st["flt_sticky"].get(fkey, False)
        if fl and not fwas:
            st["flt_first_seen"][fkey] = now
        st["flt_sticky"][fkey] = bool(fl)
        ftxt = "FILTERED:FIRED" if fl else "FILTERED:clean"
        print(f"  depth {d:<3} links ({ps_txt:>10} extra resolution time)"
              f"{'  FIRED' + note if fired else '  clean so far'}"
              f"   [{ftxt}]")

    # The comparison the filter exists to make.  Raw saturates within
    # microseconds (see the Phase 2 counters below), so a filtered bit that
    # is still clean after real exposure says the raw bit was the structural
    # g1/g2 overlap all along, not a metastable excursion.
    if anom is not None and flt is not None:
        nraw = bin(anom & 0x3F).count("1")
        nflt = bin(flt & 0x3F).count("1")
        print()
        print(f"  raw fired {nraw}/{NCH} channels, width-filtered fired "
              f"{nflt}/{NCH}")
        if nraw and not nflt:
            print("  -> every raw hit was narrower than the filter's "
                  "passband.  Consistent with the structural arc-delta")
            print("     overlap, NOT with a metastable excursion.")
        elif nflt:
            print("  -> at least one hit was wide enough to survive the "
                  "filter.  That is the interesting case: it cannot be")
            print("     explained by the fixed O5/O6 arc delta alone.")

    print()
    print("detector-threshold sticky bits (same construction, known pulse "
          "widths -- context above)")
    print("-" * 78)
    for i, w in enumerate(WIDTHS):
        fired = bool((thresh >> i) & 1) if thresh is not None else None
        key = str(w)
        was = st["threshold_sticky"].get(key, False)
        if fired and not was:
            st["threshold_first_seen"][key] = now
        st["threshold_sticky"][key] = bool(fired)
        first_seen = st["threshold_first_seen"].get(key)
        note = ""
        if fired:
            when = time.strftime("%Y-%m-%d %H:%M", time.localtime(first_seen)) \
                if first_seen else "before this poll history"
            note = f"  <-- FIRED, first seen {when}"
        print(f"  width {w:<3} links"
              f"{'  FIRED' + note if fired else '  clean so far'}")

    # -- Phase 1 report: raw per-instance, never aggregated --------------------
    print()
    print(f"Phase 1: depth-0 population ({NPOP} independent instances, same "
          f"stimulus, no depth variable)")
    print("-" * 78)
    if pop is None:
        print("  no POP line in the log")
    else:
        fired_idx = []
        for i in range(NPOP):
            bit = bool((pop >> i) & 1)
            key = str(i)
            was = st["pop_sticky"].get(key, False)
            if bit and not was:
                st["pop_first_seen"][key] = now
            st["pop_sticky"][key] = bit
            if bit:
                fired_idx.append(i)
        print(f"  fired: {len(fired_idx)}/{NPOP}  -- instances {fired_idx}")
        print(f"  raw bits (pop[0] first): "
              f"{''.join('1' if (pop >> i) & 1 else '0' for i in range(NPOP))}")
        print("  a uniform-looking spread across instances argues the six "
              "ch[] depths are comparable;")
        print("  a small number of instances dominating argues per-site "
              "capture floor, not depth, explains ch[]'s pattern.")

    # -- Phase 2 report: per-channel windowed hit-rate counter, alongside the
    # sticky bit above, never instead of it --------------------------------
    print()
    print("Phase 2 negative control (window-latch/sync/counter chain, I0 "
          "tied to 0 -- proves the chain itself, not just the plain sticky "
          "latch)")
    print("-" * 78)
    winctrl_bad = winctrl_cnt is None or winctrl_cnt != 0
    if winctrl_cnt is None:
        print("  no WINCTRL line in the log -- cannot tell whether the "
              "window-latch chain is trustworthy")
    elif winctrl_cnt == 0:
        print("  winctrl_hitcnt = 0  -- the window-latch/sync/counter chain "
              "does not self-trigger; Phase 2 counts below can be trusted "
              "as real hits, not chain noise.")
    else:
        print(f"  winctrl_hitcnt = {winctrl_cnt}  <-- nonzero with NOTHING "
              f"driving it.  The window-latch chain self-triggers; every "
              f"Phase 2 count below is noise, not signal, until this reads "
              f"0.")

    print()
    print("Phase 2: windowed hit-rate counters (same channels as the sticky "
          "bits above, additional signal)")
    if winctrl_bad:
        print("  ** UNTRUSTED: see the negative control above **")
    print("-" * 78)
    for i, d in enumerate(DEPTHS):
        key = str(d)
        cnt, ovf = hitcnt[i], hitcnt_ovf[i]
        prev = st["hitcnt"].get(key)
        st["hitcnt"][key] = cnt
        st["hitcnt_ovf"][key] = ovf
        if cnt is None:
            print(f"  depth {d:<3} links: no HITCNT{i} line in the log")
            continue
        delta = f", +{cnt - prev} since last poll" if prev is not None and cnt >= prev else ""
        ovf_note = "  <-- OVERFLOWED, count is not reliable" if ovf else ""
        print(f"  depth {d:<3} links: {cnt:>10} window-hits{delta}{ovf_note}")

    st["winctrl_hitcnt"] = winctrl_cnt

    report_diag("diag16", "ch[5]", 16, diag16, st, now)
    report_diag("diag8", "ch[3]", 8, diag8, st, now)

    save_state(st)

    print()
    print(f"poll #{st['poll_count']}, state saved to {STATE}")
    if any_fired:
        print()
        print("At least one depth has recorded a both-grants event.  This is "
              "the interesting")
        print("result MTBF.md exists to find, not a script failure -- see "
              "state.json for when,")
        print("and cross-check against the detector floor above before "
              "trusting a shallow depth's zero.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
