#!/usr/bin/env python3
"""Read hw/arb_prot.v -- the arbiter AS SHIPPED, under sustained contention.

    python3 hw/arb_prot_measure.py --program     # first run: load and start
    python3 hw/arb_prot_measure.py               # every run after that

WHY --program IS NOT THE DEFAULT.  Reconfiguring the device clears every
sticky latch and resets the exposure to zero.  The whole result accumulates on
silicon between invocations with nobody watching, so --program is destructive
and must be asked for explicitly.

WHAT THIS MEASURES, and how it differs from arb_mtbf_measure.py.  That script
reads the bare decision element hammered by two free-running rings.  This one
reads bd_arbiter -- the cell a compiler emits -- wrapped in the four-phase
protocol it was specified against, with a real server and two self-timed
clients.  Three sticky bits per instance:

    serv  A1 ^ A2   normal exclusive service.  MUST be 1.
    viol  A1 . A2   both clients acknowledged at once.  MUST be 0.
    ovl   g1 . g2   both grants high at once, width-filtered.  MUST be 0.

THE PAIR IS THE RESULT, NOT THE ZEROS.  Every detector here is a LUT feedback
latch, and a latch that never sets reads identically to a latch that cannot.
An instance whose serv bit is 0 has not proved anything and is excluded from
the denominator; only serv=1 instances contribute exposure.  That is the whole
reason the serv bit exists, and it is checked before any zero is believed.

EXPOSURE IS IN ARBITRATION EVENTS, NOT SECONDS.  Instance 0's client-1 request
drives a counter, so the handshake rate is measured on the die.  Seconds are
meaningless for an MTBF here -- what matters is how many times the decision
element was actually asked to choose.
"""

import argparse
import json
import os
import pathlib
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "build/hw/arb_prot"
BIT = OUT / "arb_prot.bit"
STATE = OUT / "state.json"

VIVADO_LAB = pathlib.Path(os.environ.get(
    "VIVADO_LAB", "/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab"))
XSDB = VIVADO_LAB / "bin/xsdb"
HW_SERVER = VIVADO_LAB / "bin/hw_server"

# Must match arb_prot.v.
NARB = 96
NARBW = (NARB + 31) // 32
TAG = 0x3C
CONSTS = {2: 0xDEAD_BEEF, 3: 0x5A5A_1234}
VIOL_ADDRS = [8, 9, 10]
OVL_ADDRS = [12, 13, 14]
SERV_ADDRS = [16, 17, 18]
CFG_ADDR = 4
STATUS_ADDR = 5
SAMPLE_ADDR = 6

SILICON_FACTOR = 0.975     # measured, hw/README.md

WINDOW_MS = int(os.environ.get("ARB_WINDOW_MS", "8000"))
REPEATS = int(os.environ.get("ARB_REPEATS", "3"))

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

foreach a {{2 3}} {{
    puts "CONST $a [rd $a]"
}}
puts "CFG [rd 4]"
puts "STATUS [rd 5]"
for {{set k 0}} {{$k < 24}} {{incr k}} {{
    puts "SAMPLE 0 [rd 6]"
}}

for {{set rep 0}} {{$rep < {repeats}}} {{incr rep}} {{
    set ctrl 0x20
    u1 0
    set t0 [clock microseconds]
    after {window_ms}
    set ctrl 0x00
    u1 0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {{$t1 - $t0}}]"
    puts "HKCOUNT $rep [rd 0]"
    puts "SVCCOUNT $rep [rd 1]"
}}

puts "VIOL0 [rd 8]"
puts "VIOL1 [rd 9]"
puts "VIOL2 [rd 10]"
puts "OVL0 [rd 12]"
puts "OVL1 [rd 13]"
puts "OVL2 [rd 14]"
puts "SERV0 [rd 16]"
puts "SERV1 [rd 17]"
puts "SERV2 [rd 18]"

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


def run_board(program, repeats=None):
    reps = REPEATS if repeats is None else repeats
    OUT.mkdir(parents=True, exist_ok=True)
    script = OUT / "measure.tcl"
    script.write_text(TCL.format(
        program=TCL_PROGRAM.format(bit=BIT) if program else "",
        repeats=reps, window_ms=WINDOW_MS))
    r = subprocess.run([str(XSDB), str(script)], capture_output=True,
                       text=True, timeout=120 + reps * (WINDOW_MS / 1000 + 30))
    return r.stdout + r.stderr


# WINDOW carries a plain decimal microsecond count from Tcl's clock, not a
# 48-bit scan word, so it must not go through decode() -- an odd-length decimal
# string raises out of bytes.fromhex() rather than returning a wrong number,
# which is how this was caught, but a same-length one would have parsed
# silently into a garbage elapsed time.
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


def bits_of(words, n):
    v = 0
    for i, w in enumerate(words):
        v |= (w & 0xFFFFFFFF) << (32 * i)
    return [i for i in range(n) if (v >> i) & 1]


def load_state():
    if STATE.exists():
        return json.loads(STATE.read_text())
    return dict(loaded_at=None, last_poll_at=None, poll_count=0,
                serv_seen={}, viol_first_seen={}, ovl_first_seen={},
                cumulative_events=0.0, svc_hz=None)


def save_state(st):
    STATE.write_text(json.dumps(st, indent=2, sort_keys=True))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--program", action="store_true",
                    help="reconfigure the device and RESTART the exposure")
    ap.add_argument("--light", action="store_true",
                    help="fewer rate windows; for routine polling")
    args = ap.parse_args()

    if args.light:
        reps = 1
    else:
        reps = REPEATS

    if not BIT.exists():
        print(f"missing {BIT} -- run ./hw/build_hw.sh arb_prot first",
              file=sys.stderr)
        return 2
    if not ensure_hw_server():
        print("hw_server did not come up", file=sys.stderr)
        return 2

    st = load_state()
    if args.program:
        print("--program given: this reconfigures the device and erases the "
              "whole accumulated exposure.")
        st = dict(loaded_at=None, last_poll_at=None, poll_count=0,
                  serv_seen={}, viol_first_seen={}, ovl_first_seen={},
                  cumulative_events=0.0, svc_hz=None)
    elif st["loaded_at"] is None:
        print("no state.json and --program not given -- the device may not be "
              "running this bitstream yet.  Run with --program first.",
              file=sys.stderr)
        return 2

    out = run_board(args.program, repeats=reps)
    if "DONE" not in out:
        print("board scan did not complete:\n" + out[-3000:], file=sys.stderr)
        return 2

    now = time.time()
    if st["loaded_at"] is None:
        st["loaded_at"] = now
    got = parse(out)

    print("=" * 78)
    print("arb_prot -- bd_arbiter under sustained four-phase contention")
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
    cfg = field(got["CFG"][-1][1])["data"]
    narb = (cfg >> 16) & 0xFF
    clen1, clen2 = (cfg >> 12) & 0xF, (cfg >> 8) & 0xF
    slen, wfilt = (cfg >> 4) & 0xF, cfg & 0xF
    print(f"\n  build config: NARB={narb} CLEN1={clen1} CLEN2={clen2} "
          f"SLEN={slen} WFILT={wfilt}")
    if narb != NARB:
        print(f"  NARB on the die is {narb}, this script expects {NARB} -- "
              f"stale bitstream or stale script.  Stop.")
        return 1

    stat = field(got["STATUS"][-1][1])["data"]
    print(f"  status: hold_run={stat & 1} por_done={(stat >> 1) & 1} "
          f"armed={(stat >> 2) & 1}")
    if not (stat >> 2) & 1:
        print("  NOT ARMED yet -- the sticky latches are still disabled and "
              "every bit below is meaningless.  Poll again shortly.")
        return 1

    # -- 3. is the silicon actually running? ---------------------------------
    samples = {field(w)["data"] for _, w in got.get("SAMPLE", [])}
    print(f"\n  liveness: {len(samples)} distinct value(s) across 24 async "
          f"samples of the request/ack bus")
    if len(samples) < 2:
        print("  the sampled bus never changed -- the arbiters are NOT "
              "running.  Every zero below is a dead rig, not a clean result.")
        return 1

    # -- 4. handshake rate, measured -----------------------------------------
    # The counter is FREE-RUNNING and never cleared -- hold_run only gates
    # whether it increments, so a second window reads the first window's total
    # plus its own.  The rate is therefore the DELTA between consecutive reads,
    # not the raw value; taking the raw value of the last window reported three
    # times the true rate on the first run of this script.
    # Window 0 is a BASELINE READ, not a measurement.  The counter also
    # survives between invocations of this script, so window 0's delta would be
    # taken against whatever the previous poll left behind -- on the first run
    # that read 386 MHz against a true 96.6 MHz.  Only windows 1..N have a
    # trustworthy predecessor, which is why REPEATS defaults above 1.
    #
    # The overflow flag is expected and is NOT a poison here: at ~97 MHz a
    # 32-bit counter wraps every ~44 s, but a single 8 s window advances it by
    # ~7.7e8, well under 2^32, so at most one wrap can fall inside a window and
    # the correction below is unambiguous.
    rate = None
    prev = None
    for rep, us in sorted(got.get("WINDOW", [])):
        svc = [field(w) for i, w in got.get("SVCCOUNT", []) if i == rep]
        if not svc:
            continue
        if svc[-1]["data"] == 0xFFFFFFFF:
            print(f"  window {rep}: counter read while running, poisoned")
            continue
        cur = svc[-1]["data"]
        if prev is None:
            prev = cur
            print(f"  window {rep}: baseline read ({cur}), not a rate")
            continue
        delta = cur - prev
        prev = cur
        if delta < 0:              # 32-bit wrap
            delta += 1 << 32
        secs = us / 1e6
        hz = delta / secs / SILICON_FACTOR
        ovf = " OVERFLOWED" if svc[-1]["ovf"] else ""
        print(f"  window {rep}: {secs:.3f} s, {delta} handshakes "
              f"-> {hz/1e6:.2f} MHz{ovf}")
        rate = hz if rate is None else max(rate, hz)
    if rate:
        st["svc_hz"] = rate
    rate = st.get("svc_hz")
    if rate is None:
        print("  no rate window this poll; run without --light once to "
              "measure the handshake rate.")

    # -- 5. the three sticky sets --------------------------------------------
    serv = bits_of([field(got[f"SERV{i}"][-1][1])["data"] for i in range(3)],
                   NARB)
    viol = bits_of([field(got[f"VIOL{i}"][-1][1])["data"] for i in range(3)],
                   NARB)
    ovl = bits_of([field(got[f"OVL{i}"][-1][1])["data"] for i in range(3)],
                  NARB)

    for i in serv:
        st["serv_seen"].setdefault(str(i), now)
    for i in viol:
        st["viol_first_seen"].setdefault(str(i), now)
    for i in ovl:
        st["ovl_first_seen"].setdefault(str(i), now)

    eligible = sorted(int(k) for k in st["serv_seen"])
    void = [i for i in range(NARB) if i not in eligible]

    print(f"\nSELF-REPORT -- which instances proved they can latch at all")
    print("-" * 78)
    print(f"  serv (A1 ^ A2), must be set: {len(eligible)}/{NARB}")
    if void:
        print(f"  NEVER SERVED, excluded from the denominator: {void}")
        print(f"  (an instance that never served has not shown its detectors "
              f"work; its zeros below prove nothing)")
    else:
        print(f"  every instance has served -- all {NARB} contribute exposure")

    print(f"\nTHE RESULT")
    print("-" * 78)
    for label, idx, first in (
            ("A. both clients acknowledged (A1 . A2)", viol,
             st["viol_first_seen"]),
            ("B. both grants high, width-filtered (g1 . g2)", ovl,
             st["ovl_first_seen"])):
        live = [i for i in idx if i in eligible]
        if not live:
            print(f"  {label}: clean on all {len(eligible)} eligible instances")
        else:
            print(f"  {label}: *** FIRED on {len(live)} instance(s) ***")
            for i in live:
                t = first.get(str(i))
                dt = (t - st["loaded_at"]) / 3600 if t else float("nan")
                print(f"        instance {i}, first seen {dt:.2f} h after load")

    # -- 6. exposure and the bound -------------------------------------------
    elapsed = now - st["loaded_at"]
    print(f"\nEXPOSURE")
    print("-" * 78)
    print(f"  elapsed: {elapsed/3600:.2f} h")
    if rate:
        events = len(eligible) * elapsed * rate
        print(f"  handshake rate: {rate/1e6:.2f} MHz per instance (measured)")
        print(f"  arbitration events: {len(eligible)} instances x "
              f"{elapsed:.0f} s x {rate:.3e} Hz = {events:.3e}")
        nviol = len([i for i in viol if i in eligible])
        novl = len([i for i in ovl if i in eligible])
        if events <= 0:
            print("\n  no exposure accumulated yet -- poll again later.")
        elif nviol == 0 and novl == 0:
            print(f"\n  no failure of either kind in {events:.3e} arbitration "
                  f"events.")
            print(f"  Rule of Three 95% upper bound on the failure rate: "
                  f"{3/events:.3e} per arbitration")
            print(f"  -> MTBF at least {events/3:.3e} arbitrations")
            if rate:
                yrs = (events / 3) / rate / 3600 / 24 / 365
                print(f"     = {yrs:.3e} years for ONE arbiter running "
                      f"flat out at {rate/1e6:.2f} MHz")
            # The denominator above is EVERY arbitration, contested or not.
            # That is right for the two structural modes -- either can occur on
            # any arbitration -- and wrong for metastability, which needs both
            # requests inside the mutex's decision aperture.  Uncontested
            # arbitrations are settled by structural exclusion and never had a
            # chance to fail, yet they inflate the count all the same.  The
            # contested fraction has never been measured; an aperture-over-
            # period estimate puts it near 1e-3.  Printed every poll on purpose:
            # this number is quoted straight out of the cron output, and without
            # the caveat attached to it, it is quoted as the wrong quantity.
            print("\n  NOTE: this bounds the TOTAL failure rate per "
                  "arbitration, not the")
            print("  metastability rate.  Uncontested arbitrations cannot fail "
                  "that way but")
            print("  are counted anyway; the contested fraction is unmeasured "
                  "and may be")
            print("  ~1e-3, which would weaken the metastability bound by ~3 "
                  "orders.")
            print("  See verify/MTBF.md, \"The exposure figure is not a "
                  "metastability bound\".")
        else:
            print(f"\n  {nviol} protocol violation(s), {novl} grant "
                  f"overlap(s) -- this is a finding, not a bound.")
    else:
        print("  handshake rate not yet measured; run without --light once.")

    st["last_poll_at"] = now
    st["poll_count"] += 1
    save_state(st)
    print(f"\npoll #{st['poll_count']}, state saved to {STATE}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
