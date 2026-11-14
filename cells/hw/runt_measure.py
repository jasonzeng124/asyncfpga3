#!/usr/bin/env python3
"""Run H_RUNT(w) on the board: 128 C-element LUT loops, each forced by an
episode of a different routed width, T trials each, and judge the rig first.

    BD_RLOC=none NEXTPNR_FREQ=50 hw/build_hw.sh runt_top
    python3 hw/runt_measure.py --table      # instance -> cell table, no board
    python3 hw/runt_measure.py              # the measurement

WHAT IT MEASURES.  See hw/runt_top.v's header.  Per instance, summed over
RUNT_RUNS runs of RUNT_T trials:

    ones    trials q was 1 at the end of the window (captured)
    emit    trials q rose at least once            (trials - emit: rejected)
    multi   trials q rose at least twice           (the runt went round)
    late    trials q was still rising in the second half of the window

THE RIG JUDGES ITSELF BEFORE ANY NUMBER IS BELIEVED.  "=== RIG OK ===" only if
the scan path reads its constants, its control echo and the descriptor of
every instance back exactly as hw/runt_top.v's plan rule (mirrored below)
says; the ring clock is alive and the measured window is >= 1 us even with
the clock taken 10% fast; every run completed exactly T trials; every counter
decodes to an LFSR state; and every control behaved in every trial:

    NEG    ones = emit = multi = late = 0
    LONG   ones = emit = trials, multi = late = 0
    PULSE  ones = multi = late = 0, and k = 3 (~1.4 ns pulse) emit = trials --
           otherwise the edge counter's floor is above anything interesting and
           a zero multi count means nothing
    any    multi <= emit, late <= emit (a thermometer cannot skip a stage)
    masked (RUNT_SPLIT=1 only) every counter of a group that did not launch = 0

Otherwise "=== RIG FAIL: ... ===" and exit 1.  After RIG OK it prints the
H_RUNT lines: how many TEST instances showed >= 2 rising edges in >= 1 trial
("=== RUNT CIRCULATES ===" if any), how many were still oscillating late in
the window, and the per-instance capture fraction (also in the TSV, which is
what research/tools/runt_judge.py joins with the SDF prediction).

OUTPUT.  build/hw/runt_top/runt_measured.tsv (RUNT_TSV overrides): one
'# ' header line with the verdict and the build, then

    instance k ones multi_edge_trials trials kind ka kb group slot emit late raw

raw is every run's 32-bit counter word as read (LFSR states, hex,
late|multi|emit|ones), comma-separated -- what was on the wire, undecoded.
Raw session logs go to build/hw/runt_top/raw/, stamped with the bitstream's
md5; RUNT_OFFLINE=1 re-judges them without a board and refuses logs from a
different bitstream.

ENVIRONMENT
    RUNT_T        trials per run, default 250 (<= 254: 8-bit LFSR counters)
    RUNT_RUNS     runs, default 4 (1000 trials)
    RUNT_WEXP     window = 16 << RUNT_WEXP rclk cycles, default 3
    RUNT_CAL_MS   rclk calibration window, default 1000
    RUNT_SPLIT    1: also run each group ALONE (RUNT_SPLIT_RUNS each, default
                  1) -- the masked groups are a crosstalk control, and the
                  capture fraction alone vs together is reported
    RUNT_OFFLINE  1: judge raw logs already on disk
    RUNT_TSV      output path
    RUNT_OUT      build directory, default build/hw/runt_top
    VIVADO_LAB    as for hw/ro_many_measure.py
"""

import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = pathlib.Path(os.environ.get("RUNT_OUT", ROOT / "build/hw/runt_top"))
BIT = OUT / "runt_top.bit"
RAW = OUT / "raw"

VIVADO_LAB = pathlib.Path(os.environ.get(
    "VIVADO_LAB", "/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab"))
XSDB = VIVADO_LAB / "bin/xsdb"
HW_SERVER = VIVADO_LAB / "bin/hw_server"

# ---- must match hw/runt_top.v -------------------------------------------
G, S = 8, 16
NI = G * S
KC = 8
TAG = 0x96
CONSTS = {8: 0xDEADBEEF, 9: 0x5A5A1234, 10: 0x00000000}
KINDS = ["TEST", "NEG", "LONG", "PULSE"]
KSEQ = [0, 1, 0, 1, 2, 0, 1, 3, 0, 1, 2, 3]


def rot(i):
    return ((i % S) + (i // S)) % S


def kind(i):
    r = rot(i)
    return 1 if r == 0 else 2 if r == 8 else 3 if r in (4, 12) else 0


def ka(i):
    return KC if kind(i) == 1 else 0


def kb(i):
    r, g = rot(i), i // S
    kd = kind(i)
    if kd == 0:
        return KSEQ[(r - 1 - r // 4 + g) % 12]
    if kd == 1:
        return 0
    if kd == 2:
        return KC
    return (2 * g + (1 if r == 12 else 0)) % 4


def k_of(i):
    """The episode's chain length: KB for TEST/PULSE/LONG, -KA for NEG."""
    return -ka(i) if kind(i) == 1 else kb(i)


def lfsr8(x):
    return ((x << 1) & 0xFF) | (1 ^ (((x >> 7) ^ (x >> 5) ^ (x >> 4) ^ (x >> 3)) & 1))


DECODE = {}
_x = 0
for _n in range(255):
    DECODE[_x] = _n
    _x = lfsr8(_x)
assert len(DECODE) == 255 and 0xFF not in DECODE

# ---- control word (hw/runt_top.v hold[33:0]) -----------------------------
GO, ZERO, CAL = 0x10, 0x20, 0x40


def ctrl_word(T=0, gmask=0, wexp=0, inst=0):
    return (inst << 7) | (T << 14) | (gmask << 22) | (wexp << 30)


T = int(os.environ.get("RUNT_T", "250"))
RUNS = int(os.environ.get("RUNT_RUNS", "4"))
WEXP = int(os.environ.get("RUNT_WEXP", "3"))
CAL_MS = int(os.environ.get("RUNT_CAL_MS", "1000"))
SPLIT = os.environ.get("RUNT_SPLIT", "0") == "1"
SPLIT_RUNS = int(os.environ.get("RUNT_SPLIT_RUNS", "1"))
OFFLINE = os.environ.get("RUNT_OFFLINE", "0") == "1"
TSV = pathlib.Path(os.environ.get("RUNT_TSV", OUT / "runt_measured.tsv"))
N_SAMPLES = 24
CTRL_PROBE = ctrl_word(T=0x5A, gmask=0xA5, wexp=0x9, inst=0x33)


# ------------------------------------------------------------ instance table

def find_cell(cells, name):
    if name in cells:
        return name
    for n in cells:                      # a packer suffix such as $LUT6
        if n.startswith(name) and re.fullmatch(r"\$\w+", n[len(name):]):
            return n
    return None


def phys_pins(cell):
    """logical I<n> -> physical A<k>, nextpnr's X_ORIG_PORT_A<k> record (see
    verify/tighten.py orig_ports)."""
    out = {}
    for k in range(1, 7):
        v = cell.get("attributes", {}).get(f"X_ORIG_PORT_A{k}")
        if v and re.fullmatch(r"I\d+", v):
            out[v] = f"A{k}"
    return out


def write_table():
    """instance -> the cells the w prediction walks, checked against the
    netlist when one exists (routed preferred: it has the pin permutation)."""
    jpath = None
    for cand in (OUT / "runt_top_routed.json", OUT / "runt_top.json"):
        if cand.exists():
            jpath = cand
            break
    cells = {}
    if jpath:
        mods = json.loads(jpath.read_text())["modules"]
        top = mods.get("runt_top") or list(mods.values())[0]
        cells = top.get("cells", {})
    rows, missing = [], []
    for i in range(NI):
        kd = kind(i)
        p = f"inst[{i}]"
        dut = f"{p}.pl.u" if kd == 3 else f"{p}.ce.dut.u"
        logical = ({"a": "I0", "b": "I1", "rst": "I2"} if kd == 3 else
                   {"a": "I0", "b": "I1", "q": "I2", "rst": "I3"})
        ch_a = [f"{p}.da.chain.g[{j}].u" for j in range(ka(i))]
        ch_b = [f"{p}.db.chain.g[{j}].u" for j in range(kb(i))]
        want = [dut, f"{p}.fa", f"{p}.fb", f"{p}.t0", f"{p}.t1", f"{p}.t2"] + ch_a + ch_b
        pins = "-"
        if cells:
            found = {w: find_cell(cells, w) for w in want}
            missing += [w for w, f in found.items() if f is None]
            if found[dut]:
                pm = phys_pins(cells[found[dut]])
                if pm:
                    pins = ",".join(f"{s}={pm.get(l, '?')}" for s, l in logical.items())
        rows.append([i, i // S, i % S, KINDS[kd], ka(i), kb(i), k_of(i), dut,
                     ",".join(f"{s}={l}" for s, l in logical.items()), pins,
                     f"{p}.fa", f"{p}.fb", ",".join(ch_a) or "-", ",".join(ch_b) or "-",
                     f"{p}.t0"])
    path = OUT / "instances.tsv"
    OUT.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as f:
        f.write("# runt_top instance table; clock: bufg_rclk drives every "
                "fa/fb C pin; the thermometer t0/t1/t2 is clocked by the dut's "
                "output net q\n")
        f.write("instance\tgroup\tslot\tkind\tka\tkb\tk\tdut_cell\tlogical_pins\t"
                "physical_pins\tla_cell\tlb_cell\tchain_a\tchain_b\tthermo0_cell\n")
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"instance table -> {path}")
    if not jpath:
        print("  no netlist in the build directory; names are the plan's, unchecked")
        return 0
    print(f"  checked against {jpath.name}: "
          f"{'all names present' if not missing else f'{len(missing)} MISSING'}")
    for m in missing[:10]:
        print(f"    missing {m}")
    if jpath.name == "runt_top.json":
        print("  (synthesised netlist: physical pins appear only after a route)")
    return 1 if missing else 0


# ------------------------------------------------------------------ xsdb

TCL_HEAD = r"""
connect -url tcp:localhost:3121
targets -set -filter {name =~ "xc7z010*"}
@PROG@
jtag targets -set -filter {name =~ "xc7z010*"}

# Locked for the whole session: a background hw_server scan that lands in
# USER1 commits a random control word (see hw/ro_many_measure.py).
jtag lock 600000

set seq [jtag sequence]
set ctrl 0

proc u1 {addr} {
    global seq ctrl
    $seq clear
    $seq irshift -state IDLE -integer 6 0x02
    $seq drshift -capture -state IDLE -integer 48 [expr {$addr | $ctrl}]
    return [$seq run -hex]
}

# Both shifts end in IDLE, through Update-DR.  The first commits addr, the
# second captures what it selected.
proc rd {addr} {
    u1 $addr
    return [u1 $addr]
}

# bit 37 of the capture word = done; hex is little-endian bytes
proc isdone {h} {
    set b [scan [string range $h 8 9] %x]
    return [expr {($b >> 5) & 1}]
}
"""

TCL_SETUP = r"""
foreach a {8 9 10} {
    puts "CONST $a [rd $a]"
}
set ctrl @PROBE@
puts "ECHO [rd 13]"
set ctrl 0
u1 13
for {set i 0} {$i < @NI@} {incr i} {
    set ctrl [expr {$i << 7}]
    puts "DESC $i [rd 3]"
}
set ctrl 0
for {set k 0} {$k < @NS@} {incr k} {
    puts "SAMPLE [rd 12]"
}
set ctrl 0x40
u1 14
set t0 [clock microseconds]
after @CALMS@
set ctrl 0
u1 14
set t1 [clock microseconds]
puts "CALWIN [expr {$t1 - $t0}]"
puts "CAL [rd 14]"
jtag unlock
puts "SETUPDONE"
exit
"""

TCL_RUN = r"""
set base @BASE@
set ctrl [expr {$base | 0x20}]
u1 2
set ctrl $base
u1 2
set ctrl [expr {$base | 0x10}]
u1 2
set n 0
set s [u1 2]
while {![isdone $s] && $n < 500} {
    set s [u1 2]
    incr n
}
puts "POLLS $n [isdone $s]"
set ctrl $base
u1 2
puts "FINAL [rd 2]"
for {set i 0} {$i < @NI@} {incr i} {
    set ctrl [expr {$base | ($i << 7)}]
    puts "CNT $i [rd 0]"
}
jtag unlock
puts "RUNDONE @TAG@"
exit
"""


def tcl(body, program=False, **kw):
    s = TCL_HEAD.replace("@PROG@", f"fpga -f {BIT}" if program
                         else "# already configured") + body
    for k, v in kw.items():
        s = s.replace(f"@{k}@", str(v))
    return s


def ensure_hw_server():
    probe = ["bash", "-c", "exec 3<>/dev/tcp/127.0.0.1/3121 && echo up"]
    if "up" in subprocess.run(probe, capture_output=True, text=True).stdout:
        return True
    subprocess.Popen([str(HW_SERVER), "-d", "-s", "tcp::3121"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(30):
        if "up" in subprocess.run(probe, capture_output=True, text=True).stdout:
            return True
        subprocess.run(["sleep", "1"])
    return False


def session(name, script, timeout):
    path = OUT / f"runt_{name}.tcl"
    path.write_text(script)
    try:
        r = subprocess.run([str(XSDB), str(path)], capture_output=True,
                           text=True, timeout=timeout)
        log = r.stdout + r.stderr
    except subprocess.TimeoutExpired as e:
        log = ((e.stdout or b"").decode(errors="replace")
               + (e.stderr or b"").decode(errors="replace") + "\nTIMEOUT\n")
    (RAW / f"{name}.log").write_text(log)   # whatever happened
    return log


# -------------------------------------------------------------- decoding

def decode(hexstr):
    """xsdb -hex gives bytes least-significant first, LSB shifted first."""
    return int.from_bytes(bytes.fromhex(hexstr), "little")


def field(word):
    return dict(data=word & 0xFFFFFFFF, addr=(word >> 32) & 0xF,
                busy=(word >> 36) & 1, done=(word >> 37) & 1,
                tag=(word >> 40) & 0xFF)


def plan():
    """[(name, gmask, T)] -- the runs this invocation makes."""
    runs = [(f"all{r:02d}", 0xFF, T) for r in range(RUNS)]
    if SPLIT:
        runs += [(f"g{g}r{r:02d}", 1 << g, T) for g in range(G)
                 for r in range(SPLIT_RUNS)]
    return runs


# ------------------------------------------------------------------ main

def main():
    if "--table" in sys.argv[1:]:
        return write_table()

    if not 1 <= T <= 254:
        print("RUNT_T must be 1..254 (8-bit LFSR counters)", file=sys.stderr)
        return 2
    if not BIT.exists():
        print(f"missing {BIT} -- BD_RLOC=none NEXTPNR_FREQ=50 hw/build_hw.sh "
              f"runt_top first", file=sys.stderr)
        return 2
    stamp = OUT / "toolchain.txt"
    if not stamp.exists():
        print("toolchain    UNSTAMPED -- build/hw/runt_top/toolchain.txt is "
              "missing; a result without its build is not a result",
              file=sys.stderr)
        return 2
    tc_line = stamp.read_text().splitlines()[0]
    print(f"toolchain    {tc_line}")
    md5 = hashlib.md5(BIT.read_bytes()).hexdigest()
    print(f"bitstream    {BIT} md5 {md5}")

    RAW.mkdir(parents=True, exist_ok=True)
    runs = plan()
    logs = {}
    if OFFLINE:
        stamp_md5 = (RAW / "bit.md5").read_text().strip() if (RAW / "bit.md5").exists() else ""
        if stamp_md5 != md5:
            print(f"raw logs on disk are from bitstream {stamp_md5 or '?'}, not "
                  f"this one; refusing to judge them", file=sys.stderr)
            return 2
        for name in ["setup"] + [r[0] for r in runs]:
            p = RAW / f"{name}.log"
            logs[name] = p.read_text() if p.exists() else ""
    else:
        if not XSDB.exists():
            print(f"xsdb not found at {XSDB}", file=sys.stderr)
            return 2
        if not ensure_hw_server():
            print("hw_server did not come up on tcp:3121", file=sys.stderr)
            return 2
        (RAW / "bit.md5").write_text(md5 + "\n")
        logs["setup"] = session("setup", tcl(
            TCL_SETUP, program=True, PROBE=hex(CTRL_PROBE), NI=NI, NS=N_SAMPLES,
            CALMS=CAL_MS), timeout=300 + CAL_MS / 1000)
        print(f"setup        {'ok' if 'SETUPDONE' in logs['setup'] else 'DID NOT COMPLETE'}")
        for name, gm, t in runs:
            logs[name] = session(name, tcl(
                TCL_RUN, BASE=hex(ctrl_word(T=t, gmask=gm, wexp=WEXP)), NI=NI,
                TAG=name), timeout=300)
            print(f"run {name:8s} {'ok' if f'RUNDONE {name}' in logs[name] else 'DID NOT COMPLETE'}")

    why = []          # reasons for RIG FAIL

    # ---- the scan path ---------------------------------------------------
    su = logs.get("setup", "")
    if "SETUPDONE" not in su:
        why.append("setup session did not complete")
    nconst = 0
    for m in re.finditer(r"^CONST (\d+) ([0-9a-fA-F]+)$", su, re.M):
        a, f = int(m.group(1)), field(decode(m.group(2)))
        if f["tag"] == TAG and f["addr"] == a and f["data"] == CONSTS[a]:
            nconst += 1
    if nconst != 3:
        why.append(f"constants: {nconst} of 3 read back right")
    m = re.search(r"^ECHO ([0-9a-fA-F]+)$", su, re.M)
    f = field(decode(m.group(1))) if m else None
    if not f or f["tag"] != TAG or f["addr"] != 13 or f["data"] != (CTRL_PROBE >> 4):
        why.append("control echo (addr 13) did not return the word written")
    desc_bad = 0
    ndesc = 0
    for m in re.finditer(r"^DESC (\d+) ([0-9a-fA-F]+)$", su, re.M):
        i, f = int(m.group(1)), field(decode(m.group(2)))
        d = f["data"]
        ndesc += 1
        if not (f["tag"] == TAG and f["addr"] == 3 and d & 0xF == kb(i)
                and (d >> 4) & 0xF == ka(i) and (d >> 8) & 3 == kind(i)
                and (d >> 10) & 0x7F == i and (d >> 24) == NI):
            desc_bad += 1
            if desc_bad <= 5:
                print(f"  descriptor inst {i}: {d:08x}, plan kind {KINDS[kind(i)]} "
                      f"ka {ka(i)} kb {kb(i)}")
    if ndesc != NI or desc_bad:
        why.append(f"descriptors: {desc_bad} wrong, {NI - ndesc} missing -- the "
                   f"bitstream is not the plan this script judges against")
    samples = [field(decode(h))["data"] & 1
               for h in re.findall(r"^SAMPLE ([0-9a-fA-F]+)$", su, re.M)]
    if not samples or not 0 < sum(samples) < len(samples):
        why.append(f"rclk sampler stuck ({sum(samples)}/{len(samples)}) -- the "
                   f"ring clock is not running")

    # ---- the window --------------------------------------------------------
    f_mhz = None
    mw = re.search(r"^CALWIN (\d+)$", su, re.M)
    mc = re.search(r"^CAL ([0-9a-fA-F]+)$", su, re.M)
    if mw and mc:
        fc = field(decode(mc.group(1)))
        if fc["tag"] == TAG and fc["addr"] == 14 and fc["data"] not in (0, 0xFFFFFFFF):
            f_mhz = fc["data"] / int(mw.group(1))
    if f_mhz is None:
        why.append("rclk calibration did not read back")
        win_us = None
    else:
        cyc = 16 << WEXP
        win_us = cyc / (f_mhz * 1.10)       # the clock taken 10% fast
        print(f"rclk         {f_mhz:.2f} MHz; window {cyc} cycles = "
              f"{cyc / f_mhz:.2f} us ({win_us:.2f} us at +10%)")
        if win_us < 1.0:
            why.append(f"window {win_us:.2f} us < 1 us at +10% clock; raise RUNT_WEXP")

    # ---- the runs ----------------------------------------------------------
    acc = {i: dict(ones=0, emit=0, multi=0, late=0, trials=0, raw=[]) for i in range(NI)}
    masked = {i: dict(ones=0, emit=0, multi=0, late=0, trials=0) for i in range(NI)}
    alone = {i: dict(ones=0, trials=0) for i in range(NI)}
    for name, gm, t in runs:
        lg = logs.get(name, "")
        if f"RUNDONE {name}" not in lg:
            why.append(f"run {name} did not complete")
            continue
        mp = re.search(r"^POLLS (\d+) (\d)$", lg, re.M)
        if not mp or mp.group(2) != "1":
            why.append(f"run {name}: done never seen")
            continue
        mf = re.search(r"^FINAL ([0-9a-fA-F]+)$", lg, re.M)
        ff = field(decode(mf.group(1))) if mf else None
        if (not ff or ff["tag"] != TAG or ff["addr"] != 2
                or ff["data"] & 0xFF != t or (ff["data"] >> 16) & 0xFF != t
                or (ff["data"] >> 24) != gm or (ff["data"] >> 8) & 7 != 0):
            why.append(f"run {name}: status {ff['data'] if ff else 0:08x} is not "
                       f"{t} trials of gmask {gm:02x} back in IDLE")
            continue
        got = 0
        for m in re.finditer(r"^CNT (\d+) ([0-9a-fA-F]+)$", lg, re.M):
            i, f = int(m.group(1)), field(decode(m.group(2)))
            got += 1
            if f["tag"] != TAG or f["addr"] != 0 or f["data"] == 0xFFFFFFFF:
                why.append(f"run {name} inst {i}: misaligned or poisoned read")
                continue
            vals = [DECODE.get((f["data"] >> (8 * b)) & 0xFF) for b in range(4)]
            if None in vals:
                why.append(f"run {name} inst {i}: counter state the LFSR never reaches")
                continue
            ones, emit, multi, late = vals
            launched = (gm >> (i // S)) & 1
            if gm == 0xFF:
                a = acc[i]
                a["raw"].append(f"{f['data']:08x}")
            elif launched:
                a = alone[i]
                a["ones"] += ones
                a["trials"] += t
                continue
            else:
                a = masked[i]
            a["ones"] += ones
            a["emit"] += emit
            a["multi"] += multi
            a["late"] += late
            a["trials"] += t
        if got != NI:
            why.append(f"run {name}: {got} of {NI} counter words came back")

    # ---- the controls ------------------------------------------------------
    ctl_bad = []
    for i in range(NI):
        a, kd = acc[i], kind(i)
        n = a["trials"]
        o, e, mu, la = a["ones"], a["emit"], a["multi"], a["late"]
        tag = f"inst {i} {KINDS[kd]} k={k_of(i)}: ones {o} emit {e} multi {mu} late {la} of {n}"
        if mu > e or la > e:
            ctl_bad.append(f"{tag} (thermometer out of order)")
        if kd == 1 and (o or e or mu or la):
            ctl_bad.append(tag)
        elif kd == 2 and (o != n or e != n or mu or la):
            ctl_bad.append(tag)
        elif kd == 3 and (o or mu or la or (kb(i) == 3 and e != n)):
            ctl_bad.append(tag)
        mk = masked[i]
        if mk["trials"] and (mk["ones"] or mk["emit"] or mk["multi"] or mk["late"]):
            ctl_bad.append(f"inst {i} counted while its group was MASKED: {mk}")
    if any(acc[i]["trials"] == 0 for i in range(NI)):
        why.append("no all-group trials were tallied")
    if ctl_bad:
        print(f"\n{len(ctl_bad)} control violation(s):")
        for c in ctl_bad[:20]:
            print(f"    {c}")
        why.append(f"{len(ctl_bad)} control instance(s) misbehaved")

    # ---- the TSV, whatever the verdict -------------------------------------
    verdict = "OK" if not why else "FAIL: " + "; ".join(why)
    TSV.parent.mkdir(parents=True, exist_ok=True)
    with open(TSV, "w") as f:
        f.write(f"# rig {verdict} | {tc_line} | bit md5 {md5} | T {T} x {RUNS} runs"
                f" | wexp {WEXP} | rclk {f_mhz if f_mhz else 0:.3f} MHz\n")
        f.write("instance\tk\tones\tmulti_edge_trials\ttrials\tkind\tka\tkb\t"
                "group\tslot\temit\tlate\traw\n")
        for i in range(NI):
            a = acc[i]
            f.write(f"{i}\t{k_of(i)}\t{a['ones']}\t{a['multi']}\t{a['trials']}\t"
                    f"{KINDS[kind(i)]}\t{ka(i)}\t{kb(i)}\t{i // S}\t{i % S}\t"
                    f"{a['emit']}\t{a['late']}\t{','.join(a['raw']) or '-'}\n")
    print(f"\nper-instance table -> {TSV}")

    if why:
        print(f"\n=== RIG FAIL: {'; '.join(why)} ===")
        return 1
    print("\n=== RIG OK ===")

    # ---- H_RUNT --------------------------------------------------------------
    test = [i for i in range(NI) if kind(i) == 0]
    n = acc[test[0]]["trials"]
    multi = [i for i in test if acc[i]["multi"]]
    late = [i for i in test if acc[i]["late"]]
    rej = [i for i in test if acc[i]["emit"] == 0]
    died = [i for i in test if acc[i]["emit"] > acc[i]["ones"] and not acc[i]["multi"]]
    missed = [i for i in test if acc[i]["ones"] > acc[i]["emit"]]
    print(f"\nH_RUNT  {len(test)} TEST instances x {n} trials, window "
          f"{16 << WEXP} rclk cycles")
    print(f"H_RUNT  multi-edge (>= 2 rising edges in >= 1 trial): {len(multi)} of "
          f"{len(test)}")
    print(f"H_RUNT  still rising late in the window in >= 1 trial: {len(late)}")
    print(f"H_RUNT  rejected outright (no edge in any trial): {len(rej)}")
    print(f"H_RUNT  emitted a pulse that then died (emit > ones, multi = 0): {len(died)}")
    if missed:
        print(f"H_RUNT  WARNING {len(missed)} instance(s) ended at 1 more often than q "
              f"was seen to rise -- the edge counter missed real edges; the multi "
              f"counts are a floor, not a count")
    pulse = {}
    for i in range(NI):
        if kind(i) == 3:
            pulse.setdefault(kb(i), []).append(acc[i]["emit"] / acc[i]["trials"])
    print("H_RUNT  open-LUT pulse (PULSE, loop cut) emitted fraction by k: "
          + "  ".join(f"k={k}: {min(v):.3f}..{max(v):.3f}" for k, v in sorted(pulse.items())))
    if multi:
        print("\n=== RUNT CIRCULATES ===")
        for i in multi:
            a = acc[i]
            print(f"    inst {i:3d} k={k_of(i)}  multi {a['multi']}/{n}  late "
                  f"{a['late']}/{n}  ones {a['ones']}/{n}")
    else:
        print("\n=== NO RUNT CIRCULATED (above the edge counter's floor) ===")

    print("\ncapture fraction (ones / trials), TEST instances by k:")
    for k in sorted({kb(i) for i in test}):
        row = sorted((acc[i]["ones"] / n, i) for i in test if kb(i) == k)
        print(f"  k={k}  " + " ".join(f"{i}:{fr:.2f}" for fr, i in row))

    if SPLIT:
        d = [abs(alone[i]["ones"] / alone[i]["trials"] - acc[i]["ones"] / n)
             for i in test if alone[i]["trials"]]
        if d:
            print(f"\nalone vs together: |delta capture fraction| median "
                  f"{sorted(d)[len(d) // 2]:.3f}, max {max(d):.3f} over {len(d)} "
                  f"TEST instances; masked groups read zero throughout")
    return 0


if __name__ == "__main__":
    sys.exit(main())
