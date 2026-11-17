#!/usr/bin/env python3
"""Measure carry_ro_top's 64 rings on the board and place the die in the CARRY4 / MUXF7 band.

    cd cells
    python3 hw/carry_ring/carry_measure.py BIT PREDICTED.tsv [OUTDIR]

BIT is the committed bitstream, PREDICTED.tsv carry_predict.py's per-ring terms
of THAT route (both committed before any run).  OUTDIR defaults to
build/hw/carry_ro_top; raw per-group logs go to OUTDIR/raw/gNN.log, the
per-ring table to OUTDIR/measured.tsv.

THE HARNESS IS hw/ro_many_measure.py's, imported, not copied: its xsdb TCL
(one session and one jtag lock per group, configure once on the first group,
constants / group echo / 24 async liveness samples / poison read / clear-run-
stop windows), its hw_server bring-up and its scan decode.  carry_ro_top.v
keeps ro_many_top's JTAG register map bit for bit, with G = 8 groups.
Environment as ro_many_measure.py: RO_WINDOW_MS (default 4000), RO_REPEATS
(default 2), RO_FORCE=1 to re-measure groups on disk, RO_OFFLINE=1 to judge
logs already on disk, VIVADO_LAB for xsdb / hw_server.  Wrap the call in
hw/board.sh (the board lock).

EXIT STATUS: 2 if the readback fails its own checks (constants, group echo,
liveness, poison, overflow, zero counts) or a ring is not the ring that was
asked for (period outside what any band position could give); otherwise
carry_fit.py's verdict (0 PASS, 1 FAIL).  Last lines: CARRY_BAND, F7_BAND,
LUT_BAND and === PASS === / === FAIL ===.
"""
import csv
import importlib.util
import os
import pathlib
import re
import statistics
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
CELLS = HERE.parent.parent
sys.path.insert(0, str(CELLS / "hw"))
sys.path.insert(0, str(CELLS / "verify"))
import ro_many_measure as rm                               # noqa: E402

B, G = 8, 8
KINDS = ["L8", "C1", "C4", "F8", "C16", "L16", "C32", "F16"]   # KIND[(g+b)%8], carry_ro_top.v


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    bit = pathlib.Path(sys.argv[1]).resolve()
    predp = pathlib.Path(sys.argv[2]).resolve()
    out = pathlib.Path(sys.argv[3] if len(sys.argv) > 3 else CELLS / "build/hw/carry_ro_top").resolve()
    out.mkdir(parents=True, exist_ok=True)
    # point the ro_many harness at this design
    rm.OUT, rm.BIT, rm.RAW = out, bit, out / "raw"
    rm.G = G
    groups = [g for g in rm.parse_groups(os.environ.get("RO_GROUPS", "0-%d" % (G - 1))) if g < G]
    pred = {(int(r["g"]), int(r["b"])): r for r in csv.DictReader(open(predp), delimiter="\t")}
    if len(pred) != B * G:
        print("PREDICTED.tsv has %d rings, want %d" % (len(pred), B * G))
        return 2
    print("bitstream    %s  md5 %s" % (bit, subprocess.run(["md5sum", str(bit)], capture_output=True,
                                                          text=True).stdout.split()[0]))
    if not rm.OFFLINE:
        if not rm.XSDB.exists():
            print("xsdb not found at %s (set VIVADO_LAB)" % rm.XSDB)
            return 2
        if not rm.ensure_hw_server():
            print("hw_server did not come up on tcp:3121")
            return 2
    rm.RAW.mkdir(parents=True, exist_ok=True)
    logs, programmed = {}, False
    for g in groups:
        cached = rm.RAW / ("g%02d.log" % g)
        if cached.exists() and not rm.FORCE and ("GROUPDONE %d" % g) in cached.read_text():
            logs[g] = cached.read_text()
            print("group %d   cached" % g)
            continue
        if rm.OFFLINE:
            print("group %d   not on disk -- skipped (RO_OFFLINE)" % g)
            continue
        log = rm.run_group(g, program=not programmed)
        programmed = True
        logs[g] = log
        print("group %d   %s" % (g, "ok" if ("GROUPDONE %d" % g) in log else "SESSION DID NOT COMPLETE"))
    done = [g for g in groups if ("GROUPDONE %d" % g) in logs.get(g, "")]
    if not done:
        print("no group completed; nothing is a measurement")
        return 2

    # ---- readback checks, as ro_many_measure.py --------------------------
    bad = []
    for g in done:
        L = logs[g]
        for m in re.finditer(r"^CONST (\d+) (\d+) ([0-9a-fA-F]+)$", L, re.M):
            a, f = int(m.group(2)), rm.field(rm.decode(m.group(3)))
            if a in rm.CONSTS and not (f["tag"] == rm.TAG and f["addr"] == a and f["data"] == rm.CONSTS[a]):
                bad.append("group %d const addr %d read %08x" % (g, a, f["data"]))
        m = re.search(r"^ECHO (\d+) ([0-9a-fA-F]+)$", L, re.M)
        f = rm.field(rm.decode(m.group(2))) if m else None
        if not f or f["tag"] != rm.TAG or f["addr"] != 13 or f["data"] != g:
            bad.append("group %d: group echo %s" % (g, f and f["data"]))
        samples = [rm.field(rm.decode(h))["data"] for h in re.findall(r"^SAMPLE \d+ ([0-9a-fA-F]+)$", L, re.M)]
        for b in range(B):
            bits = [(v >> b) & 1 for v in samples]
            if not bits or not (0 < sum(bits) < len(bits)):
                bad.append("group %d slot %d (%s) not turning" % (g, b, KINDS[(g + b) % 8]))
        for m in re.finditer(r"^POISON (\d+) (\d+) ([0-9a-fA-F]+)$", L, re.M):
            if rm.field(rm.decode(m.group(3)))["data"] != 0xFFFFFFFF:
                bad.append("group %d: poison read missing (control dead)" % g)
    meas = {}
    for g in done:
        L = logs[g]
        win = {int(r): int(us) for _g, r, us in re.findall(r"^WINDOW (\d+) (\d+) (\d+)$", L, re.M)}
        counts = {}
        for _g, rep, a, h in re.findall(r"^COUNT (\d+) (\d+) (\d+) ([0-9a-fA-F]+)$", L, re.M):
            f = rm.field(rm.decode(h))
            a = int(a)
            if f["tag"] != rm.TAG or f["addr"] != a:
                bad.append("group %d rep %s slot %d misaligned" % (g, rep, a))
            if f["ovf"]:
                bad.append("group %d slot %d OVERFLOW (lower RO_WINDOW_MS)" % (g, a))
            if f["data"] in (0, 0xFFFFFFFF):
                bad.append("group %d slot %d count %08x" % (g, a, f["data"]))
            counts.setdefault(a, []).append((int(rep), f["data"]))
        for b, cs in counts.items():
            per = [win[rep] * 1e6 / c for rep, c in cs if c and c != 0xFFFFFFFF]
            if per:
                meas[(g, b)] = (statistics.mean(per), (max(per) - min(per)) / statistics.mean(per))
    print("readback     %d group(s), %d ring(s) measured, %d problem(s)" % (len(done), len(meas), len(bad)))
    for x in bad[:12]:
        print("   ", x)
    if bad:
        print("=== FAIL === the scan path does not read back what the design holds; nothing is a measurement")
        return 2

    # ---- is each count the ring that was asked for? ----------------------
    # Any band position x in [0.1, 0.5], y in [0, 1] bounds the period; a ring
    # outside that by 5% is not this ring (mux mis-select) or not this model.
    wrong = []
    for (g, b), (p, _s) in meas.items():
        t = pred[(g, b)]
        lo, R, C, F = (float(t[k]) for k in ("lo_ps", "R_ps", "C_ps", "F_ps"))
        if not (0.95 * (lo + 0.1 * R) <= p <= 1.05 * (lo + 0.5 * R + C + F)):
            wrong.append("g%d.b%d %s%s: %.0f ps, possible %.0f..%.0f" % (
                g, b, t["kind"], t["n"], p, 0.95 * (lo + 0.1 * R), 1.05 * (lo + 0.5 * R + C + F)))
    spread = sorted(s for _p, s in meas.values())
    print("windows      %d x %d ms per group; window-to-window spread median %.3f%%, max %.3f%%" % (
        rm.REPEATS, rm.WINDOW_MS, 100 * statistics.median(spread), 100 * spread[-1]))
    tsv = out / "measured.tsv"
    with open(tsv, "w") as f:
        f.write("g\tb\tkind\tn\tmeasured_ps\tspread\n")
        for (g, b), (p, s) in sorted(meas.items()):
            t = pred[(g, b)]
            f.write("%d\t%d\t%s\t%s\t%.1f\t%.6f\n" % (g, b, t["kind"], t["n"], p, s))
    print("per-ring table -> %s" % tsv)
    if wrong:
        print("=== FAIL === %d ring(s) outside every band position: %s" % (len(wrong), "; ".join(wrong[:6])))
        return 2
    print()
    spec = importlib.util.spec_from_file_location("carry_fit", HERE / "carry_fit.py")
    cf = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cf)
    rows, skipped = cf.load(str(predp), str(tsv))
    return cf.judge(rows, skipped)


if __name__ == "__main__":
    sys.exit(main())
