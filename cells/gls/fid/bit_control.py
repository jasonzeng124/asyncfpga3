#!/usr/bin/env python3
"""
bit_control.py -- one deterministic bitstream bug, re-applied to a route,
must be caught by the bitstream-built simulation.

    bit_control.py ROUTE_DIR KIND [--work DIR] [--good] [--gls]

KIND (F4 acceptance inventory names):
  dsp_constpins      fasm_audit --write-unpatched constpins-packer: INMODE0..4,
                     ALUMODE2/3, OPMODE6 get no tile-constant bit (the August
                     packer half of nextpnr-xilinx-dsp-constpins.patch)
  dsp_constpins_inv  ... constpins-inv: the bussed IS_<pin>[i]_INVERTED lookup
                     never flips, so the tile bit carries the net, not the value
  dsp_areg           ... areg: ZAREG/ZBREG_2_*CASCREG_1 written as !ACASCREG.
                     Harmless whenever ACASCREG=0 (every route of this flow), so
                     the control then INJECTS the mechanism: those bits cleared
  lut_pinmap         ... pinmap: the run-together X_ORIG_PORT parse.  Harmless
                     when every run-together pin is GND-tied (gcd_hw today), so
                     the control then injects the mechanism on live pins
                     (inject_pinmap.py)
  lut_pinmap_live    always that injection, whatever the real writer does

ROUTE_DIR is a fusion_bench / flow.sh route (pnr/soak.{fasm,json,sdf},
pnr/soak_routed.json, tb_*.v) or a build_hw.sh dir (<d>.fasm, <d>_routed.json,
<d>.sdf).  Steps: write the buggy FASM; fasm2frames + xc7frames2bit (the
build's own tools and db) to a .bit; fasm2net.py --bit; fasm_equiv.py against
the routed JSON; with --gls, the GLS of the bitstream-built netlist (soak_fid.py
for a soak route).  --good runs the unmodified bitstream through the same steps
first and requires it to pass -- a control that cannot pass the good bitstream
proves nothing.

Output: one line, exit status 0 / 1 / 2:
  CONTROL <kind> DETECTED: <how>      the bitstream-built flow failed the bug
  CONTROL <kind> MISSED: <why>        it did not (the control failed)
  CONTROL <kind> ERROR: <why>         could not run (or --good failed)
"""
import argparse, os, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CELLS = HERE.parent.parent
TC = os.environ.get("TC", "/root/dev2/lib/fpgatoolchain")
DB = os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7")
PART = os.environ.get("PART", "xc7z010clg400-1")
PRJ = os.path.join(TC, "openxc7-src/prjxray")
WRITER = {"dsp_constpins": "constpins-packer", "dsp_constpins_inv": "constpins-inv",
          "dsp_areg": "areg", "lut_pinmap": "pinmap", "lut_pinmap_live": "pinmap"}


def sh(cmd, log=None, **kw):
    r = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **kw)
    if log:
        Path(log).write_text(r.stdout)
    return r.returncode, r.stdout


def to_bit(fasm, out_dir):
    env = dict(os.environ, PYTHONPATH=PRJ + ":" + os.path.join(TC, "openxc7/lib/python"))
    frames, bit = out_dir / "x.frames", out_dir / "x.bit"
    with open(frames, "w") as f:
        r = subprocess.run([sys.executable, os.path.join(PRJ, "utils/fasm2frames.py"), "--db-root", DB,
                            "--part", PART, str(fasm)], stdout=f, stderr=subprocess.PIPE, env=env, text=True)
    if r.returncode:
        raise RuntimeError("fasm2frames: " + r.stderr[-300:])
    rc, out = sh([os.path.join(TC, "openxc7/bin/xc7frames2bit"), "--part_file",
                  os.path.join(DB, PART, "part.yaml"), "--part_name", PART, "--frm_file", str(frames),
                  "--output_file", str(bit)])
    frames.unlink()
    if rc or not bit.exists():
        raise RuntimeError("xc7frames2bit: " + out[-300:])
    return bit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("route", type=Path)
    ap.add_argument("kind", choices=sorted(WRITER))
    ap.add_argument("--work", type=Path)
    ap.add_argument("--good", action="store_true")
    ap.add_argument("--gls", action="store_true")
    a = ap.parse_args()
    rd = a.route.resolve()
    if (rd / "pnr/soak_routed.json").exists():
        soak = True
        fasm, routed, sdf = rd / "pnr/soak.fasm", rd / "pnr/soak_routed.json", rd / "pnr/soak.sdf"
    else:
        soak = False
        d = rd.name
        fasm, routed, sdf = rd / ("%s.fasm" % d), rd / ("%s_routed.json" % d), rd / ("%s.sdf" % d)
    work = (a.work or Path("/tmp") / ("bitctl_%s_%s" % (rd.name, a.kind))).resolve()
    work.mkdir(parents=True, exist_ok=True)

    def say(word, msg, code):
        print("CONTROL %s %s: %s  [route %s]" % (a.kind, word, msg, rd))
        sys.exit(code)

    def check(bitfile, tag):
        """-> (equivalent?, equiv summary, gls verdict or None, gls summary)"""
        out = work / tag
        out.mkdir(exist_ok=True)
        rc, txt = sh([sys.executable, str(HERE / "fasm2net.py"), "--bit", str(bitfile), "--out", str(out / "fid"),
                      "--names", str(routed), "--sdf", str(sdf), "--allow"], out / "fasm2net.log")
        if not (out / "fid/fasm_routed.json").exists():
            raise RuntimeError("fasm2net failed: %s" % txt[-300:])
        rc, eq = sh([sys.executable, str(HERE / "fasm_equiv.py"), str(routed), str(out / "fid/fasm_routed.json"),
                     str(out / "fid/routes.tsv"), str(out / "fid/stubs.tsv"), "--max", "3"], out / "equiv.txt")
        v = [l for l in eq.splitlines() if l.startswith("VERDICT")]
        refused = [l.strip() for l in (out / "fid/report.txt").read_text().splitlines()
                   if re.match(r"\s+\d+\s+REFUSED", l)]
        gls = gsum = None
        if a.gls:
            if not soak:
                raise RuntimeError("--gls is implemented for soak routes; use build_fid.sh/run_fid.sh here")
            rc2, g = sh([sys.executable, str(HERE / "soak_fid.py"), str(rd), str(out / "gls"), "bit",
                         "--bit", str(bitfile)], out / "gls.txt", cwd=str(CELLS.parent / "bdc"))
            gls = rc2 == 0
            gsum = " / ".join(l for l in g.splitlines() if l.startswith("SOAK"))[:400]
        return rc == 0, ((v[0] if v else "no verdict") + ("; " + "; ".join(refused) if refused else "")), gls, gsum

    try:
        if a.good:
            (work / "good").mkdir(exist_ok=True)
            gbit = to_bit(fasm, work / "good")
            ok, esum, gls, gsum = check(gbit, "good")
            if not ok or gls is False:
                say("ERROR", "the GOOD bitstream does not pass: %s %s" % (esum, gsum or ""), 2)
        bug = work / "bug.fasm"
        rc, out = sh([sys.executable, str(CELLS / "verify/fasm_audit.py"), str(routed), str(fasm),
                      "--write-unpatched", WRITER[a.kind], str(bug)])
        how = "real unpatched writer (fasm_audit --write-unpatched %s)" % WRITER[a.kind]
        if a.kind == "lut_pinmap_live":
            rc, out = sh([sys.executable, str(HERE / "inject_pinmap.py"), str(routed), str(fasm), str(bug)])
            if rc:
                say("ERROR", "inject_pinmap: " + out[-200:], 2)
            how = "injected on live pins: " + out.splitlines()[0]
        elif sorted(open(bug).read().split()) == sorted(open(fasm).read().split()):
            # the real writer changes no bit on this route
            if a.kind == "dsp_areg":
                lines = [l for l in open(fasm).read().splitlines()
                         if not re.search(r"\.Z[AB]REG_2_[AB]CASCREG_1$", l.strip())]
                if len(lines) == len(open(fasm).read().splitlines()):
                    say("ERROR", "no DSP on this route: nothing to inject", 2)
                open(bug, "w").write("\n".join(lines) + "\n")
                how = ("real writer HARMLESS here (ACASCREG=0 everywhere); injected: every "
                       "Z[AB]REG_2_[AB]CASCREG_1 bit cleared")
            elif a.kind == "lut_pinmap":
                rc, out = sh([sys.executable, str(HERE / "inject_pinmap.py"), str(routed), str(fasm), str(bug)])
                if rc:
                    say("ERROR", "inject_pinmap: " + out[-200:], 2)
                how = "real writer HARMLESS here (functionally); injected on live pins: " + out.splitlines()[0]
            else:
                say("ERROR", "the real writer changes no bit and there is no injection for this kind", 2)
        elif a.kind == "lut_pinmap":
            how += " (if every changed LUT is GND-tied the control is expected to be MISSED)"
        (work / "bug").mkdir(exist_ok=True)
        bbit = to_bit(bug, work / "bug")
        ok, esum, gls, gsum = check(bbit, "bug")
    except (RuntimeError, OSError) as e:
        say("ERROR", str(e), 2)
    caught = (not ok) or (gls is False)
    msg = "%s | equivalence: %s%s" % (how, esum, (" | GLS: " + gsum) if gsum else "")
    say("DETECTED" if caught else "MISSED", msg, 0 if caught else 1)


if __name__ == "__main__":
    main()
