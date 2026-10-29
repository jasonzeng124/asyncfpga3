#!/usr/bin/env python3
"""Does this gate-level simulation reproduce what the board showed?

    python3 cells/gls/fid/acceptance.py [--items id,id] [--sdf-cmd CMD]
                                        [--netlist-cmd CMD] [--corner min|typ|max]
                                        [--ro-many-data DIR] [--work DIR]
                                        [--vectors 0-15] [--report out.json]
                                        [--stack default|full] [--band 0.38]

The yardstick for the board-fidelity GLS (research/PROGRAM.md, "THE
priority").  It runs one GLS CONFIGURATION over every silicon datum in
research/data/fid/inventory.json and reports, per item, prediction against
measurement for timings, and for failures whether the simulation fails the way
the silicon did.  HARD items (well-established data) and SOFT items (evidence
to look into) are reported separately; only a hard mismatch says the model is
wrong.

THE CONFIGURATION.  By default today's GLS: cells/gls/gen.py over nextpnr's
routed JSON and nextpnr's SDF.  Two hooks replace one piece each:

  --sdf-cmd CMD      CMD <routed.json> <out.sdf> must write the SDF to use in
                     place of nextpnr's (F1: a prjxray delay calculator).  It
                     may carry min:typ:max and separate rise/fall; --corner
                     picks the triple member for the ring tests, and gen.py
                     reads what it reads.
  --netlist-cmd CMD  CMD <design.fasm> <routed.json> <out.json> must write a
                     routed-JSON-shaped netlist built FROM THE FASM (F2), which
                     then replaces nextpnr's routed JSON as gen.py's input.
                     Without it the netlist is nextpnr's routed JSON, which
                     does not read the FASM at all: a bitstream bug is
                     invisible to it BY CONSTRUCTION, and the bitstream items
                     say so instead of simulating twice.

  --stack full       THE FULL BOARD-FIDELITY STACK (research/data/fid/
                     fullstack.md), in place of both hooks:
                       netlist  decoded from a BITSTREAM by fasm2net.py --bit:
                                the patched run reads the build's own .bit
                                (assembled from the FASM with the build's
                                fasm2frames + xc7frames2bit when there is
                                none), the unpatched run the buggy FASM
                                assembled the same way (bit_control.to_bit);
                       delays   xray_delay.py's prjxray RC-tree SDF of the
                                route, re-keyed onto the bits' netlist;
                                --corner picks its column for gen.py
                                (GLS_SDF_FIELD: min = FAST_MIN, typ =
                                SLOW_MIN, max = SLOW_MAX, band = FAST_MIN +
                                --band * (SLOW_MAX - FAST_MIN));
                       model    GLS_MODEL=fid primitives (fid_core.vh).
                     gcd items run gls/'s steps on that netlist, one vector
                     at a time; soak (DSP) items run soak_fid.py ... bit.  A
                     buggy bitstream the decoder REFUSES counts as a sim FAIL,
                     but the item is then flagged WEAK: no wrong answer was
                     simulated (fid/README.md, dsp_areg).  The ring items read
                     the prjxray SDF at the same column.

THE ITEMS (kind in inventory.json):

  ring_route       ro_top's five rings.  Period = the sum over the ring's loop
                   of rise + fall arc delays from the configured SDF (each arc
                   is crossed once by each edge; an inverting ring alternates).
                   Measured on two August routes that cannot be rebuilt, so
                   the comparison is ACROSS routes: soft.
  ring_population  ro_many_top's 128 rings, the hard ring test.  Needs the
                   measured route's per-ring table (hw/ro_many_measure.py
                   RO_OFFLINE=1 RO_MEAS_TSV=...) and that route's routed JSON
                   and SDF: --ro-many-data DIR holding measured.tsv,
                   ro_many_top_routed.json, ro_many_top.sdf.  Without it the
                   item is BLOCKED, and today's rebuild's predicted
                   distribution is printed for reference only.
  bitstream_bug    a deterministic FASM-writer bug re-applied to a FASM by
                   verify/fasm_audit.py --write-unpatched.  The sim must PASS
                   the patched FASM (the board did, after the fix) and FAIL the
                   unpatched one (the board did, before it).
  property / record  not simulated: the oracle, its source line and why.

Every item's oracle is quoted with its source line from inventory.json.
Exit 0 when no HARD item mismatches (BLOCKED is not a pass; it is reported).
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import statistics
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CELLS = HERE.parent.parent
REPO = CELLS.parent
GLS = CELLS / "gls"
sys.path.insert(0, str(CELLS / "verify"))
sys.path.insert(0, str(REPO / "bdc"))

CORNER = {"min": 0, "typ": 1, "max": 2}
CORNERS = sorted(CORNER) + ["band"]     # band: fast_min + b * (slow_max - fast_min)
STACKS = ("default", "full")


# ------------------------------------------------------------------ the SDF

RE_CELL = re.compile(r"\(CELL\s*\(CELLTYPE\s+\"[^\"]*\"\)\s*\(INSTANCE\s+([^)]*)\)", re.S)
RE_TRIPLE = r"\((-?[\d.]*):(-?[\d.]*):(-?[\d.]*)\)"
RE_IOPATH = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+" + RE_TRIPLE + r"(?:\s+" + RE_TRIPLE + r")?\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+" + RE_TRIPLE + r"(?:\s+" + RE_TRIPLE + r")?\)")


def _pick(groups, k, band=None):
    """(rise, fall) at corner k from a 3- or 6-number match; a missing fall
    triple means fall = rise (SDF's own rule).  k == "band": min + band *
    (max - min) of each triple, as gen.py's GLS_SDF_FIELD=band reads it."""
    def num(x):
        return float(x) if x not in ("", None) else None
    r = [num(g) for g in groups[:3]]
    f = [num(g) for g in groups[3:6]] if groups[3] is not None else r
    if k == "band":
        def b(t):
            lo, hi = t[0], t[2]
            if lo is None or hi is None:
                raise ValueError("band needs both ends of the triple: %r" % (t,))
            return lo + band * (hi - lo)
        return b(r), b(f)
    rise = r[k] if r[k] is not None else next(x for x in r if x is not None)
    fall = f[k] if f[k] is not None else next(x for x in f if x is not None)
    return rise, fall


def unesc(s):
    return s.replace("\\", "")


def parse_sdf_rf(path, corner="max", band=0.38):
    """{src_pin: [(dst_pin, rise_ps, fall_ps)]} for every IOPATH and
    INTERCONNECT; pins are 'instance/port' with SDF escapes removed.  Units are
    taken as ps (nextpnr's TIMESCALE is 1ps; an SDF in ns is scaled)."""
    k = "band" if corner == "band" else CORNER[corner]
    text = Path(path).read_text()
    scale = 1000.0 if re.search(r"\(TIMESCALE\s+1\s*ns\)", text) else 1.0
    edges = {}
    pos = 0
    cells = [(m.start(), unesc(m.group(1).strip())) for m in RE_CELL.finditer(text)]
    cells.append((len(text), None))
    for (start, inst), (end, _) in zip(cells, cells[1:]):
        body = text[start:end]
        for m in RE_IOPATH.finditer(body):
            a, b = unesc(m.group(1)), unesc(m.group(2))
            if a.startswith("(") or "(" in a:
                a = re.sub(r"^\((?:posedge|negedge)\s+", "", a)
            r, f = _pick(m.groups()[2:], k, band)
            edges.setdefault(f"{inst}/{a}", []).append((f"{inst}/{b}", r * scale, f * scale))
        for m in RE_IC.finditer(body):
            r, f = _pick(m.groups()[2:], k, band)
            edges.setdefault(unesc(m.group(1)), []).append((unesc(m.group(2)), r * scale, f * scale))
    del pos
    return edges


def ring_period(edges, prefix, exclude=()):
    """Walk the ring under `prefix` from its inverter once around; -> (period
    ps = sum of rise + fall over the loop, links walked) or (None, reason)."""
    def mine(pin):
        inst = pin.rpartition("/")[0]
        return inst.startswith(prefix) and inst not in exclude
    start = f"{prefix}inv/O6"
    if start not in edges:
        return None, f"no arcs out of {start}"
    total, pin, seen = 0.0, start, set()
    while True:
        nxt = [(d, r, f) for d, r, f in edges.get(pin, ()) if mine(d)]
        if len(nxt) != 1:
            return None, f"{pin} has {len(nxt)} in-ring successors"
        dst, r, f = nxt[0]
        total += r + f
        pin = dst
        if pin == start:
            return total, None
        if pin in seen:
            return None, f"walk revisited {pin}"
        seen.add(pin)


# ---------------------------------------------------------------- the config

# --stack full: where the pieces live (the same defaults the tools use)
XRAY_DB = Path(os.environ.get("XRAY_DB", "/root/dev2/lib/xray/prjxray-db/zynq7"))   # xray_delay.py's
TC = Path(os.environ.get("TC", "/root/dev2/lib/fpgatoolchain"))                       # fasm2net/bit_control's
PRJXRAY = Path(os.environ.get("PRJXRAY_SRC", str(TC / "openxc7-src/prjxray")))


def git_rev(path):
    r = subprocess.run(["git", "-C", str(path), "rev-parse", "--short=8", "HEAD"],
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else "unknown"


class Config:
    def __init__(self, a, work):
        self.sdf_cmd = a.sdf_cmd
        self.netlist_cmd = a.netlist_cmd
        self.corner = a.corner
        self.work = work
        self.stack = getattr(a, "stack", "default") or "default"
        self.band = getattr(a, "band", 0.38)
        if self.stack == "full" and (self.sdf_cmd or self.netlist_cmd):
            raise ValueError("--stack full fixes the netlist (the bits) and the SDF (xray_delay.py); "
                             "it does not take --sdf-cmd or --netlist-cmd")
        if self.corner == "band" and self.stack != "full":
            # nextpnr's SDF has one number per arc: band would silently read it
            raise ValueError("--corner band reads an SDF with a fast and a slow end: --stack full only")

    def describe(self):
        if self.stack != "full":
            return {"sdf": self.sdf_cmd or "nextpnr routed SDF",
                    "netlist": self.netlist_cmd or "nextpnr routed JSON (FASM not read)",
                    "corner": self.corner}
        d = {"stack": "full",
             "netlist": "fasm2net.py --bit: decoded from the bitstream (patched: the build's .bit; "
                        "unpatched: the buggy FASM through the build's fasm2frames + xc7frames2bit)",
             "sdf": f"xray_delay.py prjxray RC tree (db {XRAY_DB}, rev {git_rev(XRAY_DB)}), "
                    "re-keyed onto the bits' netlist",
             "model": "GLS_MODEL=fid",
             "corner": self.corner,
             "gls_env": self.gls_env()}
        extra = {k: v for k, v in os.environ.items()
                 if k.startswith("GLS_") and k not in d["gls_env"] and k != "GLS_WORK"}
        if extra:
            d["inherited_env"] = extra
        return d

    def gls_env(self):
        """The environment gen.py / soak_fid.py read for this stack ({} by default)."""
        if self.stack != "full":
            return {}
        e = {"GLS_MODEL": "fid", "GLS_SDF_FIELD": self.corner}
        if self.corner == "band":
            e["GLS_SDF_BAND"] = repr(self.band)
        return e

    def xray_sdf(self, routed_json, nextpnr_sdf, tag):
        """xray_delay.py's SDF for this route, cached by the md5 of its inputs."""
        key = md5(routed_json)[:8] + md5(nextpnr_sdf)[:8]
        out = self.work / f"{tag}.xray.{key}.sdf"
        if out.exists():
            return out
        tmp = out.with_suffix(".part")
        env = {**os.environ, "PYTHONPATH": f"{PRJXRAY}:{TC / 'openxc7/lib/python'}",
               "XRAY_DB": str(XRAY_DB)}
        r = subprocess.run([sys.executable, str(HERE / "xray_delay.py"), "--routed", str(routed_json),
                            "--sdf", str(nextpnr_sdf), "--out", str(tmp)], env=env,
                           capture_output=True, text=True)
        (self.work / f"{tag}.xray.log").write_text(r.stdout + r.stderr)
        if r.returncode or not tmp.exists():
            raise RuntimeError(f"xray_delay.py failed (rc {r.returncode}), see {self.work / f'{tag}.xray.log'}")
        tmp.rename(out)
        return out

    def sdf_for(self, routed_json, nextpnr_sdf, tag):
        if self.stack == "full":
            return self.xray_sdf(routed_json, nextpnr_sdf, tag)
        if not self.sdf_cmd:
            return Path(nextpnr_sdf)
        out = self.work / f"{tag}.alt.sdf"
        subprocess.run(shlex.split(self.sdf_cmd) + [str(routed_json), str(out)], check=True)
        return out

    def netlist_for(self, fasm, routed_json, tag):
        """-> (netlist json path, True if it was built from the FASM)."""
        if not self.netlist_cmd:
            return Path(routed_json), False
        out = self.work / f"{tag}.fromfasm.json"
        subprocess.run(shlex.split(self.netlist_cmd) + [str(fasm), str(routed_json), str(out)],
                       check=True)
        return out, True


def md5(path):
    return hashlib.md5(Path(path).read_bytes()).hexdigest()


# ----------------------------------------------------------------- the items

def run_ring_route(item, cfg, inv_root):
    rd = REPO / item["route_dir"]
    sdf = cfg.sdf_for(rd / "ro_top_routed.json", rd / "ro_top.sdf", "ro_top")
    edges = parse_sdf_rf(sdf, cfg.corner, cfg.band)
    o = item["oracle"]
    rows = []
    for i, (n, meas) in enumerate(zip(o["links"], o["measured_ps"])):
        pred, err = ring_period(edges, f"ro[{i}].", exclude={f"ro[{i}].bg"})
        if pred is None:
            rows.append({"ring": i, "links": n, "error": err})
            continue
        rows.append({"ring": i, "links": n, "predicted_ps": round(pred),
                     "measured_ps": meas, "err_pct": round(100 * (pred / meas - 1), 1)})
    errs = [r["err_pct"] for r in rows if "err_pct" in r]
    return {"rows": rows, "route": str(rd), "sdf_md5": md5(sdf)[:8],
            "verdict": "compared across routes (the measured route is gone)",
            "median_err_pct": statistics.median(errs) if errs else None,
            "ok": None}


def ring_len(g, b):
    return [7, 15, 31, 63][(g + b) % 4]


def run_ring_population(item, cfg, data, tol=5.0):
    out = {}
    rd = REPO / item["route_dir"]
    if rd.exists():
        sdf = cfg.sdf_for(rd / "ro_many_top_routed.json", rd / "ro_many_top.sdf", "ro_many_today")
        edges = parse_sdf_rf(sdf, cfg.corner, cfg.band)
        by = {}
        for g in range(16):
            for b in range(8):
                p, _ = ring_period(edges, f"grp[{g}].ro[{b}].")
                if p:
                    by.setdefault(ring_len(g, b), []).append(p)
        out["today_route_predicted_median_ps"] = {n: round(statistics.median(v)) for n, v in sorted(by.items())}
    if not data:
        out.update(verdict="BLOCKED: the measured route's per-ring table and SDF are not "
                   "in the repo (see inventory 'needs')", ok=None, blocked=True)
        return out
    d = Path(data)
    sdf = cfg.sdf_for(d / "ro_many_top_routed.json", d / "ro_many_top.sdf", "ro_many_meas")
    edges = parse_sdf_rf(sdf, cfg.corner, cfg.band)
    rows, errs = [], []
    for line in (d / "measured.tsv").read_text().splitlines()[1:]:
        g, b, n, meas = line.split("\t")[:4]
        g, b, meas = int(g), int(b), float(meas)
        p, err = ring_period(edges, f"grp[{g}].ro[{b}].")
        if p is None:
            rows.append({"g": g, "b": b, "error": err})
            continue
        e = 100 * (p / meas - 1)
        errs.append((int(n), e))
        rows.append({"g": g, "b": b, "links": int(n), "predicted_ps": round(p),
                     "measured_ps": meas, "err_pct": round(e, 2)})
    allv = sorted(e for _, e in errs)
    bylen = {n: statistics.median([e for m, e in errs if m == n]) for n in sorted({m for m, _ in errs})}
    slower = sum(1 for e in allv if e < 0)   # predicted < measured: the silicon is slower
    med = statistics.median(allv)
    # The pass criterion (PROGRAM.md: "within the measured scatter"): the
    # median error and every length's median error inside +/-tol, and -- at
    # the slow corner -- no ring slower than the model's slow max at all.
    ok = abs(med) <= tol and all(abs(v) <= tol for v in bylen.values())
    why = [f"median {med:+.1f}% and per-length medians within +/-{tol}%"]
    if cfg.corner == "max":
        ok = ok and slower == 0
        why.append(f"{slower} ring(s) slower than the slow-max prediction (must be 0)")
    out.update(rows=rows, n=len(allv), median_err_pct=med,
               p05=allv[int(0.05 * len(allv))], p95=allv[int(0.95 * len(allv)) - 1],
               median_by_length=bylen, rings_slower_than_model=slower,
               ok=ok, verdict="per-ring comparison on the measured route: " + "; ".join(why))
    return out


def gls_gcd(netlist_json, sdf, work, vectors, env_extra=None):
    """gls/build.sh's steps on (netlist, sdf) in `work`; then each vector.
    env_extra (--stack full: GLS_MODEL=fid, GLS_SDF_FIELD...) is read by
    gen.py, and GLS_MODEL=fid compiles run_baked.vvp with -DGLS_FID, as
    gls/build.sh does.  -> {vec: (complete, line)}, gate ok"""
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    shutil.copy(netlist_json, work / "routed.json")
    shutil.copy(sdf, work / "routed.sdf")
    (work / "provenance.txt").write_text(
        f"acceptance.py: routed.json md5 {md5(work / 'routed.json')}  sdf md5 {md5(work / 'routed.sdf')}\n")
    env = {**os.environ, **(env_extra or {}), "GLS_WORK": str(work)}
    fid = ["-DGLS_FID", f"-I{GLS}"] if env.get("GLS_MODEL") == "fid" else []
    for cmd in (["gen.py"], ["gen_probe.py", "urig."], ["gen_chan.py"], ["gen_signals.py"]):
        subprocess.run([sys.executable, str(GLS / cmd[0]), *cmd[1:]], cwd=work, env=env,
                       check=True, stdout=open(work / "gen.log", "a"), stderr=subprocess.STDOUT)
    subprocess.run(["iverilog", "-gspecify", "-I.", "-o", "gate.vvp", str(GLS / "tb_gate.v"),
                    "netlist.v", str(GLS / "prims.v")], cwd=work, check=True,
                   stdout=open(work / "compile.log", "a"), stderr=subprocess.STDOUT)
    subprocess.run(["iverilog", "-gspecify", "-DGLS_TRANSPORT_IC", *fid, "-I.", "-o", "run_baked.vvp",
                    str(GLS / "tb_run.v"), "netlist_baked.v", str(GLS / "prims.v")], cwd=work,
                   check=True, stdout=open(work / "compile.log", "a"), stderr=subprocess.STDOUT)
    gate = subprocess.run(["vvp", "gate.vvp"], cwd=work, capture_output=True, text=True).stdout
    gate_ok = "ANNOTATE_DONE" in gate and not re.search(r"SDF (WARNING|ERROR)", gate)
    res = {}
    for v in vectors:
        out = subprocess.run(["vvp", "run_baked.vvp", f"+VEC={v}", "+TEND=150000", "+QUIET=200000"],
                             cwd=work, capture_output=True, text=True).stdout
        m = re.search(r"RESULT .*", out)
        line = m.group(0) if m else "no verdict line"
        mm = re.search(r"laps=(\d+) errs=(\d+) oks=(\d+)", line)
        complete = bool(mm) and int(mm.group(2)) == 0 and int(mm.group(3)) > 0
        res[v] = (complete, line)
    for pat in ("*.vvp", "netlist*.v", "annot.sdf", "routed.json", "routed.sdf"):
        for f in work.glob(pat):      # ~100 MB per run; the logs and maps stay
            f.unlink()
    return res, gate_ok


def gls_fusion(route_dir, netlist_json, sdf, work):
    """fusion_bench's own routed GLS (fast + stalled, C-derived oracle) on a
    copy of the route with the netlist/SDF swapped in.  -> {kind: status}"""
    import fusion_bench as fb
    P = fb.parse          # bdc/parse.py, as fusion_bench imported it
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(route_dir, work, ignore=shutil.ignore_patterns("gls", "*.vvp", "seed*"))
    seed = sorted(Path(route_dir).glob("seed*"))[0]
    shutil.copytree(seed / "pnr", work / "pnr")
    for f in ("tb_fast.v", "tb_stalled.v"):
        shutil.copy(seed / f, work / f)
    shutil.copy(netlist_json, work / "pnr/soak_routed.json")
    shutil.copy(sdf, work / "pnr/soak.sdf")
    func = P.parse_module((work / "input.mlir").read_text())[0]
    r = fb.simulate_route(work, func, strict_gls=False, parse=fb.kernel_metrics)
    for pat in ("*.vvp", "netlist*.v", "annot.sdf"):
        for f in work.rglob(pat):
            f.unlink()
    return r["routed_gls"]


def run_bitstream_bug(item, cfg, vectors):
    if cfg.stack == "full":
        return run_bitstream_bug_full(item, cfg, vectors)
    import fasm_audit as fa
    rd = REPO / item["route_dir"]
    if item["id"].startswith("lutpinmap"):
        routed, sdf0, fasm = rd / "gcd_hw_routed.json", rd / "gcd_hw.sdf", rd / "gcd_hw.fasm"
    else:
        seed = sorted(rd.glob("seed*"))[0] / "pnr"
        routed, sdf0, fasm = seed / "soak_routed.json", seed / "soak.sdf", seed / "soak.fasm"
    out = {"route": str(rd)}
    for f, want in item.get("expect_md5", {}).items():
        got = md5(rd / f)[:8]
        out.setdefault("md5", {})[f] = f"{got} ({'matches' if got == want else 'DIFFERS from'} {want})"
    work = cfg.work / item["id"]
    work.mkdir(parents=True, exist_ok=True)
    bad_fasm = work / "unpatched.fasm"
    nchanged = fa.write_unpatched(item["bug"], str(routed), str(fasm), str(bad_fasm))
    out["unpatched_lines_changed"] = nchanged
    sdf = cfg.sdf_for(routed, sdf0, item["id"])
    runs = {}
    for tag, fz in (("patched", fasm), ("unpatched", bad_fasm)):
        net, from_fasm = cfg.netlist_for(fz, routed, f"{item['id']}.{tag}")
        key = md5(net) + md5(sdf)
        prior = next((r for r in runs.values() if r["input"] == key), None)
        if prior is not None:
            runs[tag] = {**prior, "note": f"simulation input identical to the {prior['tag']} "
                         f"run (the netlist does not read the FASM): result copied, not re-run"}
            runs[tag]["tag"] = tag
            continue
        if item["id"].startswith("lutpinmap"):
            res, gate_ok = gls_gcd(net, sdf, work / f"gls_{tag}", vectors)
            passed = all(c for c, _ in res.values())
            runs[tag] = {"tag": tag, "input": key, "from_fasm": from_fasm, "gate_ok": gate_ok,
                         "complete": f"{sum(c for c, _ in res.values())}/{len(res)}",
                         "vectors": {v: l for v, (c, l) in res.items()}, "sim_passes": passed}
        else:
            st = gls_fusion(rd, net, sdf, work / f"gls_{tag}")
            runs[tag] = {"tag": tag, "input": key, "from_fasm": from_fasm, "status": st,
                         "sim_passes": all(s == "pass" for s in st.values())}
    out["runs"] = runs
    good, bad = runs["patched"]["sim_passes"], runs["unpatched"]["sim_passes"]
    out["ok"] = good and not bad
    out["verdict"] = ("reproduces the board: passes the fixed bitstream, fails the buggy one"
                      if out["ok"] else
                      "MISS: the sim PASSES a bitstream the board failed" if good and bad else
                      "MISS: the sim fails the bitstream the board passed" if not good else "?")
    return out


# ------------------------------------------------- bitstream items, full stack

REFUSAL = re.compile(r"\s+\d+\s+(REFUSED|CONTENTION|FLOATING)")


def to_bit(fasm, out_dir):
    """the build's fasm2frames + xc7frames2bit (bit_control.to_bit)"""
    import bit_control as bc
    out_dir.mkdir(parents=True, exist_ok=True)
    return bc.to_bit(fasm, out_dir)


def decode_bits(bit, routed, sdf, out):
    """fasm2net.py --bit (--allow: a refusal is reported, not a crash) and
    fasm_equiv.py.  -> {json, sdf, refused: [...], equiv: verdict line}"""
    r = subprocess.run([sys.executable, str(HERE / "fasm2net.py"), "--bit", str(bit), "--out", str(out),
                        "--names", str(routed), "--sdf", str(sdf), "--allow"],
                       capture_output=True, text=True)
    (out.parent / f"{out.name}.fasm2net.log").write_text(r.stdout + r.stderr)
    if not (out / "fasm_routed.json").exists():
        raise RuntimeError(f"fasm2net.py --bit {bit} wrote no netlist: {(r.stdout + r.stderr)[-300:]}")
    rep = (out / "report.txt").read_text() if (out / "report.txt").exists() else ""
    refused = [ln.strip() for ln in rep.splitlines() if REFUSAL.match(ln)]
    e = subprocess.run([sys.executable, str(HERE / "fasm_equiv.py"), str(routed), str(out / "fasm_routed.json"),
                        str(out / "routes.tsv"), str(out / "stubs.tsv"), "--out", str(out / "equiv.txt"),
                        "--max", "4"], capture_output=True, text=True)
    v = [ln for ln in e.stdout.splitlines() if ln.startswith("VERDICT")]
    return {"json": out / "fasm_routed.json", "sdf": out / "fasm.sdf", "refused": refused,
            "equiv": v[0] if v else f"no verdict (rc {e.returncode})"}


def soak_bit(seeddir, bit, sdf, work, env_extra):
    """soak_fid.py SEEDDIR WORK bit --bit B with GLS_SDF = the prjxray SDF.
    -> (passes, SOAK lines, refused?)"""
    env = {**os.environ, **env_extra, "GLS_SDF": str(sdf)}
    r = subprocess.run([sys.executable, str(HERE / "soak_fid.py"), str(seeddir), str(work), "bit",
                        "--bit", str(bit)], cwd=str(REPO / "bdc"), env=env, capture_output=True, text=True)
    (Path(str(work) + ".log")).write_text(r.stdout + r.stderr)
    lines = [ln for ln in r.stdout.splitlines() if ln.startswith("SOAK")]
    verdict = [ln for ln in lines if ln.startswith("SOAK_VERDICT")]
    if not verdict:     # a crash or a truncated run is never a pass, nor a detection
        raise RuntimeError(f"soak_fid.py printed no SOAK_VERDICT (rc {r.returncode}), see {work}.log")
    passes = verdict[0] == "SOAK_VERDICT PASS" and r.returncode == 0
    refused = any("decode to something the model refuses" in ln for ln in lines)
    return passes, lines, refused


def judge_full(runs):
    """-> (ok, weak, verdict) from the patched/unpatched runs of the full stack.
    A buggy bitstream that fails only because the decoder refuses it is a FAIL
    of the sim, but a WEAK one: no wrong answer was simulated."""
    good, bad = runs["patched"], runs["unpatched"]
    ungated = [t for t, x in runs.items() if x.get("gate_ok") is False]
    if ungated:     # delays that did not all land: the run is not a result either way
        return None, False, ("INVALID: the ANNOTATE_DONE gate is not clean on the %s run(s)"
                             % "/".join(ungated))
    if not good["sim_passes"]:
        why = "refused by the decoder" if good.get("refused") else "the simulation fails"
        return False, False, f"MISS: the sim fails the bitstream the board passed ({why})"
    if bad["sim_passes"]:
        return False, False, "MISS: the sim PASSES a bitstream the board failed"
    if bad.get("refused"):
        return True, True, ("reproduces the board ONLY BY REFUSAL (WEAK): the decoder refuses the buggy "
                            "configuration, no wrong answer was simulated: " + "; ".join(bad["refused"])[:200])
    return True, False, ("reproduces the board: the bits-decoded full stack passes the fixed bitstream "
                         "and fails the buggy one in simulation")


def run_bitstream_bug_full(item, cfg, vectors):
    import fasm_audit as fa
    rd = REPO / item["route_dir"]
    gcd = item["id"].startswith("lutpinmap")
    if gcd:
        seeddir = None
        routed, sdf0, fasm, built = (rd / "gcd_hw_routed.json", rd / "gcd_hw.sdf", rd / "gcd_hw.fasm",
                                     rd / "gcd_hw.bit")
    else:
        seeddir = sorted(rd.glob("seed*"))[0]
        routed, sdf0, fasm, built = (seeddir / "pnr/soak_routed.json", seeddir / "pnr/soak.sdf",
                                     seeddir / "pnr/soak.fasm", seeddir / "pnr/soak.bit")
    out = {"route": str(rd), "stack": "full"}
    for f, want in item.get("expect_md5", {}).items():
        got = md5(rd / f)[:8]
        out.setdefault("md5", {})[f] = f"{got} ({'matches' if got == want else 'DIFFERS from'} {want})"
    work = cfg.work / item["id"]
    work.mkdir(parents=True, exist_ok=True)
    bad_fasm = work / "unpatched.fasm"
    nchanged = fa.write_unpatched(item["bug"], str(routed), str(fasm), str(bad_fasm))
    out["unpatched_lines_changed"] = nchanged
    if nchanged == 0:
        out.update(ok=None, blocked=True, verdict="BLOCKED: the unpatched writer changes no FASM line on "
                   "this route, so the two bitstreams are the same: nothing to discriminate")
        return out
    sdf = cfg.sdf_for(routed, sdf0, item["id"])
    # the bitstreams: the build's own .bit for the patched run; the buggy FASM
    # assembled by the same tools.  Re-assembling the patched FASM too tells
    # whether those tools reproduce the build's .bit, i.e. whether the two
    # bitstreams differ by the bug alone.
    pbit_asm = to_bit(fasm, work / "bit_patched")
    if built.exists():
        pbit = built
        out["patched_bit"] = (f"{built} (the build's; the FASM re-assembled "
                              f"{'is byte-identical' if pbit_asm.read_bytes() == built.read_bytes() else 'DIFFERS'})")
    else:
        pbit = pbit_asm
        out["patched_bit"] = f"{pbit_asm} (no .bit in the route: assembled from its FASM)"
    ubit = to_bit(bad_fasm, work / "bit_unpatched")
    out["md5s"] = {"routed_json": md5(routed), "nextpnr_sdf": md5(sdf0), "xray_sdf": md5(sdf),
                   "patched_bit": md5(pbit), "unpatched_bit": md5(ubit)}
    if md5(pbit) == md5(ubit):
        raise RuntimeError("the unpatched bitstream is byte-identical to the patched one")
    env = cfg.gls_env()
    runs = {}
    for tag, bit in (("patched", pbit), ("unpatched", ubit)):
        if gcd:
            dec = decode_bits(bit, routed, sdf, work / f"fid_{tag}")
            run = {"tag": tag, "from_bits": True, "bit_md5": md5(bit), "equivalence": dec["equiv"],
                   "refused": dec["refused"]}
            if dec["refused"]:
                run.update(sim_passes=False, complete="not simulated: decoder refused")
            else:
                res, gate_ok = gls_gcd(dec["json"], dec["sdf"], work / f"gls_{tag}", vectors, env)
                run.update(gate_ok=gate_ok, complete=f"{sum(c for c, _ in res.values())}/{len(res)}",
                           vectors={v: ln for v, (c, ln) in res.items()},
                           never_complete=[v for v, (c, _) in res.items() if not c],
                           sim_passes=all(c for c, _ in res.values()))
                for f in (dec["json"], dec["sdf"]):     # ~100 MB; report/equiv/maps stay
                    f.unlink()
        else:
            passes, lines, refused = soak_bit(seeddir, bit, sdf, work / f"gls_{tag}", env)
            run = {"tag": tag, "from_bits": True, "bit_md5": md5(bit), "status": " / ".join(lines),
                   "refused": [ln for ln in lines if "refuses" in ln] if refused else [],
                   "sim_passes": passes}
        runs[tag] = run
    out["runs"] = runs
    out["ok"], out["weak"], out["verdict"] = judge_full(runs)
    return out


# ------------------------------------------------------------------- report

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--inventory", type=Path, default=REPO / "research/data/fid/inventory.json")
    ap.add_argument("--items", help="comma-separated item ids (default: all)")
    ap.add_argument("--sdf-cmd")
    ap.add_argument("--netlist-cmd")
    ap.add_argument("--corner", choices=CORNERS, default="max",
                    help="SDF column; band (fast_min + --band * (slow_max - fast_min)) needs --stack full")
    ap.add_argument("--stack", choices=STACKS, default="default",
                    help="full: bits-decoded netlist + xray_delay.py SDF + GLS_MODEL=fid (see above)")
    ap.add_argument("--band", type=float, default=0.38,
                    help="--corner band's position in [fast min, slow max] (gen.py GLS_SDF_BAND)")
    ap.add_argument("--ro-many-data")
    ap.add_argument("--ring-tol", type=float, default=5.0,
                    help="ring128 pass band for the median errors, percent")
    ap.add_argument("--work", type=Path, default=REPO / "build/fid/acceptance")
    ap.add_argument("--vectors", default="0-15")
    ap.add_argument("--report", type=Path)
    a = ap.parse_args()
    lo, _, hi = a.vectors.partition("-")
    vectors = list(range(int(lo), int(hi or lo) + 1))
    a.work = a.work.resolve()
    a.work.mkdir(parents=True, exist_ok=True)
    try:
        cfg = Config(a, a.work)
    except ValueError as e:
        ap.error(str(e))
    inv = json.loads(a.inventory.read_text())
    want = set(a.items.split(",")) if a.items else None
    results = []
    for it in inv["items"]:
        if want and it["id"] not in want:
            continue
        kind = it["kind"]
        print(f"... {it['id']} ({kind}, {it['grade']})", flush=True)
        try:
            if kind == "ring_route":
                r = run_ring_route(it, cfg, inv)
            elif kind == "ring_population":
                r = run_ring_population(it, cfg, a.ro_many_data, a.ring_tol)
            elif kind == "bitstream_bug":
                r = run_bitstream_bug(it, cfg, vectors)
            else:
                r = {"verdict": "not simulated: " + it.get("reproducible", ""), "ok": None,
                     "not_run": True}
        except Exception as e:      # an item that cannot run is a row, not a crash
            r = {"verdict": f"ERROR: {type(e).__name__}: {e}", "ok": None, "error": True}
        results.append({"id": it["id"], "grade": it["grade"], "kind": kind,
                        "title": it["title"], "sources": it.get("sources", []),
                        "oracle": it.get("oracle"), **r})
    report = {"config": cfg.describe(), "results": results}
    if a.report:
        a.report.write_text(json.dumps(report, indent=1, default=str) + "\n")
    print_report(report)
    hard_bad = [r for r in results if r["grade"] == "hard" and r.get("ok") is False]
    return 1 if hard_bad else 0


def print_report(rep):
    print("\nGLS configuration:", json.dumps(rep["config"]))
    for grade in ("hard", "soft", "excluded"):
        rows = [r for r in rep["results"] if r["grade"] == grade]
        if not rows:
            continue
        print(f"\n==== {grade.upper()} ({len(rows)}) " + "=" * 50)
        for r in rows:
            st = {True: "MATCH", False: "MISMATCH", None: "-"}[r.get("ok")]
            if r.get("blocked"):
                st = "BLOCKED"
            if r.get("not_run"):
                st = "NOT RUN"
            if r.get("error"):
                st = "ERROR"
            if r.get("weak") and st == "MATCH":
                st = "MATCH (WEAK: by refusal)"
            print(f"\n[{st}] {r['id']}: {r['title']}")
            print(f"    source: {', '.join(r['sources'])}")
            print(f"    {r.get('verdict', '')}")
            if r["kind"] == "ring_route" and "rows" in r:
                for x in r["rows"]:
                    if "err_pct" in x:
                        print(f"      ring {x['ring']} ({x['links']:>3} links): predicted "
                              f"{x['predicted_ps']:>7} ps, measured {x['measured_ps']:>7} ps, "
                              f"error {x['err_pct']:+.1f}%")
                    else:
                        print(f"      ring {x['ring']}: {x['error']}")
            if r["kind"] == "ring_population":
                if "today_route_predicted_median_ps" in r:
                    print(f"      today's rebuild, predicted median period by length: "
                          f"{r['today_route_predicted_median_ps']} (reference only)")
                if "n" in r:
                    print(f"      n={r['n']}  median error {r['median_err_pct']:+.2f}%  "
                          f"p05 {r['p05']:+.1f}%  p95 {r['p95']:+.1f}%  by length "
                          f"{ {k: round(v, 1) for k, v in r['median_by_length'].items()} }  "
                          f"silicon slower than model on {r['rings_slower_than_model']}")
            if r["kind"] == "bitstream_bug" and "runs" in r and r.get("stack") == "full":
                print_full_bug(r)
            elif r["kind"] == "bitstream_bug" and "runs" in r:
                for k, v in r.get("md5", {}).items():
                    print(f"      {k} md5 {v}")
                print(f"      unpatched FASM: {r['unpatched_lines_changed']} line(s) differ")
                for tag in ("patched", "unpatched"):
                    x = r["runs"][tag]
                    what = x.get("complete") or x.get("status")
                    print(f"      {tag:9} sim {'PASSES' if x['sim_passes'] else 'FAILS'} "
                          f"({what}){'  [from FASM]' if x.get('from_fasm') else ''}"
                          f"{'  ' + x['note'] if 'note' in x else ''}")
            if r.get("oracle") and r["kind"] in ("bitstream_bug", "record", "property"):
                print(f"      board: {json.dumps(r['oracle'])[:240]}")


def print_full_bug(r):
    for k, v in r.get("md5", {}).items():
        print(f"      {k} md5 {v}")
    print(f"      unpatched FASM: {r['unpatched_lines_changed']} line(s) differ")
    print(f"      patched bit: {r['patched_bit']}")
    print("      md5: " + "  ".join(f"{k} {v[:8]}" for k, v in r["md5s"].items()))
    for tag in ("patched", "unpatched"):
        x = r["runs"][tag]
        what = x.get("complete") or x.get("status")
        print(f"      {tag:9} sim {'PASSES' if x['sim_passes'] else 'FAILS'} ({what})  [from the .bit]")
        if "equivalence" in x:
            print(f"                equivalence (information): {x['equivalence']}")
        if x.get("never_complete"):
            print(f"                never complete: {','.join(map(str, x['never_complete']))}")
        if x.get("gate_ok") is False:
            print("                ANNOTATE gate NOT clean (SDF warning/error or no ANNOTATE_DONE)")
        if x.get("refused"):
            print(f"                refused: {'; '.join(x['refused'])[:200]}")


if __name__ == "__main__":
    sys.exit(main())
