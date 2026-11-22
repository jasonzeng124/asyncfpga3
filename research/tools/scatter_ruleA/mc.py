#!/usr/bin/env python3
"""mc.py HWDIR FIDDIR OUTDIR --runs SCALE:DRAW[,SCALE:DRAW...] [--base xray|nextpnr]
For each run: gen.py's exact factors at region 0.16*SCALE, wire 0.126*SCALE (draw
DRAW), applied by scale_sdf to the nextpnr-named SDF, then tighten.py on it.
Appends one row per run to OUTDIR/results.tsv; keeps each tighten log."""
import argparse, os, re, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REGION1, WIRE1 = 0.16, 0.126
SEC = {"A": "A. the request", "H": "H. the ack", "I": "I. the stage", "F": "F. a fast-fall"}


def parse(log):
    out, cur = {k: [] for k in SEC}, None
    for l in open(log):
        if re.match(r"^[A-Z]\. ", l):
            cur = next((k for k, v in SEC.items() if l.startswith(v)), None)
            continue
        m = re.match(r"^  (\S+)\s.*?\bmargin\s+(-?\d+)", l)
        if m and cur:
            out[cur].append((int(m.group(2)), m.group(1)))
            g = re.search(r"\bguard\s+(\d+)", l)
            if cur == "A" and g:      # rule A before its guardband: req - peak
                out.setdefault("Araw", []).append((int(m.group(2)) + int(g.group(1)), m.group(1)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("hw"); ap.add_argument("fid"); ap.add_argument("out")
    ap.add_argument("--runs", required=True)
    ap.add_argument("--base", default="xray")
    ap.add_argument("--watch", default="urig.udut.uori2")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    os.environ.setdefault("GLS_SDF_FIELD", "band")
    os.environ["GLS_SCATTER_MODE"] = "wire"
    os.environ.setdefault("GLS_SCATTER", "0.126")
    os.environ.setdefault("GLS_SCATTER_REGION", "0.16")
    import scale_sdf
    gen, work = scale_sdf.load_gen(a.fid)
    res = os.path.join(a.out, "results.tsv")
    if not os.path.exists(res):
        open(res, "w").write("scale\tdraw\tbase\tA_min\tA_min_cell\tA_neg\tA_neg_cells\twatch_A\t"
                             "H_min\tH_min_cell\tI_min\tI_min_cell\tF_min\tunmatched\tAraw_min\tAraw_min_cell\tAraw_neg\twatch_Araw\n")
    for run in a.runs.split(","):
        sc, draw = run.split(":")
        t0 = time.time()
        d = os.path.join(a.out, "s%s_d%s_%s" % (sc, draw, a.base))
        os.makedirs(d, exist_ok=True)
        scale_sdf.set_draw(gen, REGION1 * float(sc), WIRE1 * float(sc), draw)
        io_f, ic_f, st = scale_sdf.factors(gen)
        sdf = os.path.join(d, "gcd_hw.sdf")
        st = scale_sdf.apply(a.hw, a.base, io_f, ic_f, st, sdf)
        for f in ("gcd_hw_routed.json", "toolchain.txt"):
            if not os.path.exists(os.path.join(d, f)) and os.path.exists(os.path.join(a.hw, f)):
                os.symlink(os.path.join(a.hw, f), os.path.join(d, f))
        log = os.path.join(d, "tighten.log")
        subprocess.run([sys.executable, os.path.join(scale_sdf.REPO, "cells/verify/tighten.py"), sdf,
                        "--osc", "dhk", "--osc", "invhk"], stdout=open(log, "w"),
                       stderr=subprocess.STDOUT, env=dict(os.environ, PYTHONHASHSEED="0"))
        os.remove(sdf)
        p = parse(log)
        A = sorted(p["A"])
        if not A:
            sys.exit("no rule A lines in " + log)
        mn = lambda k: (str(min(p[k])[0]), min(p[k])[1]) if p[k] else ("-", "-")
        neg = [c for m, c in A if m < 0]
        w = [str(m) for m, c in A if c == a.watch]
        row = [sc, draw, a.base, str(A[0][0]), A[0][1], str(len(neg)), ",".join(neg) or "-",
               w[0] if w else "-", *mn("H"), *mn("I"), mn("F")[0],
               "io%d/ic%d" % (st.get("IO_unmatched", 0), st.get("IC_unmatched", 0))]
        R = sorted(p.get("Araw", []))
        row += [str(R[0][0]), R[0][1], str(sum(1 for m, c in R if m < 0)),
                ([str(m) for m, c in R if c == a.watch] or ["-"])[0]]
        open(res, "a").write("\t".join(row) + "\n")
        print("\t".join(row), "%.0fs" % (time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
