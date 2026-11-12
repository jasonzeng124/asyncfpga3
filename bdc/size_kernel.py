#!/usr/bin/env python3
"""Route-measured matched-delay sizes for a frontend kernel, by ratchet.

    python3 bdc/size_kernel.py --mlir build/frontend/xorshift/comp/handshake_transformed.mlir \\
        --output build/size/xorshift --seeds 1 2 3 4 [--start sizes.vh] \\
        [--headroom] [--fresh-seeds 9 10 11 12]

This is the procedure that produced research/data/{collatz,xorshift}_sizes_T3.vh
and ipow_dsp1_sizes_T9.vh, previously a set of scratch loops plus
research/data/collatz_ratchet_merge.py, made one tool:

1. RATCHET.  Iteration k routes the kernel with sizes T<k>.vh on every
   --seeds seed (bdc/fusion_bench.py --mlir --route: build, every post-route
   audit, routed GLS fast + stalled).  If every seed is clean on every
   enforced rule, stop: T<k> is the answer.  Otherwise T<k+1> is the per-cell
   MAXIMUM of
     - T<k> itself (nothing already in the sizes file is ever lowered),
     - each seed's `verify/tighten.py --emit` proposals (rule A request
       lengths, rule H acknowledge holds, rule I stage pads), and
     - each seed's verify/skew.py rule E asks, "fix: N more bd_delay
       element(s) on <link>", as current + N + 1, where current is T<k>'s
       value or, for a link T<k> does not size yet, the kernel's own
       DELAY_<LINK> default read from that iteration's dut.v.
   A cell T<k> does not yet carry takes the max of the proposals even when it
   is below the placeholder: that is the tightening the ratchet exists for.
   Merging across all seeds of an iteration is what makes the sizes a property
   of the seed SET rather than of one route (CLAUDE.md: one route is a sample).

2. HEADROOM (--headroom).  +1 link on every compute cell the sizes carry --
   every BD_SZ_UUT_* that is not a link (ULINK_*), an acknowledge hold (_UACK)
   or a stage pad (_SDELAY).  The recipe that made gcd_hw R2/R5 and ipow T9
   hold on seeds the ratchet never saw: each of T6..T8 had failed one fresh
   route in four to eight by one link.

3. FRESH SEEDS (--fresh-seeds).  The final sizes on seeds that never fed the
   ratchet: per-seed audits, GLS, latency.  This is the validation; seeds the
   sizes were fitted on are not evidence for them.

Enforced, per seed: tighten.py rules A, H, I, F (and B, C, K, L where the
design has them; rule D is the documented screen and is reported, not
enforced -- skew.py's rule E is its measurement), skew.py rule E, arb_fork.py
rule J, and both routed GLS runs.  Rules F and J have no delay knob: a
violation there stops the ratchet as NOT CONVERGED rather than padding
anything, because it is placement, not sizing.

BD_DSP and BDC_LINK_FASTFALL are read from the environment by the flow and
by bdc/emit.py respectively; whatever they are is recorded in summary.json.
Exit 0 when the final sizes are clean on every seed asked for, 1 otherwise.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

REPO = Path(__file__).resolve().parent.parent
CELLS = REPO / "cells"
BDC = REPO / "bdc"

ENFORCED = ("A", "B", "C", "F", "H", "I", "K", "L")   # tighten.py sections
RE_DEF = re.compile(r"^`define\s+(\S+)\s+(\d+)", re.M)
RE_ASK = re.compile(r"fix: (\d+) more bd_delay element\(s\) on (\S+)")


# ------------------------------------------------------------------ sizes

def read_sizes(text):
    return {k: int(v) for k, v in RE_DEF.findall(text)}


def write_sizes(path, sizes, header):
    Path(path).write_text("// " + header + "\n" + "".join(
        f"`define {k} {sizes[k]}\n" for k in sorted(sizes)))


def link_macro(link):
    """skew.py names the link by its instance under uut; tighten.py's macro
    for it is BD_SZ_ + the path, upper-cased, non-alphanumerics to _."""
    return "BD_SZ_UUT_" + re.sub(r"[^A-Za-z0-9]", "_", link).upper()


def dut_default(dut_text, macro):
    """The kernel's own DELAY_<X> default for macro BD_SZ_UUT_<X>, or None."""
    if not macro.startswith("BD_SZ_UUT_"):
        return None
    name = macro[len("BD_SZ_UUT_"):]
    m = re.search(r"parameter\s+DELAY_" + re.escape(name) + r"\s*=\s*(\d+)",
                  dut_text)
    return int(m.group(1)) if m else None


def skew_asks(skew_text):
    """[(macro, n)] for every rule E fix ask in a skew.py log."""
    return [(link_macro(link), int(n)) for n, link in RE_ASK.findall(skew_text)]


def merge(current, proposals, asks, dut_text):
    """One ratchet step.  -> (new sizes, [log lines]).

    current    the sizes the routes were built with
    proposals  [dict] tighten.py --emit output, one per route
    asks       [(macro, n)] rule E asks over all routes
    dut_text   that iteration's dut.v, for links current does not size
    """
    new, log = dict(current), []
    for prop in proposals:
        for k, v in prop.items():
            if k in current:
                if v > new[k]:
                    log.append(f"rule A/H/I: {k} {new[k]} -> {v}")
                    new[k] = v
            else:
                new[k] = max(new.get(k, 0), v)
    for k, n in asks:
        base = current.get(k)
        if base is None:
            base = dut_default(dut_text, k)
            if base is None:
                raise ValueError(f"rule E asks for {k}: no size macro and no "
                                 f"DELAY default for it in dut.v")
        want = base + n + 1
        if want > new.get(k, 0):
            log.append(f"rule E: {k} {base} + {n} + 1 -> {want}")
            new[k] = want
    lowered = [k for k in current if new[k] < current[k]]
    assert not lowered, lowered      # the invariant the whole method rests on
    return new, log


def headroom(sizes):
    """+1 on every compute cell's delay."""
    out = dict(sizes)
    for k in sizes:
        if not k.startswith("BD_SZ_UUT_"):
            continue
        rest = k[len("BD_SZ_UUT_"):]
        if rest.startswith("ULINK_") or rest.endswith("_UACK") \
                or rest.endswith("_SDELAY"):
            continue
        out[k] = sizes[k] + 1
    return out


# ----------------------------------------------------------------- audits

def tighten_sections(text):
    """{section letter: VIOLATION count} plus F's 'not audited' as violations."""
    counts, sec = {}, None
    for line in text.splitlines():
        m = re.match(r"^([A-Z])\. ", line)
        if m:
            sec = m.group(1)
            counts.setdefault(sec, 0)
            continue
        if sec and ("VIOLATION" in line
                    or (sec == "F" and "not audited" in line)):
            counts[sec] += 1
    return counts


def seed_verdict(seeddir, rec):
    """Every enforced rule's count for one route, and whether it is clean."""
    t = (seeddir / "tighten.log").read_text() if (seeddir / "tighten.log").exists() else ""
    sec = tighten_sections(t)
    sk = (seeddir / "skew.log").read_text() if (seeddir / "skew.log").exists() else ""
    m = re.findall(r"(\d+) select gates, (\d+) measured, (\d+) violated", sk)
    e = int(m[-1][2]) if m else None
    j = rec.get("audits", {}).get("arb_fork", {}).get("violations")
    gls = rec.get("routed_gls", {})
    v = {r: sec.get(r, 0) for r in ENFORCED if r in sec}
    v["E"] = e
    v["J"] = j
    v["D(screen)"] = sec.get("D", 0)
    v["gls"] = gls if isinstance(gls, dict) else {"error": str(gls)}
    clean = (bool(t) and e == 0 and j == 0
             and all(sec.get(r, 0) == 0 for r in ENFORCED)
             and isinstance(gls, dict) and gls
             and all(x == "pass" for x in gls.values()))
    return v, bool(clean)


# ---------------------------------------------------------------- latency

def trips(kernel, vec, expected):
    """Loop trips per vector, for the per-iteration slope; None if unknown."""
    i = vec.get("in", vec)
    if kernel.startswith("xorshift"):
        return i.get("rounds")
    if kernel == "ipow":
        return i.get("e")
    if kernel.startswith("collatz"):
        return (expected or {}).get("out0")
    return None


def slope_ns(xs, ys):
    pts = [(x, y) for x, y in zip(xs, ys) if x is not None and y is not None]
    if len(pts) < 3 or len({x for x, _ in pts}) < 2:
        return None
    n = len(pts)
    mx = sum(x for x, _ in pts) / n
    my = sum(y for _, y in pts) / n
    sxx = sum((x - mx) ** 2 for x, _ in pts)
    return sum((x - mx) * (y - my) for x, y in pts) / sxx / 1000.0


def per_iteration(outdir, kernel, rec):
    vf = outdir / "vectors.json"
    if not vf.exists() or "routed_fast" not in rec:
        return None
    vecs = json.loads(vf.read_text())
    xs = [trips(kernel, v, v.get("expected")) for v in vecs]
    return slope_ns(xs, rec["routed_fast"])


# -------------------------------------------------------------------- run

def run_round(mlir, outdir, sizes_path, seeds, kernel):
    """fusion_bench on every seed, tighten --emit on every route.
    -> {seed: (verdicts, clean, proposals, asks, ns_per_iter)}, dut.v text"""
    outdir.mkdir(parents=True, exist_ok=True)
    log = outdir / "fusion_bench.log"
    with open(log, "w") as f:
        r = subprocess.run(
            [sys.executable, str(BDC / "fusion_bench.py"), "--mlir", str(mlir),
             "--output", str(outdir), "--sizes", str(sizes_path), "--route",
             "--nextpnr-seeds", *map(str, seeds)],
            cwd=BDC, stdout=f, stderr=subprocess.STDOUT)
    res = outdir / "results.json"
    if not res.exists():
        raise RuntimeError(f"fusion_bench wrote no results (exit {r.returncode}); see {log}")
    row = json.loads(res.read_text())
    dut = (outdir / "dut.v").read_text() if (outdir / "dut.v").exists() else ""
    out = {}
    for s in seeds:
        rec = row.get("routes", {}).get(str(s), {})
        sd = outdir / f"seed{s}"
        sdf = sd / "pnr" / "soak.sdf"
        if not sdf.exists():
            out[s] = ({"route": rec.get("route", "no SDF")}, False, {}, [], None)
            continue
        emit = sd / "proposals.vh"
        subprocess.run([sys.executable, str(CELLS / "verify" / "tighten.py"),
                        str(sdf), "--emit", str(emit)], cwd=CELLS,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        props = read_sizes(emit.read_text()) if emit.exists() else {}
        asks = skew_asks((sd / "skew.log").read_text()) if (sd / "skew.log").exists() else []
        v, clean = seed_verdict(sd, rec)
        out[s] = (v, clean, props, asks, per_iteration(outdir, kernel, rec))
    return out, dut


def report(tag, results, lines):
    for s, (v, clean, _, asks, ns) in sorted(results.items()):
        lines.append(f"  {tag} seed {s}: {'CLEAN' if clean else 'NOT CLEAN'}  "
                     + "  ".join(f"{k}={v[k]}" for k in v if k != "gls")
                     + f"  gls={v.get('gls')}"
                     + (f"  {ns:.1f} ns/iteration" if ns else ""))
        print(lines[-1], flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--mlir", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3, 4])
    ap.add_argument("--start", type=Path, help="initial sizes (default: placeholders)")
    ap.add_argument("--max-iter", type=int, default=8)
    ap.add_argument("--headroom", action="store_true")
    ap.add_argument("--fresh-seeds", type=int, nargs="*", default=[])
    a = ap.parse_args()
    mlir = a.mlir.resolve()
    out = a.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    kernel = mlir.parent.parent.name
    env = {k: os.environ.get(k) for k in ("BD_DSP", "BDC_LINK_FASTFALL",
                                           "BDC_OP_FUSION", "BDC_FORK_FUSION")}
    summary = {"kernel": kernel, "mlir": str(mlir), "seeds": a.seeds,
               "env": env, "iterations": []}
    lines = [f"size_kernel {kernel}: seeds {a.seeds}, env {env}"]
    print(lines[0], flush=True)

    cur = read_sizes(a.start.read_text()) if a.start else {}
    tpath = out / "T0.vh"
    write_sizes(tpath, cur, f"{kernel} T0: " + (str(a.start) if a.start else "placeholders"))
    converged = False
    for k in range(a.max_iter):
        res, dut = run_round(mlir, out / f"it{k}", tpath, a.seeds, kernel)
        report(f"it{k}", res, lines)
        summary["iterations"].append({
            "sizes": str(tpath),
            "seeds": {s: {"clean": c, "rules": v, "ns_per_iter": ns}
                      for s, (v, c, _, _, ns) in res.items()}})
        if all(c for _, c, *_ in res.values()):
            converged = True
            lines.append(f"it{k}: CLEAN on every seed with {tpath.name}")
            print(lines[-1], flush=True)
            break
        knobless = [s for s, (v, *_r) in res.items()
                    if (v.get("F") or v.get("J"))]
        if knobless:
            lines.append(f"it{k}: rule F or J violated on seed(s) {knobless}: no "
                         f"delay knob for either -- NOT CONVERGED, stopping")
            print(lines[-1], flush=True)
            break
        props = [p for _, _, p, _, _ in res.values()]
        asks = [x for *_r, a_, _ in res.values() for x in a_]
        new, mlog = merge(cur, props, asks, dut)
        if new == cur:
            lines.append(f"it{k}: the merge changes nothing and the routes are "
                         f"not clean -- NOT CONVERGED, stopping")
            print(lines[-1], flush=True)
            break
        for m in mlog:
            print("    " + m, flush=True)
        cur = new
        tpath = out / f"T{k + 1}.vh"
        write_sizes(tpath, cur, f"{kernel} T{k + 1}: per-cell max of T{k} + "
                    f"tighten --emit on seeds {a.seeds} + rule E asks (it{k})")
    else:
        lines.append(f"no convergence in {a.max_iter} iterations")
        print(lines[-1], flush=True)

    final = tpath
    if converged and a.headroom:
        final = out / (tpath.stem + "H.vh")
        write_sizes(final, headroom(cur), f"{kernel} {tpath.stem} + 1 link on "
                    f"every compute cell (headroom)")
        lines.append(f"headroom: {final.name}")
        print(lines[-1], flush=True)
    summary["converged"] = converged
    summary["final"] = str(final)

    ok = converged
    if converged and a.fresh_seeds:
        res, _ = run_round(mlir, out / "fresh", final, a.fresh_seeds, kernel)
        report("fresh", res, lines)
        summary["fresh"] = {s: {"clean": c, "rules": v, "ns_per_iter": ns}
                            for s, (v, c, _, _, ns) in res.items()}
        nss = [ns for *_r, ns in res.values() if ns]
        if nss:
            lines.append(f"fresh: {sum(nss) / len(nss):.1f} ns/iteration "
                         f"({min(nss):.1f}-{max(nss):.1f}) over {len(nss)} seeds")
            print(lines[-1], flush=True)
        ok = all(c for _, c, *_ in res.values())
    (out / "summary.json").write_text(json.dumps(summary, indent=2, default=str) + "\n")
    (out / "summary.txt").write_text("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
