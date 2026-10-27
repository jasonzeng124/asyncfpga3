#!/usr/bin/env python3
"""ring_scatter.py WORK [ndraws] -- what ring-to-ring period scatter a gen.py
delay perturbation produces on ro_many_top's 128 rings.

WORK holds routed.json + routed.sdf of ro_many_top.  The perturbation is
gen.py's own (read_sdf with the caller's GLS_* environment: GLS_SCATTER,
GLS_SCATTER_MODE, GLS_SCATTER_REGION, GLS_REGION_SLICES), drawn for seeds
1..ndraws; the loop walk is ring_predict.py's.  For each draw every ring's
perturbed/unperturbed period ratio is divided by the draw's median ratio (a
global scale is a corner, not scatter -- the same normalisation hw/README.md
applies to the board), and the median |ratio-1| is reported per ring length
and overall: the number to compare with the 8.5% median ring scatter on
record.  It says nothing about WHICH rings are slow on the board (per-ring
board periods of that route are not in the repo)."""
import importlib.util, os, statistics, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
GLS = os.path.abspath(os.path.join(HERE, "..", ".."))


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def periods(work, env):
    """child: one draw -> {ring: period}"""
    os.environ.update(env)
    os.environ["GLS_WORK"] = work
    gen = load(os.path.join(GLS, "gen.py"), "gen")
    rp = load(os.path.join(GLS, "fid", "ring_predict.py"), "rp")
    iop, ic, _sh, *_ = gen.read_sdf(gen.SDF)
    from collections import defaultdict
    E = defaultdict(list)
    for s, d, ps in ic:
        E[s].append((d, (ps, ps, ps)))
    for inst, lst in iop.items():
        for a, z, ps in lst:
            E["%s/%s" % (inst, a)].append(("%s/%s" % (inst, z), (ps, ps, ps)))
    out = {}
    for name, n, pref, ex in rp.rings("ro_many_top"):
        t, _k = rp.loop(E, pref, ex)
        if t:
            out[name] = (n, 2 * t[0])
    return out


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[1] == "--child":
    import json
    print(json.dumps(periods(sys.argv[2], {})))
    sys.exit(0)

if __name__ == "__main__":
    import json
    work = sys.argv[1]
    nd = int(sys.argv[2]) if len(sys.argv) > 2 else 4

    def run(extra):
        env = {k: v for k, v in os.environ.items() if not k.startswith("GLS_")}
        env.update(extra)
        r = subprocess.run([sys.executable, __file__, "--child", work], env=env,
                           capture_output=True, text=True, check=True)
        return json.loads(r.stdout.strip().splitlines()[-1])
    base = run({})
    pert = {k: v for k, v in os.environ.items() if k.startswith("GLS_")}
    devs, bylen = [], {}
    for seed in range(1, nd + 1):
        p = run(dict(pert, GLS_SCATTER_SEED=str(seed)))
        rat = {r: p[r][1] / base[r][1] for r in base}
        med = statistics.median(rat.values())
        for r, x in rat.items():
            d = abs(x / med - 1)
            devs.append(d)
            bylen.setdefault(base[r][0], []).append(d)
    print("perturbation: %s, %d draws x %d rings" % (" ".join("%s=%s" % kv for kv in sorted(pert.items())) or "none", nd, len(base)))
    print("median |period/median - 1|: all %.2f%%  " % (100 * statistics.median(devs)) +
          "  ".join("L%d %.2f%%" % (L, 100 * statistics.median(v)) for L, v in sorted(bylen.items())))
