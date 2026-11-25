"""meta_dtmc.py -- probabilistic resolution of the arbiter's state loop (Storm).

Not a postulated exponential: the chain is the discretised LINEARISED loop
around the metastable point (B-arb-analog.md: tau v' = F(v) - v, gain g > 1 at
the saddle, so v grows like e^{(g-1) t / tau}), plus a small noise term.

  state v in {-N..N}: the node voltage offset from the saddle, in grid units
  step (one tick of length dt):  v' = a v (stochastically rounded to the
         grid, so E[v'] = a v exactly) + n,  a = exp(dt (g-1)/tau),
         n = -1, 0, +1 with probabilities p, 1-2p, p  (thermal noise)
  |v| >= N: resolved (absorbing; N = distance to a valid logic level)
  initial: v0 uniform on {-M..M}  (request skew uniform inside the aperture,
         mapped linearly to an initial offset)

Storm computes P(unresolved after k ticks) exactly for this chain.  We fit the
tail slope and compare it with ln a = dt (g-1)/tau, the rate the ODE predicts.
Run:  <venv>/bin/python -I meta_dtmc.py
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def prism(a, N, M, p):
    L = ["dtmc", "", "module loop",
         f"  s : [0..1] init 0;",          # 0 = before the decision, 1 = running
         f"  v : [{-N}..{N}] init 0;"]
    k = 2 * M + 1
    L.append("  [] s=0 -> " + " + ".join(
        f"1/{k}:(s'=1)&(v'={x})" for x in range(-M, M + 1)) + ";")
    for x in range(-N + 1, N):
        # stochastic rounding: E[v'] = a v exactly, so the grid adds no dead
        # zone around the saddle (plain rounding freezes |v| < 1/(2(a-1)))
        y = a * x
        lo = math.floor(y)
        fr = y - lo
        dist = {}
        for base, pb in ((lo, 1 - fr), (lo + 1, fr)):
            if pb <= 0:
                continue
            for dn, pr in ((-1, p), (0, 1 - 2 * p), (1, p)):
                if pr <= 0:
                    continue
                z = max(-N, min(N, base + dn))
                dist[z] = dist.get(z, 0) + pb * pr
        ups = [f"{pr!r}:(v'={z})" for z, pr in sorted(dist.items())]
        L.append(f"  [] s=1 & v={x} -> " + " + ".join(ups) + ";")
    L.append(f"  [] s=1 & (v={-N} | v={N}) -> (v'=v);")
    L.append("endmodule")
    L.append(f'label "res" = s=1 & (v={-N} | v={N});')
    return "\n".join(L) + "\n"


def run(a, N=4000, M=400, p=0.05, ks=range(0, 241, 20)):
    import stormpy
    import tempfile
    t0 = time.time()
    fd, path = tempfile.mkstemp(suffix=".prism")
    with os.fdopen(fd, "w") as fh:
        fh.write(prism(a, N, M, p))
    prog = stormpy.parse_prism_program(path)
    os.unlink(path)
    props = stormpy.parse_properties(
        ";".join(f'P=? [ F<={k + 1} "res" ]' for k in ks), prog)
    model = stormpy.build_model(prog, props)
    out = []
    for k, pr in zip(ks, props):
        r = stormpy.model_checking(model, pr)
        out.append((k, 1 - r.at(model.initial_states[0])
                    if hasattr(r, "at") else
                    1 - r.get_value(model.initial_states[0])))
    return out, model.nr_states, time.time() - t0


if __name__ == "__main__":
    for a in (1.05, 1.1, 1.2):
        for p in (0.0, 0.1, 0.3):
            out, ns, sec = run(a, p=p)
            # local decay rate between successive k, in units of ln a
            loc = []
            for (k0, u0), (k1, u1) in zip(out, out[1:]):
                if u0 > 0 and u1 > 0 and u0 < 1 and u1 < 1:
                    loc.append(-(math.log(u1) - math.log(u0)) / (k1 - k0)
                               / math.log(a))
            print(f"a={a} (ln a={math.log(a):.4f}) noise p={p}: states={ns} "
                  f"{sec:.2f}s  local rate / ln a: "
                  + " ".join(f"{x:.2f}" for x in loc))
            print("    k : P(unresolved after k ticks)  "
                  + "  ".join(f"{k}:{u:.3g}" for k, u in out))
