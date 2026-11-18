"""neg.py: run simcheck_obs with emit.token_floor wrapped so that ONE stage it added (on value DROP_STAGE) is taken back.
usage: DROP_STAGE=n_trueResult_16 python3 neg.py <simcheck args>   (run from worktree root)"""
import os, sys, runpy
sys.path.insert(0, os.path.join(os.getcwd(), "bdc"))
import emit
orig = emit.token_floor
drop = os.environ["DROP_STAGE"]
def wrapped(func, linked, depth, exclude=frozenset(), forbid=frozenset()):
    added = orig(func, linked, depth, exclude, forbid)
    hits = [v for v, n in added if emit.vname(v) == drop]
    assert hits, f"no stage added on {drop}: {[(emit.vname(v), n) for v, n in added]}"
    v = hits[-1]
    depth[v] -= 1
    if depth[v] == 0:
        linked.discard(v); del depth[v]
    print(f"NEG: took back one stage on ulink_{drop}: now {depth.get(v, 0)}", file=sys.stderr)
    return [(x, n) for x, n in added if not (x is v and n == max(m for y, m in added if y is v))]
emit.token_floor = wrapped
sys.argv = ["simcheck_obs.py"] + sys.argv[1:]
runpy.run_path(os.path.join(os.getcwd(), "bdc", "simcheck_obs.py"), run_name="__main__")
