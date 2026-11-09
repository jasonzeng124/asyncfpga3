"""run the path-skew adversary (UNTRUSTED). usage: skewrun.py c"""
import sys, os, json, pickle, subprocess
sys.path.insert(0, "/tmp/claude-0/race")
c = sys.argv[1]
from envchk import run, evs, idn
S = pickle.load(open("/tmp/claude-0/race/adv/skew_c%s.pkl" % c, "rb"))
ref = pickle.load(open("/tmp/claude-0/race/adv/r_12_18_c%s_pmid_none_0.pkl" % c, "rb"))
for s in S:
    adv = json.load(open("/tmp/claude-0/race/adv/skew_c%s_%d.json" % (c, s["i"])))
    for envd in ({}, {"all": 500000}, {"req_fall": 500000}, {"pack_fall": 500000}):
        fn = "/tmp/claude-0/race/adv/skew_c%s_%d_%s.pkl" % (c, s["i"], "_".join("%s%d" % kv for kv in envd.items()) or "noenv")
        env = dict(os.environ, ADV=json.dumps(adv), ENVD=json.dumps(envd), OUT=fn)
        subprocess.run(["python3", "/tmp/claude-0/race/simenv.py", c, "12", "18"], env=env, stdout=subprocess.DEVNULL, check=True)
        r = run(ref, fn); H = pickle.load(open(fn, "rb"))
        def T(nk):
            e = evs(H, idn[nk[0]]); return e[nk[1]] if nk[1] < len(e) else None
        tY = T(s["Y"]); gaps = [(tY - T(x)) if (tY is not None and T(x) is not None) else None for x in s["Xs"]]
        print("c=%s Y=%s(%d) env=%s: out %s ok=%s hazards=%d exact-count-diffs=%d guards-with-z-change=%d %s | Y - X gaps (ps) min %s max %s (mid-run gaps were %s..%s)" % (
            c, s["Y"][0], s["Y"][1], envd, r["res"], r["ok"], r["hz"], r["ndiff"], r["zchg"], r["zchg_ex"][:2],
            min(g for g in gaps if g is not None) if any(g is not None for g in gaps) else None, max(g for g in gaps if g is not None) if any(g is not None for g in gaps) else None,
            min((T.__defaults__ or [None])) if False else "", ""), flush=True)
