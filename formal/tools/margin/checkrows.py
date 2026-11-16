#!/usr/bin/env python3
"""margin/checkrows.py OUT/ (shard C, UNTRUSTED): re-run EVERY failing row of OUT/margins.txt at its kappa_fail with a
dump and check it with gatecheck.py (every gate relation of GateOKRunt w incl. the H_RUNT read-lag bound, every delay
in Spec.Adm) and envcheck.py (Env + SeqEnv, ArbOK T, out0). A w = 20 failure whose run has lag violations is NOT an
admissible behaviour (the simulator skipped a narrow-pulse chain longer than the arc's band allows) and is reported
INADMISSIBLE. Writes OUT/checked.txt. The simulator command is taken from OUT/witness/command.txt (first command)."""
import os, re, subprocess, sys, json
O = os.path.abspath(sys.argv[1]); H = os.path.dirname(os.path.abspath(__file__)); F = os.path.dirname(os.path.dirname(H))
base = [l for l in open(os.path.join(O, "witness", "command.txt")) if not l.startswith("#")][0].split()
env = {}
while "=" in base[0] and not base[0].startswith("/"): k, v = base.pop(0).split("=", 1); env[k] = v
def setopt(cmd, opt, val):
    cmd = list(cmd)
    if opt in cmd: cmd[cmd.index(opt) + 1] = val
    else: cmd += [opt, val]
    return cmd
pairs = base[base.index("--pairs") + 1:]; pairs = pairs[:next(i for i, x in enumerate(pairs) if x.startswith("--"))]
bnd = json.load(open(os.path.join(O, "bnd.json"))); bnd["arbs"] = json.load(open(os.path.join(O, "arbs.json")))
json.dump(bnd, open(os.path.join(O, "bnd_arbs.json"), "w"))
out = open(os.path.join(O, "checked.txt"), "w"); adm = []
out.write("# every failing row re-run at kappa_fail and checked (gatecheck.py, envcheck.py); UNTRUSTED checkers\n")
for l in open(os.path.join(O, "margins.txt")):
    if l.startswith("#"): continue
    f = l.split()
    if len(f) < 6 or not re.match(r"^[0-9.]+$", f[4]): continue
    w = f[0].split("=")[1]; k = f[4]; route = f[-1]
    q = re.match(r"quiet@([0-9.]+)", f[6]) if len(f) > 6 else None
    if f[5] in ("FAIL-noanswer", "UNDECIDED") and q:
        out.write("%s w=%s k=%s %s | NOT-CHECKED (%s); checking its first quiet failure at %s |\n" % (f[1], w, k, f[2], f[5], q.group(1)))
        k = q.group(1)
    elif f[5] in ("FAIL-noanswer", "UNDECIDED"):
        # a livelock to tmax or an event-capped run is not a finite counterexample (it would need a periodicity
        # argument, as Lean's Frontier36 did for gcd_ps); it is not checked and does not enter kappa_hi
        out.write("%s w=%s k=%s %s | NOT-CHECKED (%s: no finite witness) |\n" % (f[1], w, k, f[2], f[5])); out.flush(); continue
    S = [[a.rsplit("/", 1)[0], int(a.rsplit("/", 1)[1])] for a in route.split(",")]
    tag = "%s_%s_w%s" % (f[1].replace("/", "_"), f[2], w)
    cf = os.path.join(O, "tmp", "chk_%s.json" % tag); df = os.path.join(O, "tmp", "chk_%s_dump.json" % tag)
    os.makedirs(os.path.dirname(cf), exist_ok=True); json.dump({"S": S, "F": []}, open(cf, "w"))
    cmd = setopt(setopt(setopt(base, "--kappa", k), "--classes", cf), "--w", w) + ["--dump", df]
    if w == "0": i = cmd.index("--w"); del cmd[i:i + 2]
    e = dict(os.environ, **env)
    r = subprocess.run(cmd, capture_output=True, text=True, env=e)
    res = ([x for x in r.stdout.splitlines() if x.startswith("RESULT")] or ["NO-VERDICT (event cap)"])[0]
    if not os.path.exists(df):
        out.write("%s | %s | no dump\n" % (l.strip()[:60], res)); out.flush(); continue
    g = subprocess.run(["python3", os.path.join(H, "gatecheck.py"), os.path.join(O, "net.json"), os.path.join(O, "bnd.json"), df,
                        "0", k, w, "@" + cf], capture_output=True, text=True, env=e).stdout.strip().splitlines()
    v = subprocess.run(["python3", os.path.join(F, "tools", "huff", "envcheck.py"), os.path.join(O, "net.json"),
                        os.path.join(O, "bnd_arbs.json"), df, "400000", "1000", "3000"] + pairs, capture_output=True, text=True).stdout
    gl = g[-1] if g else "gatecheck: no output"
    m = re.search(r"mismatches (\d+) arcs outside Adm (\d+) lag violations (\d+)", gl)
    ok = m and m.group(1) == "0" and m.group(2) == "0" and m.group(3) == "0" and "Env + SeqEnv: OK" in v
    envnote = ""
    if m and m.group(1) == "0" and m.group(2) == "0" and m.group(3) == "0" and not ok:
        # gate relations clean, Env violated: typically the simulated harness released the data on the first fall of an
        # acknowledge that then glitched back up (Spec.Env wants data held while req or ack is high). Retry with a
        # harness that holds the data until its next request (--datachange handshake): also a Spec.Env environment.
        os.unlink(df)
        cmd = setopt(cmd, "--datachange", "handshake")
        r = subprocess.run(cmd, capture_output=True, text=True, env=e)
        res = ([x for x in r.stdout.splitlines() if x.startswith("RESULT")] or ["NO-VERDICT (event cap)"])[0]
        if os.path.exists(df):
            g = subprocess.run(["python3", os.path.join(H, "gatecheck.py"), os.path.join(O, "net.json"), os.path.join(O, "bnd.json"), df,
                                "0", k, w, "@" + cf], capture_output=True, text=True, env=e).stdout.strip().splitlines()
            v = subprocess.run(["python3", os.path.join(F, "tools", "huff", "envcheck.py"), os.path.join(O, "net.json"),
                                os.path.join(O, "bnd_arbs.json"), df, "400000", "1000", "3000"] + pairs, capture_output=True, text=True).stdout
            gl = g[-1] if g else "gatecheck: no output"
            m = re.search(r"mismatches (\d+) arcs outside Adm (\d+) lag violations (\d+)", gl)
            ok = m and m.group(1) == "0" and m.group(2) == "0" and m.group(3) == "0" and "Env + SeqEnv: OK" in v
            envnote = "[env broad violated Env; rerun with --datachange handshake] "
        else:
            envnote = "[env broad violated Env; handshake rerun gave no dump] "
    arb = re.search(r"T >= (\d+)", v)
    out.write("%s w=%s k=%s %s | %s%s | %s | ArbOK T>=%s | %s\n" % (f[1], w, k, f[2], envnote, "ADMISSIBLE" if ok else "INADMISSIBLE", res,
              arb.group(1) if arb else "?", gl)); out.flush()
    if ok and not res.startswith("RESULT OK"): adm.append((float(k), int(w), f[1], f[2], f[3], res))
    if os.path.exists(df): os.unlink(df)
out.close()
# kappa_hi: smallest kappa with an ADMISSIBLE failing run (finite: wrong value, or quiet with an answer missing). A w = 20 behaviour is also a behaviour of the plain
# statement (Lean: seqRunt_of_seq direction used by the refutations), so kappa_hi(w = 0) = min over both.
with open(os.path.join(O, "kappa_hi.txt"), "w") as kh:
    kh.write("# kappa_hi = smallest kappa at which an ADMISSIBLE failing run was found (search; gatecheck + envcheck passed)\n")
    kh.write("# kappa_lo (proved safe): none for this build (no certificate)\n")
    for w in (20, 0):
        c = [x for x in adm if x[1] == w or (w == 0 and x[1] == 20)]
        if c:
            b = min(c); kh.write("w=%d: kappa_hi = %.2f  race %s pin %s from %s (run at w=%d) %s\n" % (w, b[0], b[2], b[3], b[4], b[1], b[5]))
        else:
            kh.write("w=%d: kappa_hi: no admissible failure found among the swept rows (search)\n" % w)
print(open(os.path.join(O, "kappa_hi.txt")).read())
print(open(os.path.join(O, "checked.txt")).read())
