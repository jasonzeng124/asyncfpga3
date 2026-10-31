import re, sys, os
out, *ins = sys.argv[1:]
rd = lambda p: {m[1]: int(m[2]) for m in re.finditer(r"^`define (\S+) (\d+)", open(p).read(), re.M)}
m = {}
for p in ins:
    for k, v in rd(p).items():
        m[k] = max(m.get(k, 0), v)
# rule E: skew.py's "fix: N more bd_delay element(s) on <link>" on each route the raw
# proposals came from -> current length (first input, the sizes that route was built with) + N + 1.
cur = rd(ins[0])
W = os.environ.get("COLL_ROOT", "/tmp/claude-0/-home-user-asyncfpga3/1493a6da-414d-591f-aed7-9ee9f21c4602/scratchpad/wt_coll/build/coll")
for p in ins[1:]:
    mm = re.search(r"raw8?_it(\d+)_s(\d+)\.vh$", p)
    if not mm:
        continue
    log = f"{W}/it{mm[1]}/seed{mm[2]}/skew.log"
    if not os.path.exists(log):
        continue
    for n, link in re.findall(r"fix: (\d+) more bd_delay element\(s\) on (\S+)", open(log).read()):
        k = "BD_SZ_UUT_" + re.sub(r"[^A-Za-z0-9]", "_", link).upper()
        base = cur.get(k)
        if base is None:
            # no size macro yet: the kernel's own DELAY_<LINK> default from the emitted dut.v
            dut = f"{W}/it{mm[1]}/dut.v"
            d = re.search(r"parameter\s+DELAY_" + re.escape(k[len("BD_SZ_UUT_"):]) + r"\s*=\s*(\d+)", open(dut).read()) if os.path.exists(dut) else None
            if d is None:
                sys.exit(f"rule E asks for {link}: no size macro and no DELAY default in {dut}")
            base = int(d[1])
        m[k] = max(m.get(k, 0), base + int(n) + 1)
        print(f"rule E: {k} {base} -> {m[k]}")
open(out, "w").write("// collatz ratchet: per-cell max of " + " ".join(p.split("/")[-1] for p in ins) + " + rule E fix asks\n" + "".join(f"`define {k} {m[k]}\n" for k in sorted(m)))
print(len(m), "cells")
