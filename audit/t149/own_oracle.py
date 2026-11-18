#!/usr/bin/env python3
"""T149: own expected values for the suite kernels (research 4fc96e310 / 5a8053b31). For each kernel K with kernels/K/K.c and
vec.hex: compile K.c with an own driver (in_int_t = int, the Integration.h include stubbed, main renamed away), map the
two 32-bit bench words to the kernel's parameters from its signature (int: one word each in order; long long / int64:
lo = word 0, hi = word 1), run every vector, print the 32-bit result, compare with research's vec.exp.
usage: own_oracle.py REPO K [K ...]"""
import os, re, subprocess, sys, tempfile
R, ks = sys.argv[1], sys.argv[2:]
bad = 0
for k in ks:
    src = open(f"{R}/kernels/{k}/{k}.c").read()
    m = re.search(r"\b\w[\w ]*?\b" + k + r"\s*\(([^)]*)\)\s*\{", src)
    params = [p.strip() for p in m.group(1).split(",") if p.strip()]
    hdr = open(f"{R}/kernels/{k}/{k}.h").read() if os.path.exists(f"{R}/kernels/{k}/{k}.h") else ""
    wide = re.search(r"typedef\s+(long\s+long|int64_t)\s+in_int_t", hdr) is not None   # the kernel's own header widens in_int_t
    rt = re.search(r"(\w[\w ]*?)\s+" + k + r"\s*\(", src).group(1).split()[-1]
    body = src.replace('#include "dynamatic/Integration.h"', "").replace(f'#include "{k}.h"', "")
    body = re.sub(r"int\s+main\s*\(", "int unused_main(", body)
    vec = [l.split() for l in open(f"{R}/kernels/{k}/vec.hex") if l.strip() and not l.startswith("#")]
    calls = []
    for w in vec:
        w0, w1 = int(w[0], 16), int(w[1], 16) if len(w) > 1 else 0
        args, wi = [], [w0, w1]
        for p in params:
            if "long" in p or "64" in p or (wide and "in_int_t" in p): args.append(f"(long long)(((unsigned long long){w1}u << 32) | {w0}u)")
            else: args.append(f"(int){wi.pop(0)}u")
        calls.append(f'printf("%08x\\n", (unsigned)({k}({", ".join(args)})));')
    prog = ("#include <stdio.h>\n#include <stdint.h>\ntypedef %s in_int_t; typedef long long in_int64_t;\n#define CALL_KERNEL(...) 0\n") % ("long long" if wide else "int") + body + \
           "\nint main(void){\n" + "\n".join(calls) + "\nreturn 0;}\n"
    d = tempfile.mkdtemp(); open(f"{d}/t.c", "w").write(prog)
    r = subprocess.run(["gcc", "-O1", "-fwrapv", "-w", "-o", f"{d}/t", f"{d}/t.c"], capture_output=True, text=True)
    if r.returncode: print(f"{k}: own compile failed: {r.stderr[:200]}"); bad += 1; continue
    got = subprocess.run([f"{d}/t"], capture_output=True, text=True).stdout.split()
    exp = open(f"{R}/kernels/{k}/vec.exp").read().split()
    diff = [i for i, (a, b) in enumerate(zip(got, exp)) if int(a, 16) != int(b, 16)]
    ok = not diff and len(got) == len(exp)
    bad += not ok
    print(f"{k}: params {params}: {len(got)} vectors, {'MATCH' if ok else 'DIFFER at ' + str(diff) + ' (n %d/%d)' % (len(got), len(exp))}")
print("kernels differing:", bad)
