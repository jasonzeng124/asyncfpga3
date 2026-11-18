#!/usr/bin/env python3
"""own oracle: oracle.py REPO K VECFILE -> one 8-hex result per vector (kernel's C, own driver, gcc -O1 -fwrapv).
Mapping: words in order, one per int argument (all four kernels take (int,int))."""
import re, subprocess, sys, tempfile
R, k, vf = sys.argv[1:4]
src = open(f"{R}/kernels/{k}/{k}.c").read()
m = re.search(r"\bint\s+" + k + r"\s*\(([^)]*)\)\s*\{", src)
params = [p.strip() for p in m.group(1).split(",")]
assert len(params) == 2 and all(p.startswith("in_int_t") for p in params), params
body = src.replace('#include "dynamatic/Integration.h"', "").replace(f'#include "{k}.h"', "")
body = re.sub(r"int\s+main\s*\(", "int unused_main(", body)
words = [int(w, 16) for w in re.sub(r"//[^\n]*", " ", open(vf).read()).split()]
assert len(words) % 2 == 0
calls = [f'printf("%08x\\n", (unsigned){k}((int){words[j]}u, (int){words[j+1]}u));' for j in range(0, len(words), 2)]
prog = "#include <stdio.h>\ntypedef int in_int_t;\n#define CALL_KERNEL(...) 0\n" + body + "\nint main(void){\n" + "\n".join(calls) + "\nreturn 0;}\n"
d = tempfile.mkdtemp(); open(f"{d}/t.c", "w").write(prog)
subprocess.run(["gcc", "-O1", "-fwrapv", "-w", "-o", f"{d}/t", f"{d}/t.c"], check=True)
sys.stdout.write(subprocess.run([f"{d}/t"], capture_output=True, text=True, check=True).stdout)
