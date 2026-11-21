#!/usr/bin/env python3
"""C reference values for formal/tools/verify (probe C-vk).

Compiles the kernel's C file (kernels/<k>/<k>.c, unchanged) with a generated harness and
runs it on the chosen vectors. The expected values therefore come from the C source,
never from a circuit run or from the MLIR.

    python3 cref.py C_FILE FUNC "a,b" "a,b" ...     -> one line per vector: a,b -> r

Compiler: the system gcc, with -fwrapv (i32 two's complement wrap-around: the hardware's
`addi`/`muli`; plain C leaves signed overflow undefined) and -O0. `>>` of a negative int is
arithmetic in gcc (implementation-defined in C). `CALL_KERNEL` (dynamatic/Integration.h) is
stubbed out; the file's own `main` is renamed away.
"""
import os
import subprocess
import sys
import tempfile


def c_reference(c_file, func, vectors):
    """-> list of int results (signed C int), one per vector."""
    c_file = os.path.abspath(c_file)
    arity = len(vectors[0])
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "dynamatic"))
        with open(os.path.join(d, "dynamatic", "Integration.h"), "w") as f:
            f.write("#define CALL_KERNEL(...) ((void)0)\n")
        args = ", ".join(f"int a{i}" for i in range(arity))
        call = ", ".join(f"(int)strtol(argv[i + {i}], 0, 10)" for i in range(arity))
        with open(os.path.join(d, "harness.c"), "w") as f:
            f.write("#include <stdio.h>\n#include <stdlib.h>\n"
                    f"int {func}({args});\n"
                    "int main(int argc, char **argv) {\n"
                    f"  for (int i = 1; i + {arity - 1} < argc; i += {arity})\n"
                    f"    printf(\"%d\\n\", {func}({call}));\n"
                    "  return 0;\n}\n")
        exe = os.path.join(d, "ref")
        cmd = ["gcc", "-O0", "-fwrapv", "-w", "-I", d, "-I", os.path.dirname(c_file),
               "-Dmain=verify_orig_main", "-c", c_file, "-o", os.path.join(d, "k.o")]
        subprocess.run(cmd, check=True)
        subprocess.run(["gcc", "-O0", "-fwrapv", "-w", os.path.join(d, "harness.c"),
                        os.path.join(d, "k.o"), "-o", exe], check=True)
        argv = [str(x) for v in vectors for x in v]
        out = subprocess.run([exe] + argv, check=True, capture_output=True, text=True,
                             timeout=60).stdout.split()
    if len(out) != len(vectors):
        raise SystemExit(f"cref: expected {len(vectors)} results, got {len(out)}")
    return [int(x) for x in out]


if __name__ == "__main__":
    vs = [tuple(int(x) for x in a.split(",")) for a in sys.argv[3:]]
    for v, r in zip(vs, c_reference(sys.argv[1], sys.argv[2], vs)):
        print(",".join(map(str, v)), "->", r)
