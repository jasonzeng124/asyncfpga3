#!/usr/bin/env python3
"""est_sizes.py KERNEL_V KERNEL -- a sizes.vh holding every matched delay at bdc/emit.py's own estimate (the kernel's
parameter defaults), under the bench's macro names (BD_SZ_BRIDGE_I_UDUT_<INST>, cells/hw/gen_bench.py).  Building with
it gives the same circuit as building with no sizes file; corner_audit.py sizes only the lines a sizes.vh lists.
A kernel with no matched delay gets a file with no lines (exit 0); a file with no bdc_KERNEL module at all is an error."""
import re, sys
src = open(sys.argv[1]).read()
m = re.search(r"module\s+bdc_" + re.escape(sys.argv[2]) + r"\s*#\((.*?)\)\s*\(", src, re.S)
if not m:
    # A kernel with no matched delay at all (test_int16: a constant joined with the call's end token) has no parameter
    # clause: nothing to size, and the file says so (auto_size.sh then builds once and judges that route).
    if re.search(r"module\s+bdc_" + re.escape(sys.argv[2]) + r"\s*\(", src):
        print("// est_sizes.py: bdc_%s has no matched delay (no parameters): nothing to size" % sys.argv[2])
        sys.exit(0)
    sys.exit("est_sizes.py: no module bdc_%s in %s" % (sys.argv[2], sys.argv[1]))
print("// est_sizes.py: bdc/emit.py's estimates for bdc_%s (the kernel's parameter defaults)" % sys.argv[2])
for inst, d in re.findall(r"parameter\s+DELAY_(\w+)\s*=\s*(\d+)", m.group(1)):
    print("`define BD_SZ_BRIDGE_I_UDUT_%s %s" % (inst.upper(), d))
