# Compare fusion_bench.kernel_vectors('collatz64') expected values against the compiled C kernel.
import sys, subprocess
sys.path.insert(0, sys.argv[1] + "/bdc")
import fusion_bench
vecs, exp = fusion_bench.kernel_vectors("collatz64")
out = subprocess.run([sys.argv[2]] + [str(v["n"]) for v in vecs], capture_output=True, text=True).stdout.split("\n")
bad = 0
for v, e, line in zip(vecs, exp, out):
    n, steps, peak = map(int, line.split())
    ok = (e["out0"] == steps)
    bad += not ok
    print("n=%-9d expected=%-5d C=%-5d peak=%-14d peak>2^31=%s %s" % (v["n"], e["out0"], steps, peak, peak > 2**31, "OK" if ok else "MISMATCH"))
print("vectors", len(vecs), "mismatches", bad, "peak>2^31:", sum(1 for l in out if l and int(l.split()[2]) > 2**31))
