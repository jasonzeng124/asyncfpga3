"""mutband.py BANDS.json OUT.json ARC DELTA -- add DELTA ps to the lower AND upper end of one arc
(negative control NEGband of probe E9ArbNet: the certificate was generated from the unmutated bands,
so the arbiter's virtual-node bands no longer equal CoreOf of the per-pin bands)."""
import json
import sys

b = json.load(open(sys.argv[1]))
k, dlt = sys.argv[3], int(sys.argv[4])
lo, hi = b["arcs"][k]
b["arcs"][k] = [lo + dlt, hi + dlt]
json.dump(b, open(sys.argv[2], "w"))
print(f"mutband: {k} [{lo}, {hi}] -> {b['arcs'][k]}")
