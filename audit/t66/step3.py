# T66: recompute research's step-3 summary (per-variant means, error ranges) from step3_predictions.tsv; cross-check
# measured_ps against the committed graph's trace period where a graph of that run exists.
import csv, sys, os, re, statistics as st
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t')); gdir = sys.argv[2]
by = {}
for r in rows: by.setdefault(r['variant'], []).append(r)
for v, rs in by.items():
    p = [int(r['predicted_ps']) for r in rs]; m = [int(r['measured_ps']) for r in rs]; e = [a - b for a, b in zip(p, m)]
    bad = [r['seed'] for r in rs if int(r['pred_minus_meas_ps']) != int(r['predicted_ps']) - int(r['measured_ps'])]
    print(f"{v}: n={len(rs)} pred mean {st.mean(p)/1000:.2f} meas mean {st.mean(m)/1000:.2f} err mean {st.mean(e)/1000:+.2f} range {min(e)/1000:+.2f}..{max(e)/1000:+.2f} |err| max {max(map(abs,e))/1000:.2f}  arith-mismatch {bad}")
    for r in rs:
        g = os.path.join(gdir, f"{v}_{r['seed']}", 'check.txt')
        if os.path.exists(g):
            P = int(re.search(r'period P = (\d+)', open(g).read())[1])
            if abs(P - int(r['measured_ps'])) > 10: print(f"   {v}_{r['seed']}: measured {r['measured_ps']} vs graph trace P {P}")
        gb = os.path.join(gdir, f"x50_{r['seed']}", 'check.txt')
        if os.path.exists(gb):
            Pb = int(re.search(r'period P = (\d+)', open(gb).read())[1])
            if Pb != int(r['base_ps']): print(f"   base {v}_{r['seed']}: base_ps {r['base_ps']} vs x50 graph {Pb}")
ae = [abs(int(r['pred_minus_meas_ps'])) for r in rows if r['variant'] not in ('p12',)]
print(f"all but p12: n={len(ae)} mean |err| {st.mean(ae)/1000:.2f} ns, max {max(ae)/1000:.2f}")
