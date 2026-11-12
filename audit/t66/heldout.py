# T66: held-out accuracy recomputed from predictions as stated in research's JOURNAL (2026-11-12 03:35-06:35 entries, written
# before or independently of measurement) and measured periods from the committed graphs' check.txt (trace P).
import re, statistics as st
G = '/root/t66/research/data/eventgraph/graphs/'
pred = {  # run: predicted ns (JOURNAL text)
 'pmf_1': 29.07, 'pmf_3': 29.29, 'pmf_4': 30.13, 'pmf_5': 30.11,
 'ipowfm_1': 46.09, 'ipowfm_2': 44.92, 'ipowfm_3': 45.06, 'ipowfm_4': 44.08,
 'colfm_1': 53.03, 'colfm_2': 53.93, 'colfm_3': 53.50, 'colfm_4': 53.71,
 'col_cdmo_1': 57.85, 'col_cdmo_2': 58.52, 'col_cdmo_3': 57.84, 'col_cdmo_4': 58.19,
 'colb_1': 56.45, 'colb_2': 56.39, 'colb_3': 58.77, 'colb_4': 56.44}
e = []
for r, p in pred.items():
    P = int(re.search(r'period P = (\d+)', open(G + r + '/check.txt').read())[1]) / 1000
    e.append(p - P); print(f"{r}: pred {p:.2f} meas {P:.3f} err {p-P:+.2f}")
print(f"n={len(e)} mean {st.mean(e):+.2f} mean|err| {st.mean(map(abs,e)):.2f} max|err| {max(map(abs,e)):.2f}")
