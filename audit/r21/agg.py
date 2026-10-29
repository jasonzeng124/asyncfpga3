import sys, re, glob, collections
# usage: agg.py 'glob'   -> per-file-group summary; violation = server transactions < client acks
rows = collections.defaultdict(lambda: [0,0,0,0,0,0,[] ,0])  # trials, meta, commit, viol, simulA, x, Ws, hang
for f in sorted(glob.glob(sys.argv[1])):
    key = re.sub(r'_s\d+\.log$', '', f.split('/')[-1])
    for ln in open(f):
        if not ln.startswith('T '): continue
        d = dict(kv.split('=') for kv in ln.split()[1:])
        r = rows[key]; r[0] += 1
        r[1] += int(d['meta']); r[2] += int(d['commit'])
        v = int(d['srv']) < int(d['ack1']) + int(d['ack2'])
        if v: r[3] += 1; r[6].append((int(d['QP']), int(d['W']), int(d['trp']), int(d['delta'])))
        r[4] += int(d['ovA']) > 0; r[5] += int(d['x']) > 0; r[7] += int(d['hang'])
for k, r in rows.items():
    Ws = r[6]
    wr = (min(w for _,w,_,_ in Ws), max(w for _,w,_,_ in Ws)) if Ws else None
    tr = (min(t for *_,t,_ in [(a,b,t,dd) for a,b,t,dd in Ws]), max(t for a,b,t,dd in Ws)) if Ws else None
    dr = (min(dd for a,b,t,dd in Ws), max(dd for a,b,t,dd in Ws)) if Ws else None
    qp = collections.Counter(a for a,*_ in Ws)
    print(f"{k}: trials={r[0]} meta={r[1]} commit={r[2]} VIOL={r[3]} (simultaneous A1&A2 in {r[4]}) x_trials={r[5]} hang={r[7]} "
          f"viol_W={wr} viol_trp={tr} viol_delta={dr} viol_byQP={dict(qp)}")
