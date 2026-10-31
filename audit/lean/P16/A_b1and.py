"""Auditor P16: recompute b1_and's lo-to-lo B1 row (lo Q + lo Dq - lo Dr >= 0) on the 16 committed
xarbnet outputs (formal 58251494 tools-A/xaudit/arbnet/results/xan_{d,3,4,5}_{slow,fast,gb,indep}.txt).
Independent of the new print line: from each ROW line's band-form B1 margin
  B1 = lo Q + lo Dq - hi Dr - 2     (rowsDiag; Dr = Dr1 g1 / Dr2 g2 / Dr1 R0 / Dr2 R0 band)
the lo-to-lo margin is B1 + 2 + (hi Dr - lo Dr). Compare with the printed value, report minima."""
import re, glob, sys
D = '/root/wt-f14/formal/tools-A/xaudit/arbnet/results/'
files = sorted(glob.glob(D + 'xan_[d345]_*.txt'))
files = [f for f in files if re.search(r'xan_[d345]_(slow|fast|gb|indep)\.txt$', f)]
print(len(files), 'files')
allmin = None; per = {}; mism = 0; nread = 0; arbcount = {}
for f in files:
    tag = re.search(r'xan_(\w+)_(\w+)\.txt', f).groups()
    txt = open(f).read()
    blocks = re.split(r'(?=\[xarbnet\] arbiter [^:]+: lo-to-lo)', txt)[1:]
    arbcount[tag] = len(blocks)
    rowmin = None
    for b in blocks:
        name = re.match(r'\[xarbnet\] arbiter ([^:]+):', b).group(1)
        pr = dict((k, int(v)) for k, v in re.findall(r'\((\w\d), (-?\d+)\)', re.search(r'lo-to-lo[^\[]*\[(.*?)\]\n', b).group(1)))
        m = re.search(r'Dr1 g1/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\), Dr2 g2/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\)', b)
        r1g, r1R, r2g, r2R = [(int(m.group(2*i+1)), int(m.group(2*i+2))) for i in range(4)]
        width = {'g1': r1g[1]-r1g[0], 'g2': r2g[1]-r2g[0], 's1': r1R[1]-r1R[0], 's2': r2R[1]-r2R[0]}
        rows = dict((k, int(v)) for k, v in re.findall(r'ROW \S+ (\w\d): B1 (-?\d+)', b))
        for k in ('g1', 'g2', 's1', 's2'):
            own = rows[k] + 2 + width[k]; nread += 1
            if own != pr[k]: mism += 1; print('MISMATCH', tag, name, k, own, pr[k])
            if rowmin is None or own < rowmin[0]: rowmin = (own, name.split('.')[2], k)
    per[tag] = rowmin
    if allmin is None or rowmin[0] < allmin[0]: allmin = (rowmin[0], tag, rowmin[1:])
for tag in sorted(per): print(tag, 'arbiters', arbcount[tag], 'min lo-to-lo margin', per[tag])
for kind in ('slow', 'fast', 'gb', 'indep'):
    print(kind, 'min over seeds', min(per[t][0] for t in per if t[1] == kind))
print('readers checked', nread, 'mismatches vs printed', mism, 'global min', allmin,
      'all >= 0:', all(v[0] >= 0 for v in per.values()))
