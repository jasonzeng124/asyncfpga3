# how early does each fid output leave x? compare with min/max pin delay
import sys, json, collections
st = json.load(open(sys.argv[1])); lv = 0
obs = collections.defaultdict(list)
for l in open(sys.argv[2]):
    p = l.split()
    if p and p[0] == 'O': obs[(int(p[1]), p[2])].append((int(p[4]), p[3]))
c_before_min = 0; c_mid = 0; c_max = 0
for i, c in enumerate(st['cells']):
    if c['kind'] != 'lut': continue
    for o, T in (('6', c['T6']), ('5', c['T5'])):
        D = [max(t - 1, 0) + 1 for t in T]
        first = next((t for t, v in obs[(i, o)] if v in '01'), None)
        if first is None: continue
        if first < min(D): c_before_min += 1
        elif first < max(D): c_mid += 1
        else: c_max += 1
print('first binary value: before min D', c_before_min, '; in [minD,maxD)', c_mid, '; at >= maxD', c_max)
