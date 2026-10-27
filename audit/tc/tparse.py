"""Parse tighten.py logs (one per corner SDF) -> per-row raw and banded margins.
   python3 tparse.py TAG LOG_sdf LOG_fmin LOG_fmax LOG_smin LOG_smax"""
import re, sys
PAT = [("A", re.compile(r"^\s+(\S+)\s+\d+ links\s+\S+(?: ps)?\s+req\s+(\d+)\s+peak\s+(\d+)\s+guard\s+(\d+)\s+margin\s+(-?\d+)")),
       ("F", re.compile(r"^\s+(\S+)\s+\d+ links\s+flushed\s+(\d+)\s+reusable\s+(\d+)\s+guard\s+(\d+)\s+margin\s+(-?\d+)")),
       ("HI", re.compile(r"^\s+(\S+)\s+\d+ links\s+close\s+(\d+)\s+data\s+(\d+)\s+guard\s+(\d+)\s+margin\s+(-?\d+)"))]
def parse(p):
    out = {}
    for line in open(p):
        for r, pat in PAT:
            m = pat.match(line)
            if m:
                a, b = int(m.group(2)), int(m.group(3))
                late_req, data = (b, a) if r == "F" else (a, b)
                out[(r, m.group(1))] = (late_req, data, int(m.group(4)), int(m.group(5)))
    return out
tag, logs = sys.argv[1], sys.argv[2:]
P = [parse(l) for l in logs]
names = ["sdf", "fmin", "fmax", "smin", "smax"]
print("seed\trule\trow\tsdf_raw\tsdf_rule\tfast_raw\tslow_raw\tfastG\tslowG\tmix_raw\tmixG\tsmax_rule")
C = {"fast": (1, 2), "slow": (3, 4), "mix": (1, 4)}
for k in sorted(P[0]):
    if not all(k in x for x in P): continue
    cols = [tag, k[0], k[1].replace("urig.udut.", ""), P[0][k][0] - P[0][k][1], P[0][k][3]]
    raw, band = {}, {}
    for c, (a, b) in C.items():
        q, d = P[a][k][0], P[b][k][1]
        raw[c], band[c] = q - d, round(0.772 * q - 1.155 * d)
    cols += [raw["fast"], raw["slow"], band["fast"], band["slow"], raw["mix"], band["mix"], P[4][k][3]]
    print("\t".join(map(str, cols)))
