#!/usr/bin/env python3
"""Event windows of the pipe3 controllers under the OPEN-LOOP stimulus of
designs/pipe3.stim.json, from the counter-domain inequalities that Events2 proves
for every behaviour (untrusted arithmetic, evidence for A-events2):

  lower (Beh.M_le_pin, walk_le):  M t j <= M (t - lo_jp) (src j p) + off j p   for every pin
  upper (Beh.ge_pins):            once the reset pin is low at F t,
                                  M t j >= min_p M (t - hi_jp) (src j p) + off j p
  reset:                          M t j = 0 while rst is high at the LUT sample

so the k-th event of c_j lies in [early(j,k), late(j,k)] with
  early(j,k) = max(T + loR + loF, max_p early(src, k - off) + lo_jp)
  late(j,k)  = max(T + hiR + hiF, max_p late(src, k - off) + hi_jp)
(an environment pin's source events are the stimulus edges, exact). Printed next
to the X windows XSim reported (results/pipe3_slow_corner.txt). Also checks the
environment half of `Back` for this stimulus: every sender edge n comes after the
latest (n-1)-th event of c0, every receiver edge n after the latest n-th event of
c2, each by at least the own-feedback-minus-route margin (hiQ - loG).
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, "..", "designs")
stim = json.load(open(os.path.join(D, "pipe3.stim.json")))
U = 10
LUT, ROUTE, FB = (9, 13), (36, 44), (27, 33)
T = next(e["t_ps"] for e in stim["events"] if "rst" in e["set"]) // U
env = {"req_in": [], "ack_out": []}
for e in stim["events"]:
    for k in env:
        if k in e["set"]:
            env[k].append(e["t_ps"] // U)
# pins: (src, off, lo, hi); src is a stage index or an env port name
chain = (2 * ROUTE[0] + LUT[0], 2 * ROUTE[1] + LUT[1])
pins = {0: [("req_in", 0, ROUTE), (1, 1, ROUTE)],
        1: [(0, 0, chain), (2, 1, ROUTE)],
        2: [(1, 0, chain), ("ack_out", 1, ROUTE)]}
K = 4
early, late = {}, {}
def ev(tab, s, k, which):
    if k <= 0:
        return 0
    if isinstance(s, str):
        return env[s][k - 1] if k <= len(env[s]) else None
    return tab.get((s, k))
for k in range(1, K + 1):
    for j in range(3):
        e = T + ROUTE[0] + LUT[0]; l = T + ROUTE[1] + LUT[1]; ok = True
        for (s, off, b) in pins[j]:
            a = ev(early, s, k - off, 0); z = ev(late, s, k - off, 1)
            if a is None or z is None:
                ok = False; break
            e = max(e, a + LUT[0] + b[0]); l = max(l, z + LUT[1] + b[1])
        if ok:
            early[(j, k)], late[(j, k)] = e, l
xs = open(os.path.join(HERE, "..", "results", "pipe3_slow_corner.txt")).read()
names = {0: "stage[0].u.ctl.u/O", 1: "stage[1].u.ctl.u/O", 2: "stage[2].u.ctl.u/O"}
print("event windows of the controller outputs, ps (counter domain = [early, late); XSim = X window [a, b] + 10 ps)")
for j in range(3):
    blk = xs.split("STORAGE " + names[j])[1].split("STORAGE")[0]
    xw = [(int(a), int(b)) for a, b in re.findall(r"X \[(\d+), (\d+)\] ps: transition", blk)]
    for k in range(1, K + 1):
        if (j, k) not in early:
            continue
        cd = (early[(j, k)] * U, late[(j, k)] * U)
        x = xw[k - 1] if k - 1 < len(xw) else None
        xr = f"[{x[0]}, {x[1] + U}]" if x else "-"
        same = "same" if x and (x[0], x[1] + U) == cd else "DIFFERENT"
        print(f"  c{j} event {k}: counter [{cd[0]}, {cd[1]}]  XSim {xr}  {same}")
# environment half of Back for this open-loop stimulus
m = FB[1] - ROUTE[0]
bad = []
for n, tau in enumerate(env["req_in"], 1):
    if n >= 2 and not (late[(0, n - 1)] + m <= tau):
        bad.append(f"req_in edge {n} at {tau*U} ps before c0 event {n-1} is surely done ({late[(0, n-1)]*U} ps)")
for n, tau in enumerate(env["ack_out"], 1):
    if not (late[(2, n)] + m <= tau):
        bad.append(f"ack_out edge {n} at {tau*U} ps before c2 event {n} is surely done ({late[(2, n)]*U} ps)")
print("environment waits for its partner in every behaviour (env half of Back):", "yes" if not bad else "NO")
for b in bad:
    print("  ", b)
