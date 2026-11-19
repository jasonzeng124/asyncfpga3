# place_from.py -- nextpnr-xilinx --pre-place script: keep the previous route's placement (build_bench.sh BD_PLACE_FROM).
#
# Runs inside nextpnr (ctx is its context), after packing and before placement.  Every cell whose name is in the
# previous route's routed JSON (BD_PLACE_FROM, its NEXTPNR_BEL attributes) is bound to the same BEL, so the placer
# leaves it there; cells that are new (a delay line that grew) are placed around them.  Cells with an XDC location
# are left to the placer's own constraint pass.
# Strength (BD_PLACE_STRENGTH, default fixed): STRENGTH_FIXED.  Measured on test_bool_array s1 it 6 from it 5:
# 'user' keeps every cell but the router then does not permute the LUT input pins of the bound cells, and the LUT5 /
# LUT6 pairs the packer starts on the same physical pin (A1) stay in conflict (55 overused site wires, no route);
# 'strong' lets the post-place repair move 681 cells; 'fixed' keeps all 6130 (only the 3 new cells are relocated),
# the router permutes 8313 LUT pins and converges, bench clock 111.5 MHz.
#
# Why (research/data/converge/notes.txt): the automatic sizing loop re-routes after every size change, and a re-route
# moves each constraint's margin by ~0.5 ns (sd) even where none of its lines changed -- on test_bool_array seed 1,
# it 5 -> it 6 added 3 delay elements and 6051 of the 6136 cells the two routes share changed BEL.  The loop then chases
# fresh misses (95 % of the rows short on a finish route were not short on the route before).  With the placement kept,
# a size change moves only the cells it adds.
#
# BD_PLACE_FREE (optional regex): cells whose names match are left for the placer even when the previous route had
# them (e.g. a line whose length changed, to let it be laid out again as a whole).
# Prints "place_from: bound N of M cells (new K, free R, taken T, type-mismatch Y)".
import json, os, re

src = os.environ["BD_PLACE_FROM"]
free_rx = os.environ.get("BD_PLACE_FREE", "")
free_re = re.compile(free_rx) if free_rx else None
STRENGTH = {"user": STRENGTH_USER, "locked": STRENGTH_LOCKED, "fixed": STRENGTH_FIXED, "strong": STRENGTH_STRONG}[
    os.environ.get("BD_PLACE_STRENGTH", "fixed")]
if src.endswith(".json"):            # a routed JSON: its NEXTPNR_BEL attributes
    with open(src) as f:
        d = json.load(f)
    top = [m for m in d["modules"].values()
           if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in m.get("cells", {}).values())]
    prev = {n: c["attributes"]["NEXTPNR_BEL"] for n, c in top[0]["cells"].items() if "NEXTPNR_BEL" in c.get("attributes", {})}
else:                                # research/tools/auto/auto_size.sh's place_I.txt: "cell<TAB>bel" per line
    prev = {}
    with open(src) as f:
        for ln in f:
            if ln.strip() and not ln.startswith("#"):
                n, b = ln.rstrip("\n").split("\t")
                prev[n] = b
# yosys numbers abc's cells from a counter shared by the whole run ($abc$<run>$auto$blifparse.cc:<l>:parse_blif$<k>),
# and a kernel whose size changed shifts <run> and every <k> of the harness's LUTs by the same amount (xorshift s1 it 5
# -> 6: 21205 -> 21209; only 3687 of 7533 names matched).  The cell is the same: key it by k - run.  A key two cells
# of one route share is dropped (no guess).
RE_ABC = re.compile(r"\$abc\$(\d+)\$auto\$blifparse\.cc:(\d+):parse_blif\$(\d+)")


def norm(name):
    return RE_ABC.sub(lambda m: "$abc$*$auto$blifparse.cc:%s:parse_blif$+%d" % (m.group(2), int(m.group(3)) - int(m.group(1))),
                      name)


nprev, dup = {}, set()
for k, b in prev.items():
    q = norm(k)
    if q in nprev:
        dup.add(q)
    nprev[q] = b
for q in dup:
    del nprev[q]
# Then by order within a name class: the other auto-numbered names ($auto$ff.cc:..$N, $auto$alumacc.cc:..$N.carry4, ...)
# keep their count and their order while some of their numbers move (xorshift s1 it 5 -> 6: 9 carry chains all +4, a
# block of 104 of 1910 flops renumbered).  The cells neither key matched are paired in numeric order inside each class
# (digits replaced), and only where the class has as many unmatched cells on both sides; else they are left new.
cur = [nm for nm, _ in ctx.cells]
hit = {nm: (prev.get(nm) or nprev.get(norm(nm))) for nm in cur}
used = {b for b in hit.values() if b}
klass = lambda nm: re.sub(r"\d+", "N", nm)
nums = lambda nm: tuple(int(x) for x in re.findall(r"\d+", nm))
left_prev, left_cur = {}, {}
for k, b in prev.items():
    if b not in used:
        left_prev.setdefault(klass(k), []).append(k)
for nm in cur:
    if not hit[nm]:
        left_cur.setdefault(klass(nm), []).append(nm)
ranked = 0
for c, lc in left_cur.items():
    lp = left_prev.get(c, [])
    if lp and len(lp) == len(lc):
        for a, b in zip(sorted(lc, key=nums), sorted(lp, key=nums)):
            hit[a] = prev[b]
            ranked += 1
n = new = freed = taken = mism = bound = 0
for name, cell in ctx.cells:
    n += 1
    bel = hit.get(name)
    if bel is None:
        new += 1
        continue
    if free_re is not None and free_re.search(name):
        freed += 1
        continue
    if cell.bel is not None:          # already placed (a packer constraint): leave it
        continue
    if any(kv.first == "BEL" for kv in cell.attrs):   # an XDC / user location: the placer binds it itself
        continue
    if ctx.getBelType(bel) != cell.type:
        mism += 1
        continue
    if not ctx.checkBelAvail(bel):
        taken += 1
        continue
    ctx.bindBel(bel, cell, STRENGTH)
    bound += 1
print("place_from: bound %d of %d cells (new %d, free %d, taken %d, type-mismatch %d, ambiguous keys %d, paired by order %d) from %s"
      % (bound, n, new, freed, taken, mism, len(dup), ranked, src))
