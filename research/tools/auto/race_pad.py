#!/usr/bin/env python3
"""race_pad.py RACE_TXT ZMIN CUR.vh PROP.vh NEG.tsv [PREFIX] -- the sizing loop's latch-fed steer check (auto_size.sh
AUTO_RACE_Z): read research/tools/race_find.py's lines for one route (every steer whose condition comes from a link
latch and whose request crosses that link's request line, the draw model's margin mean / sd per race), and for every race
below ZMIN sd: raise the link's request line (BD_SZ_<PREFIX><LINK>, the link's DELAY) in the rule's proposal PROP.vh to
at least one element above CUR.vh, and append a row "R <margin> R <steer> line" to the rule's NEG.tsv, so the loop counts
the route as not clean and builds the next one with the link longer (ratchet.py pins the raise).

Why (formal B21 / B28, research/data/ssta/README.md): the rule measures this pair with guards of 3 %, about one standard
deviation of the draw model's scatter on two ~1.1 ns paths; on suite13t xorshift s1 (rule CLEAN) the race at ucond_br9
was 140 +- 48 ps, 0.2 % of the model's points below zero. One more element on the link's request line adds ~150-250 ps
to the request side only. Prints one summary line."""
import re
import sys


def rd(p):
    out, order, lines = {}, [], []
    for ln in open(p):
        lines.append(ln)
        m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
        if m:
            out[m.group(1)] = int(m.group(2))
            order.append(m.group(1))
    return out, order, lines


def main():
    rt, zmin, curp, propp, negp = sys.argv[1:6]
    pre = "BD_SZ_" + (sys.argv[6] if len(sys.argv) > 6 else "BRIDGE_I_UDUT_")
    zmin = float(zmin)
    re_line = re.compile(r"^(\S+) \(\S+ cond \S+, req \S+\) link (\S+): .*margin F - S mean (-?\d+) ps, sd (\d+) ps "
                         r"\(mean / sd (-?[\d.]+|inf)\)")
    races = []
    for ln in open(rt):
        m = re_line.match(ln)
        if m:
            z = float(m.group(5)) if m.group(5) != "inf" else 1e9
            races.append((z, m.group(1), m.group(2), int(m.group(3)), int(m.group(4))))
    if not races:
        print("race: no latch-fed steer race found")
        return
    cur, _, _ = rd(curp)
    prop, porder, plines = rd(propp)
    short = [r for r in races if r[0] < zmin]
    padded = {}
    for z, steer, link, mean, sd in short:
        mac = pre + link.upper()
        if mac not in cur:
            continue
        want = max(prop.get(mac, cur[mac]), cur[mac] + 1)
        padded[mac] = max(padded.get(mac, 0), want)
    if padded:
        out = []
        for ln in plines:
            m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
            if m and m.group(1) in padded:
                ln = "`define %s %d   // race_pad: latch-fed steer below %.1f sd\n" % (m.group(1), padded[m.group(1)], zmin)
                padded_seen = True
            out.append(ln)
        missing = [m for m in padded if m not in prop]
        out += ["`define %s %d   // race_pad: latch-fed steer below %.1f sd\n" % (m, padded[m], zmin) for m in missing]
        open(propp, "w").write("".join(out))
        with open(negp, "a") as f:
            for z, steer, link, mean, sd in short:
                f.write("R\t%d\tR %s (latch %s: %d +- %d ps, %.2f sd)\tline\n" % (mean - int(round(zmin * sd)), steer,
                                                                                link, mean, sd, z))
    w = min(races)
    print("race: %d latch-fed steer race(s), weakest %s (%s) %.2f sd; below %.1f sd: %d%s" % (
        len(races), w[1], w[2], w[0], zmin, len(short),
        (" -> padded " + ", ".join("%s %d->%d" % (m, cur[m], v) for m, v in sorted(padded.items()))) if padded else ""))


if __name__ == "__main__":
    main()
