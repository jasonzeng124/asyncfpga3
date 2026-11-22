#!/usr/bin/env python3
"""adv_sdf.py SDF ARCS_TSV OUT_SDF SPEC -- an SDF with ONE delay per arc, for replaying an adversarial delay assignment
(formal's race-only adversary, FOR-RESEARCH B21) in the gate-level simulation.

SDF is the route's prjxray SDF (cells/gls/fid/xray_delay.py: every triple FAST_MIN : SLOW_MIN : SLOW_MAX), ARCS_TSV the
same run's --arcs file (all four corner columns per arc: FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX).  SPEC is a text file:

    default  POS                 every arc not matched below sits at POS of its own corner interval
    corner   fast | slow         the interval: [FAST_MIN, FAST_MAX] (fast) or [SLOW_MIN, SLOW_MAX] (slow)
    S  KIND  SRC_REGEX  DST_REGEX     arcs set to the interval's maximum (KIND: IC or IO)
    F  KIND  SRC_REGEX  DST_REGEX     arcs set to the interval's minimum
    X  POS  KIND  SRC_REGEX  DST_REGEX  arcs at POS of the interval

Regexes are matched (re.fullmatch) against the unescaped names of the arcs TSV (IC: SRC pin / DST pin; IO: INST/IN /
INST/OUT).  Every S / F / X line must match at least one arc, or the tool stops.  Each written arc carries the chosen
delay in all three columns of both triples, so the simulation reads it at any GLS_SDF_FIELD (min / max) with no
scatter.  SETUPHOLD lines and arcs the TSV does not list (none on a fresh run) are copied unchanged.  Prints, per
S / F / X line, the arcs it set.
"""
import re
import sys

RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)\s+\((\d+):(\d+):(\d+)\)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)\s+\((\d+):(\d+):(\d+)\)\)")


def unesc(s):
    return s.replace("\\", "")


def main():
    sdf, tsv, out, specf = sys.argv[1:5]
    corner, default, rules = "fast", 0.5, []
    for ln in open(specf):
        w = ln.split()
        if not w or w[0].startswith("#"):
            continue
        if w[0] == "default":
            default = float(w[1])
        elif w[0] == "corner":
            corner = w[1]
            assert corner in ("fast", "slow")
        elif w[0] in ("S", "F"):
            rules.append([1.0 if w[0] == "S" else 0.0, w[1], re.compile(w[2]), re.compile(w[3]), ln.strip(), 0])
        elif w[0] == "X":
            rules.append([float(w[1]), w[2], re.compile(w[3]), re.compile(w[4]), ln.strip(), 0])
        else:
            sys.exit("adv_sdf.py: spec line? %s" % ln)
    arcs = {}
    hdr = None
    for ln in open(tsv):
        f = ln.rstrip("\n").split("\t")
        if hdr is None:
            hdr = f
            continue
        d = dict(zip(hdr, f))
        if d["kind"] not in ("IC", "IO"):
            continue
        lo, hi = ((int(d["fast_min_ps"]), int(d["fast_max_ps"])) if corner == "fast"
                  else (int(d["slow_min_ps"]), int(d["slow_max_ps"])))
        arcs[(d["kind"], d["src"], d["dst"])] = (lo, hi)

    def value(kind, src, dst):
        lo, hi = arcs[(kind, src, dst)]
        pos = default
        for r in rules:
            if r[1] == kind and r[2].fullmatch(src) and r[3].fullmatch(dst):
                pos = r[0]
                r[5] += 1
                print("  %-60s %s %s -> %s  [%d, %d] -> %d" % (r[4][:60], kind, src, dst, lo, hi,
                                                               int(round(lo + pos * (hi - lo)))))
                break
        return int(round(lo + pos * (hi - lo)))

    o = []
    inst = None
    n = {"IC": 0, "IO": 0, "kept": 0}
    for line in open(sdf):
        m = RE_IC.search(line)
        if m:
            src, dst = unesc(m.group(1)), unesc(m.group(2))
            if ("IC", src, dst) in arcs:
                v = value("IC", src, dst)
                line = line[:m.start()] + "(INTERCONNECT %s %s (%d:%d:%d) (%d:%d:%d))" % (
                    m.group(1), m.group(2), v, v, v, v, v, v) + line[m.end():]
                n["IC"] += 1
            else:
                n["kept"] += 1
            o.append(line)
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            o.append(line)
            continue
        m = RE_IO.search(line)
        if m and inst:
            key = ("IO", inst + "/" + m.group(1), inst + "/" + m.group(2))
            if key in arcs:
                v = value(*key)
                line = line[:m.start()] + "(IOPATH %s %s (%d:%d:%d) (%d:%d:%d))" % (
                    m.group(1), m.group(2), v, v, v, v, v, v) + line[m.end():]
                n["IO"] += 1
            else:
                n["kept"] += 1
        o.append(line)
    open(out, "w").write("".join(o))
    bad = [r[4] for r in rules if r[5] == 0]
    print("adv_sdf: corner %s, default position %.3f; %d INTERCONNECT, %d IOPATH set; %d arcs kept; rules: %s"
          % (corner, default, n["IC"], n["IO"], n["kept"], ", ".join("%d" % r[5] for r in rules)))
    if bad:
        sys.exit("adv_sdf.py: rule(s) matched nothing: %s" % "; ".join(bad))


if __name__ == "__main__":
    main()
