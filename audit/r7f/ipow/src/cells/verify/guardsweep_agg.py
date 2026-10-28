#!/usr/bin/env python3
"""Aggregate the 24 guardsweep.py runs into one table per design.

Reads build/rloc/guardsweep/{seed}_{design}.{variant}.txt (or
{design}.{variant}.txt for the default seed), each produced by
verify/guardsweep.py, and prints:

  rows   = guardband width
  cols   = variant (base / v1 / v2)
  cell   = violations aggregated over the 4 seeds, e.g. "0/6/5/3"
           (order: default, seed1, seed2, seed3), plus worst guarded margin
           over the same 4 seeds.

Also prints, per (band, variant), the total links/elems summed over the 4
seeds -- the actual padding cost if the band were adopted everywhere.
"""
import pathlib, re, sys

OUT = pathlib.Path(__file__).resolve().parent
SEEDS = ["dflt", "seed1", "seed2", "seed3"]
DESIGNS = ["gcd_ps", "ipow_ps"]
VARIANTS = ["base", "v1", "v2"]

ROW_RE = re.compile(
    r"^(?P<name>\S.*?)\s+(?P<lo>[\d.]+)\s+(?P<hi>[\d.]+)\s+(?P<viol>-?\d+)\s+"
    r"(?P<links>-?\d+)\s+(?P<elems>-?\d+)\s+(?P<worst>[+-]?\d+|n/a)\s*$")


def path_for(seed, design, variant):
    if seed == "dflt":
        return OUT / f"{design}.{variant}.txt"
    return OUT / f"{seed}_{design}.{variant}.txt"


def parse(path):
    """-> [(name, lo, hi, viol, links, elems, worst_or_None), ...] in file order."""
    rows = []
    if not path.exists():
        return None
    for line in path.read_text().splitlines():
        m = ROW_RE.match(line)
        if not m:
            continue
        w = m.group("worst")
        rows.append((m.group("name").strip(), float(m.group("lo")),
                      float(m.group("hi")), int(m.group("viol")),
                      int(m.group("links")), int(m.group("elems")),
                      None if w == "n/a" else int(w)))
    return rows


def main():
    missing = []
    data = {}  # (design, variant, seed) -> rows
    for design in DESIGNS:
        for variant in VARIANTS:
            for seed in SEEDS:
                p = path_for(seed, design, variant)
                rows = parse(p)
                if rows is None:
                    missing.append(str(p))
                    continue
                data[(design, variant, seed)] = rows

    if missing:
        print(f"MISSING {len(missing)} file(s), aggregation is PARTIAL:",
              file=sys.stderr)
        for m in missing:
            print(f"  {m}", file=sys.stderr)

    # band names/order taken from whichever run succeeded first
    any_rows = next(iter(data.values()), None)
    if any_rows is None:
        print("no data at all", file=sys.stderr)
        return 1
    band_names = [r[0] for r in any_rows]

    for design in DESIGNS:
        print(f"\n=== {design} ===")
        header = f"{'guardband':<24}"
        for variant in VARIANTS:
            header += f"{variant:>26}"
        print(header)
        for bi, bname in enumerate(band_names):
            line = f"{bname:<24}"
            for variant in VARIANTS:
                per_seed = []
                worsts = []
                links_tot = elems_tot = 0
                ok = True
                for seed in SEEDS:
                    rows = data.get((design, variant, seed))
                    if rows is None or bi >= len(rows):
                        per_seed.append("?")
                        ok = False
                        continue
                    _, lo, hi, viol, links, elems, worst = rows[bi]
                    per_seed.append(str(viol))
                    if worst is not None:
                        worsts.append(worst)
                    links_tot += links
                    elems_tot += elems
                cell = "/".join(per_seed)
                w = min(worsts) if worsts else float("nan")
                line += f"{cell:>14} w{w:>+6.0f}" if worsts else f"{cell:>14} {'w n/a':>7}"
            print(line)
        # cost rows: total links/elems summed over 4 seeds, per band/variant
        print(f"\n  {design}: total links/elems needing padding, summed over "
              f"the 4 seeds")
        header2 = f"  {'guardband':<24}"
        for variant in VARIANTS:
            header2 += f"{variant:>18}"
        print(header2)
        for bi, bname in enumerate(band_names):
            line = f"  {bname:<24}"
            for variant in VARIANTS:
                links_tot = elems_tot = 0
                any_seed = False
                for seed in SEEDS:
                    rows = data.get((design, variant, seed))
                    if rows is None or bi >= len(rows):
                        continue
                    any_seed = True
                    _, lo, hi, viol, links, elems, worst = rows[bi]
                    links_tot += links
                    elems_tot += elems
                cell = f"{links_tot}L/{elems_tot}E" if any_seed else "?"
                line += f"{cell:>18}"
            print(line)
    return 0 if not missing else 2


if __name__ == "__main__":
    sys.exit(main())
