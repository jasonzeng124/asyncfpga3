#!/usr/bin/env python3
"""inventory_md.py -- research/data/fid/inventory.md from inventory.json.

    python3 cells/gls/fid/inventory_md.py [--check]

inventory.json is the copy acceptance.py reads; inventory.md is generated
from it and never edited by hand.  One table row per item: the title and its
oracle (JSON, cut at 160 characters), the grade and its reason, the sources,
and how the datum is reproducible today; for an item acceptance.py can run on
a local route (route_dir), that route and how it is produced.  --check exits 1
if inventory.md is not what this would write.
"""
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
INV = REPO / "research/data/fid/inventory.json"
MD = REPO / "research/data/fid/inventory.md"

HEAD = """# Silicon data inventory for the board-fidelity GLS (F4)

Generated from `inventory.json` (the machine-readable copy `cells/gls/fid/acceptance.py` reads). \
Graded per research/PROGRAM.md "THE priority": **hard** = well-established, a model that disagrees is wrong; \
**soft** = evidence to investigate; **excluded** = the instrument was not verified.

| id | datum (oracle) | grade, and why | source | reproducible today |
|---|---|---|---|---|
"""


def row(it):
    repro = it.get("reproducible", "")
    if it.get("route_build"):
        # only items that carry route_build get the extra text: every other row is unchanged
        repro += "; acceptance.py route `%s`, produced by: %s" % (
            it["route_dir"], " ; ".join("`%s`" % c for c in it["route_build"]))
    return "| %s | %s: %s | **%s**: %s | %s | %s |" % (
        it["id"], it["title"], json.dumps(it.get("oracle", {}))[:160], it["grade"], it["grade_reason"],
        ", ".join(it["sources"]), repro)


def render(inv):
    return HEAD + "".join(row(it) + "\n" for it in inv["items"])


def main():
    text = render(json.loads(INV.read_text()))
    if "--check" in sys.argv[1:]:
        ok = MD.read_text() == text
        print("inventory.md is %s" % ("up to date" if ok else "STALE: run cells/gls/fid/inventory_md.py"))
        return 0 if ok else 1
    MD.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
