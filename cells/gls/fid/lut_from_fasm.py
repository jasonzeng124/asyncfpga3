#!/usr/bin/env python3
"""A narrow FASM -> netlist step: LUT pin decoding only.  A TEST DOUBLE for
F2, so that cells/gls/fid/acceptance.py can show it is able to report a
match on a bitstream bug, not a substitute for a real FASM netlist.

    python3 lut_from_fasm.py <design.fasm> <routed.json> <out.json>

For every LUT site it reads the INIT the FASM actually holds.  Where that is
the patched encoding of the routed JSON's cells, the cells are copied as they
are.  Where it is instead what the UNPATCHED nextpnr writer would have made of
them (verify/fasm_audit.py unpatched_lut_names: split on ' ', an unknown token
read as I0), each cell's X_ORIG_PORT_A<n> is rewritten to that reading
('I2I0 ' -> 'I0 I0'), which makes cells/gls/gen.py decode exactly the
function the bitstream holds.  Any other INIT is an error: this script does
not know how to model it, and saying nothing would be the very failure it
exists to expose.

What it does NOT do: routing, DSPs, flops, carry chains, IO -- anything but
the meaning of a LUT's input pins.  A real F2 replaces it.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "verify"))
import fasm_audit as fa  # noqa: E402


def main(fasm, routed, out):
    d = json.loads(Path(routed).read_text())
    mods = d["modules"]
    top = next(m for m in mods.values() if "1" in str(m.get("attributes", {}).get("top", ""))) \
        if len(mods) > 1 else next(iter(mods.values()))
    cells = top["cells"]
    _, vecs = fa.read_fasm(fasm)
    sites = fa.load_sites()
    by_site = {}
    for c in cells.values():
        if c["type"] != "SLICE_LUTX":
            continue
        m = fa.RE_BEL.match(c["attributes"].get("NEXTPNR_BEL", ""))
        by_site.setdefault((m.group(1), m.group(2)), {})[m.group(3)] = c
    same = rewritten = 0
    for (site, letter), slot in by_site.items():
        got = vecs.get(f"{fa.slice_prefix(site, sites)}.{letter}LUT.INIT")
        good = fa.expected_lut_bits(slot.get("6"), slot.get("5"))
        if got == good:
            same += 1
            continue
        bad = fa.expected_lut_bits(slot.get("6"), slot.get("5"), fa.unpatched_lut_names)
        if got != bad:
            sys.exit(f"lut_from_fasm: {site}/{letter}LUT holds an INIT that is neither the "
                     f"patched nor the unpatched encoding -- not modelled")
        for c in slot.values():
            for k in range(6):
                key = f"X_ORIG_PORT_A{k + 1}"
                if key in c["attributes"]:
                    c["attributes"][key] = " ".join(
                        f"I{n}" for n in fa.unpatched_lut_names(c["attributes"], k))
        rewritten += 1
    Path(out).write_text(json.dumps(d))
    print(f"lut_from_fasm: {same} LUT sites as routed, {rewritten} rewritten to the FASM's reading")


if __name__ == "__main__":
    main(*sys.argv[1:4])
