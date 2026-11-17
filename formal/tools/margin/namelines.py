#!/usr/bin/env python3
"""margin/namelines.py ROUTED.json < text > text (shard C, UNTRUSTED naming): append the yosys instance nextpnr placed at
each decoded LUT node named in the text (SLICE_XxYy.<L>6 / .<L>5, or SLICE_XxYy.<L>LUT.O6 / .O5) as NODE{cell}."""
import json, re, sys
def belmap(routed):
    return {c["attributes"].get("NEXTPNR_BEL"): n for n, c in json.load(open(routed))["modules"]["top"]["cells"].items()
            if c.get("attributes", {}).get("NEXTPNR_BEL")}
PAT = re.compile(r"\b(SLICE_X\d+Y\d+)\.([A-D])(?:LUT\.O)?([56])\b")
def name(bel, text):
    return PAT.sub(lambda m: "%s{%s}" % (m.group(0), bel.get("%s/%s%sLUT" % m.groups(), "?")), text)
if __name__ == "__main__":
    sys.stdout.write(name(belmap(sys.argv[1]), sys.stdin.read()))
