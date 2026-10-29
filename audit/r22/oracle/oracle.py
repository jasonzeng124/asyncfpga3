import re, math, sys
# parse the rig's vector table and check expected == gcd(a,b) (Python math.gcd) and == the dynamatic C (compiled separately)
src = open('/root/wt-r22/cells/hw/gcd_rig.v').read()
rows = re.findall(r"4'd(\d+):\s+vector = \{32'h([0-9A-F]+), 32'h([0-9A-F]+), 32'h([0-9A-F]+)\}", src)
for i, g, b, a in rows:
    a, b, g = int(a, 16), int(b, 16), int(g, 16)
    print(i, f"{a:08X} {b:08X} {g:08X}", "gcd=%08X" % math.gcd(a, b), "OK" if math.gcd(a, b) == g else "MISMATCH")
