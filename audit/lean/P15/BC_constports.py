#!/usr/bin/env python3
"""Auditor P15bc: for every bdc_fused_* instance in bdc's gcd_kernel.v, trace each e<i>_data port
back through `assign x = y;` and bd_link data_in->data_out until a constant (`assign x = N'hV;`)
or something else (unit output, merge/mux output, start value ...). Prints the constant ports.
Usage: python3 -I BC_constports.py gcd_kernel.v"""
import re, sys
src = open(sys.argv[1]).read()
top = src[src.rfind("\nmodule "):]          # the last module = the kernel top
assign = {}
for a, b in re.findall(r"assign\s+(\w+)\s*=\s*([^;]+);", top):
    assign[a] = b.strip()
for din, dout in re.findall(r"\.data_in\((\w+)\),\s*\.req_out\(\w+\),\s*\.ack_out\(\w+\),\s*\.data_out\((\w+)\)", top):
    assert dout not in assign; assign[dout] = din
def trace(n, depth=0):
    path = [n]
    while n in assign and depth < 50:
        n = assign[n]; path.append(n); depth += 1
    return path
for inst in re.finditer(r"bdc_fused_(\w+)\s*#\([^)]*\)\)\s*(\w+)\s*\((.*?)\);", top, re.S):
    mod, name, body = inst.groups()
    ports = dict(re.findall(r"\.(e\d+)_data\((\w+)\)", body))
    out = []
    for p in sorted(ports):
        path = trace(ports[p]); last = path[-1]
        tag = ("CONST " + last) if re.fullmatch(r"\d+'[hd][0-9a-fA-F]+", last) else ("from " + last)
        out.append("%s<-%s" % (p, tag))
    print("%-9s %s" % (mod, "; ".join(out)))
