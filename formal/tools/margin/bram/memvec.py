#!/usr/bin/env python3
"""margin/bram/memvec.py (shard C, UNTRUSTED): a research benchvec (v2) vector file -> simx's operands and RAM file.

    python3 memvec.py VEC.hex EXP.txt MEMEXP.txt NET.json KERNEL_BENCH.v OUTDIR

VEC.hex: research's v2 vectors (per call: the operand words, then every array's elements, one 32-bit word each).
EXP.txt / MEMEXP.txt: research/tools/suite/oracle_mem.sh's output for VEC (ORACLE_RUNS=1, ORACLE_MEMOUT=MEMEXP): the
result per call and every array's final contents, computed from the kernel's C (never from a run).
Writes OUTDIR/pairs.txt (simx --pairs: the first operand word as a, the second as b, or the one word twice),
OUTDIR/want.txt (simx --want), OUTDIR/mem.txt (simx --mem: "F k id addr word16" = the host's fill before call k,
"X k id addr word16" = the contents expected after call k). The fill is written into the RAM's contents directly
(the bench's host port, its arbiter slot and its timing are NOT simulated: a host-fill race is outside this check).
Array -> RAMs: the kernel's port <array>_host_req feeds <ctrl>_uport's s_req (KERNEL_BENCH.v); the port's RAMs are
<ctrl>_uport.umem<j>.uram, holding bits 16j .. 16j+15 of each word (bdc's bdc_memport: DW 32 = two x18 RAMs); the word
address is the element index. Arrays are numbered in the order of their <array>_host_req ports in the module header,
which is the C signature order oracle_mem.sh uses (checked only by the readback of a correct route).
"""
import json, os, re, sys

vecf, expf, memf, netf, kvf, out = sys.argv[1:7]
os.makedirs(out, exist_ok=True)
L = [l.strip() for l in open(vecf)]
m = re.match(r"^// benchvec words=(\d+) mems=(\d+)", L[0])
if not m:
    sys.exit("memvec: %s has no v2 header" % vecf)
nw, nm = int(m.group(1)), int(m.group(2))
calls, cur = [], None
for l in L[1:]:
    if l.startswith("// call"):
        cur = {"ops": [], "arrs": []}; calls.append(cur); continue
    if l.startswith("//"):
        if cur is not None and len(cur["ops"]) == nw:
            cur["arrs"].append([])
        continue
    if not l or cur is None:
        continue
    for w in l.split():
        if len(cur["ops"]) < nw:
            cur["ops"].append(int(w, 16))
        else:
            cur["arrs"][-1].append(int(w, 16))
for c in calls:
    if len(c["arrs"]) != nm:
        sys.exit("memvec: a call with %d arrays, header says %d" % (len(c["arrs"]), nm))
exp = [l.strip() for l in open(expf) if l.strip()]
if len(exp) != len(calls):
    sys.exit("memvec: %d results for %d calls" % (len(exp), len(calls)))
mexp = {}
for l in open(memf):
    mm = re.match(r"^call=(\d+) mem=(\d+) data=([0-9a-fA-F,]*)", l.strip())
    if mm:
        mexp[(int(mm.group(1)), int(mm.group(2)))] = [int(x, 16) for x in mm.group(3).split(",") if x]
kv = open(kvf).read()
hdr = re.findall(r"input\s+wire\s+(\w+)_host_req\b", kv)
arrays = list(dict.fromkeys(hdr))
if len(arrays) != nm:
    sys.exit("memvec: kernel host ports %s, vectors have %d arrays" % (arrays, nm))
ctrl = {}
for a in arrays:
    mm = re.search(r"(\w+)_uport\s*\(\s*\.rst\(rst\),\s*\.s_req\(\{%s_host_req\b" % re.escape(a), kv)
    if not mm:
        sys.exit("memvec: no port whose s_req takes %s_host_req" % a)
    ctrl[a] = mm.group(1)
N = json.load(open(netf))
rid = {}
for r in N.get("rams", []):
    mm = re.match(r"^.*\.udut\.(\w+)_uport\.umem(\d+)\.uram$", r.get("json_cell") or "")
    if mm:
        rid[(mm.group(1), int(mm.group(2)))] = r["id"]
lines = []
for k, c in enumerate(calls):
    for ai, a in enumerate(arrays):
        rams = sorted(j for (cc, j) in rid if cc == ctrl[a])
        if not rams:
            sys.exit("memvec: no RAM of %s_uport in the net" % ctrl[a])
        for tag, words in (("F", c["arrs"][ai]), ("X", mexp.get((k, ai)))):
            if words is None:
                sys.exit("memvec: no expected contents for call %d array %d" % (k, ai))
            for adr, w in enumerate(words):
                for j in rams:
                    lines.append("%s %d %d %d %04x" % (tag, k, rid[(ctrl[a], j)], adr, (w >> (16 * j)) & 0xffff))
open(os.path.join(out, "mem.txt"), "w").write("\n".join(lines) + "\n")
ops = [c["ops"] + c["ops"][:1] if nw == 1 else c["ops"][:2] for c in calls]
open(os.path.join(out, "pairs.txt"), "w").write(" ".join("0x%x,0x%x" % (o[0], o[1]) for o in ops) + "\n")
open(os.path.join(out, "want.txt"), "w").write(",".join("0x" + e for e in exp) + "\n")
print("memvec: %d calls, %d operand words, arrays %s -> %s, RAMs %s; %d mem lines" % (len(calls), nw, arrays,
      [ctrl[a] for a in arrays], sorted(rid.items()), len(lines)), file=sys.stderr)
