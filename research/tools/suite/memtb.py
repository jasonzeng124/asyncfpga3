#!/usr/bin/env python3
"""memtb.py -- RTL check of a memory kernel, the recipe of research/tools/suite/tb_store1.v made generic.

    memtb.py KERNEL VEC.hex [--runs R] [--calls N] [--timeout-us T] [--out DIR] [--vcd] [--dut FILE]

simcheck.py drives scalars only.  This drives any kernel bdc emits with a host port on every memory (`--host-mem`, what
the bench builds): per call, fill every array through its host slot, send every argument (scalars, the memories'
starts, start) and take every result, R runs on the same arrays without refilling (as ps7_bench.v does), then read
every array back.  Zero-wire-delay RTL (cells/sim/bd_prims_sim.v arcs): it shows the handshakes complete and compute
the C's answer and final arrays, nothing about routed timing.  BDC_AUTO and the other bdc switches are read from the
environment, as emit.py reads them.

Vectors: a v2 file (research/data/suite/bench/README.md; research/tools/suite/memvec.py writes one): per call the
operand words in signature order, then every element of each memref in signature order.
Expected values: the kernel's C (kernels/K, research/data/suite/dynsrc/K, dynamatic/integration-test[/memory]/K),
through research/tools/suite/oracle_mem.sh where it accepts the kernel; for a kernel it refuses (void, or an array of
more than one dimension -- most of Dynamatic's store tests) through the same recipe here (gcc -O1 -fwrapv,
CALL_KERNEL stubbed, main renamed), an N-D array filled and read back row-major, as the frontend flattens it.
Never recorded from a run.

Per call it prints `MEMTB call=J run=R out0=... exp=... ok|BAD` (a kernel with a data result) and `MEMTB call=J mem=M
bad=K`; a run that does not finish within T us of circuit time prints `MEMTB TIMEOUT call=J run=R` with every
result's token count and stops.  Last line: `MEMTB SUMMARY PASS|FAIL|TIMEOUT ...`.

THE RAM BOUNDARY IN THIS MODEL.  bd_mem's acknowledge is the RAM clock delayed by DCO LUT arcs, and the read data is
valid the RAM's clock-to-out after the same edge (cells/sim/bd_prims_sim.v BD_RAM_TCO, 2454 ps, prjxray's max).  bdc
emits DCO = 12, a placeholder: a route meets DCO >= clock-to-out because verify/tighten.py rule C checks it and the gate
simulates it.  Here, at zero wire delay, 12 arcs are 1488 ps: the acknowledge announces the word ~1 ns before it
exists, and a load that captures its word at the acknowledge (bdc_load_cap: every load on an arbitrated port) returns
the PREVIOUS word on its port -- wrong values that are this model's, not the kernel's (research/data/suite/memorder.md).
So by default every RAM port's DCO parameter is raised, in this testbench only, to cover the clock-to-out at this
--route-ps (`MEMTB note: DCO ...`), as rule C requires of a route; --keep-dco keeps the emitted value.  Either way a
monitor on every bd_mem reports read data that changes while its acknowledge is already high (`MEMTB RAM-BOUNDARY`,
counted in the summary as a failure), and the RAM model's setup violations and the port's one-hot check are printed
and counted, not left in run.log.

--jitter SEED[:PCT] compiles cells/sim with BD_JITTER: every LUT arc of the design scattered per instance by up to
+-PCT percent (default 30), reproducibly per SEED -- an order that holds only at the nominal arcs fails under some
seed.  Under --jitter the setup line (DSETUP) is covered too, since its chain scatters with everything else.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
sys.path.insert(0, os.path.join(R, "bdc"))
import emit  # noqa: E402
from hs import parse  # noqa: E402


def csource(k):
    for d in (os.path.join(R, "kernels", k), os.path.join(R, "research", "data", "suite", "dynsrc", k),
              os.path.join(R, "dynamatic", "integration-test", k),
              os.path.join(R, "dynamatic", "integration-test", "memory", k)):
        if os.path.exists(os.path.join(d, k + ".c")):
            return d
    sys.exit(f"memtb: no C source for {k}")


def driver_c(k, src_dir, held):
    """A C driver for kernels oracle_mem.sh refuses: void results and N-D arrays (flattened row-major)."""
    src = open(os.path.join(src_dir, k + ".c")).read()
    s = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
    s = re.sub(r"//[^\n]*", " ", s)
    m = re.search(r"(^|[;}\n])\s*([A-Za-z_][\w \t]*?)\b" + re.escape(k) + r"\s*\(([^)]*)\)\s*\{", s)
    if not m:
        sys.exit(f"memtb: no definition of {k}(...) {{ in the C")
    ret = re.sub(r"\b(static|inline|extern)\b", "", m.group(2)).strip()
    params = [p.strip() for p in m.group(3).split(",") if p.strip() and p.strip() != "void"]
    scal, arrs, args = [], [], []
    for p in params:
        if "*" in p:
            sys.exit(f"memtb: {k} has a pointer argument ({p})")
        am = re.match(r"(.+?)\s*\b([A-Za-z_]\w*)\s*((\[[^\]]+\])+)\s*$", p)
        if am:
            arrs.append((am.group(1).strip(), am.group(3), am.group(2)))
            args.append("b%d" % (len(arrs) - 1))
            continue
        pm = re.match(r"(.+?)\s*\b([A-Za-z_]\w*)$", p)
        scal.append(pm.group(1).strip())
        args.append("a%d" % (len(scal) - 1))
    if [n for _, _, n in arrs] != held:
        sys.exit(f"memtb: the frontend's memrefs {held} are not all of {k}'s C arrays in C order {[n for _, _, n in arrs]}")
    hdr = os.path.exists(os.path.join(src_dir, k + ".h"))
    bufs = "\n".join("static %s b%d%s;" % (t, i, d) for i, (t, d, _) in enumerate(arrs))
    nel = "\n".join("  nel[%d] = (int)(sizeof(b%d) / sizeof(%s)); esz[%d] = (int)sizeof(%s);" % (i, i, t, i, t)
                    for i, (t, _d, _n) in enumerate(arrs))
    decl = "\n".join("    %s a%d = (%s)take(w, &k, (int)sizeof(%s));" % (t, i, t, t) for i, t in enumerate(scal))
    words = " + ".join("(int)sizeof(%s) / 4" % t for t in scal) or "0"
    fill = "\n".join("    for (i = 0; i < nel[%d]; i++) ((%s *)b%d)[i] = (%s)w[k++];" % (i, t, i, t)
                     for i, (t, _d, _n) in enumerate(arrs))
    dump = "\n".join(('    if (mo) { fprintf(mo, "call=%%d mem=%d data=", call); for (i = 0; i < nel[%d]; i++) '
                      'fprintf(mo, "%%s%%08x", i ? "," : "", (unsigned)((%s *)b%d)[i] & msk(esz[%d])); '
                      'fprintf(mo, "\\n"); }') % (i, i, t, i, i) for i, (t, _d, _n) in enumerate(arrs))
    void = ret == "void"
    call = ("%s(%s);" % (k, ", ".join(args))) if void else ("res = (unsigned)%s(%s);" % (k, ", ".join(args)))
    return '''#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include "%(inc)s"
%(bufs)s
static int nel[16], esz[16];
static unsigned long long take(const unsigned *w, int *k, int bytes) {
  unsigned long long v;
  if (bytes <= 4) { v = w[*k]; *k += 1; } else { v = (unsigned long long)w[*k] | ((unsigned long long)w[*k + 1] << 32); *k += 2; }
  return v;
}
static unsigned msk(int bytes) { return bytes >= 4 ? 0xffffffffu : (1u << (8 * bytes)) - 1u; }
int main(int argc, char **argv) {
  static unsigned w[1 << 22];
  int nw, nm, nwords = 0, call, i, r, runs = atoi(argv[2]), per;
  char line[512];
  FILE *f = fopen(argv[1], "r"), *mo = fopen(argv[3], "w");
%(nel)s
  if (!f || !fgets(line, sizeof line, f) || sscanf(line, "// benchvec words=%%d mems=%%d", &nw, &nm) != 2) return 2;
  if (nw != %(words)s || nm != %(narr)d) { fprintf(stderr, "memtb: words=%%d mems=%%d do not fit the C\\n", nw, nm); return 2; }
  while (nwords < (1 << 22) && fscanf(f, " %%x", &w[nwords]) == 1) nwords++;
  per = nw; for (i = 0; i < %(narr)d; i++) per += nel[i];
  if (per == 0 || nwords %% per) { fprintf(stderr, "memtb: %%d words is not a whole number of %%d-word calls\\n", nwords, per); return 2; }
  for (call = 0; call * per < nwords; call++) {
    unsigned res = 0;
    int k = call * per;
%(decl)s
%(fill)s
    for (r = 0; r < runs; r++) { %(call)s }
    printf("%%08x\\n", res%(mask)s);
%(dump)s
  }
  return 0;
}''' % dict(inc=(k + ".h") if hdr else "k.c", bufs=bufs, nel=nel, decl=decl, words=words, narr=len(arrs),
            fill=fill, call=call, dump=dump, mask="" if void else " & msk((int)sizeof(%s))" % ret), void


def oracle(k, vec, runs, held, tmp):
    """(answers per call or None for a void kernel, {(call, mem): [words]}) from the C."""
    memout = os.path.join(tmp, f"memout_{runs}.txt")
    env = dict(os.environ, ORACLE_RUNS=str(runs), ORACLE_MEMOUT=memout)
    cp = subprocess.run([os.path.join(R, "research", "tools", "suite", "oracle_mem.sh"), k, vec], env=env,
                        capture_output=True, text=True)
    void = False
    if cp.returncode != 0:
        src_dir = csource(k)
        text, void = driver_c(k, src_dir, held)
        d = os.path.join(tmp, f"drv{runs}")
        os.makedirs(os.path.join(d, "dynamatic"), exist_ok=True)
        open(os.path.join(d, "dynamatic", "Integration.h"), "w").write("#define CALL_KERNEL(f, ...) f(__VA_ARGS__)\n")
        ksrc = open(os.path.join(src_dir, k + ".c")).read()
        ksrc = re.sub(r"(^|\n)int main[ \t]*\([ \t]*(void)?[ \t]*\)", r"\1int main_unused(void)", ksrc)
        open(os.path.join(d, "k.c"), "w").write(ksrc)
        open(os.path.join(d, "d.c"), "w").write(text)
        cc = "clang" if "_BitInt" in ksrc else "gcc"
        objs = ["d.c"] + (["k.c"] if os.path.exists(os.path.join(src_dir, k + ".h")) else [])
        b = subprocess.run([cc, "-O1", "-fwrapv", "-w", "-I", d, "-I", src_dir, "-o", os.path.join(d, "drv")]
                           + [os.path.join(d, o) for o in objs], capture_output=True, text=True)
        if b.returncode != 0:
            sys.exit(f"memtb: oracle_mem.sh refused {k} ({cp.stderr.strip()}) and the driver did not compile:\n{b.stderr}")
        lines = open(vec).read().splitlines()
        clean = os.path.join(d, "vec.hex")       # the header line, then the words without the comment lines
        open(clean, "w").write(lines[0] + "\n" + "\n".join(re.sub(r"//.*", "", ln) for ln in lines[1:]) + "\n")
        cp = subprocess.run([os.path.join(d, "drv"), clean, str(runs), memout], capture_output=True, text=True)
        if cp.returncode != 0:
            sys.exit(f"memtb: the C driver failed: {cp.stderr}")
    ans = [int(x, 16) for x in cp.stdout.split()]
    mem = {}
    for line in open(memout):
        mm = re.match(r"call=(\d+) mem=(\d+) data=(.*)", line.strip())
        if mm:
            mem[(int(mm.group(1)), int(mm.group(2)))] = [int(x, 16) for x in mm.group(3).split(",") if x]
    return (None if void else ans), mem


def ports(text, mod):
    m = re.search(r"module\s+" + re.escape(mod) + r"\b(.*?)\);", text, flags=re.S)
    out = {}
    for d, w, n in re.findall(r"(input|output)\s+wire\s+(\[\d+:0\]\s*)?(\w+)", m.group(1)):
        out[n] = (d, int(re.match(r"\[(\d+)", w).group(1)) + 1 if w else 1)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("kernel")
    ap.add_argument("vec")
    ap.add_argument("--runs", type=int, default=2)
    ap.add_argument("--calls", type=int, default=0, help="only the first N calls (0 = all)")
    ap.add_argument("--timeout-us", type=int, default=2000, help="per run, circuit time")
    ap.add_argument("--out", default="")
    ap.add_argument("--vcd", action="store_true")
    ap.add_argument("--dut", help="use this --host-mem Verilog instead of emitting")
    ap.add_argument("--route-ps", type=int, default=0, help="BD_ROUTE_PS (cells/sim/bd_prims_sim.v: ps per arc), as simcheck")
    ap.add_argument("--keep-dco", action="store_true",
                    help="keep the emitted DCO (do not cover the RAM model's clock-to-out); the monitor still reports")
    ap.add_argument("--jitter", default="", help="SEED[:PCT]: BD_JITTER, every LUT arc scattered per instance")
    a = ap.parse_args()
    k = a.kernel
    vec = os.path.abspath(a.vec)
    mlir = os.path.join(R, "build", "frontend", k, "comp", "handshake_transformed.mlir")
    func = [f for f in parse.parse_module(open(mlir).read(), filename=mlir) if not f.is_declaration][0]
    out = os.path.abspath(a.out or os.path.join(R, "cells", "build", "memtb", k))
    os.makedirs(out, exist_ok=True)
    if a.dut:
        text = open(a.dut).read()
    else:
        emit.HOST_MEM = True
        text, _f, _d = emit.generate(mlir, top=False)
    dut = os.path.join(out, f"{k}_dut.v")
    open(dut, "w").write(text)
    mod = f"bdc_{k}"
    P = ports(text, mod)

    mems, scal, ctrl = [], [], []
    for arg in func.args:
        b = emit.portname(arg.name)
        if arg.raw.startswith("memref"):
            mm = re.fullmatch(r"memref<(\d+)x[iu](\d+)>", arg.raw)
            mems.append((b, int(mm.group(1)), int(mm.group(2))))
        elif arg.is_control:
            ctrl.append(b)
        else:
            scal.append((b, arg.width))
    res = [(emit.portname(r.name), 0 if r.is_control else r.width) for r in func.results]
    datares = [(b, w) for b, w in res if w]
    if len(datares) > 1:
        sys.exit(f"memtb: {k} has {len(datares)} data results (one supported)")

    hdr = open(vec).readline()
    hm = re.match(r"// benchvec words=(\d+) mems=(\d+)", hdr)
    if not hm:
        sys.exit(f"memtb: {vec} has no v2 header")
    nw, nm = int(hm.group(1)), int(hm.group(2))
    if nm != len(mems) or nw != sum(max(1, w // 32) for _b, w in scal):
        sys.exit(f"memtb: {vec} says words={nw} mems={nm}; {k} has {scal} and {len(mems)} memories")
    words = [int(x, 16) for x in re.sub(r"//[^\n]*", " ", open(vec).read()).split()]
    per = nw + sum(d for _b, d, _w in mems)
    if len(words) % per:
        sys.exit(f"memtb: {len(words)} words is not a whole number of {per}-word calls")
    ncalls = len(words) // per
    if a.calls:
        ncalls = min(ncalls, a.calls)

    with tempfile.TemporaryDirectory() as tmp:
        held = [arg.name for arg in func.args if arg.raw.startswith("memref")]
        ans1, _m1 = oracle(k, vec, 1, held, tmp)
        ansR, memR = oracle(k, vec, a.runs, held, tmp)
    with open(os.path.join(out, "vec.hex"), "w") as f:
        f.write("\n".join("%08x" % w for w in words[:ncalls * per]) + "\n")
    with open(os.path.join(out, "exp.hex"), "w") as f:
        for c in range(ncalls):
            f.write("%08x %08x\n" % ((ans1 or [0] * ncalls)[c], (ansR or [0] * ncalls)[c]))
    with open(os.path.join(out, "memexp.hex"), "w") as f:
        for c in range(ncalls):
            for j, (_b, d, w) in enumerate(mems):
                vals = memR.get((c, j))
                if vals is None or len(vals) != d:
                    sys.exit(f"memtb: the oracle gave no final contents for call {c} memory {j}")
                f.write("\n".join("%08x" % v for v in vals) + "\n")

    L = ["`timescale 1ps/1ps", "module tb_memtb;", "    reg rst = 1;"]
    conn = ["        .rst(rst)"]
    for b, w in scal:
        L.append(f"    reg {b}_req = 0; wire {b}_ack; reg [{w - 1}:0] {b}_data = 0;")
        conn += [f".{b}_req({b}_req)", f".{b}_ack({b}_ack)", f".{b}_data({b}_data)"]
    for b in ctrl:
        L.append(f"    reg {b}_req = 0; wire {b}_ack;")
        conn += [f".{b}_req({b}_req)", f".{b}_ack({b}_ack)"]
    for b, w in res:
        L.append(f"    wire {b}_req; reg {b}_ack = 0; integer {b}_n = 0;" + (f" wire [{w - 1}:0] {b}_data;" if w else ""))
        conn += [f".{b}_req({b}_req)", f".{b}_ack({b}_ack)"] + ([f".{b}_data({b}_data)"] if w else [])
    for b, d, w in mems:
        h = b + "_host"
        aw, dw = P[h + "_addr"][1], P[h + "_wdata"][1]
        L.append(f"    reg {h}_req = 0, {h}_we = 0; reg [{aw - 1}:0] {h}_addr = 0; reg [{dw - 1}:0] {h}_wdata = 0;"
                 f" wire {h}_ack; wire [{dw - 1}:0] {h}_rdata;")
        conn += [f".{h}_req({h}_req)", f".{h}_ack({h}_ack)", f".{h}_addr({h}_addr)", f".{h}_wdata({h}_wdata)",
                 f".{h}_we({h}_we)", f".{h}_rdata({h}_rdata)"]
    missing = [p for p in P if p != "rst" and not any(f".{p}(" in c for c in conn)]
    if missing:
        sys.exit(f"memtb: ports not driven: {missing}")
    # The RAM boundary (docstring): cover the model's clock-to-out with DCO unless --keep-dco, and watch every bd_mem.
    prims = open(os.path.join(R, "cells", "sim", "bd_prims_sim.v")).read()
    tco = int(re.search(r"`define BD_RAM_TCO\s+(\d+)", prims).group(1))
    tsu = max(int(x) for x in re.findall(r"`define BD_RAM_TSU_\w+\s+(\d+)", prims))
    jseed, jpct = 0, 0
    if a.jitter:
        jseed, _c, jp = a.jitter.partition(":")
        jseed, jpct = int(jseed), int(jp or 30)
    hop = 124 + a.route_ps
    hop_lo, hop_hi = hop * (100 - jpct) / 100.0, hop * (100 + jpct) / 100.0
    need = {"UCO": -(-(tco + 3 * hop_hi) // hop_lo)}
    if a.jitter:
        need["USETUP"] = -(-(tsu + 3 * hop_hi) // hop_lo)
    hdr = re.search(r"module\s+" + re.escape(mod) + r"\s*#\((.*?)\)\s*\(", text, flags=re.S)
    over = {}
    for pn, pv in re.findall(r"parameter\s+(DELAY_\w+_(?:UCO|USETUP))\s*=\s*(\d+)", hdr.group(1) if hdr else ""):
        want = int(need.get(pn.rpartition("_")[2], 0))
        if not a.keep_dco and int(pv) < want:
            over[pn] = want
    if over:
        print("MEMTB note: %d RAM delay parameter(s) raised in this testbench to cover the RAM model (clock-to-out %d ps"
              ", setup %d ps) at %d ps per arc%s: %s" % (len(over), tco, tsu, hop, " +-%d%%" % jpct if jpct else "",
              ", ".join(sorted(set("%s %s" % (k.rpartition("_")[2], v) for k, v in over.items())))))
    rams = []          # every bd_mem instance path under dut
    for pm, body in re.findall(r"module\s+(\w+)(.*?)endmodule", text, flags=re.S):
        um = re.findall(r"\bbd_mem(?:_ff)?\s*#\s*\((?:[^()]|\([^()]*\))*\)\s*(\w+)\s*\(", body)
        if not um:
            continue
        for inst in re.findall(r"\b" + re.escape(pm) + r"\s*(?:#\s*\((?:[^()]|\([^()]*\))*\))?\s*(\w+)\s*\(", text):
            rams += [f"dut.{inst}.{u}" for u in um]
    L.append("    integer ramviol = 0; time ackmin = 64'd1000000000;")
    for j, rp in enumerate(rams):
        L += [f"    time tedge{j} = 0;", f"    always @(posedge {rp}.ram_clk) tedge{j} = $time;",
              f"    always @(posedge {rp}.ack) if ($time - tedge{j} < ackmin) ackmin = $time - tedge{j};",
              f"    always @({rp}.rdata) if ({rp}.ack === 1'b1 && rst === 1'b0) begin ramviol = ramviol + 1;"
              f" if (ramviol <= 3) $display(\"MEMTB RAM-BOUNDARY {rp}: read data changed %0t ps after the clock edge,"
              f" the acknowledge already high (clock-to-out > DCO in this model)\", $time - tedge{j}); end"]
    L.append(f"    {mod} " + ("#(" + ", ".join(f".{k}({v})" for k, v in sorted(over.items())) + ") " if over else "")
             + "dut (" + ",\n        ".join(conn) + ");")
    nexp = ncalls * sum(d for _b, d, _w in mems)
    L += [f"    reg [31:0] vec [0:{ncalls * per - 1}];", f"    reg [31:0] exp [0:{2 * ncalls - 1}];",
          f"    reg [31:0] mexp [0:{max(nexp, 1) - 1}];",
          "    integer c, r, i, k, bad, fails, mbase, inrun, timeouts; reg [31:0] q; time t0;"]
    for b, d, w in mems:
        h = b + "_host"
        L += [f"    task host_{b}(input integer a, input [31:0] dd, input we, output [31:0] qq);", "        begin",
              f"            wait ({h}_ack === 1'b0);",
              f"            {h}_addr = a; {h}_wdata = dd; {h}_we = we;",
              f"            #1000 {h}_req = 1;", f"            wait ({h}_ack === 1'b1);",
              f"            #3000 qq = {h}_rdata;", f"            {h}_req = 0;", f"            wait ({h}_ack === 1'b0);",
              "            #1000;", "        end", "    endtask"]
    for b, w in res:
        L += [f"    always @(posedge {b}_req) {b}_n = {b}_n + 1;"]
    L += ["    initial begin", f'        $readmemh("{out}/vec.hex", vec); $readmemh("{out}/exp.hex", exp);']
    if nexp:
        L.append(f'        $readmemh("{out}/memexp.hex", mexp);')
    L += ["        fails = 0; inrun = 0; timeouts = 0;", f"        #{max(20000, 48000 * len(func.nodes))} rst = 0; #20000;",
          f"        for (c = 0; c < {ncalls}; c = c + 1) begin", f"            k = c * {per} + {nw};"]
    for b, d, w in mems:
        L += [f"            for (i = 0; i < {d}; i = i + 1) host_{b}(i, vec[k + i], 1'b1, q);", f"            k = k + {d};"]
    L += [f"            for (r = 0; r < {a.runs}; r = r + 1) begin", "                k = c * " + str(per) + ";",
          "                t0 = $time; inrun = 1;", "                fork"]
    wi = 0
    for b, w in scal:
        if w == 64:
            L.append(f"                    begin {b}_data = {{vec[k + {wi + 1}], vec[k + {wi}]}}; #200 {b}_req = 1; wait ({b}_ack === 1'b1); {b}_req = 0; wait ({b}_ack === 1'b0); end")
            wi += 2
        else:
            L.append(f"                    begin {b}_data = vec[k + {wi}]; #200 {b}_req = 1; wait ({b}_ack === 1'b1); {b}_req = 0; wait ({b}_ack === 1'b0); end")
            wi += 1
    for b in ctrl:
        L.append(f"                    begin #200 {b}_req = 1; wait ({b}_ack === 1'b1); {b}_req = 0; wait ({b}_ack === 1'b0); end")
    for b, w in res:
        cap = ""
        if w:
            cap = (f" q = {b}_data; if (q !== ((r == 0) ? exp[2 * c] : exp[2 * c + 1]) && (r == 0 || r == {a.runs - 1})) "
                   f"begin fails = fails + 1; $display(\"MEMTB call=%0d run=%0d {b}=%08x exp=%08x BAD\", c, r, q, "
                   f"(r == 0) ? exp[2 * c] : exp[2 * c + 1]); end else $display(\"MEMTB call=%0d run=%0d {b}=%08x ok\", c, r, q);")
        L.append(f"                    begin wait ({b}_req === 1'b1);{cap} #300 {b}_ack = 1; wait ({b}_req === 1'b0); #300 {b}_ack = 0; end")
    L += ["                join", "                inrun = 0;",
          '                $display("MEMTB call=%0d run=%0d done at %0t ps (%0t ps)", c, r, $time, $time - t0);',
          "                #2000;", "            end", "            mbase = 0;"]
    for j, (b, d, w) in enumerate(mems):
        mw = "32'hffffffff" if w >= 32 else f"32'h{(1 << w) - 1:08x}"
        L += ["            bad = 0;",
              f"            for (i = 0; i < {d}; i = i + 1) begin",
              f"                host_{b}(i, 32'h0, 1'b0, q);",
              f"                if ((q & {mw}) !== mexp[c * {nexp // max(ncalls, 1)} + mbase + i]) begin bad = bad + 1;"
              f" if (bad <= 3) $display(\"MEMTB call=%0d mem={j} [%0d]=%08x want %08x\", c, i, q & {mw}, "
              f"mexp[c * {nexp // max(ncalls, 1)} + mbase + i]); end",
              "            end",
              f'            $display("MEMTB call=%0d mem={j} ({b}) bad=%0d", c, bad);',
              "            if (bad) fails = fails + 1;", f"            mbase = mbase + {d};"]
    L += ["        end",
          f'        $display("MEMTB RAM ports={len(rams)} ack-after-edge min %0d ps, clock-to-out {tco} ps, read data changed under the acknowledge %0d time(s)", ackmin, ramviol);',
          "        if (ramviol) fails = fails + 1;",
          f'        $display("MEMTB SUMMARY %s calls={ncalls} runs={a.runs} fails=%0d at %0t ps", fails ? "FAIL" : "PASS", fails, $time);',
          "        $finish;", "    end",
          "    initial forever begin #1000000;",
          f"        if (inrun && $time - t0 > 64'd{a.timeout_us * 1000000}) begin",
          '            $display("MEMTB TIMEOUT call=%0d run=%0d after %0t ps", c, r, $time - t0);']
    for b, w in res:
        L.append(f'            $display("    {b}: %0d token(s) seen, req=%b ack=%b", {b}_n, {b}_req, {b}_ack);')
    L += [f'            $display("MEMTB SUMMARY TIMEOUT calls={ncalls} runs={a.runs} at call %0d run %0d", c, r);',
          "            $finish;", "        end", "    end"]
    if a.vcd:
        L += ["    initial begin", f'        $dumpfile("{out}/memtb.vcd");', "        $dumpvars(0, tb_memtb);", "    end"]
    L.append("endmodule")
    tb = os.path.join(out, "tb_memtb.v")
    open(tb, "w").write("\n".join(L) + "\n")
    vvp = os.path.join(out, "tb_memtb.vvp")
    cmd = (f"iverilog -g2012 -gspecify -Wno-timescale -DBD_ROUTE_PS={a.route_ps}{' -DBD_JITTER' if a.jitter else ''} "
           f"-o {vvp} {R}/cells/sim/bd_prims_sim.v "
           f"{R}/cells/sim/bd_env.v {R}/cells/rtl/*.v {dut} {tb}")
    cp = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if cp.returncode != 0:
        print(cp.stdout + cp.stderr)
        sys.exit("memtb: COMPILE FAIL")
    cp = subprocess.run(["vvp", "-n", vvp] + ([f"+JSEED={jseed}", f"+JPCT={jpct}"] if a.jitter else []),
                        capture_output=True, text=True, cwd=out)
    open(os.path.join(out, "run.log"), "w").write(cp.stdout + cp.stderr)
    lines = [ln for ln in cp.stdout.splitlines() if ln.startswith("MEMTB") or ln.startswith("    ")]
    # The RAM model's setup check and the port's one-hot check print; they are failures, not log noise.
    viol = [ln.strip() for ln in cp.stdout.splitlines() if "BUNDLING" in ln or re.search(r"\bFAIL bdc_", ln)]
    if viol:
        lines[-1:-1] = ["MEMTB VIOLATION %s" % v for v in viol[:5]] + (["MEMTB VIOLATION ... %d in all" % len(viol)]
                                                                       if len(viol) > 5 else [])
        lines = [ln.replace("MEMTB SUMMARY PASS", "MEMTB SUMMARY FAIL") for ln in lines]
    print("\n".join(lines))
    return 0 if any("MEMTB SUMMARY PASS" in ln for ln in lines) else 1


if __name__ == "__main__":
    sys.exit(main())
