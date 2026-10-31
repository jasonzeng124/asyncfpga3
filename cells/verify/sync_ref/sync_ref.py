#!/usr/bin/env python3
"""The synchronous reference for xorshift_round: route it, then find the
shortest clock period at which the routed netlist, with its SDF delays, is
still functionally correct.

  sync_ref.py route <out>                       flow.sh on sync_top.v
  sync_ref.py sim   <out> <period_ps> [...]     routed GLS at each period

Same kernel, same flow, same device, same GLS (transport-delay wires, the
baked FF primitive with the device's setup/hold) as the async numbers in
../README.md -- so the columns are comparable: the clock period IS the
interval, latency is three periods (two stages plus the output register).

The sim samples uut.out_data 50 ps before each rising edge against the
LFSR->xorshift model.  PASS at a period means every routed path made it;
FAIL means a wrong word, and the baked flop prints a HOLD VIOLATION if the
hold window is broken.  nextpnr's own Fmax is the other number to quote: it
is a max over every arc, the sim only sees the arcs the LFSR exercises, so
the sim threshold is a floor on the period and the STA number the ceiling.
"""
import json, os, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
CELLS = HERE.parent.parent
TOP = HERE / "sync_top.v"


def run(cmd, log, env=None, cwd=None, timeout=3600):
    r = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, env=env, cwd=cwd, timeout=timeout)
    pathlib.Path(log).write_text(r.stdout)
    if r.returncode:
        raise RuntimeError(f"{cmd[0]} failed, see {log}\n{r.stdout[-3000:]}")
    return r.stdout


def route(out):
    out = pathlib.Path(out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(BD_TOP_V=str(TOP), BD_TOP_M="sync_top", BD_OUT=str(out / "pnr"),
               BD_NO_TIGHTEN="1")
    env.setdefault("BD_RLOC", "none")   # nothing here carries an RLOC stamp
    run([str(CELLS / "flow.sh")], out / "route.log", env=env, cwd=CELLS)
    log = (out / "pnr/pnr.log").read_text()
    fmax = re.findall(r"Max frequency for clock 'clk': ([\d.]+) MHz", log)
    print(f"routed -> {out}; nextpnr Fmax {fmax[-1] if fmax else '?'} MHz")


def lfsr(s):
    return ((s << 1) & 0xffffffff) | (((s >> 31) ^ (s >> 21) ^ (s >> 1) ^ s) & 1)


def xorshift(x):
    x ^= (x << 13) & 0xffffffff
    x ^= x >> 17
    x ^= (x << 5) & 0xffffffff
    return x & 0xffffffff


def netname_bits(out):
    """Top-level synthesized scalar net name -> routed net bit id, through
    whichever alias of the same net, at any level of the kept hierarchy,
    nextpnr kept the name of."""
    routed = json.loads((out / "pnr/soak_routed.json").read_text())
    nets = routed["modules"]["top"]["netnames"]
    mods = json.loads((out / "pnr/soak.json").read_text())["modules"]
    parent = {}

    def find(k):
        while k in parent:
            k = parent[k]
        return k

    def union(a, b):
        a, b = find(a), find(b)
        if a != b:
            parent[a] = b

    names = {}   # (prefix, bit) -> [names]

    def collect(mname, prefix):
        m = mods[mname]
        for name, net in m["netnames"].items():
            bs = net["bits"]
            for i, b in enumerate(bs):
                if isinstance(b, int):
                    sc = name if len(bs) == 1 else f"{name}[{i + net.get('offset', 0)}]"
                    names.setdefault((prefix, b), []).append(prefix + sc)
        for cname, cell in m["cells"].items():
            child = mods.get(cell["type"])
            if child is None or not child.get("cells"):
                continue
            for port, bs in cell["connections"].items():
                for pb, b in zip(child["ports"][port]["bits"], bs):
                    if isinstance(b, int) and isinstance(pb, int):
                        union((prefix + cname + ".", pb), (prefix, b))
            collect(cell["type"], prefix + cname + ".")

    top = [n for n, m in mods.items() if m.get("attributes", {}).get("top")][0]
    collect(top, "")
    groups = {}
    for key, ns in names.items():
        groups.setdefault(find(key), []).extend(ns)
    out_map = {}
    for ns in groups.values():
        hit = [n for n in ns if n in nets]
        if hit:
            for n in ns:
                out_map[n] = nets[hit[0]]["bits"][0]
    return out_map


TB = """`timescale 1ps/1ps
module tb;
  reg clk = 0;
  wire [31:0] out_data;
{conn}
  integer i, bad = 0;
  reg [31:0] expected [0:{n}-1];
  initial begin
{exp}
    #2000;
    for (i = 0; i < {n}; i = i + 1) begin
      clk = 1; #({half}); clk = 0; #({half} - 50);
      if (i >= 4 && out_data !== expected[i]) begin
        bad = bad + 1;
        if (bad < 5) $display("cycle %0d: got %h expected %h", i, out_data, expected[i]);
      end
      #50;
    end
    if (bad == 0) $display("PASS period {period}");
    else $display("FAIL period {period}: %0d bad", bad);
    $finish;
  end
endmodule
"""


def sim(out, period, n=200):
    out = pathlib.Path(out).resolve()
    gls = out / "gls"
    gls.mkdir(exist_ok=True)
    if not (gls / "netlist_baked.v").exists():
        import shutil
        shutil.copy2(out / "pnr/soak.sdf", gls / "routed.sdf")
        shutil.copy2(out / "pnr/soak_routed.json", gls / "routed.json")
        run(["python3", str(CELLS / "gls/gen.py")], gls / "generate.log",
            env={**os.environ, "GLS_WORK": str(gls)})
        run(["iverilog", "-g2012", "-gspecify", "-s", "tb_gate", "-o",
             str(gls / "gate.vvp"), str(CELLS / "gls/prims.v"),
             str(gls / "netlist.v"), str(CELLS / "gls/tb_gate.v")],
            gls / "compile_gate.log")
        gate = run(["vvp", "gate.vvp"], gls / "gate.log", cwd=gls)
        if "ANNOTATE_DONE" not in gate or re.search(r"SDF (WARNING|ERROR)", gate):
            raise RuntimeError(f"SDF annotation failed: {gls}")
    bits = netname_bits(out)

    def bit(name):
        for cand in (name, "uut." + name):
            if cand in bits:
                return bits[cand]
        raise KeyError(name)

    conn = ["top dut();",
            "always @(clk) force dut.n%d = clk;" % bit("pin_in"),
            "assign out_data = {" + ", ".join(
                f"dut.n{bit(f'out_data[{i}]')}" for i in reversed(range(32))) + "};"]
    # src(k) after k edges; r_x(k) = src(k-1); r_v9(k) = c9(r_x(k-1));
    # out(k) = c14(r_v9(k-1)) = xorshift(src(k-3)); sampled before edge k+1.
    s = 0x5a3c5a3c
    srcs = [s]
    for _ in range(n + 4):
        s = lfsr(s)
        srcs.append(s)
    exp = [xorshift(srcs[k - 3]) if k >= 3 else 0 for k in range(1, n + 1)]
    tb = TB.format(n=n, half=period // 2, period=period, conn="\n".join(conn),
                   exp="\n".join(f"    expected[{i}] = 32'h{v:08x};" for i, v in enumerate(exp)))
    (gls / f"tb_{period}.v").write_text(tb)
    vvp = gls / f"sim_{period}.vvp"
    run(["iverilog", "-g2012", "-gspecify", "-DGLS_TRANSPORT_IC", "-s", "tb", "-o", str(vvp),
         str(CELLS / "gls/prims.v"), str(gls / "netlist_baked.v"), str(gls / f"tb_{period}.v")],
        gls / f"compile_{period}.log")
    r = subprocess.run(["vvp", str(vvp)], text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, cwd=gls)
    (gls / f"sim_{period}.log").write_text(r.stdout)
    viol = len(re.findall(r"VIOLATION", r.stdout))
    verdict = [l for l in r.stdout.splitlines() if l.startswith(("PASS", "FAIL"))]
    print(period, verdict[-1] if verdict else r.stdout[-300:],
          f"({viol} FF timing violations)" if viol else "")
    return bool(verdict) and verdict[-1].startswith("PASS") and not viol


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] not in ("route", "sim"):
        sys.exit(__doc__)
    if sys.argv[1] == "route":
        route(sys.argv[2])
    else:
        ok = all([sim(sys.argv[2], int(p)) for p in sys.argv[3:]])
        sys.exit(0 if ok else 1)
