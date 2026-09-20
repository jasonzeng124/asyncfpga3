#!/usr/bin/env python3
"""Reproducible fusion experiments, without a Dynamatic installation.

These materialized graphs model arithmetic kernels, not frontend output.
Simulation measures handshake cost with placeholder matched delays and ideal
arithmetic. It is not routed timing or a silicon frequency prediction.
"""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess

import emit
from hs import parse


REPO = Path(__file__).resolve().parents[1]
CELLS = REPO / "cells"
MASK = (1 << 32) - 1


class Graph:
    def __init__(self, name, args):
        self.name = name
        self.args = args
        self.lines = []

    def node(self, op, operands="", type_sig="<i32>", attrs=""):
        value = f"%v{len(self.lines)}"
        attr = f" {{{attrs}}}" if attrs else ""
        self.lines.append(f"    {value} = {op} {operands}{attr} : {type_sig}")
        return value

    def fork(self, value, n=2):
        result = f"%v{len(self.lines)}"
        self.lines.append(f"    {result}:{n} = fork [{n}] {value} : <i32>")
        return [f"{result}#{i}" for i in range(n)]

    def const(self, value):
        ctl = self.node("source", type_sig="<>")
        return self.node("constant", ctl, "<>, <i32>", f"value = {value} : i32")

    def binary(self, op, a, b):
        return self.node(op, f"{a}, {b}")

    def text(self, result):
        args = ", ".join(f"%{a}: !handshake.channel<i32>" for a in self.args)
        names = json.dumps(self.args)
        return (
            f"handshake.func @{self.name}({args}, ...) -> !handshake.channel<i32>"
            f' attributes {{argNames = {names}, resNames = ["out"]}} {{\n'
            + "\n".join(self.lines) + f"\n    end {result} : <i32>\n}}\n"
        )


def xorshift(x):
    x = (x ^ (x << 13)) & MASK
    x ^= x >> 17
    return (x ^ (x << 5)) & MASK


def fixture(name):
    if name == "xorshift_round":
        g = Graph(name, ["x"])
        x = "%x"
        for op, shift in [("shli", 13), ("shrui", 17), ("shli", 5)]:
            a, b = g.fork(x)
            x = g.binary("xori", a, g.binary(op, b, g.const(shift)))
        return g.text(x), lambda v: xorshift(v["x"])
    if name == "square":
        g = Graph(name, ["x"])
        a, b = g.fork("%x")
        return g.text(g.binary("muli", a, b)), lambda v: v["x"] ** 2 & MASK
    if name == "diamond":
        g = Graph(name, ["x", "y"])
        a, b = g.fork("%x")
        c, d = g.fork("%y")
        left = g.binary("addi", a, c)
        right = g.binary("subi", b, d)
        return g.text(g.binary("xori", left, right)), (
            lambda v: ((v["x"] + v["y"]) ^ (v["x"] - v["y"])) & MASK
        )
    if name == "signed_min":
        g = Graph(name, ["x", "y"])
        a, b = g.fork("%x")
        c, d = g.fork("%y")
        pred = g.node("cmpi", f"slt, {a}, {c}")
        result = g.node("select", f"{pred}[{b}, {d}]", "<i1>, <i32>")
        return g.text(result), (
            lambda v: min((v["x"], v["y"]), key=lambda x: x ^ (1 << 31))
        )
    raise ValueError(name)


FIXTURES = ("xorshift_round", "square", "diamond", "signed_min")


def vectors(func, count=96):
    rng = random.Random(20260919)
    edges = (0, 1, MASK, 1 << 31, (1 << 31) - 1, 0x55555555, 0xAAAAAAAA)
    return [
        {a.name: edges[(i + j) % len(edges)] if i < len(edges)
         else rng.getrandbits(a.width) for j, a in enumerate(func.args)}
        for i in range(count)
    ]


def testbench(func, inputs, expected, *, stalls):
    n = len(inputs)
    lines = [
        "`timescale 1ps / 1ps", "module tb;",
        "reg rst = 1;", "wire out_req;", "reg out_ack = 0;",
        "wire [31:0] out_data;", "integer received = 0;",
        "time first_result, last_result;",
        f"reg [31:0] expected [0:{n - 1}];",
    ]
    conns = [".rst(rst)", ".out_req(out_req)", ".out_ack(out_ack)",
             ".out_data(out_data)"]
    for j, a in enumerate(func.args):
        b = a.name
        lines += [
            f"wire {b}_req, {b}_ack;", f"wire [31:0] {b}_data;",
            f"integer {b}_sent = 0;", f"time {b}_first;",
            f"reg [31:0] {b}_values [0:{n - 1}];",
            f"bd_source #(.W(32)) {b}_src(.req({b}_req), .ack({b}_ack),"
            f" .data({b}_data));",
            f"always @(posedge {b}_req) if ({b}_sent == 0) {b}_first = $time;",
            "initial begin",
        ]
        lines += [f"  {b}_values[{i}] = 32'h{v[b]:08x};"
                  for i, v in enumerate(inputs)]
        gap = f"(({b}_sent * {j + 3}) % 11) * 977" if stalls else "0"
        send_tail = " #1000;" if stalls else ""
        lines += [
            "  wait (!rst); #20000;",
            f"  for ({b}_sent = 0; {b}_sent < {n}; {b}_sent = {b}_sent + 1) begin",
            f"    #({gap}); {b}_src.send({b}_values[{b}_sent]);{send_tail}",
            "  end", "end",
        ]
        conns += [f".{b}_{p}({b}_{p})" for p in ("req", "ack", "data")]
    lines += [
        f"bdc_{func.name} dut({', '.join(conns)});",
        'bd_monitor #(.W(32), .CHAN("out"), .EARLY_RELEASE(1)) monitor',
        "  (.req(out_req), .ack(out_ack), .data(out_data));",
        "initial begin",
    ]
    lines += [f"  expected[{i}] = 32'h{v:08x};" for i, v in enumerate(expected)]
    sink_wait = (
        f"    #(1000 + (received % 7) * 1777);"
        if stalls else ""
    )
    sink_release = "#1000; out_ack = 0;" if stalls else "out_ack = 0;"
    lines += ["  #2000000; rst = 0; monitor.arm;", "end", "initial begin",
              "  wait (!rst);", f"  repeat ({n}) begin",
              "    wait (out_req === 1);",
              "    if (out_data !== expected[received])",
              '      $fatal(1, "token %0d: got %h expected %h", received,'
              " out_data, expected[received]);",
              "    if (received == 0) first_result = $time;",
              "    last_result = $time;",
              sink_wait,
              f"    out_ack = 1; wait (out_req === 0); {sink_release}",
              "    received = received + 1;", "  end", "  #100000;"]
    for a in func.args:
        lines.append(f"  if ({a.name}_sent != {n}) $fatal(1, \"source stalled\");")
    ready = func.args[0].name + "_first"
    for a in func.args[1:]:
        ready = f"(({ready}) > {a.name}_first ? ({ready}) : {a.name}_first)"
    lines += [
        '  if (out_req !== 0 || monitor.errors != 0) $fatal(1, "protocol error");',
        f'  $display("METRICS %0d %0d", first_result - ({ready}),'
        f" (last_result - first_result) / {n - 1});",
        '  $display("PASS"); $finish;', "end",
        'initial if ($test$plusargs("vcd")) begin',
        '  $dumpfile("trace.vcd"); $dumpvars(0, tb); end',
        'initial begin #100000000; $fatal(1, "timeout"); end', "endmodule",
    ]
    return "\n".join(lines) + "\n"


def run(command, log, *, cwd=None, env=None, timeout=300):
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, cwd=cwd, env=env, timeout=timeout)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{command[0]} failed; see {log}")
    return result.stdout


def metrics(output):
    match = re.search(r"METRICS (\d+) (\d+)", output)
    if "PASS" not in output or match is None:
        raise RuntimeError("simulation did not report passing measurements")
    return tuple(map(int, match.groups()))


def measure(name, outdir, *, synth=False, stalls=None):
    outdir.mkdir(parents=True, exist_ok=True)
    text, reference = fixture(name)
    path = outdir / "input.mlir"
    path.write_text(text)
    func = parse.parse_module(text)[0]
    rtl = outdir / "dut.v"
    rtl.write_text(emit.generate(str(path), top=False)[0])
    e = emit.Emitter(func)
    assert e.fusion is not None
    data = vectors(func)
    expected = [reference(v) for v in data]
    tb_stalled = outdir / "tb_stalled.v"
    tb_fast = outdir / "tb_fast.v"
    tb_stalled.write_text(testbench(func, data, expected, stalls=True))
    tb_fast.write_text(testbench(func, data, expected, stalls=False))
    sources = [CELLS / "sim/bd_prims_sim.v", CELLS / "sim/bd_env.v",
               *sorted((CELLS / "rtl").glob("*.v")), rtl]
    outputs = {}
    for kind, tb in (("stalled", tb_stalled), ("fast", tb_fast)):
        sim = outdir / f"sim_{kind}.vvp"
        run(["iverilog", "-g2012", "-gspecify", "-s", "tb", "-o",
             str(sim), *map(str, [*sources, tb])],
            outdir / f"compile_{kind}.log")
        outputs[kind] = metrics(run(["vvp", str(sim)],
                                     outdir / f"sim_{kind}.log"))
    latency, interval = outputs["fast"]
    stalled_latency, stalled_interval = outputs["stalled"]
    result = {
        "kernel": name, "fork_fusion": emit.BDC_FORK_FUSION,
        "max_nodes": emit.MAX_FUSE_NODES, "fastfall": emit.BDC_FASTFALL,
        "regions": len(e.fusion.anchor_region),
        "forks_absorbed": sum(n.op == "fork" and i in e.fusion.skip
                              for i, n in enumerate(func.nodes)),
        "storage_bits": sum(max(e.ch[v][0], 1) * d for v, d in e.depth.items()),
        "storage_stages": sum(e.depth.values()),
        "latency_ps": latency, "interval_ps": interval,
        "stalled_latency_ps": stalled_latency,
        "stalled_interval_ps": stalled_interval,
    }
    if synth:
        script = outdir / "synth.ys"
        json_path = outdir / "netlist.json"
        script.write_text(
            "read_verilog " + " ".join(map(str, sorted((CELLS / "rtl").glob("*.v"))))
            + f" {rtl}\nsynth_xilinx -top bdc_{name} -family xc7 -noclkbuf -noiopad\n"
            + f"write_json {json_path}\nstat\n"
        )
        run(["yosys", "-s", str(script)], outdir / "synth.log")
        modules = json.loads(json_path.read_text())["modules"]

        def counts(module):
            result: Counter[str] = Counter()
            for cell in modules[module]["cells"].values():
                kind = cell["type"]
                attrs = modules.get(kind, {}).get("attributes", {})
                primitive = any(int(attrs.get(k, "0"), 2)
                                for k in ("blackbox", "whitebox"))
                if kind in modules and not primitive:
                    result.update(counts(kind))
                else:
                    result[kind] += 1
            return result

        result["cells"] = dict(counts(f"bdc_{name}"))
        result["lut_cells"] = sum(v for k, v in result["cells"].items()
                                  if re.fullmatch(r"LUT[1-6](_2)?", k))
    return result


def routed_signals(outdir, func):
    synthesis = json.loads((outdir / "pnr/soak.json").read_text())
    source = synthesis["modules"][f"bdc_{func.name}_top"]
    routed = json.loads((outdir / "pnr/soak_routed.json").read_text())
    nets = routed["modules"]["top"]["netnames"]
    physical = {}
    aliases = {}

    def root(bit):
        while bit in aliases:
            bit = aliases[bit]
        return bit

    def collect(module, prefix, ports):
        def canonical(bit):
            return ports.get(bit, (prefix, bit))

        for name, net in module["netnames"].items():
            bits = net["bits"]
            for i, bit in enumerate(bits):
                scalar = name if len(bits) == 1 else f"{name}[{i + net.get('offset', 0)}]"
                if prefix + scalar in nets:
                    physical[canonical(bit)] = nets[prefix + scalar]["bits"][0]
        for name, cell in module["cells"].items():
            child = synthesis["modules"].get(cell["type"])
            if child is None or not child.get("cells"):
                continue
            bindings = {}
            for port, values in cell["connections"].items():
                for bit, value in zip(child["ports"][port]["bits"], values):
                    value = canonical(value)
                    if bit in bindings and root(bindings[bit]) != root(value):
                        aliases[root(bindings[bit])] = root(value)
                    bindings[bit] = value
            collect(child, prefix + name + ".", bindings)

    collect(source, "", {})
    physical = {root(bit): value for bit, value in physical.items()}
    return {port: [physical[root(("", b))] for b in bits]
            for port, bits in source["cells"]["uut"]["connections"].items()}


def measure_route(name, outdir, *, seeds):
    """Drive the DUT boundary in the routed soak harness; retain its wire delays."""
    path = outdir / "input.mlir"
    func = parse.parse_module(path.read_text())[0]
    top = outdir / "top.v"
    top.write_text(emit.generate(str(path))[0])
    env = os.environ.copy()
    for key in ("BD_NO_TIGHTEN", "BD_SIZES", "NEXTPNR_SEED"):
        env.pop(key, None)
    env.update(BD_TOP_V=str(top), BD_TOP_M=f"bdc_{name}_top",
               BD_OUT=str(outdir / "pnr"), BD_RESIZE_SEEDS=str(seeds))
    run([str(CELLS / "flow.sh")], outdir / "route.log", env=env, timeout=3600)
    sdf = outdir / "pnr/soak.sdf"
    for audit in ("tighten", "skew"):
        run(["python3", str(CELLS / f"verify/{audit}.py"), str(sdf)],
            outdir / f"{audit}.log")
    return {**simulate_route(outdir, func), "resize_seeds": seeds}


def simulate_route(outdir, func):
    gls = outdir / "gls"
    gls.mkdir(exist_ok=True)
    shutil.copy2(outdir / "pnr/soak.sdf", gls / "routed.sdf")
    shutil.copy2(outdir / "pnr/soak_routed.json", gls / "routed.json")
    run(["python3", str(CELLS / "gls/gen.py")], gls / "generate.log",
        env={**os.environ, "GLS_WORK": str(gls)})
    run(["iverilog", "-g2012", "-gspecify", "-s", "tb_gate", "-o",
         str(gls / "gate.vvp"), str(CELLS / "gls/prims.v"),
         str(gls / "netlist.v"), str(CELLS / "gls/tb_gate.v")],
        gls / "compile_gate.log")
    gate = run(["vvp", "gate.vvp"], gls / "gate.log", cwd=gls)
    if "ANNOTATE_DONE" not in gate or re.search(r"WARNING|ERROR", gate):
        raise RuntimeError(f"SDF annotation failed: {gls}")

    signals = routed_signals(outdir, func)
    drive = ["rst", "out_ack"]
    observe = ["out_req", "out_data"]
    for arg in func.args:
        drive += [f"{arg.name}_req", f"{arg.name}_data"]
        observe.append(f"{arg.name}_ack")
    connection = ["top dut();"]
    driven = set()
    for port in drive:
        for i, bit in enumerate(signals[port]):
            if bit in driven:
                raise RuntimeError("soak harness aliases independently driven ports")
            driven.add(bit)
            value = f"{port}[{i}]" if port.endswith("_data") else port
            connection.append(f"wire drive_{bit} = {value};")
            connection.append(f"initial force dut.n{bit} = drive_{bit};")
    for port in observe:
        bits = signals[port]
        value = "{" + ", ".join(f"dut.n{b}" for b in reversed(bits)) + "}"
        connection.append(f"assign {port} = {value};")

    outputs = {}
    for kind in ("stalled", "fast"):
        tb = (outdir / f"tb_{kind}.v").read_text()
        tb = re.sub(r"bdc_\w+ dut\([^\n]+", "\n".join(connection), tb)
        (gls / f"tb_{kind}.v").write_text(tb)
        sim = gls / f"sim_{kind}.vvp"
        run(["iverilog", "-g2012", "-gspecify", "-s", "tb", "-o",
             str(sim), str(CELLS / "gls/prims.v"),
             str(CELLS / "sim/bd_env.v"), str(gls / "netlist_baked.v"),
             str(gls / f"tb_{kind}.v")],
            gls / f"compile_{kind}.log")
        outputs[kind] = metrics(run(["vvp", str(sim)],
                                     gls / f"sim_{kind}.log", cwd=gls))
    latency, interval = outputs["fast"]
    stalled_latency, stalled_interval = outputs["stalled"]
    fasm = (outdir / "pnr/soak.fasm").read_text()
    return {
        "routed_latency_ps": latency, "routed_interval_ps": interval,
        "routed_stalled_latency_ps": stalled_latency,
        "routed_stalled_interval_ps": stalled_interval,
        "fastfall": emit.BDC_FASTFALL,
        "routed_lut_sites_including_harness": fasm.count("LUT.INIT"),
        "toolchain": (outdir / "pnr/toolchain.txt").read_text().splitlines(),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, default=REPO / "build/fusion-bench")
    ap.add_argument("--kernels", nargs="+", choices=FIXTURES, default=FIXTURES)
    ap.add_argument("--caps", nargs="+", type=int, default=[4, 8])
    ap.add_argument("--synth", action="store_true")
    ap.add_argument("--route", action="store_true",
                    help="resize, audit, and simulate routed xorshift with SDF")
    ap.add_argument("--seeds", type=int, default=3,
                    help="routes checked for every resize candidate")
    args = ap.parse_args()
    if args.route and args.kernels != ["xorshift_round"]:
        ap.error("--route currently requires --kernels xorshift_round")
    results = []
    for forks, cap in [(False, 4), *((True, n) for n in args.caps)]:
        emit.BDC_FORK_FUSION, emit.MAX_FUSE_NODES = forks, cap
        for name in args.kernels:
            out = args.output.resolve() / f"{name}-forks{int(forks)}-cap{cap}"
            row = measure(name, out, synth=args.synth)
            if args.route:
                row.update(measure_route(name, out, seeds=args.seeds))
            results.append(row)
            print(json.dumps(row), flush=True)
    (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
