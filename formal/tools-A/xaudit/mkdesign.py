#!/usr/bin/env python3
"""Hand-flatten multi-cell designs from cells/rtl into yosys `write_json` form.

No yosys is installed in this container (the toolchain cache under
~/dev2/lib/fpgatoolchain is absent), so the designs below are flattened BY
HAND from the structural Verilog of the frozen cells, keeping every LUT INIT,
pin order and connection exactly as cells/rtl/*.v instantiates them, and named
as yosys names flattened instances. Rebuild with yosys when the toolchain is
back (`synth_xilinx -flatten ... ; write_json`) and diff: the xaudit result
must not change. What is NOT here: IBUF/OBUF pads (an inner design has none),
and anything synthesis could merge (every LUT in these cells is (* keep *)).

  pipe3  : bd_pipe #(.W(2), .N(3)) with the defaults SDELAY=1, DACK=0, DELAY=0
           (cells/rtl/bd_link.v, bd_ce.v bd_c2n, bd_latch.v pair, bd_delay N=1)
  ring3  : the tb_ring control ring, N=3, K=1: stage 0 bd_c2n_set, stages 1-2
           bd_c2n, c_i = C(c_{i-1}, ~c_{i+1})  (cells/tb/tb_ring.v)

Usage: mkdesign.py OUTDIR
"""
import json
import os
import sys

C2N = 0x00B2_00B2_00B2_00B2        # bd_c2n      (bd_ce.v)
C2N_SET = 0xFFB2_FFB2_FFB2_FFB2    # bd_c2n_set  (bd_ce.v)
LATCH_PAIR = 0xFF33_CC00_B8B8_B8B8  # bd_latch pair (bd_latch.v)
BUF = 0x2                          # bd_delay chain LUT1 (bd_latch.v)


class Mod:
    def __init__(self, name):
        self.name = name
        self.next = 2
        self.ports = {}
        self.cells = {}
        self.netnames = {}

    def net(self, name, width=1):
        bits = list(range(self.next, self.next + width))
        self.next += width
        self.netnames[name] = {"hide_name": 0, "bits": bits, "attributes": {}}
        return bits if width > 1 else bits[0]

    def port(self, name, direction, bits):
        self.ports[name] = {"direction": direction,
                            "bits": bits if isinstance(bits, list) else [bits]}

    def lut(self, name, k, init, ins, outs):
        """ins: list of k bits (net numbers or "0"/"1"); outs: dict pin->bit."""
        ty = "LUT6_2" if "O5" in outs else f"LUT{k}"
        width = 64 if ty == "LUT6_2" else 2 ** k
        conns = {f"I{i}": [b] for i, b in enumerate(ins)}
        dirs = {f"I{i}": "input" for i in range(len(ins))}
        for p, b in outs.items():
            conns[p] = [b]
            dirs[p] = "output"
        self.cells[name] = {
            "hide_name": 0, "type": ty,
            "parameters": {"INIT": format(init, f"0{width}b")},
            "attributes": {"keep": "00000000000000000000000000000001"},
            "port_directions": dirs, "connections": conns}

    def json(self):
        return {"creator": "formal/tools-A/xaudit/mkdesign.py (hand flattening of cells/rtl)",
                "modules": {self.name: {"attributes": {"top": "00000000000000000000000000000001"},
                                        "ports": self.ports, "cells": self.cells,
                                        "netnames": self.netnames}}}


def pipe3(W=2, N=3):
    m = Mod("pipe3")
    rst, req_in, ack_out = m.net("rst"), m.net("req_in"), m.net("ack_out")
    din = m.net("data_in", W)
    c = [m.net(f"stage[{i}].u.c") for i in range(N)]
    q = [m.net(f"stage[{i}].u.lat.q", W) for i in range(N)]
    # r[k] into stage k: r[0] = req_in; r[i+1] = SDELAY line (1 LUT1) of c[i]
    # for the inner boundaries, DELAY = 0 (bypass) for the last.
    r = [req_in] + [m.net(f"r[{i+1}]") for i in range(N - 1)] + [c[N - 1]]
    a = c + [ack_out]                     # a[k] out of stage k = its node (DACK = 0)
    for i in range(N):
        m.lut(f"stage[{i}].u.ctl.u", 6, C2N, [r[i], a[i + 1], c[i], rst, "0", "0"],
              {"O": c[i]})
        d = din if i == 0 else q[i - 1]
        for j in range(0, W - 1, 2):
            m.lut(f"stage[{i}].u.lat.pair[{j // 2}].u", 6, LATCH_PAIR,
                  [d[j], c[i], q[i][j], d[j + 1], q[i][j + 1], "1"],
                  {"O5": q[i][j], "O6": q[i][j + 1]})
        if i + 1 < N:
            m.lut(f"stage[{i}].u.rdly.chain.g[0].u", 1, BUF, [c[i]], {"O": r[i + 1]})
    m.port("rst", "input", rst)
    m.port("req_in", "input", req_in)
    m.port("ack_out", "input", ack_out)
    m.port("data_in", "input", din)
    m.port("ack_in", "output", c[0])
    m.port("req_out", "output", c[N - 1])
    m.port("data_out", "output", q[N - 1])
    return m


def ring3(N=3, K=1):
    m = Mod("ring3")
    rst = m.net("rst")
    c = [m.net(f"c[{i}]") for i in range(N)]
    for i in range(N):
        m.lut(f"st[{i}].u", 6, C2N_SET if i < K else C2N,
              [c[(i - 1) % N], c[(i + 1) % N], c[i], rst, "0", "0"], {"O": c[i]})
    m.port("rst", "input", rst)
    m.port("c", "output", c)
    return m


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "."
    os.makedirs(out, exist_ok=True)
    for mod in (pipe3(), ring3()):
        with open(os.path.join(out, mod.name + ".json"), "w") as f:
            json.dump(mod.json(), f, indent=1)
        print("wrote", os.path.join(out, mod.name + ".json"))
