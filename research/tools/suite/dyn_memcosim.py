#!/usr/bin/env python3
"""dyn_memcosim.py [--seeds N] [--cycles C] [--defect NAME] -- dynamatic_est.py's memory units against Dynamatic's own
Verilog, cycle by cycle (dynfig, 2026-11-18).

dynamatic_est.py's MemController and Load classes are a transcription of dynamatic/data/verilog (mem_controller.v,
mem_controller_loadless.v, support/mc_support.v: read_memory_arbiter, write_memory_arbiter, the pending-store counter,
mc_control; load.v: two tehbs, handshake/tehb.v + dataless/tehb.v).  The answer check of the estimator cannot see a
cycle-count error in them (research/data/suite/dynamatic/README.md, control d).  This runs both on the same circuit
and the same random environment and compares every port in every cycle:

  two `load` units -> mem_controller (NUM_LOADS 2, NUM_STORES 1, NUM_CONTROLS 1, DATA 8, ADDR 4) -> a BRAM with a
  1-cycle registered read (loadEn: q <= mem[loadAddr]; storeEn: mem[storeAddr] <= storeData, read-first), the
  testbench's memory as the estimator models it.

Environment (identical on both sides, a deterministic function of seeded tables and the DUT's readies): every input
channel (two load addresses, store address, store data, ctrl, memStart, ctrlEnd) offers a token sequence with random
gaps (0 = back to back) and holds valid and data until taken; the load data outputs and memEnd see a random ready
each cycle.  Logged per cycle: each load's addrIn_ready / dataOut_valid / dataOut, stAddr_ready, stData_ready,
ctrl_ready, memStart_ready, memEnd_valid, ctrlEnd_ready, the BRAM port (loadEn + loadAddr, storeEn + storeAddr +
storeData); and the BRAM's contents at the end.  Verilog: iverilog on the files from dynamatic/data/verilog, unedited.

--defect injects an error into the Python units (a negative control: it must be reported):
  bram2   the read data arrives one cycle late (the BRAM's read latency 2)
  prio    the read arbiter prefers load 1 over load 0
  nodec   a store does not decrement the pending-store counter
Exit 0 when every seed matches (or, with --defect, when every seed mismatches)."""
import argparse
import os
import random
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dynamatic_est as de  # noqa: E402

VDIR = os.path.join(de.DYN, "data", "verilog")
VFILES = ["handshake/mem_controller.v", "handshake/mem_controller_loadless.v", "handshake/load.v", "handshake/tehb.v",
          "handshake/dataless/tehb.v", "support/mc_support.v"]
INS = ["a0", "a1", "sa", "sd", "ct", "ms", "ce"]      # environment -> circuit
OUTS = ["d0", "d1", "me"]                             # circuit -> environment (random ready)
DW, AW, DEPTH = 8, 4, 16

TB = r"""
`timescale 1ns/1ps
module tb;
  reg clk = 0, rst = 1;
  always #5 clk = ~clk;
  localparam N = %(N)d;
  reg [31:0] T_a0 [0:N]; reg [31:0] T_a1 [0:N]; reg [31:0] T_sa [0:N]; reg [31:0] T_sd [0:N];
  reg [31:0] T_ct [0:N]; reg [31:0] T_ms [0:N]; reg [31:0] T_ce [0:N]; reg [2:0] RB [0:N];
  reg [7:0] mem [0:15]; reg [7:0] q;
  integer cyc, f, i;
  initial begin
    $readmemh("a0.hex", T_a0); $readmemh("a1.hex", T_a1); $readmemh("sa.hex", T_sa); $readmemh("sd.hex", T_sd);
    $readmemh("ct.hex", T_ct); $readmemh("ms.hex", T_ms); $readmemh("ce.hex", T_ce); $readmemh("rb.hex", RB);
    $readmemh("mem.hex", mem);
  end
`define ENV(ch) \
  reg ch``_v; reg [15:0] ch``_x; reg [15:0] ch``_w; integer ch``_i; wire ch``_r; \
  always @(posedge clk) begin \
    if (rst) begin ch``_v <= 0; ch``_i <= 0; ch``_w <= T_``ch[0][31:16]; ch``_x <= 0; end \
    else if (ch``_v && ch``_r) begin \
      ch``_i <= ch``_i + 1; \
      if (T_``ch[ch``_i + 1][31:16] == 0) begin ch``_v <= 1; ch``_x <= T_``ch[ch``_i + 1][15:0]; end \
      else begin ch``_v <= 0; ch``_w <= T_``ch[ch``_i + 1][31:16] - 1; end \
    end else if (!ch``_v) begin \
      if (ch``_w == 0) begin ch``_v <= 1; ch``_x <= T_``ch[ch``_i][15:0]; end else ch``_w <= ch``_w - 1; \
    end \
  end
  `ENV(a0) `ENV(a1) `ENV(sa) `ENV(sd) `ENV(ct) `ENV(ms) `ENV(ce)
  wire d0_r = RB[cyc][0], d1_r = RB[cyc][1], me_r = RB[cyc][2];
  wire [3:0] l0_ao, l1_ao; wire l0_aov, l1_aov, l0_aor, l1_aor;
  wire [7:0] l0_dm, l1_dm; wire l0_dmv, l1_dmv, l0_dmr, l1_dmr;
  wire [7:0] d0_x, d1_x; wire d0_v, d1_v, me_v;
  wire loadEn, storeEn; wire [3:0] loadAddr, storeAddr; wire [7:0] storeData;
  load #(.DATA_TYPE(8), .ADDR_TYPE(4)) l0 (.clk(clk), .rst(rst), .addrIn(a0_x[3:0]), .addrIn_valid(a0_v),
    .addrIn_ready(a0_r), .addrOut(l0_ao), .addrOut_valid(l0_aov), .addrOut_ready(l0_aor), .dataFromMem(l0_dm),
    .dataFromMem_valid(l0_dmv), .dataFromMem_ready(l0_dmr), .dataOut(d0_x), .dataOut_valid(d0_v), .dataOut_ready(d0_r));
  load #(.DATA_TYPE(8), .ADDR_TYPE(4)) l1 (.clk(clk), .rst(rst), .addrIn(a1_x[3:0]), .addrIn_valid(a1_v),
    .addrIn_ready(a1_r), .addrOut(l1_ao), .addrOut_valid(l1_aov), .addrOut_ready(l1_aor), .dataFromMem(l1_dm),
    .dataFromMem_valid(l1_dmv), .dataFromMem_ready(l1_dmr), .dataOut(d1_x), .dataOut_valid(d1_v), .dataOut_ready(d1_r));
  mem_controller #(.NUM_CONTROLS(1), .NUM_LOADS(2), .NUM_STORES(1), .DATA_TYPE(8), .ADDR_TYPE(4)) mc (
    .clk(clk), .rst(rst), .memStart_valid(ms_v), .memStart_ready(ms_r), .memEnd_valid(me_v), .memEnd_ready(me_r),
    .ctrlEnd_valid(ce_v), .ctrlEnd_ready(ce_r), .ctrl({16'b0, ct_x}), .ctrl_valid(ct_v), .ctrl_ready(ct_r),
    .ldAddr({l1_ao, l0_ao}), .ldAddr_valid({l1_aov, l0_aov}), .ldAddr_ready({l1_aor, l0_aor}),
    .ldData({l1_dm, l0_dm}), .ldData_valid({l1_dmv, l0_dmv}), .ldData_ready({l1_dmr, l0_dmr}),
    .stAddr(sa_x[3:0]), .stAddr_valid(sa_v), .stAddr_ready(sa_r), .stData(sd_x[7:0]), .stData_valid(sd_v),
    .stData_ready(sd_r), .loadData(q), .loadEn(loadEn), .loadAddr(loadAddr), .storeEn(storeEn),
    .storeAddr(storeAddr), .storeData(storeData));
  always @(posedge clk) begin
    if (loadEn) q <= mem[loadAddr];
    if (storeEn) mem[storeAddr] <= storeData;
  end
  initial begin
    f = $fopen("v.log", "w");
    cyc = 0;
    @(posedge clk); #1 rst = 0;
    for (cyc = 0; cyc < N; cyc = cyc + 1) begin
      @(negedge clk);
      $fdisplay(f, "%%0d a0r=%%0d a1r=%%0d d0=%%0d:%%0h d1=%%0d:%%0h sar=%%0d sdr=%%0d ctr=%%0d msr=%%0d mev=%%0d cer=%%0d ld=%%0d:%%0h st=%%0d:%%0h:%%0h",
        cyc, a0_r, a1_r, d0_v, d0_v ? d0_x : 0, d1_v, d1_v ? d1_x : 0, sa_r, sd_r, ct_r, ms_r, me_v, ce_r,
        loadEn, loadEn ? loadAddr : 0, storeEn, storeEn ? storeAddr : 0, storeEn ? storeData : 0);
      @(posedge clk);
    end
    #1;
    for (i = 0; i < 16; i = i + 1) $fdisplay(f, "mem %%0d %%0h", i, mem[i]);
    $fclose(f);
    $finish;
  end
endmodule
"""


def tables(seed, n):
    rng = random.Random(seed)
    T = {}
    for ch in INS:
        rows = []
        for _ in range(n + 1):
            gap = rng.choice([0, 0, 0, 1, 1, 2, 3, 7]) if ch in ("a0", "a1", "sa", "sd") else rng.choice([0, 1, 3, 9, 20])
            if ch in ("a0", "a1", "sa"):
                x = rng.randrange(DEPTH)
            elif ch == "sd":
                x = rng.randrange(256)
            elif ch == "ct":
                x = rng.choice([0, 1, 1, 2, 3])
            else:
                x = 0
            rows.append((gap, x))
        T[ch] = rows
    rb = [rng.randrange(8) if rng.random() < 0.8 else 7 for _ in range(n + 1)]
    mem = [(i * 37 + 11 + seed) & 0xFF for i in range(DEPTH)]
    return T, rb, mem


class _Sim:
    def __init__(self, nchan, mem):
        self.V, self.R, self.D = [False] * nchan, [False] * nchan, [0] * nchan
        self.memories = {"m": list(mem)}
        self.stores = 0


def python_run(T, rb, mem, n, defect=None):
    # channels: a0 -> l0.addrIn (0); l0.addrOut -> mc (1); mc -> l0.dataFromMem (2); l0.dataOut -> env (3); same for
    # l1 (4..7); sa (8); sd (9); ct (10); ms (11); ce (12); me (13)
    sim = _Sim(14, mem)
    l0 = de.Load(sim, "l0", 0, [0, 2], [1, 3])
    l1 = de.Load(sim, "l1", 0, [4, 6], [5, 7])
    mc = de.MemController(sim, "mc", 0, 11, [10], [1, 5], [2, 6], [8], [9], 12, 13, "m", DEPTH, DW)
    if defect == "prio":
        mc.ld_addr, mc.ld_data = mc.ld_addr[::-1], mc.ld_data[::-1]
    if defect == "nodec":
        orig = mc.tick

        def tick_nodec():
            c = mc.counter
            st = any(mc._st_sel())
            orig()
            if st:
                mc.counter += 1
        mc.tick = tick_nodec
    units = [l0, l1, mc]
    for u in units:
        u.reset()
    if defect == "bram2":
        orig_tick = mc.tick
        hold = {"prev": 0}

        def tick_bram2():
            rd = any(mc._ld_sel())
            orig_tick()
            if rd:     # the word read now comes out with the NEXT read: one register too many on the data path
                mc.bram_q, hold["prev"] = hold["prev"], mc.bram_q
        mc.tick = tick_bram2
    chan = {"a0": 0, "a1": 4, "sa": 8, "sd": 9, "ct": 10, "ms": 11, "ce": 12}
    env = {ch: dict(v=False, i=0, w=T[ch][0][0], x=0) for ch in INS}
    V, R, D = sim.V, sim.R, sim.D
    log = []
    for cyc in range(n):
        for ch in INS:
            c = chan[ch]
            V[c] = env[ch]["v"]
            D[c] = env[ch]["x"] & (0xF if ch in ("a0", "a1", "sa") else 0xFF if ch == "sd" else 0xFFFF)
        R[3], R[7], R[13] = bool(rb[cyc] & 1), bool(rb[cyc] & 2), bool(rb[cyc] & 4)
        for _ in range(100):
            if not any([u.comb() for u in units]):
                break
        else:
            raise RuntimeError("no fixed point at cycle %d" % cyc)
        ls, ss = mc._ld_sel(), mc._st_sel()
        le = any(ls)
        la = D[mc.ld_addr[ls.index(True)]] if le else 0
        se = any(ss)
        sa_, sd_ = (D[mc.st_addr[0]], D[mc.st_data[0]]) if se else (0, 0)
        log.append("%d a0r=%d a1r=%d d0=%d:%x d1=%d:%x sar=%d sdr=%d ctr=%d msr=%d mev=%d cer=%d ld=%d:%x st=%d:%x:%x" % (
            cyc, R[0], R[4], V[3], D[3] if V[3] else 0, V[7], D[7] if V[7] else 0, R[8], R[9], R[10], R[11], V[13],
            R[12], le, la, se, sa_, sd_))
        hs = {ch: env[ch]["v"] and R[chan[ch]] for ch in INS}
        for u in units:
            u.tick()
        for ch in INS:
            e = env[ch]
            if hs[ch]:
                e["i"] += 1
                g, x = T[ch][e["i"]]
                if g == 0:
                    e["v"], e["x"] = True, x
                else:
                    e["v"], e["w"] = False, g - 1
            elif not e["v"]:
                if e["w"] == 0:
                    e["v"], e["x"] = True, T[ch][e["i"]][1]
                else:
                    e["w"] -= 1
    log += ["mem %d %x" % (i, x) for i, x in enumerate(sim.memories["m"])]
    return log


def verilog_run(T, rb, mem, n, work):
    for ch in INS:
        with open(os.path.join(work, ch + ".hex"), "w") as f:
            f.write("\n".join("%08x" % ((g << 16) | x) for g, x in T[ch]) + "\n")
    with open(os.path.join(work, "rb.hex"), "w") as f:
        f.write("\n".join("%x" % b for b in rb) + "\n")
    with open(os.path.join(work, "mem.hex"), "w") as f:
        f.write("\n".join("%02x" % x for x in mem) + "\n")
    with open(os.path.join(work, "tb.v"), "w") as f:
        f.write(TB % dict(N=n))
    exe = os.path.join(work, "tb.vvp")
    if not os.path.exists(exe):
        subprocess.run(["iverilog", "-g2012", "-o", exe, os.path.join(work, "tb.v")] +
                       [os.path.join(VDIR, x) for x in VFILES], check=True, cwd=work)
    subprocess.run(["vvp", "-n", exe], check=True, cwd=work, stdout=subprocess.DEVNULL)
    return [l.rstrip("\n") for l in open(os.path.join(work, "v.log"))]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--seeds", type=int, default=8)
    ap.add_argument("--cycles", type=int, default=3000)
    ap.add_argument("--defect", choices=["bram2", "prio", "nodec"])
    a = ap.parse_args()
    work = tempfile.mkdtemp(prefix="dyn_memcosim_")
    bad = 0
    events = dict(ld=0, st=0, d0=0, d1=0, me=0)
    for s in range(1, a.seeds + 1):
        T, rb, mem = tables(s, a.cycles)
        vl = verilog_run(T, rb, mem, a.cycles, work)
        pl = python_run(T, rb, mem, a.cycles, a.defect)
        diff = next((i for i, (x, y) in enumerate(zip(vl, pl)) if x != y), None)
        if diff is None and len(vl) != len(pl):
            diff = min(len(vl), len(pl))
        for l in vl:
            events["ld"] += " ld=1" in l
            events["st"] += " st=1" in l
            events["d0"] += " d0=1" in l
            events["d1"] += " d1=1" in l
            events["me"] += " mev=1" in l
        if diff is None:
            print("seed %d: %d cycles, every port equal in every cycle, BRAM contents equal" % (s, a.cycles))
        else:
            bad += 1
            print("seed %d: MISMATCH at line %d\n  verilog: %s\n  python:  %s" % (s, diff, vl[diff] if diff < len(vl)
                                                                                    else "-", pl[diff] if diff < len(pl) else "-"))
    print("events over all seeds (Verilog): BRAM reads %(ld)d, BRAM writes %(st)d, cycles with load 0 data valid "
          "%(d0)d, load 1 data valid %(d1)d, memEnd valid %(me)d" % events)
    if a.defect:
        print("defect %s: %d of %d seeds mismatch -> %s" % (a.defect, bad, a.seeds, "CAUGHT" if bad == a.seeds else
                                                            "NOT CAUGHT on every seed"))
        sys.exit(0 if bad == a.seeds else 1)
    print("%d of %d seeds match" % (a.seeds - bad, a.seeds))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
