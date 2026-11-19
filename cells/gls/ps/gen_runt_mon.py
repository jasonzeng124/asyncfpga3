#!/usr/bin/env python3
"""gen_runt_mon.py -- a narrow-pulse (runt) monitor on the kernel's handshake outputs, for one bench route.

    python3 cells/gls/ps/gen_runt_mon.py ROUTED_JSON NETS_MAP OUT.v
    (cells/gls/ps/build_ps.sh runs it with PS_RUNTS=1, after gen.py, in the work directory; bench_gate.sh sets
     PS_RUNTS=1 under GATE_RUNTS=1 / GATE_RUNTS=fail and reads what the monitor prints)

WHY.  A bundled-data steer's output rises only with its request, and the request must find the select settled
(rule E).  When it does not, the wrong branch fires for as long as the select is late and then falls: a runt.  The
gate's model (cells/gls/fid_core.vh) passes every pulse through a LUT (transport) and lets the receiving C-element
reject one shorter than its own loop minus WIN/2 (TAU = WIN = 150 ps, unsourced), so a route can race on every call
and still return right answers: flow v1's ipow seed 4 route did (40 runts of 17-474 ps on the loop-exit steer in
9 us, research/data/suite/hangs.md section 3; SIM-VS-BOARD rows 4 and 6).  Whether silicon swallows such a pulse is
what BOARD-QUEUE item 2 (H_RUNT) measures.  This monitor makes the pulses visible to the gate instead of hiding them
behind the resolver.

WHAT IS WATCHED.  The kernel only (cells under bridge_i.udut. in nextpnr's routed JSON; never the bench's clocked
side), each net at its DRIVER pin in the netlist decoded from the bitstream (nets.map, as gen_bundle_mon.py): a pulse
is measured where it leaves the LUT, and the interconnect is transport, so every reader sees it.  A LUT output is
watched when it is
  (A) a state node -- its output routed back into one of its own pins (C-element, link controller, arbiter state) --
      except latch storage (`.lat.`: bd_latch / bd_latch_rst data bits);
  (B) a steer output (every LUT of a bd_steer: req0 = O5, req1 = O6, and the acknowledge OR);
  (C) the driver of one of the kernel's channel nets (a top-level `<name>_req` / `<name>_ack`): matched-delay outputs
      (a link's req_out / ack_in, a mux's / operator's / merge's z_req), a constant source's request;
  (D) a LUT that reads nothing but control and drives a pin of an (A) node: a muxn's select decode, an inner pipe
      stage's request line;
  (E) an arbiter's grants (`.ugrant`) and every cell's request OR (`.uor`).
Data LUTs (latch bits, data muxes `.udat.`, an operator's datapath, a merge's index / data) are never watched; the
interior elements of a matched delay are not (their last element is, by C or D).  Each net is reported with a class
(steer, mux, merge, link = a link / pipe stage's controller node = its latch enable, join = bd_join / bd_fork /
operator joins, op, chan, src, state) and the instance it belongs to.

WHAT IS COUNTED.  A pulse is a level bounded by the same 0/1 level on both sides (0-1-0 a high pulse, 1-0-1 a low
dip, 0-x-0 / 1-x-1 an x pulse); its width is the time between its two edges at the driver.  Each net is sampled 1 ps
after it changes (fid_core.vh's FID_SAMPLE): the changes of one time step count once, as the level they settle at, so a
zero-width simulator glitch (a resolver can move a state node twice in one step) is not a pulse.  Per net: pulses narrower than each of three
thresholds (+RUNT_T1 / +RUNT_T2 / +RUNT_T3, default 150 / 500 / 1000 ps; +RUNT_T3=0 sets the third to the loop
threshold: the longest loop of any watched state node at this run's corner + WIN/2 + 3 * WIN/4, the widest pulse the
gate's runt model can still reject at some reader), of which high / low / x, the narrowest 0/1
pulse of ANY width (a legitimate handshake phase included, so the separation between runts and handshakes is
visible), and the time of the first pulse narrower than T3.  Printed:
  RUNT t=.. k=.. w=.. lvl=1|0|x inst=.. net=..   the first +RUNT_MAXLINES (default 100) pulses narrower than T3
  RUNTMON batch=B k=.. cls=.. inst=.. role=.. net=.. n<T1>=.. n<T2>=.. n<T3>=.. hi=.. lo=.. x=.. min=.. first=..
                                                 cumulative, at every batch end (bench_busy falling), for every net
                                                 with a pulse narrower than T3 so far
  RUNTSUM batch=B nets=N n<T1>=.. n<T2>=.. n<T3>=.. x=.. hit=H minall=..
                                                 the same totals; minall = the narrowest 0/1 pulse on any watched net
and once more (batch=end) 1 ps before +TEND, in case the bench never finishes.  The per-net table (index, class,
instance, role, RTL net, driver pin, the node's own loop TLOOP and its state-node readers' loops, from gen.py's
netlist_baked.v) is written to runt_nets.tsv beside OUT.v.

A net that cannot be found in nets.map is an error, not a silent omission.
"""
import json, os, re, sys, collections

KPFX = "bridge_i.udut."


def main():
    rj, nmap, out = sys.argv[1:4]
    m = list(json.load(open(rj))["modules"].values())[0]
    nets, cells = m["netnames"], m["cells"]
    # the kernel's instance types (bdc's kernel Verilog beside the routed JSON, as gen_memport_mon.py)
    itype = {}
    kv = [f for f in os.listdir(os.path.dirname(os.path.abspath(rj))) if f.endswith("_kernel_bench.v")]
    if len(kv) == 1:
        ktext = open(os.path.join(os.path.dirname(os.path.abspath(rj)), kv[0])).read()
        for mt, nm in re.findall(r"^\s*(bd_\w+|bdc_\w+)\s*(?:#\(.*?\))?\s*(\w+)\s*\(", ktext, re.M | re.S):
            itype.setdefault(nm, mt)
    else:
        sys.exit("gen_runt_mon: want exactly one *_kernel_bench.v beside %s, found %s" % (rj, kv))

    names_of = collections.defaultdict(list)
    for n, v in nets.items():
        for b in v["bits"]:
            if isinstance(b, int):
                names_of[b].append(n)
    drv, rdrs = {}, collections.defaultdict(list)
    for cn, c in cells.items():
        bel = c["attributes"].get("NEXTPNR_BEL")
        for p, d in c.get("port_directions", {}).items():
            for b in c["connections"].get(p, []):
                if not isinstance(b, int):
                    continue
                if d == "output" and bel:
                    drv[b] = (cn, bel, p)
                elif d == "input":
                    rdrs[b].append((cn, p))
    by_pin = {}
    for line in open(nmap):
        if line.startswith("#"):
            continue
        w, _, n = line.strip().partition(" ")
        by_pin.setdefault(n, w)

    def kernel_lut(cn):
        c = cells[cn]
        return c["type"] == "SLICE_LUTX" and cn.startswith(KPFX)

    def ins(cn):
        c = cells[cn]
        return {b for p, d in c["port_directions"].items() if d == "input"
                for b in c["connections"].get(p, []) if isinstance(b, int)}

    def outs(cn):
        c = cells[cn]
        return [(p, b) for p, d in c["port_directions"].items() if d == "output"
                for b in c["connections"].get(p, []) if isinstance(b, int)]

    def split(cn):
        base = re.sub(r"\$LUT[56]$", "", cn)
        rest = base[len(KPFX):]
        top = rest.split(".")[0]
        return top, rest[len(top):], itype.get(top, "?")

    def is_data(cn):
        _, sub, _ = split(cn)
        return ".lat." in sub or ".udat." in sub

    chan_rx = re.compile(r"^" + re.escape(KPFX) + r"[A-Za-z0-9_]+_(req|ack)$")
    klut = [cn for cn in cells if kernel_lut(cn)]
    state = {}   # bit -> cell, for (A)
    for cn in klut:
        if is_data(cn):
            continue
        i = ins(cn)
        for p, b in outs(cn):
            if b in i:
                state[b] = cn
    statecells = set(state.values())
    datapath = ("bdc_fused", "bdc_load", "bdc_store", "bdc_memport")
    sel = {}     # bit -> (cell, port, why)
    for cn in klut:
        if is_data(cn):
            continue
        top, sub, mt = split(cn)
        for p, b in outs(cn):
            why = None
            if b in state:
                why = "A"
            elif mt == "bd_steer":
                why = "B"
            elif any(chan_rx.match(n) for n in names_of.get(b, [])):
                why = "C"
            elif re.search(r"\.(ugrant|ustate|uor)$", re.sub(r"\$LUT[56]$", "", cn)):
                why = "E"
            elif not mt.startswith(datapath) and any(rc in statecells for rc, _ in rdrs.get(b, [])):
                why = "D"   # feeds a state node's pin and is not an operator's datapath (a muxn decode, a pipe stage line)
            if why:
                sel[b] = (cn, p, why)

    def classify(cn, p, why):
        top, sub, mt = split(cn)
        base = re.sub(r"\$LUT[56]$", "", cn)
        if mt == "bd_steer":
            role = {"O5": "req0", "O6": "req1"}.get(p, p) if sub == ".u" else "ack" if sub == ".uack" else sub[1:]
            return "steer", top, role
        if ".ctl." in sub or sub.startswith(".ctl"):
            return "link", top, (sub[1:].replace(".ctl.u.u", ".en").replace(".u.ctl", "") or "en")
        if ".uarb" in sub or mt in ("bd_arbiter",):
            r = sub[1:]
            if r.endswith(".ustate"):
                r += ".q" if p == "O6" else ".R0"
            elif r.endswith(".ugrant"):
                r += ".g2" if p == "O6" else ".g1"
            return "merge", top, r
        if mt.startswith("bdc_amerge") or mt == "bd_merge":
            return "merge", top, sub[1:] or p
        if mt == "bd_mux" or mt.startswith("bdc_muxn"):
            return "mux", top, sub[1:] or p
        if mt.startswith("bdc_fused") or mt.startswith("bdc_load") or mt.startswith("bdc_store"):
            return ("op" if why != "A" else "join"), top, sub[1:] or p
        if mt in ("bd_join", "bd_fork"):
            return "join", top, mt[3:] + (sub if why != "A" else "")
        if mt == "bd_src":
            return "src", top, "req"
        if mt in ("bd_link", "bd_pipe") or mt.startswith("bdc_link") or mt.startswith("bdc_pipe"):
            return "chan", top, sub[1:] or p
        return ("state" if why == "A" else "chan"), top, sub[1:] or p

    def best_name(b):
        ns = names_of.get(b, [])
        top = [n for n in ns if chan_rx.match(n)]
        if top:   # a request output that also names a sink's acknowledge (bd_snk: ack = req) keeps its _req name
            return sorted(top, key=lambda n: (not n.endswith("_req"), len(n), n))[0][len(KPFX):]
        k = [n for n in ns if n.startswith(KPFX)]
        return (sorted(k, key=len)[0][len(KPFX):] if k else (ns[0] if ns else "?"))

    # loops from gen.py's baked netlist (the run's own corner), if present: the node's own TLOOP and its readers'
    tloop, rd_w, w_rd = {}, collections.defaultdict(list), {}
    nb = os.path.join(os.path.dirname(os.path.abspath(out)), "netlist_baked.v")
    if os.path.exists(nb):
        lut_rx = re.compile(r"SLICE_LUTX #\((.*?)\) (c_\d+) \((.*?)\);")
        for ln in open(nb):
            if ln.startswith("  ICBUF"):
                mm = re.search(r"\.I\((\w+)\), \.O\((\w+)\)", ln)
                if mm:
                    rd_w[mm.group(1)].append(mm.group(2))
            elif ln.startswith("  SLICE_LUTX"):
                mm = lut_rx.search(ln)
                if not mm:
                    continue
                prm, pins = mm.group(1), dict(re.findall(r"\.(\w+)\((\w+)\)", mm.group(3)))
                o = pins.get("O6") or pins.get("O5")
                t = re.search(r"\.TLOOP[56]\((\d+)\)", prm)
                if o and t:
                    tloop[o] = int(t.group(1))
                    for pn in ("A1", "A2", "A3", "A4", "A5", "A6"):
                        if pn in pins:
                            w_rd.setdefault(pins[pn], []).append(o)

    rows = []
    for b, (cn, p, why) in sorted(sel.items(), key=lambda kv: (kv[1][0], kv[1][1])):
        bel = cells[cn]["attributes"]["NEXTPNR_BEL"]
        pin = "%s/%s" % (bel, p)
        if pin not in by_pin:
            sys.exit("gen_runt_mon: %s (%s) -> %s not in %s" % (cn, p, pin, nmap))
        cls, inst, role = classify(cn, p, why)
        w = by_pin[pin]
        own = tloop.get(w)
        rl = sorted({tloop[o] for x in rd_w.get(w, []) for o in w_rd.get(x, []) if o in tloop and o != w})
        rows.append((cls, inst, role, best_name(b), pin, w, why, own, rl))
    if not rows:
        sys.exit("gen_runt_mon: no kernel net selected in %s" % rj)
    if "bridge_i.bench_busy" not in nets or nets["bridge_i.bench_busy"]["bits"][0] not in drv:
        sys.exit("gen_runt_mon: no placed driver for bridge_i.bench_busy in %s" % rj)
    bb = nets["bridge_i.bench_busy"]["bits"][0]
    bbpin = "%s/%s" % drv[bb][1:]
    if bbpin not in by_pin:
        sys.exit("gen_runt_mon: bench_busy -> %s not in %s" % (bbpin, nmap))

    NN = len(rows)
    owns = [r[7] for r in rows if r[7] is not None]
    TLMAX = max(owns) if owns else 0
    L = ["// GENERATED by cells/gls/ps/gen_runt_mon.py for one route -- do not check in.",
         "`timescale 1ps/1ps",
         "module runt_mon;",
         "    localparam integer NN = %d;" % NN,
         "    // the longest loop (TLOOP: feedback wire + pin arc, gen.py) of any watched state node at this run's corner",
         "    localparam integer TLMAX = %d;" % TLMAX,
         "    wire [NN-1:0] s;"]
    for k, r in enumerate(rows):
        L.append("    assign s[%d] = tb_ps.dut.%s;   // %s %s %s %s %s" % (k, r[5], r[0], r[1], r[2], r[3], r[4]))
    L.append("    wire bench_busy = tb_ps.dut.%s;   // %s" % (by_pin[bbpin], bbpin))
    clist = sorted({r[0] for r in rows})
    L.append("    localparam integer NC = %d;" % len(clist))
    L.append("    integer ck [0:NN-1];   // the class of each net: %s" % " ".join("%d=%s" % kv for kv in enumerate(clist)))
    L.append("    reg [8*8-1:0] cn [0:NC-1];")
    L.append("    initial begin")
    for k, r in enumerate(rows):
        L.append("        ck[%d] = %d;" % (k, clist.index(r[0])))
    for i, c in enumerate(clist):
        L.append('        cn[%d] = "%s";' % (i, c))
    L.append("    end")
    L.append("    reg [8*200-1:0] nm [0:NN-1];")
    L.append("    initial begin")
    for k, r in enumerate(rows):
        L.append('        nm[%d] = "cls=%s inst=%s role=%s net=%s";' % (k, r[0], r[1], r[2], r[3][-80:]))
    L.append("    end")
    L += [
        "    integer t1, t2, t3, maxl, nl, batch, tend, k0, win;",
        "    time tl [0:NN-1], tf [0:NN-1], mn [0:NN-1];",
        "    reg [1:0] pv [0:NN-1], cv [0:NN-1];",
        "    integer c1 [0:NN-1], c2 [0:NN-1], c3 [0:NN-1], ch [0:NN-1], cl [0:NN-1], cx [0:NN-1];",
        "    time big = 64'd1 << 60;",
        "    initial begin",
        "        t1 = 150; t2 = 500; t3 = 1000; maxl = 100; nl = 0; batch = 0; tend = 0;",
        "        if ($value$plusargs(\"RUNT_T1=%d\", t1)) ;",
        "        if ($value$plusargs(\"RUNT_T2=%d\", t2)) ;",
        "        if ($value$plusargs(\"RUNT_T3=%d\", t3)) ;",
        "        // +RUNT_T3=0: the loop threshold -- the longest kernel loop + WIN/2 + 3 sigma of the resolver's noise",
        "        // (WIN/4): the widest pulse the gate's runt model (fid_core.vh) can still reject at some reader",
        "        win = 150; if ($value$plusargs(\"META_WIN=%d\", win)) ;",
        "        if (t3 == 0) t3 = TLMAX + win / 2 + 3 * (win / 4);",
        "        if ($value$plusargs(\"RUNT_MAXLINES=%d\", maxl)) ;",
        "        for (k0 = 0; k0 < NN; k0 = k0 + 1) begin",
        "            tl[k0] = 0; tf[k0] = 0; mn[k0] = big; pv[k0] = 2; cv[k0] = 2;",
        "            c1[k0] = 0; c2[k0] = 0; c3[k0] = 0; ch[k0] = 0; cl[k0] = 0; cx[k0] = 0;",
        "        end",
        "        $display(\"RUNTMON setup nets=%0d t1=%0d t2=%0d t3=%0d tloopmax=%0d (cells/gls/ps/gen_runt_mon.py)\", NN, t1, t2, t3,",
        "                 TLMAX);",
        "    end",
        "    function [1:0] enc(input v);",
        "        enc = (v === 1'b0) ? 2'd0 : (v === 1'b1) ? 2'd1 : 2'd2;",
        "    endfunction",
        "    // edge_(k, value, t): called 1 ps after a change (the sampler below), with the level the net settled at in",
        "    // that time step and the step's time t; a step whose changes cancel is no edge (no zero-width pulse).",
        "    task edge_(input integer k, input [1:0] nv, input time te);",
        "        time w;",
        "        begin",
        "            if (nv != cv[k]) begin",
        "                begin",
        "                    if (pv[k] != 2'd2 && nv == pv[k]) begin   // a pulse of level cv[k], same level both sides",
        "                        w = te - tl[k];",
        "                        if (cv[k] != 2'd2 && w < mn[k]) mn[k] = w;",
        "                        if (w < t3) begin",
        "                            if (cv[k] == 2'd2) cx[k] = cx[k] + 1;",
        "                            else begin",
        "                                c3[k] = c3[k] + 1;",
        "                                if (w < t2) c2[k] = c2[k] + 1;",
        "                                if (w < t1) c1[k] = c1[k] + 1;",
        "                                if (cv[k] == 2'd1) ch[k] = ch[k] + 1; else cl[k] = cl[k] + 1;",
        "                            end",
        "                            if (tf[k] == 0) tf[k] = tl[k];",
        "                            if (nl < maxl) begin",
        "                                nl = nl + 1;",
        "                                $display(\"RUNT t=%0t k=%0d w=%0d lvl=%0s %0s\", tl[k], k, w,",
        "                                         cv[k] == 2'd1 ? \"1\" : cv[k] == 2'd0 ? \"0\" : \"x\", nm[k]);",
        "                            end",
        "                        end",
        "                    end",
        "                    pv[k] = cv[k]; cv[k] = nv; tl[k] = te;",
        "                end",
        "            end",
        "        end",
        "    endtask",
        "    genvar g;",
        "    // the sampler (fid_core.vh's FID_SAMPLE): the level 1 ps after a change, so the changes of one time step count",
        "    // once, as the level they settle at (a state node's resolver can move its output twice in one step)",
        "    generate for (g = 0; g < NN; g = g + 1) begin : w",
        "        reg armed = 1'b0;",
        "        time ts;",
        "        always @(s[g]) if (!armed) begin armed = 1'b1; ts = $time; #1; armed = 1'b0; edge_(g, enc(s[g]), ts); end",
        "    end endgenerate",
        "    task report(input integer b);",
        "        integer k, a1, a2, a3, ax, hit, c, cnn, chit, cn3, im;",
        "        time ma, cmin;",
        "        begin",
        "            a1 = 0; a2 = 0; a3 = 0; ax = 0; hit = 0; ma = big;",
        "            for (k = 0; k < NN; k = k + 1) begin",
        "                a1 = a1 + c1[k]; a2 = a2 + c2[k]; a3 = a3 + c3[k]; ax = ax + cx[k];",
        "                if (mn[k] < ma) ma = mn[k];",
        "                if (c3[k] + cx[k] > 0) begin",
        "                    hit = hit + 1;",
        "                    if (b < 0)",
        "                        $display(\"RUNTMON batch=end k=%0d n1=%0d n2=%0d n3=%0d hi=%0d lo=%0d x=%0d min=%0d first=%0t %0s\",",
        "                                 k, c1[k], c2[k], c3[k], ch[k], cl[k], cx[k], mn[k] == big ? 0 : mn[k], tf[k], nm[k]);",
        "                    else",
        "                        $display(\"RUNTMON batch=%0d k=%0d n1=%0d n2=%0d n3=%0d hi=%0d lo=%0d x=%0d min=%0d first=%0t %0s\",",
        "                                 b, k, c1[k], c2[k], c3[k], ch[k], cl[k], cx[k], mn[k] == big ? 0 : mn[k], tf[k], nm[k]);",
        "                end",
        "            end",
        "            for (c = 0; c < NC; c = c + 1) begin   // per class: nets, nets hit, pulses < T3, narrowest pulse of any width",
        "                cnn = 0; chit = 0; cn3 = 0; cmin = big;",
        "                for (k = 0; k < NN; k = k + 1) if (ck[k] == c) begin",
        "                    cnn = cnn + 1; cn3 = cn3 + c3[k] + cx[k]; if (c3[k] + cx[k] > 0) chit = chit + 1;",
        "                    if (mn[k] < cmin) cmin = mn[k];",
        "                end",
        "                im = (cmin == big) ? -1 : cmin;",
        "                if (b < 0) $display(\"RUNTCLS batch=end cls=%0s nets=%0d hit=%0d n3=%0d minall=%0d\", cn[c], cnn, chit, cn3, im);",
        "                else $display(\"RUNTCLS batch=%0d cls=%0s nets=%0d hit=%0d n3=%0d minall=%0d\", b, cn[c], cnn, chit, cn3, im);",
        "            end",
        "            im = (ma == big) ? -1 : ma;",
        "            if (b < 0)",
        "                $display(\"RUNTSUM batch=end nets=%0d t1=%0d t2=%0d t3=%0d n1=%0d n2=%0d n3=%0d x=%0d hit=%0d minall=%0d tloopmax=%0d\",",
        "                         NN, t1, t2, t3, a1, a2, a3, ax, hit, im, TLMAX);",
        "            else",
        "                $display(\"RUNTSUM batch=%0d nets=%0d t1=%0d t2=%0d t3=%0d n1=%0d n2=%0d n3=%0d x=%0d hit=%0d minall=%0d tloopmax=%0d\",",
        "                         b, NN, t1, t2, t3, a1, a2, a3, ax, hit, im, TLMAX);",
        "        end",
        "    endtask",
        "    // a batch ends when bench_busy goes 1 -> 0 (gen_memport_mon.py's rule: its x -> 0 at reset is not one)",
        "    reg busy_q = 1'b0;",
        "    always @(bench_busy) begin",
        "        if (busy_q === 1'b1 && bench_busy === 1'b0) begin report(batch); batch = batch + 1; end",
        "        busy_q = bench_busy;",
        "    end",
        "    initial if ($value$plusargs(\"TEND=%d\", tend) && tend > 0) begin #(tend * 1000 - 1); report(-1); end",
        "endmodule"]
    open(out, "w").write("\n".join(L) + "\n")
    tsv = os.path.join(os.path.dirname(os.path.abspath(out)), "runt_nets.tsv")
    with open(tsv, "w") as f:
        f.write("# k\tclass\tinstance\trole\tnet\tdriver_pin\twire\twhy\town_tloop_ps\treaders_tloop_ps (min..max (n) over its readers that are state nodes)\n")
        for k, r in enumerate(rows):
            f.write("%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" % (
                k, r[0], r[1], r[2], r[3], r[4], r[5], r[6], "" if r[7] is None else r[7],
                "%d..%d (%d)" % (r[8][0], r[8][-1], len(r[8])) if r[8] else ""))
    cnt = collections.Counter(r[0] for r in rows)
    print("runt monitor: %d kernel nets (%s), bench_busy %s -> %s; table %s" % (
        NN, ", ".join("%s %d" % kv for kv in sorted(cnt.items())), bbpin, out, tsv))


if __name__ == "__main__":
    main()
