#!/usr/bin/env python3
"""
soak_fid.py -- routed GLS of a fusion_bench / flow.sh "soak" route (the kernel
harness, e.g. ipow with BD_DSP=1), on either netlist:

    soak_fid.py SEEDDIR WORK ref                     nextpnr's routed JSON (as fusion_bench does)
    soak_fid.py SEEDDIR WORK fasm  [--fasm F]        rebuilt from a FASM (default SEEDDIR/pnr/soak.fasm)
    soak_fid.py SEEDDIR WORK bit    --bit B          rebuilt from a bitstream

SEEDDIR is a fusion_bench route dir: pnr/{soak_routed.json, soak.sdf,
soak.fasm, soak.json}, tb_fast.v and tb_stalled.v, with input.mlir in its parent.

The testbench is built exactly as bdc/fusion_bench.py simulate_route() builds
it -- same harness text, same bd_source SETUP leads, same port nets resolved
with routed_signals() -- except that on the FASM-built netlist each routed-JSON
net is replaced by the net with the SAME DRIVER BEL PIN in the bits' netlist.
The result is one line per kind:

    SOAK <kind> PASS lat=<per-vector latencies, ps>      or      SOAK <kind> FAIL: <why>

and one verdict line, SOAK_VERDICT PASS|FAIL, exit 0|1.  A REFUSED decode
(a bit configuration the model does not have, e.g. INMODE[1]=1) is a FAIL.
"""
import argparse, json, os, re, shutil, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GLS = HERE.parent
CELLS = GLS.parent
sys.path.insert(0, str(CELLS.parent / "bdc"))
import fusion_bench as FB          # noqa: E402
import emit                        # noqa: E402
from hs import parse               # noqa: E402


def run(cmd, log, **kw):
    r = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **kw)
    Path(log).write_text(r.stdout)
    return r.returncode, r.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("seeddir", type=Path)
    ap.add_argument("work", type=Path)
    ap.add_argument("mode", choices=("ref", "fasm", "bit"))
    ap.add_argument("--fasm", type=Path)
    ap.add_argument("--bit", type=Path)
    ap.add_argument("--gate", action="store_true", help="also run the ANNOTATE_DONE gate")
    a = ap.parse_args()
    sd = a.seeddir.resolve()
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    func = parse.parse_module((sd.parent / "input.mlir").read_text())[0]
    pnr = sd / "pnr"

    def verdict(ok, lines):
        for ln in lines:
            print(ln)
        print("SOAK_VERDICT %s" % ("PASS" if ok else "FAIL"))
        sys.exit(0 if ok else 1)

    # ---- the netlist
    if a.mode == "ref":
        shutil.copy2(pnr / "soak_routed.json", work / "routed.json")
        shutil.copy2(pnr / "soak.sdf", work / "routed.sdf")
    else:
        src = ["--bit", str(a.bit)] if a.mode == "bit" else ["--fasm", str(a.fasm or pnr / "soak.fasm")]
        rc, out = run([sys.executable, str(HERE / "fasm2net.py"), *src, "--out", str(work / "fid"),
                       "--names", str(pnr / "soak_routed.json"), "--sdf", str(pnr / "soak.sdf"), "--allow"],
                      work / "fasm2net.log")
        rep = (work / "fid/report.txt").read_text() if (work / "fid/report.txt").exists() else out
        refused = [l.strip() for l in rep.splitlines() if re.match(r"\s+\d+\s+(REFUSED|CONTENTION|FLOATING)", l)]
        if rc and not (work / "fid/fasm_routed.json").exists():
            verdict(False, ["SOAK all FAIL: fasm2net failed, see %s" % (work / "fasm2net.log")])
        if refused:
            ex = [l.strip() for l in rep.splitlines() if "e.g." in l][:3]
            verdict(False, ["SOAK all FAIL: the bits decode to something the model refuses: %s | %s"
                            % ("; ".join(refused), " | ".join(ex))])
        shutil.copy2(work / "fid/fasm_routed.json", work / "routed.json")
        shutil.copy2(work / "fid/fasm.sdf", work / "routed.sdf")
    rc, _ = run([sys.executable, str(GLS / "gen.py")], work / "generate.log",
                env={**os.environ, "GLS_WORK": str(work)}, timeout=FB.GLS_TIMEOUT)
    if rc:
        verdict(False, ["SOAK all FAIL: gen.py failed, see %s" % (work / "generate.log")])
    if a.gate:
        run(["iverilog", "-g2012", "-gspecify", "-s", "tb_gate", "-o", str(work / "gate.vvp"),
             str(GLS / "prims.v"), str(work / "netlist.v"), str(GLS / "tb_gate.v")], work / "compile_gate.log")
        _, g = run(["vvp", "gate.vvp"], work / "gate.log", cwd=work, timeout=FB.GLS_TIMEOUT)
        print("GATE %s" % ("ANNOTATE_DONE clean" if "ANNOTATE_DONE" in g and not re.search(r"WARNING|ERROR", g)
                           else "FAILED, see %s" % (work / "gate.log")))

    # ---- port nets: fusion_bench's own resolution on the routed JSON ...
    signals = FB.routed_signals(sd, func)
    if a.mode != "ref":
        # ... then the same driver bel pin in the bits' netlist
        rj = json.loads((pnr / "soak_routed.json").read_text())["modules"]["top"]
        fj = json.loads((work / "routed.json").read_text())["modules"]["top"]
        drv = {}
        for cn, c in rj["cells"].items():
            for p, bl in c["connections"].items():
                if c["port_directions"].get(p) == "output" and bl:
                    drv[bl[0]] = (c["attributes"].get("NEXTPNR_BEL"), p, c["type"])
        fbit = {}
        for cn, c in fj["cells"].items():
            for p, bl in c["connections"].items():
                if c["port_directions"].get(p) == "output" and bl:
                    fbit[(c["attributes"].get("NEXTPNR_BEL"), p)] = bl[0]
                    if c["type"] == "PSEUDO_VCC":
                        fbit["VCC"] = bl[0]
                    if c["type"] == "PSEUDO_GND":
                        fbit["GND"] = bl[0]
        missing = []

        def tr(b):
            d = drv.get(b)
            if d is None:
                missing.append(b)
                return b
            if d[2] in ("PSEUDO_VCC", "PSEUDO_GND"):
                missing.append(("const", b))
                return fbit.get("VCC" if d[2] == "PSEUDO_VCC" else "GND", b)
            if (d[0], d[1]) not in fbit:
                missing.append((d[0], d[1]))
                return b
            return fbit[(d[0], d[1])]
        signals = {p: [tr(b) for b in bits] for p, bits in signals.items()}
        if missing:
            verdict(False, ["SOAK all FAIL: %d port bits have no same-driver net in the bits' netlist: %s"
                            % (len(missing), missing[:6])])
    leads = FB.source_lead(sd, FB.routed_signals(sd, func),
                           [emit.portname(x.name) for x in func.args if not x.is_control])
    drive, observe = ["rst"], []
    for res in func.results:
        b = emit.portname(res.name)
        drive.append(f"{b}_ack")
        observe += [f"{b}_req"] + ([] if res.is_control else [f"{b}_data"])
    for arg in func.args:
        b = emit.portname(arg.name)
        drive += [f"{b}_req"] + ([] if arg.is_control else [f"{b}_data"])
        observe.append(f"{b}_ack")
    connection = ["top dut();"]
    driven = set()
    for port in drive:
        for i, bit in enumerate(signals[port]):
            if bit in driven:
                verdict(False, ["SOAK all FAIL: harness aliases independently driven ports"])
            driven.add(bit)
            value = f"{port}[{i}]" if port.endswith("_data") else port
            connection.append(f"wire drive_{bit} = {value};")
            connection.append(f"initial force dut.n{bit} = drive_{bit};")
    for port in observe:
        bits = signals[port]
        connection.append(f"assign {port} = " + "{" + ", ".join(f"dut.n{b}" for b in reversed(bits)) + "};")
    ok, lines = True, []
    for kind in ("stalled", "fast"):
        tb = (sd / f"tb_{kind}.v").read_text()
        tb = re.sub(r"bdc_\w+ dut\([^\n]+", "\n".join(connection), tb)
        for arg, lead in leads.items():
            if lead is not None:
                tb = re.sub(rf"bd_source #\(\.W\((\d+)\)\) {arg}_src\(",
                            rf"bd_source #(.W(\1), .SETUP({lead})) {arg}_src(", tb)
        (work / f"tb_{kind}.v").write_text(tb)
        sim = work / f"sim_{kind}.vvp"
        rc, _ = run(["iverilog", "-g2012", "-gspecify", "-DGLS_TRANSPORT_IC", "-s", "tb", "-o", str(sim),
                     str(GLS / "prims.v"), str(CELLS / "sim/bd_env.v"), str(work / "netlist_baked.v"),
                     str(work / f"tb_{kind}.v")], work / f"compile_{kind}.log")
        if rc:
            ok = False
            lines.append("SOAK %s FAIL: compile, see %s" % (kind, work / f"compile_{kind}.log"))
            continue
        _, out = run(["vvp", str(sim)], work / f"sim_{kind}.log", cwd=work, timeout=FB.GLS_TIMEOUT)
        sim.unlink()
        try:
            lat = FB.kernel_metrics(out)
            lines.append("SOAK %s PASS lat=%s" % (kind, ",".join(map(str, lat))))
        except RuntimeError as e:
            ok = False
            bad = [l for l in out.splitlines() if re.search(r"FAIL|FATAL|MISMATCH|ERROR|[Tt]imeout|got|expected", l)][:3]
            lines.append("SOAK %s FAIL: %s %s" % (kind, e, " | ".join(bad)))
    verdict(ok, lines)


if __name__ == "__main__":
    main()
