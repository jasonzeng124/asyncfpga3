#!/usr/bin/env python3
"""SVF generator for the knapsack BSCANE2/USER1 JTAG harness ("Path C").

Emits an SVF file that drives the full 4-phase bundled-data handshake of
zynq/knapsack_jtag_top.v over the EBAZ4205's PL TAP USER1 instruction,
playable by openFPGALoader's SVF player (the build at
~/dev2/lib/jtag/openFPGALoader). Golden results are compared via SVF
TDO+MASK, so the PLAYER ITSELF fails if a result is wrong. It can also
emit the same scan sequence in a simple line format that
tests/tb_jtag_bridge.v plays in simulation -- one generator, two
backends, so sim and hardware literally share the vectors.

Chain encoding (EMPIRICALLY VERIFIED on the bench: 2026-07-20
zynq/svf/idcode_check.svf, refined 2026-07-21 with echo probes against
the live knapsack_jtag_top bitstream -- do NOT change without
re-benching):
  * the player rejects HIR/HDR/TIR/TDR, so the ARM DAP padding of the
    cascaded Zynq chain is inlined into every vector;
  * SIR 10 = (PL_INSTR6 << 4) | 0xF   (DAP BYPASS=0xF in the LOW 4 bits)
  * SDR 33 (W+1), and the two directions are NOT symmetric:
      - TDO (read):  the PL capture word is ALIGNED in the LOW 32 bits;
      - TDI (write): the PL DR receives the payload shifted RIGHT by 1,
        so the control word must be emitted at bits [W:1], i.e.
        TDI = word << WRITE_SHIFT with WRITE_SHIFT = 1.
    Measured 2026-07-21: writing 0xFF at frame [7:0] echoed back 0x7F;
    writing bit 11 landed in hold bit 10 (rst) and strict-checked clean
    (probe SVFs, deleted; this comment is the record). Explanation: the
    player auto-pads the detected chain (ARM DAP at index 0) with one
    bypass cycle AFTER the DR payload and 4 BYPASS bits AFTER the IR
    payload; the DAP's bypass flop between TDI and the PL TAP delays
    the write path by one bit while the read path (PL nearest TDO) is
    direct. That asymmetry is also why SIR wants the instruction in the
    HIGH 6 bits while DR data reads back in the LOW 32.
7-series USER1 = 0x02, so every SIR here is (0x02<<4)|0xF = 0x02F.

DR chain layout -- MUST match zynq/knapsack_jtag_top.v exactly:
  write side (committed to the hold register on UPDATE):
    [7:0]  i_data (cap)   [8] i_req   [9] o_ack   [10] rst   [31:11] --
  read side (loaded into the shift register on CAPTURE):
    [10:0] echo of the current hold register
    [11]   i_ack (synchronized)      [12] o_req (synchronized)
    [15:13] constant TAG 3'b101 (scan-alignment / hookup proof)
    [31:16] o_data

Why "check status while committing new control in ONE scan" is safe:
in the IEEE 1149.1 DR path (Select-DR -> Capture-DR -> Shift-DR ->
Exit1-DR -> Update-DR) Capture-DR strictly precedes Update-DR, so the
TDO of a scan reports the state BEFORE that same scan's control commit.
E.g. one scan both checks i_ack=1 and drops i_req.

Why no polling: SVF has no loops. The core completes a call in
microseconds (~27 us at the measured ~478 ps/hop) while JTAG scans over
USB are milliseconds apart; a RUNTEST <T_RUN> TCK idle before each
status check is overwhelmingly sufficient (1000 TCK is >= 100 us even
at a 10 MHz TCK, and the USB turnaround adds ms on top).

Bundled-data ordering is guaranteed by scan SEQUENCING, not hardware
delay: cap is applied with i_req=0 in one scan, then i_req=1 with the
SAME data in a later scan, so data always leads the request by a full
scan (+ RUNTEST). Return-to-zero is completed explicitly every call
(drop i_req after i_ack, drop o_ack after o_req falls) -- holding a
level high is the historical v1 hardware deadlock, see CLAUDE.md.

usage:
  python3 zynq/svfgen_jtag.py                    # zynq/svf/knapsack_golden.svf
  python3 zynq/svfgen_jtag.py --no-check         # zynq/svf/knapsack_nocheck.svf
  python3 zynq/svfgen_jtag.py --sim build/knapsack_jtag/scans_golden.txt
  python3 zynq/svfgen_jtag.py --caps 0 5 31 -o /tmp/x.svf
"""

import argparse
import os
import sys

# ---- DR chain layout (single source of truth on the host side) --------
W = 32                       # PL USER1 DR width
SDR_LEN = W + 1              # + inlined DAP BYPASS bit (top)
# Write-side frame shift, measured on hardware (see header): TDI bit
# m+1 lands in hold bit m; TDO is aligned. Applied at EMIT time (both
# SVF and sim vectors), so pack/unpack stay an exact mirror of the RTL
# hold/capture layout. tests/tb_jtag_bridge.v's TAP model reproduces
# the same contract (DAP bypass flop + one player pad-after cycle).
WRITE_SHIFT = 1
DATA_W = 8
BIT_DATA = 0
BIT_IREQ = 8
BIT_OACK = 9
BIT_RST = 10
BIT_IACK = 11
BIT_OREQ = 12
BIT_TAG = 13
TAG_W = 3
TAG = 0b101
BIT_ODATA = 16
ODATA_W = 16

M_ECHO = ((1 << (BIT_RST + 1)) - 1)              # [10:0]
M_IACK = 1 << BIT_IACK
M_OREQ = 1 << BIT_OREQ
M_TAG = ((1 << TAG_W) - 1) << BIT_TAG
M_ODATA = ((1 << ODATA_W) - 1) << BIT_ODATA
V_TAG = TAG << BIT_TAG

IR_USER1 = 0x02
SIR_LEN = 10
SIR_VAL = (IR_USER1 << 4) | 0xF                  # + DAP BYPASS, low 4 bits

# examples/knapsack.c header golden table (independent Python brute force)
GOLDEN = [(0, 0), (1, 2), (3, 5), (5, 8), (10, 15), (15, 23),
          (17, 26), (20, 29), (25, 34), (28, 38), (31, 41)]


def pack_ctrl(rst, o_ack, i_req, i_data):
    """Control word driven into the hold register (write-side layout)."""
    assert rst in (0, 1) and o_ack in (0, 1) and i_req in (0, 1)
    assert 0 <= i_data < (1 << DATA_W)
    return ((rst << BIT_RST) | (o_ack << BIT_OACK) |
            (i_req << BIT_IREQ) | (i_data << BIT_DATA))


def unpack_capture(word):
    """Fields of a captured word (read-side layout)."""
    assert 0 <= word < (1 << W)
    return dict(
        i_data=(word >> BIT_DATA) & ((1 << DATA_W) - 1),
        i_req=(word >> BIT_IREQ) & 1,
        o_ack=(word >> BIT_OACK) & 1,
        rst=(word >> BIT_RST) & 1,
        i_ack=(word >> BIT_IACK) & 1,
        o_req=(word >> BIT_OREQ) & 1,
        tag=(word >> BIT_TAG) & ((1 << TAG_W) - 1),
        o_data=(word >> BIT_ODATA) & ((1 << ODATA_W) - 1),
    )


def _selftest():
    """pack/unpack must be exact mirrors of each other and of the RTL."""
    for rst in (0, 1):
        for oack in (0, 1):
            for ireq in (0, 1):
                for d in (0, 1, 0x55, 0xAA, 0xFF):
                    w = pack_ctrl(rst, oack, ireq, d)
                    u = unpack_capture(w)      # capture echoes hold in [10:0]
                    assert (u["rst"], u["o_ack"], u["i_req"],
                            u["i_data"]) == (rst, oack, ireq, d), (w, u)
                    assert u["i_ack"] == 0 and u["o_req"] == 0
                    assert u["tag"] == 0 and u["o_data"] == 0
    full = (V_TAG | M_IACK | M_OREQ | (0xBEEF << BIT_ODATA) |
            pack_ctrl(1, 1, 1, 0xFF))
    u = unpack_capture(full)
    assert u == dict(i_data=0xFF, i_req=1, o_ack=1, rst=1, i_ack=1,
                     o_req=1, tag=TAG, o_data=0xBEEF), u
    assert (M_ECHO | M_IACK | M_OREQ | M_TAG | M_ODATA) == (1 << W) - 1


# ---- abstract op list --------------------------------------------------
# ("NOTE", text) / ("RESET",) / ("SIR", val) / ("RUNTEST", n)
# ("SDR", wr32, exp32-or-None, mask32-or-None)

def build_ops(vectors, check, t_run, t_rst):
    ops = [("RESET",), ("SIR", SIR_VAL)]
    held = [pack_ctrl(1, 0, 0, 0)]       # hold register after config / TLR

    def sdr(wr, status, mask, note):
        exp = (V_TAG | (held[0] & M_ECHO) | status) if mask else None
        ops.append(("NOTE", note))
        ops.append(("SDR", wr, exp, mask))
        held[0] = wr & M_ECHO

    strict = (M_TAG | M_ECHO | M_IACK | M_OREQ) if check else None

    sdr(pack_ctrl(1, 0, 0, 0), 0, strict,
        "sanity: TAG + echo of the power-up hold (rst=1), core quiet")
    ops.append(("RUNTEST", t_rst))
    sdr(pack_ctrl(0, 0, 0, 0), 0, strict,
        "release rst (echo still shows rst=1: capture precedes update)")
    ops.append(("RUNTEST", t_rst))

    for cap, exp in vectors:
        ops.append(("NOTE", f"---- knapsack({cap}) : expect {exp} ----"))
        sdr(pack_ctrl(0, 0, 0, cap), 0, strict,
            f"apply cap={cap} with i_req=0 (data leads request)")
        ops.append(("RUNTEST", t_run))
        sdr(pack_ctrl(0, 0, 1, cap), 0, strict,
            "raise i_req (same data held)")
        ops.append(("RUNTEST", t_run))
        sdr(pack_ctrl(0, 0, 0, cap), M_IACK,
            (M_TAG | M_ECHO | M_IACK) if check else None,
            "check i_ack=1; drop i_req in the same scan (capture-before-"
            "update); o_req deliberately unchecked (may still be rising)")
        ops.append(("RUNTEST", t_run))
        dmask = ((M_TAG | M_ECHO | M_IACK | M_OREQ | M_ODATA) if check
                 else M_ODATA)
        sdr(pack_ctrl(0, 1, 0, cap),
            M_OREQ | (exp << BIT_ODATA), dmask,
            f"check i_ack=0, o_req=1, o_data=={exp}; raise o_ack")
        ops.append(("RUNTEST", t_run))
        sdr(pack_ctrl(0, 0, 0, 0), 0, strict,
            "check o_req=0 (RTZ done); drop o_ack")
        ops.append(("RUNTEST", t_run))
        sdr(pack_ctrl(0, 0, 0, 0), 0, strict,
            "clean idle: i_ack=0, o_req=0, hold echoed idle")

    ops.append(("RESET",))               # TLR re-asserts rst=1: core parked
    return ops


def _frame_wr(v):
    """Write-side 33-bit frame: the PL DR receives TDI >> 1 (DAP bypass
    flop on the write path), so emit the control word at bits [W:1]."""
    return (v << WRITE_SHIFT) & ((1 << SDR_LEN) - 1)


def _frame_rd(v):
    """Read-side 33-bit frame: PL capture word aligned in the low W
    bits; bit W (the DAP's captured 0) is never checked."""
    return v & ((1 << W) - 1)


def emit_svf(ops, path, header):
    ln = ["! " + h for h in header]
    ln += ["TRST OFF;", "ENDIR IDLE;", "ENDDR IDLE;"]
    for op in ops:
        if op[0] == "NOTE":
            ln.append("! " + op[1])
        elif op[0] == "RESET":
            ln.append("STATE RESET;")
            ln.append("STATE IDLE;")
        elif op[0] == "SIR":
            ln.append(f"SIR {SIR_LEN} TDI ({op[1]:03X});")
        elif op[0] == "RUNTEST":
            ln.append(f"RUNTEST {op[1]} TCK;")
        elif op[0] == "SDR":
            _, wr, exp, mask = op
            tdi = _frame_wr(wr)
            if mask is None:
                ln.append(f"SDR {SDR_LEN} TDI ({tdi:09X});")
            else:
                # MASK must ALWAYS accompany TDO with this player: an
                # omitted MASK defaults to all-ones (parse_hex default),
                # which would also compare the DAP pad bit.
                ln.append(f"SDR {SDR_LEN} TDI ({tdi:09X}) "
                          f"TDO ({_frame_rd(exp & mask):09X}) "
                          f"MASK ({_frame_rd(mask):09X});")
    with open(path, "w") as f:
        f.write("\n".join(ln) + "\n")


def emit_sim(ops, path, header):
    """tests/tb_jtag_bridge.v line format. All values are ON-THE-WIRE
    frames, identical to the SVF (TDI already carries WRITE_SHIFT; the
    TB's TAP model reproduces the player+chain behavior, so sim and
    hardware share the exact same vectors):
    R                       TAP reset (5x TMS=1) then idle
    I <3-hex>               10-bit SIR, chain-padded value
    D <9-hex> <9-hex> <9-hex>   33-bit SDR: TDI TDO MASK (MASK 0 = no check)
    W <n>                   RUNTEST: n TCK cycles in Run-Test/Idle
    E <n>                   trailer: expected number of D lines (anti-truncation)
    """
    ln = ["# " + h for h in header]
    nsdr = 0
    for op in ops:
        if op[0] == "NOTE":
            ln.append("# " + op[1])
        elif op[0] == "RESET":
            ln.append("R")
        elif op[0] == "SIR":
            ln.append(f"I {op[1]:03X}")
        elif op[0] == "RUNTEST":
            ln.append(f"W {op[1]}")
        elif op[0] == "SDR":
            _, wr, exp, mask = op
            nsdr += 1
            if mask is None:
                exp, mask = 0, 0
            ln.append(f"D {_frame_wr(wr):09X} {_frame_rd(exp & mask):09X} "
                      f"{_frame_rd(mask):09X}")
    ln.append(f"E {nsdr}")
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w") as f:
        f.write("\n".join(ln) + "\n")


def main():
    _selftest()
    zdir = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--caps", type=int, nargs="+", metavar="CAP",
                    help="capacities to run (default: the 11 golden ones)")
    ap.add_argument("--no-check", action="store_true",
                    help="lenient mode for debugging: TDO checks only on "
                         "o_data, nothing else compared")
    ap.add_argument("--runtest", type=int, default=1000, metavar="TCK",
                    help="idle TCK cycles between scans (default 1000)")
    ap.add_argument("--runtest-reset", type=int, default=2000, metavar="TCK",
                    help="idle TCK cycles around reset release (default 2000)")
    ap.add_argument("-o", "--out", help="SVF output path (default "
                    "zynq/svf/knapsack_golden.svf, or knapsack_nocheck.svf "
                    "with --no-check)")
    ap.add_argument("--sim", metavar="PATH",
                    help="also write the simulation scan-vector file for "
                         "tests/tb_jtag_bridge.v")
    a = ap.parse_args()

    if a.caps is None:
        vectors = GOLDEN
    else:
        gold = dict(GOLDEN)
        missing = [c for c in a.caps if c not in gold]
        if missing:
            sys.exit(f"no golden value for cap(s) {missing}; known: "
                     f"{sorted(gold)} (extend GOLDEN from examples/"
                     "knapsack.c or an interpreter run first)")
        vectors = [(c, gold[c]) for c in a.caps]

    check = not a.no_check
    ops = build_ops(vectors, check, a.runtest, a.runtest_reset)
    nsdr = sum(1 for op in ops if op[0] == "SDR")
    header = [
        "knapsack over BSCANE2/USER1 (zynq/knapsack_jtag_top.v), Path C",
        "generated by zynq/svfgen_jtag.py -- edit the generator, not this",
        f"vectors: {', '.join(f'{c}->{e}' for c, e in vectors)}",
        f"{nsdr} scans, {'STRICT' if check else 'o_data-only'} TDO checks",
        "chain frame: SIR 10=(instr<<4)|0xF; SDR 33, TDO aligned low 32,",
        "TDI shifted left 1 (DAP write-path delay; benched 2026-07-21)",
    ]

    out = a.out or os.path.join(
        zdir, "svf",
        "knapsack_golden.svf" if check else "knapsack_nocheck.svf")
    emit_svf(ops, out, header)
    print(f"wrote {out} ({nsdr} scans, {len(vectors)} vectors, "
          f"checks={'strict' if check else 'o_data only'})")
    if a.sim:
        emit_sim(ops, a.sim, header)
        print(f"wrote {a.sim} (sim scan-vector format)")


if __name__ == "__main__":
    main()
