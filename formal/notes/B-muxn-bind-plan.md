# Plan: binding `bdc_muxn` into the driver-bound network (theorem done, witness not)

2026-10-31, shard B. With `FiniteNetBoundT` (170 of 175 links bound on both sides), the 5
unbound link sides are the source's request side (cannot be gate-modelled on a terminating run:
`FiniteNetSrc.chW_src_unwired`) and 4 ACKNOWLEDGE sides that end at a `muxn` (by #eval on
`ackSrcT`/`FiniteNetBoundMCensus.ackEnd`). This note is the design for that last class.

## The cells (bdc/emit.py `emit_muxn`, generated per kernel, not in cells/rtl)

| cell | function | pins | drives |
|---|---|---|---|
| `sel[k]` | `ctl_req & (s == k)`: **yosys-mapped logic**, no fixed INIT in the emitter | ctl.req, the index bits | `uj_k`'s b pin |
| `uj_k` (`bd_c2`) | `C(in_k_req, sel_k)` | in_k.req, sel_k | j_k |
| `uor` | `LUT1 2'h2` of `|j` (the OR itself is yosys logic) | j_0..j_{n-1} | the delay chain |
| `request_delay("|j")` | `compute.request_delay`: FASTFALL stages | the OR | z.req |
| `ua_k` (`bd_c2`) | `C(j_k, z_ack)`, a mux acknowledge | j_k, z.ack | in_k.ack |
| `ctl_ack` | a wire from z.ack | | ctl.ack |

gcd_hw has ONE muxn (op 163, 3 inputs). The 4 unbound sides (Python, bsim4's ackSrc
re-implementation) are its three input acknowledges (`ackSrc in_k = ua_k`) and its CONTROL
acknowledge, which is a wire from z.ack; z (`g250.0`) feeds a SINK, so binding the control
side also needs the sink's acknowledge modelled (C's sim: `ack = req`). `reqSrc z` = the last
delay stage.

## What exists and what is missing

Exists (`AssumeGuaranteeMuxNFin`): `FDecSpec` (a decode LUT3 of ctl_req and two index bits,
truncated), `FMuxASpec` (= `ua_k`, already used for `bd_mux` and the arbiter's `ua1`/`ua2`, with
`BWit2Lib.maB` as its checker), `FAndSpec` (a FASTFALL stage, REAL LUT2 `4'h8`), `FBufSpec`.
`FMuxJSpec` is `bd_mux`'s join with the decode folded in; `bdc_muxn`'s join is a plain `bd_c2`
whose b pin is the decode node, so it is `FCelSpec GC2` with one internal pin (checker
`celB`), and the decode is its own cell.

Missing:
1. **The decode's real LUT.** The emitter leaves `ctl_req & (s == k)` to yosys, so the
   netlist's INIT is whatever yosys chose; read it from C's generated netlist
   (`Formal.Gen.Cells`, if C generated gcd_hw's muxn) or from the synthesized gcd_hw
   netlist, never from the emitter's comment. FDecSpec assumes a LUT3; check the index width
   of gcd_hw's muxn (3 inputs, so 2 index bits plus ctl_req: a LUT3 fits).
2. The 3-input request OR in truncated form (`FiniteOrN` exists; check that it is the
   truncated `FCellOK` form with a Bool checker) and `compute.request_delay`'s exact stage
   list for the muxn's DELAY parameter.
3. Bool checkers for FDecSpec and FAndSpec (only `combB`/`celB`/`maB`/`bufB`/`orB` exist).
4. A simulator model (bsim5) of the generated cells, so that C's checker still passes and
   the pins are wire copies of their drivers (as bsim2..4).
5. The usual layer: `FiniteNetBoundN` (`ackSrcN`, census 174/175, `toOKBT`), then a BWit5 chain
   whose NChk imports BWit4NChk (memory: each NChk peaks ~11 GB).

The request side of the muxn's z needs no new binding for the census (no unbound request
side ends there), but its cells must still be specified, since `ua_k` reads `z_ack` and `j_k`.

## Status (2026-10-31, later)

Theorem level done: `FiniteNetBoundN` (decode `FDecSpec`, join `FCelSpec GC2`, acknowledge
`FMuxASpec` per input; the input acknowledges bound; 173 of 175). Not done: items 1-4 above
(the decode's INIT from a netlist, the OR and delay chain, Bool checkers for FDecSpec, a
simulator model) and so no witness; the control acknowledge (via the sink) stays unbound.
