# gcd_ps: what H_ENV requires of the AXI register slave (shard A, 2026-11-01)

Owner decision 1: "The boundary of the theorem is the kernel's handshake ports inside gcd_ps. The AXI register slave
is the environment: state what H_ENV then requires of it, including how STATUS inputs cross into the PS clock (a
missing synchronizer there is a finding, not an assumption)."

Source read: `cells/hw/gcd_ps.v` at research bfa659b4 (the target's build). Boundary nodes: decoded net eee97ec8,
`tools-A/target/out/boundary_e6bb4aec.json` (`boundary_ps.py`). This is a reading of the source, not yet a check of
the decoded bits (the decoded environment logic is in the netlist and can be checked the same way later).

## The boundary nodes and what drives them

| Spec field | node | driven by (gcd_ps.v) |
|---|---|---|
| `rst` | SLICE_X2Y29.DQ | `ctrl_rst`, an aclk flop, powers up 1, cleared by a host CTRL write |
| `a.req = b.req = start.req` | SLICE_X3Y30.C5Q | `req_core`: set by a CTRL write (aclk), cleared ASYNCHRONOUSLY by `i_ack_pl` (the bd_fork's joined acknowledge); bd_fork broadcasts it, so the three requests are one node |
| `a.data`, `b.data` | 32 + 32 distinct nodes | `a_data_reg`, `b_data_reg`: aclk flops written by the host |
| `out0.ack` | SLICE_X4Y34.A6 | `ctrl_o_ack AND o_req_pl`, a LUT |
| `pend.ack` | SLICE_X2Y21.B6 | `bd_delay #(2)` of `p_end_req` (a LUT chain: the environment's sink) |
| kernel outputs `a.ack`, `b.ack`, `start.ack`, `out0.req`, `out0.data`, `pend.req` | | the kernel `bridge_i.udut` |

## STATUS into the PS clock

`STATUS.i_ack` (from `i_ack_host = ctrl_i_req & ~req_core`, which moves asynchronously when `req_core` is cleared)
and `STATUS.o_req` (from the kernel's `o_req_pl`) each pass a two-flop synchronizer (`sync_i_ack`, `sync_o_req`)
before the AXI read mux. `O_DATA` is sampled every aclk into `o_data_capture` without a synchronizer, and the host
reads it only after `o_req` has passed both stages; the kernel's data are bundled before its request, so they are
stable by then and the capture of that cycle is clean. **No missing synchronizer found.**

## Spec.Env / SeqEnv, field by field

| obligation | met by | kind |
|---|---|---|
| `rst` high on [0, R), low after | `ctrl_rst` powers up 1; the host clears it once and never sets it again | host |
| `va k, vb k < 2^31` | the registers are 32 bits wide; the host writes only operands below 2^31 (research's vectors) | host |
| input request low on [0, R] | `req_core` powers up 0; the host sets `i_req` only after clearing `rst` | host |
| request falls only with its acknowledge high | `req_core` is cleared by the JOINED acknowledge, which is high only when all three channel acks are high | construction |
| request rises only with its acknowledge low | the host's CTRL write for pair k+1 must come after the kernel's three input acks fell for pair k; the host cannot see them (STATUS.i_ack is the sticky host view), so this holds only because they fall within ns of the request's fall and the host acts ms later | **host timing + circuit** |
| data held from `su` before the request rise until the acknowledge falls (broad rule) | data are written before the CTRL write (at least one aclk earlier: `su` up to 10 ns); the next pair's writes come after the output handshake, by when the input acks fell (as above) | host order + timing |
| request live | the host sets it for each offered pair; it falls by the asynchronous clear | host + construction |
| `out0.ack` low on [0, R]; rises only with `out0.req` high; falls only with `out0.req` low | `ctrl_o_ack` powers up 0; the AND gate cannot rise without `o_req`, and falls with it | construction (the AND passes any `o_req` glitch to the kernel as an ack pulse: a circuit property, `o_req` clean) |
| `out0.ack` rises no earlier than `Δo` after `out0.req` | the host sees `o_req` through two flops (20 ns at 100 MHz) and then polls; Δo is the host's latency | host timing |
| `pend.ack` follows `pend.req` | bd_delay #(2): a delay line, ack = delayed req | construction (a LUT chain on the environment side) |
| `pend.ack` rises no earlier than `Δo` after `pend.req` | only as long as the bd_delay's delay: **Δo in the theorem must be at most that delay** (hundreds of ps), not the host's latency | construction, bounds Δo |
| SeqEnv: the next request only after the output handshake completed | the host's sequence (poll `o_req` low, then clear `o_ack`, then write the next pair) | host |

## Findings

1. No missing synchronizer on STATUS.
2. The release of `req_core`'s asynchronous clear (when the joined ack falls) is asynchronous to aclk. A CTRL write
   that SETS `i_req` in the same aclk cycle would be a recovery/removal violation. The host sequence rules it out only
   by timing (ms polling against ns handshakes): an assumption on the host, not a property of the circuit.
3. "Request rises only with its acknowledge low" is met only because the kernel's input acknowledges fall long before
   the host's next write. Spec's H_ENV states it as the environment's obligation; for gcd_ps it is a joint property of
   the host's timing and the kernel's own ack timing (which the theorem itself would have to bound).
4. Δo is bounded by the `pend` sink's delay line, not by the host.

Not shown: any of this on the decoded bits (the environment logic is decoded too; it can be checked the same way as
the kernel later), the PS7 side (AXI timing, the SLCR bring-up), the board.
