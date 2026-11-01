# B-hprim: H_PRIM in window form (shard B, THE goal, 2026-11-01)

## Problem, plainly
THE goal's H_PRIM says each primitive behaves as its Core digital model, with the
delay semantics that is pessimistic for what is proved (or all three of transport,
inertial, involution). Core's primitive files state timing as fixed-delay per-pin
transport. A proof about the bitstream needs ONE relation per primitive output that
every admissible behaviour satisfies.

## The relation
`Formal.Cells.HPrimWin.WinH f pin lo hi y`: at instant τ, if each pin i is abstracted
by the Kleene value v i over its whole window [τ - hi i, τ - lo i], then y τ ⊒ f v.
f = the primitive's Kleene function (LUT mux tree `Lut.keval` / `Lut62` O5,O6; `mux2`
for MUXF7/F8; `Carry.kout` for CARRY4). A routed wire/pip is the 1-pin case f = id.

## What is proved (HPrimWin.lean, Core only, checked)
- `win_of_varTransport`: transport whose per-pin delay may change at every instant,
  inside the band, implies WinH (monotone f). `win_of_timed` / `win_of_mux`-style
  corollary: Core's fixed-delay `Timed.H` with delays in band implies WinH.
- `win_inertial` / `win_of_sampled`: any behaviour whose output at each instant is f
  of pin values read somewhere inside the windows (pulse swallowing, shrinking,
  jitter) implies WinH.
- `win_widen`: WinH on a band implies WinH on any wider band (guard g only widens).
- `win_forced`, `win_settles`: steady pins force the output (liveness half).
- `win_sic`: single-input change, no glitch when f with that pin X is defined.
- `buf_win`, `buf_not_fixed`: a buffer behaviour in WinH that no fixed-delay transport
  model has (WinH is strictly weaker than Core's Timed.H).

## Involution (HPrimInv.lean, needs Mathlib; CHECKED 2026-11-01)
Done for (a); (b) only with input separation (inv_sep_win, from Core's trace_transfer_sep).
Original plan: (a) concrete counterexample on Core's `ratPair` (δ∞ = 2, δmin = 1): band [3/2, 2],
input pulse [0, 3/2): output high on [2, 17/6), and at τ = 29/10 the input is steady 1
on its window [0.9, 1.4] while the output is 0. So WinH does NOT cover involution
channels whose δmin is below the band's lower end. (b) positive: δmin ≥ lo and δ∞ ≤ hi
implies WinH (every surviving output transition of input n lies in (t n + δmin, t n + δ∞],
and a cancelling pair cannot straddle a steady window).

## Not covered / open
- FDRE/FDSE: Core `SeqFlop` relation carries H_FF_RESOLVE (bounded resolution of a
  disturbed flop). That is not one of THE goal's five hypotheses. gcd_hw's bitstream
  contains 326 flops (306 FDRE, 20 FDSE, decoded route 2) and gcd_hw.v has a ring-
  oscillator clock and two-flop synchronizers (gcd_bench.v sync_i_ack/sync_o_req);
  any flop that samples an asynchronous signal can be disturbed. Either the theorem's
  boundary excludes those flops (they are harness, under H_ENV), or H_ARB(T) is read to
  cover synchronizer flops, or a sixth hypothesis is needed. Decision is shard A's
  (Spec.lean); recorded for them.
- The dispatch from the decoded instance kinds (lut6_2, muxf7, muxf8, carry4, fdre, fdse
  in every gcd_hw route) to these relations with XrayData arcs is the next file
  (HPrimNet), once A's Spec.lean fixes the net/pin waveform types.
