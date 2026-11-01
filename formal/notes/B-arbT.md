# B-arbT: the held bd_arbiter under H_ARB(T) (shard B, 2026-11-01)

File: `formal/lean/Formal/Cells/ArbT.lean` (Core only, checked, standard axioms).

## Problem, plainly
THE goal allows one assumption about arbiters, H_ARB(T): each arbiter cell's internal race
resolves within T ps. Everything else about the arbiter must be derived from the gate model
(Spec v1: Boolean, per-pin read times in the bands). Is the arbiter then safe, and how does
T enter?

## Semantics
`RGate k init pins lo hi t0 y`: y t = INIT[addr(pin i read at f i t)] with every read delay in
[lo i, hi i], from t0 on. Same as Spec v1's GateOK minus the monotonicity of f, so positive
results transfer to GateOK. Real INITs of bd_arbiter (ustate q/R0, ugrant g1/g2, ua1/ua2 =
bd_c2), checked against their equations by decide.

## Proved
- `q_stays`: q keeps a settled value b while every pin-read combination confirms b
  (`confirm_freeze`: A0 high; `confirm_tie`: both requests high). No H_ARB needed.
- `grant_excl`: q constant on the grant gates' read windows => not both grants.
- `ack_stays_low`, `one_ack`: q settled W before A0 rises => the losing client's ack does not
  rise during that server transaction, whatever A0 does.
- `double_ack` (counterexample): all six gates hold (unit delays, q feedback band [2,3]),
  H_ARB(T) in B's strong form (ArbOK2: r1, r2, rst, A0 constant on [t1,t2] => q constant on
  [t1+T, t2]) holds for every T >= 7; near-tie (r1 at 10, r2 at 11); q oscillates (a runt
  circulating in the feedback loop, the model's metastability) until 20; server raises A0 at
  18 (R0 rose at 12, stays high: one transaction); A1 rises at 19 and A2 at 20.
  Negative control: moving the resolution read (t = 21 -> 19) breaks the kernel check.

## What it means
H_ARB(T) does not make the arbiter safe by itself. Safety needs q settled before A0 rises
(plus the grant and ua read windows, W): with H_ARB(T) that is the timing obligation
"from the last edge at ustate's pins to A0's rise at ua >= T + W", a path through the
server/downstream that the checker must generate and prove from the bands. So the largest
T for which THE theorem can hold is bounded by the shortest such path in the target.

## Not covered
Full cell contract (four-phase on all three channels, liveness, chaining phases); route
arcs between cells (pins = nodes here); the obligation's generation on the target netlist.
