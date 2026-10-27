# C-12a: C-element and arbiter checks in a SAT/SMT model checker

Status: IN PROGRESS (notes kept current as work proceeds).

Tools installed (pip, python3.13): z3-solver 5.3.2 (BMC, k-induction, Spacer/IC3
via CHC), cvc5 1.4.2 (python), python-sat 1.9.dev17. apt: nusmv / yices2 not
in the archive; cvc5/boolector are (not needed). yosys-smtbmc exists in the
openXC7 toolchain but has no delay model for combinational loops (not used).

## Progress log (partial results; the summary at the top is written last)

03:50 Engine (`tsmc.py`: BMC, k-induction with simple-path, Spacer) and cell
library (`cells.py`: real-INIT LUTs binary/Kleene, channels win/fifo/inert/kwin)
work. C-element: min pulse width W = Dmax = dl_hi + dw_hi exactly, for win and
fifo channels, every delay set tried (agrees with shard B, CElemTiming.lean);
inertial channels need only Dmax - dl_lo + 1. Bare arbcell, tb semantics (route
lumped into the inertial LUT arc, fixed max arcs, 4 ps ticks): grant overlap
for route < 16 ps, none to depth 110 at route = 16 ps: the 16 ps margin of the
bd_arb.v header, reproduced exactly.
