# C probe 8g: the gate-level Muller chain under bounded delays

Status: IN PROGRESS (skeleton written first; see sections below as they fill).

Plan: (1) timed semantics = every node of 8c's chain (src, snk, c_k, b_k,
w_k, f_k) an inertial channel [lo_i, hi_i] after its real LUT function
(free feedback wire); derive H_FB_BEFORE_INPUT from per-guard inequalities
hi(f_k) < sum of lo over the neighbour loop; bridge: every timed trace is an
rt run. (2) converse: concrete inertial trace with 11b-shaped delays that
glitches. (3) n <= 3 (8c's rt range), generic-n conditional on a checker.
