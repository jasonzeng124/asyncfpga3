# C-12c: zone-based timed-automata checking (TChecker)

Status: IN PROGRESS (notes kept current as work proceeds).

## Tool acquisition (2026-10-27)

- `git clone --depth 1 https://github.com/ticktac-project/tchecker` into the
  scratchpad (`$S/ext/tchecker`): **works** (the clone was the route 12b could
  not try). Commit d711ace9ff754d8d952f5d491a31591115300c7f (2025-12-09).
- apt: flex 2.6.4, libboost-all-dev 1.83.0, catch2 3.4.0 installed; bison
  3.8.2, cmake 3.28.3, g++ (Ubuntu 24.04) already present.
- Build: cmake Release, `make -j2 install` into
  `formal/tools/zone/build/tchecker/` (gitignored `build/`).
- Build time 268 s (`make -j2`, LTO); the install step fails only at the
  doxygen `html` docs, after all four binaries (`tck-reach`, `tck-liveness`,
  `tck-simulate`, `tck-syntax`) and `libtchecker.a` are installed. Peak RSS of
  the compile was not measured (no /usr/bin/time); -j2 stayed well inside the
  cgroup.

## C-element result (item 1), DONE

`celem.py thr`: 40 (dl, dw) rows x ~30 e_lo values x 2 properties, 61 s total,
<= 258 zones per check. Units 1/10 of a 12b tick (re-checked at 1/100: same
thresholds, identical zone counts -- zones do not grow with the constant
scale, digital clocks do). Dense-time exact thresholds:

| channel | spec (O moves only when a=b!=O) | hazard-free |
|---|---|---|
| inertial | **e_lo > dw_hi - dl_lo** (strict) | **e_lo > dw_hi** (strict) |
| transport (FIFO) | **e_lo >= dw_hi** (closed) | n/a (no swallowing) |

So 12b's "e_lo >= dw_hi, independent of the LUT delay" is exact only for
transport. For inertial, the spec bound depends on dl_lo: 12b's sweep always
had dl_lo = 1 tick, which is exactly the tick of the digital grid, so the
dl_lo term was hidden by the tie rule. The safe (hazard-free / transport)
bound is dw_hi: strict for inertial (at equality a zero-width excitation is
swallowed = hz), closed for transport (zero-width reversal cancelled).
