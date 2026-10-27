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

## Arbiter thresholds (item 3), DONE -- interim notes

Dense time, 0.1 ps resolution (u=10), nominal arcs, zero routing except the
swept wire, srv window [s_lo, s_lo+20], clients fall [4,24] ps after A.
Every check < 0.3 s inertial (<= 300 zones), 2-4 s transport (<= 3.5 k zones,
63 MB).
- HELD ack exclusion (amutex): inertial holds iff s_lo > 56 ps (strict);
  transport (no q runt) holds iff s_lo >= 56 ps (closed); tx_nr same in
  transport. 12b's "~60 ps" (15 ticks) is 56 ps exactly, i.e. the 14-tick
  boundary 12b saw at "<= 14 fails".
- A0 fork (HELD): holds iff wa < 112 + c_lo ps, c_lo = client's minimum
  r-fall response (checked c_lo = 0, 4, 20, 40: thresholds 112, 116, 132, 152).
  So 12b's 116 ps = O6 rise (A2, 56) + c_lo (4) + O6 rise (q, 56), and the
  dependence on c_lo is now explicit. Same in transport (_nr).
- UNHELD grant overlap: mutex iff wq_g > 16 ps (strict). UNHELD ho/tx iff
  s_lo >= 60 ps fails (59.9 holds).
- NEW: HELD arbiter, q->ugrant route wq_g: inertial mutex holds iff
  wq_g < 56 ps; transport (pure delay) mutex fails for EVERY wq_g > 0 (0.1 ps
  fails) even with no runt on q. Mechanism (witness): r1 alone, q rises, r2
  rises after q has committed but before the new q reaches ugrant.I2; ugrant
  sees r2 & ~qg(old) and g2 gets an excitation of width (wq_g - (t_r2 -
  t_q)); g1 then rises 52 ps after qg arrives while g2 falls only 124 ps
  after it. The hold does not cover this (A0 is low). 12b never saw it because
  its HELD rows had wq_g <= 32 ps inertial, and wq_g = 0 in transport except
  the spread row that OOMed.
