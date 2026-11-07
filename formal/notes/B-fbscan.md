# B-fbscan: storage-node margins on the decoded target (simulation, untrusted; 2026-11-01)

fb_switch (SpecFb) needs each flipping forcing episode of a feedback LUT to outlast its feedback loop.
tools-B/target/fbscan.py over the 16 gcd_rig.v vector baseline dumps (sequential env, corner 0.5, mid-window,
episodes after reset release). Weakest nodes (minimum over vectors of episode / simulated loop delay):

```
SLICE_X2Y18.DLUT.O6 ratio 1.72 episode 1143 ps, sim loop 665 ps, loop SLOW_MAX 1064 ps
SLICE_X0Y18.CLUT.O6 ratio 2.76 episode 1376 ps, sim loop 499 ps, loop SLOW_MAX 783 ps
SLICE_X42Y82.ALUT.O6 ratio 3.16 episode 1923 ps, sim loop 608 ps, loop SLOW_MAX 964 ps
SLICE_X6Y99.CLUT.O6 ratio 3.21 episode 1554 ps, sim loop 484 ps, loop SLOW_MAX 770 ps
SLICE_X38Y78.ALUT.O6 ratio 3.68 episode 2237 ps, sim loop 608 ps, loop SLOW_MAX 964 ps
SLICE_X2Y44.ALUT.O6 ratio 3.94 episode 2802 ps, sim loop 711 ps, loop SLOW_MAX 1135 ps
SLICE_X42Y82.CLUT.O6 ratio 4.07 episode 1427 ps, sim loop 351 ps, loop SLOW_MAX 562 ps
SLICE_X36Y37.ALUT.O6 ratio 4.18 episode 2523 ps, sim loop 604 ps, loop SLOW_MAX 959 ps
```

Adversarial runs on the weakest node: see JOURNAL-B (tools-B/target/fbadv.py).
