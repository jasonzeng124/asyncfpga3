# B-specfb: feedback LUTs under the frozen Spec (shard B, 2026-11-01)

File: `formal/lean/Formal/Cells/SpecFb.lean` (over `Formal.Target.Spec`, check.sh OK).

Problem, plainly: every storage node of the target (C-element, latch, arbiter q) is a LUT
reading its own output. THE goal gives a resolution assumption only to arbiters. What does
the Spec's GateOK alone guarantee for such a node?

Proved (any gate, any p, corner; caller supplies Nat bounds implied by Adm per pin):
- fb_stays: confirmed value stays (pins + feedback = b give b on every visible combination).
- fb_forced: forced value appears (every visible combination gives c, whatever the feedback).
- fb_switch: forced on [s, e] with e + 1 >= s + hi_fb, then confirmed: clean switch to c.
- fb_runt_oscillates: bd_c2 (0xE8 on a, b, q), arcs 1/1/3 ps exact, a = 1, b high 1 ps:
  forced for 1 ps < 3 ps, and GateOK admits a behaviour that oscillates for ever.

Meaning: the proof must derive, per storage node of the target, that every forcing episode
at its pins lasts >= the feedback arc's upper bound (or otherwise excludes circulating runts).
That is an obligation for the generic checker (shard C), generated per node from the bands.
H_ARB(T) covers only arbiter state nodes; every C-element is on its own.
