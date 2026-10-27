# C probe 9c: the gate-level Muller chain (`bd_pipe` control) for ALL n

(Status: in progress. Part 1, untimed iso + rt for all n, is DONE and checks in Wip;
part 2, the timed corollary for all n, is being written.)

## Verdict (part 1)

**Works.** A hand invariant local to two adjacent positions of the chain is
inductive for every n, and it gives hazard-freedom, the pair rules (four-phase
protocol on every link) and token order for every n >= 1, both with isochronic
feedback and under H_FB_BEFORE_INPUT (rt). The closure check is a finite check
on 3- and 4-position windows, done once by `decide +kernel` (about 10 s,
1.4 GB), plus a gluing lemma proved by hand for every n.

## The invariant

Positions: 0 = sentinel (value 48), 1 = source (16 + src), k+2 = stage k (the
4 bits c, b, w, f as a number < 16), n+2 = sink (32 + snk), n+3 = sentinel.
`Inv m n s`: every adjacent pair of positions is in a fixed table `adj m`
(13 entries for iso, 21 for rt, the same for every n and every stage).
The table is the set of adjacent pairs seen in the reachable states of n = 5
(Python BFS). Python also shows: for n = 1..6, the set of states satisfying
`Inv` is EXACTLY the reachable set (iso 18, 72, 288, 1152, 4608, 18432; rt 26,
160, 986, 6076, 37442, 230728). So the reachable set of the chain is
"pairwise definable". (Exactness is a Python observation, not proved in Lean;
Lean proves only reachable => Inv, which is all the theorems need.)
