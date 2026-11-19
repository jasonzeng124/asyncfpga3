# A: the "join extension" step (DONE 2026-11-19 evening; see the status block at the end) -- what fuse_check needs to prove BDC_RING_FUSE without the C

Shard A, 2026-11-19. Context: FOR-RESEARCH A26. Research's BDC_RING_FUSE merges a loop's update `u = f(x)` and test
`c = g(f(x), n)` into one cell whose single join waits for x AND n. After the existing steps (multi-input ForkComm on
the packed cell + absorb + an unpack identity), the fused graph differs from the default one in ONE place:

  default:  comp [a]    u F          (a: a copy of x)
  fused:    comp [a, b] u F'         (F' = F, ignoring input 1; b: an extra copy of n from n's fork)

Why it holds in research's shape (`_ring_merge`: x' = f(x); c = test(x'); steer(c, x')): every reader of u is a
`branch` whose condition is a fork copy of c, and c's producer reads n's other copy b2. So the k-th u token is consumed
only together with the k-th c token, which already needed the k-th n token. Waiting for it at u's producer changes no
consumption order.

Statement to prove (Lean, any graph): rs holds `fork n (b2 :: rest)`, `comp [a] u F`, `comp [a2, b2] c G`; every reader of
u (through forks of u) is a branch whose condition is (through forks of) c; nothing else writes b2, c, u or their
copies. rs' = rs with `fork n (b :: b2 :: rest)` and `comp [a, b] u F'`. Then complete runs correspond, with the same
store outside {a, b, u and its copies}.

Relation (as in IncCmp2): L = the x-values that rs has already turned into u and rs' has not; rs' a = L ++ rs a; every
u copy in rs = (rs' copy) ++ map F L; rs' b holds exactly the n-tokens of iterations whose u is not yet produced.
Needed invariant: #(branch firings on each u copy) <= #(c tokens produced) <= #(n-fork firings). The catch-up step:
when rs fires a branch on a u copy that rs' lacks, rs' first fires `comp [a, b]`; b is non-empty by the invariant.
Terminal: rs' may keep a tokens on a (their rs counterparts sit unconsumed on u copies): private channels only.

Estimate: one day (the counting invariant across forks of c is the bulk). Payoff: fuse_check proves BDC_RING_FUSE on
all 26 importable kernels without C sources (today: 6 kernels via autoproof).

## Status (2026-11-19 21:10 UTC)
* Done, all Lean-checked with standard axioms: `Steps/JoinExt.lean` + `JoinExtSim.lean` (je_forward / je_backward,
  store-only counting invariant, no ghost history), `Steps/ForkComm2.lean` (two-input ForkComm), `Steps/ScriptRF.lean`
  (StepRF: forkcomm2, unpack with k-part slice rules, unjoin, permute, forkmerge; runScriptRF_sound).
* fuse_check.py proves BDC_RING_FUSE per kernel on 18 of 26 importable kernels (ringfuse_census.txt), gcd included.
* Open, in order of payoff: (1) k-input ForkComm and a k-input join extension (iterative_division, iterative_sqrt,
  nest3: cells with 3+ inputs, some dead after BDC_CONST_DATA); (2) sqrtsub: the unfused test reads a two-input
  update's result (planner: forkcomm2 on the unfused side + dedupe across a fork tree via forkmerge).
