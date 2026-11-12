# Shard A: chaining per-pair episodes into THE statement (S6), 2026-11-10

**What is proved (Lean, check.sh OK).** `Formal.Target.PlanRPS.the_of_stepR_all`: for every g > 0, 0 ≤ κ < 1 and reset
R ≥ ⌈(1+κ)g⌉·(15,600 + 87·3,881) + 1 ps, THE statement `NetCorrectSeq net boundary arbs p T R su Δo` follows from
`StepHypR p T R su Δo` alone: in every behaviour meeting THE hypotheses (Behaves, ArbOK T, Env, SeqEnv), from the
read island `IslR p x t` at a rising pair request `t ≥ R`, there is one complete pair episode
`Assembly.StepCore x boundary Δo (IslR p x) t t2 t0` (no new request in (t, t2); a/b/start acks and out0/end
requests move per four-phase; out0 rises once, at t0, and carries gcd of the operands at t + 1; boundary low at t2;
`IslR` at t2). Base (reset) and quiet steps are proved (`isl_islR`, `islR_next`, C's island data).

**`IslR p x t`** (generalised 08:2x): for some set S of logic nodes containing a.ack, b.ack, start.ack, out0.req
(C's 414-node idle island `CViewPS.memI` at reset end), every member w has a read-map witness F of its routed
gate relation and a pin set P that forces its LUT to 0 whatever the other pins read; each P-pin reads an island member
S-member or env node (shared request 186985, end.ack 104477) through a route of min delay ≥ 1 ps, and that source is low on
[F j t, t] (the read at t already sees it low, and it has stayed low since).

**Why not a quiet window (the finding that matters for the S4 certificate).** Under `SeqEnv` the env may lower
out0.ack 1 ps after out0.req falls and raise the next request at once (Env puts no lower bound on a fall and no
gap before a request). Simulated (tools-A/target/simadv_hold.py, `--nextreq seq --dfall 1`, corner 0.5, κ = 0, pairs
(12,18), (17,5), (8,12)): at both re-requests out0.req changed 4 ps earlier and 8 more island members within 3.9 ns
(a falling chain 160932, 160916, 160996, 19495, 20614, 21015, 20999, 20983); `IslR` holds there
(tools-A/target/islr_check.py), the M-window island does not.
**Consequence for C's TimedOccX/AO route:** `TBehX.quiet` (every exact node constant on [t0 - H, t0]) cannot hold at
the start of episode k ≥ 2 against such an env, for any H > 4 ps. A per-episode certificate therefore needs either
1. a start condition weaker than `quiet`: e.g. the exact nodes are, at t0, *forced* by reads that see stable sources
   (IslR's form), so they cannot move before an event of the certificate causes them to; or
2. the previous episode's tail (out0.req's fall and its 8-node falling chain) as the first events of the next
   episode's certificate (the certificate starts at the previous episode's last quiet point); or
3. one certificate for the whole run from reset (all n pairs), which C's all-pairs plan does not cover yet
   ("Not covered: ... reset/quiet start"; one episode only).
Option 1 composes directly with `StepHypR`. Episode 1 (after reset) is unaffected: C's reset island gives `quiet`.

**Addendum (08:1x): what is still moving at a fastest re-request (simulation, (12,18) then (17,5), corner 0.5, κ = 0).**
In the 5 ns before the second request, 27 logic nodes changed: the 9 island members above, out0.ack (env), and 17
non-island control nodes reacting to out0.ack's fall, two of them 1-2 ps before the request (154630 SLICE_X4Y31.C6,
160973 SLICE_X5Y31.D6), then 154646, 154614, 154737 (X4Y31.D6, X4Y31.B6, X4Y32.D6) and a 10-LUT chain over 4.8 ns
(35740/35723/35707 X15Y77.C/B/A6, 31576/31560/31544 X14Y77.D/C/B6, 70070/70054 X21Y81.B/A6, 65714/65698/65682/65666
X20Y81.D/C/B/A6). Over 50 ns, 164 island members and ~580 other logic nodes changed. So for a per-episode
certificate with `TBehX.quiet` at H ≈ 5 ns, these 26 non-env nodes must be data-claimed (dat = true, "low/stable
from its last change") or the start weakened; IslR covers only the island. Both races (this chain and the island
tail made slow, everything else fast, κ = 0.3/0.35, fastest SeqEnv, 3 pairs) were correct in simulation.
