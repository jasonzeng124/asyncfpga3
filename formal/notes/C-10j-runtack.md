# C-10j: does the grant-fork runt break the handshake? (H_RUNT_ACK)

Shard C, probe 10j, 2026-10-27.

Files (all mine):
- `formal/lean/Formal/Timing/RuntAck.lean`: the theory, the checker and the certificates.
- `formal/lean/Formal/Timing/RuntAckInst.lean`: generated. It holds 576 certificates, 288 ack
  verdicts, 304 index verdicts and one non-vacuity row, all decided by the kernel.
- `formal/tools/runtack/{extract,emit,summarize,rulea}.py` and `check.sh`. Outputs go to
  `formal/tools/runtack/build/`; `summary.md` there is the per-instance table.
- `Wip/C10j/` is empty. What is unproved is a named hypothesis, listed below, not an
  unfinished proof.

## Verdict

**Works.** The handshake is safe on all 36 routed gcd_hw `bd_arbiter` instances. This is
proved in the model, at all four consistent prjxray corners.
(Scope, per audit P5 row 3e2c968; aud2 wording 2026-10-29: the routes are gcd_hw seeds d, 2, 3, 4
built for C-10e, not the board bitstreams, and are not on disk; each row uses one consistent
corner, without the 0.772/1.155 band; the passes depend on the server latency (H_SRV) and, for
the index rows, on H_FF_DRAINED.)
- **Acknowledge.** There are 195 corner rows where the runt exists (W > 0, out of 288). On
  every one of them the runt has ended at ua_k's core before A0 can arrive there.
  - The worst margin is **+468 ps**: gcd_hw_d merge12.uarb1, client 1, FMIN. The runt ends at
    753 ps after q's edge; the certified minimum server path is 1057 ps.
  - The **largest server latency the race needs** to stay safe is 1771 ps. The shortest
    certified server path on any live row is 1057 ps.
  - So a server about 0.5 to 1.8 ns faster than the routed one, depending on the row, would
    break it. `demo_fast_server` shows that with an instantaneous server the worst row fails.
- **Index.** There are 198 runt rows for the index and data LUTs (`won = g2 | A2`, the z_data
  mux). The runt ends at their outputs at least **+2633 ps** before z_req can rise.
  - This uses the rise graph, under H_FF_DRAINED.
  - Without H_FF_DRAINED (allowing z_req to rise through the fast-fall taps), 64 of the 198 rows
    would fail. So that hypothesis carries real weight; it is rule F's obligation.
- **Lost transaction.** None. A2 stays low, so r2 stays up and client 2 is served after the
  handover.
- **link_arb s1..s4: not decidable on chip.** R0 and A0 go through pads, so the server is the
  board.
  - The board's round trip from R0 (ustate O5) to A0 at ua_k's pin must be at least
    **263 to 1441 ps**, depending on the copy and corner. The table is in `build/summary.md`.
  - An OBUF→pad→IBUF round trip is physically longer than that, but this probe does not prove
    it.
- **What breaks:** only the header's claim that the grant wires are exclusive (C-10i). The
  handshake survives, with margin, as long as the server is not faster than the "need" column.

## H_RUNT_ACK, precisely

This is the client-2 direction; client 1 is the mirror (q falls, r1 is late, the g1 runt is on
O5). The model:
- per-(pin, output) pure delays, as in C-10i / B's `ArbOverlapRace`;
- the real INITs: `stA`, `r0A`, `gr1`, `gr2`, `c2` (bd_c2, 00E8…), and `idxLut` (1110).

The scenario `Scn2`: r1 and r2 are steps, and q is a single rising step at T on the horizon
`t < H` (no q runt). Every relation holds for `t < H`. A0 is constrained only by H_SRV.

Definitions:
- `W2 = (b6 − L) − (a2 − s2)`. This is C-10i's window: a runt exists iff W2 > 0.
- `late2 = b6 + dg`: when the runt ends at ua2's core (q → ugrant → g2 → ua2), counted from T.
- `early2 = min(Lr, L − s2 + u2) + srv + da`: the earliest instant A0 can reach ua2's core.
  - R0 can rise through the q path (`Lr`).
  - R0 can also rise through the **r2·¬q term before the new q reaches ustate's O5**
    (`L − s2 + u2`). `cons2` shows that r2 reaches ustate's core no earlier than T + L − s2.
  - This second term is new. C-10i's ackcheck and rule A's from-q walk both miss it.
  - It is the earlier of the two in 134 of 288 rows, by up to 38 ps (O5-vs-O6 arc differences).
- **H_RUNT_ACK2 (`Ok2`): `W2 ≤ 0 ∨ late2 ≤ early2`.**
- **Index form (H_RUNT_IDX):** `W2 ≤ 0 ∨ b6 + e ≤ min(Lr, L − s2 + u2) + dz`.
  - `e` is the route plus arc of any LUT that reads g2.
  - `dz` is a lower bound on R0 → z_req (H_ZREQ: z_req rises only after R0 has been high
    for dz).

What downstream may and may not observe:
- **May observe:** the runt on g2 itself (C-10i), and a runt on the index or data LUT outputs
  while z_req is low.
- **May not observe, under Ok2:** A2 rising (`no_extra_ack2`).
- **May not observe, under H_RUNT_IDX:** an index or data LUT output that differs from its
  runt-free value while z_req is high (`idx_clean2`, for any LUT function `f`).
- Client 1: `no_extra_ack1`. g1 has no index reader in bdc_amerge (`unused_g1`; this was
  checked on the netlists, where the only g1 reader is ua1).

## Theorems (namespace `Formal.Timing.RuntAck`; all checked, no sorry, axiom or native_decide)

Each item says what it proves and what it assumes.
- **`c_low`**: a transport C-element (bd_c2 INIT) that never sees both inputs high never
  rises, given its reset and feedback delay > 0.
- **`cons2` / `cons1`**: consistency of the request timing.
  - Proves: the late request reaches ustate's core no earlier than q's own feedback.
  - Holds whatever A0 does, because with both requests up the INIT holds.
- **`r0lb2` / `r0lb1`**: R0 cannot rise before `T + min(Lr, L − s_k + u_k)`.
- **`gwin2` / `gwin1`**: the runt is confined to `[t_k + a_k, T + b)`.
- **`no_extra_ack2` / `no_extra_ack1`**: `Ok_k` ⇒ A_k stays low on the whole horizon.
- **`idx_clean2`**: the index form above.
- **Converses**, built on concrete witness traces:
  - `wit2_scn` / `wit1_scn`: the witness satisfies every gate relation. The witness has the
    server answering at exactly `srv`, and the C-element trace `ceTr` is a well-founded
    recursion through `c2`.
  - `extra_ack2` / `extra_ack1`: when `0 < W ∧ early < late`, the witness has R0 rising
    exactly once, ustate's core never seeing the late client asking with the state on its side,
    and A_k high anyway.
  - `extra_ack2_both`: A1 also rises in the same witness, which gives two acknowledges for one
    R0 rise.
  - `wrong_index2`: z_req is high while `idxLut` = 1 and q = 1 (client 1 owns the grant).
- **`spurious_ack2_iff` / `spurious_ack1_iff`: H_RUNT_ACK is exact.**
  - Statement: a scenario with an extra acknowledge exists iff `0 < W ∧ early < late`.
  - Side conditions:
    - `hu`: the other request reaches R0's core before the q it caused.
    - `hsa`: A0 reaches ustate after q's feedback.
  - Both side conditions hold on all 288 rows (computed in Python, not decided in Lean).
- **Checker:** `Row`, `okAck`, `okAck_sound1/2`, `okAck_exact1/2`, `inst_no_extra_ack1/2`,
  `inst_idx_clean2`.
  - These work on prefix-cancelled routed quantities (H_SHARED_PREFIX, as in C-10i).
  - A passing row means no extra ack and no wrong index at any prefixes.
  - A failing row is a real violation when the server answers at its bound.
- **`Cert`, `Cert.ok`, `cert_bound`**: a truncated potential certificate (a balanced BST of
  potentials ≤ M, arcs checked `p v ≤ p u + w`).
  - Proves: every path of the graph from R0 to n is at least `c.p n` long.
  - Requires `Complete`: every arc that leaves a node with p < M is listed.
- `#print axioms` gives at most propext, Classical.choice and Quot.sound. `demo_fast_server`
  depends on no axioms.

## Per-instance evaluation (item 3)

`RuntAckInst.lean` has the following, per instance and corner (FMIN, FMAX, SMIN, SMAX):
- **Two certificates.**
  - `_F`: the full routed SDF graph, every arc, prjxray-priced at that column. The fallback is
    0.772 × SDF; at most 1 fallback arc is in any cone. It is used for A0.
  - `_R`: the rise graph, with the fast-fall side taps removed, for z_req.
- **The ack rows** for both clients, with `P := cert.p <ua_k A0 pin>`.
- **One index row per g2 reader**, with `P := certR.p <z_req tail>`.

Result: **all 288 ack verdicts and all 304 index verdicts are `true`.** The per-instance table
is in `build/summary.md`. Read the "need" column as the minimum server latency each instance
relies on.

To keep the certificates small (≤ ~40 arcs), each one is truncated at M = the bound its
verdicts need, plus 1. The margins reported in this note are the exact Dijkstra distances. They
are evidence; the Lean verdicts are pass/fail.

**Which instances can actually break the handshake:**
- **gcd_hw:** none of the 36, at any consistent corner, with the routed server.
- **link_arb:** depends on the board (ENV, above).

## Item 4: tighten.py rule A and the amerge select

`rulea.py` replays rule A's own pairing, importing `cells/verify/tighten.py` read-only: the same
false-arc pruning, peers and confinement.

**Does the walk start at q? Yes**, on all 36 amerge stages.
- ustate's O6 (q) is a storage node, so `cell_boundary` puts it in rule A's source set.
- The from-q pairing measures `q → ugrant → g2 → index/data LUT (or ua2) outputs` against
  `q → ustate O5 → R0 → uor → chain → z_req`.
- With rule A's guard, the from-q margin is ≥ 4904 ps, in SDF.
- rule A's `early()` drops the fast-fall taps: this is exactly H_FF_DRAINED, which agrees with
  our rise graph.

**Does that cover the race? In practice yes; exactly, no.** Rule A misses three things:
1. **No site pins.** Rule A prices with nextpnr's SDF, which has none. C-10i showed the race
   window is a site-pin effect.
2. **The r2·¬q path.** Rule A does not pair the q-launched runt end against the r2-launched
   early R0 (the `L − s2 + u2` term, up to 38 ps earlier).
3. **Pairing per source.** It pairs per source, not as the race does.

The prjxray-priced, kernel-checked index margin (+2633 ps) is what discharges the race. Rule A's
200 ps guard would also cover items 1 and 2 on these routes, but that is not a proof.

## What checks (exact command)

    formal/tools/runtack/check.sh      # ~2.5 min

The script runs these steps in order:
1. Extract, one process per route (reusing 10i's extractor by import).
2. Emit, then a drift check against the committed `RuntAckInst.lean`.
3. Compile the Lean (theory ~4 s, instances ~11 s).
4. `scan.py`.
5. `#print axioms`.
6. Negative control: one flipped verdict, which the kernel refuses.
7. The rule-A replay.

Last run: `C-10j check PASS`. It uses core Lean only and imports `Formal.Timing.GrantFork`
(and through it B's `ArbBinary`), all read-only.

## Hypotheses and fidelity

**H_SRV** (A0 rises only ≥ srv after R0 was high), with srv bounded by **H_CAUSAL_PATH**.
- Claim: every causal chain from R0 rising to A0 rising at ua_k is a path in the routed timing
  graph, and every arc's delay is at least its corner weight.
- Why it holds: A0 is the consumer's acknowledge, which needs z_req, which needs R0.
- Pessimism: it crosses C-elements and latches as pass-throughs, and keeps every SDF arc
  (including INIT-dead ones), so it is a pessimistic lower bound.
- `Complete` (the cone is listed in full) is an extraction claim that the extractor meets by
  construction.
- Test: the GLS sweep in C-10i §4 (force A0 = R0 through a short delay d; A2 must fire iff
  d < need).

**H_FF_DRAINED** (index only).
- Claim: a fast-fall link of the z_req chain (AND(s_k, r0), INIT 1000) rises only after its
  chain input rises. That needs the chain to be drained when R0 rises.
- This is rule F's obligation. It is not proved here.
- A Lean lemma about AND chains would take about 0.5 day.

**Scenario hypotheses** (as in C-10i): H_A0_LOW at the start, no q runt (tier 3 excluded),
single request edges. The horizon H is where client 1 drops r1; after that, B's handover
results apply.

**Primitives:**
- **LUTs:** real INITs, with per-(pin, output) transport delays. This is pessimistic for runts
  (it passes every runt) and therefore safe for the "no extra ack" direction. The C-element is
  B's `c2` with a feedback pure delay; a ringing A2 in the converse is a transport artefact, but
  its first rise is not.
- **Wires:** prjxray RC trees with site pins (tcheck's `Prjx`), with exact prefix splits on the
  q and r nets.
- **Corners:** one consistent column per row, rounded outward: late side up, early side down,
  sign-consistent for every field. The independent-box reading of C-10i is not evaluated here.
- **Server arcs:** prjxray where `Prjx` prices them, otherwise 0.772 × SDF (H_FALLBACK_BAND).
  At most 1 such arc in any certificate cone.
- **link_arb's r nets** are pad-driven. Only the q-side "need" is reported there.

## Surprises / did not work

- **The r2·¬q early R0 path.** R0 = r1·q + r2·¬q can rise from the late request, before the new
  q reaches O5. This is glitch-free in the transport model (the union with r1·q is contiguous),
  but it is up to 38 ps earlier than the q path. Nobody had it.
- **Polarity.** A polarity-blind min path to z_req goes through the fast-fall taps (459 ps
  against 3517 ps at FMIN on merge10). Without the rise-only reading the index check means
  nothing.
- **Python ordering.** Hash-ordered sets made the first generated file nondeterministic. It is
  now sorted.

## Effort to finish / what it buys

- **Buys:** a proved, exact statement of what the grant-fork runt can and cannot do downstream,
  per-instance kernel verdicts, and a server-latency floor per instance. That floor is the
  number that matters if anyone ever puts a fast server behind `bd_arbiter`.
- **To finish:**
  - an H_FF_DRAINED lemma (~0.5 day);
  - an IOB-priced bound for link_arb (~2 h);
  - the GLS sweep (C-10i §4).
