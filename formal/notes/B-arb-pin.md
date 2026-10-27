# B probe Barp: bd_arbcell with per-pin, non-monotone read maps

File: `formal/lean/Formal/Cells/ArbPin.lean` (core Lean, about 1300 lines). It imports
`ArbBinary` (for `stF`/`gr1`/`gr2` = the real INITs through `lutB`/`o5B`/`o6B`) and
`LibGapSteer` (for `Rd`). It adds no shared definitions.

Check: `/tmp/claude-0/.../scratchpad/bchk.sh formal/lean/Formal/Cells/ArbPin.lean`
prints `[bchk] OK` (-DautoImplicit=false, about 23 s). The file has no
sorry/admit/axiom/native_decide. `#print axioms` on all 48 main theorems gives a subset of
`propext, Classical.choice, Quot.sound`.

## Which earlier arbiter results hold in a model at least this general?

None of them. ArbBinary, ArbA0Fork, ArbOverlapRace, ArbCorners(Pin) and ArbHeldTimed2 use
transport delays, one per pin or per output. ArbHandover uses a rise-fast pure delay.
ArbKleene uses atomic Kleene LUTs. ArbInvolution uses involution channels. In
`LibGapSteer.Rd`, a pin shows its driver at any instant of its window, chosen
independently at every output instant, so samples can arrive out of order. A behaviour
with all windows of width 0 is a transport behaviour. Every transport result therefore
holds here only if its proof survives arbitrary sampling. This file re-derives the
windows and compares them.

## Model

- **Cells.** `ustate` is `bd_c2n_set` (INIT FFB2…, pins r1, r2, q, rst=0). `ugrant` is a
  LUT6_2 with INIT 0C0C0C0C_A0A0A0A0 (O5 = g1 = r1·q, O6 = g2 = r2·~q).
- **Read maps.** Every pin has one, including the q feedback (`pq`) and the two pins the
  INIT ignores.
- **H_PIN_READ.** Each map lies in a box (`Box`):
  - ustate r1 in [a1,A1], r2 in [a2,A2], feedback in [l,L];
  - ugrant r1→O5 in [b1,B1], r2→O6 in [b2,B2], q→O5 in [c5,C5], q→O6 in [c6,C6].
- **H_ST, H_PRE.** H_ST holds for t ≥ 0 (rst released); q = q0 before 0.
- **Box.Ok.** lo ≤ hi, lo ≥ 0, l ≥ 1.
- **Hypotheses used only by the necessity witnesses:**
  - H_LOOP2: L ≥ 2;
  - H_LOOP_WIN: l < L;
  - H_QWIN: c5 < C6 ∧ c6 ≤ C5+1.
- **Requests.** Single steps (`up e`, `dn e`).
- **Exclusion.** `Excl`: never g1 = g2 = 1.
- **Transport.** A cell is transport when every window has width 0.

## (a) Exact windows (every iff over the box, with witnesses both ways)

**Same sense: both rise, r1 at e1, r2 at e2, q0 = 0.** Side 2 won last. Let g = e2 − e1.

- **QUIET, g ≤ a1 − A2.** q never moves (`su_quiet`), so exclusion holds. Plain
  language: r2 is surely seen by ustate before r1 can be. Note what this means for
  "simultaneous" requests (g = 0): they are safe only if A2 ≤ a1, i.e. if the two pin
  windows do not overlap.
- **OSCILLATION, a1 − A2 < g < A1 − a2 + L.** Under H_LOOP2 and H_QWIN, `su_osc` gives a
  transport behaviour in which q takes both values after every time bound and g1 = g2 = 1
  after every bound.
- **COMMIT, g ≥ A1 − a2 + L.** q = 1 from e1 + A1 in every behaviour (`su_commit`).
  Exclusion holds iff `¬SuOvT`. Closed form (`suOvT_closed`):
  **C6 ≤ c5 ∨ e1 + A1 + C6 ≤ max(e1+b1, e2+b2)**.

`su_box_iff` (every per-pin behaviour) and `su_transport_iff` (transport behaviours only)
have the same right-hand side: **exclusion ⟺ QUIET ∨ (COMMIT ∧ ¬SuOvT)**. The
counter-traces are `su_osc` and `su_rise_cex`. Non-vacuity: `su_nonvacuous` (commit, every
behaviour exclusive, side 1 granted) and `su_osc_instance`.

**Opposite sense: r1 rises at e1, r2 falls at e2, q0 = 0.** Let X0 = max(e1+a1, e2+a2) and
X1 = max(e1+A1, e2+A2).

- In every behaviour, q = 0 before X0 and q = 1 from X1 (`o1_before`, `o1_after`). The
  resolution time is bounded in every digital behaviour.
- `o1_box_iff` (under H_LOOP_WIN): exclusion ⟺ ¬O1Ov. Here O1Ov means: there is a t in
  [e1+b1, e2+B2) of RISE type or FALL type.
  - RISE type: c5 < C6 ∧ X0+c5 ≤ t ≤ X1−1+C6.
  - FALL type: c6 < C5 ∧ X0+2 ≤ X1 ∧ X0+c5 ≤ t ∧ X0+1+c6 ≤ t ∧ t ≤ X1−1+C6 ∧
    t ≤ X1−2+C5.
- `o1_transport_iff`: transport exclusion ⟺ ¬O1OvT, which is RISE type only.
- Counter-traces:
  - `o1_rise_cex` (transport, one clean q rise);
  - `o1_fall_cex` (non-monotone). At one instant both ustate request pins sample early
    and everywhere else late. q makes a 1-instant runt, and the loop reads around it.
- Non-vacuity: `o1_nonvacuous`. The requests move at the same instant, and every
  behaviour of that box is exclusive.

**Handover: r2 waiting, the holder r1 falls at f, q0 = 1.**

- In every behaviour, q = 1 before f+a1 and q = 0 from f+A1 (`h12_before`, `h12_after`).
- `h12_box_iff`: exclusion ⟺ ¬H12Ov, which combines a clean-fall (DOWN) type and a
  dip-runt type.
- `h12_transport_iff` with `h12OvT_closed`: transport exclusion ⟺
  **C5 ≤ c6 ∨ B1 ≤ a1 + c6**.
- Counter-traces: `h12_down_cex` (transport) and `h12_runt_cex` (non-monotone: q dips to 0
  for one instant).

## Do the non-monotone reads change the earlier windows?

| scenario | transport window (box) | per-pin window | same? |
|---|---|---|---|
| same sense, both rise | QUIET ∨ (COMMIT ∧ ¬SuOvT) | identical (`su_box_iff`) | yes, under H_QWIN (`su_same`) |
| opposite sense | ¬O1OvT (rise type) | ¬O1Ov (rise or fall type) | iff c5 < C6 (`o1_same`); differs otherwise (`o1_differs`) |
| handover r1→r2 | C5 ≤ c6 ∨ B1 ≤ a1+c6 | ¬H12Ov | iff c6 < C5 (`h12_same`); differs otherwise (`h12_differs`) |
| g1·g2 run length | ≤ \|b5−b6\| (`ArbOverlapRace.grant_cap`) | unbounded: both grants high for ever (`su_overlap_forever`) | **no** |

Rows 1-3 compared with the earlier files:

- **Row 1 (ArbBinary).** Specialise to ArbBinary's model: the requests reach both LUTs
  together and the grants read the same q, so a = A = L and b = c = d5/d6. The window
  becomes exactly g ≤ 0 ∨ g ≥ L, under H_QWIN (with fixed delays: d6 = d5 + 1, as in
  ArbBinary's runt example d5 = 1, d6 = 2). This is ArbBinary's runt (0 < g < L) and its sufficient
  |g| > L, now exact. H_GRANT_SKEW is not needed in this scenario. With d5 = d6, H_QWIN
  fails, and ArbBinary's `exclusion_zero_skew` covers that case.
- **Row 3 (ArbOverlapRace).** This is `handover12`'s cell condition (overlap > 0 iff
  b > 0 ∧ κ1 > 0) taken at the box corners. It is unchanged whenever c6 < C5.

**The finding.** In transport, a break-before-make ordering of the q→O5 and q→O6 windows
protects one direction:
- C6 ≤ c5 protects a q rise;
- C5 ≤ c6 protects a q fall.

With non-monotone reads that protection is lost. Out-of-order samples at ustate make q
runt in the opposite direction, and the runt presents the opposite edge to the grants.
Two conditions are needed for this:
- the ustate request window has at least 2 instants (X1 − X0 ≥ 2, A1 − a1 ≥ 2);
- the loop window has at least 2 instants (l < L).

What remains is the request-versus-q-path inequality (the κ-type term). For example,
`h12_differs` is a box with q→O5 faster than q→O6, as with q on A5. It is exclusive under
transport but overlaps per pin. When the windows already allow both orderings
(c5 < C6 ∧ c6 < C5), nothing changes. That holds in any box spanning corners with a
shared q wire spread.

**The run cap does not survive.** `su_overlap_forever` and its `boxS` instance take
q→O5/O6 windows at least one loop wide (L−1 ≤ C5−c5, c5+L ≤ C6, c6 ≤ c5+1) and an
oscillating q. Then both grants are high at every instant from some time on. So
`ArbOverlapRace.cell_never_203` is a transport-only statement. In this model it fails
whenever the windows are that wide. The model is permissive here, arguably beyond the
silicon: a real pin does not resample an oscillating node chaotically over a 10 ps
window. This is the price of dropping FIFO.

## (b) Outside the windows

- **Same sense.** Between QUIET and COMMIT there is eternal oscillation, on an open
  interval of gaps (`su_osc`). This is the binary-model analogue of ArbInvolution's
  unbounded resolution, which there happens only at the critical gap s* and nearby. That
  file is cited for context only. The interval here is an artefact of binary channels
  with no decay, just as transport was in ArbBinary.
- **Opposite sense and handover.** Resolution is always bounded, by X1 and by f+A1
  respectively. Per pin, however, q CAN runt even though each request makes one clean
  edge:
  - `o1_fall_cex`: q = 1 at s, 0 at s+1;
  - `h12_runt_cex`: q = 1, 0, 1.

  Transport cannot do this: ArbBinary's `opposite_sense_clean` gives exactly one edge.

## (c) What downstream can see

- **`Cell.reader`.** A reader that reads g1 and g2 through its own windows sees the
  grant pair of a cell in `readerBox`, whose grant windows are widened by the reader's.
  So every sufficient condition applies with the composed windows (`o1_reader_excl`,
  `su_reader_excl`). The converse is NOT proved: the composed maps are correlated.
- **`reader_handover_iff` (exact).** Take a clean exclusive handover: g2 falls at h, g1
  rises at h' ≥ h. A reader sees both high for some maps iff **h' − h < Y2 − y1**. This is
  the header's "a consumer must not read within one loop delay" restated: the reader's
  own skew window must not exceed the handover gap.
- **`reader_glitch_iff` (exact).** A non-monotone reader can see a single clean grant
  edge as 1 then 0 iff its window has at least 3 instants. A FIFO reader cannot
  (`reader_mono_step`).

## Not covered

- the `bd_arbiter` A0 hold;
- mirror cases (q0 = 1 same sense, both falling, r1↓/r2↑, the r2→r1 handover);
- the same-sense oscillation regime without H_QWIN (in fixed-delay boxes this is a
  question about residues modulo L; open);
- request waveforms other than single steps;
- Kleene/X values;
- the shared-q-pin correlation between the O5 and O6 reads (treated as two independent
  maps, which is the worst case; `same_read_excl` is the other extreme);
- prjxray numeric instances (all boxes here are illustrative);
- the per-route evaluation of the κ-type terms.

## For the cell owner

Exclusion during handover in the per-pin, non-FIFO model does not follow from the
O5/O6 arc ordering. It needs the κ-type inequality to hold for both orderings:
- B1 ≤ a1 + c6, roughly: the r1 fall reaches O5 before the q fall can reach O6.

If pin FIFO is assumed (as the GLS does), the transport windows apply, and so do the
earlier numbers in ArbOverlapRace and ArbCorners. Whether a LUT input pin is FIFO is a
hypothesis about the fabric: H_PIN_FIFO, not tested. A test would be a GLS or board
pulse-train experiment on one pin.
