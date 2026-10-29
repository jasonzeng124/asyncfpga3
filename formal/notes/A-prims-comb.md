# A-prims-comb: digital semantics of the combinational primitives (LUT6_2, MUXF7/F8, CARRY4, OUTMUX hops)

Probe PrimsComb, shard A, session 2026-10-29. North-star goal 1.

STATUS: in progress. Census done; Xray/XrayData/Muxf compile (check.sh pending for Carry,
Lut62, Hops, GenCheck).

## 1. Census: which primitives the routed designs use

| design | LUT6_2 (fractured) | MUXF7 | MUXF8 | CARRY4 | source |
|---|---|---|---|---|---|
| gcd_hw (route d, kernel + rig) | yes (8925 LUT sites incl. O5; bd_latch W=32 is 16 LUT6_2 pairs, bd_steer LUT6_2 ×38) | 857 | 343 | 59 | C-11f-design-import.md coverage table (bitstream read-back); B-gcd-cells.md |
| gcd_hw (urig. prefix only, xaudit cut) | (in the 8546 LUTs) | 824 | 341 | 38 | tools-A/xaudit/gcd/inputs/routed2x_d_slow.txt line 3 |
| collatz | yes (bd_latch W=32 in every link; not counted) | yes: 196 F7/F8 select nets | (F7/F8 not separated) | yes: 14 CARRY4 CIN cascade nets, research JOURNAL 05:45: 64 CARRY4 S arcs | C-10n-kernels.md fallback census; research/JOURNAL.md |
| xorshift | yes (same) | yes: 4 F7/F8 select nets | (not separated) | yes: 11 CIN nets | C-10n-kernels.md |
| ipow | yes (same) | yes: 106 F7/F8 select nets | (not separated) | yes: 3 CIN nets; also DSP48E1 (77,778 fallback arcs) | C-10n-kernels.md |

Caveat: the routed JSONs of collatz/xorshift/ipow are not on disk in this sandbox (they were in
/tmp of an earlier one; no yosys/nextpnr here), so their counts are indirect (net kinds in the
tcheck fallback census). The presence of each primitive is certain from those nets; exact
instance counts are not available. A CIN net count is a lower bound on cascaded CARRY4s only.
So every one of the four designs uses LUT6_2 (fractured O5/O6), MUXF7 and CARRY4; MUXF8 is
confirmed on gcd_hw only.

## 2. Data source (prjxray-db), and the corner rule
- `zynq7/timings/slicel.sdf` sha256 fd31d66077f869d01f13d9fabbd0dcd38b4aab0322179ecf9ac190a3b70c5456,
  `slicem.sdf` sha256 3d2da5714d8c81165fa51403fb719b3ddd9e7ea7ab79280ae4e157d11a29172e, fetched
  2026-10-29 from raw.githubusercontent.com/f4pga/prjxray-db/master (the toolchain copy under
  $TC is not on this sandbox; research/JOURNAL.md says the research branch uses prjxray-db commit
  0a0added, 2021-12-14; the master file was not compared against that commit: a lead TODO).
- Triple = `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)` (prjxray utils/makesdf.py IOPATH template).
  Fast and slow corners. NOT rise/fall. One band per arc for both edges.
- Numbers are not hand-transcribed: `Wip/PrimsComb/xray2lean.py` generates
  `Formal/Core/Prims/XrayData.lean` (exact ns -> integer ps; fails on >3 decimals), with the
  SDF line of each number in a comment, and has a `--check` drift mode.
- The lost draft's hand-transcribed SLICEL numbers (Wip/_snapA/.../Xray.lean) agree with the
  generated ones for F7AMUX/F7BMUX/F8MUX, CARRY4, CARRY4_O5 (checked by eye on the mux rows).

## 3. Files (all Mathlib-free; `decide` / `decide +kernel`, no native_decide)

| file | what |
|---|---|
| `Formal/Core/Prims/Xray.lean` | types: `Corner`, `Band` (lo/hi per ONE corner, `In`, `add`, `hull`, series/hull lemmas), `SiteType`, `Letter`, `FMux`, `MuxArcs`, `CPin`, `COut`, `C4Var`, `OSrc`, `CHop` |
| `Formal/Core/Prims/XrayData.lean` | GENERATED numbers: `selmux`, `f7Hop`, `f8SelHop`, `carry4Arc` (240 arms, 14 CARRY4 variants x 2 site types), `lut6Arc`, `lut5Arc`, `outMux`, `outMuxL`, `carryHop` |
| `Formal/Core/Prims/Muxf.lean` | MUXF7/F8 (`mux2`), static + timed |
| `Formal/Core/Prims/Carry.lean` | CARRY4 (`kout`), static + timed, support = prjxray arc list |
| `Formal/Core/Prims/Lut62.lean` | LUT6_2 as one tree (`L62.o6Tree`, `o5Tree`) |
| `Formal/Core/Prims/Hops.lean` | OUTMUX / site hops as series delay arcs, variant hulls, data well-formedness |
| `Formal/Core/Prims/GenCheck.lean` | equality with shard C's `Formal.Gen.Netlist` interpreter (Kleene reading) |
| `Wip/PrimsComb/xray2lean.py` | the generator (+ `--check`) |

## 4. What is proved (plain language)

**MUXF7/MUXF8 (Muxf.lean).** Assumed: H_MUXF_PASS (the mux is a pass-transistor mux whose
output is Kleene-sound at every instant: with a mid-rail select and equal data it stays at the
data level) and H_PERPIN_TRANSPORT (each of the 3 arcs is a constant transport delay).
Proved: `mux2` agrees with the Boolean mux, is monotone, contains X, and is the most-defined
monotone extension (`mux2_exact`). The AND-OR gate realisation is strictly less defined, exactly
at (S=X, I0=I1=1): the classic static-1 hazard (`aoMux_hazard`), i.e. what H_MUXF_PASS decides.
Timed, any delays, any select waveform: select change with equal data never glitches
(`sel_change_glitch_free`); the deselected input can do anything (`unselected_glitch_free`);
any single-input change with equal old/new output is glitch-free (`sic_glitch_free`); same for a
MUXF8 over two MUXF7 (`F8Timed.sic_glitch_free`, all 128x7 cases). Proved glitch trace
(`data_first_glitch`): S rises and the deselected I0 changes at the same pin instant ⇒ wrong
value on [d0, dS). With prjxray data the select arc is the slowest arc of every slice mux at
both corners (`sel_slowest`, SLICEL+SLICEM), so that glitch happens for EVERY admissible delay
pair (`data_first_glitch_xray`), at least 16 ps (fast) / 22 ps (slow) wide (`glitch_width_table`).
NOT covered: slews, charge sharing, pulse filtering (inertial/involution), the hop from the LUT.

**CARRY4 (Carry.lean).** Model: 4 MUXCY (`mux2`, H_MUXCY_PASS) + 4 XORCY (exact Kleene XOR);
c0 from the PRECYINIT configuration mux (`precy`). Proved: Boolean agreement, monotonicity, X
containment; the chain with S=a xor b, DI=a is a 4-bit adder (all 512 cases, `adder`); NO
single-pin-change function hazard on any of the 8 outputs (all 512x9x8 cases, `kout_sic`), hence
glitch-free under per-pin transport for ANY delays (`sic_glitch_free`). Two-pin hazard: an
operand-bit flip moves S0 and DI0 together; CO0 unchanged but Kleene X (`two_pin_hazard`); timed
trace (`co0_glitch`): if S0->CO0 is faster than DI0->CO0, CO0 drops to 0 on [dS, dD); the other
order never glitches (`co0_no_glitch_other_order`); prjxray's bands admit both orders at both
corners (`co0_orders_admissible`: fast 89 < 112, slow 258 < 329). `support_matches_xray`: the
model's output-on-pin dependencies are exactly prjxray's SLICEL CARRY4 arc list (all 9x8 pairs).
Timing hypothesis H_C4_PERPIN: each output is the chain function of the pins each delayed by its
own IOPATH (prjxray gives no internal stage delays). NOT covered: internal ripple timing beyond
IOPATHs, the meaning of _LBOTH/_LFF variants (hulled in Hops).

**LUT6_2 (Lut62.lean).** One 64-cell tree: O6 = mux on A6 over two 5-input sub-trees, O5 = the
lower sub-tree (`o5_is_o6_branch`, definitional). Proved for EVERY INIT and Kleene input:
the A6-rooted physical tree equals Core's A1-rooted `Lut62.o6.keval` (`o6Tree_eq_keval`), so the
rank order is irrelevant statically; A6 tied 1 ⇒ O6 = upper half exactly (`o6_tied`); A6 = X ⇒
merge of the halves (`o6_A6_X`); shared read: bd_latch pair cell with en = X gives X on BOTH
outputs (`shared_X`). NOT covered: per-rank skew (LutTree), O5/O6 relative timing (data in
XrayData.lut5Arc/lut6Arc only).

**Site hops (Hops.lean).** Series composition of arcs at one corner (`Band.In.add`); the
a5lut->AMUX hop (62::78)(163::202) (`amux_a5lut`, the E8Mux number); every O5->OUTMUX path is at
least 62 ps fast / 163 ps slow above the LUT5 arc alone (`o5_path_includes_outmux`); prjxray's
two names per LUT output into the OUTMUX (x5lut vs o5, x6lut vs o6) have different numbers in
every column/site (`outmux_names_disagree`), hulled soundly (`outMuxHull_sound`); CARRY4 arcs
hulled soundly over variants (`carry4Hull_sound`); every generated band is well formed (`all_ok`).
Data oddity: the ?CY0 hops have one number at all four positions (`cy0_flat`).

**Equality with shard C (GenCheck.lean).** C's interpreter (`Formal.Gen.Netlist.Cell.out`,
Kleene reading), imported read-only: MUXF7/F8 `O` = `mux2` (`muxf_eq`; `mux2 = kmux`); LUT6_2 `O6`
= the physical A6-rooted tree, `O5` = the shared lower sub-tree (`lut62_o6_eq`, `lut62_o5_eq`);
CARRY4 all 8 outputs = `kout` with c0 = CI or CYINIT (`carry4_eq`). **One mismatch**, harmless
on decoded bitstreams: C's c0 = CI OR CYINIT vs the silicon's PRECYINIT mux; equal for every
configuration under C-11f's tie (unused one = 0) (`carry4_c0`), different if both driven
(`carry4_c0_differs`).
