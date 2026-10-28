# P7: formal's findings about research, checked on research head 4051359

Auditor subagent, 2026-10-28. Checkouts: formal 6863284 (~/wt-f7), research 4051359 (~/wt-r7).
Toolchain: ~/audit-tc (nextpnr 9c732bc6303458df, toolchain.sh 9/9 ok; prjxray-db under
~/audit-tc/openxc7/share/nextpnr/prjxray-db). No git commands were run. Formal's tools were read
as the thing under test and never used as evidence. All scripts and artefacts are under
`audit/r7f/`.

Code drift: the findings quote research 7f6c724 / 350f9be. Every line range they quote matches
head 4051359 exactly: `tighten.py:674-697` cell_boundary, `:705-727` CONST_DRV/starts_reaching,
`gen.py:412-427` perturb, `:494-512` perturb_ic, `fid_core.vh:84-86,101-103`, `run_fid.sh:13`.
So none of the findings has been fixed on research.

| # | source commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|---|
| 1 | 7f46f23 (C, C-10n) | "tighten.cell_boundary (and tcheck rules2.py) times GND/VCC tie-off routes as data (false path, overstates rule-A peak by 0.9-4.2 ns; whole cause of ipow s3 rule-A -59 ps)" | **CONFIRMED** (0.9 ns low end not seen) | Own ipow routes from research head (T9, BD_DSP=1). Seed 3 reproduces `uut.umuli1` margin **-59**, peak 18442 (= 17715 + 727 lag), "data from $PACKER_GND_DRV/Y". With cell_boundary wrapped to drop tie-offs (`r7f/ipow/noconst.py`, tighten's own code otherwise), the peak is 14953 (= **14226** + 727) and the margin is **+4128**. Rule A is then clean. Tie-off is the late source on 4/4 ipow cells (ucmpi2, umuli1, uselect0, ushrsi0) on s1 and s3, on collatz s1 uselect0 (VCC) and on xorshift s1 ucmpi0 (GND). Overstatement: 2.0-4.2 ns (ipow), 2.66 (collatz), 2.54 (xorshift) | It is a real false path: a configuration tie-off never toggles. **It is conservative on all 4 routes.** It enters only check_bundled's max-over-starts, so it can only lower a margin. The tie-off reaches no rule-A request tail under tighten's own confinement (`r7f/ipow/constreach.py`: 0 reaches; 2 per route only when unconfined). **The code does not guarantee this, though.** If a tie-off ever reached a tail inside the confine, check() would pair through the constant, return non-None and skip the more pessimistic check_bundled, which could be optimistic. Rules I/H/D are not affected (their sources filter is_const, :2133/2137). formal's rules2.py:111/114 still calls T.cell_boundary unfiltered at 6863284 |
| 2 | 95ca2d6 (B, B-gls-vs-exact) | "gen.py:494-512 never applies GLS_SCALE_INST to wire delays with wire-mode scatter on" | **CONFIRMED**, still at 4051359 | `r7f/gen/scale_wire.py` imports research gen.py with the wire model stubbed to factor 1.0. GLS_SCALE_INST=uut.x:3 gives: arc mode, interconnect 1000→3193; no scatter, 1000→3000; **wire mode, interconnect 1000→1000** while the cell arc is 1000→3193 | n_scaled_inst counts only the cell arcs in wire mode, so the "matched no instance" guard (gen.py:582) still passes. A fault run with wire scatter injects only the cell part of the fault, silently. Arcs that fall back from the wire model (route sink not found) do get the scale |
| 3a | 71ea5f3 (A, ForRes §4) | "prjxray-db has inverted FAST tuples ... 14 pips ... [0.202, 0.105, 0.231, 0.312] ... only inverted tuples in the zynq7 db ... xray_delay.py propagates them" | **CONFIRMED** (per-route counts UNVERIFIED) | Own scan of all 149 `zynq7/tile_type_*.json` (`r7f/xray/inverted.py`): 40,422 delay 4-tuples. **28** have FAST_MIN > FAST_MAX, all in BRKH_INT (14 pips × src_to_dst/dst_to_src), all [0.202, 0.105, 0.231, 0.312]. **0** SLOW inversions. prjxray's `fast_slow_tuple_to_corners` keeps the order (no sort). Research `xray_delay.d4/add4` sums the columns unchanged: INT+BRKH+INT = (0.300, 0.223, ...) ns, still inverted by 77 ps (`r7f/xray/d4probe.py`). No lo>hi check exists | "gcd_hw R5: 2-20 arcs per seed" is not reproduced. None of my routes crosses BRKH (ipow s1/s3 arcs.tsv: 0 arcs with fast_min > fast_max), and neither do 2 sibling gcd_hw routes. A research bq3_min fasm route has 3 nets through these pips, so the case occurs in practice. "Unsafe direction" holds only if the true FAST_MIN is the lower of the two |
| 3b | 71ea5f3 (§5 tcheck table) | "What the verified checker (tcheck) replaces ... 1661 of 1900 agree ... 0 rows fail at a fixed corner"; gaps table | **UNVERIFIED** (agreement counts); project-side rows spot-**CONFIRMED** | The agreement counts are output of formal's own tool, which was not re-run. Project side: tie-off row = item 1. "First stages fed by a compute cell not audited by rule I" shows up as 23 "not audited" lines on ipow s3. tighten's rule-J flat 124 ps LUT model is commented at skew.py:235 | The DSP/CARRY4 fallback rows were not checked |
| 3c | 71ea5f3 (§6/§7 GLS SAF/X re-run on 350f9be) | "CARRY4 and SLICE_LATX [SAF] even under fid ... O0 rises at 1223 ps, 23 ps after its cause, through a 223 ps arc"; "SLICE_LATX pessimistic ... SLICE_FFX hides X on SR and CE" | **CONFIRMED** at 4051359 (prims.v md5 f4f16462…, fid_core.vh 2422ccea…) | Own tb (`r7f/glsx/tb_saf.v`), default and -DGLS_FID give the same result. S0 pulses 1000-1010 and CIN rises at 1200: O0 rises at **1223** and stays high, where transport gives a pulse 1223-1233 then a rise at 1422. Narrow pulses (29/99 ps) are swallowed. `tb_x.v`: latch with CK=x, CE=0 → x (silicon holds 0); latch with CK=0, CE=x → x (holds 0); flop with SR=x, CE=1, D=1 → 1 (should be x); flop with CE=x → holds Q (should be x) | CARRY4 and SLICE_LATX sit outside the `ifdef GLS_FID` in prims.v. My F2 shows a hold to 0, not 1, because of a different setup; both hide X |
| 4 | 95ca2d6 (B) | "fid resolver runts printed only with +META_VERBOSE; no protocol/overlap/start-count monitor in design runs" | **CONFIRMED** | fid_core.vh: META lines only print `if (verbose)` and rejected RUNT lines only `if (verbose > 1)`. The counters n_meta/n_rej/n_commit are never printed (no final block). run_fid.sh runs `vvp run_baked.vvp +VEC +TEND +QUIET` with no META_VERBOSE. tb_run.v checks only laps/ERR/OK/deadlock/ring-stopped | Gcd-specific value guards exist (gen_absguard/gen_cmpguard), but they are not protocol monitors. The arbiter CHMON lives only in the f3 unit bench (`fid/f3/tb_f3_arbm.v`, run with META_VERBOSE=1) |
| 5 | eb346fb (A, Events8) | "gcd_hw CLEAN at slow/fast on all 4 seeds; gb seed d fails ENTRY on 3 arbiter guard pins (-51/-94/-68 ps)" | **UNVERIFIED** | The numbers come from formal's xaudit/events8 Lean certificate on gcd_hw R5 routes (seeds d/3/4/5) at corners slow/fast/indep/gb. gb = one die in [0.668, 1.0] × SLOW_MAX, and 0.668 = skew.py GUARD_LO/GUARD_HI = 0.772/1.155 (checked at skew.py:239-240). No R5 seed-d route was rebuilt, and the ENTRY semantics were not re-implemented | Internal inconsistency: A-events5's analysis flagged the **same 3 pins** at gb seed d as -52 (merge3.ua1) / -26 (merge2.ua2) / -9 (merge3.ua2). Events8 gives -94 / -68 / -51, a uniform ~42 ps shift. The "plo−1 / strict" explanation in A-events8 does not account for 42 ps. FOR-RESEARCH §11 cites the Events8 figures |

## Details

### 1. Tie-off false path in rule A
- **Code at head.** `cell_boundary()` (tighten.py:674-697) collects every source outside the
  region with no `is_const` test. `CONST_DRV`/`is_const` (:705-709) exist, and
  `starts_reaching` (:712-727) uses them. Rule A (:1684-1698) passes the unfiltered sources to
  `check()` and then to `check_bundled()`.
- **Builds.** I built from a research-head copy, not formal's `git archive` of the formal
  branch, and without formal's `--freq 100` patch:
  `cells/flow.sh` with `NEXTPNR_SEED=s BD_DSP=1 BD_TOP_V=../top.v BD_SIZES=../sizes.vh`.
  - Kernels: ipow T9 (seeds 1, 3), collatz T3 (seed 1) and xorshift T3 (seed 1).
  - Logs: `audit/r7f/<k>/s<n>/{flow,tighten,tighten_noconst}.log`.
  - Every flow ran to `flow.sh PASS`.
- **The ipow s3 -59 ps is the formal figure exactly.** It reproduces bit-for-bit at research
  head, and so does the no-const peak 14226.
- **Peaks, with tie-offs vs without (ps):**
  - ipow s3: ucmpi2 9136/5978, umuli1 18442/14953, uselect0 18964/16729, ushrsi0 11112/6866.
  - ipow s1: 8541/6040, 17824/14642, 18518/16541, 10375/6621.
  - collatz s1: uselect0 9607/6943.
  - xorshift s1: ucmpi0 7206/4667.
- **Other violations.** tighten exits 1 on every route because of rule D bd_steer `ucond_br*`
  screens, -4 to -7 ns. research/JOURNAL.md documents these as known and covered by rule E,
  and they do not depend on the tie-off. Rule A is clean on every route except ipow s3, and
  that one is cleared by removing the tie-off.
- **Is it conservative?**
  - Yes on the evidence. A constant source in check_bundled only adds candidates to the max on
    the data side.
  - The one non-conservative channel is a constant reaching the request tail inside the
    confine. Then check() would pair through it, and the cell would no longer get the
    bundled-channel pessimism. That reach occurs on 0 of 43 rule-A sites over the 4 routes.
  - The fix (filter is_const in cell_boundary) removes both effects.
  - The cost of the bug is speed: over-sized lines (umuli1 47 → 38 links, ushrsi0 30 → 16 on
    s3). Longer lines can matter to rule F, but those are re-checked with the actual sizes.

### 2. GLS_SCALE_INST in wire mode
In wire mode, `perturb_ic` returns `ps * DELAY_SCALE * f` (gen.py:512). It never loops over
`SCALE_INST` the way `perturb` does at :420-424. The probe output is in the table.

### 3. Inverted FAST tuples
- **Database.** The scan output is in the table. The only 4-tuple field in the db is
  `delay`, so "only inverted tuples in the zynq7 db" holds.
- **Output format.** xray_delay writes `(FAST_MIN:SLOW_MIN:SLOW_MAX)` (:876, :903). So on a
  crossing arc the GLS min column carries the summed FAST_MIN, which is ~97 ps per crossing
  above the summed FAST_MAX.
- **Per-route counts.** Not reproduced: no BRKH crossing on the routes available.

### 4. fid observability
See the table. The runt and metastability counters exist, but no design run ever reports
them.

### 5. Events8
Not recomputed. The pin set agrees with A-events5's independent analysis. The magnitudes
disagree by about 42 ps per pin, so treat the exact margins as tool-specific until one of them
is reproduced.

## Scripts (auditor-owned)
- `audit/r7f/ipow/noconst.py`: tighten with tie-off sources dropped.
- `audit/r7f/ipow/constreach.py`: tie-off → request-tail reachability under tighten's own
  confinement.
- `audit/r7f/gen/scale_wire.py`: GLS_SCALE_INST probe.
- `audit/r7f/xray/inverted.py`, `brkh_route.py`, `d4probe.py`.
- `audit/r7f/glsx/tb_x.v`, `tb_saf.v`.
