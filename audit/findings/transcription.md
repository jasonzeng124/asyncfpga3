# Transcription fidelity: LUT INITs and pin maps, RTL vs Lean

Auditor's own extraction. Nothing from the audited branches was imported or run
except their source text, which was parsed, and the RTL, which yosys elaborated.

- Lean: branch `claude/formal` at 71ee3e86 (`/home/user/wt-formal/formal/lean/Formal/**`, plus `Wip/` for reference).
- RTL: branch `claude/research` at 19a93c1 (`/home/user/wt-research/cells/rtl/*.v`).
- Tools:
  - `audit/tools/extract_inits.py` parses the RTL and the Lean, matches them, and evaluates truth tables.
  - `audit/tools/yosys_inits.py` extracts the INITs from the yosys netlist.
- Reproduce:
  ```
  python3 -I audit/tools/extract_inits.py [--json OUT]
  python3 -I audit/tools/yosys_inits.py --work DIR
  ```
  (yosys 0.62: `~/audit-tc/openxc7/bin/yosys`)

## Bottom line

**No transcription mismatch was found.** Every LUT INIT constant in the Lean
files that is meant to model an RTL LUT equals the RTL constant, bit for bit.
That covers 70 named constants and 4 inline 16-bit sub-tables. At every use
site with an explicit pin list (187 sites), the Lean pin order I0..I5 and the
choice of output (O5/O6/O) agree with the RTL instance. All 74 truth-table
checks pass:

- the RTL INIT against the RTL header equation;
- the RTL INIT against the equation the Lean claims.

The yosys netlist matches the text parse for all 123 elaborated LUT cells:
INIT, pin nets and feedback wiring.

## 0. The RTL in the two branches

The two branches' `cells/rtl/*.v` are **byte-identical**: `cmp` reports all 10
files the same. The LUT sets that the script parses from each branch are also
identical: 41 instances.

The Lean comments cite `cells/rtl/...` line numbers. I spot-checked these
against this RTL, for example `bd_ce.v:34/40/49/55/62/70/81/86`,
`bd_arb.v:91/245/249`, `bd_latch.v:38/44/64/126/135/138/180/183/209/215` and
`bd_link.v:171-190`. All of them are correct, so the Lean follows this RTL,
whichever branch it is read from.

Other files under `cells/` do differ between the branches:

- `cells/gls/build.sh`
- `cells/gls/gen.py`
- `cells/verify/tighten.py`
- `cells/verify/test_rule_a_links.py`
- `cells/gls/fid` (only on the research branch)

None of these holds a LUT INIT that the Lean transcribes.
`cells/verify/inits.py` is identical in both branches.

## 1. Per-cell verdicts

The columns mean:

- "INIT eq": the Lean constant(s) equal the RTL `.INIT`.
- "pins eq": the Lean pin lists equal the RTL `.I0..I5` order, with constants
  tied as in the RTL.
- "TT": the truth table of the RTL INIT under its RTL pin map equals both the
  RTL header equation and the Lean-claimed equation, checked over all input rows.
- "yosys": the elaborated netlist reproduces the INIT, the pin nets and the feedback.

| Cell (RTL instance) | RTL INIT | Lean constants (files) | INIT eq | pins eq | TT hdr / Lean | yosys | Verdict |
|---|---|---|---|---|---|---|---|
| `bd_c2.u` bd_ce.v:34 | 00E8_00E8_00E8_00E8, I=[a,b,q,rst,0,0] | INIT_c2 / INIT_C2 / C2_INIT / C2 / INIT_C2_RST / Init.bd_c2 (CElemFn, CElemTiming, CTree, ArbKleene, ArbA0Fork, ArbBinary, ArbHandover, ArbHeldTimed, Core/Lut); `0x00E8` LUT4 sub-table (Core/Ternary, Bridge) | Y (sub-table: low 16 bits, I4=I5=0, Y) | Y | OK/OK (16 rows) | Y | **CONFIRMED** |
| `bd_c2_set.u` :40 | FFE8_FFE8_FFE8_FFE8 | INIT_c2_set (CElemFn, CElemTiming), Init.bd_c2_set | Y | Y | OK/OK | Y | **CONFIRMED** |
| `bd_c2n.u` :49 | 00B2_00B2_00B2_00B2 | INIT_c2n (CElemFn, CElemTiming, Net/HandshakeMuller), INIT_C2N (LinkHandshake), Init.bd_c2n | Y | Y (HandshakeMuller `[req_in, ack_out, c, 0]` = bd_link_ctl's a, b=c_next=ack_out, q) | OK/OK | Y | **CONFIRMED** |
| `bd_c2n_set.u` :55 (also `bd_arbcell.ustate`, ring stage) | FFB2_FFB2_FFB2_FFB2 | INIT_c2n_set, CS_INIT, C2N_SET, INIT_C2N_SET, Init.bd_c2n_set, Wip ARBCELL_INIT | Y | Y (`[r1,r2,q,rst]` = bd_arbcell `.a(r1) .b(r2)`) | OK/OK | Y | **CONFIRMED** |
| `bd_c3.u` :62 | 0000_FE80_0000_FE80, I=[a,b,c,q,rst,0] | INIT_c3, INIT_C3, Init.bd_c3 | Y | Y | OK/OK (32) | Y | **CONFIRMED** |
| `bd_c4.u` :70 | 0000_0000_FFFE_8000, I=[a,b,c,d,q,rst] | INIT_c4, INIT_C4, Init.bd_c4 | Y | Y | OK/OK (64) | Y | **CONFIRMED** |
| `bd_c2_norst.u` :81 | E8E8_E8E8_E8E8_E8E8 | INIT_c2_norst, Init.bd_c2_norst | Y | Y | OK/OK | Y | **CONFIRMED** |
| `bd_c3_norst.u` :86 | FE80_FE80_FE80_FE80 | INIT_c3_norst, Init.bd_c3_norst | Y | Y | OK/OK | Y | **CONFIRMED** |
| `bd_ctree` (N=9: tree of c4/c2…) | via bd_c2/c3/c4 | CTree c2r/c3r/c4r | Y | Y | (as above) | Y | **CONFIRMED** (LUT level) |
| `bd_arbiter.ustate` bd_arb.v:245, LUT6_2 | FFF0_FFB2_ACAC_ACAC, I=[r1,r2,q,rst,A0,1], O6=q, O5=R0 | ST_INIT, INIT_HELD, ARB_ST, Init.arb_state, Wip ARBITER_INIT | Y | Y; O6↔q, O5↔R0 in every use | OK/OK (32): q = rst + (A0 ? q : C(r1,~r2)); R0 = r1.q + r2.~q | Y | **CONFIRMED** |
| `bd_arbiter.ugrant` :249 / `bd_arbcell.ugrant` :91, LUT6_2 | 0C0C_0C0C_A0A0_A0A0, I=[r1,r2,q,0,0,1], O5=g1, O6=g2 | GR_INIT, INIT_GRANTS, GRANT, Init.arb_grant | Y | Y; O5↔g1, O6↔g2 in every use | OK/OK (g1=r1.q, g2=r2.~q) | Y | **CONFIRMED** |
| `bd_arbiter.ua1/ua2` (= bd_c2) | 00E8… | C2_INIT etc. | Y | Y (I0=g_k, I1=A0, I2=A_k, I3=rst) | OK | Y | **CONFIRMED** |
| `bd_latch.u` pair :38, LUT6_2 | FF33_CC00_B8B8_B8B8, I=[d_i,en,q_i,d_j,q_j,1], O5=q_i, O6=q_j | PAIR, INIT_PAIR, Init.latch_pair | Y | Y | OK/OK (32) | Y | **CONFIRMED** |
| `bd_latch.u` odd :44 | B8B8_B8B8_B8B8_B8B8, I=[d,en,q,0,0,0] | ODD, INIT_LAT, Init.latch_odd | Y | Y | OK/OK | Y | **CONFIRMED** |
| `bd_latch_rst.u` :66 (INIT from localparam ternary) | 00B8… (RESET_VALUE bit 0) / FFB8… (bit 1), I=[d,en,q,rst,0,0] | RST0/RST1 (Latch), Init.latch_rst0/1 | Y (both alternatives) | Y | OK/OK | Y (W=2, RESET_VALUE=2 elaborates both) | **CONFIRMED** |
| `bd_delay` LUT1 :126/:135, LUT2 SIDE_INIT :138 | 2'h2; 4'h8 (FASTFALL) / 4'hE (FASTRISE), I=[s[i], a] | BUF, FF_SIDE, FR_SIDE (Bundling); Init.delay_buf/and/or | Y | Y (stage 0 `Gate BUF [(s 0)] (s 1)`, side `[(s i),(s 0)=a]`) | OK | Y | **CONFIRMED** |
| `bd_datamux.u` pair :209 / odd :215 | FFAA_5500_E4E4_E4E4; 8'hE4 | Init.datamux_pair/odd (Core/Lut only, no cell proof uses them) | Y | Y | OK (hdr) | Y | **CONFIRMED** (constant only) |
| `bd_link_dctl` ub/ua/uld/ult bd_link.v:171-190 | F320…, FA80…, 0F08…, 0101… | INIT_DB/DA/DLD/DLT (LinkHandshake) | Y | Y. Specialisations: rst=0; uld I1 = s = 1 (LDN=0, as the Lean states); ult I2 = `if broad then ack else 0` = RTL `gate` generate | OK/OK (Lean equations checked on the rst=0 [, s=1] rows) | Y (BROAD=1/0, LDN=0/2) | **CONFIRMED** |
| `bd_link` (bd_link_ctl = bd_c2n + bd_latch + bd_delay) | as above | LinkHandshake, LinkTimed, Net/Ring, HandshakeMuller | Y | Y | — | Y (both `BD_LINK_DC` settings) | **CONFIRMED** (LUT level) |
| ring stage (cells/tb/tb_ring.v) | bd_c2n / bd_c2n_set with a=c[i-1], b=c[i+1] | Net/Ring `c2nsetB (s prv) (s nxt) (s i) rst` | Y | Y | — | n/a (tb) | **CONFIRMED** |
| `INIT_UNHELD` 0xFFB2FFB2ACACACAC (ArbHandover) | not in RTL (the RTL has only the held node) | — | n/a | pins as ustate | I derived it from "O6 = rst + C(r1,~r2), O5 = r1.q + r2.~q, I4 ignored" and get the same constant | n/a | **CONFIRMED as stated** (a hypothetical cell, correctly labelled as not shipped) |
| `xor2` 0x6 (Core/Lut, hazard example) | none | — | n/a | n/a | n/a | n/a | not an RTL transcription (equal in value to `bd_flink_ctl.uck` only by coincidence) |

Cells with LUTs but **no Lean counterpart**. Their INITs pass my
RTL-header truth-table checks (TT hdr OK), and yosys matches them:

| Cell | LUTs | Lean |
|---|---|---|
| `bd_steer` | u 8888_8888_2222_2222 (req0=req.~s, req1=req.s), uack E | none |
| `bd_bd2dr` | u 8888…2222… (f=req.~d, t=req.d) | none |
| `bd_dr2bd` | u EEEE…B2B2… (d=maj(t,~f,d), either=t+f), uor E | none |
| `bd_src` | LUT1 1 (req=~ack) | none |
| `bd_mem` | ubuf LUT1 2 | none |
| `bd_merge` | uor E, usel E (+ bd_c2 acks, datamux) | none (acks/datamux constants only) |
| `bd_mux` | uj0 0000_AE08_0000_AE08 = ~rst.C(x_req, ctl_req.~s), uj1 EA80 = ~rst.C(y_req, ctl_req.s), uor E | none |
| `bd_mlink_ctl` | ux F9 = rst+~(done^ack), uz AA82 = s.(rst+~(done^ack)) | none |
| `bd_flink_ctl` | uck 06 = ~rst.(done^ack), uq E2 = ck?done:req_in | none |
| `bd_delay_gated` | LUT1 2, LUT2 8 with I1=gate | none (Bundling models bd_delay's tap from `a`, not `gate`) |

For all of these, `PROGRAM.md` lists the cell as Phase-2 work, and
`JOURNAL-B.md` records the probes Lib1 (bd_ctl/merge/mux) and Lib2
(bd_end/mem/mlink) only as *launched*. **The journals make no proof claim for
any cell in this table, so no proved cell lacks a Lean counterpart.**

## 2. Method details and what each check covers

- **RTL parser.** It strips comments, then reads module bodies, every
  `LUTk`/`LUT6_2 #(.INIT(...))` instance and its named `.Ix/.O/.O5/.O6`
  connections. It evaluates an INIT that is a literal, a `localparam` or a
  ternary to the set of possible values; `bd_latch_rst` gives {00B8…, FFB8…}
  and `bd_delay` SIDE_INIT gives {8, E}. Both `ifdef` arms are read.
- **Lean parser.** It strips comments and reads these forms:
  - every `def X : Nat := 0x…`;
  - every `def x : Lut k|Lut62 := ⟨0x…#n⟩`;
  - inline `initTbl 0x…` and `Nat.testBit 0x…`;
  - every call `lutB|lutK|o5B|o6B|o5K|o6K|.gate|Gate INIT [pins]`;
  - every `X(.o5|.o6).(k)eval (bvec|kvec [pins] k)`.

  It found 81 hex constants. Five of them are proof bitmasks, not INITs, and
  were skipped: `mask1-3` and `dmask0/1`. `ArbHandover.MASK` is written in
  decimal, so the hex pattern never picks it up; it is a reachability bitmask,
  not an INIT. It found 202 call sites:
  - 187 with a concrete INIT, all matched;
  - 13 with an INIT that is a parameter of a generic lemma;
  - 2 calling INIT_UNHELD.

- **Generic-parameter sites.** I checked these by hand:
  - `CElemTiming.exc init a b q r` passes pins `[a,b,q,r,0,0]` and is used
    only with c2, c2_set and c2n, all of which have that RTL map.
  - The `ArbHandover` `st`/`init` functions pass `[r1,r2,q,0|rst,a0,1]` with
    HELD or UNHELD.
  - In the Bundling generic side-stage lemmas, I0 is the chain and I1 the tap.
- **Pin comparison.** It works position by position.
  - Both sides constant: the values must be equal.
  - A Lean constant on a live RTL pin is recorded as a specialisation. All 48
    such sites are rst=0 or rst=1, a scenario value of r1/r2/en, or `s=1`
    under LDN=0.
  - A Lean variable on an RTL constant is accepted only if the output
    provably does not depend on that pin given the RTL constants (CElemFn's
    `[a,b,q,rst,u,v]` lemmas). The script checks this by enumeration.
  - Variable names are matched through an explicit role table. A few
    per-site overrides are documented in the script (`CONTEXT`):
    - the arbiter acks `cel g a fb` and `C2(g1, A0)`;
    - the node numbering of the ternary networks;
    - `HandshakeMuller` `celN r a q`;
    - scenario-only Kleene lemmas such as `bd_c2_contain`.

  Every site's verdict is `EQUAL` or `EQUAL+SPEC`. None is MISMATCH or REVIEW.
- **O5/O6.** Lean's `o5B/o5K` is `INIT mod 2^32` over I0..I4, and
  `o6B/o6K` is the full INIT with I5=1. That is the Xilinx LUT6_2 definition.
  Every Lean O5 use names g1, R0 or q_i, and every O6 use names g2, q or q_j,
  matching the RTL `.O5/.O6` nets. This includes the TernarySound `arbNet`
  nodes 5-8.
- **Truth tables.** My evaluator uses I0 as the LSB, and O5 = INIT[31:0]. I
  transcribed the claims by hand from the RTL comments and the Lean theorem
  statements; none was imported. The dctl Lean equations are checked only on
  the rst=0 rows, and on the s=1 rows for `uld`, because that is what Lean
  states. I also derived the five LUT6_2 constants (held state, unheld state,
  grants, latch pair, datamux pair) from their equations, and all five agree.
- **yosys.** For each of 33 top/parameter/define combinations, the script runs
  `read_verilog -lib cells_sim.v`, then the RTL, then
  `hierarchy -top … -chparam …`, `proc` and `write_json`. It does no
  optimisation or techmap. The combinations cover `BD_LINK_DC` and
  `bd_ctree N=9`. All 123 LUT cells reproduce a regex-parsed instance: the
  INIT, the base name of each pin net (allowing `assign` aliases such as
  `gate=ack_out` and `d=t`), and the exact set of feedback pins (pin bit ==
  own output bit).

  Two instances are not separately attributed: `bd_latch.v:126` and `:135` are
  textually identical (`LUT1 2'h2 .I0(s[i]) .O(s[i+1])`), and the netlist
  matcher credits both to :126.

## 3. Caveats (scope, not defects)

- **Logical level only.** This audit checks the logical INIT and the logical
  pin map. After place and route, nextpnr may permute the physical pins
  A1..A6 and rewrite the INIT to match. The Lean never models physical pins,
  and JOURNAL-C lists "FASM -> Lean (physical INIT after pin permutation)" as
  future work. **The physical-level equivalence is UNVERIFIED.** It matters
  for the per-pin arc numbers in ArbHandover/ArbHeldTimed/ArbA0Fork, which
  are keyed to logical I0/I2.
- **Specialisations in the models.** Many models tie `rst=0`, or `s=1` in
  `bd_link_dctl` with LDN=0. These are correct transcriptions of a
  post-reset or default-parameter configuration. They do not cover
  `LDN>0`, where `s` is a FASTFALL delay of `lt`.
- **TernarySound `arbNet`.** It models O5 and O6 of one LUT6_2 as separate
  gates. The file states this is an over-approximation, and it does not
  affect the transcription.
