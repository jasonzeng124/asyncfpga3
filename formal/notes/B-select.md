# B: the select race in Lean (PROGRAM.md 2026-11-15, item 4) — status and plan

## What research's rules are (read from claude/research `cells/verify/tighten.py`, 2026-11-15)
- **Rule H** (hold, :1772-1870): for a controller (a link stage's C-element) that drives latch enables, the latch's
  LATEST close (`t_en` = max over enable pins of enable route + max LUT arc) must come before the EARLIEST next
  value at any of its data pins (`t_int` = shortest path from the controller's fall through every other state node,
  mux joins included; `t_ext` = from outside via DACK); guard `max(0.2t, 200) ps`.
- **Rule I** (setup, :1888-1990): the EARLIEST close (`t_close` = up->ctl rise + ctl->up ack + up->ctl fall + min
  enable arc) must come after the LATEST data arrival from the upstream latches (+ the latch's own loop wire).
- `hold_bits.py`: per simulated run (one corner), no latch D pin moves in (P, close].
These are SDF-based, single-corner, with guards. The Lean below is for every delay in the prjxray band (g, κ).

## Lean, checked (standard axioms)
| file | theorem | says |
|---|---|---|
| `Cells/ForceTree.lean` | `force_tree`, `force_tree_minmax` | per-node value windows through LUTs forced by a SUBSET of pins (select + selected input); each pin's window shifted by its band; unforced pins may glitch |
| `Cells/SelectCapture.lean` | `select_capture` | a latch bit fed by a forcing tree captures `val m ⊕ pd` if **setup** `a m + Wd ≤ τ` (rule I) and **hold** `τ + hi e ≤ b m + lo d + 1` (rule H) |
| `Cells/SelHoldPS.lean` | `certs_ok`, `sel_ok` | 20 emitted select-hold rows of THE target (9 umux instances), each kernel-checked; κ bound per row 0.606-0.855 (median 0.694); premises (enable open on [a,e], statics, memory rows) not discharged |
| `Cells/SelectHold.lean` | `SelRow`, `selOK`, `select_hold_row` | THE target, g = 1: a row = 2 chain certificates from the latch's enable source (to the select, to the selected input) + mux `KRow` + latch `LRow`; Bool-checked; gives the hold half of `target_latch_close`'s data window through the mux |

## Measured on THE target (Python, untrusted; `tools-B/select/`)
4,185 latch bits; 1,484 capture through a mux-like LUT; 1,070 of those are not covered by any hold row yet (933
`umux*.udat`, select and inputs latches at depth 0; 69 `uselect*`, 58 `ushrsi*`, 10 `ushli*` through cones up to
depth 13).

## Plan
1. Emit `SelRow`s for the 933 umux latches: 20 done (`SelHoldPS.lean`); 674 never close in the one simulated run used, so more runs (other pairs) are needed; chains come from a structural search, not ctlcert.
2. Deeper cones (uselect/ushrsi/ushli): a forcing tree of depth > 0 = several chains + several `KRow`s; generalise
   `select_hold_row` to a list of mux rows (each reads chain ends or earlier mux rows).
3. **Rule I as a certificate.** The close is not a hold of one cause: the enable closes after the upstream request's
   fall, which follows the controller's acknowledge, which follows the request's rise (the round trip). Setup row =
   (a) a window-START bound on the data source from the upstream event (`CertPS` window `.1`, upper band sums) and
   (b) a LOWER bound on the close time τ: the enable source keeps "open" while the upstream request is high, and
   the request stays high until the acknowledge reaches it (a hold certificate on the request, cause = the
   acknowledge's old value). Composition: `winD.1 + Wd ≤ τ_min`. Same two-chain + margin-ratio form.
4. **Completeness** (with C): every latch bit of a netlist has a hold row (LatchHoldCert / SelectHold) and a setup
   row; then `target_latch_close`'s data premises are discharged for all 4,185 bits. That is the "every capture has
   a certificate ⇒ safe" statement for captures; the handshake side is C's AO certificates.
5. **For research's tool:** the same rows from a build's `.fasm` (C's margin tool) give, per select link, the κ at
   which its hold (rule H) or setup (rule I) row stops checking: research's "which race moved and by how much".
