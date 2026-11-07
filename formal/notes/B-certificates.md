# Hold certificates: race obligations of THE target in every behaviour (shard B, 2026-11-07)

## Problem, plainly
B's RaceTablePS (185 storage nodes) says: after a storage node flips, its acknowledge comes back through a path
that is at least as slow as the node's own feedback loop, up to κ = 0.415 (g = 1). The path was taken from simulated
runs ("necessity checked in the runs only"). The question here: does the acknowledge path's delay bound hold in
EVERY behaviour of the circuit? Answer: yes, given a few local value premises per node, for 181 of the 185 rows
(once the kernel checks below pass).

## Method (Lean, standard axioms)
- `CtlChain`: a gate whose INIT is `w` whenever a set of its pins shows given values (tied pins at their constants;
  optionally its own feedback at `w`: a C-element hold) keeps `w` while those pins' sources do, delayed by each pin's
  routed band (`hold_set`, `hold_mem`).
- `CertPS`: a certificate = rows (a LUT of THE target, its controlling pin set, the held value, labels saying where
  each controlling pin's hold comes from: the cause, a static premise, or an earlier row). `certOK` (kernel decide on
  THE netlist's own gates and pin chains) + `cert_sound`: every row holds on its computed window.
- `CertMarginPS`/`CertRaceAll`: for a chain-shaped certificate, the window end is the cause plus the path's summed
  lower bands; with the RaceTablePS-style integer facts on (path ++ ack pin) vs feedback pin, `race_holds`: every read
  of the node's acknowledge pin within the node's feedback-loop upper delay after its flip sees the old value, for
  g = 1, κ ≤ 83/200, every corner. `target_races_of`: all rows of a checked list at once (one corner).
- `RaceCertPS.target_b_switch_041`: for the binding row (ulink_n_falseResult_85 stage 0) the obligation is assembled
  with `cfb_switch` into "the node rises cleanly and stays", at κ ≤ 0.41.

## Premises left per row (order-level facts for the network argument, shard C)
- the node shows its old value on `[a, e]` (it flips at `e + 1`);
- each static node (an input of a path LUT that also controls it; 0-9 per row) keeps its value on `[a, E]` with
  `E ≥ e + PS` (`PS` ≥ the path sums);
- each memory row's node shows its value on its feedback window before its hold starts;
- `a` is at least every row's collapse start.

## Data
`tools-B/ps/gen_certs_ps.py` (untrusted generator; certificates from simb dumps at corner 0) -> `Formal/Cells/
CertRowsPS(2)/Bxx.lean` (certificates, `certsNN_ok`) and `RaceAllPS(2)/Bxx.lean` (node pins, `racesNN_ok`). Batch 1:
158 rows (3-pair run), batch 2: 23 rows ((2^30, 3·2^29), (7, 3), (3, 7)); 4 rows without a certificate from these
dumps: SLICE_X4Y54.A, X4Y51.A, X16Y25.B, X16Y18.D -- their RaceTablePS episodes are power-up episodes (t = 37, 55, 55,
194 ns, while the reset is high), not post-reset ones, and are far from binding (κ 0.85-0.985).

## Not shown
The premises; the switch assembly (`cfb_switch`) for rows other than the binding one; the 4 rows; that the
episodes the certificates describe are the ones that occur (the certificate is valid whenever its premises hold,
whatever the run).
