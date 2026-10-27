# The arbitrated memory port's two matched delays, measured on silicon

Board: EBAZ4205, `xc7z010clg400-1`, `aclk` = 100 MHz, nextpnr
`d216cb36a370f78a`. Harness `hw/mem_arb_ps.v`, driver `hw/xsdb_mem_arb.tcl`,
sweeps `hw/mem_arb_dco_sweep.sh`, negative controls `hw/negctl_mem_arb.sh`.
Design under test: two bundled-data stations sharing one
`bdc_memport_arb_10_32_2`, ordered only by a program-order token.

Companion to `hw/MEM_DCO.md`, which does the same job for a bare `bd_mem`.

## The two delays

`bd_mem` manufactures a RAM clock from `req`. Two matched delays sit either
side of it, one per RAMB18E1 gang (this port has two, since `bd_mem` is 16 bits
wide and the channel is 32):

- **`USETUP`** (rule B) holds the request off until address and write data have
  reached the RAM's input pins. Too short and the RAM clocks in nothing.
- **`UCO`** (rule C) delays the acknowledge until read data has come *out* of
  the RAM. In four-phase bundled data `ack` means "the data lines are valid",
  so `UCO`'s single job is to cover the RAMB18E1's clock-to-out, which prjxray
  `BRAM_L.sdf` puts at 2454 ps.

## The harness could not see rule C at all until 2026-08-24

The first version reported PASS at every `UCO` including zero. That was a
property of the observer, not the circuit: the only consumer of the load's read
data was a two-flop synchroniser into the PS clock domain, which the host did
not sample until it had been round an AXI read — tens of nanoseconds after
`z_req` rose, against a 2454 ps defect. The data had always arrived by the time
anything looked.

More board time would not have fixed this. What fixed it was a consumer that
reads the data *when the protocol says it is valid*: `edge_cap` latches `z_data`
on the raw `z_req` edge, which is what a downstream bundled-data station does.
nextpnr routes `z_req` to that flop's clock pin through local routing — the
build still reports a single BUFG — so nothing was inserted that would delay
the capture edge and re-hide the defect.

It keeps its own verdict. A rule B failure and a rule C failure are different
defects and one pass bit would hide which fired.

## Rule C: the band

`NEXTPNR_SEED=1`, `USETUP` held at 8/8.

| UCO | P1 | P2 | edge_mism | ns/pair | |
|---:|---:|---:|---:|---:|---|
| 0 | 0 | 0 | 64 | 150.0 | rule C red |
| 1 | 0 | 0 | 64 | 150.0 | rule C red |
| 2–8 | 0 | 0 | 0 | 160.0 | ok |
| 10–12 | 0 | 0 | 0 | 170.0 | ok |

Threshold between 1 and 2 links; the shipped default is 12. Monotone, unlike
`bd_mem`'s own band.

Two things to read off the table rather than the verdict column. The latency
moves in steps with the delay (150 → 160 → 170 ns), which is the independent
evidence that the knob is actually wired to the circuit — a sweep whose rows all
come back identical has meant a *disconnected parameter* in this project before,
and it reads exactly like a structural result. And `P1`/`P2` stay 0 in **every**
row including the red ones: the data-path verdict cannot see this defect at any
`UCO`, which is the whole case for the second checker.

## Rule B: not a cliff

`NEXTPNR_SEED=1`, `UCO` held at 12/12.

| USETUP | P1 | P2 | edge_mism | ns/pair | |
|---:|---:|---:|---:|---:|---|
| 0 | 64 | 64 | 2176 | 160.0 | everything red |
| 1 | 64 | 64 | 2176 | 160.0 | everything red |
| 2 | **1** | **1** | **2** | 160.0 | **1 access in 64 fails** |
| 3–6 | 0 | 0 | 0 | 160.0 | ok |
| 7–12 | 0 | 0 | 0 | 170.0 | ok |

The `USETUP=2` row is the finding. At 0 and 1 every access fails and no test
could miss it. At 2, exactly one address in 64 fails — a **marginal zone** one
link wide where the failure rate is a fraction and depends on which address and
data pattern hit the worst path.

That explains `verify/resize.sh`'s bad answer on this port without needing a new
hypothesis. It settled `UMEM0_USETUP` at **5**, which passes here, and 5 then
failed rule B on 3 of 8 independently seeded routes. Five is two links above
this route's threshold of three, on a design whose manufactured clock arrival
moves 4325 → 5730 ps (about four links) across six seeds. A loop that shrinks a
delay until a test stops passing lands in the marginal zone by construction,
because the marginal zone passes on most single runs. **Sampling raises the bar;
only a guardband moves it.** Rule A has `max(0.2·t_data, 200 ps)`; B and C have
none, and that remains an open decision.

## What the negative controls establish

`hw/negctl_mem_arb.sh` rebuilds with one delay zeroed.

- `USETUP → 0` goes red on everything: 64/64 mismatches, `got=0x00000000`
  against `expect=0xc0d00a00`.
- `UCO → 0` goes red on the edge-sampled checker only: `edge_mism=64`,
  `got=0xbf2f0a00` vs `expect=0xc0d00a00`, with `P1`/`P2` still 0.

Read that second failing word. The low half is correct and the high half is
garbage. The two RAM gangs are the two halves, `umem1`'s manufactured clock
arrives ~285 ps after `umem0`'s, and with the delay removed only the later gang
misses the capture edge. **A clock-to-out violation does not present as a wrong
value; it presents as a half-settled one** — which any checker that samples late
will watch settle and call correct.

The broken build is also the fast one: 150.0 ns per pair against 170.0, a real
12% for data that is half-formed and a host that cannot tell. That is the
concrete shape of "shortening a matched delay is the risky direction" — the
reward is visible from outside and the damage is not.

## A note on stimulus

At `USETUP=2` the edge-sampled checker saw 2 failures in 2176 samples while the
two 64-access phases each saw 1 — meaning **all 2048 speed-loop accesses
passed**. The speed loop hammers one address with one payload: nothing toggles,
so nothing races. It contributes ~34× the samples and ~0× the coverage. Sample
count is not stress.

## NOT MEASURED: how far the threshold moves between placements

Everything above is **one placement**. The obvious follow-up — sweep `USETUP` at
seeds 2 and 3 and see where the threshold lands, since the spread between the
highest and lowest threshold is empirically the smallest guardband that would
have held — was started and **not finished**: board access ended partway
through. Seed 2 got as far as `1 → red, 2..5 → ok, 7 → ok` with point 6
unresolved; seed 3 produced no valid points at all.

Do not read seed 2's partial row as "the threshold moved from 3 to 2". It is
seven builds from a sweep that never completed, and the single most important
thing this document says is that the interesting region is exactly where single
runs are unreliable. **The cross-seed guardband number is unmeasured and the
next person with a board should get it.** One command:

```
WHAT=usetup NEXTPNR_SEED=<n> hw/mem_arb_dco_sweep.sh 1 2 3 4 5 6 7
```

A point that prints `INCONCLUSIVE` means the board never answered — re-run it.
It does not mean red. An earlier version of the script scored those as failures
and produced a convincing fake non-monotone band.
