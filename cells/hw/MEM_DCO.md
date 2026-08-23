# `bd_mem`'s `DCO`, measured on silicon

Board: EBAZ4205, `xc7z010clg400-1`, `aclk` = 100 MHz, nextpnr
`d216cb36a370f78a`. Harness `hw/mem_port_ps.v`, driver `hw/dco_sweep.sh`,
all points at `DSETUP=2 USE_BUFG=0`. Raw logs under
`build/hw_mem/dco_sweep/`.

## What `DCO` is responsible for

`bd_mem` manufactures a strobe from `req`, waits `DCO` `bd_delay` links, then
raises `ack`. In four-phase bundled data `ack` *means* the data lines are
valid, so `DCO` has exactly one job: cover the RAMB18E1's clock-to-out.
prjxray's `BRAM_L.sdf` puts that at 2454 ps.

## The old evidence was blind

B3 reported `DSETUP=2 DCO=11 PASS on silicon, 0/49152`. That pass could not
have gone red. `mem_port_ps` sampled `port_rdata` on `posedge aclk` once a
2-FF-synchronized `ack` was high — at least two `aclk` edges, ≥ 20 ns after
`ack` really rose, against a 2454 ps defect. Same shape as the −2587 ps race
that passed because the synchronizer was slower than the race.

`mem_port_ps` now carries a second checker, `edge_cap`, which samples
`port_rdata` on the **raw `ack` edge** — what a real bundled-data consumer
does. Both verdicts are reported, never folded together.

## The sweep

`edge_mism` / `sync_mism`, mismatches out of 49152 reads (1024 addresses ×
16 bits × 3 patterns):

| `DCO` | seed default | seed 1 | seed 2 | seed 3 |
|------:|-------------:|-------:|-------:|-------:|
| 0  | **1024** | | | |
| 1  | **1024** | | | |
| 2  | **1024** | | | |
| 3  | **1024** | | | |
| 4  | **1024** | **1024** | 0 | **1024** |
| 5  | **16**   | 0 | **512** | **32** |
| 6  | 0 | 0 | 0 | 0 |
| 7  |   | 0 | 0 | 0 |
| 8  | 0 | | | |
| 11 | 0 | | | |

`sync_mism` is **0 at every one of these 24 points**, including the ones
where the design is provably corrupting reads. That is the blindness, stated
as a measurement rather than as an argument.

## Reading it

**The failure signature is the right one.** At `DCO=0` the first mismatch is
pattern 2 (addr=data), addr `0x000`, got `0x03ff`, expect `0x0000`. `0x3ff`
is the *previous* access's address: the RAM output has not changed yet at the
`ack` edge.

**Two thirds of the walk cannot detect this at all.** Every mismatch is in
pattern 2. Walking-1 and walking-0 write the same value to every address, so
a stale read is indistinguishable from a correct one — no sampling strategy
rescues those patterns. Any future memory test that has to catch a `t_co`
violation needs a pattern whose value changes per access.

**The crossing is a band, not a number, and it is not monotone.** Seed 2 is
clean at `DCO=4` and red at `DCO=5`. Changing `DCO` changes the netlist, so
every point is a *different placement* — not one placement with more delay.
The partial counts at `DCO=5` (16, 512, 32) are what the edge of a real
setup window looks like. See the `one-route-is-a-sample` finding.

**A clean result at low `DCO` is worth much less than a red one.** The edge
checker has a resolution of its own: the routed `ack → CLK` minus
`port_rdata → D` skew at `edge_cap`, which moves with placement like
everything else. So the sweep bounds `DCO` from **below** only. Seed 2's
clean `DCO=4` is evidence about that route's checker, not about `DCO=4`.

## What to use

Keep `DCO=11`. No route went red at or above 6, the highest `DCO` at which
any route corrupted is 5, and 11 is roughly twice that. It is also the value
rule B/C derives from the SDF independently. Shortening a matched delay is
the risky direction: too short is silent PVT corruption that simulation
cannot show.

Any real design re-derives its own value against its own routed SDF over
more than one seed. These numbers are this harness's placements.

## Still open

`DSETUP` is **not** validated by any of this. A too-short `DSETUP` corrupts
what gets *written*, which is persistent and which any checker would see, so
the earlier `DSETUP=0` negative control passing is not explained by observer
blindness. Either 0 is genuinely adequate here, or the walk does not stress
the address setup window against the manufactured strobe. Unresolved.
