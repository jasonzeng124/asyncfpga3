# A-fidelity: how faithful each model is, for every primitive except the LUT core

Shard A. The LUT mux tree has its own probe (`A-lut-tree.md`). This note
covers everything else: routing, the LUT input pins and output, MUXF7/F8,
CARRY4, the FFs and the latch. `FEASIBILITY.md` asks how faithful each
primitive's model is, and §3 is that table.

Files:
- `formal/lean/Formal/Core/Fidelity.lean`: **proved**. It checks cleanly: no sorry, admit, axiom,
  native_decide or bv_decide. `#print axioms` on `mem_path`, `elmore_mono`, `mem_hop` and
  `le_widen` lists only `propext`, `Classical.choice` and `Quot.sound`.
- `formal/lean/Wip/Fidelity.lean`: not proved. It holds the pulse-filter and involution channel
  shapes. It has one `sorry` (`boundedTransport_passes`), and the rest of it checks.

Check command (the only output is the deprecation warning on `Mathlib.Data.Real.Basic`):

    cd formal/lean && ../slot.sh lake env lean Formal/Core/Fidelity.lean

## 1. Sources (all read, nothing assumed)

- `prjxray/prjxray/timing.py` (f4pga/prjxray master). It models an RC tree of
  Outpin / Buffer / PassTransistor / Wire / Inpin. Buffers and Outpins are roots. Buffers
  and Inpins are leaves. A Buffer shows its upstream only its `in_cap`, and a
  PassTransistor passes its whole downstream C upstream. Wires are pi-models: their
  own R sees C/2. `utils/create_timing_worksheet_db.py` gives the delay to a sink at
  corner k as **Σ intrinsic_k(element) + Σ R·C_downstream**. The RC sum is a
  single number that does not depend on the corner. Only the intrinsic part has corners.
- prjxray-db `zynq7/` (xc7z010clg400-1, the same speed grade as the board, -1).
  - Pip data is `delay=[fast_min, fast_max, slow_min, slow_max]` (ns), `res` (Ω)
    and `in_cap` (fF). So R·C·1e-6 is in ns, which `prjxray/tile.py` confirms with its /1e3 scaling on each.
  - **All 3737 INT_L pips have `is_pass_transistor = 0`**: every programmable
    interconnect pip is modelled as a buffer.
  - The only pips marked pass-transistor are the 88 (CLBLL_L) and 93 (CLBLM_L) fixed
    tile-wire → site-pin connections (IMUX→A1, CTRL→SR, LOGIC_OUTS, COUT→COUT_N).
    They have `delay=null` and `res=0`, so they carry no electrical element.
  - Typical INT pips (slow max / fast min):
    - IMUX_L: 0.138 / 0.038 ns, R = 1611 Ω, in_cap 7.7 fF.
    - Singles and doubles (xxBEG): 0.12–0.19 / 0.033–0.07 ns, R = 1.16–1.58 kΩ, in_cap 8.4–10 fF.
    - Long (LV/LH): 0.301 / 0.108 ns, R = 757 Ω.
  - Wires: `res` 45–79 Ω for CLB-adjacent wires, C 4.7–13 fF.
  - Site output pin drive R: A–D 1.3–1.45 kΩ, AMUX 1.85 kΩ, AQ 1.43 kΩ, COUT 0.69 kΩ.
- prjxray-db `zynq7/timings/CLBLL_L.sdf`.
  - **The two triples on every IOPATH are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`,
    not rise/fall.** This is confirmed in `utils/makesdf.py` line 63. The Vivado dump
    (`fuzzers/007-timing/bel/runme.tcl`) asks only for DELAY, FAST_MAX, FAST_MIN,
    SLOW_MAX and SLOW_MIN, so prjxray has **no rise/fall data at all**.
  - **TIMINGCHECKs (setup, hold, recovery, removal) are written only for the SLOW corner**
    (makesdf.py, `({SLOW_MIN}::{SLOW_MAX})`).
- `origin/claude/research:cells/gls/prims.v` and `README.md`: today's GLS.
- `research/PROGRAM.md`: the board-fidelity GLS plan.
- `research/JOURNAL.md` at 02:21: workstreams F1–F4 have started. None has
  committed a model yet.

## 2. Which cells use which primitive

The census below is a grep of `cells/rtl/*.v` plus the synthesis flow.

| primitive | where it comes from | in which cells / designs |
|---|---|---|
| LUT1–LUT6, LUT6_2 | hand-instantiated, `(* keep *)` | every control cell: `bd_ce` (C-elements), `bd_link`, `bd_ctl`, `bd_mux`, `bd_merge`, `bd_end`, `bd_arb`, `bd_latch` (LUT latches and the LUT1/LUT2 matched delay lines), `bd_mlink` (LUT3/LUT4) |
| routing (INT pips, wires) | the router | everything. The README says the median wire is 720 ps against 124 ps of logic, so routing is most of every delay |
| MUXF7 / MUXF8 | yosys `synth_xilinx` (no `-nowidelut`) inferring them from wide muxes | **no hand-written cell.** They appear only in the bdc-emitted datapath cones (wide `?:` and selects) and in rig logic (`gen_bench.py`: lat_ctr → mux7/mux8 tree) |
| CARRY4 | yosys inference of `+`, `-`, `<`, `==` | **no control cell.** Datapath adders and comparators (`bdc/emit.py` emits a behavioural `xa > xb`; README: "a CARRY4 chain"). gcd's subtractors use `PRECYINIT_CONST` |
| FDRE | inferred `always @(posedge ck)` | `bd_mlink` bank (one FDRE per bit, clock = fabric net `ck`, `-noclkbuf`). It is not integrated: every other cell is four-phase. Also in rig counters (1044 FDRE in one bench) |
| FDSE | inferred | rig: gcd_hw's `rst_sr` (20 of 247 flops) |
| FDCE / FDPE (async SR) | `always @(posedge aclk or negedge aresetn)` | **only in the PS-side `*_ps.v` shells** (the AXI clock domain). No async-SR flop is in an asynchronous cell |
| LDCE (slice latch) | not used | `bd_latch.v` puts storage on LUTs on purpose, because LDCE.G uses the slice CLK pin (see its header) |
| BUFG / RAMB18E1 / DSP48E1 | `bd_mem` (BUFG or LUT1 clock buffer, RAMB18E1), DSP via `BD_DSP=1` | out of scope here |

So the C-element, latch, link, arbiter and delay-line proofs need only:
**LUT core (other probe) + LUT input pins + LUT output + routing**.
CARRY4 and MUXF7/8 matter only for the *bundling constraint* of datapath cones.
FFs matter only for `bd_mlink` and the rigs.

## 3. The per-primitive fidelity table

The **band** is prjxray's `[fast_min, slow_max]`, so an element with
`delay=[a,b,c,d]` gets `DelayBound.ofCorners` = `[a, d]`. "RC" is the Elmore
term from `timing.py`. The hypothesis names are the Lean argument names a
circuit theorem should take (proposed). `Formal.Core.Fidelity` gives the
interval algebra they plug into.

| # | primitive | what the silicon is | faithful channel abstraction (and why) | proposed Lean hypothesis + interval (xc7z010-1, ns) | today's GLS (`cells/gls`) | where formal model and GLS disagree | how to test |
|---|---|---|---|---|---|---|---|
| R1 | **buffered pip** (every INT pip on this part) | config-SRAM-selected mux followed by a restoring CMOS buffer that drives the next wire | **Bounded transport for pulses wider than `wpass`.** A pulse narrower than `wkill` may vanish, and one in between may come out as a runt (X). The restoring stage plus its RC load is a low-pass followed by a threshold, which is inertial-ish but not ideal inertial: the faithful binary model is an involution channel (Függer et al.). `wkill ≈ 0.69·τ` with τ = R_drv·C_down ≈ 1.5 kΩ × 15–50 fF ≈ 20–75 ps, so `wkill` is about 15–50 ps per hop. The width change per hop, \|t_rise − t_fall\|, is **not in prjxray** (no rise/fall data) | `H_pip : BoundedTransport (hop intr κ lo hi …)` with `intr = ofCorners pip.delay`: e.g. IMUX [0.038, 0.138], single [0.033, 0.19], long [0.108, 0.301], plus RC `[κ·Elmore_lo, Elmore_hi]`. Valid only for pulses ≥ `wpass`, a named parameter (≈ 3·τ_max + band width until measured) | one `ICBUF` per sink pin carrying nextpnr's single number (pip max + one lumped RC from a guessed Manhattan length). Baked build: **transport** (`-DGLS_TRANSPORT_IC`). Annotated build: inertial specify path. Corners are ×0.9 / ×1.1 only | (a) **Band:** GLS uses one point. The formal band is 3–4× wide (IMUX 0.038 → 0.138). (b) **Fanout:** prjxray adds ~8–10 fF of `in_cap` for each enabled downstream pip, about +10–15 ps per extra sink at the driver. nextpnr has no fanout term. (c) **Narrow pulses:** GLS transport passes pulses of any width. Silicon kills those under ~15–50 ps. This matters only for liveness arguments that rely on a narrow pulse arriving, which no current four-phase cell does | GLS: research F1's hand cases (one pip, chain, fanout-N). Board: the n=128 rings put this die's point inside the band. **Pulse-shrink experiment:** XOR a signal with a k-LUT1-delayed copy to make a pulse of tunable width, send it through N hops into a toggle-FF counter, and sweep k for the smallest surviving width and the shrink per hop (the method of carry-chain TDC papers) |
| R2 | **pass-transistor pip** | on this part only fixed tile-wire→site-pin aliases (`delay=null`, `res=0`). The INT mux's internal NMOS pass-transistor tree is inside the "buffered pip" of R1 | Zero-delay alias (prjxray). Physically, a static pass-transistor or RC network driven by a monotone edge has a **monotone** response: for RC networks with grounded C, the impulse response is nonnegative (Metzler/M-matrix argument), so a chain of on-transistors **cannot create a glitch** from a clean edge. It only slows the edge and low-pass filters it, and with a threshold receiver it can **swallow a runt** (yes, inertial-ish). The NMOS weak-1 nonlinearity is restored by the buffer | `H_alias : y = x` (zero delay). The monotone-response claim is stated as an informal placeholder in Wip; it needs exp/ODE, which is outside the built Mathlib | no cell: pins wired directly | none on this part | not separately observable. It is lumped into R1 measurements |
| R3 | **wire** (R, C) | distributed RC line | No channel of its own: its R and C go into the driver's Elmore term (pi-model). As a low-pass, it adds to R1's rejection window | `RC` sections in `elmorePi`, with ranges `LeRC lo x`, `LeRC x hi`. Model factor `hmodel : κ·elmore x ≤ t ≤ elmore x`. Elmore is an upper bound on the 50 % delay of an RC tree (Gupta–Tutuianu–Pileggi 1997). κ = 0 is always sound. prjxray/Vivado use κ = 1 and are ±1.5 % from Vivado | inside nextpnr's lumped number | prjxray's R and C do not depend on the corner (only the intrinsic part has corners), so the formal `rcBound` widens it explicitly (`widen ε`, κ) | per-wire scatter from the ring data (research F3) |
| R4 | **LUT input pins A1..A6** (the input buffers of the LUT) | the site pin's buffer feeding the select lines of the mux tree | bounded transport (single input change), same as R1 | `H_lutpin_i : ofCorners` from the **site-pin Inpin intrinsic**: A1 [0.172, 0.516], A2 [0.170, 0.507], A3 [0.107, 0.344], A4 [0.086, 0.284], A5 [0.033, 0.112], **A6 [0.002, 0.005]** | not modelled separately. LUT arcs are a flat 124 ps on every pin | **Large, and worth checking first:** prjxray keeps the pin dependence of a LUT **in the site input pin** (up to 0.516 ns slow on A1 against 0.005 on A6). The LUT6 cell arcs are flat (0.100/0.124 slow on every pin; A-lut-tree notes this too). If nextpnr-xilinx drops the site-pin intrinsic, every A1/A2 arc in today's GLS is short by up to ~0.4 ns at the slow corner. The order A6 ≪ A5 < A4 < A3 < A2 ≈ A1 also supports A-lut-tree's inferred order (A6 at the root, A1 at the leaves) | grep nextpnr-xilinx's chipdb or arch for site-pin delays. Board: a ring through one LUT, rerouted to each A_i with the same routing (A-lut-tree proposes the same experiment) |
| R5 | **LUT output** (O6 / O5 → site pin A/AMUX) | output driver | bounded transport. Its R is the Elmore root | O6→A: LUT6 arc [0.045, 0.124] (all pins). O5: [0.042, 0.154]. →AMUX route-through pip [0.069, 0.211]. Drive R 1.33 kΩ (A), 1.85 kΩ (AMUX) | flat 124 (O6), 116–153 (O5). **inertial** specify path | GLS swallows any LUT output pulse narrower than ~124 ps. Silicon passes pulses down to ~tens of ps. **GLS hides LUT hazard glitches that silicon would propagate** (research PROGRAM already lists this) | GLS: rerun each passing design with transport LUT outputs. Any change of outcome means the design depends on glitch semantics and needs an explicit hypothesis |
| M1 | **MUXF7** (SELMUX2_1 F7AMUX/F7BMUX) | 2:1 mux on the LUT outputs inside the slice, then a buffer | data inputs: bounded transport. **Select with D0 = D1:** hypothesis `H_muxf_kleene`, meaning no output glitch (a break-before-make pass gate floats and holds its value, make-before-break shorts equal levels). It is the same hypothesis as the LUT's `H_mux_kleene` | D→OUT [0.053, 0.193] (F7A) / [0.062, 0.223] (F7B). S→OUT [0.085, 0.276] / [0.093, 0.296] | zero-time `?:` + inertial specify 104/104/273. With S = X and D0 = D1, `?:` gives D (Kleene) | GLS is Kleene-exact and inertial. Silicon behaviour on an S toggle with D0 = D1 is unverified. MUXF7 sits only in datapath cones, where a glitch is harmless under the bundling constraint (see C1) | board: D0 = D1 = 1, toggle S at ring rate, count OUT falls with a ripple counter (expect 0) |
| M2 | **MUXF8** | same, one level up | same as M1 | D→OUT [0.019, 0.104], S→OUT [0.080, 0.273] | 104 / 273, inertial | as M1 | as M1 |
| C1 | **CARRY4** (MUXCY ×4 + XORCY ×4) | dedicated carry chain: muxes and XORs inside the slice | **Not a transport channel.** On a multi-input change the chain glitches (ripple), which is ordinary in silicon. The faithful *and sufficient* abstraction for a bundled-data cone is **bounded settling:** "from the last input change at t, the output equals f(inputs) on [t + hi, next change). Before that it is arbitrary, X included". Proofs then need only `hi` per arc. Glitches are allowed, and the matched delay covers them | `H_carry_settle` with per-arc `hi` from the SLOW max, e.g. CIN→CO3 0.114, S0→CO3 0.508, CYINIT→O3 0.642, DI0→CO3 0.526, S0→O3 0.582 (`lo` is unused). `PRECYINIT_CONST` is a named parameter of the function | zero-time functional model + inertial specify (nextpnr numbers, the same values as prjxray slow max). `cin0 = CIN \| CYINIT` | GLS filters ripple glitches narrower than the arc delay. Harmless under bounded settling. The formal model would disagree only if some cell used a CARRY4 output as a control or enable signal. None does | GLS: transport vs inertial on CARRY4 must not change the outcome of any bundled cone. Board: count CO3 glitches (toggle-FF counter) during an operand change, as a sanity check that glitches exist and the settle bound covers them |
| F1 | **FDRE / FDSE CK→Q** | master-slave flop | given setup/hold met: Q takes D after a bounded delay (transport, one edge) | `H_ckq : ofCorners` FF_INIT CLK→Q [0.099, 0.303] (REG_INIT_FF: [0.112, 0.340]) | specify `posedge CK => Q`, TCKQ from nextpnr's patched chipdb | band against a single point | ring of FFs (toggle) per corner point |
| F2 | **FF setup / hold** | sampling window | `H_window`: if D and CE are stable on [t − setup, t + hold], Q = D. Otherwise Q ∈ {0, 1, X} **for an unbounded time** (metastability), and only a probabilistic bound holds. That is out of scope for proofs: a design must make the window structurally unreachable | SLOW only: DIN setup −0.057/−0.046 (negative), hold 0.181/0.225. CE setup 0.088/0.109, hold −0.011/−0.009. **No FAST-corner window in prjxray**, and hold usually binds at FAST: this is a gap and needs a named hypothesis `H_hold_fast` (or a Vivado lookup) | a behavioural check: a D/CE change within TSU before or THD after CK makes Q = X. `TSU > 0` is guarded, so the negative setup is ignored | GLS checks [t_ck, t_ck + THD], which covers the true window [t + 0.046, t + 0.225]. Conservative, but only at the slow-corner numbers | board: skew sweep on `bd_mlink`'s bank, data against ck with delay-line taps, to find the capture window |
| F3 | **async SR (FDCE/FDPE), SR→Q** | async set/reset path | bounded transport + recovery/removal window | SR→Q [0.182, 0.552] (QH), [0.233, 0.764] (QL). RECOVERY 0.358/0.404, REMOVAL −0.248 (slow only) | **not modelled:** SLICE_FFX treats SR as synchronous (FDRE/FDSE only). Correct for every cell, since FDCE/FDPE exist only in the PS-side `*_ps.v` | none for the async cells | none needed for the cells |
| L1 | **LDCE** (slice latch) | not used (see `bd_latch.v`) | — | REG_INIT_LAT D→Q [0.073, 0.264], G→Q [0.129, 0.443] are recorded for completeness | — | — | — |

## 4. What the Lean file proves (exact names, `namespace Formal.Core.Fidelity`)

**Interval algebra** (`DelayBound`: `lo hi : ℝ`, `0 ≤ lo`, `lo ≤ hi`)
- `DelayBound.series` (interval sum) satisfies `series_assoc`, `series_comm`, `zero_series` and `series_zero`.
- `mem_series`: a delay in `a` plus a delay in `b` lies in `series a b`.
- Containment `Le`: `Le.refl`, `Le.trans`, `Mem.of_le`, and **`series_mono`** (series is monotone in both arguments).
- `path` (a list of hops). **`mem_path`** is the bridge: hop delays in hop bounds ⇒ path delay in the path bound. Also `path_append` and `path_mono`.

**prjxray corners**
- `Corners` takes a 4-tuple with its ordering as hypotheses. `ofCorners` gives `[fast_min, slow_max]` and `slowOnly` gives `[slow_min, slow_max]`, with `slowOnly_le_ofCorners`.
- `widen b ε` gives `[lo(1−ε), hi(1+ε)]`, and `le_widen` shows it contains `b`.

**Elmore delay**
- `RC`, `totalC`, `elmore` (L-sections) and `elmorePi` (prjxray's pi-model).
- **`elmore_mono`**: pointwise larger R and C with a nonnegative start ⇒ the Elmore delay is no smaller. It covers every R and C at once. `elmore_mono_R` and `elmore_mono_C` are the single-element versions.
- `elmorePi_mono`, `elmorePi_le_elmore`, `elmore_nonneg`, `totalC_mono`, `Nonneg.of_le`.

**From R/C ranges to a bound**
- `rcBound κ … lo hi` with **`mem_rcBound`**, and `hop` (intrinsic in series with RC) with **`mem_hop`**.
- The hypotheses `hlo`, `hhi` (the real R and C lie in their ranges) and `hmodel` (the real RC delay lies in `[κ·elmore, elmore]`) are explicit arguments.

**Trace level**
- `BoundedTransport b x y`: an order-preserving, onto warp with per-instant delay in `b`.
- **`boundedTransport_series`**: two such channels in series form one with the `series` bound.
- `boundedTransport_widen`.

A sanity `example` checks prjxray's IMUX corners and one Elmore value (1.4765 kΩ × 28.14 fF).

## 5. What does not check yet, and why

- `Wip/Fidelity.lean: boundedTransport_passes` (`sorry`): proving that a transport channel passes
  every pulse with its width changed by ≤ hi − lo needs the warp to be continuous at the pulse
  edges. `BoundedTransport` does not require that yet. About 0.5 day.
- `PassesWide` (pulse-filter envelope) and `Involution` are stated as shapes only. The trace
  semantics of an involution channel (cancellation of pending edges) is not written. 2–4 days,
  and it is the faithful binary model.
- RC-network monotonicity and runt rejection (the R2/R3 physics) need `Real.exp` and linear ODEs,
  which are outside the built Mathlib subset. They stay a cited fact plus a named hypothesis.
- **The corner-correlation hypothesis is the important missing piece** (see verdict).

## 6. Verdict

**Works.** The bridge from prjxray numbers to proof hypotheses is proved and small. Every
assumption it makes is an argument.

The work exposes one structural obstacle for bundled-data proofs. The sound per-element band
`[fast_min, slow_max]` is 3–4× wide (IMUX: 0.038 → 0.138 ns). A matched delay checked
element-by-element against the whole band (data path at slow max, delay line at fast min) will
almost never close. Real margins come from **tracking**: on one die at one moment, every element
sits near the same point in its band. The next Lean step should therefore be a corner-parametrised
bound:
- `d_e(s) = lerp(fast_e, slow_e, s)·(1 ± ε_e)` with one shared `s ∈ [0,1]`.
- Theorems quantify over all `s` and take `H_track : ε ≤ ε_max` as a hypothesis.
- `ε_max` is sized from the n=128 ring scatter, which research F3 is measuring.

This is about 1 day on top of `Fidelity.lean`: series composition commutes with fixing `s`.

## 7. Disagreements to hand to the research branch (check which side is wrong)

1. **SDF triple meaning.** The two triples in prjxray-db `timings/*.sdf` are (FAST)(SLOW)
   (`utils/makesdf.py`), but standard SDF reads two triples as (rise)(fall). If F1 or `gen.py`
   feeds those files to iverilog or any SDF reader unchanged, every rise gets the fast corner and
   every fall gets the slow one. `research/PROGRAM.md`'s wording "cell arcs with rise/fall,
   fast/slow" suggests this misreading is a live risk. prjxray has no rise/fall data at all.
2. **LUT pin dependence lives in the site-pin Inpin delay** (A1 up to 0.516 ns slow, A6 0.005).
   Check that nextpnr-xilinx's chipdb, and F1's calculator, include it. If today's SDF lacks it,
   A1/A2 arcs are short by up to ~0.4 ns.
3. **Setup/hold exist only at the SLOW corner.** Hold at FAST is unmodelled in both prjxray and
   today's GLS.
4. **RC term has no corner** in prjxray, and Vivado's R and C do vary with PVT. Do not apply the
   ×0.9/×1.1-style scaling only to the intrinsic part and call the result a corner.
5. **Inertial cell paths** (LUT, MUXF, CARRY4, FF) in GLS against the formal envelope (narrow
   pulses may pass). GLS hides hazards. The cheapest check is the transport-vs-inertial A/B
   rerun of each passing design (R5).
6. **Fanout loading** (+~10 ps per extra enabled sink pip at the driver) is in prjxray's Elmore
   term but not in nextpnr's.

## 8. Effort and value

- **Done:** about 2.5 h.
- **Remaining:**
  - Corner-parametrised bounds with tracking: about 1 day.
  - `boundedTransport_passes`: about 0.5 day.
  - Involution-channel trace semantics: 2–4 days.
  - A Python check that sums prjxray-db numbers along a routed path and emits the
    `DelayBound` literals for a cell's hypotheses: about 0.5 day. It would reuse `timing.py`,
    and the research F1 calculator could feed it directly.
- **What it buys:**
  - Every delay hypothesis a cell theorem takes now has a documented, mechanical source (a
    prjxray tuple + Elmore + an explicit ε/κ), and a theorem that composing hops keeps soundness.
  - The table gives each primitive its abstraction: transport for routing and pins, bounded
    settling for CARRY4/MUXF in datapath cones, a window-or-metastable hypothesis for FFs.
  - Items 1–4 of §7 are concrete, checkable risks for the board-fidelity GLS being built now.
