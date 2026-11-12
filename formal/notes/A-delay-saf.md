# A-delay-saf: the GLS's "sample at fire" delay channel, formalized

Probe: formalize the delay rule that `A-gls-compare.md` §1 found in the research GLS LUT
(an iverilog specify path), and compare it with the sound channels. Namespace
`Formal.Core.DelaySAF`. Discrete time (ℕ, 1 step = 1 ps), Lean core only. It imports
`Formal.Core.Trace.Discrete` (`Sig`, `Tr`, `delay`, `Transport`, `pulse`, `inertial`,
`exists_tr`, `transport_comp`, `transport_mono`, `inertial_min_width`, ...) and copies none of it.

## What checks

`formal/lean/Formal/Core/Delay/SAF.lean`: no errors, no warnings, no
`sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`. `#print axioms` (run on a scratch copy
in `/tmp/delay-saf/`) gives at most `propext, Classical.choice, Quot.sound`.

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    ../slot.sh lake env lean Formal/Core/Delay/SAF.lean

As a sanity check, `#eval` (scratch, not committed) reproduces the GLS numbers in
A-gls-compare:
- input pulses 1000–1010 and 1120–1130 at d = 124 give output edges `[1124, 1134]`;
- a 124 ps pulse passes, with edges `[1124, 1248]`;
- a 123 ps pulse gives no edges.

### The model

- `fireB d x t`: an update fires entering step `t+1` iff the input changed entering step
  `t+1-d`.
- `saf d x`: the output starts at `x 0`. At a fire step `t+1` it becomes `x t`, the value
  *just before* the fire step. Otherwise it holds. Nothing is cancelled.
- Tie convention: when an input change and a fire fall on the same step, the fire sees the
  old value. This is the only convention that reproduces the GLS's measured "w = d passes"
  step. It is also the convention `channel_fit.py`'s `model_saf` uses ("an input edge AT u
  not yet seen"), and that model scored 140/140 on the GLS.

### Theorems (each corresponds to an item of the probe)

**(1) Bridge to pure delay.**
- `saf_eq_delay_iff : saf d x = delay d x ↔ Faithful d x` is exact. `Faithful d x` means
  that every fire copies the value its own change set: `x (k+1) ≠ x k → x (k+d) = x (k+1)`.
- `faithful_of_spaced`, `saf_eq_delay_of_spaced`: if no two changes of the input are closer
  than d steps (`Spaced d x`, d ≥ 1), then SAF is exactly the pure delay d.

**(2) Isolated pulses.**
- `saf_pulse_long`: a pulse of width w ≥ d passes, delayed by d, with its width unchanged.
- `saf_pulse_short`: a pulse of width w < d vanishes.
- `saf_pulse_eq_inertial : saf d (pulse a p w) = delay 1 (inertial (d-1) (pulse a p w))`.
  The right-hand side is `Trace.Discrete`'s inertial delay. Its window convention is offset
  by one step, so it rejects widths ≤ d−1 and SAF rejects widths < d. In continuous terms
  this is `InertialRD d d` with ties passing.

**(3) Early propagation and runts.**
- `saf_early`: for every 1 ≤ ε < d, the witness `early d ε` rises at 1, falls at d and
  rises for good at s = 2d−ε.
  - The input's last change is at s.
  - The SAF output differs from the final value at every t < s+ε, and equals it from s+ε on.
  - The pure delay still shows the old value at s+d−1.
  - So the output settles ε after the edge that sets its final value, for any ε in [1, d).
- `saf_runt`: two input pulses `[1,1+w)` and `[d,d+w)`, both narrower than d, produce exactly
  one output pulse `pulse false (1+d) w`. This holds for every 1 ≤ w ≤ d−2.
- `saf_runt_not_inertial`: that output is not `delay 1 (inertial (d-1) i)` for **any** input
  `i`. The proof uses `inertial_min_width`.

**(4) Soundness against bounded delay.**
- `saf_transport : Transport 1 d x (saf d x)` (d ≥ 1). SAF is contained in the sound FIFO
  transport channel with band [1, d], and the read-time map `gsaf` is monotone.
  `saf_window` is the window form: the output at t equals the input at some u in
  [t−d, t−1].
- `saf_not_transport`: for d ≥ 2, `¬ Transport lo hi (early d 1) (saf d (early d 1))`
  whenever lo ≥ 2 and hi ≤ 2d−2. This includes every band [lo, d] with lo ≥ 2.
- So [1, d] is the exact discrete band. **The GLS per-LUT delay d is an upper bound only. Its
  lower bound is one time quantum (0⁺ in real time).** The probe expected the window
  [0, d]; the proved result is slightly sharper, [1, d]: a fire never copies a same-step
  change.

**(5) Settle times and bundled data.**

Throughout, `SettledFrom s T` means `∀ t ≥ T, s t = s T`.

| theorem | statement |
|---|---|
| `settle_of_transport` | any `Transport lo hi` behaviour settles no later than the pure delay `hi` does |
| `saf_settle_le_delay` | one LUT: if `delay d x` is settled from S, then `saf d x` is settled from S. **GLS settle ≤ pure-delay settle** |
| `chain_settle_le_delay` | a 2-LUT chain (LUT 2 = any `g : Bool → Bool` of LUT 1): the same inequality, via `transport_comp` (band [2, d1+d2]) |
| `chain_early` | **the reverse fails.** For d ≥ 2: GLS chain settled from 2d+d2; pure-delay chain not settled from 2d+d2 (it settles at 3d−1+d2). The GLS calls the data valid d−1 steps early |
| `net_settle_static` | a 2-LUT network with side input b on LUT 2: the GLS output settles by `max(Ta+d1, Tb)+d2`, the static-timing bound |
| `xor_settle_late` | **in a reconvergent network even "GLS ≤ transport" fails.** LUT 2 = XOR, side input = the pure-delay image of LUT 1. The pure-delay output is constant; the GLS output still moves at 3d−1+d2. So the chain inequality is a chain property, not a network property |
| `net_eq_delay_of_faithful` | **trust condition.** If, in the GLS run, LUT 1's function value and LUT 2's function value `f(y1, b)` are each `Faithful` for their d, then the GLS network output **equals** the pure-delay network output |
| `net_eq_delay_of_spaced` | the same, with the stimulus condition "each LUT's function value never changes twice within its d" |

## The statement the research branch can act on

1. **A GLS run is trustworthy, meaning identical to the pure-delay run with the same SDF
   delays, if every LUT update fires with the value its own scheduling change produced.**
   Equivalently, no LUT's zero-time function value changes again within d of a change.
   - This is checkable on the GLS trace itself (`Faithful` is a property of the GLS
     signals).
   - A monitor in `prims.v`: at each specify-path fire, compare the copied value with the
     value recorded when the update was scheduled, and flag every mismatch.
   - A run with zero flags is exactly the transport run.
2. **When flags occur, the GLS margin is not trustworthy in either direction.**
   - On a chain it is optimistic: by up to d−1 per glitching LUT (`chain_early`), which
     is the dangerous direction under CLAUDE.md.
   - With reconvergence it can be pessimistic as well (`xor_settle_late`).
   - The only bound that survives is the static one, `net_settle_static`: a margin taken
     against T_in + Σd is sound for the GLS.
   - Do not take margins from observed GLS settle times on glitchy cones.
   - Alternatively, switch LUTs to transport (`always @(f) o <= #d f`).
3. **Hazard-freedom claims backed by a GLS run are not affected.** `saf_transport` makes
   every GLS behaviour a `Transport 1 d` behaviour, so it lies inside any Causal/Ternary
   soundness result stated for transport channels.
   - Runt-freedom claims are affected: `saf_runt_not_inertial`. A GLS run shows runts that
     no inertial channel shows.
   - Delay lower-bound claims are affected: `saf_not_transport`.

## Fidelity

- **SAF vs the GLS.** The model is a single d per LUT, for both edges and all pins.
  - That matches `gen.py`'s `(d:d:d)` single-number SDF.
  - Per-pin and rise/fall arcs are not modelled: Wip W1. There the fire order can cross,
    which no FIFO channel does, so the W1 transport claim may need an extra hypothesis.
  - The tie convention was checked against the GLS step at w = d (A-gls-compare §2).
  - The model has not been run against `channel_fit.py`'s random traces from Lean.
    Test: export `edges (saf d x)` from Lean `#eval` for the same traces and diff.
- **SAF vs silicon.** SAF is not a silicon model. Its zero-latency edges and full-swing runts
  are unphysical (A-gls-compare §1). It is formalized so that GLS results can be read
  correctly, not so it can be used as a model.
  - The sound silicon envelope is still `Transport lo hi` with lo > 0 (Delay/Pure,
    Delay/Corner).
  - `saf_transport` says the GLS is inside the envelope [1, d] but not inside [lo, d] for
    lo ≥ 2. So it explores behaviours silicon cannot have (too-early edges), and it may miss
    ones silicon can have.
- **Discrete time.**
  - One step is 1 ps, which is iverilog's timescale in the GLS.
  - The real-time version (left-limit sampling, band [0⁺, d]) is stated in Wip W2 and not
    proved.
  - `Discretize.lean`'s bridge would carry `saf_transport` to real time only through its
    `Sep` hypothesis. That hypothesis excludes exactly the glitch bursts that matter here,
    so a direct real-time proof is the right route.

## What does not check / open (`formal/lean/Wip/DelaySAF.lean`, `sorry`)

- W1 `safRF_transport`: per-value delays (rise/fall arcs).
- W2 `safR_chan`: the real-time SAF is inside `DelayPure.Chan 0 d`.
- W3: n-LUT chains and arbitrary DAGs. For DAGs, `net_eq_delay_of_faithful` generalizes by
  topological induction.

## Verdict

**Works.** All five items are proved in discrete time, with explicit witnesses.

**Effort to finish:**
- W1 and W3: about 1 day.
- W2 (real time): about 1 day.

**What it buys:** a precise, checkable criterion for when the research GLS's timing numbers
are the transport numbers (the `Faithful` monitor), and proofs that outside that criterion:
- GLS margins are neither upper nor lower bounds;
- the GLS shows runts no inertial channel shows;
- the GLS violates any delay lower bound above one quantum.
