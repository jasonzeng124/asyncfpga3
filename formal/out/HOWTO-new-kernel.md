# HOWTO: run the event-level checker (and the X/hazard audit) on a new kernel

From a compiled kernel to a verdict. Done so far for three kernels besides gcd:

- collatz (probe K2, 2026-10-27, `formal/notes/A-k2.md`): scripts in `k2/`;
- ipow and xorshift (probe K3, 2026-10-29, `formal/notes/A-k3.md`): scripts in `k3/`, which take
  the kernel name as an argument. **Start from `k3/`**; `k2/` is kept as the first worked example.

The gcd_hw runs that came first are in `formal/notes/A-xaudit-gcd.md` (xaudit),
`A-events6.md` (xevents5), `A-events7.md` and `A-events8.md` (xevents7/8).

Two tools come out of this. Each answers a different question, and neither replaces the
`cells/` gates or routed GLS.

| tool | input | question | engine (proved) / front end (untrusted) |
|---|---|---|---|
| `xevents8` (preferred; `xevents7`, `xevents5` are its predecessors) | the control skeleton of the routed netlist, its bands, a certificate | for EVERY behaviour of the routed netlist (any environment choices), does every control stage obey the event-count (handshake) discipline? | `Events8*.lean` (on top of `Events7*`, `Events6*`) / `events8/cert8.py` (untrusted: Lean re-checks it) |
| `xaudit` | flattened routed netlist, per-arc bands, a stimulus | for this ONE stimulus, can any storage node see X or a hazard, for any delays in the bands and any power-up state? | `Formal/Core/XAudit/{Design,Untimed,Fast}.lean` / `Main.lean` parser + printer (trusted) |

All script paths below are relative to `formal/tools-A/xaudit/`.

## 0. Rules that apply before anything

- Toolchain: `cells/verify/toolchain.sh` must exit 0 before every build, or nothing routed is a
  result. Record the nextpnr sha256 it prints (9c732bc6303458df for every number so far).
  `k3/build_k3.sh` runs it before every seed and stores the output next to the route.
- In a cloud sandbox, restore the cached toolchain rather than building it. The key is
  `cloud/toolchain-cache.sh key`. Do **not** use `cloud/toolchain-cache.sh fetch` from a probe:
  it runs `git fetch` and `git update-ref` (state-changing git). If the branch
  `origin/toolchain-cache/<key>` is already in the clone, read it instead:

      TC=~/dev2/lib/fpgatoolchain
      git ls-tree --name-only origin/toolchain-cache/<key> | grep '^part-' | sort | \
        while read p; do git cat-file blob origin/toolchain-cache/<key>:$p; done | \
        zstd -dc | tar -C $TC.tmp -xf - && mv $TC.tmp $TC     # (mkdir -p $TC.tmp first)
      apt-get install -y zstd iverilog libtcl8.6 libboost-python1.83.0 \
        libboost-filesystem1.83.0 libboost-program-options1.83.0   # the binaries need these at run time
      cells/verify/toolchain.sh      # 9/9 "ok"; toolchain.sh cannot see missing libraries
      ldd $TC/openxc7/bin/nextpnr-xilinx | grep "not found"    # must print nothing

  Several probes may restore at once: unpack into a temporary directory and `mv` it, under a
  `flock` (K3 used `/tmp/tc-restore.lock`), so nobody runs a half-unpacked nextpnr.
- Never build in the shared tree. Export it: `git archive HEAD | tar -C ~/k3src_<k> -xf -`
  (`k3/build_k3.sh` does this, and records the revision in `.k3-rev`). A `git worktree add`
  writes into `.git`.
- Routes, arcs and netlists stay outside the repo (`~/k3out/<k>/<seed>/`). Commit only small
  result text (`k3/out/`).
- **ONE nextpnr at a time** on a 4-core machine shared with Lean: wrap every build in
  `flock /tmp/nextpnr.lock …`.
- Always pass `--freq` (`NEXTPNR_FREQ=100`, build_hw.sh's knob; `build_k3.sh` sets it). The
  rig's only clock is the readback/housekeeping `tck`; its "PASS at 100 MHz" is not a kernel
  number, but without `--freq` the route is made against nextpnr's 12 MHz default.
  (collatz in K2 was built without it.)
- One route is a sample: use 4 placer seeds that place AND pass the `cells/` audits (§2). A seed
  that does not place, or fails an audit, is reported, not hidden, and replaced.
- Every Lean process runs under `formal/slot.sh`. Do not run `lake build` yourself.

## 1. A design the tools can cut

The front end (`routed2x.py`) keeps every cell under one instance prefix and cuts at flip-flop
outputs and at named nets. What it needs from the design:

- a **closed handshake environment** around the kernel inside that prefix. The kernel's input
  requests and output acknowledges must be driven by LUT logic in the cut, not by flip-flops.
  A free input that is a request breaks the event checker's assumptions. The gcd_hw rig
  (`cells/hw/gcd_rig.v`) is that environment: a `bd_fork` to the inputs, two C-elements
  (`uenv0`/`uenv1`) closing the ring, and a padded `out0_req` (`urdly`);
- the **operands from flip-flops** (a vector ROM indexed by an FF register), so that synthesis
  cannot fold the datapath, and so that they become a few free inputs (`idx[3:0]`);
- the **reset as one net** (`rig_rst`) that can be named with `--cut-net`;
- a **self-check** (a mismatch against the C-derived expected value, then `ok`/`err`), so the
  xaudit run says something about the answer and not only about X.

For a kernel with **two 32-bit inputs plus `start`** (ipow `b, e`; xorshift `seed, rounds`),
`k3/gen_rig.py <k> OUTDIR` writes `<k>_rig.v` and `<k>_hw.v`: collatz_rig's ring with a 3-way
fork, and a 16-entry ROM `{expected, a, b}` whose expected values it computes from a Python
transcription of `kernels/<k>/<k>.c` (32-bit wrap, the C's signed/unsigned shifts). Add a kernel
by adding its function and vector list to the `K` table; check the transcription against the C by
hand, never against a run. For other port shapes copy `k2/collatz_rig.v` (one input) or edit
gen_rig.py. **[kernel]**: the DUT module, the port names (read them from the emitted
`build/gen/<k>_kernel.v`), the fork width and the ROM. Pick a vector 1 that finishes in a few loop
iterations and whose answer is not 0.

`cells/hw/build_hw.sh` has no case for a new rig. `k3/build_k3.sh` adds one to the exported copy
only. The case is the gcd_hw case with the kernel swapped: emit the kernel, and map a sizes
file's `BD_SZ_URIG_UDUT_<INST>` macros onto the kernel's `DELAY_<INST>` parameters.

## 2. Build, 4 seeds, audit

    flock /tmp/nextpnr.lock k3/build_k3.sh <k> d 3 4 5   # SRC=~/k3src_<k> OUT=~/k3out/<k>; 1-2 min per seed
    # = from the export's cells/: [NEXTPNR_SEED=N] NEXTPNR_FREQ=100 BD_SIZES=<sizes> \
    #     BDC_SELECT_PADS=<{}> BD_RLOC=v4 ./hw/build_hw.sh <k>_hw
    k3/audit_k3.sh <k> d 3 4 5                           # the cells/ audits, one line per seed

- Sizes: use route-measured sizes if they exist (`research/data/<k>_*sizes_T*.vh`, renamed
  `BD_SZ_UUT_*` -> `BD_SZ_URIG_UDUT_*`, harness `BD_SZ_UPIPE_*` lines dropped). They were measured
  on another harness, so re-audit them on these routes. Check that every sized name matches a
  `DELAY_` parameter of the emitted kernel; parameters the file does not size keep emit.py's
  defaults (ipow: 17 of 67, all non-compute links).
- **DSP48E1** (ipow's `muli`): BD_DSP defaults to 1, so the multiplies are DSP48E1s. Fine for the
  build; see §3 for the netlist.
- **Seeds that do not place.** `ERROR: post-placement validity check failed for Bel
  'SLICE_X0Y../A5FF'` is a known nextpnr legality failure (collatz seed 3, xorshift seeds 4 and 6,
  gcd_hw R5 seed 2). Report it and take the next seed.
- The bitstream step fails without python `textx` (build_hw.sh exits 1 after `fasm_audit
  PASS`). Nothing here needs a bitstream; check `fasm_audit PASS` and `0 group(s) dropped` in the
  log instead of the exit code.
- The audits (`audit_k3.sh` runs exactly these; the rig's housekeeping ring has to be declared):

      python3 verify/tighten.py SDF --osc dhk --osc invhk   # rules A/H/I/F/B/C; D is a one-sided screen
      python3 verify/skew.py SDF                            # rule E (what rule D defers to)
      python3 verify/arb_fork.py SDF

  tighten.py exits 1 whenever rule D's screen flags something (8 on ipow and xorshift, the
  `ucond_br*` steers; rule E then measures all of them as met). Read the per-rule counts, not the
  exit code. **A route with a rule A, H, I or F violation is not a result**: xorshift seeds 3
  (rule A −52 ps, rule I −177 ps) and 7 (rule A −339 ps) failed, as CLAUDE.md says rebuilds of the
  shipped xorshift do about 2 times in 8. Replace them (K3 took 8 and 9) and say so.
- Record the md5 of every `<k>_hw_routed.json` and `<k>_hw.sdf`, and the nextpnr sha256
  (`k3/out/builds.txt` is the format).

## 3. Per-arc delays and the xaudit netlist

    git show 7dc5dde:cells/gls/fid/xray_delay.py > ~/k3tools/xray_delay.py   # md5 3e69bf6a
    pip install --target ~/k3tools/pylib simplejson intervaltree
    k3/bands_k3.sh <k> d 3 4 5        # xray_delay.py (~1-2 min/seed), then the netlist at 4 corners

- Use research **7dc5dde** (or later) of `xray_delay.py`. The older 801db02 (md5 99b10a6d, used
  for every committed gcd_hw band file) omits the slice OUTMUX hop on O5 / F7 / F8 / CARRY4
  outputs (62..231 ps per arc); see `notes/A-e8mux.md`, which found 7dc5dde equal to its fixed
  calculator on every comb->comb arc.
- `xray_delay.py` needs `XRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7` and
  `PYTHONPATH=$TC/openxc7-src/prjxray:~/k3tools/pylib`. Its default DB path does not exist in the
  cloud image.
- The netlist builder is `k3/routed2x_k3.py`, generated by `k3/mk_routed2x_k3.py` from the current
  `routed2x.py` plus one option (bands_k3.sh regenerates it on every run):
  - `--cut-type DSP48E1_DSP48E1` (bands_k3.sh passes it for ipow): `routed2x.py` rejects a DSP48E1
    as "not combinational". With the option the DSPs become hard cells whose outputs are FREE
    inputs. Event-checker verdicts hold for every waveform on a free input, so this is sound for
    them; `k3/skel_dsp_check.py net.json skel.json` reports whether the control skeleton reads one
    (on ipow it reads none: its 7 inputs are `rig_rst` and 6 select-data nets). For xaudit, a free
    product means a datapath answer through the DSP is not checked.
  - Without `--cut-type` its output is byte-identical to routed2x.py's (checked on xorshift d).
- `--inverted hull`: prjxray has rows with FAST_MIN > FAST_MAX on a few pins. routed2x.py now
  rejects them (exit 1) unless `--inverted hull`, which takes [min, max] and lists the rows in the
  report (before E8Mux they were written lo > hi and the Lean reader narrowed them to [lo, lo]).
  bands_k3.sh passes hull. On ipow/xorshift they occur at the fast corner only, on data-latch or shell arcs, none in the
  control skeleton.
- Check the routed2x report:
  - **free inputs** must be exactly the FF-driven operands, the reset, and (with --cut-type) the
    cut cells' outputs. Anything else (a request, an acknowledge) means the environment is not
    inside the cut;
  - `CARRY4 ... model floor`: paths where the 1-step-per-element model is faster than the real
    lo. This is the documented sub-step imprecision.
- Corners, one band per element:

| corner | band | meaning |
|---|---|---|
| `slow` | [SLOW_MIN, SLOW_MAX] | the whole die at the slow corner (H_ONE_CORNER) |
| `fast` | [FAST_MIN, FAST_MAX] | the whole die at the fast corner (H_ONE_CORNER) |
| `indep` (mixed) | [FAST_MIN, SLOW_MAX] | each element anywhere in sign-off range, independently. Physically pessimistic |
| `gb` | slowmax --widen 0.332 = [0.668 SLOW_MAX, SLOW_MAX] | the `skew.py` guardband ratio GUARD_LO/GUARD_HI |
| `slowmax --widen w` | [(1-w) SLOW_MAX, SLOW_MAX] | precision sweep only. w = 0 is one delay assignment, NOT a sign-off band |

Never mix corners inside one analysis, except as the labelled `indep` row.

## 4. Build the checkers without `lake build`

None of the executables imports Mathlib, so this works while Mathlib is still compiling.

    k3/mk_k3.sh          # XAUDIT_OLEAN=~/k3olean: the 34 modules of xaudit, xevents5 and xevents8,
                         # one at a time through ../lean.sh (slot.sh); ~10-40 min on a busy machine
    NATIVE=1 XAUDIT_OUT=~/k3xa k3/mk_k3.sh   # + native xaudit (only for xaudit)

- Check every per-module log (`~/k3olean.<module>.log`) for `error` and `sorry`: there must be none.
- `../lean.sh` mirrors `formal/lean/.lake/build/lib/lean/Formal` into the overlay as symlinks;
  that directory must exist (any partial lake build creates it).
- `build.sh` alone fails to link (`undefined symbol: initialize_formal_Formal_Core_XAudit_Parse`):
  its module list predates `Parse.lean`. `mk_k3.sh NATIVE=1` adds Parse and relinks. Before using
  a native binary, check it: it must reproduce `results/pipe3_slow_corner.txt` byte for byte.
- The run scripts call `lean --run Formal/Core/XAudit/Events8Main.lean` (interpreted) on the
  overlay. When the lake build has the `[[lean_exe]]` targets, `lake exe …` replaces this.

## 5. xevents8: the event-level verdict, all seeds and corners

    k3/run_events_k3.sh <k>   # SEEDS="d 3 4 5" CORNERS="slow fast indep gb" CHK="8 5" NEG=1; -> k3/out/<k>/
    k3/table_k3.sh <k> "d 3 4 5" > k3/out/<k>/table.txt
    # per seed x corner:
    #   python3 events4/skel.py net.json C.bands.json skel.json skel_C.bands.json
    #   python3 events8/cert8.py skel.json skel_C.bands.json cert8_C.json
    #   xevents8 skel.json skel_C.bands.json cert8_C.json --fuel 256
    #   (CHK=5 adds events6/cert6.py + xevents5 for comparison; events5/ana5.py, untrusted, always)

- Run at most 2 `lean --run` jobs at once (`J=2`). Parallel runs have produced empty outputs.
  table_k3.sh prints `EMPTY OUTPUT` for such a row; rerun it.
- A full kernel (4 seeds × 4 corners × 2 checkers + 5 negative controls) took about 30 min on a
  machine also building Mathlib.
- Pass `--fuel F` larger than the longest pin path. The default of 64 is too short for collatz
  (65- and 73-element paths: `RECOG-FAIL` and `NOT RECOGNISED` at 64). Any fuel is sound, because
  `Recog6 … fuel` is the hypothesis whatever the value. The k3 scripts use 256.

What every accepted row prints, and must print: `Design.WF true; Recog6 node failures 0;
Net4.OK7 true`, `derivation log: … accepted by runLog: true`, cert8 `errors 0`, and `select
partitions (SelPart): [...]` (empty = SelPart vacuous).

The last line of an xevents8 run is the verdict:

- **`VERDICT CLEAN (Events8.design_verdict8; hypotheses: per-pin SatPin, H_ARB, SelOK, SelPart,
  HDsub (n judgements))`**. This is an instance of `Events8.design_verdict8` about every behaviour
  of the parsed netlist: every real control node's output equals the phase of its event counter.
  Hypotheses:
  - `SatPin`: each LUT reads each input pin through its own monotone delay in the gate's band,
    and each routed arc is in its band. The bands are prjxray's, through the trusted parser;
  - the constant wires and the reset (`hrst`: one held pulse from t = 0);
  - `H_ARB`: the arbiter cores behave as the virtual mux cores (NOT checked);
  - `SelOK`: the bundling of the selects (the `skew.py` rule E question, not proved here);
  - `SelPart`: the pattern groups of one multi-bit select are never true together;
  - `HDsub`: 2 count inequalities per guarded pin (labelled walks from the guarded source through
    SUB), computed by the checker; open (`notes/A-events8.md`).

  GuardOK is NOT a hypothesis: each guarded pin carries a Lean-checked guard certificate
  (BACK-G, ENTRY, EXIT1, EXIT2, LINE, strict margins). It does not cover: the datapath values;
  the answer; metastability; anything outside the bands; another route; `skel.py` itself.
- **`VERDICT RECOGNISED, RESIDUAL n`**: recognised, but n items have no certificate that checks.
  Each is printed as `RESIDUAL Back|Line|Excl|Guard … margin m` and becomes an extra hypothesis
  (for a guarded pin: GuardOK for that pin).
  - A margin ≤ 0 is a timing finding: the bound the certificate needs fails at this corner. 0 is
    a FAIL (strict margins).
  - "no certificate" is a gap in what cert8/Lean can express.
- **`VERDICT NOT RECOGNISED`**: `Design.WF`, `Recog6` or `Net4.OK7` failed (`RECOG-FAIL` lines).
  Nothing is claimed.

xevents5's CLEAN (`Events6.design_verdict`) additionally assumes GuardOK and does not check guarded
pins, so an xevents5 row can be CLEAN or have fewer residual items where xevents8 has guard items.
xevents8 can also certify line pins xevents5 cannot (cert7/cert8 try every R3 candidate): on ipow
d indep it certified 21/23 lines against xevents5's 17/23.

**Negative controls (must be rejected)**, run by `run_events_k3.sh` on seed d slow:

| control | mutation | expected |
|---|---|---|
| NEG-fb5000 | +5000 ps on an arbiter's own-feedback arc (`k2/negctl_k2.py` finds the pin from the netlist; nextpnr permutes LUT pins per route, so gcd's hard-coded `/I0` is wrong) | `RESIDUAL Back <that cell> … margin < 0` |
| NEG-recog | certificate: one node's `qi := ri` | `RECOG-FAIL`, `NOT RECOGNISED` |
| NEGnoguard | `cert8.py --no-guard` | every guarded pin `RESIDUAL Guard … no certificate` |
| NEGentry | +GPS on both bounds of one guarded pin's arc | that pin `RESIDUAL Guard … ENTRY < 0` |
| NEGexit | +GPS on the hi of that stage's guard-pin arc | that pin `RESIDUAL Guard … EXIT2 < 0` |

**Make every defect larger than that item's margin.** Two controls failed to fail at first:
collatz's NEG-fb at gcd's +1500 ps (stage margin 2054 ps), and ipow's NEGentry/NEGexit at gcd's
+5000 / +18000 ps (that pin's ENTRY margin was 8312 ps and EXIT2 37219 ps: the margins include
the walks through the delay lines). The k3 defaults are 5000 ps (feedback) and GPS = 60000 ps.

## 6. xaudit: one transaction, X/hazard verdict

    k2/run_xaudit_k2.sh       # SEED=d; slow/fast/slowmax w=0,0.02,0.05; then gcd/fbrace.py
    # = xaudit net.json --bands C.bands.json --stim k2/v1_220ns.stim.json --timed-only --all
    #   then python3 gcd/analyze.py on the report (it reads the rig_* names, kernel-independent)

(Not yet run on ipow or xorshift. For ipow with `--cut-type DSP48E1_DSP48E1` the products are free
inputs, so the answer cannot be certified; the X/hazard verdict on the control still means
something.)

- Stimulus: `{"horizon_ps": H, "init": {"rig_rst": 1, "idx": 1}, "events": [{"t_ps": 20000,
  "set": {"rig_rst": 0}}]}`. Choose H from a concrete run (`gcd/csim.py --mode hi --strobe
  rig_lap`) plus margin. The memory is about (number of wires) × (H / 25 ps) cells.
- Step size matters on long transactions. Rounding adds up to one step per element, and it
  accumulates. On collatz, slowmax w = 0 failed to certify at 25 ps and certified at 10 ps
  (`--unit-ps 10` in routed2x.py, same netlist). Memory scales as wires × steps: 2.25 GB for
  10.8k wires × 22k steps.
- What a result means (`A-xaudit.md`): for every delay assignment inside the bands and every
  power-up state, each storage node's value is the printed one outside the printed X windows.
  - "clean" / power-up windows are not flags.
  - `STORED X POSSIBLE` is any 0→X→1 longer than `--xmax` (2 ns). Read the window before
    calling it storage.
  - `UNRESOLVED` and `GLITCH` are real losses of precision or real hazards. The analysis cannot
    tell which.
  - A data-latch bit that is X for the whole run is a latch this transaction never writes.
- The analyze.py summary gives `rig_lap`, `rig_res_data`, `rig_ok` and `rig_err` where they are
  binary. **A certified transaction** means: rig_lap binary 1 at a time, rig_res_data binary and
  equal to the C answer, rig_ok = 1 and rig_err = 0 over intervals. That holds for every delay
  in the bands, for this one vector, from this reset.
- `gcd/fbrace.py net.json C.bands.json` (untrusted) lists storage nodes whose own feedback can
  be slower than the fastest neighbour response. It is a race candidate list.

## 7. Shell pitfalls seen in these probes

- `until ! pgrep -f "<script name>"` never ends when the waiting shell's own command line
  contains the name. Wait on an output file instead (`until [ -s out.txt ]`).
- Do not edit a bash script while a run of it is in progress: bash reads the file as it goes.

## 8. What to write down

The table per seed and corner: the xevents8 verdict line, its RESIDUAL items with margins, the
xevents5 and ana5 verdicts for comparison; the negative-control results with the defect sizes;
the toolchain fingerprint; the md5s; every seed that did not place or failed an audit. State
what each verdict assumes (§5). None of it is a silicon claim.
