# HOWTO: run the formal X/hazard audit and the event-level checker on a new kernel

From a compiled kernel to a verdict, in the order it was first done for a second kernel
(collatz, probe K2, 2026-10-27; `formal/notes/A-k2.md`). The gcd_hw runs that came first are in
`formal/notes/A-xaudit-gcd.md` (xaudit) and `formal/notes/A-events6.md` (xevents5).

Two tools come out of this. Each answers a different question, and neither replaces the
`cells/` gates or routed GLS.

| tool | input | question | engine (proved) / front end (untrusted) |
|---|---|---|---|
| `xaudit` | flattened routed netlist, per-arc bands, a stimulus | for this ONE stimulus, can any storage node see X or a hazard, for any delays in the bands and any power-up state? | `Formal/Core/XAudit/{Design,Untimed,Fast}.lean` / `Main.lean` parser + printer (trusted) |
| `xevents5` | the control skeleton of that netlist, its bands, a certificate | for EVERY behaviour of the routed netlist (any environment choices), does every control stage obey the event-count (handshake) discipline? | `Events6*.lean`, `Events5.lean` / `cert6.py` (untrusted: Lean re-checks it) |

All script paths below are relative to `formal/tools-A/xaudit/`. The collatz scripts in `k2/`
are the worked example; copy them and change the names marked **[kernel]**.

## 0. Rules that apply before anything

- Toolchain: `cells/verify/toolchain.sh` must exit 0 before every build, or nothing routed is a
  result. Record the nextpnr sha256 it prints (9c732bc6303458df for every number so far).
- In a cloud sandbox, restore the cached toolchain rather than building it. The key is
  `cloud/toolchain-cache.sh key`. Without touching the shared tree:

      git ls-tree --name-only origin/toolchain-cache/<key> | sort | \
        while read p; do git cat-file blob origin/toolchain-cache/<key>:$p; done | \
        zstd -dc | tar -C ~/dev2/lib/fpgatoolchain -xf -
      apt-get install -y zstd iverilog libtcl8.6 libboost-python1.83.0 \
        libboost-filesystem1.83.0 libboost-program-options1.83.0   # the binaries need these at run time
      cells/verify/toolchain.sh      # 9/9 "ok"; toolchain.sh cannot see missing libraries

- Never build in the shared tree. Export it: `git archive HEAD | tar -C ~/k2src -xf -`
  (`k2/build_k2.sh` does this). A `git worktree add` writes into `.git`.
- Routes, arcs and netlists stay outside the repo. Commit only small result text.
- One route is a sample: use 4 placer seeds. A seed that does not place is reported, not hidden.
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

For collatz this was `k2/collatz_rig.v`: gcd_rig.v with `bdc_collatz`, a 2-way fork (`n`,
`start`), no probe ports, and a ROM of `{expected, n}` computed from `kernels/collatz/collatz.c`.
The shell `k2/collatz_hw.v` is `cells/hw/gcd_hw.v` minus the gcd-only abs/cmp probes, so the
cut has the same shape: free inputs `idx[3:0]` and `rig_rst`. **[kernel]**: the DUT module, the
port names (read them from the emitted `build/gen/<k>_kernel.v`), the fork width and the ROM.
Pick a vector 1 that finishes in a few loop iterations and whose answer is not 0.

`cells/hw/build_hw.sh` has no case for a new rig. `k2/build_k2.sh` adds one to the exported
copy only. The case is the gcd_hw case with the kernel swapped: emit the kernel, and map a
sizes file's `BD_SZ_URIG_UDUT_<INST>` macros onto the kernel's `DELAY_<INST>` parameters.

## 2. Build, 4 seeds

    k2/build_k2.sh d 4 5 6          # SRC=~/k2src OUT=~/k2out; ~30 s per collatz seed
    # = from the export's cells/: [NEXTPNR_SEED=N] BD_SIZES=<sizes> BDC_SELECT_PADS=<pads> \
    #     BD_RLOC=v4 ./hw/build_hw.sh <top>

- Sizes: use route-measured sizes if they exist (collatz: `research/data/collatz_sizes_T3.vh`,
  renamed `BD_SZ_UUT_*` -> `BD_SZ_URIG_UDUT_*`). They were measured on another harness, so
  re-audit them on these routes.
- The bitstream step fails without python `textx`. Nothing here needs a bitstream.
- Audit each route with the `cells/` gates and record the counts. The rig's housekeeping ring has
  to be declared:

      python3 verify/tighten.py SDF --osc dhk --osc invhk   # rules A/H/I/F...; D is a screen
      python3 verify/skew.py SDF                            # rule E
      python3 verify/arb_fork.py SDF

- Record the md5 of every `<top>_routed.json` and `<top>.sdf`, and the nextpnr sha256.

## 3. Per-arc delays and the xaudit netlist

    git show origin/claude/research:cells/gls/fid/xray_delay.py > ~/k2tools/xray_delay.py
    pip install --target ~/k2tools/pylib simplejson intervaltree
    k2/bands_k2.sh "d 4 5 6"        # xray_delay.py, then routed2x.py at 4 corners

- `xray_delay.py` needs `XRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7`. Its default path
  does not exist in the cloud image.
- `routed2x.py ROUTED --xray-arcs arcs.tsv --corner C --out net.json --bands C.bands.json
  [--keep-prefix urig.] [--cut-net rig_rst]`. Check its report:
  - **free inputs** must be exactly the FF-driven operands plus the reset. Anything else (a
    request, an acknowledge) means the environment is not inside the cut;
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

Neither executable imports Mathlib.

    XAUDIT_OLEAN=~/k2olean k2/mk_k2.sh              # every dependency, through lean.sh/slot.sh
    NATIVE=1 XAUDIT_OUT=~/k2xa XAUDIT_OLEAN=~/k2olean k2/mk_k2.sh   # + native xaudit

`build.sh` alone fails to link (`undefined symbol: initialize_formal_Formal_Core_XAudit_Parse`):
its module list predates `Parse.lean`. `mk_k2.sh NATIVE=1` adds Parse and relinks. Before using
a native binary, check it: it must reproduce `results/pipe3_slow_corner.txt` byte for byte.

When the lake build has the `[[lean_exe]]` targets, `lake exe xaudit` / `lake exe xevents5`
replace this. The k2 run scripts use `.lake/build/bin/<exe>` if it exists, and otherwise
`lean --run Formal/Core/XAudit/<Main>.lean` (the same code, interpreted).

## 5. xevents5: the event-level verdict, all seeds and corners

    k2/run_events_k2.sh       # SEEDS="d 4 5 6" CORNERS="slow fast indep gb"; writes k2/results/
    # per seed x corner:
    #   python3 events4/skel.py net.json C.bands.json skel.json skel_C.bands.json
    #   python3 events6/cert6.py skel.json skel_C.bands.json cert_C.json
    #   xevents5 skel.json skel_C.bands.json cert_C.json
    #   python3 events5/ana5.py skel.json skel_C.bands.json      (untrusted, comparison only)

Pass `--fuel F` larger than the longest pin path. The default of 64 is too short for collatz's longest pin
paths, 65 and 73 elements: collatz printed 4 `RECOG-FAIL` lines and `NOT RECOGNISED` at 64, and
none at 256. Any fuel is sound, because `Recog6 … fuel` is the hypothesis whatever the value.

The last line of an xevents5 run is the verdict:

- **`VERDICT CLEAN (Events6.design_verdict; hypotheses: per-pin SatPin, H_ARB, SelOK, GuardOK)`**
  This is a theorem about every behaviour of the parsed netlist. Every real control node's output
  equals the phase of its event counter, under these hypotheses:
  - `SatPin`: each LUT reads each input pin through its own monotone delay in the gate's band,
    and each routed arc is in its band. The bands are prjxray's, through the trusted parser;
  - `H_ARB`: the arbiter cores behave as the virtual mux cores (NOT checked);
  - `SelOK`: the bundling of the selects (the `skew.py` rule E question, not proved here);
  - `GuardOK`: the guarded-pin timing (W-E4g, open).

  It does not cover: the datapath values; the answer; metastability; anything outside the
  bands; another route. The reset must be one held pulse from t = 0 (`hrst`).
- **`VERDICT RECOGNISED, RESIDUAL n`**: the netlist was recognised (`Recog6` true and `Net4.OK`),
  but n items have no certificate that checks. Each one is printed as `RESIDUAL Back|Line|Excl
  ... margin m`, and each becomes an extra hypothesis of `design_verdict`.
  - A margin ≤ 0 is a timing finding: the bound the certificate needs fails at this corner.
  - "no certificate" is a gap in what cert6/Lean can express. Known classes on gcd: U3 labels
    through reconverging merges, n-ary merges, the arbiter cascade, guarded delay-line pins.
- **`VERDICT NOT RECOGNISED`**: `Design.WF`, `Recog6` or `Net4.OK` failed (`RECOG-FAIL` lines).
  Nothing is claimed.

Negative control (must fail). Add 1500 ps to one arbiter's own-feedback arc and re-run:

    python3 k2/negctl_k2.py skel.json skel_slow.bands.json NEG.bands.json <arbiter ua2 cell>

`events4/negctl.py` hard-codes gcd's pin name. nextpnr permutes LUT pins per route, so
`negctl_k2.py` finds the feedback pin from the netlist.

Make the defect larger than that stage's measured margin. On collatz, +1500 ps (gcd's value) left
the stage CLEAN at margin 554 ps, and +3000 ps gave `RESIDUAL ... margin -946`. Also mutate the
certificate (`qi := ri` on one node): Recog6 must print `RECOG-FAIL` and `NOT RECOGNISED`.

## 6. xaudit: one transaction, X/hazard verdict

    k2/run_xaudit_k2.sh       # SEED=d; slow/fast/slowmax w=0,0.02,0.05; then gcd/fbrace.py
    # = xaudit net.json --bands C.bands.json --stim k2/v1_220ns.stim.json --timed-only --all
    #   then python3 gcd/analyze.py on the report (it reads the rig_* names, kernel-independent)

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
  be slower than the fastest neighbour response. It is a race candidate list, and on gcd its
  candidates appeared only at `indep`.

## 7. What to write down

The table per seed and corner: the xevents5 verdict line, its RESIDUAL items with margins, and
ana5's verdict. Add the xaudit summary per corner, the negative-control result, the toolchain
fingerprint, the md5s, and every seed that did not place. State what each verdict assumes
(above). None of it is a silicon claim.
