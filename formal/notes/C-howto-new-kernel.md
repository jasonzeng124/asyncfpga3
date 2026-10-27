# How to take a new kernel through shard C's tools (probe C-10n, 2026-10-27)

Four steps, from the Dynamatic handshake MLIR to a timing verdict on the routed design. Each step
says what it proves, what it does not, and the commands that run it. Shard A's tools (X/hazard
audit `xaudit` and the event checker) have their own guide: `formal/out/HOWTO-new-kernel.md`.

Worked examples:
- step 1: ipow (probe C-8v: `Formal/Net/IpowHw*.lean`) and gcd_hw (C-8i, C-8k);
- step 4: collatz, xorshift and ipow (C-10n: `formal/notes/C-10n-kernels.md`).

Throughout, `<k>` stands for the kernel (e.g. `collatz`) and `<K>` for its Lean name (`Collatz`).

## 0. Before anything

    cells/verify/toolchain.sh             # must print 9 "ok" lines and exit 0; record its sha256
                                          # (9c732bc6303458df for every C-10n number)
    ~/dev2/lib/fpgatoolchain/openxc7/bin/yosys -V   # toolchain.sh cannot see missing .so files:
                                          # a fresh container needs `apt-get install -y libtcl8.6
                                          # libboost-...1.83.0` and `python3 -m pip install
                                          # simplejson textx intervaltree`
    export PATH=$HOME/.elan/bin:$PATH     # Lean 4 (core only for shard C; never `lake build` in
                                          # formal/lean, it would build Mathlib)

Every Lean process goes through `formal/slot.sh`. The input is the MLIR that bdc compiles:
`cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir` (the committed copy of
`build/frontend/<k>/...`). The C reference is `kernels/<k>/<k>.c`. Expected values are always
derived from the C, never from a run's output.

## 1. Dataflow import and a token-level proof (`formal/tools/dfimport`)

    python3 formal/tools/dfimport/mlir2lean.py cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir \
        -o formal/lean/Formal/Net/<K>Hw.lean --segments formal/lean/Formal/Net/<K>HwSeg.lean \
        --ns Formal.Net.<K>Hw --graph-module Formal.Net.<K>Hw --label <k> --short <k>

- **What it does.** Exports the graph bdc *emits*: bdc's own parser, its op-fusion plan and its
  lowering choices (`br` is a wire, an n-input control_merge is an arbiter plus fork, and so on).
  The output is a Lean `List Rule` plus the schedule certificates (`--segments`).
- **Option status.** `--ns/--graph-module/--label/--short` come from probe C-8v. When this note
  was written they were in the working tree but not yet committed. HEAD's `mlir2lean.py` writes
  the gcd_hw names only.
- **Drift check.** `formal/tools/dfimport/check.sh` covers gcd_hw. A new kernel needs the same
  two lines (regenerate into a temp dir, then `diff` against the committed file).

Then write `formal/lean/Formal/Net/<K>HwProof.lean` by hand, following
`Formal/Net/IpowHwProof.lean` (or `GcdHwProof.lean` + `GcdHwNat.lean`):
1. Transcribe the C function from `kernels/<k>/<k>.c`, fuelled, using the shared i32 operators
   `Formal.Net.GcdHw.Ops`.
2. Prove any rewrite Dynamatic made (ipow: `gR_eq` for the i1 `trunci/andi/select` form).
3. State the theorem: from one token per input, every complete run, under any schedule and any
   arbiter outcome, ends with exactly the C result. H_ONE_INVOCATION is proved from the initial
   store, not assumed.

Check it:

    cd formal/lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake build Formal.Net.<K>HwProof
    cd formal && ./check.sh Formal/Net/<K>Hw.lean Formal/Net/<K>HwSeg.lean Formal/Net/<K>HwProof.lean

- **Proves:** the *token-level* graph bdc emits computes the C function, on every schedule.
- **Does not cover:**
  - gates, delays or cells;
  - the hand-written C transcription (a reviewer must compare it with the .c file);
  - H_SOURCE_ETERNAL (source/constant chains treated as always valid, the tool's one modelling
    step);
  - liveness, unless proved separately (`GcdHwLive`, `IpowHwLive`).

  The gcd_hw circuit-level chain (`Capstone*`, `gcd_hw_circuit_safe''`) has not been redone for
  any other kernel.

## 2. Generated cells (`formal/tools/gen`)

    formal/tools/gen/gen.sh --check       # every cells/rtl module, re-synthesized by the project's
                                          # yosys, equals the committed Formal/Gen/Cells.lean
    # does the kernel use only cells that have a Gen target?  (empty output = yes)
    python3 bdc/emit.py cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir -o /tmp/<k>.v
    grep -oE '^\s*bd_[a-z0-9_]+\b' /tmp/<k>.v | tr -d ' ' | sort -u | while read m; do
      awk -v m=$m '$2==m{f=1} END{if(!f) print m" has no Gen target"}' formal/tools/gen/targets.txt; done

- **What it is.** The library is kernel-independent, so a new kernel needs nothing here unless it
  instantiates a cell with no target. collatz, xorshift and ipow use bd_arbiter, bd_delay,
  bd_delay_gated, bd_fork, bd_join, bd_link, bd_mux, bd_pipe, bd_snk, bd_src and bd_steer, and
  all of them have targets.
- **Proves:** each cell's Lean term (INITs, pin maps, feedback wires) is what yosys synthesizes
  from `cells/rtl`, and 163 theorems tie those terms to shard B's transcriptions. A changed INIT
  breaks the build.
- **Does not cover:**
  - bdc's per-kernel *compute units* (the fused `uaddi`/`ucmpi`/`umuli`... modules emitted into
    the kernel file), which are not in `cells/rtl` and are not imported;
  - bd_mem's BRAM (opaque);
  - DSP48E1 (ipow's multiplies);
  - parameter values other than the representatives in targets.txt.

## 3. Netlist / bitstream import (`formal/tools/fasm2lean2`)

    python3 formal/tools/fasm2lean2/fasm2lean2.py <route>/soak.fasm <route>/soak.xdc --ns <K> \
        --json /tmp/<k>.f2l.json --out /tmp/<k>.lean

- **On a whole kernel this refuses**, and that is the correct behaviour. The model covers LUT6 and
  LUT6_2 only, and a compiled kernel has MUXF7/F8, CARRY4 and FFs. Run on collatz seed 1 it
  printed `site features the model does not cover (refused): ... AOUTMUX.F7 [wide mux] ...
  CARRY4.ACY0 [carry chain]`.
- **What does work:**
  - the C-11c flow (`formal/tools/fasm2lean2/check.sh`, `route.sh`) on a LUT-only cut, e.g.
    bd_link + bd_arbiter: bits = yosys import up to a checked renaming;
  - the timing front end of step 4, which reuses fasm2lean's FASM walker (`Extract.walk`) only
    to find each routed net's pips for prjxray delays, not to import logic.
- **In progress, not claimed:** whole-design import (`Formal/Net/FasmDesign/` was untracked when
  this note was written).
- **Proves** (where it runs): the bits loaded on the chip implement the logical cells. This is
  what catches re-pointed pips that `fasm_audit` cannot see.
- **Does not cover:** whole kernels (yet); timing.

## 4. Timing checker on the routed kernel (`formal/tools/kcheck`)

Add one row to `formal/tools/kcheck/kernels.tsv` with these columns:
- kernel name;
- MLIR path;
- sizes file: `research:<path>` reads it from `origin/claude/research`; a repo path is used as
  is; `none` gives the placeholders, with BD_NO_TIGHTEN=1;
- BD_DSP;
- why these sizes.

Then:

    formal/tools/kcheck/run.sh <k> 1 2 3 4          # >= 4 placer seeds; ~5 min/route + ~2 min/check
    # SKIP_ROUTE=1 re-checks existing routes; KCHECK_FRONT_REV=worktree uses tcheck's current
    # front end instead of git HEAD's; KCHECK_TAG=x keeps a second set of results apart;
    # KCHECK_JOBS (default 2) caps parallel nextpnr / extract jobs; KCHECK_FREQ (default 100 MHz)

`run.sh` does the following:
1. Runs `cells/verify/toolchain.sh` and stops on failure.
2. Builds the tcheck snapshot `build/tcheck_snap`: a copy of `formal/tools/tcheck`'s Lean
   package, built through `slot.sh`, after `sync.sh --check` passes on the original. It runs the
   toy and cert self-tests.
3. Freezes tcheck's Python front end (`build/tools/front_*`).
4. Builds each route with **the project's own flow** in an exported copy of `cells/` and `bdc/`:
   `bdc/emit.py` (with the soak top), then `cells/flow.sh` with BD_TOP_V/BD_TOP_M, BD_SIZES,
   BD_OUT, NEXTPNR_SEED and BD_DSP. This is fusion_bench's `--mlir --route` minus its GLS.
   flow.sh's own gates run (fracture, fasm_audit, zero_arcs). The copy's nextpnr line gets
   `--freq $KCHECK_FREQ --timing-allow-fail`, because flow.sh passes no --freq. The patch is
   asserted to apply once.
5. Runs the project rules: `tighten.py` (A, H, I, F; D is a screen), `skew.py -v` (E) and
   `arb_fork.py` (J).
6. Runs `extract.py --rules2 AEFJWR --cert` and the compiled checker.
7. Compares the two row by row and writes `results/<k>/{summary.txt, agree.tsv, disagree.tsv,
   rows.tsv, routes.tsv, toolchain.txt}`.

Reading the result:
- **tcheck verdict:** PASS at both fastG and slowG, i.e. one prjxray corner at a time
  (H_ONE_CORNER) times the project's 0.772/1.155 guard band.
- **disagree.tsv classes:**
  - **band-only:** fails only with the band; the unguarded prjxray fast and slow corners both
    pass.
  - **frontend-gap?:** an unguarded corner fails and the deciding instance contains fallback
    arcs (SDF band in place of prjxray). Confirm with `diag.py`.
  - **corner-fail:** an unguarded corner fails with no fallback. A candidate real failure.
  - **project-only:** the project rule fails and tcheck passes.
- **Explaining a row:**

      zcat build/<k>/s<seed>/check/obl.tc.gz | awk '/^inst <RULE> <row> /{p=1} /^inst /&&!/<row>/{p=0} p' > /tmp/i.tc
      python3 formal/tools/tcheck/diag.py /tmp/i.tc '<RULE> <row>' fast   # critical paths, per-arc intervals

  A fallback arc shows the same `84..128`-style interval in every prjxray column.

- **What a PASS proves** (`Tcheck.verdict_sound`, `cverdict_sound`, `pot_sound`; audit = propext,
  Classical.choice, Quot.sound): for every run of the *emitted* netlist in which each arc's delay
  lies in its interval, the obligation's data change precedes its target change by the setup.
  The late sides are checked potentials on the whole cyclic routed graph, so the extractor's path
  choice is not trusted.
- **What it does NOT prove:**
  - **The front end is untrusted:** `extract.py` builds the graph from nextpnr's SDF and FASM and
    assigns the intervals (prjxray-db, Elmore RC, site hops). Arcs it has no prjxray number for
    fall back to the SDF band (H_FALLBACK_BAND). It also chooses the obligations and their phase
    rules (C-10e/10g/10h).
  - Known front-end gaps:
    - the slice OUTMUX hop on LUT outputs (being fixed by C-10m);
    - CARRY4 CIN nets and F7/F8 select nets, which fall back.
  - **Rows mirror the project rules only.** No gcd_hw capstone rows (rules10k/10l are gcd_hw-
    specific) and no end-to-end correctness. A kernel with all rows PASS has the A/E/F/H/I/J
    obligations discharged under the delay model, nothing more.
  - **Silicon:** the prjxray numbers are a model (C-10c); rise and fall are not separated;
    on-die correlation is the corner model's assumption.
- **The route is a sample.** Quote mean and range over at least 4 seeds, never one route.
