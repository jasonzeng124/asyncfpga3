#!/usr/bin/env bash
# C kernel -> handshake_transformed.mlir, reproducing Dynamatic's own
# tools/dynamatic/scripts/compile.sh by hand.
#
#   ./frontend.sh <kernel-name>
#   ./frontend.sh fir
#
# WHY THIS SCRIPT EXISTS AT ALL
#
# compile.sh is meant to run inside the `dynamatic` interactive driver shell,
# which sets up DYNAMATIC_DIR/bin (a symlink farm build.sh normally builds)
# and then sources compile.sh with ~18 positional arguments. Neither the
# driver (`build/bin/dynamatic`) nor `hls-verifier` built in this tree --
# both fail on a `dyn_cast` member call newer LLVM removed, in
# tools/hls-verifier/include/HlsTb.h. We don't need either: hls-verifier only
# matters for RTL-vs-software co-simulation, and the driver is just argument
# plumbing around compile.sh. So this script *is* that plumbing, with the
# path guesswork compile.sh's own comments admit to (it references both
# $DYNAMATIC_DIR/bin/... and $DYNAMATIC_DIR/build/bin/... for what are
# sometimes the same binary) resolved concretely for this checkout.
#
# We stop right after --handshake-infer-basic-blocks (compile.sh's
# F_HANDSHAKE_TRANSFORMED). We do NOT run --handshake-place-buffers: that
# pass runs a MILP against a target clock period, and there is no clock --
# see COMPILER-PLAN.md. It also isn't built here (no Gurobi, no CBC), so it
# would fail regardless.
#
# This script never edits anything under dynamatic/ -- it only reads
# binaries and headers out of it. All generated files land under build/,
# which is gitignored (see the repo-root .gitignore's unanchored `build/`
# pattern, the same convention cells/flow.sh uses for cells/build/).

set -euo pipefail
cd "$(dirname "$0")/.."   # repo root, so every path below is unambiguous

# ---------------------------------------------------------------------------
# Fixed locations
# ---------------------------------------------------------------------------
DYN="$PWD/dynamatic"
LLVM_BIN="$DYN/build/llvm-project/bin"     # prebuilt clang/opt, NOT dynamatic/bin
DYN_BIN="$DYN/build/bin"                   # dynamatic-opt, source-rewriter, etc.
DYN_LIB="$DYN/build/lib"                   # clang plugin / opt-plugin .so files

# build.sh normally symlinks this in as build/include/clang_headers (see its
# create_include_symlink call); that symlink was never created here because
# the top-level `bin/` target of build.sh's OTHER symlinks never got built.
# The real directory it points at exists regardless -- clang's own bundled
# resource headers (stddef.h, stdarg.h, ...) -- so we use it directly instead
# of recreating a symlink inside dynamatic/, which we are not allowed to
# touch.
CLANG_HEADERS="$DYN/build/llvm-project/lib/clang/18/include"

# This script drives only prebuilt native binaries (clang, opt,
# dynamatic-opt, translate-llvm-to-std, source-rewriter) -- none of that
# needs Python or ninja. Both are pinned elsewhere in this project
# (/home/jayjay/.local/share/uv/python/cpython-3.12-linux-x86_64-gnu/bin/python3.12,
# ~/.local/bin/ninja) for build.sh and bdc/hs/*.py; this script has no call
# site for either, so none is hardcoded here.

CLANG="$LLVM_BIN/clang"
OPT="$LLVM_BIN/opt"
SOURCE_REWRITER="$DYN_BIN/source-rewriter"
TRANSLATE_LLVM_TO_STD="$DYN_BIN/translate-llvm-to-std"
DYNAMATIC_OPT="$DYN_BIN/dynamatic-opt"
DYN_PRAGMAS_PLUGIN="$DYN_LIB/DynPragmasPlugin.so"
MEM_DEP_ANALYSIS_PLUGIN="$DYN_LIB/MemDepAnalysis.so"

for f in "$CLANG" "$OPT" "$SOURCE_REWRITER" "$TRANSLATE_LLVM_TO_STD" \
         "$DYNAMATIC_OPT" "$DYN_PRAGMAS_PLUGIN" "$MEM_DEP_ANALYSIS_PLUGIN"; do
  [ -x "$f" ] || [ -e "$f" ] || { echo "missing required tool: $f"; exit 2; }
done
[ -d "$CLANG_HEADERS" ] || { echo "missing clang resource headers: $CLANG_HEADERS"; exit 2; }

# ---------------------------------------------------------------------------
# Arguments
# ---------------------------------------------------------------------------
KERNEL="${1:-}"
if [ -z "$KERNEL" ]; then
  echo "usage: $0 <kernel-name>   (e.g. $0 fir)"
  echo "kernel must be a directory under kernels/ or dynamatic/integration-test/ containing <kernel>.c"
  exit 2
fi

# Where a kernel lives. This repo's own kernels/ wins over Dynamatic's
# shipped integration-test/ so we can write kernels that exercise op and
# control-flow shapes the shipped suite doesn't reach, without editing the
# vendored tree. Same-named directory in kernels/ shadows the shipped one.
SRC_DIR="$PWD/kernels/$KERNEL"
[ -d "$SRC_DIR" ] || SRC_DIR="$DYN/integration-test/$KERNEL"
SRC_C="$SRC_DIR/$KERNEL.c"
[ -f "$SRC_C" ] || { echo "no such kernel source: $SRC_C"; exit 2; }
echo "== $KERNEL: source $SRC_C =="

OUT="build/frontend/$KERNEL"
COMP="$OUT/comp"           # mirrors compile.sh's own $COMP_DIR naming
rm -rf "$OUT"
mkdir -p "$COMP"

# A step failed if its exit code is nonzero. Name it and stop -- do not let a
# later step run against a truncated/garbage file from a step that "mostly"
# worked. (This is the same contract cells/flow.sh's `|| { echo ...; exit 1; }`
# blocks give the PnR gates: printing a failure message must never be
# followed by falling through to exit 0.)
fail() { echo "FAILED at step: $1"; exit 1; }

# A step that "succeeded" but wrote nothing is worse than one that errored,
# because set -e won't catch it. Every stage below is checked for this.
require_nonempty() {
  [ -s "$1" ] || fail "$2 (produced empty output: $1)"
}

echo "== $KERNEL: 0/8 copy source =="
cp "$SRC_C" "$COMP/$KERNEL.c" || fail "copy source"

# ---------------------------------------------------------------------------
# Step 1 -- source-rewriter: disable short-circuit evaluation of && / ||.
# Dynamatic's semantics evaluate both operands of && / || always (no
# short-circuiting), because short-circuiting requires control-dependent
# operand suppression that the elastic dataflow model doesn't give you for
# free. This rewrites the C source in place. compile.sh only skips this step
# when ENABLE_SHORT_CIRCUIT=1; we never want that, so we always run it.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 1/8 source-rewriter (disable short-circuit) =="
"$SOURCE_REWRITER" "$COMP/$KERNEL.c" -- \
  -I "$DYN/include" -I "$SRC_DIR" -I "$CLANG_HEADERS" \
  || fail "source-rewriter"
require_nonempty "$COMP/$KERNEL.c" "source-rewriter"

# ---------------------------------------------------------------------------
# Step 2 -- clang -O0 -emit-llvm, with Dynamatic's pragma-handling plugin.
# -ffp-contract=off (via -Xclang, so it survives clang's driver-level
# argument filtering) stops clang fusing float mul+add into a single op,
# which would hide an operation the handshake lowering needs to see.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 2/8 clang -> LLVM IR =="
"$CLANG" -O0 -funroll-loops -S -emit-llvm "$COMP/$KERNEL.c" \
  -I "$DYN/include" \
  -I "$SRC_DIR" \
  -I "$CLANG_HEADERS" \
  -fplugin="$DYN_PRAGMAS_PLUGIN" \
  -Xclang \
  -ffp-contract=off \
  -o "$COMP/clang.ll" \
  || fail "clang -> LLVM IR"
require_nonempty "$COMP/clang.ll" "clang -> LLVM IR"

# ---------------------------------------------------------------------------
# Step 3 -- sed cleanups on the .ll text (verbatim from compile.sh):
#   - strip "optnone": -ffp-contract=off makes clang add it even though we
#     passed -O0 for real optimization further down via `opt`; optnone would
#     silently veto every pass in step 4.
#   - strip "noinline": clang always adds it; it would block the `inline`
#     pass compile.sh depends on the same way.
#   - strip "target datalayout" / "target triple": mlir-translate's LLVM
#     dialect importer doesn't understand these lines.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 3/8 sed cleanups on .ll =="
sed -i "s/optnone//g" "$COMP/clang.ll" || fail "sed strip optnone"
sed -i "s/noinline//g" "$COMP/clang.ll" || fail "sed strip noinline"
sed -i "s/^target datalayout = .*$//g" "$COMP/clang.ll" || fail "sed strip target datalayout"
sed -i "s/^target triple = .*$//g" "$COMP/clang.ll" || fail "sed strip target triple"
require_nonempty "$COMP/clang.ll" "sed cleanups"

# ---------------------------------------------------------------------------
# Step 4 -- canonicalization passes (verbatim pass list from compile.sh: it
# inlines, promotes stack allocas to SSA registers, canonicalizes loops to
# do-while form, and lowers switches to branches -- all groundwork
# lower-cf-to-handshake later on assumes has already happened).
# ---------------------------------------------------------------------------
echo "== $KERNEL: 4/8 opt canonicalization passes =="
"$OPT" -S \
  -passes="inline,mem2reg,consthoist,instcombine<max-iterations=1000;no-use-loop-info>,function(loop-mssa(licm<no-allowspeculation>)),function(loop(loop-idiom,indvars,loop-deletion)),simplifycfg,loop-rotate,simplifycfg,sink,lowerswitch,simplifycfg,dce" \
  "$COMP/clang.ll" \
  > "$COMP/clang.opt.ll" \
  || fail "opt canonicalization passes"
require_nonempty "$COMP/clang.opt.ll" "opt canonicalization passes"

# ---------------------------------------------------------------------------
# Step 5 -- memory dependence analysis. Attaches !dest.ops metadata to
# load/store pairs so the handshake lowering knows which memory accesses
# must be ordered against each other. A no-op for kernels with no array
# accesses (test_loop_free, gcd), which is expected, not a failure.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 5/8 mem-dep-analysis =="
"$OPT" -S \
  -load-pass-plugin "$MEM_DEP_ANALYSIS_PLUGIN" \
  -passes="mem-dep-analysis" \
  -polly-process-unprofitable \
  "$COMP/clang.opt.ll" \
  > "$COMP/clang.opt.dep.ll" \
  || fail "mem-dep-analysis"
require_nonempty "$COMP/clang.opt.dep.ll" "mem-dep-analysis"

# ---------------------------------------------------------------------------
# Step 6 -- LLVM IR -> MLIR `cf` dialect.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 6/8 translate-llvm-to-std -> cf.mlir =="
"$TRANSLATE_LLVM_TO_STD" \
  "$COMP/clang.opt.dep.ll" \
  -function-name "$KERNEL" \
  -csource "$SRC_C" \
  -dynamatic-path "$DYN" \
  -o "$COMP/cf.mlir" \
  || fail "translate-llvm-to-std"
require_nonempty "$COMP/cf.mlir" "translate-llvm-to-std"

# ---------------------------------------------------------------------------
# Step 7 -- cf-level transformations, then lower cf -> handshake.
# Four dynamatic-opt invocations, each writing the file the next one reads,
# same as compile.sh's non-FTD, non-straight-to-queue, non-duplication path
# (the driver's default: FAST_TOKEN_DELIVERY=0, STRAIGHT_TO_QUEUE=0,
# ENABLE_DUPLICATION unset).
#
# The DISABLE_LSQ branch point in compile.sh has no established default in
# this environment (it's a positional argument the driver would normally
# supply). We always take the --mark-memory-interfaces branch rather than
# --force-memory-interface="force-mc=true": it's the more general pass (lets
# Dynamatic pick MC vs LSQ per access pattern instead of forcing MC
# everywhere) and, empirically, none of the four kernels here have memory
# access patterns requiring an actual LSQ, so it produces the same MC-only
# result --force-mc=true would while remaining correct for kernels that
# would need an LSQ.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 7/8 cf transformations + lower-cf-to-handshake =="
"$DYNAMATIC_OPT" \
  --allow-unregistered-dialect \
  "$COMP/cf.mlir" \
  --drop-unlisted-functions="function-names=$KERNEL" \
  --func-set-arg-names="source=$SRC_C" \
  --flatten-memref-row-major \
  --canonicalize \
  --arith-reduce-strength="max-adder-depth-mul=3" \
  --push-constants \
  > "$COMP/cf_transformed.mlir" \
  || fail "cf transformations"
require_nonempty "$COMP/cf_transformed.mlir" "cf transformations"

"$DYNAMATIC_OPT" \
  --allow-unregistered-dialect \
  "$COMP/cf_transformed.mlir" \
  --consume-producer-output-attr-marker \
  > "$COMP/cf_consumed_pragmarkers.mlir" \
  || fail "consume producer-output pragma markers"
require_nonempty "$COMP/cf_consumed_pragmarkers.mlir" "consume producer-output pragma markers"

"$DYNAMATIC_OPT" "$COMP/cf_consumed_pragmarkers.mlir" \
  --mark-memory-interfaces \
  > "$COMP/cf_mem_interface_marked.mlir" \
  || fail "mark memory interfaces"
require_nonempty "$COMP/cf_mem_interface_marked.mlir" "mark memory interfaces"

"$DYNAMATIC_OPT" "$COMP/cf_mem_interface_marked.mlir" \
  --lower-cf-to-handshake \
  > "$COMP/handshake.mlir" \
  || fail "lower-cf-to-handshake"
require_nonempty "$COMP/handshake.mlir" "lower-cf-to-handshake"

# ---------------------------------------------------------------------------
# Step 8 -- handshake-level transformations. This is the deliverable file.
#   --handshake-deactivate-mem-dependencies / --handshake-replace-memory-interfaces:
#     resolve the interface markers step 7 attached into real mem_controller
#     / lsq ops.
#   --handshake-remove-unused-memrefs: drop memref args nothing reads/writes.
#   --handshake-optimize-bitwidths: narrow channel widths where legal (e.g.
#     the array-index channels above end up i10, not i32).
#   --handshake-materialize: enforces one-producer/one-consumer per SSA
#     value by inserting fork/sink -- this is the channel discipline the rest
#     of this project's op->cell mapping is built on.
#   --handshake-infer-basic-blocks: tags any operation step 7/8 introduced
#     without a handshake.bb attribute (forks, sinks, materialized ops).
# We stop here. --handshake-place-buffers is never run -- see header comment.
# ---------------------------------------------------------------------------
echo "== $KERNEL: 8/8 handshake transformations -> handshake_transformed.mlir =="
"$DYNAMATIC_OPT" "$COMP/handshake.mlir" \
  --handshake-deactivate-mem-dependencies --handshake-replace-memory-interfaces \
  --handshake-remove-unused-memrefs \
  --handshake-optimize-bitwidths \
  --handshake-materialize --handshake-infer-basic-blocks \
  > "$COMP/handshake_transformed.mlir" \
  || fail "handshake transformations"
require_nonempty "$COMP/handshake_transformed.mlir" "handshake transformations"

echo "== $KERNEL: done -> $COMP/handshake_transformed.mlir =="
