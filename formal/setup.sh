#!/usr/bin/env bash
# Idempotent, timed install of elan + Lean 4 + Mathlib for formal/lean.
#   formal/setup.sh   (safe to re-run; skips what is already there)
# Network notes (2026-10-27 sandbox): release.lean-lang.org, Reservoir,
# cache.mathlib.org and lakecache.blob.core.windows.net are blocked by the
# proxy. So: Lean comes from the GitHub release zip, Mathlib by git (the
# lakefile uses a git URL), and if `lake exe cache get` fails, the Mathlib
# modules the project imports are built from source (lake builds only the
# transitive imports; budget ~1-2 h on 4 cores for the first build).
set -uo pipefail
T0=$(date +%s)
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$HERE/lean"
TC=$(cat lean-toolchain)            # leanprover/lean4:vX.Y.Z
VER=${TC#*:v}
retry() { local i; for i in 1 2 3 4 5; do "$@" && return 0; sleep $((2**i)); done; return 1; }
if ! command -v elan >/dev/null 2>&1; then
  echo "[setup] installing elan"
  retry curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.$$.sh
  sh /tmp/elan-init.$$.sh -y --default-toolchain none --no-modify-path
  rm -f /tmp/elan-init.$$.sh
fi
if ! elan toolchain list 2>/dev/null | grep -q "v$VER"; then
  echo "[setup] installing Lean $VER"
  if ! elan toolchain install "$TC" >/dev/null 2>&1; then
    echo "[setup] elan download blocked; using the GitHub release zip"
    mkdir -p "$HOME/.lean-toolchains"
    retry curl -sSfL -C - -o /tmp/lean-$VER.zip \
      "https://github.com/leanprover/lean4/releases/download/v$VER/lean-$VER-linux.zip" || { echo "[setup] FAIL: Lean download"; exit 1; }
    (cd "$HOME/.lean-toolchains" && unzip -q -o /tmp/lean-$VER.zip) && rm -f /tmp/lean-$VER.zip
    elan toolchain link "$TC" "$HOME/.lean-toolchains/lean-$VER-linux"
  fi
fi
lean --version
[ -d .lake/packages/mathlib ] || retry lake update || { echo "[setup] FAIL: lake update"; exit 1; }
if lake exe cache get; then
  echo "[setup] Mathlib oleans from cache"
else
  echo "[setup] Mathlib cache unreachable: building the imported part of Mathlib from source"
fi
# Builds the project; with no cache this also builds every Mathlib module it imports.
"$HERE/slot.sh" lake build 2>&1 | tail -3
echo "[setup] done in $(( $(date +%s) - T0 ))s"
echo "[setup] add to PATH: export PATH=\$HOME/.elan/bin:\$PATH"
