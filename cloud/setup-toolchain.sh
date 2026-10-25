#!/usr/bin/env bash
# Build this project's ONE toolchain in a fresh cloud sandbox.
#
#   cloud/setup-toolchain.sh            # everything, idempotent
#   TC=/some/dir cloud/setup-toolchain.sh
#
# Mirrors ~/dev2/lib/fpgatoolchain/openxc7-src/build.sh on the owner's machine
# (adapted from openXC7/toolchain-installer), plus every patch in patches/ and
# a regenerated chipdb -- nextpnr-xilinx-ff-timing.patch changes the chipdb
# importer, so a .bin built without it routes fine and has 100 ps FF timing.
#
# It ends by running cells/verify/toolchain.sh.  If that fails, nothing this
# sandbox routes is a number.  Do not "fix" a failure by editing toolchain.sh.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
TC="${TC:-$HOME/dev2/lib/fpgatoolchain}"
SRC="$TC/openxc7-src"
PREFIX="$TC/openxc7"
JOBS="${JOBS:-$(nproc)}"

YOSYS_REV=v0.62
NEXTPNR_REV=bfdeaf7c          # base every patch in patches/ is written against
PRJXRAY_REV=ce065d470ea9547bba97b9df4476a0148e728c95
PRJXRAY_DB_REV=0.8.2
PART=xc7z010clg400-1

log() { printf '\n== %s\n' "$*"; }

if command -v apt-get >/dev/null; then
    SUDO=""; [ "$(id -u)" = 0 ] || SUDO="sudo"
    log "apt dependencies"
    $SUDO apt-get update -qq
    $SUDO env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq \
        build-essential clang bison flex gawk tcl-dev libffi-dev libreadline-dev \
        pkg-config zlib1g-dev git cmake python3 python3-dev python3-pip \
        libboost-all-dev libeigen3-dev libantlr4-runtime-dev antlr4 \
        iverilog uuid-dev default-jre-headless >/dev/null
fi

# A cached build for exactly these patches skips everything below.
BUILT=0
if [ ! -x "$PREFIX/bin/nextpnr-xilinx" ] && [ "${NO_CACHE:-0}" != 1 ]; then
    "$REPO/cloud/toolchain-cache.sh" fetch || true
fi

mkdir -p "$SRC" "$PREFIX/bin" "$PREFIX/lib/python"

clone() {  # clone <dir> <url> <rev>
    [ -d "$SRC/$1/.git" ] || git clone -q "$2" "$SRC/$1"
    git -C "$SRC/$1" fetch -q --tags origin || true
    git -C "$SRC/$1" checkout -q "$3"
    git -C "$SRC/$1" submodule update -q --init --recursive
}

if [ ! -x "$PREFIX/bin/yosys" ]; then
    log "yosys $YOSYS_REV"
    BUILT=1
    clone yosys https://github.com/YosysHQ/yosys.git "$YOSYS_REV"
    make -C "$SRC/yosys" -j"$JOBS" >/dev/null
    make -C "$SRC/yosys" install PREFIX="$PREFIX" >/dev/null
fi

if [ ! -x "$PREFIX/bin/xc7frames2bit" ]; then
    log "prjxray"
    BUILT=1
    clone prjxray https://github.com/openXC7/prjxray.git "$PRJXRAY_REV"
    cmake -S "$SRC/prjxray" -B "$SRC/prjxray/build" -DCMAKE_INSTALL_PREFIX="$PREFIX" >/dev/null
    make -C "$SRC/prjxray/build" -j"$JOBS" >/dev/null
    make -C "$SRC/prjxray/build" install >/dev/null
fi

# prjxray's Python side (fasm2frames).  Its own block, guarded on the import,
# so a failure here is retried on the next run instead of being skipped because
# xc7frames2bit already exists.  `python3 -m pip`, not `pip3`: in the cloud
# image they are different interpreters.  The `-e` lines in requirements.txt
# are relative to the prjxray checkout; prjxray itself is reached through
# PYTHONPATH (build_hw.sh) and fasm is built below against the shared antlr.
if ! PYTHONPATH="$SRC/prjxray:$PREFIX/lib/python" python3 -c 'import fasm, prjxray, intervaltree, simplejson' 2>/dev/null; then
    log "prjxray python"
    { grep -v '^-e' "$SRC/prjxray/requirements.txt"; echo cython; } > "$SRC/prjxray-req.txt"   # fasm's setup.py imports Cython
    python3 -m pip install -q --break-system-packages -r "$SRC/prjxray-req.txt" 2>/dev/null \
        || python3 -m pip install -q -r "$SRC/prjxray-req.txt"
    (cd "$SRC/prjxray/third_party/fasm" && \
        PYTHONNOUSERSITE=1 python3 setup.py install --antlr-runtime=shared --home="$PREFIX" >/dev/null)
fi

if [ ! -d "$PREFIX/share/nextpnr/prjxray-db/zynq7" ]; then
    log "prjxray-db $PRJXRAY_DB_REV"
    clone prjxray-db https://github.com/openXC7/prjxray-db.git "$PRJXRAY_DB_REV"
    mkdir -p "$PREFIX/share/nextpnr/prjxray-db"
    cp -r "$SRC/prjxray-db/"* "$PREFIX/share/nextpnr/prjxray-db/"
fi

# nextpnr: always re-apply the patches from THIS checkout, so the binary
# matches the branch being worked on rather than whatever was built last.
STAMP="$PREFIX/.patches.sha"
WANT=$(cat "$REPO"/patches/nextpnr-xilinx-*.patch | sha256sum | cut -c1-16)
if [ ! -x "$PREFIX/bin/nextpnr-xilinx" ] || [ "$(cat "$STAMP" 2>/dev/null)" != "$WANT" ]; then
    log "nextpnr-xilinx $NEXTPNR_REV + patches/"
    BUILT=1
    clone nextpnr-xilinx https://github.com/openXC7/nextpnr-xilinx.git "$NEXTPNR_REV"
    N="$SRC/nextpnr-xilinx"
    git -C "$N" checkout -q -- .
    # Order: the three that touch fasm.cc stack in this order; the rest are independent.
    for p in lut-pinmap dsp-constpins dsp-areg rloc-group lut-perm-sink place-weight ff-timing pybindings; do
        f="$REPO/patches/nextpnr-xilinx-$p.patch"
        [ -f "$f" ] || continue
        git -C "$N" apply --whitespace=nowarn "$f" || { echo "PATCH FAILED: $p" >&2; exit 1; }
        echo "  applied $p"
    done
    for p in "$REPO"/patches/nextpnr-xilinx-*.patch; do   # anything new not in the list above
        b=$(basename "$p" .patch); b=${b#nextpnr-xilinx-}
        case " lut-pinmap dsp-constpins dsp-areg rloc-group lut-perm-sink place-weight ff-timing pybindings " in
            *" $b "*) ;; *) git -C "$N" apply --whitespace=nowarn "$p"; echo "  applied $b (unlisted)";;
        esac
    done
    sed -i 's/foreach (PyVer 3 36 37 38 39 310 311 312)/foreach (PyVer 3 36 37 38 39 310 311 312 313 314)/' "$N/CMakeLists.txt"
    cmake -S "$N" -B "$N/build" -DCMAKE_INSTALL_PREFIX="$PREFIX" -DARCH=xilinx \
        -DUSE_OPENMP=ON -DBUILD_GUI=OFF -DBUILD_TESTS=OFF >/dev/null
    make -C "$N/build" -j"$JOBS" >/dev/null
    make -C "$N/build" install >/dev/null
    cp "$N/build/bbasm" "$PREFIX/bin/"
    cp "$N/xilinx/constids.inc" "$PREFIX/lib/"
    cp "$N/xilinx/constids.inc" "$N"/xilinx/python/* "$PREFIX/lib/python/"
    rm -rf "$PREFIX/lib/external"; cp -r "$N/xilinx/external" "$PREFIX/lib/external"
    rm -f "$PREFIX/xc7z010clg400.bin"    # importer may have changed: regenerate
    echo "$WANT" > "$STAMP"
fi

if [ ! -s "$PREFIX/xc7z010clg400.bin" ]; then
    log "chipdb $PART"
    BUILT=1
    N="$SRC/nextpnr-xilinx"
    (cd "$N" && python3 xilinx/python/bbaexport.py --device "$PART" --bba /tmp/xc7z010.bba)
    "$PREFIX/bin/bbasm" -l /tmp/xc7z010.bba "$PREFIX/xc7z010clg400.bin"
    rm -f /tmp/xc7z010.bba
fi

cat > "$PREFIX/export.sh" <<EOF
export TC=$TC
export PYTHONPATH=$PREFIX/lib/python
export PATH=$PREFIX/bin:\$PATH
export NEXTPNR_XILINX_PYTHON_DIR=$PREFIX/lib/python
export PRJXRAY_DB_DIR=$PREFIX/share/nextpnr/prjxray-db
EOF

# Dynamatic is not built here (LLVM, hours).  The frontend outputs for the
# existing kernels are committed as fixtures; restore them where every script
# expects them.
mkdir -p "$REPO/build/frontend"
cp -rn "$REPO/cloud/fixtures/frontend/"* "$REPO/build/frontend/"

log "fingerprint"
TC="$TC" "$REPO/cells/verify/toolchain.sh"
echo "toolchain ready: source $PREFIX/export.sh"

# Only a build that just passed the fingerprints is worth caching.  A failed
# upload costs the next session a rebuild, nothing more.
if [ "$BUILT" = 1 ]; then
    log "publish toolchain cache"
    TC="$TC" "$REPO/cloud/toolchain-cache.sh" publish || echo "toolchain cache: publish FAILED (next session rebuilds)"
fi
