#!/usr/bin/env bash
# Auditor's own Lean install (no elan): GitHub release zip into ~/audit-lean.
# Usage: audit/tools/install_lean.sh 4.35.0
set -euo pipefail
VER=${1:?version}
D=$HOME/audit-lean
mkdir -p $D
if [ ! -x $D/lean-$VER-linux/bin/lean ]; then
  curl -sSfL -o $D/lean.zip "https://github.com/leanprover/lean4/releases/download/v$VER/lean-$VER-linux.zip"
  (cd $D && unzip -q -o lean.zip && rm lean.zip)
fi
$D/lean-$VER-linux/bin/lean --version
sha256sum $D/lean-$VER-linux/bin/lean
