#!/bin/bash
# usage: build.sh <srcroot> <outdir> module...
set -e
L=/root/audit-lean/lean-4.35.0-linux/bin/lean
SRC=$1; OUT=$2; shift 2
mkdir -p $OUT
for m in "$@"; do
  f=$SRC/$(echo $m|tr . /).lean; o=$OUT/$(echo $m|tr . /).olean
  mkdir -p $(dirname $o)
  echo "== $m"; /usr/bin/time -f "%es %MKB" env LEAN_PATH=$OUT $L -j2 --root=$SRC -o $o $f
done
