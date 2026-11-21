#!/usr/bin/env bash
# compile listed modules (paths relative to formal/lean) into the private overlay /tmp/events7/olean
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
for f in "$@"; do
  o=/tmp/events7/olean/${f%.lean}.olean
  [ -L "$o" ] && unlink "$o"
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/events7/olean:$LEAN_PATH" exec lean -o "$1" "$2"' sh "$o" "$f" > /tmp/events7/mk_$(basename $f).log 2>&1
  echo "$f rc=$? errors=$(grep -c 'error' /tmp/events7/mk_$(basename $f).log)"
done
