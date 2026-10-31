#!/usr/bin/env bash
# compile listed modules (paths relative to formal/lean) into the private overlay /tmp/events8/olean
# (on top of A-events7's /tmp/events7/olean, until the lead's lake build has the Formal oleans)
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
mkdir -p /tmp/events8/log
for f in "$@"; do
  o=/tmp/events8/olean/${f%.lean}.olean
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/events8/olean:/tmp/events7/olean:$LEAN_PATH" exec lean -o "$1" "$2"' sh "$o" "$f" > /tmp/events8/log/mk_$(basename $f).log 2>&1
  echo "$f rc=$? errors=$(grep -c 'error' /tmp/events8/log/mk_$(basename $f).log)"
done
