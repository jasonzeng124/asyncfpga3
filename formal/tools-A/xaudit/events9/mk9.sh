#!/usr/bin/env bash
# compile listed modules (paths relative to formal/lean) into the private overlay /tmp/events9/olean
# (on top of A-events8 /tmp/events8/olean, until the lead's lake build has the Formal oleans)
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
mkdir -p /tmp/events9/log
# full overlay (Lean takes Formal.* from the first LEAN_PATH entry with a Formal/ dir)
[ -d /tmp/events9/olean/Formal ] || { mkdir -p /tmp/events9/olean; cp -rs /tmp/events8/olean/Formal /tmp/events9/olean/; }
for f in "$@"; do
  o=/tmp/events9/olean/${f%.lean}.olean
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/events9/olean:/tmp/events8/olean:$LEAN_PATH" exec lean -o "$1" "$2"' sh "$o" "$f" > /tmp/events9/log/mk_$(basename $f).log 2>&1
  echo "$f rc=$? errors=$(grep -c 'error' /tmp/events9/log/mk_$(basename $f).log)"
done
