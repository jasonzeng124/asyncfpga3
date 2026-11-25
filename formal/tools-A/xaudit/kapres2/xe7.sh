#!/usr/bin/env bash
# run the committed xevents7 (Events7Main.lean) with lean --run on the private overlay built by mk.sh.
# At most 2 of these at once (own 2-slot flock in /tmp/kapres2/xslots), and each one also holds a
# formal/slot.sh slot.
export PATH=$HOME/.elan/bin:$PATH
mkdir -p /tmp/kapres2/xslots
while :; do
  for i in 1 2; do
    exec {fd}>/tmp/kapres2/xslots/s$i
    if flock -n "$fd"; then
      cd /home/user/asyncfpga3/formal/lean
      FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/kapres2/olean:$LEAN_PATH" exec lean --run Formal/Core/XAudit/Events7Main.lean "$@"' sh "$@"
      exit $?
    fi
    exec {fd}>&-
  done
  sleep 2
done
