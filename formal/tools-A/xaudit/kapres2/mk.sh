#!/usr/bin/env bash
# KapRes2: private olean overlay /tmp/kapres2/olean for xevents7.  Starts from a copy of the E7r
# overlay (/tmp/events7/olean: the committed Events5/6 chain) and recompiles the five committed
# Events7 modules into it, so the checker run is the committed source.  Every lean through slot.sh.
export PATH=$HOME/.elan/bin:$PATH
O=/tmp/kapres2/olean
[ -d $O/Formal ] || { mkdir -p $O; cp -r /tmp/events7/olean/Formal $O/; }
cd /home/user/asyncfpga3/formal/lean
for m in Events7Core Events7Excl Events7Cert Events7Beh Events7Main; do
  f=Formal/Core/XAudit/$m.lean
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="'$O':$LEAN_PATH" exec lean -o "$1" "$2"' sh "$O/${f%.lean}.olean" "$f" > /tmp/kapres2/mk_$m.log 2>&1
  echo "$f rc=$? errors=$(grep -c 'error' /tmp/kapres2/mk_$m.log)"
done
