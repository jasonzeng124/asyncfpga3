#!/usr/bin/env bash
# compile listed modules (paths relative to formal/lean) into the private overlay /tmp/events6/olean
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/asyncfpga3/formal/lean
[ -d /tmp/events6/olean/Formal ] || cp -rs $PWD/.lake/build/lib/lean/Formal /tmp/events6/olean/
for f in "$@"; do
  o=/tmp/events6/olean/${f%.lean}.olean
  [ -L "$o" ] && unlink "$o"
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c 'LEAN_PATH="/tmp/events6/olean:$LEAN_PATH" exec lean -o "$1" "$2"' sh "$o" "$f" > /tmp/events6/mk_$(basename $f).log 2>&1
  echo "$f rc=$? errors=$(grep -c 'error' /tmp/events6/mk_$(basename $f).log)"
done
