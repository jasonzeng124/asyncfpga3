#!/usr/bin/env bash
# Native build of xevents5 from the COMMITTED sources (same module chain as mk.sh), into
# /tmp/kapres/exe/xevents5: lean -c (C per module, against the olean overlay) -> leanc -> link.
# Every lean/leanc step goes through slot.sh.  Same program as `lean --run Events5Main.lean`.
export PATH=$HOME/.elan/bin:$PATH
HERE="$(cd "$(dirname "$0")" && pwd)"
OL=${OL:-/tmp/kapres/olean}; E=/tmp/kapres/exe
cd /home/user/asyncfpga3/formal/lean
mkdir -p $E/c $E/o
MODS=$(grep -o 'Formal/[A-Za-z0-9/]*\.lean' "$HERE/mk.sh")
for f in $MODS; do
  m=$(echo ${f%.lean} | tr / .)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c "LEAN_PATH=\"$OL:\$LEAN_PATH\" exec lean -c \"\$1\" \"\$2\"" sh "$E/c/$m.c" "$f" > $E/c/$m.log 2>&1 || { echo "lean -c $f failed"; exit 1; }
  FORMAL_SLOT_CWD=$PWD ../slot.sh leanc -c -O3 -DNDEBUG -o "$E/o/$m.o" "$E/c/$m.c" || { echo "leanc $m failed"; exit 1; }
done
FORMAL_SLOT_CWD=$PWD ../slot.sh leanc -o $E/xevents5 $E/o/*.o && echo "built $E/xevents5"
