#!/usr/bin/env bash
# KapRes2: native build of xevents8 from the COMMITTED sources (the module chain of mk.sh, against
# its olean overlay): lean -c per module -> leanc -> link, into $KR/exe/xevents8.  Every step
# through slot.sh.  Same program as `lean --run Formal/Core/XAudit/Events8Main.lean`.
export PATH=$HOME/.elan/bin:$PATH
KR=${KR:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/KapRes2}
OL=$KR/olean; E=$KR/exe
cd /home/user/asyncfpga3/formal/lean
mkdir -p $E/c $E/o
MODS=$(cd $OL && find Formal -name '*.olean' | sed 's|\.olean$|.lean|')
for f in $MODS; do
  m=$(echo ${f%.lean} | tr / .)
  [ -e "$E/o/$m.o" ] && continue
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c "LEAN_PATH=\"$OL:\$LEAN_PATH\" exec lean -DautoImplicit=false -c \"\$1\" \"\$2\"" sh "$E/c/$m.c" "$f" > $E/c/$m.log 2>&1 || { echo "lean -c $f failed"; exit 1; }
  FORMAL_SLOT_CWD=$PWD ../slot.sh leanc -c -O3 -DNDEBUG -o "$E/o/$m.o" "$E/c/$m.c" || { echo "leanc $m failed"; exit 1; }
done
FORMAL_SLOT_CWD=$PWD ../slot.sh leanc -o $E/xevents8 $E/o/*.o && echo "built $E/xevents8"
