#!/usr/bin/env bash
# KapRes2: run the committed xevents8 (Events8Main.lean): the native build $KR/exe/xevents8
# (mkexe.sh) if present and marked READY (after its output was compared with lean --run), else lean --run on the private overlay (mk.sh).  Holds a slot.sh slot.
export PATH=$HOME/.elan/bin:$PATH
KR=${KR:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/KapRes2}
cd /home/user/asyncfpga3/formal/lean
if [ -x $KR/exe/xevents8 ] && [ -e $KR/exe/READY ]; then
  FORMAL_SLOT_CWD=$PWD exec ../slot.sh $KR/exe/xevents8 "$@"
fi
FORMAL_SLOT_CWD=$PWD exec ../slot.sh lake env sh -c 'LEAN_PATH="'$KR'/olean:$LEAN_PATH" exec lean --run Formal/Core/XAudit/Events8Main.lean "$@"' sh "$@"
