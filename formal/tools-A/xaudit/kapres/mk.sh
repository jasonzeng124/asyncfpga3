#!/usr/bin/env bash
# Compile the COMMITTED xevents5 module chain (Mathlib-free) into a private olean overlay
# /tmp/kapres/olean, through slot.sh (the lakefile stanza xevents5 exists, but `lake build`
# is the lead's; this avoids touching .lake/build).  Same as events6/mk.sh, other directory.
export PATH=$HOME/.elan/bin:$PATH
OL=${OL:-/tmp/kapres/olean}
cd /home/user/asyncfpga3/formal/lean
mkdir -p $OL /tmp/kapres/mklog
for f in Formal/Core/Kleene.lean Formal/Core/Lut.lean Formal/Core/Circuit.lean Formal/Core/Trace/Discrete.lean \
  Formal/Core/XSim.lean Formal/Core/XAudit/Design.lean Formal/Core/XAudit/Events.lean Formal/Core/XAudit/EventsRing.lean \
  Formal/Core/XAudit/EventsDesign.lean Formal/Core/XAudit/Events2.lean Formal/Core/XAudit/Events2Time.lean \
  Formal/Core/LutCells.lean Formal/Core/XAudit/Events2Design.lean Formal/Core/XAudit/Events2Strict.lean \
  Formal/Core/XAudit/Events2PinDesign.lean Formal/Core/XAudit/Events3.lean Formal/Core/XAudit/Events4.lean \
  Formal/Core/XAudit/Events5Line.lean Formal/Core/XAudit/Events5.lean Formal/Core/XAudit/Events6Gate.lean \
  Formal/Core/XAudit/Events6Cert.lean Formal/Core/XAudit/Events6Design.lean Formal/Core/XAudit/Events6Beh.lean \
  Formal/Core/XAudit/Parse.lean Formal/Core/XAudit/Events5Main.lean; do
  o=$OL/${f%.lean}.olean
  mkdir -p $(dirname $o)
  FORMAL_SLOT_CWD=$PWD ../slot.sh lake env sh -c "LEAN_PATH=\"$OL:\$LEAN_PATH\" exec lean -o \"\$1\" \"\$2\"" sh "$o" "$f" > /tmp/kapres/mklog/$(basename $f).log 2>&1
  echo "$f rc=$? errors=$(grep -c 'error' /tmp/kapres/mklog/$(basename $f).log)"
done
