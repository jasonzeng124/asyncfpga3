#!/usr/bin/env bash
# Which nextpnr is about to produce these numbers?
#
# Every routed number this project quotes belongs to one binary.  Three of the
# four bugs found here were bitstream bugs -- the netlist, the timing report
# and the simulation were all clean and only the bits were wrong -- so "the
# toolchain is patched" is not background, it is part of the measurement, and
# a build against an unpatched binary produces numbers that look exactly as
# plausible as the real ones.
#
# This is not hypothetical.  On 2026-08-20 the DSP const-pin fix was reverted
# in the source tree and rebuilt while the installed binary still carried it:
# three artefacts, two of them wrong, and nothing said so.  Hence a check that
# runs before the flow rather than a note telling someone to remember.
#
# Fingerprints, not version strings.  Each patch leaves a distinctive literal
# in .rodata; a version string would be identical across all four states.
#
# One fingerprint per patch, and only fingerprints that were CHECKED against an
# unpatched binary.  The obvious candidate for the constpins packer half --
# "ALUMODE3", which that half adds as a boost::starts_with literal -- passes on
# an unpatched binary too, so it is not here.  A check that cannot fail is
# worse than no check: it reports "ok" for a broken toolchain.  The fasm half
# discriminates and the two halves ship as one patch, so one line covers it.
set -u
NEXTPNR="${1:-$HOME/dev2/lib/fpgatoolchain/openxc7/bin/nextpnr-xilinx}"

[ -x "$NEXTPNR" ] || { echo "toolchain: no nextpnr at $NEXTPNR" >&2; exit 2; }

# fingerprint                          patch file                      what it fixes
CHECKS=(
  "X_ORIG_PORT_%s names logical input|nextpnr-xilinx-lut-pinmap.patch|131 LUTs written into the bitstream with permuted pins"
  "ZAREG_2_ACASCREG_1|nextpnr-xilinx-dsp-areg.patch|DSP cascade register mode encoded wrong"
  "]_INVERTED|nextpnr-xilinx-dsp-constpins.patch|8 DSP48E1 pins with no route got no bit (INMODE gated A to zero)"
  "Packing RLOC_GROUP relative-placement clusters|nextpnr-xilinx-rloc-group.patch|RLOC_GROUP relative placement (bd_link C node next to its latch)"
)

miss=0
for c in "${CHECKS[@]}"; do
    IFS='|' read -r fp patch what <<< "$c"
    if strings -a "$NEXTPNR" | grep -qF -- "$fp"; then
        printf '  ok      %-38s %s\n' "$patch" "$what"
    else
        printf '  MISSING %-38s %s\n' "$patch" "$what"
        miss=1
    fi
done

SHA=$(sha256sum "$NEXTPNR" | cut -d' ' -f1)
printf '  binary  %s\n' "$NEXTPNR"
printf '  sha256  %s\n' "${SHA:0:16}"

# Provenance has to be recorded when the artefact is MADE, not when it is used.
# A check run just before programming the board reports whichever binary is
# installed at that moment, which is not necessarily the one that built the
# bitstream about to be loaded -- so it can say "ok" over a stale bitstream and
# the stamp would be a lie.  This runs from inside the build, which is the only
# moment the answer is true, and it appends rather than overwrites so a number
# can still be attributed weeks later.  Nobody has to remember to do it.
LOG=${BD_TOOLCHAIN_LOG:-$(dirname "$0")/../build/toolchain.log}
mkdir -p "$(dirname "$LOG")" 2>/dev/null &&
    printf '%s %s %s %s\n' "$(date -Is)" "$SHA" \
        "$([ "$miss" -eq 0 ] && echo ok || echo MISSING)" \
        "${BD_STAMP:-$(basename "$NEXTPNR")}" >> "$LOG" 2>/dev/null || true

if [ $miss -ne 0 ]; then
    echo
    echo "  This binary is missing a patch from patches/.  Any bitstream it"
    echo "  produces may be wrong in a way the netlist and the timing report"
    echo "  will not show.  Rebuild and reinstall before trusting a number:"
    echo "      cd \$TC/openxc7-src/nextpnr-xilinx && git apply -p1 patches/<the one>"
    echo "      cmake --build build -j4 && install -m755 build/nextpnr-xilinx \$TC/openxc7/bin/"
    exit 1
fi
exit 0
