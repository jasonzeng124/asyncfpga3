# BOARD-QUEUE #1 route reproduction (claude/research 19a93c1)

Clean worktree ../wt-rb1 at 19a93c1; fixtures copied to build/frontend (cloud/fixtures: the MLIR is a recorded
Dynamatic output, not regenerated -- Dynamatic is not built here). Toolchain: cloud/setup-toolchain.sh (cache),
nextpnr sha256 9c732bc6303458dfed297c4099b6b9d75d912b64100b574d8c815fb8e2f411d4.
Command: cd cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw  -> build_hw.sh PASS (2m48s)

Results (run 1 TC=/root/audit-tc; run 2 the same toolchain copied to /root/dev2/lib/fpgatoolchain, their path):
- gcd_hw.sdf md5 6f8b99e6c49bb7ef8855c881cecabe5c (both runs) = claimed 6f8b99e6. CONFIRMED.
- gcd_hw.bit vs committed research/board/gcd_hw_03e82630.bit: cmp -l -> 7 differing bytes, offsets 102-114, all
  inside the bitstream header's date ("2026/10/27" vs "2026/10/25") and time fields. Configuration payload
  byte-identical. CONFIRMED (the committed bit is what this source + toolchain produces). The claim "3 header
  bytes differ" is slightly off (7 here, date and time), immaterial.
- gcd_hw_routed.json md5: run1 1fce68f0 (contains 6815 absolute toolchain paths from yosys src attributes),
  run2 5703039032088ede6776809354a260fa; claimed 1c6a1fb9. NOT reproduced. The json embeds absolute paths of
  the toolchain; the claimed md5 presumably depends on the owner's/agent's exact paths. Because the SDF and the
  bit payload are identical, I read this as path metadata, but it is UNVERIFIED: routed.json md5 is not a
  portable reproducibility check, and BOARD-QUEUE #2/#3 tell the reader to compare exactly that md5.
