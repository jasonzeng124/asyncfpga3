# Dynamatic's integer tests that emit through bdc: their C, for the oracles

Copied byte for byte (suitew, 2026-11-17) from `$HOME/dynamatic/integration-test/<name>/` -- the Dynamatic tree
`bdc/frontend.sh` reads through the `dynamatic` link (not a git checkout, so there is no commit to quote; the sha256
of every file is below). Sources only: each test's `.c` and, where the test has one, its `.h`. Not edited.

Why here: a farm task has no `dynamatic/` directory, and the suite's expected values are compiled from the C at run
time (`research/tools/suite/oracle.sh`, `oracle_mem.sh` look in `kernels/<name>/`, then here, then
`dynamatic/integration-test/<name>/`). Why not `kernels/<name>/`: a directory there shadows Dynamatic's test in
`bdc/frontend.sh`. The frontend output of each test is `cloud/fixtures/frontend/<name>/comp/`; vectors are
`research/data/suite/vec/<name>.hex`; the suite rows are in `kernels/SUITE.md`. `gcd` (already in the suite) keeps
its own oracle, `research/data/gcd_draws/gcd_oracle.sh`.

```
2112e35b84271f9bc695ff7e6a269a8550c81f9b535d80f09ea6abcd63a20f73  factorial/factorial.c
30ef2ab4e4d0795a93d096b9d48d0da8800425b8737dcfbe44a6249cb46b620a  factorial/factorial.h
d4edd8bfb2a6481e592aaa9751acdd0b3d245ce8db1216a7ca6684238a9e5f28  fir/fir.c
8a0796c47f5f80812a5ed6d2d43865ae6598da2b709a09672514f01bdb0ae957  fir/fir.h
036f58d962370e3da7993d490b6125015a5f2104aed6bafb06516f7f654f162b  if_loop_1/if_loop_1.c
4215bb450b90abdb8a584e5a22903a31c540f3f737b1392c53293e3a926001d8  if_loop_1/if_loop_1.h
f576a069828aae8c0e5093f48f97996dd18d3cbbf28f138d3d05b06b189f27e9  if_loop_2/if_loop_2.c
ddc55fd0006119dafedb144d820d6e90ea717d26266f31aa152493701f62743b  if_loop_2/if_loop_2.h
eafc7d41441e8f145ce7d31116acdabb068a280ad6c078b88f50c173e34c10cb  iterative_division/iterative_division.c
823c896031375fe4e908202e118c7b470c238358fa4a805d34cfacdae812323e  iterative_division/iterative_division.h
2e21f1202c2529a102e7469f172935599470bf7f745a7874aed719d5fc075384  iterative_sqrt/iterative_sqrt.c
22be33417db731588aa62de04f635b80e81bec2c5333b19998d94d48cf24b6cf  iterative_sqrt/iterative_sqrt.h
f712d58a98799ae4e2777b2475a87531bb85d43f241d9892dcb2275b640a15c3  sumi3_mem/sumi3_mem.c
05a97e00f8049aa92d7a76f66675c8007b0ae64c579b57f036d80b59a55ae002  sumi3_mem/sumi3_mem.h
3752157c6573353902f37983cd66fa78abc7386841cc81a69ef44fc15794b5a2  test_bitint/test_bitint.c
1351736b34fe8e08b2d1d4ed1f6844e5b01a770bd9cffab64592d52a02d16d33  test_int16/test_int16.c
979044cd41773a523cae8d143fdb329fc7642508c48fa82c8070394fd651e6ca  test_loop_free/test_loop_free.c
51cc0885523a83fa73ca98bb744165e684b71a75d630a7b63166e2b9fe04c3ef  unused_arg/unused_arg.c
```
