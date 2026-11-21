# Frontend fixtures with the exit-test rewrite (BDC_FE_EXITCOND=1)

`bdc/frontend.sh <kernel>` with `BDC_FE_EXITCOND=1` (step 4b: one LLVM `indvars` + `simplifycfg` with the data layout
"e-n32", stripped again: LLVM's own proven rewrite of a loop's exit test, e.g. `i + 1 < n` -> `i + 1 != n`), run on the
cluster on 2026-11-20 with the owner's Dynamatic build in $HOME/dynamatic, at research commit e328ccdfd. Only the 37
kernels of research/tools/suite/kernels.txt whose handshake MLIR differs from cloud/fixtures/frontend are here; the
other 25 come out byte-identical. The same script without the knob reproduces cloud/fixtures/frontend (xorshift
checked, 601170a0). Per kernel, what changed in handshake_transformed.mlir (diff lines; the new cmpi predicates):
    xorshift changed-lines=2       1 cmpi ne 
    gcd changed-lines=2       1 cmpi ult 
    isprime changed-lines=16       1 cmpi sgt 
    countloop changed-lines=2       1 cmpi ne 
    nest3 changed-lines=170       3 cmpi ne 
    twoloops changed-lines=60       2 cmpi ne 
    brhash changed-lines=2       1 cmpi ne 
    lfsrfind changed-lines=89       1 cmpi eq       1 cmpi ne 
    quadrec changed-lines=2       1 cmpi ne 
    horner changed-lines=2       1 cmpi ne 
    fold64 changed-lines=94       1 cmpi ne       1 cmpi ult 
    varshift changed-lines=2       1 cmpi ne 
    nested changed-lines=4       2 cmpi ne 
    memsum changed-lines=100       1 cmpi ne 
    dot2 changed-lines=100       1 cmpi ne 
    gather changed-lines=108       1 cmpi ne 
    fill changed-lines=2       1 cmpi ne 
    test_bitint changed-lines=67       1 cmpi ne 
    if_loop_1 changed-lines=2       1 cmpi ne 
    if_loop_2 changed-lines=2       1 cmpi ne 
    sumi3_mem changed-lines=52       1 cmpi ne 
    fir changed-lines=67       1 cmpi ne 
    test_memory_1 changed-lines=2       1 cmpi ne 
    test_memory_2 changed-lines=2       1 cmpi ne 
    mul_example changed-lines=38       1 cmpi ne 
    share_test_2 changed-lines=189       1 cmpi ne 
    test_stdint changed-lines=40       1 cmpi ne 
    spmv changed-lines=4       2 cmpi ne 
    sobel changed-lines=335       2 cmpi eq       4 cmpi ne       1 cmpi ult 
    test_flatten_array changed-lines=260       3 cmpi ne 
    image_resize changed-lines=152       2 cmpi ne 
    vector_rescale changed-lines=34       1 cmpi ne 
    stencil_2d changed-lines=252       3 cmpi ne 
    iir changed-lines=44       1 cmpi ne 
    share_test_1 changed-lines=133       2 cmpi ne 
    nested_loop changed-lines=141       1 cmpi ne       1 cmpi slt 
    video_filter changed-lines=310       2 cmpi ne 
A 2-line change is the loop test's predicate alone (slt -> ne on xorshift, countloop, brhash, quadrec, horner,
varshift, fill, if_loop_1 / 2, test_memory_1 / 2); a larger one is indvars restructuring the loop (trip-count
arithmetic, widened or merged induction variables). Correctness is LLVM's proof plus, as for every fixture, the draws
against the C oracle on every route; nothing here has been routed yet.
