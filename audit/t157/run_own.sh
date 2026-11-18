#!/usr/bin/env bash
# run_own.sh: build each kernel with agentA's driver under several compilers/flags, run every vector.
set -u
A=/root/agentA; R=/root/wt-rh
mkdir -p $A/out $A/bin
declare -A LENS=( [factorial]="" [iterative_division]="" [iterative_sqrt]="" [test_int16]="" [test_loop_free]=""
  [unused_arg]="1" [if_loop_1]="100" [if_loop_2]="100" [sumi3_mem]="1000" [fir]="1000 1000" [dot2]="32 32"
  [gather]="32 32" [memsum]="32" [test_bitint]="10 10" )
for k in factorial iterative_division iterative_sqrt test_int16 test_loop_free unused_arg if_loop_1 if_loop_2 sumi3_mem fir test_bitint dot2 gather memsum; do
  if [ -d $R/kernels/$k ]; then S=$R/kernels/$k; V=$S/vec.hex; else S=$R/research/data/suite/dynsrc/$k; V=$R/research/data/suite/vec/$k.hex; fi
  python3 $A/flat.py $V ${LENS[$k]} > $A/out/$k.flat || { echo "$k: flat failed"; continue; }
  if [ $k = test_bitint ]; then CFGS="clang:-O0 clang:-O2 clang:-O0_-fwrapv clang:-O2_-fwrapv"
  else CFGS="gcc:-O0 gcc:-O2 gcc:-O0_-fwrapv gcc:-O2_-fwrapv gcc:-O3 clang:-O2 gcc:-O1_-fsanitize=undefined,address_-fsanitize-recover=all"; fi
  for cf in $CFGS; do
    cc=${cf%%:*}; fl=${cf#*:}; fl=${fl//_/ }; tag=$(echo "$cf" | tr -c 'A-Za-z0-9\n' '_' | cut -c1-40)
    $cc $fl -w -Dmain=kmain_unused -I$A/stub -I$S -c $S/$k.c -o $A/bin/$k.$tag.k.o && \
    $cc $fl -w -DK_$k -c $A/drv.c -o $A/bin/$k.$tag.d.o && $cc $fl $A/bin/$k.$tag.k.o $A/bin/$k.$tag.d.o -o $A/bin/$k.$tag || { echo "$k $cf: build failed"; continue; }
    for fill in 0 0xa5a5a5a5; do
      [ $k != unused_arg ] && [ $fill != 0 ] && continue
      sfx=""; [ $k = unused_arg ] && sfx=".fill$fill"
      ASAN_OPTIONS=halt_on_error=0:detect_leaks=0 UBSAN_OPTIONS=halt_on_error=0:print_stacktrace=0 \
        $A/bin/$k.$tag $fill < $A/out/$k.flat > $A/out/$k.$tag$sfx.res 2> $A/out/$k.$tag$sfx.err
    done
  done
done
# test_bitint under UBSan in trap mode (this clang has no sanitizer runtimes), one process per call
S=$R/research/data/suite/dynsrc/test_bitint
clang -O1 -fsanitize=undefined,bounds -fsanitize-trap=all -w -Dmain=kmain_unused -I$A/stub -I$S -c $S/test_bitint.c -o $A/bin/tb.k.o
clang -O1 -fsanitize=undefined -fsanitize-trap=all -w -DK_test_bitint -c $A/drv.c -o $A/bin/tb.d.o
clang -fsanitize=undefined -fsanitize-trap=all $A/bin/tb.k.o $A/bin/tb.d.o -o $A/bin/tb_trap
while read l; do echo "$l" | $A/bin/tb_trap 2>/dev/null || echo "TRAP ${l:0:12}"; done < $A/out/test_bitint.flat > $A/out/test_bitint.trap.res
