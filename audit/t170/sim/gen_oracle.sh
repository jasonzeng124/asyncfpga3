#!/bin/bash
# my own gcc build of each kernel's C: reads "a [b]" lines, prints result (or NT if exceeds step cap, n/a here)
set -e
RS=/root/agentJ/rs/kernels
for k in xorshift collatz ipow countloop isprime sqrtsub; do
  n=$(grep -o "in_int_t [a-z]*[,)]" <(grep "^int $k(" $RS/$k/$k.c) | wc -l)
  if [ "$n" = 2 ]; then call="$k(a[0],a[1])"; proto="int $k(int,int);"; else call="$k(a[0])"; proto="int $k(int);"; fi
  cat > drv_$k.c <<EOC
#include <stdio.h>
$proto
int main(void){ long long a[2]={0,0}; char line[256];
 while(fgets(line,sizeof line,stdin)){ int c=sscanf(line,"%lld %lld",&a[0],&a[1]); if(c<1)continue; printf("%d\n", $call);} return 0;}
EOC
  gcc -O1 -fwrapv -w -I/root/agentJ/sim/inc -Dmain=kernel_main -I$RS/$k -c $RS/$k/$k.c -o k_$k.o
  gcc -O1 -w drv_$k.c k_$k.o -o oracle_$k
done
echo built
