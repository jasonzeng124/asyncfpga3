/* Auditor's oracle: dynamatic integration-test/gcd/gcd.c (main branch, fetched 2026-10-27), compiled as is,
   evaluated on the 16 (a,b) pairs of cells/hw/gcd_rig.v; prints a b gcd in hex. */
#include <stdio.h>
#include "gcd_kernel.c"
int main(void){ unsigned v[16][2]={{0,5},{7,0},{0xC,0x12},{0x30,0x12},{1,1},{0x11,5},{0x798F20,0x12B87CA0},{0x42F,0x1CE},{0x10E,0xC0},{0x10000,0x1000},{0x18697,0x18697},{0x1E240,0xC0A14},{0x7FFFFFFF,2},{0xF4240,0xF423F},{0x24,0x3C},{0x400,0x300}};
 for(int i=0;i<16;i++) printf("%d %08X %08X %08X\n",i,v[i][0],v[i][1],(unsigned)gcd((int)v[i][0],(int)v[i][1])); }
