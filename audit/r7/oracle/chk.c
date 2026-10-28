#include <stdio.h>
#include "gcd_kernel.c"
#include "tab.h"
int main(void){int bad=0;for(int i=0;i<16;i++){unsigned r=(unsigned)gcd((int)T[i][0],(int)T[i][1]);
printf("%2d a=%08X b=%08X table=%08X C=%08X %s\n",i,T[i][0],T[i][1],T[i][2],r,r==T[i][2]?"ok":"MISMATCH");bad+=r!=T[i][2];}
printf("mismatches %d\n",bad);return bad;}
