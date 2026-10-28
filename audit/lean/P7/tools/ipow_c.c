#include <stdio.h>
#include <stdint.h>
int ipow(int b, int e){int r=1;while(e>0){if((e&1)==1)r=r*b;b=b*b;e=e>>1;}return r;}
int main(){unsigned v[][2]={{3,7},{2,31},{2,32},{0xFFFFFFFFu,3},{5,0x80000000u},{7,0x7FFFFFFFu},{123456789,987654321},{0xDEADBEEF,0x1234}};
for(int i=0;i<8;i++) printf("%u %u %u\n",v[i][0],v[i][1],(unsigned)ipow((int)v[i][0],(int)v[i][1]));}
