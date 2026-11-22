#include <stdio.h>
#include <stdlib.h>
int collatz(int n){int steps=0; while(n!=1){ if((n&1)==0) n=n>>1; else n=3*n+1; steps=steps+1;} return steps;}
int main(int c,char**v){for(int i=1;i<c;i++)printf("RES %d %d\n",atoi(v[i]),collatz(atoi(v[i])));}
