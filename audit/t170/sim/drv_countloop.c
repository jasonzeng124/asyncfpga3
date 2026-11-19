#include <stdio.h>
int countloop(int,int);
int main(void){ long long a[2]={0,0}; char line[256];
 while(fgets(line,sizeof line,stdin)){ int c=sscanf(line,"%lld %lld",&a[0],&a[1]); if(c<1)continue; printf("%d\n", countloop(a[0],a[1]));} return 0;}
