"""token-level loop structure of bdc's binary gcd (GcdHw.lean), per pair: list of loop-head visits with branch values"""
import sys
def tz(x):
    n=0
    while x and x%2==0: x//=2; n+=1
    return n
def run(a,b):
    tr=[]
    if a==0 or b==0: return [("zero",)]
    s=0
    if (a|b)&1==0:
        while True:
            a>>=1;b>>=1;s+=1; c=((a|b)&1)==0; tr.append(("L2",c))
            if not c: break
    # strip a
    while True:
        ex=(a&1)!=0 or a<1; tr.append(("L4",not ex))
        if ex: break
        a>>=1
    while True:
        ex=(b&1)!=0 or b<1; tr.append(("L6",not ex))
        if ex: break
        b>>=1
    z=(b==0); tr.append(("Z8",z))
    if not z:
      while True:
        a,b=min(a,b),abs(a-b)   # cm9 head
        tr.append(("L9",))
        while True:
            ex=(b&1)!=0 or b<1; tr.append(("L10",not ex))
            if ex: break
            b>>=1
        z=(b==0); tr.append(("Z10",z))
        if z: break
    return tr, a<<s
if __name__=="__main__":
    a,b=int(sys.argv[1]),int(sys.argv[2]); tr,g=run(a,b); import math
    print(g, math.gcd(a,b)); print(tr)
