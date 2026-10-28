# compare cf_transformed.mlir semantics (i32 wrap) with Lean ipowSpec (re-typed from IpowHwLive.lean:39)
import random
M=1<<32
def s32(x): x%=M; return x-M if x>=1<<31 else x
def mlir(b,e):
    b%=M; e%=M
    if not s32(e)>0: return 1
    x1,x2,x3=b,e,1
    while True:
        r7 = x3 if (x2&1)==0 else (x3*x1)%M
        x8=(x1*x1)%M; x9=(s32(x2)>>1)%M
        if s32(x9)>0: x1,x2,x3=x8,x9,r7
        else: return r7
def spec(b,e): return pow(b,e,M) if e<2**31 else 1
random.seed(7)
V=[(0,0),(0,1),(1,0),(3,7),(2,31),(2,32),(2,33),(0xFFFFFFFF,2),(0xFFFFFFFF,3),(7,0x7FFFFFFF),(5,0x80000000),(5,0xFFFFFFFF),(0x10000,2),(3,40)]
V+=[(random.getrandbits(32),random.getrandbits(32)) for _ in range(3000)]
V+=[(random.getrandbits(32),random.getrandbits(8)) for _ in range(3000)]
bad=[v for v in V if mlir(*v)!=spec(*v)]
print(len(V),'vectors, mismatches',len(bad),bad[:5])
print('ipow(3,7)=',mlir(3,7),' ipow(2,32)=',mlir(2,32),' ipow(0xFFFFFFFF,3)=',hex(mlir(0xFFFFFFFF,3)))
