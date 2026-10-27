# Independent derivation: INIT from RTL header equations (I0 = LSB of address)
def init(n, f):
    v=0
    for a in range(1<<n):
        bits=[(a>>i)&1 for i in range(n)]
        if f(*bits): v|=1<<a
    return v
def cel(ins,q):
    if all(ins): return 1
    if not any(ins): return 0
    return q
chk={}
# LUT6 with I5 const handled by including all 6 bits
chk['steer O6(req1=req&s), I5=1 half'] = (init(6,lambda r,s,a,b,c,i5: (r and s) if i5 else (r and not s)), 0x8888888822222222)
chk['dr2bd HOLD O6=t|f (I5=1), O5=maj(t,~f,d)'] = (init(6,lambda t,f,d,b,c,i5: (t or f) if i5 else (1 if (t+(1-f)+d)>=2 else 0)), 0xEEEEEEEEB2B2B2B2)
chk['or2']=(init(2,lambda a,b:a or b),0xE)
chk['c2 !rst&&C(a,b)'] = (init(6,lambda a,b,q,r,i4,i5: (not r) and cel([a,b],q) if not i4 and not i5 else None), None)
# just compute c2 over full 64 with I4,I5 ignored? RTL INIT replicates for I4,I5: compute replicating
chk['c2'] = (init(6,lambda a,b,q,r,i4,i5: (not r) and cel([a,b],q)), 0x00E800E800E800E8)
chk['j0 !rst&&C(x,c&~s)'] = (init(6,lambda x,c,s,q,r,i5: (not r) and cel([x,c and not s],q)), 0x0000AE080000AE08)
chk['j1 !rst&&C(y,c&s)'] = (init(6,lambda y,c,s,q,r,i5: (not r) and cel([y,c and s],q)), 0x0000EA800000EA80)
chk['src ~ack']=(init(1,lambda a: not a),0x1)
chk['buf']=(init(1,lambda a:a),0x2)
chk['ux rst|~(done^ack)']=(init(3,lambda d,a,r: r or not (d^a)),0xF9)
chk['uz s&(rst|~(done^ack))']=(init(4,lambda s,d,a,r: s and (r or not(d^a))),0xAA82)
chk['uck ~rst&(done^ack)']=(init(3,lambda d,a,r: (not r) and (d^a)),0x06)
chk['uq ck?done:req']=(init(3,lambda q,c,d: d if c else q),0xE2)
chk['latch B8 en?d:q (I0 d,I1 en,I2 q)']=(init(6,lambda d,e,q,x,y,z: d if e else q),0xB8B8B8B8B8B8B8B8)
chk['dctl b']=(init(6,lambda req,ack,ld,b,rst,i5: (not rst) and ((req and ld and not ack) or (b and not (ack and not ld))) and not i5 or 0), 0x0000F3200000F320)
chk['dctl a']=(init(6,lambda req,b,ld,a,rst,i5: (not i5) and (not rst) and ((req and b and ld) or (a and not ((not req) and (not ld))))), 0x0000FA800000FA80)
chk['dctl ld']=(init(6,lambda lt,s,a,ld,rst,i5: (not i5) and (not rst) and ((lt and s and not a) or (ld and not a))), 0x00000F0800000F08)
chk['dctl lt']=(init(6,lambda b,a,g,x,y,z: (not b) and (not a) and (not g) and not x and not y and not z), 0x0101010101010101)
chk['and2 gated']=(init(2,lambda s,g: s and g),0x8)
for k,(got,exp) in chk.items():
    if exp is None: continue
    print(('OK  ' if got==exp else 'DIFF'), k, hex(got), hex(exp))
