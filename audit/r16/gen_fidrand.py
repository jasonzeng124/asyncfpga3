# audit r16: random-trace cross-check of formal GLSFid (fidO6/fidO5/fidMux2 = perPin with
# pinDelay = max(T+off-1,0)+1) against the unmodified fid_core.vh FID_LUT6 / FID_MUX2.
# usage: gen_fidrand.py SEED K END outdir  -> writes tb_fidrand.v and stim.json
import sys, random, json
seed, K, END, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
def wave():
    # random edge times; clustered so coincident edges and 1 ps pulses are frequent
    ts = set(); t = rng.randint(0, 50)
    while t < END - 600:
        ts.add(t)
        r = rng.random()
        t += 1 if r < 0.15 else rng.randint(2, 6) if r < 0.3 else rng.randint(7, 400)
    if rng.random() < 0.3: ts.add(0)   # a change exactly at time 0
    return sorted(ts)
cells = []
for k in range(K):
    T6 = [rng.choice([0, 1, 2, rng.randint(1, 300), rng.randint(40, 130)]) for _ in range(6)]
    T5 = [rng.choice([0, 1, rng.randint(1, 300), rng.randint(40, 130)]) for _ in range(5)]
    INIT = rng.getrandbits(64) if rng.random() < 0.7 else rng.choice(
        [0x6666666666666666, 0x9669699669969669, 0xFFFF0000FFFF0000 ^ rng.getrandbits(64) & 0xFF00FF])
    cells.append(dict(kind='lut', INIT=INIT, T6=T6, T5=T5, w=[wave() for _ in range(6)]))
for k in range(K // 4):
    T = [rng.choice([0, 1, rng.randint(1, 300)]) for _ in range(3)]
    cells.append(dict(kind='mux', T=T, w=[wave() for _ in range(3)]))
L = ['`timescale 1ps/1ps', 'module tb_fidrand;']
for i, c in enumerate(cells):
    n = 6 if c['kind'] == 'lut' else 3
    L.append(f'  reg [{n-1}:0] in{i} = 0; wire o6_{i}, o5_{i};')
    if c['kind'] == 'lut':
        p = ', '.join([f".INIT(64'h{c['INIT']:016x})"] + [f'.T{j+1}_6({c["T6"][j]})' for j in range(6)]
                      + [f'.T{j+1}_5({c["T5"][j]})' for j in range(5)])
        L.append(f'  FID_LUT6 #({p}) u{i} (.A1(in{i}[0]), .A2(in{i}[1]), .A3(in{i}[2]), .A4(in{i}[3]), '
                 f'.A5(in{i}[4]), .A6(in{i}[5]), .EN6(1\'b0), .EN5(1\'b0), .O5(o5_{i}), .O6(o6_{i}));')
    else:
        L.append(f'  FID_MUX2 #(.TD0({c["T"][0]}), .TD1({c["T"][1]}), .TS0({c["T"][2]})) u{i} '
                 f'(.D0(in{i}[0]), .D1(in{i}[1]), .S0(in{i}[2]), .OUT(o6_{i})); assign o5_{i} = 1\'b0;')
    L.append(f'  always @(o6_{i}) $display("O %0d 6 %b %0t", {i}, o6_{i}, $time);')
    L.append(f'  always @(o5_{i}) $display("O %0d 5 %b %0t", {i}, o5_{i}, $time);')
    for j, ts in enumerate(c['w']):
        body = []; prev = 0
        for t in ts:
            body.append(f'#{t-prev} in{i}[{j}] = ~in{i}[{j}];'); prev = t
        L.append(f'  initial begin {" ".join(body)} end')
L.append(f'  initial begin #{END} $display("END"); $finish; end')
L.append('endmodule')
open(f'{out}/tb_fidrand.v', 'w').write('\n'.join(L) + '\n')
json.dump(dict(END=END, cells=cells), open(f'{out}/stim.json', 'w'))
