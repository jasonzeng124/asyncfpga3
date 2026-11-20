#!/usr/bin/env python3
"""mr_expr_check.py FIXTURES_DIR BDC_DIR [K=V,...] [--vectors N] [--ctl flipbit]
Does each BDC_RING_FUSE multi-result cell's emitted Verilog COMPUTE what fuse_check's model of it computes?
(The part audit T170 left open after mr_verilog_check.py: that checks the layout, this checks the values.)

For every kernel FIXTURES_DIR/<k>/comp/handshake_transformed.mlir (env default BDC_AUTO=1):
  1. bdc's emit.py --no-top writes the Verilog; each `bdc_fused_<inst>` module whose z_data packs two or more parts.
  2. fuse_check's importer (dfimport + MR_NEW) imports the same MLIR with the same env; its side record (FA_MR_LOG)
     names, for each packed comp, the region members it packs, so each model cell is paired with the Verilog module
     whose z_data packs w_n<member> for exactly those members.
  3. iverilog simulates the module (its handshake cells stubbed; LUT1 as its INIT table; the datapath as emitted)
     on N input vectors: per input every combination of 0, 1, 2, -1, INT_MIN, INT_MAX of its width where the count
     allows, then random. z_data is compared with the model expression evaluated with the Lean Ops semantics
     (formal/lean/Formal/Net/GcdHwLib.lean: addi / subi / ... / cmpi via the sign flip / select / extsi ...).
     The model's inputs are the region's external inputs in order; the Verilog's e0..eK ports in the same order.
Prints one line per kernel: OK (cells, vectors) / MISMATCH (cell, vector, model, verilog) / no multi-result cell /
emit / import / sim failed / unpaired. Exit 2 on MISMATCH or unpaired, 3 if some kernel was not checked, else 0.
Control --ctl flipbit: bit 0 of the first cell's z_data is inverted in the Verilog -> must MISMATCH.
Untrusted (simulation on finitely many vectors; iverilog's Verilog semantics).
"""
import contextlib, io, itertools, os, random, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fuse_check as F          # noqa: E402
import mr_verilog_check as MV   # noqa: E402

# ---- the Lean Ops semantics (GcdHwLib.lean), on Nat ----
def flip(w, a): return (a % 2 ** w + 2 ** (w - 1)) % 2 ** w
def shrsi(w, a, b):
    x = a % 2 ** w
    return x >> b if x < 2 ** (w - 1) else (2 ** w - 1) - ((2 ** w - 1 - x) >> b)
def cmpi(p, w, a, b):
    x, y, sx, sy = a % 2 ** w, b % 2 ** w, flip(w, a), flip(w, b)
    return int({'eq': x == y, 'ne': x != y, 'ult': x < y, 'ule': x <= y, 'ugt': y < x, 'uge': y <= x,
                'slt': sx < sy, 'sle': sx <= sy, 'sgt': sy < sx, 'sge': sy <= sx}[p])
BIN = {'addi': lambda w, a, b: (a + b) % 2 ** w, 'subi': lambda w, a, b: (a % 2 ** w + 2 ** w - b % 2 ** w) % 2 ** w,
       'muli': lambda w, a, b: (a * b) % 2 ** w, 'andi': lambda w, a, b: (a & b) % 2 ** w,
       'ori': lambda w, a, b: (a | b) % 2 ** w, 'xori': lambda w, a, b: (a ^ b) % 2 ** w,
       'shli': lambda w, a, b: (a << b) % 2 ** w, 'shrui': lambda w, a, b: (a % 2 ** w) >> b, 'shrsi': shrsi}

def ev(e, env):
    k = e[0]
    if k == 'var': return env[e[1]] if e[1] < len(env) else 0
    if k == 'lit': return e[1]
    if k == 'sel': return ev(e[2], env) if ev(e[1], env) % 2 == 1 else ev(e[3], env)
    if k == 'un':
        o, w, a = e[1], e[2], ev(e[3], env)
        if o[0] in ('trunci', 'extui'): return a % 2 ** w
        if o[0] == 'extsi':
            dw = o[1]; x = a % 2 ** w
            return x if x < 2 ** (w - 1) else x + 2 ** dw - 2 ** w
        raise ValueError(o)
    if k == 'bin':
        o, w, a, b = e[1], e[2], ev(e[3], env), ev(e[4], env)
        if o[0] == 'cmpi': return cmpi(o[1][0], w, a, b)
        return BIN[o[0]](w, a, b)
    raise ValueError(e)

STUBS = r"""
module bd_join #(parameter N = 2) (input wire rst, input wire [N-1:0] req_in, output wire [N-1:0] ack_out,
    output wire req, input wire ack);
  assign ack_out = {N{1'b0}}; assign req = 1'b0;
endmodule
module bd_delay_gated #(parameter N = 1) (input wire a, input wire gate, output wire z); assign z = a; endmodule
module LUT1 #(parameter [1:0] INIT = 2'h0) (input wire I0, output wire O); assign O = INIT[I0]; endmodule
module LUT2 #(parameter [3:0] INIT = 4'h0) (input wire I0, I1, output wire O); assign O = INIT[{I1, I0}]; endmodule
"""

def edges(w):
    m = 2 ** w
    return sorted({0, 1, 2 % m, m - 1, 2 ** (w - 1), 2 ** (w - 1) - 1})

def vectors(widths, n, seed):
    rng = random.Random(seed)
    combos = list(itertools.product(*[edges(w) for w in widths]))
    if len(combos) > n // 2: combos = rng.sample(combos, n // 2)
    out = [list(c) for c in combos]
    while len(out) < n: out.append([rng.randrange(2 ** w) for w in widths])
    return out

def sim_module(mod_text, name, widths, W, vecs, td):
    """Run module `name` on vecs; return [z_data] or None."""
    ports = ''.join(f'  reg [{w - 1}:0] e{i};\n' for i, w in enumerate(widths))
    conn = ', '.join([f'.e{i}_data(e{i}), .e{i}_req(1\'b0)' for i in range(len(widths))])
    lines = []
    for v in vecs:
        lines.append(' '.join(f'e{i} = {w}\'h{x:x};' for i, (x, w) in enumerate(zip(v, widths))) +
                     ' #1 $display("%h", z);')
    tb = (f"module tb;\n{ports}  wire [{W - 1}:0] z;\n  {name} dut(.rst(1'b0), {conn}, .z_ack(1'b0), .z_data(z));\n"
          "  initial begin\n    " + '\n    '.join(lines) + "\n    $finish;\n  end\nendmodule\n")
    f = os.path.join(td, name + '.v')
    open(f, 'w').write('`timescale 1ns/1ps\n' + STUBS + mod_text + '\n' + tb)
    exe = os.path.join(td, name + '.vvp')
    p = subprocess.run(['iverilog', '-g2012', '-o', exe, '-s', 'tb', f], capture_output=True, text=True)
    if p.returncode != 0: return None, p.stderr[-400:]
    p = subprocess.run(['vvp', '-n', exe], capture_output=True, text=True, timeout=600)
    outs = [l.strip() for l in p.stdout.splitlines() if re.fullmatch(r'[0-9a-fA-FxXzZ]+', l.strip())]
    if len(outs) != len(vecs): return None, 'vvp printed %d of %d' % (len(outs), len(vecs))
    return [int(o, 16) if re.fullmatch(r'[0-9a-fA-F]+', o) else None for o in outs], ''

def check(mlir, bdc, env, nvec):
    e = dict(os.environ); e.update(env)
    with tempfile.TemporaryDirectory() as td:
        vf = os.path.join(td, 'k.v')
        p = subprocess.run([sys.executable, os.path.join(bdc, 'emit.py'), mlir, '--no-top', '-o', vf], env=e,
                           capture_output=True, text=True)
        if p.returncode != 0 or not os.path.exists(vf): return 'emit failed'
        v = open(vf).read()
        F.PP.BDCDIR = bdc
        lf = os.path.join(td, 'mr.log'); open(lf, 'w').close()
        try:
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                R = F.imp(mlir, os.path.join(td, 'm.lean'), 'M', dict(env, FA_MR_LOG=lf))[0]
            t = open(os.path.join(td, 'm.lean')).read()
            names = eval(re.search(r'def chanNames : List String := (\[.*?\])\n', t).group(1))
        except Exception:
            return 'import failed'
        log = {}
        for line in open(lf):
            rec = eval(line); log[rec[0]] = (rec[1], rec[2])
        model = {}   # frozenset of part wire names -> (inputs, expr, W)
        for r in R:
            if r[0] != 'comp' or r[2] >= len(names): continue
            m = re.fullmatch(r'__mr_(\d+)', names[r[2]])
            if not m or int(m.group(1)) not in log: continue
            parts, ext = log[int(m.group(1))]
            model[frozenset(f'w_n{mi}' for _, _, _, mi in parts)] = (r[1], r[3], sum(w for _, w, _, _ in parts), ext)
        mods = {}
        for m in re.finditer(r"module (bdc_fused_\w+) .*?endmodule", v, re.S):
            body = m.group(0); a = re.search(r"assign z_data = \{", body)
            if not a: continue
            inner, _ = MV.concat_body(body, a.end() - 1)
            parts = [at for item in MV.split_top(inner) for at in MV.atoms(item, body)]
            if len(parts) < 2: continue
            mods[frozenset(nm for nm, _ in parts if nm)] = (m.group(1), body)
        if not model and not mods: return 'no multi-result cell'
        if set(model) != set(mods):
            return f'MISMATCH: unpaired cells: model {sorted(map(sorted, model))} verilog {sorted(map(sorted, mods))}'
        nv = 0; first = True
        for key, (name, body) in sorted(mods.items(), key=lambda x: x[1][0]):
            ins, expr, W, ext = model[key]
            widths = [int(x.group(1)) + 1 for x in sorted(re.finditer(r"input\s+wire\s+\[(\d+):0\]\s*e(\d+)_data", body),
                                                                key=lambda x: int(x.group(2)))]
            zw = int(re.search(r"output wire \[(\d+):0\]\s*z_data", body).group(1)) + 1
            # the Verilog joins on every external input; the model reads the live ones (constants are literals)
            live = [k for k, x in enumerate(ext) if x == 'live']
            if len(widths) != len(ext) or len(live) != len(ins):
                return f'MISMATCH: {name}: {len(widths)} Verilog inputs, {len(ext)} region inputs, {len(ins)} live model inputs'
            if zw != W: return f'MISMATCH: {name}: z_data {zw} bits, model {W}'
            mt = body
            if CTL == 'flipbit' and first:
                mt = re.sub(r"assign z_data = (\{.*?\});", r"assign z_data = \1 ^ 1;", body, count=1, flags=re.S)
            first = False
            lv = vectors([widths[k] for k in live], nvec, 1)
            vecs = []
            for x in lv:   # constant inputs driven with their value (None: a bare source, driven 0)
                it = iter(x); vecs.append([next(it) if c == 'live' else (c or 0) % 2 ** widths[k] for k, c in enumerate(ext)])
            got, err = sim_module(mt, name, widths, W, vecs, td)
            if got is None: return f'sim failed: {name}: {err}'
            for x, vec, g in zip(lv, vecs, got):
                want = ev(expr, x) % 2 ** W
                if g != want:
                    return f'MISMATCH: {name}: inputs {[hex(x) for x in vec]} model {want:#x} verilog {g if g is None else hex(g)}'
            nv += len(vecs)
    return f'OK ({len(mods)} cell(s), {nv} vectors)'

CTL = None

def main():
    global CTL
    args = sys.argv[1:]; nvec = 200
    if '--ctl' in args: i = args.index('--ctl'); CTL = args[i + 1]; del args[i:i + 2]
    if '--vectors' in args: i = args.index('--vectors'); nvec = int(args[i + 1]); del args[i:i + 2]
    if len(args) < 2: print(__doc__); return 1
    fx, bdc = args[0], os.path.abspath(args[1])
    env = F.parse_env(args[2]) if len(args) > 2 else {'BDC_AUTO': '1'}
    rc = 0
    for k in sorted(os.listdir(fx)):
        m = os.path.join(fx, k, 'comp', 'handshake_transformed.mlir')
        if not os.path.exists(m): continue
        r = check(m, bdc, env, nvec)
        if r.startswith('MISMATCH'): rc = 2
        elif ('failed' in r) and rc == 0: rc = 3
        print(f'{k:28s} {r}', flush=True)
    return rc

if __name__ == '__main__':
    sys.exit(main())
