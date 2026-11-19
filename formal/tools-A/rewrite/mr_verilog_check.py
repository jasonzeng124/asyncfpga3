#!/usr/bin/env python3
"""mr_verilog_check.py FIXTURES_DIR BDC_DIR [K=V,...] -- does fuse_check's model of a BDC_RING_FUSE multi-result cell
(fuse_check.py MR_NEW: one cell whose value packs every result, first in the low bits; a fork; one slice per result)
have the same LAYOUT as the Verilog bdc emits for it?

For every kernel FIXTURES_DIR/<k>/comp/handshake_transformed.mlir (env default BDC_AUTO=1):
  1. bdc's emit.py --no-top writes the Verilog. In each `bdc_fused_<inst>` module whose `assign z_data = {...}` packs
     two or more wires: the parts low to high, each part's declared wire width, z_data's width.
     In the top module: every `<inst>_zdata[hi:lo]` slice.
  2. fuse_check's importer (dfimport + MR_NEW) imports the same MLIR with the same env. Each packed comp:
     its parts' offsets (`addi W (... ) (shli W e lo)`), W, and its slices' (lo, w) (`trunci w (shrui W v lo)`).
  3. Checks: the Verilog's parts tile z_data exactly (offsets = running sums of the declared widths); its slices are
     exactly those windows; the model has the same number of packed cells, the same W, the same offsets, and the same
     (window, result) pairs -- each result (bdc's SSA name) reads the same window in the model as in the Verilog.
Prints one line per kernel: OK (cells checked) / MISMATCH (what) / no multi-result cell / import or emit failed.
NOT covered: that each part's Verilog expression computes the model's expression (the general trust in bdc's region
Verilog, compute.py / emit.py, the same as for every fused cell); anything below the netlist.
"""
import io, contextlib, os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fuse_check as F   # noqa: E402

def verilog_cells(v):
    """[(W, [(lo, w), ...] parts low to high, inst)] from the fused modules; {inst: [(lo, w)]} slices from the top."""
    cells = {}
    for m in re.finditer(r"module bdc_fused_(\w+) .*?endmodule", v, re.S):
        inst, body = m.group(1), m.group(0)
        a = re.search(r"assign z_data = \{([^}]*)\};", body)
        if not a: continue
        parts = [p.strip() for p in a.group(1).split(',')]
        if len(parts) < 2: continue
        zw = re.search(r"output wire \[(\d+):0\]\s*z_data", body)
        W = int(zw.group(1)) + 1
        widths = []
        for p in reversed(parts):   # low to high
            d = re.search(r"wire \[(\d+):0\] " + re.escape(p) + r"\b", body)
            widths.append(int(d.group(1)) + 1 if d else 1)
        lo, lay = 0, []
        for w in widths: lay.append((lo, w)); lo += w
        cells[inst] = (W, lay)
    slices = {}
    for inst in cells:
        for m in re.finditer(re.escape(inst) + r"_zdata\[(\d+):(\d+)\]", v):
            hi, lo = int(m.group(1)), int(m.group(2))
            line = v[v.rfind('\n', 0, m.start()) + 1:v.find('\n', m.end())]
            nm = re.search(r"\.req_in\((\w+)_freq\)", line) or re.search(r"assign (\w+?)(?:_u)?_data = ", line)   # bdc: odata = <vname>[_u]_data (_u: linked)
            slices.setdefault(inst, set()).add((lo, hi - lo + 1, nm.group(1) if nm else '?'))
    return cells, slices

def vname_of(ssa):
    return 'n' + ssa.replace('#', '__')

def model_cells(R, names):
    """[(W, offsets, slice windows)] for every packed comp of the imported rules."""
    import eq2_check as Q
    out = []
    for l, r in enumerate(R):
        if r[0] != 'comp': continue
        e = r[3]; offs = []
        def walk(x, W):
            if x[0] == 'bin' and x[1] == ('addi',) and x[2] == W:
                walk(x[3], W); walk(x[4], W)
            elif x[0] == 'bin' and x[1] == ('shli',) and x[2] == W and x[4][0] == 'lit':
                offs.append(x[4][1])
            else:
                offs.append(0)
        if not (e[0] == 'bin' and e[1] == ('addi',)): continue
        W = e[2]; walk(e, W)
        rd = Q.readers(R, r[2])
        if len(rd) != 1 or R[rd[0]][0] != 'fork': continue
        wins = set()
        for z in R[rd[0]][2]:
            for ls in Q.readers(R, z):
                s = R[ls][3]
                if (s[0] == 'un' and s[1] == ('trunci',) and s[3][0] == 'bin' and s[3][1] == ('shrui',)
                        and s[3][2] == W and s[3][3] == ('var', 0) and s[3][4][0] == 'lit'):
                    wins.add((s[3][4][1], s[2], vname_of(names[R[ls][2]]) if R[ls][2] < len(names) else '?'))
        if len(wins) >= 2: out.append((W, sorted(offs), wins))
    return out

def check(mlir, bdc, env):
    e = dict(os.environ); e.update(env)
    with tempfile.TemporaryDirectory() as td:
        vf = os.path.join(td, 'k.v')
        p = subprocess.run([sys.executable, os.path.join(bdc, 'emit.py'), mlir, '--no-top', '-o', vf], env=e,
                           capture_output=True, text=True)
        if p.returncode != 0 or not os.path.exists(vf): return 'emit failed'
        v = open(vf).read()
        if CTL == 'swap':   # negative control: the first multi-result cell's first two slices exchange their windows
            m = re.search(r"assign z_data = \{([^}]*,[^}]*)\};", v)
            inst = re.search(r"module bdc_fused_(\w+)", v[:m.start()][::-1][::-1].split('module bdc_fused_')[-1].join(['module bdc_fused_', ''])) if m else None
            sl = re.findall(r"(\w+)_zdata\[(\d+):(\d+)\]", v)
            if sl:
                i0 = sl[0][0]; same = [x for x in sl if x[0] == i0][:2]
                a, b = f"{i0}_zdata[{same[0][1]}:{same[0][2]}]", f"{i0}_zdata[{same[1][1]}:{same[1][2]}]"
                v = v.replace(a, '@@A@@').replace(b, a).replace('@@A@@', b)
        F.PP.BDCDIR = bdc
        try:
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                R = F.imp(mlir, os.path.join(td, 'm.lean'), 'M', env)[0]
            t = open(os.path.join(td, 'm.lean')).read()
            names = eval(re.search(r'def chanNames : List String := (\[.*?\])\n', t).group(1))
        except Exception:
            return 'import failed'
    cells, slices = verilog_cells(v)
    if not cells: return 'no multi-result cell'
    bad = []
    vs = []
    for inst, (W, lay) in cells.items():
        if lay[-1][0] + lay[-1][1] != W: bad.append(f'{inst}: parts do not tile z_data ({lay}, W {W})')
        got = {(lo, w) for lo, w, _ in slices.get(inst, set())}
        if got != set(lay): bad.append(f'{inst}: slices {sorted(got)} != parts {lay}')
        vs.append((W, sorted(lo for lo, _ in lay), set(slices.get(inst, set()))))
    ms = model_cells(R, names)
    key = lambda c: (c[0], tuple(c[1]), tuple(sorted(c[2])))
    if sorted(map(key, vs)) != sorted(map(key, ms)):
        bad.append(f'model {sorted(map(key, ms))} != verilog {sorted(map(key, vs))}')
    return ('MISMATCH: ' + '; '.join(bad)) if bad else f'OK ({len(cells)} cell(s))'

CTL = None

def main():
    global CTL
    if '--ctl' in sys.argv:
        i = sys.argv.index('--ctl'); CTL = sys.argv[i + 1]; del sys.argv[i:i + 2]
    if len(sys.argv) < 3: print(__doc__); return 1
    fx, bdc = sys.argv[1], os.path.abspath(sys.argv[2])
    env = F.parse_env(sys.argv[3]) if len(sys.argv) > 3 else {'BDC_AUTO': '1'}
    rc = 0
    for k in sorted(os.listdir(fx)):
        m = os.path.join(fx, k, 'comp', 'handshake_transformed.mlir')
        if not os.path.exists(m): continue
        r = check(m, bdc, env)
        if r.startswith('MISMATCH'): rc = 2
        print(f'{k:28s} {r}')
    return rc

if __name__ == '__main__':
    sys.exit(main())
