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
  3. Checks: the Verilog's parts (nested concatenations, replications and sized literals flattened) are plain wires,
     none packed twice, and tile z_data exactly; its slices are exactly those windows; the model has the same number of
     packed cells, the same W, the same offsets, and the same (window, result, member) triples -- each result (bdc's
     SSA name) reads the same window in the model as in the Verilog, and the wire packed there is w_n<member> for the
     region member the model's part computes (importer side record, FA_MR_LOG). Model cells with no parsed Verilog
     cell, or a Verilog cell that cannot be laid out, is a MISMATCH (audit T171).
Prints one line per kernel: OK (cells checked) / MISMATCH (what) / no multi-result cell / import or emit failed.
Exit 2 on any MISMATCH, else 3 if some kernel was not checked (emit / import / check failed), else 0.
K=V,... REPLACES the default env (BDC_AUTO=1): pass BDC_AUTO=1 with any extra knob you want on the automatic flow. Controls: BDC_RING_FUSE_NEGCTL=1 env; --ctl swap.
NOT covered: that each part's Verilog expression computes the model's expression (the general trust in bdc's region
Verilog, compute.py / emit.py, the same as for every fused cell); anything below the netlist.
"""
import io, contextlib, os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fuse_check as F   # noqa: E402

def split_top(s):
    """Top-level comma-separated items of a Verilog expression list (braces / parens balanced)."""
    out, d, cur = [], 0, ''
    for ch in s:
        if ch in '{(': d += 1
        elif ch in '})': d -= 1
        if ch == ',' and d == 0: out.append(cur.strip()); cur = ''
        else: cur += ch
    if cur.strip(): out.append(cur.strip())
    return out

def concat_body(s, i):
    """s[i] == '{': the text between it and its matching '}', and the index after."""
    d = 0
    for j in range(i, len(s)):
        if s[j] == '{': d += 1
        elif s[j] == '}':
            d -= 1
            if d == 0: return s[i + 1:j], j + 1
    raise ValueError('unbalanced braces')

def atoms(x, body):
    """Flatten one Verilog concatenation operand to [(name or None, width or None)], high to low.
    name is a plain wire identifier; None for a literal / replication / any other expression."""
    x = x.strip()
    if x.startswith('{'):
        inner, k = concat_body(x, 0)
        if x[k:].strip(): return [(None, None)]
        m = re.match(r"\s*(\d+)\s*\{", inner)
        if m:   # replication {N{...}}
            sub, k2 = concat_body(inner, m.end() - 1)
            if inner[k2:].strip(): return [(None, None)]
            ws = [w for item in split_top(sub) for _, w in atoms(item, body)]
            return [(None, None if None in ws else int(m.group(1)) * sum(ws))]
        return [a for item in split_top(inner) for a in atoms(item, body)]
    m = re.fullmatch(r"(\d+)'[bBhHdDoO][0-9a-fA-FxXzZ_]+", x)
    if m: return [(None, int(m.group(1)))]
    if re.fullmatch(r"[A-Za-z_]\w*", x):
        d = re.search(r"\bwire\s+(?:\[(\d+):0\]\s*)?" + re.escape(x) + r"\b", body)
        return [(x, (int(d.group(1)) + 1 if d.group(1) else 1) if d else None)]
    return [(None, None)]

def verilog_cells(v):
    """{inst: (W, [(lo, w, part) low to high])} from the fused modules whose z_data is a concatenation
    (part = the plain wire's name, or None for a literal / replication / other expression);
    {inst: {(lo, w, consumer)}} slices from the top; [inst] cells whose z_data could not be laid out."""
    cells, bad = {}, []
    for m in re.finditer(r"module bdc_fused_(\w+) .*?endmodule", v, re.S):
        inst, body = m.group(1), m.group(0)
        a = re.search(r"assign z_data = \{", body)
        if not a: continue
        try:
            inner, k = concat_body(body, a.end() - 1)
            parts = [at for item in split_top(inner) for at in atoms(item, body)]
        except ValueError:
            bad.append(inst); continue
        if len(parts) < 2: continue
        zw = re.search(r"output wire \[(\d+):0\]\s*z_data", body)
        W = int(zw.group(1)) + 1 if zw else None
        if W is None or any(w is None for _, w in parts): bad.append(inst); continue
        lo, lay = 0, []
        for nm, w in reversed(parts):   # low to high
            lay.append((lo, w, nm)); lo += w
        cells[inst] = (W, lay)
    slices = {}
    for inst in cells:
        for m in re.finditer(re.escape(inst) + r"_zdata\[(\d+):(\d+)\]", v):
            hi, lo = int(m.group(1)), int(m.group(2))
            line = v[v.rfind('\n', 0, m.start()) + 1:v.find('\n', m.end())]
            nm = re.search(r"\.req_in\((\w+)_freq\)", line) or re.search(r"assign (\w+?)(?:_u)?_data = ", line)   # bdc: odata = <vname>[_u]_data (_u: linked)
            slices.setdefault(inst, set()).add((lo, hi - lo + 1, nm.group(1) if nm else '?'))
    return cells, slices, bad

def vname_of(ssa):
    return 'n' + ssa.replace('#', '__')

def model_cells(R, names, log):
    """[(W, offsets, slice windows (lo, w, consumer, part))] for every packed comp of the imported rules; part is
    w_n<member> (bdc's wire name for the region member that computes it), from the importer's side record."""
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
        mi = re.fullmatch(r'__mr_(\d+)', names[r[2]]) if r[2] < len(names) else None
        part = {lo: f'w_n{m}' for lo, w, v, m in log.get(int(mi.group(1)), [])} if mi else {}
        wins = set()
        for z in R[rd[0]][2]:
            for ls in Q.readers(R, z):
                if R[ls][0] != 'comp': continue   # a fork / steer / sink reading a result is not a slice (audit T171 update)
                s = R[ls][3]
                if (isinstance(s, tuple) and s[0] == 'un' and s[1] == ('trunci',) and s[3][0] == 'bin' and s[3][1] == ('shrui',)
                        and s[3][2] == W and s[3][3] == ('var', 0) and s[3][4][0] == 'lit'):
                    lo = s[3][4][1]
                    wins.add((lo, s[2], vname_of(names[R[ls][2]]) if R[ls][2] < len(names) else '?', part.get(lo, '?')))
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
            rec = eval(line); log[rec[0]] = rec[1]
    cells, slices, unparsed = verilog_cells(v)
    ms = model_cells(R, names, log)
    if not cells and not ms and not unparsed: return 'no multi-result cell'
    bad = [f'{inst}: z_data not laid out (unknown part width)' for inst in unparsed]
    vs = []
    for inst, (W, lay) in cells.items():
        if lay[-1][0] + lay[-1][1] != W: bad.append(f'{inst}: parts do not tile z_data ({lay}, W {W})')
        nms = [nm for _, _, nm in lay]
        if None in nms: bad.append(f'{inst}: a part is not a wire (literal / replication / expression): {lay}')
        if len(set(nms)) != len(nms): bad.append(f'{inst}: a wire packed twice: {lay}')
        got = {(lo, w) for lo, w, _ in slices.get(inst, set())}
        if got != {(lo, w) for lo, w, _ in lay}: bad.append(f'{inst}: slices {sorted(got)} != parts {lay}')
        pn = {(lo, w): nm for lo, w, nm in lay}
        vs.append((W, sorted(lo for lo, _, _ in lay),
                   {(lo, w, c, pn.get((lo, w)) or '?') for lo, w, c in slices.get(inst, set())}))
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
        try:
            r = check(m, bdc, env)
        except Exception as ex:   # fail closed with a verdict, never a traceback (audit T171 update)
            r = f'check failed ({type(ex).__name__}: {ex})'
        if r.startswith('MISMATCH'): rc = 2
        elif r.endswith('failed') and rc == 0: rc = 3   # not checked
        print(f'{k:28s} {r}')
    return rc

if __name__ == '__main__':
    sys.exit(main())
