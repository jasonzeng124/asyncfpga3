#!/usr/bin/env python3
"""Netlist-side INIT extraction with yosys, compared to the regex RTL parse
(extract_inits.parse_rtl) and to the Lean constants.

Run: python3 -I yosys_inits.py [--yosys PATH] [--rtl DIR] [--work DIR]

For each (top, params, defines) below yosys elaborates the RTL against the
Xilinx cell library as blackboxes (no optimisation, no techmap), writes JSON,
and every LUT1..LUT6/LUT6_2 cell is listed with its INIT and the net on each
pin.  Checked per cell:
  * INIT is one of the values the regex parse found for that module/instance;
  * constant pins equal; non-constant pins have the same base net name;
  * every feedback (pin net == own output net in the RTL text) is a real
    feedback in the netlist (same bit), and no extra feedback appears.
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import extract_inits as X  # noqa: E402  (our own script, same directory)

TOPS = [
    ('bd_c2', {}, []), ('bd_c2_set', {}, []), ('bd_c2n', {}, []), ('bd_c2n_set', {}, []),
    ('bd_c3', {}, []), ('bd_c4', {}, []), ('bd_c2_norst', {}, []), ('bd_c3_norst', {}, []),
    ('bd_ctree', {'N': 9}, []),
    ('bd_arbcell', {}, []), ('bd_arbiter', {}, []),
    ('bd_latch', {'W': 3}, []), ('bd_latch_rst', {'W': 2, 'RESET_VALUE': 2}, []),
    ('bd_delay', {'N': 3}, []), ('bd_delay', {'N': 3, 'FASTFALL': 1}, []),
    ('bd_delay', {'N': 3, 'FASTRISE': 1}, []), ('bd_delay_gated', {'N': 3}, []),
    ('bd_datamux', {'W': 3}, []),
    ('bd_link_dctl', {'BROAD': 1, 'LDN': 0}, []), ('bd_link_dctl', {'BROAD': 0, 'LDN': 2}, []),
    ('bd_link', {'W': 3, 'DELAY': 2, 'DACK': 2}, []),
    ('bd_link', {'W': 3, 'DELAY': 2, 'DACK': 2}, ['BD_LINK_DC']),
    ('bd_steer', {}, []), ('bd_bd2dr', {}, []), ('bd_dr2bd', {'HOLD': 1}, []), ('bd_dr2bd', {'HOLD': 0}, []),
    ('bd_mux', {'W': 3}, []), ('bd_merge', {'W': 3}, []),
    ('bd_mlink_ctl', {'NOPEN': 1}, []), ('bd_mlink_ctl', {'NOPEN': 3}, []), ('bd_flink_ctl', {}, []),
    ('bd_src', {}, []), ('bd_mem', {}, []),
]


def run_yosys(yosys, rtl_dir, top, params, defines, out):
    share = os.path.join(os.path.dirname(os.path.dirname(yosys)), 'share', 'yosys', 'xilinx', 'cells_sim.v')
    files = ' '.join(os.path.join(rtl_dir, f) for f in sorted(os.listdir(rtl_dir)) if f.endswith('.v'))
    defs = ' '.join('-D' + d for d in defines)
    chp = ' '.join('-chparam %s %d' % (k, v) for k, v in params.items())
    script = ('read_verilog -lib %s; read_verilog %s %s; hierarchy -top %s %s -purge_lib; proc; write_json %s'
              % (share, defs, files, top, chp, out))
    r = subprocess.run([yosys, '-q', '-p', script], capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(r.stderr[-2000:])
    return json.load(open(out))


def base_mod(name):
    m = re.match(r'\$paramod\$[0-9a-f]+\\(\w+)', name) or re.match(r'\$paramod\\(\w+)', name)
    return m.group(1) if m else name.lstrip('\\')


def bitname(mod):
    names = {}
    for n, v in mod['netnames'].items():
        if n.startswith('$'):
            continue
        for k, b in enumerate(v['bits']):
            if isinstance(b, int):
                nm = n if len(v['bits']) == 1 else '%s[%d]' % (n, k + v.get('offset', 0))
                if b not in names or len(nm) < len(names[b]):
                    names[b] = nm
    return names


def strip_idx(n):
    return re.sub(r'\[.*?\]', '', n).split('.')[-1] if isinstance(n, str) else n


def allnames(mod):
    names = {}
    for n, v in mod['netnames'].items():
        for k, b in enumerate(v['bits']):
            if isinstance(b, int):
                names.setdefault(b, set()).add(strip_idx(n))
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--yosys', default=os.path.expanduser('~/audit-tc/openxc7/bin/yosys'))
    ap.add_argument('--rtl', default='/home/user/wt-research/cells/rtl')
    ap.add_argument('--work', default='/tmp/yosys_inits_work')
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    rtl = X.parse_rtl(a.rtl)
    by = {}
    for i in rtl:
        by.setdefault((i['module'], i['name']), []).append(i)
    seen_rtl = set()
    nbad = ncell = 0
    for top, params, defines in TOPS:
        tag = top + ''.join('_%s%d' % kv for kv in params.items()) + ''.join('_' + d for d in defines)
        d = run_yosys(a.yosys, a.rtl, top, params, defines, os.path.join(a.work, tag + '.json'))
        print('== %s' % tag)
        for mname, mod in sorted(d['modules'].items()):
            bm = base_mod(mname)
            names = bitname(mod)
            aliases = allnames(mod)
            for cname, c in sorted(mod['cells'].items()):
                if not re.fullmatch(r'LUT[1-6](_2)?', c['type']):
                    continue
                ncell += 1
                init = int(c['parameters']['INIT'], 2)
                inst = cname.split('.')[-1]
                pins = []
                for k in range(6):
                    bits = c['connections'].get('I%d' % k)
                    if bits is None:
                        continue
                    b = bits[0]
                    pins.append(int(b) if isinstance(b, str) else names.get(b, '?%d' % b))
                pinset = [aliases.get(c['connections']['I%d' % k][0], set()) if not isinstance(p, int) else None
                          for k, p in enumerate(pins)]
                outs = {o: names.get(c['connections'][o][0], '?') for o in ('O', 'O5', 'O6')
                        if o in c['connections']}
                obits = {c['connections'][o][0] for o in ('O', 'O5', 'O6') if o in c['connections']}
                fb_net = [k for k in range(len(pins)) if c['connections']['I%d' % k][0] in obits]
                cands = [r for r in by.get((bm, inst), []) if r['prim'] == c['type']]
                verdict, why = 'NO RTL MATCH', ''
                for r in cands:
                    if init not in r['inits']:
                        why = 'INIT %X not in RTL %s' % (init, r['inits']); continue
                    probs = []
                    for k, (yp, rp) in enumerate(zip(pins, r['ins'])):
                        if isinstance(rp, int) or isinstance(yp, int):
                            if yp != rp and not (rp == 'gate' and yp in (0,)) and not (rp == 's' and yp == 1):
                                probs.append('I%d %r vs %r' % (k, yp, rp))
                        elif strip_idx(rp) not in pinset[k] and not (
                                rp in ('gate', 's') or (bm == 'bd_delay' and yp == 'a' and rp == 's[i]')
                                or (bm == 'bd_delay_gated' and yp == 'a' and rp == 's[i]')):
                            probs.append('I%d %r vs %r' % (k, yp, rp))
                    rfb = [k for k, p in enumerate(r['ins']) if p in r['out'].values()]
                    if rfb != fb_net:
                        probs.append('feedback pins netlist %s vs RTL %s' % (fb_net, rfb))
                    if not probs:
                        verdict, why = 'MATCH', ''
                        seen_rtl.add((r['file'], r['line']))
                        break
                    why = '; '.join(probs)
                if verdict != 'MATCH':
                    nbad += 1
                print('  %-12s %-16s %-6s INIT=%016X pins=%s out=%s fb=%s : %s %s' % (
                    bm, cname, c['type'], init, pins, outs, fb_net, verdict, why))
    missing = [i for i in rtl if (i['file'], i['line']) not in seen_rtl]
    print('\n== regex-parsed RTL LUT instances not reproduced by any netlist cell: %d' % len(missing))
    for i in missing:
        print('  %s:%s %s.%s' % (i['file'], i['line'], i['module'], i['name']))
    print('\n== netlist LUT cells: %d, not matching regex parse: %d' % (ncell, nbad))


if __name__ == '__main__':
    main()
