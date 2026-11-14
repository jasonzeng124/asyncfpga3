#!/usr/bin/env python3
"""T93 (audit, own code): sites.py generalised to any bdc kernel.  Nothing in the engine names a kernel channel.

sites.py (unchanged, still the reference for designs A/B) took its sites from research's text output and had three
xorshift-specific pieces: the steer-gate regex (ucond_br\\d+), the request-join regex (.ujoin. / _j. / .uj0/.uj1) and the
loop-counter restriction (uaddi0 + the n7/n29/n30 nets).  Here:

  * the kernel Verilog is parsed hierarchically (parse_kernel): every module defined in the file is expanded from the top
    module, which gives the instance path of every bd_steer, bd_mux, bd_join, bd_link, bd_pipe (and its stages,
    `<pipe>.many.stage[i].u` / `<pipe>.one.u`, from bd_pipe.v), bd_delay_gated, bd_arbiter and every fused op
    (a kernel module holding one bd_join and one bd_delay_gated);
  * sites    = every bd_steer (gates u$LUT6/u$LUT5, its fractured halves) and every bd_mux (gates uj0/uj1, bd_mux.v);
    req/s nets read from the instance ports, pins found by logical net name (nets.map, assign aliases resolved);
  * request-rendezvous C-elements = state LUTs under a bd_join instance path or a bd_mux's uj0/uj1;
  * steer gates (never on a select walk) = the u$LUT6/u$LUT5 of every bd_steer;
  * links = every state LUT under `<link>.lat.` whose `<link>` is a bd_link or a pipe stage from the RTL (checked: no
    latch LUT left over);
  * the counter restriction is per-design configuration (`counter`), absent for collatz; a separate informational
    `vr` (vector range) restriction drops CARRY4 slices of named adders above the bit range the gate vectors reach.

Launch discovery, the graph walks and the three margins (own / OR-join / plain) are sites.py's, unchanged.

    python3 sites_gen.py collatz        # -> sites_collatz_item22.txt / .json (3 corners, plant test)
    python3 sites_gen.py xorshift       # A/B with research's site list -> sites_results_regen.txt, compared with
                                        #   sites_results.txt / sites_results.json; plus RTL-derived inventory checks
Reads only the generated work dirs.  Never runs vvp, the project's tools or git.  Writes only in this directory.
"""
import sys, os, re, json, collections, argparse, shutil, math
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
from sta_lib import Netlist, read_names_map, read_nets_map, lut_eval

P = 'bridge_i.udut.'
GUARD_LO, GUARD_HI = 0.772, 1.155        # research's guardband (xorshift reproduction only)

DESIGNS = {
    'A': dict(item=18, rj='/root/t65/l5_1/xorshift_bench_gen_routed.json', rtl='/root/t65/l5_1/xorshift_kernel_bench.v',
              research=os.path.join(H, 'research_skew_l5_1.txt'),
              work={'worst': '/root/t65/work_l5_1_long2_worst', 'fastmin': '/root/t65/work_l5_1_long_fastmin'},
              corners=('worst', 'fastmin'),
              counter=dict(adder='uaddi0.', bits=(11, 12),
                           net_re=r'\.(n7|n7_u|n6|n6_u|n_trueResult_6|n_trueResult_6_u|n29|n30__0|n30__1|n30__1_u)_data\[(\d+)\]$')),
    'B': dict(item=17, rj='/root/t65/l3_1/xorshift_bench_gen_routed.json', rtl='/root/t65/l3_1/xorshift_kernel_bench.v',
              research=os.path.join(H, 'research_skew_l3_1.txt'),
              work={'worst': '/root/t65/work_l3_1_long2_worst', 'fastmin': '/root/t65/work_l3_1_long_fastmin'},
              corners=('worst', 'fastmin'),
              counter=dict(adder='uaddi0.', bits=(11, 12),
                           net_re=r'\.(n7|n7_u|n6|n6_u|n_trueResult_6|n_trueResult_6_u|n29|n30__0|n30__1|n30__1_u)_data\[(\d+)\]$')),
    'C': dict(item=22, rj='/root/t65/colsz2_26/collatz_bench_gen_routed.json', rtl='/root/t65/colsz2_26/collatz_kernel_bench.v',
              research=None,
              work={'worst': '/root/t65/work_colsz2_26_mon_worst', 'FAST_MIN': '/root/t65/work_colsz2_26_mon_fastmin',
                    'SLOW_MAX': '/root/t65/work_colsz2_26_mon_slowmax'},
              corners=('worst', 'FAST_MIN', 'SLOW_MAX'),
              counter=None,
              # informational only: the 13 gate vectors keep n < 2^20 (max 975400, from 6171), so 3n+1 < 2^22 in uaddi0;
              # the step count stays < 2^9 (max 261) in uaddi1.  Slice-granular: slices >= ceil(bits/4) dropped.
              vrange={'uaddi0': 22, 'uaddi1': 9}),
}


# --------------------------------------------------------------------------------------------------- kernel RTL --
INST_RE = re.compile(r'^\s*(?:\(\*[^*]*\*\)\s*)?([A-Za-z_]\w*)\s*(#\s*\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))?\s+'
                     r'([A-Za-z_][\w$]*)\s*\(', re.M)
KEYWORDS = {'module', 'input', 'output', 'inout', 'wire', 'reg', 'assign', 'always', 'if', 'else', 'begin', 'end',
            'generate', 'endgenerate', 'for', 'genvar', 'localparam', 'parameter', 'function', 'case'}


def _ports(body):
    return dict(re.findall(r'\.(\w+)\s*\(\s*([^()]*?(?:\([^()]*\))?[^()]*?)\s*\)', body))


def parse_kernel(path):
    """Hierarchical inventory of a bdc kernel file.  Paths are relative to the top module (= P in the netlist)."""
    txt = open(path).read()
    txt_nc = re.sub(r'//[^\n]*', '', txt)
    mods = {}
    for m in re.finditer(r'\bmodule\s+(\w+)\s*(#\s*\((.*?)\))?\s*\((.*?)\);(.*?)\bendmodule', txt_nc, re.S):
        defaults = dict(re.findall(r'parameter\s+(?:integer\s+)?(\w+)\s*=\s*([^,)\s]+)', m[3] or ''))
        mods[m[1]] = dict(params=defaults, body=m[5])
    def insts(body):
        out = []
        for m in INST_RE.finditer(body):
            typ, par, name = m[1], m[2] or '', m[3]
            if typ in KEYWORDS: continue
            # port list: from the '(' after the name to the matching ');'
            i = m.end(); depth = 1; j = i
            while depth and j < len(body):
                depth += {'(': 1, ')': -1}.get(body[j], 0); j += 1
            out.append(dict(type=typ, name=name, params=dict(re.findall(r'\.(\w+)\s*\(\s*([^()]*?)\s*\)', par)),
                            ports=_ports(body[i:j - 1])))
        return out
    instantiated = {i['type'] for mm in mods.values() for i in insts(mm['body'])}
    tops = [n for n in mods if n not in instantiated]
    assert len(tops) == 1, f'top module ambiguous: {tops}'
    top = tops[0]
    K = dict(top=top, steers={}, muxes={}, joins=[], links=[], pipes={}, dgated=[], arbiters=[], fused={}, merges=[],
             forks=[], instances=[])
    def walk(mod, prefix, depth=0):
        for it in insts(mods[mod]['body']):
            path = prefix + it['name']
            K['instances'].append((path, it['type']))
            t = it['type']
            if t == 'bd_steer':
                K['steers'][path] = dict(req_net=it['ports']['req'], s_net=it['ports']['s'], ports=it['ports'])
            elif t == 'bd_mux':
                K['muxes'][path] = dict(req_net=it['ports']['ctl_req'], s_net=it['ports']['s'], ports=it['ports'])
            elif t == 'bd_join': K['joins'].append(path)
            elif t == 'bd_link': K['links'].append(path)
            elif t == 'bd_pipe':
                n = int(re.sub(r"\D", '', it['params'].get('N', '2')) or 2)
                st = [f'{path}.one.u'] if n == 1 else [f'{path}.many.stage[{i}].u' for i in range(n)]
                K['pipes'][path] = st; K['links'] += st
            elif t == 'bd_delay_gated': K['dgated'].append(path)
            elif t == 'bd_arbiter': K['arbiters'].append(path)
            elif t == 'bd_fork': K['forks'].append(path)
            if t in mods:
                body = mods[t]['body']
                if re.search(r'\bbd_join\b', body) and re.search(r'\bbd_delay_gated\b', body):
                    K['fused'][path] = dict(module=t, delay_param=it['params'].get('DELAY', mods[t]['params'].get('DELAY')))
                if re.search(r'\bbd_arbiter\b', body): K['merges'].append(path)
                walk(t, path + '.', depth + 1)
    walk(top, '')
    # assign aliases (plain wire = wire), for matching a channel's data net to the single name nextpnr kept
    parent = {}
    def find(x):
        while parent.get(x, x) != x: x = parent[x]
        return x
    for a_, b_ in re.findall(r'assign\s+(\w+)\s*=\s*(\w+)\s*;', mods[top]['body']):
        parent[find(a_)] = find(b_)
    K['alias'] = find
    # request-rendezvous C-element path prefixes: bd_join instances anywhere, bd_mux joins (bd_mux.v: uj0/uj1)
    K['join_prefixes'] = [j + '.' for j in K['joins']]
    K['join_exact'] = [m + '.uj0' for m in K['muxes']] + [m + '.uj1' for m in K['muxes']]
    return K


def rtl_sites(K):
    """site -> dict(kind, req_net, s_net, gates) from the kernel inventory (sites.py's parse_rtl, generalised)."""
    out = {}
    for s, d in K['steers'].items():
        out[s] = dict(kind='bd_steer', req_net=d['req_net'], s_net=d['s_net'], gates=[s + '.u$LUT6', s + '.u$LUT5'])
    for s, d in K['muxes'].items():
        out[s] = dict(kind='bd_mux', req_net=d['req_net'], s_net=d['s_net'], gates=[s + '.uj0', s + '.uj1'])
    return out


def parse_research(path):
    out, cur = [], None
    for line in open(path):
        m = re.match(r'\s+(VIOLATED|ok)\s+(bd_steer|bd_mux)\s+(\S+)', line)
        if m:
            cur = dict(status=m[1], kind=m[2], site=m[3][len(P):]); out.append(cur); continue
        if cur is None: continue
        m = re.match(r'\s+launch\s+(\S+)/\w+', line)
        if m: cur['launch'] = m[1][len(P):].removesuffix('.ctl.u.u'); continue
        m = re.match(r'\s+req\s+(\S+)/(A\d)', line)
        if m: cur['gate'] = m[1][len(P):]; cur['req_pin'] = m[2]; continue
        m = re.match(r'\s+sel\s+(\S+)/(A\d)', line)
        if m: cur['sel_gate'] = m[1][len(P):]; cur['sel_pin'] = m[2]; continue
        m = re.match(r'\s+earliest\s+(-?\d+) ps, (\d+)', line)
        if m: cur['earliest'] = int(m[1]); cur['req_cross'] = int(m[2]); continue
        m = re.match(r'\s+latest\s+(-?\d+) ps, (\d+)', line)
        if m: cur['latest'] = int(m[1]); cur['sel_cross'] = int(m[2]); continue
        m = re.match(r'\s+margin\s+([+-]?\d+) ps raw, ([+-]?\d+) ps guarded', line)
        if m: cur['raw'] = int(m[1]); cur['guarded'] = int(m[2]); cur = None
    seen, res = set(), []
    for r in out:
        k = (r['site'], r['gate'])
        if k in seen: continue
        seen.add(k); res.append(r)
    return res


def sval(s_net):
    """'n31__2_data[0]' -> 'n31__2_data' (the select is bit 0 of a 1-bit channel)."""
    return re.sub(r'\[0\]$', '', s_net)


# ----------------------------------------------------------------------------------------------------- engine --
class Engine:
    def __init__(self, work, rj, K, counter=None, netlist=None):
        self.nl = nl = Netlist(netlist or (work + '/netlist_baked.v'))
        self.K = K
        self.counter = counter
        self.counter_re = re.compile(counter['net_re']) if counter else None
        self.site_of_c, c_of_site = read_names_map(work + '/names.map')
        _, self.name_of_wire = read_nets_map(work + '/nets.map')
        m = list(json.load(open(rj))['modules'].values())[0]
        self.lname, self.cof, self.outbits = {}, {}, {}
        bitnames = collections.defaultdict(set)
        for n, v in m['netnames'].items():
            for b in v['bits']: bitnames[b].add(n)
        for cn, c in m['cells'].items():
            bel = c['attributes'].get('NEXTPNR_BEL')
            if bel in c_of_site:
                self.lname[c_of_site[bel]] = cn; self.cof[cn] = c_of_site[bel]
                outs = [b for p_, bb in c['connections'].items() if c.get('port_directions', {}).get(p_) == 'output'
                        for b in bb if isinstance(b, int)]
                self.outbits[c_of_site[bel]] = sorted(n for b in outs for n in bitnames[b])
        del m, bitnames
        self.state_cells = set(nl.state_nets.values())
        # links from the RTL: bd_link instances and bd_pipe stages.  A state LUT under '<link>.lat.' is that link's latch.
        links = set(K['links'])
        self.latch_link, self.unknown_latch = {}, []
        for c in self.state_cells:
            ln = self.L(c)
            if ln.startswith(P) and '.lat.' in ln:
                lk = ln[len(P):].split('.lat.')[0]
                if lk in links: self.latch_link[c] = lk
                else: self.unknown_latch.append(ln)
        jp = tuple(P + j for j in K['join_prefixes']); je = {P + j for j in K['join_exact']}
        self.join_cells = {c for c in self.state_cells if self.L(c).startswith(jp) or self.L(c) in je}
        self.en_pin, self.en_only = {}, set()
        for c, link in self.latch_link.items():
            cn = self.ctl_cell(link)
            if cn is None: continue
            cnet = self.out_net(cn); cc = nl.cells[c]
            ks = [k for k in cc['support'] if k not in cc['fb'] and self.src_of(cc['pins'][f'A{k}']) == cnet]
            if len(ks) == 1: self.en_pin[c] = ks[0]
        sg = {P + s + h for s in K['steers'] for h in ('.u$LUT6', '.u$LUT5')}
        self.steer_gates = {c for c in nl.cells if self.L(c) in sg}
        self.pos_pins = {}
        for c in self.state_cells:
            cc = nl.cells[c]; init = cc['params']['INIT']; out = cc['out']
            sup = [k for k in sorted(cc['support']) if k not in cc['fb']]
            pos = set()
            for k in sup:
                others = [j for j in sup if j != k]
                for a_ in range(1 << len(others)):
                    pins = {j: (a_ >> i) & 1 for i, j in enumerate(others)}
                    pins.update(cc['const'])
                    for f in cc['fb']: pins[f] = 0
                    pins[k] = 0; v0 = lut_eval(init, out, pins)
                    pins[k] = 1; v1 = lut_eval(init, out, pins)
                    if v0 == 0 and v1 == 1: pos.add(k); break
            self.pos_pins[c] = pos
        # CARRY4 chains per owning instance (first path component), ordered by CIN <- CO3 chaining
        self.c4_index = {}
        c4 = [c for c, cc in nl.cells.items() if cc['type'] == 'CARRY4' and self.L(c).startswith(P)]
        by_co3 = {nl.cells[c]['pins'].get('CO3'): c for c in c4}
        for c in c4:
            k, x = 0, c
            while True:
                cin = nl.cells[x]['pins'].get('CIN')
                prev = by_co3.get(self.src_of(cin)) if cin else None
                if prev is None or prev == x: break
                k += 1; x = prev
            self.c4_index[c] = k

    def L(self, c): return self.lname.get(c, '?' + self.site_of_c.get(c, c))
    def src_of(self, net):
        icn = self.nl.ic_by_out.get(net)
        return self.nl.ic[icn][0] if icn else net
    def lognet(self, net): return self.name_of_wire.get(self.src_of(net), '?')
    def ctl_cell(self, link): return self.cof.get(P + link + '.ctl.u.u')
    def link_latches(self, link): return {c for c, l in self.latch_link.items() if l == link}
    def out_net(self, c): return self.nl.cells[c]['pins'][self.nl.cells[c]['out']]

    def gate_pins(self, gate, req_net, s_net, alias=lambda x: x):
        c = self.cof.get(P + gate)
        if c is None: return None
        cc = self.nl.cells[c]
        rp = sp = None
        for k in sorted(cc['support']):
            if k in cc['fb']: continue
            net = cc['pins'][f'A{k}']; ln = self.lognet(net)
            if not ln.startswith(P): continue
            ln = alias(re.sub(r'\[0\]$', '', ln[len(P):]))
            if ln == alias(req_net): rp = (f'A{k}', net)
            elif ln == alias(sval(s_net)): sp = (f'A{k}', net)
        return c, rp, sp

    def arcs_ok(self, e, allowed, excluded):
        src, dst, d, kind, cell, pin = e
        if cell in excluded: return False
        if kind == 'lut':
            if int(pin[1:]) in self.nl.cells[cell]['fb']: return False
            if cell in self.state_cells:
                if cell not in allowed: return False
                if cell in self.en_only and int(pin[1:]) != self.en_pin.get(cell): return False
                if int(pin[1:]) not in self.pos_pins[cell]: return False
        return True

    def cone(self, start, end, allowed, excluded=frozenset()):
        nl = self.nl
        fw, stk = set(), [start]
        while stk:
            n = stk.pop()
            if n in fw: continue
            fw.add(n)
            for e in nl.fan[n]:
                if self.arcs_ok(e, allowed, excluded): stk.append(e[1])
        bw, stk = set(), [end]
        while stk:
            n = stk.pop()
            if n in bw or n not in fw: continue
            bw.add(n)
            for e in nl.fin[n]:
                if self.arcs_ok(e, allowed, excluded): stk.append(e[0])
        return bw

    def topo(self, cn, allowed, excluded):
        indeg = {n: 0 for n in cn}
        edges = collections.defaultdict(list)
        for n in cn:
            for e in self.nl.fan[n]:
                if e[1] in cn and self.arcs_ok(e, allowed, excluded):
                    edges[n].append(e); indeg[e[1]] += 1
        q = [n for n in cn if indeg[n] == 0]; order = []
        while q:
            n = q.pop(); order.append(n)
            for e in edges[n]:
                indeg[e[1]] -= 1
                if indeg[e[1]] == 0: q.append(e[1])
        if len(order) != len(cn):
            left = set(cn) - set(order)
            cells = sorted({self.L(e[4])[len(P):] for n in left for e in self.nl.fin[n]
                            if e[0] in left and e[3] == 'lut' and e[4] in self.state_cells})
            raise RuntimeError(f'cycle in cone: {len(left)} nets not ordered; state cells on it: {cells[:12]}')
        return order, edges

    def longest(self, start, end, allowed, excluded=frozenset()):
        cn = self.cone(start, end, allowed, excluded)
        if end not in cn: return None, [], cn
        order, edges = self.topo(cn, allowed, excluded)
        arr = {start: 0}; pred = {}
        for n in order:
            if n not in arr: continue
            for e in edges[n]:
                t = arr[n] + e[2]
                if t > arr.get(e[1], -1): arr[e[1]] = t; pred[e[1]] = e
        path, n = [], end
        while n in pred: path.append(pred[n]); n = pred[n][0]
        return arr[end], path[::-1], cn

    def earliest_rise(self, start, end, allowed, or_cells=frozenset()):
        nl = self.nl
        cn = self.cone(start, end, allowed)
        if end not in cn: return None, [], cn, []
        order, edges = self.topo(cn, allowed, frozenset())
        arr = {start: 0}; pred = {}; notes = []
        for n in order:
            if n == start: continue
            ins = [e for e in nl.fin[n] if e[0] in cn and self.arcs_ok(e, allowed, frozenset())]
            if not ins: continue
            kind = ins[0][3]
            if kind == 'ic':
                e = ins[0]; arr[n] = arr[e[0]] + e[2]; pred[n] = [e]; continue
            if kind != 'lut':
                e = min(ins, key=lambda e: arr[e[0]] + e[2]); arr[n] = arr[e[0]] + e[2]; pred[n] = [e]
                notes.append(f'non-LUT {e[4]} on req path, plain min'); continue
            cell = ins[0][4]; cc = nl.cells[cell]; out = cc['out']; init = cc['params']['INIT']
            D = {int(e[5][1:]): e for e in ins}
            fb = cc['fb']
            free = [k for k in cc['support'] if k not in D and k not in fb]
            best = None
            for na in range(1 << len(free)):
                base = {k: (na >> i) & 1 for i, k in enumerate(free)}
                base.update(cc['const'])
                for f in fb: base[f] = 0
                pins0 = dict(base)
                for k in D: pins0[k] = 0
                if lut_eval(init, out, pins0) != 0: continue
                Dk = sorted(D)
                for s in range(1, 1 << len(Dk)):
                    pins = dict(pins0)
                    S = [Dk[i] for i in range(len(Dk)) if s >> i & 1]
                    for k in S: pins[k] = 1
                    if lut_eval(init, out, pins) != 1: continue
                    t = max(arr[D[k][0]] + D[k][2] for k in S)
                    if best is None or t < best[0]: best = (t, [D[k] for k in S], base)
            if cell in or_cells:
                e = min(D.values(), key=lambda e: arr[e[0]] + e[2]); best = (arr[e[0]] + e[2], [e], {})
            if best is None:
                raise RuntimeError(f'req cone LUT {cell} {self.L(cell)} cannot rise under the 0->1 assumption')
            arr[n] = best[0]; pred[n] = best[1]
            if len(D) > 1 and cell in self.state_cells:
                notes.append(f'{self.L(cell)[len(P):]}: derived {sorted(D)}, arrivals+arc '
                             f'{dict((f"A{k}", arr[D[k][0]] + D[k][2]) for k in sorted(D))}, rises at {best[0]}')
        path, n = [], end
        while n in pred:
            e = max(pred[n], key=lambda e: arr[e[0]] + e[2]); path.append(e); n = e[0]
        return arr.get(end), path[::-1], cn, notes

    def plain_min(self, start, end, allowed):
        cn = self.cone(start, end, allowed)
        if end not in cn: return None
        order, edges = self.topo(cn, allowed, frozenset())
        arr = {start: 0}
        for n in order:
            if n not in arr: continue
            for e in edges[n]:
                t = arr[n] + e[2]
                if t < arr.get(e[1], 1 << 60): arr[e[1]] = t
        return arr.get(end)

    def state_sources(self, nets):
        nl = self.nl
        seen, stk, srcs, other = set(), list(nets), set(), set()
        while stk:
            n = stk.pop()
            if n in seen: continue
            seen.add(n)
            if n in nl.state_nets: srcs.add(nl.state_nets[n]); continue
            ins = [e for e in nl.fin[n] if not (e[3] == 'lut' and int(e[5][1:]) in nl.cells[e[4]]['fb'])
                   and e[4] not in self.steer_gates]
            if not ins and n in nl.driver: other.add(nl.driver[n][0])
            for e in ins: stk.append(e[0])
        return srcs, other

    def upstream_links(self, link):
        ctl = self.ctl_cell(link); cnet = self.out_net(ctl)
        dnets = []
        for c in self.link_latches(link):
            cc = self.nl.cells[c]
            for k in cc['support']:
                if k in cc['fb']: continue
                net = cc['pins'][f'A{k}']
                if self.src_of(net) == cnet: continue
                dnets.append(net)
        srcs, other = self.state_sources(dnets)
        ups = sorted({self.latch_link[c] for c in srcs if c in self.latch_link} - {link})
        nonlatch = sorted({self.L(c)[len(P):] if self.L(c).startswith(P) else ("FF (outside udut)" if "$auto$ff" in self.L(c) else self.L(c))
                           for c in (srcs - set(self.latch_link)) | other if 'PACKER' not in self.L(c)})
        return ups, nonlatch

    def adder_restrict(self, nbits, latches):
        """sites.py's counter restriction; only for designs with a `counter` config."""
        adder = P + self.counter['adder']
        k = (nbits + 3) // 4
        excl = set()
        for c, cc in self.nl.cells.items():
            if cc['type'] != 'CARRY4': continue
            mm = re.search(r'slice\[(\d+)\]', self.L(c))
            if self.L(c).startswith(adder) and mm and int(mm[1]) >= k: excl.add(c)
        for c in latches:
            bs = {int(m[2]) for n in self.outbits.get(c, []) for m in [self.counter_re.search(n)] if m}
            if len(bs) > 1: raise RuntimeError(f'latch {self.L(c)} drives several counter bits {bs}')
            if bs and bs.pop() >= nbits: excl.add(c)
        return excl

    def vrange_excl(self, vrange):
        """CARRY4 slices (chain index from CIN<-CO3, cross-checked with the slice[k] name) of each named adder
        instance at index >= ceil(bits/4): carries the gate vectors never produce.  Slice-granular, so pessimistic."""
        excl = set()
        for c, k in self.c4_index.items():
            ln = self.L(c)[len(P):]
            owner = ln.split('.')[0]
            if owner not in vrange: continue
            mm = re.search(r'slice\[(\d+)\]', ln)
            if mm and int(mm[1]) != k: raise RuntimeError(f'CARRY4 chain index {k} != name {ln}')
            if k >= (vrange[owner] + 3) // 4: excl.add(c)
        return excl

    def check(self, gate_cell, rp, sp, launch, transparent=(), legacy_s=False, vrange=None):
        lc = self.ctl_cell(launch)
        if lc is None: return dict(error=f'no C node for {launch}')
        lnet = self.out_net(lc)
        lat = self.link_latches(launch)
        tlat, tctl = set(), set()
        for t in transparent:
            tlat |= self.link_latches(t); tctl.add(self.ctl_cell(t))
        missing = [c for c in lat if c not in self.en_pin]
        if missing: return dict(error=f'no en pin found for {len(missing)} launch latch LUTs')
        self.en_only = lat
        try:
            return self._check(gate_cell, rp, sp, launch, lnet, lat, tlat, tctl, transparent, legacy_s, vrange)
        finally:
            self.en_only = set()

    def _check(self, gate_cell, rp, sp, launch, lnet, lat, tlat, tctl, transparent, legacy_s, vrange):
        nl = self.nl
        req_allowed = (self.join_cells | tctl) - {gate_cell}
        s_allowed = lat | tlat
        if transparent and not legacy_s:
            s_allowed = s_allowed | tctl | req_allowed
        smax, spath, scone = self.longest(lnet, sp[1], s_allowed, excluded=self.steer_gates)
        if smax is None: return dict(error='launch does not reach the select pin')
        rmin, rpath, rcone, notes = self.earliest_rise(lnet, rp[1], req_allowed)
        if rmin is None: return dict(error='no request path from the launch to the req pin', s_max=smax)
        crossed = sorted({e[4] for n in rcone for e in nl.fin[n] if e[0] in rcone and e[4] in req_allowed})
        ror = self.earliest_rise(lnet, rp[1], req_allowed, or_cells=set(crossed))[0]
        rpl = self.plain_min(lnet, rp[1], req_allowed)
        scells = {e[4] for n in scone for e in nl.fin[n] if e[0] in scone and e[3] != 'ic'}
        adder = P + self.counter['adder'] if self.counter else None
        has_adder = bool(adder) and any(nl.cells[x]['type'] == 'CARRY4' and self.L(x).startswith(adder) for x in scells)
        r = dict(s_max=smax, req_min=rmin, own=rmin - smax, orjoin=ror - smax, plain=rpl - smax,
                 req_orjoin=ror, req_plain=rpl, crossed=[self.L(x)[len(P):] for x in crossed],
                 has_adder=has_adder, notes=notes, s_path=self.fmt_path(spath), req_path=self.fmt_path(rpath),
                 s_crit_ic=[e[4] for e in spath if e[3] == 'ic'], req_crit_ic=[e[4] for e in rpath if e[3] == 'ic'],
                 restricted={})
        if transparent and not legacy_s:
            r['s_max_legacy'] = self.longest(lnet, sp[1], lat | tlat, excluded=self.steer_gates)[0]
        if self.counter:
            for b in self.counter['bits']:
                if not has_adder: r['restricted'][b] = r['own']; continue
                excl = self.adder_restrict(b, s_allowed & set(self.latch_link)) | self.steer_gates
                smk = self.longest(lnet, sp[1], s_allowed, excluded=excl)[0]
                r['restricted'][b] = rmin - smk if smk is not None else None
        # carry content of the select cone and of its critical path (owner instance -> CARRY4 count)
        cc_cone = collections.Counter(self.L(x)[len(P):].split('.')[0] for x in scells if nl.cells[x]['type'] == 'CARRY4')
        cc_crit = collections.Counter(self.L(e[4])[len(P):].split('.')[0] for e in spath if e[3] == 'c4')
        r['carry_cone'] = dict(cc_cone); r['carry_crit'] = dict(cc_crit)
        r['crossed_latches'] = sorted({self.latch_link[e[4]] for e in spath if e[4] in self.latch_link})
        if vrange:
            ex = self.vrange_excl(vrange)
            if any(x in ex for x in scells):
                smv = self.longest(lnet, sp[1], s_allowed, excluded=ex | self.steer_gates)[0]
                r['vr'] = rmin - smv if smv is not None else None
                r['vr_s'] = smv
            else:
                r['vr'] = r['own']
        return r

    def fmt_path(self, path):
        out, t = [], 0
        for e in path:
            t += e[2]
            if e[3] == 'ic': continue
            out.append(f'{t:7d}  {e[4]} {e[5]:<8s} +{e[2]:4d}  {self.L(e[4])[len(P):]}')
        return out


# ---------------------------------------------------------------------------------------------------- driver --
def enumerate_launches(eng, sp_net, research_launch, depth):
    srcs, other = eng.state_sources([sp_net])
    direct = sorted({eng.latch_link[c] for c in srcs if c in eng.latch_link})
    notes = []
    nonlatch = sorted({eng.L(c) for c in (srcs - set(eng.latch_link)) | other if 'PACKER' not in eng.L(c)})
    if nonlatch: notes.append(f'select cone has non-latch sources {nonlatch}')
    if research_launch and research_launch not in direct:
        notes.append(f'research launch {research_launch} is NOT a direct latch source of the select: {direct}')
    out = [(l, (), 'direct') for l in direct]
    frontier = [(l, ()) for l in direct]
    for d in range(depth):
        nxt = []
        for x, tr in frontier:
            ups, nonl = eng.upstream_links(x)
            if nonl: notes.append(f'{x} latch d also from non-latch sources {nonl} (not launched)')
            for y in ups:
                if y in tr or any(y == o[0] and o[1] == (x,) + tr for o in out): continue
                cand = (y, (x,) + tr, f'upstream-{d + 1}')
                out.append(cand); nxt.append((y, (x,) + tr))
        frontier = nxt
    return out, notes


def site_list(des, K):
    """[(site, gate, research-record-or-None)]: research's list where there is one (xorshift reproduction), else RTL."""
    cfg = DESIGNS[des]
    if cfg['research']:
        return [(rr['site'], rr['gate'], rr) for rr in parse_research(cfg['research'])]
    rs = rtl_sites(K)
    return [(s, g, None) for s in sorted(rs) for g in rs[s]['gates']]


def run_design(des, depth, corners=None):
    cfg = DESIGNS[des]
    corners = corners or cfg['corners']
    K = parse_kernel(cfg['rtl'])
    sites = rtl_sites(K)
    rows, notes = [], []
    for corner in corners:
        eng = Engine(cfg['work'][corner], cfg['rj'], K, cfg['counter'])
        if eng.unknown_latch: notes.append(f'{des} {corner}: latch LUTs of no RTL link: {eng.unknown_latch[:6]}')
        if not cfg['research']:
            notes.append(f'{des} {corner}: RTL-derived graph classes: {len(eng.join_cells)} request-join C-elements '
                         f'{sorted(eng.L(c)[len(P):] for c in eng.join_cells)}; {len(eng.steer_gates)} steer gates; '
                         f'{len(eng.latch_link)} latch LUTs in {len(set(eng.latch_link.values()))} links, '
                         f'{len(eng.unknown_latch)} unassigned; {len(eng.en_pin)} with a unique en pin')
        for site, gate, rr in site_list(des, K):
            info = sites[site]
            if rr and rr.get('sel_gate') != gate: notes.append(f'{des} {gate}: research req/sel on different gates')
            gp = eng.gate_pins(gate, info['req_net'], info['s_net'], K['alias'])
            if gp is None or gp[1] is None or gp[2] is None:
                notes.append(f'{des} {corner} {gate}: could not map pins {gp}'); continue
            gc, rp, sp = gp
            if corner == corners[0]:
                if rr:
                    notes.append(f'{des} {gate}: pins by net name req {rp[0]} s {sp[0]} '
                                 + ('== research' if (rp[0], sp[0]) == (rr['req_pin'], rr['sel_pin']) else '!= research'))
                    if rp[0] != rr['req_pin'] or sp[0] != rr['sel_pin']:
                        notes.append(f'{des} {gate}: pins by net name req {rp[0]} s {sp[0]} differ from research '
                                     f'req {rr["req_pin"]} sel {rr["sel_pin"]}')
                else:
                    notes.append(f'{des} {gate}: pins by net name req {rp[0]} ({info["req_net"]}) s {sp[0]} ({info["s_net"]})')
            launches, lnotes = enumerate_launches(eng, sp[1], rr['launch'] if rr else None, depth)
            if corner == corners[0]:
                notes += [f'{des} {gate}: {x}' for x in lnotes]
            for launch, tr, how in launches:
                try:
                    r = eng.check(gc, rp, sp, launch, tr, vrange=cfg.get('vrange'))
                except RuntimeError as ex:
                    r = dict(error=str(ex))
                row = dict(design=des, corner=corner, kind=info['kind'], site=site, gate=gate,
                           req_pin=rp[0], s_pin=sp[0], launch=launch, transparent=list(tr), how=how)
                if rr:
                    row.update(research_launch=(launch == rr['launch'] and not tr),
                               research_raw=rr['raw'], research_guarded=rr['guarded'], research_status=rr['status'],
                               research_req=rr['earliest'], research_sel=rr['latest'])
                row.update(r)
                if rr and 'own' in r:
                    row['own_guarded'] = round(GUARD_LO * r['req_min'] - GUARD_HI * r['s_max'])
                    row['orjoin_guarded'] = round(GUARD_LO * r['req_orjoin'] - GUARD_HI * r['s_max'])
                rows.append(row)
        del eng
    return rows, notes


# ------------------------------------------------------------------------------------------- inventory report --
def inventory(des):
    """RTL-derived structure of a design, cross-checked against routed.json cell names (one corner's maps)."""
    cfg = DESIGNS[des]
    K = parse_kernel(cfg['rtl'])
    m = list(json.load(open(cfg['rj']))['modules'].values())[0]
    names = [n[len(P):] for n in m['cells'] if n.startswith(P)]
    del m
    L = [f'{des}: top module {K["top"]}, {len(K["instances"])} instances in the kernel hierarchy']
    def cnt(prefix): return sum(1 for n in names if n.startswith(prefix))
    L.append(f'  bd_steer ({len(K["steers"])}): ' + ', '.join(f'{s} [req {d["req_net"]}, s {d["s_net"]}]' for s, d in K['steers'].items()))
    L.append(f'  bd_mux ({len(K["muxes"])}): ' + ', '.join(f'{s} [ctl_req {d["req_net"]}, s {d["s_net"]}]' for s, d in K['muxes'].items()))
    L.append(f'  bd_join ({len(K["joins"])}), routed LUTs under each: ' + ', '.join(f'{j} {cnt(j + ".")}' for j in K['joins']))
    L.append(f'  fused ops ({len(K["fused"])}): ' + ', '.join(
        f'{f} ({d["module"]}; udly chain {cnt(f + ".udly.chain.")} LUTs; CARRY4 {sum(1 for n in names if n.startswith(f + ".") and n.endswith("carry4"))})'
        for f, d in K['fused'].items()))
    L.append(f'  arbitrated merges ({len(K["merges"])}): ' + ', '.join(K['merges']))
    L.append(f'  bd_delay_gated ({len(K["dgated"])}): ' + ', '.join(f'{d} {cnt(d + ".chain.")}' for d in K['dgated']))
    plain = [l for l in K['links'] if not any(l in st for st in K['pipes'].values())]
    L.append(f'  bd_link ({len(plain)}): ' + ', '.join(f'{l} lat {cnt(l + ".lat.")}' for l in plain))
    L.append(f'  bd_pipe ({len(K["pipes"])}): ' + ', '.join(f'{p} = ' + ' + '.join(f'stage lat {cnt(s + ".lat.")}' for s in st)
                                                           for p, st in K['pipes'].items()))
    missing_ctl = [l for l in K['links'] if (l + '.ctl.u.u') not in names]
    L.append(f'  links without a routed C node <link>.ctl.u.u: {missing_ctl or "none"}')
    missing_gate = [g for s in rtl_sites(K).values() for g in s['gates'] if g not in names]
    L.append(f'  site gates missing from routed.json: {missing_gate or "none"}')
    return L, K


def xorshift_inventory_checks():
    """RTL-derived sets vs sites.py's regexes and research's site list (A and B, worst corner engine)."""
    out = []
    REQ_JOIN_RE = re.compile(r'\.ujoin\.|_j\.|\.uj[01]$')
    for des in ('A', 'B'):
        cfg = DESIGNS[des]
        K = parse_kernel(cfg['rtl'])
        eng = Engine(cfg['work']['worst'], cfg['rj'], K, cfg['counter'])
        old_join = {c for c in eng.state_cells if REQ_JOIN_RE.search(eng.L(c))}
        old_steer = {c for c in eng.nl.cells if re.search(r'\.ucond_br\d+\.u\$LUT[56]$', eng.L(c))}
        old_latch = {c for c in eng.state_cells if eng.L(c).startswith(P) and '.lat.' in eng.L(c)}
        rg = {(rr['site'], rr['gate']) for rr in parse_research(cfg['research'])}
        rt = {(s, g) for s, d in rtl_sites(K).items() for g in d['gates']}
        out.append(f'  {des}: join C-elements RTL {len(eng.join_cells)} vs sites.py regex {len(old_join)}: '
                   f'{"EQUAL" if eng.join_cells == old_join else "DIFFERENT " + str(sorted(eng.L(c) for c in eng.join_cells ^ old_join))}')
        out.append(f'  {des}: steer gates RTL {len(eng.steer_gates)} vs regex {len(old_steer)}: '
                   f'{"EQUAL" if eng.steer_gates == old_steer else "DIFFERENT"}')
        out.append(f'  {des}: latch LUTs assigned to an RTL link {len(eng.latch_link)} of {len(old_latch)} ".lat." state LUTs; '
                   f'unassigned {eng.unknown_latch[:5] or "none"}')
        out.append(f'  {des}: site gates RTL {len(rt)} vs research {len(rg)}: '
                   f'{"EQUAL" if rt == rg else "DIFFERENT rtl-only " + str(sorted(rt - rg)) + " research-only " + str(sorted(rg - rt))}')
        del eng
    return out


# ------------------------------------------------------------------------------------- xorshift reproduction --
def fmt_row_x(r):
    tr = ('  T=' + ','.join(r['transparent'])) if r['transparent'] else ''
    lab = f"{r['design']} {r['gate']:<18s} {r['corner']:<7s} {r['launch'] + tr:<62s}"
    if 'own' not in r:
        return f"{lab} -- {r['error']}"
    r12 = r['restricted'][12]
    r12s = f"{r12:>6}" if r['has_adder'] else '     ='
    rs = f"{r['research_raw']:>+6}" if r['research_launch'] and r['corner'] == 'worst' else (
        f"({r['research_raw']:>+5})" if r['corner'] == 'worst' else '')
    return (f"{lab} s {r['s_max']:>6} req {r['req_min']:>6}  OWN {r['own']:>6}  <2^12 {r12s}  OR {r['orjoin']:>6}"
            f"  plain {r['plain']:>6}  | research raw {rs}")


def xorshift_main(depth, no_plant):
    """Re-run designs A/B through this generalised engine, write sites_results_regen.txt, compare with sites.py's
    sites_results.txt/.json.  The txt is rendered with sites.py's own summarise/sanity code (imported, not run as a
    script) so that only the row data can differ."""
    import sites as S0
    rows, notes = [], []
    for des in ('A', 'B'):
        r, n = run_design(des, depth)
        for x in r:      # sites.py rows have no carry/vr fields; drop the additions before comparing
            for k in ('carry_cone', 'carry_crit', 'crossed_latches', 'vr', 'vr_s'): x.pop(k, None)
        rows += r; notes += n
        print(f'design {des}: {len(r)} rows', file=sys.stderr)
    L = []
    L.append('T93 sites.py -- rule E at every select site, own model vs OR-join vs plain shortest path (ps, raw, no guard)')
    L.append('own = earliest req rise (AND/C wait for last input) - latest select change, common launch <link>.ctl.u.u')
    L.append('OR = C-elements crossed on the req path rise on their FIRST derived input (research semantics); '
             'plain = shortest path ignoring AND taps too')
    L.append('<2^12 = own with select cone restricted to loop counter < 2^12 ("=" when the select cone has no adder)')
    L.append("research raw: its raw margin at ITS launch (nextpnr SDF, a different delay model); in () = that "
             "site gate's research number shown on rows of other launches, for reference")
    L.append('T= links treated as transparent (launch is upstream of them)')
    L.append('')
    CORNERS = ('worst', 'fastmin')
    key = lambda r: (r['design'], r['site'], r['gate'], not r['research_launch'], r['how'], r['launch'],
                     r['transparent'], CORNERS.index(r['corner']))
    for r in sorted(rows, key=key):
        L.append(fmt_row_x(r))
    L.append('')
    L.append('== SUMMARY ==')
    slines, neg_own, or_only, both, rneg, gcls = S0.summarise(rows)
    L += slines
    L.append('')
    L.append(f'sites checked: {len({(r["design"], r["site"]) for r in rows})} '
             f'({len({(r["design"], r["gate"]) for r in rows})} gates), rows: {len(rows)} '
             f'({sum("own" in r for r in rows)} with a result)')
    L.append(f'own-model negative at either corner (any launch): {len(neg_own)}')
    for des, site, ow, of, b in neg_own:
        L.append(f'  {des} {site}: worst {ow}, fastmin {of}  (binding: {b})')
    L.append(f'research-flagged sites (raw < 0 or guarded VIOLATED): {len(rneg)}: ' + ', '.join(f'{d} {s}' for d, s in rneg))
    L.append(f'  negative under OR-join at the research launch but own >= 0 everywhere ("OR-join only"): {len(or_only)}: '
             + ', '.join(f'{d} {s}' for d, s in or_only))
    L.append(f'  negative under both own and OR-join: {len(both)}: ' + ', '.join(f'{d} {s}' for d, s in both))
    rest = [x for x in rneg if x not in or_only and x not in both]
    L.append(f'  OR-join >= 0 and own >= 0 (research flag from its guardband / SDF only): {len(rest)}: '
             + ', '.join(f'{d} {s}' for d, s in rest))
    L.append("guarded view (research's guard on our numbers, research launch, either corner):")
    for k, v in sorted(gcls.items()):
        L.append(f'  {k}: {len(v)}: ' + ', '.join(v))
    L.append('')
    L.append('== SANITY: ucond_br6 rows vs results.txt (rule_e.py) ==')
    sl, sok = sanity_br6_gen(rows)
    L += sl
    L.append(f'  -> {"all equal to results.txt (transparent rows: in latches-only mode; the default adds the transparent link en path)" if sok else "MISMATCH"}')
    if not no_plant:
        L.append('')
        L.append('== SANITY: planted delay on other sites (copy of netlist_baked.v, full re-parse) ==')
        L += plant_xorshift()
    if notes:
        L.append('')
        L.append('== NOTES (pin mapping, launch discovery) ==')
        L += ['  ' + n for n in dict.fromkeys(notes)]
    open(os.path.join(H, 'sites_results_regen.txt'), 'w').write('\n'.join(L) + '\n')
    # comparisons
    C = ['== sites_gen.py xorshift vs sites.py outputs ==']
    old_txt = open(os.path.join(H, 'sites_results.txt')).read().splitlines()
    diff = [(i, a, b) for i, (a, b) in enumerate(zip(old_txt, L)) if a != b]
    C.append(f'  sites_results_regen.txt vs sites_results.txt: {len(L)} vs {len(old_txt)} lines, '
             f'{len(diff)} differing lines' + ('  -> IDENTICAL' if not diff and len(L) == len(old_txt) else ''))
    for i, a, b in diff[:20]:
        C.append(f'    line {i + 1}: old {a!r}\n             new {b!r}')
    old_rows = json.load(open(os.path.join(H, 'sites_results.json')))['rows']
    new_rows = json.loads(json.dumps(rows, default=str))
    C.append(f'  rows vs sites_results.json: {len(new_rows)} vs {len(old_rows)}, '
             + ('ALL FIELDS IDENTICAL (incl. critical paths, crossed C-elements, notes)' if new_rows == old_rows else
                f'{sum(a != b for a, b in zip(new_rows, old_rows))} rows differ'))
    C.append('== RTL-derived inventory vs sites.py hardcoding ==')
    C += xorshift_inventory_checks()
    print('\n'.join(C))
    open(os.path.join(H, 'sites_gen_xorshift_check.txt'), 'w').write('\n'.join(C) + '\n')
    return C


def sanity_br6_gen(rows):
    """sites.py's sanity_br6, with this module's Engine for the legacy re-run."""
    old = {}
    for l in open(os.path.join(H, 'results.txt')):
        m = re.match(r'(\w) (main|combined|other operand): launch (\S+?)(?:,| |$).*?\s(worst|fastmin)\s+(u\$LUT\d)'
                     r'.*?MARGIN\s+(-?\d+)\s+<2\^11\s+(-?\d+)\s+<2\^12\s+(-?\d+).*?OR-join\s+(-?\d+)\s+plain-min\s+(-?\d+)', l)
        if not m: continue
        des, kind, launch, corner, lut = m[1], m[2], m[3], m[4], m[5]
        tr = ('ulink_n30__1',) if kind == 'combined' else ()
        old[(des, launch, tr, corner, lut)] = tuple(int(m[i]) for i in (6, 8, 9, 10))
    out, allok, legacy = [], True, {}
    for k, v in sorted(old.items()):
        des, launch, tr, corner, lut = k
        rs = [r for r in rows if r['design'] == des and r['gate'] == 'ucond_br6.' + lut and r['corner'] == corner
              and r['launch'] == launch and tuple(r['transparent']) == tr and 'own' in r]
        if not rs:
            out.append(f'  {k}: results.txt {v}  -- no sites.py row'); allok = False; continue
        r = rs[0]
        new = (r['own'], r['restricted'][12], r['orjoin'], r['plain'])
        leg = ''
        if 's_max_legacy' in r and r['s_max_legacy'] != r['s_max']:
            leg = f'  (s_max {r["s_max"]} vs latches-only {r["s_max_legacy"]}: en path of the transparent link)'
        same = new == v
        if tr and not same:
            cfg = DESIGNS[des]; K = parse_kernel(cfg['rtl'])
            eng = legacy.setdefault((des, corner), Engine(cfg['work'][corner], cfg['rj'], K, cfg['counter']))
            s = rtl_sites(K)['ucond_br6']
            gc, rp, sp = eng.gate_pins('ucond_br6.' + lut, s['req_net'], s['s_net'], K['alias'])
            lg = eng.check(gc, rp, sp, launch, tr, legacy_s=True)
            lgv = (lg['own'], lg['restricted'][12], lg['orjoin'], lg['plain'])
            leg += f'; latches-only mode {lgv} {"EQUAL" if lgv == v else "DIFFERENT"}'
            same_legacy = lgv == v
        else:
            same_legacy = same
        allok &= same_legacy
        out.append(f"  {des} {launch}{' T=' + tr[0] if tr else ''} {corner:<7s} {lut}: results.txt "
                   f"own/<2^12/OR/plain {v}  sites.py {new}  {'EQUAL' if same else 'DIFFERENT'}{leg}")
    legacy.clear()
    return out, allok


def plant_run(des, corner, cases, pd_name):
    """cases: [(gate, site, launch, transparent, ic, why, expected delta)] on one netlist copy each.
    expected <= 0: exact; expected > 0 (request path): 0 < delta <= expected."""
    cfg = DESIGNS[des]; src = cfg['work'][corner]
    K = parse_kernel(cfg['rtl']); S = rtl_sites(K)
    pd = os.path.join(H, pd_name)
    os.makedirs(pd, exist_ok=True)
    for f in ('names.map', 'nets.map'):
        if not os.path.exists(os.path.join(pd, f)): os.symlink(os.path.join(src, f), os.path.join(pd, f))
    txt = open(os.path.join(src, 'netlist_baked.v')).read()
    lines = []
    for gate, site, launch, tr, base, ic, why, exp in cases:
        m = re.search(r'ICBUF #\(\.D\((\d+)\)\) ' + ic + r' ', txt)
        d0 = int(m[1])
        open(os.path.join(pd, 'netlist_baked.v'), 'w').write(txt.replace(m[0], f'ICBUF #(.D({d0 + 2000})) {ic} ', 1))
        e2 = Engine(pd, cfg['rj'], K, cfg['counter'])
        gc, rp, sp = e2.gate_pins(gate, S[site]['req_net'], S[site]['s_net'], K['alias'])
        r = e2.check(gc, rp, sp, launch, tuple(tr), vrange=cfg.get('vrange'))
        d = r['own'] - base['own']
        ok = (d == exp) if exp <= 0 else (0 < d <= exp)
        trs = (' T=' + ','.join(tr)) if tr else ''
        lines.append(f"  PLANT {ic} (D {d0} -> {d0 + 2000}) ({why}) at {des} {corner} {gate} launch {launch}{trs}: "
                     f"own {base['own']} -> {r['own']} (delta {d:+d}, expected {exp:+d}{' or less' if exp > 0 else ''}) "
                     f"{'PASS' if ok else 'FAIL'}; OR {base['orjoin']} -> {r['orjoin']}, plain {base['plain']} -> {r['plain']}")
        del e2
    shutil.rmtree(pd)
    return lines


def plant_xorshift():
    """sites.py's plant_test cases, through this engine."""
    cfg = DESIGNS['A']; K = parse_kernel(cfg['rtl']); S = rtl_sites(K)
    eng = Engine(cfg['work']['worst'], cfg['rj'], K, cfg['counter'])
    cases = []
    for site, gate, launch in (('ucond_br3', 'ucond_br3.u$LUT6', 'ulink_n1__1'), ('umux0', 'umux0.uj0', 'ulink_n12__0')):
        gc, rp, sp = eng.gate_pins(gate, S[site]['req_net'], S[site]['s_net'], K['alias'])
        base = eng.check(gc, rp, sp, launch)
        s_ic = base['s_crit_ic'][len(base['s_crit_ic']) // 2]
        r_ic = base['req_crit_ic'][len(base['req_crit_ic']) // 2]
        cases += [(gate, site, launch, (), base, s_ic, 'critical select path', -2000),
                  (gate, site, launch, (), base, r_ic, 'critical request path', +2000)]
    far = 'ic_012664'
    cases2 = [c for c in cases] + [(c[0], c[1], c[2], (), c[4], far, 'unrelated ICBUF (ucond_br6 LUT6 s)', 0)
                                  for c in cases[::2]]
    del eng
    lines = plant_run('A', 'worst', cases2, '_plant_gen')
    # sites.py's line format: "at A worst <gate> launch <launch>: ..." -- rewrite ours to it for the text comparison
    out = []
    for l in lines:
        l = re.sub(r' \(D \d+ -> \d+\)', ' +2000 ps', l)
        out.append(l)
    return out


# ------------------------------------------------------------------------------------------------ collatz report --
def fmt_row_c(r):
    tr = ('  T=' + ','.join(r['transparent'])) if r['transparent'] else ''
    lab = f"{r['gate']:<16s} {r['corner']:<8s} {r['launch'] + tr:<64s}"
    if 'own' not in r:
        return f"{lab} -- {r['error']}"
    cc = ','.join(f'{k}x{v}' for k, v in sorted(r['carry_crit'].items())) or '-'
    vr = f"{r['vr']:>6}" if r.get('vr') is not None and r['vr'] != r['own'] else '     ='
    return (f"{lab} s {r['s_max']:>6} req {r['req_min']:>6}  OWN {r['own']:>6}  OR {r['orjoin']:>6}  plain {r['plain']:>6}"
            f"  | vr {vr}  carry(crit) {cc}")


def collatz_main(depth, no_plant):
    des = 'C'; cfg = DESIGNS[des]
    inv, K = inventory(des)
    rows, notes = run_design(des, depth)
    corners = cfg['corners']
    L = []
    L.append('T93 sites_gen.py -- rule E at every select site of the collatz board candidate (BOARD-QUEUE item 22, '
             'research 514ac04a: fcolsz2, board seed 26, own build /root/t65/colsz2_26)')
    L.append('Corners: worst = work_colsz2_26_mon_worst (band SDF: chains 0.21, CARRY4/SELMUX/FF 1, rest 0.288, + scatter); '
             'FAST_MIN = ..._mon_fastmin (xray min); SLOW_MAX = ..._mon_slowmax (xray max).  Delays: baked netlist params.')
    L.append('own   = earliest req rise at the gate (AND taps / C-elements wait for their LAST launch-derived input) '
             '- latest select change (static longest path, FULL carry everywhere), from <launch>.ctl.u.u at t=0')
    L.append('OR    = diagnostic: every C-element crossed on the request path rises on its FIRST derived input')
    L.append('plain = diagnostic: plain shortest path over the request cone (ignores the delay-chain AND taps too)')
    L.append("vr    = informational, NOT a margin: own with the uaddi0 slices >= 6 (bits >= 24) and uaddi1 slices >= 3 (bits >= 12) "
             "dropped, i.e. only carries the 13 gate vectors can produce (n < 2^20, 3n+1 < 2^22, steps < 2^9); '=' = no such carry in the cone")
    L.append('carry(crit) = CARRY4 slices on the critical select path, by owning instance')
    L.append('T= links treated as transparent (launch is upstream of them: a Muller latch passes a late d while its node is high)')
    L.append('Raw ps, no guardband.  Gates: bd_steer u$LUT6/u$LUT5 (both fractured halves), bd_mux uj0/uj1.')
    L.append('')
    L.append('== STRUCTURE (from the kernel Verilog, cross-checked with routed.json cell names) ==')
    L += inv
    L.append('')
    L.append('== ROWS: one per (site gate, launch, corner) ==')
    key = lambda r: (r['site'], r['gate'], r['how'], r['launch'], r['transparent'], corners.index(r['corner']))
    for r in sorted(rows, key=key):
        L.append(fmt_row_c(r))
    L.append('')
    L.append('== SUMMARY: minimum own margin per site and corner (over both gates and every launch) ==')
    ok = [r for r in rows if 'own' in r]
    by = collections.defaultdict(list)
    for r in ok: by[r['site']].append(r)
    hdr = f"{'site':<10s} {'kind':<8s} " + ' '.join(f'{"own " + c:>13s}' for c in corners) + ' | ' + \
          ' '.join(f'{"OR " + c:>12s}' for c in corners) + ' | ' + ' '.join(f'{"plain " + c:>14s}' for c in corners) + \
          ' | binding launch (own, worst) / critical carry'
    L.append(hdr)
    neg, summ = [], {}
    for site in sorted(by):
        rs = by[site]
        def mn(f, c): v = [x[f] for x in rs if x['corner'] == c]; return min(v) if v else None
        own = {c: mn('own', c) for c in corners}
        summ[site] = dict(own=own, orj={c: mn('orjoin', c) for c in corners}, plain={c: mn('plain', c) for c in corners})
        bind = min((x for x in rs if x['corner'] == corners[0]), key=lambda x: x['own'])
        b = bind['launch'] + (' T=' + ','.join(bind['transparent']) if bind['transparent'] else '')
        cc = ','.join(f'{k}x{v}' for k, v in sorted(bind['carry_crit'].items())) or 'no carry'
        L.append(f"{site:<10s} {rs[0]['kind']:<8s} " + ' '.join(f'{own[c]:>13}' for c in corners) + ' | '
                 + ' '.join(f'{summ[site]["orj"][c]:>12}' for c in corners) + ' | '
                 + ' '.join(f'{summ[site]["plain"][c]:>14}' for c in corners) + f' | {b} / {cc}')
        for c in corners:
            if own[c] < 0: neg.append((site, c, own[c]))
    L.append('')
    nerr = [r for r in rows if 'own' not in r]
    L.append(f'sites: {len(by)}  gates: {len({r["gate"] for r in rows})}  rows: {len(rows)} ({len(ok)} with a result, '
             f'{len(nerr)} without)')
    for r in nerr: L.append(f'  no result: {r["gate"]} {r["corner"]} {r["launch"]} T={r["transparent"]}: {r["error"]}')
    L.append(f'own-model negative (any site, launch, corner): {len(neg)}' + ''.join(f'\n  {s} {c} {v}' for s, c, v in neg))
    orneg = sorted({(r['site'], r['corner']) for r in ok if r['orjoin'] < 0})
    L.append(f'OR-join diagnostic negative (site, corner): {len(orneg)}: ' + ', '.join(f'{s} {c}' for s, c in orneg))
    worst = min(ok, key=lambda r: r['own'])
    L.append(f'overall minimum own: {worst["own"]} at {worst["gate"]} {worst["corner"]} launch {worst["launch"]}'
             + (f' T={",".join(worst["transparent"])}' if worst['transparent'] else ''))
    L.append('')
    L.append('== DATA RANGE: carries the 13 gate vectors do not exercise ==')
    L.append('  Vectors (audit/t65/collatz_13.hex): n = 2,4,16,64,256,1024,4096,16384,32768,27,97,871,6171.  Max trajectory '
             'value 975400 (< 2^20, from 6171); max odd n 325133 -> 3n+1 = 975400; uaddi0 (3n+1 on every n, even ones too) '
             '< 3*975400+1 < 2^22.  Steps (uaddi1) <= 261 < 2^9.  n>>1 (uselect0) and the n==1 compares (ucmpi0/ucmpi2) have no carry.')
    L.append('  So uaddi0 carries into bits 22..31 (slices 5 partly, 6, 7) and uaddi1 carries above bit 8 are never produced '
             'by the gate (a full-range input up to 2^31 produces them).  The own/OR/plain margins above use the STATIC '
             'longest path, i.e. the full 32-bit carry through every CARRY4 slice; `vr` shows what the vector range alone would give.')
    crow = [r for r in ok if r['carry_cone']]
    owners = collections.Counter(k for r in crow for k in r['carry_cone'])
    L.append(f'  rows whose select cone contains CARRY4s: {len(crow)} of {len(ok)}; owners: {dict(owners)}')
    vrd = [r for r in ok if r.get('vr') is not None and r['vr'] != r['own']]
    if vrd:
        mx = max(vrd, key=lambda r: r['vr'] - r['own'])
        L.append(f'  rows where the full carry is longer than the vector-range carry: {len(vrd)}; largest difference '
                 f'{mx["vr"] - mx["own"]} ps ({mx["gate"]} {mx["corner"]} {mx["launch"]} T={",".join(mx["transparent"])})')
        for site in sorted({r['site'] for r in vrd}):
            for c in corners:
                xs = [r for r in ok if r['site'] == site and r['corner'] == c]
                if xs:
                    L.append(f'    {site} {c}: min own {min(x["own"] for x in xs)} (full carry), min vr {min(x["vr"] for x in xs)}')
    else:
        L.append('  no row has its critical select path through a carry beyond the vector range: full-carry and '
                 'vector-range margins coincide (vr "=" on every row)')
    # where the carry sits: every select cone holding uaddi0 reaches s through a TRANSPARENT link (the adder's output
    # latch); the full-carry d path is the latches-only s_max, the binding path is that link's en path
    tr_c = [r for r in crow if r['transparent'] and 's_max_legacy' in r]
    if tr_c:
        L.append('  every such row is an upstream launch through a transparent link; full-carry d path (latches-only '
                 's_max) vs the en path that binds (s_max), per corner:')
        for c in corners:
            xs = [r for r in tr_c if r['corner'] == c]
            if not xs: continue
            g = min(xs, key=lambda r: r['s_max'] - r['s_max_legacy'])
            h = min(xs, key=lambda r: r['req_min'] - r['s_max_legacy'])
            L.append(f'    {c}: en path later than the full-carry d path by >= {g["s_max"] - g["s_max_legacy"]} ps '
                     f'({g["gate"]} {g["launch"]} T={",".join(g["transparent"])}); margin on the full-carry d path alone '
                     f'>= {h["req_min"] - h["s_max_legacy"]} ps')
        L.append('    i.e. the 32-bit carry of 3n+1 settles at ulink_n26.d before ulink_n26 opens (uaddi0 matched delay), '
                 'so it never sets a select margin; a full-range n cannot make it binding under this delay model.')
    nc = [r for r in ok if not r['carry_cone']]
    L.append(f'  the other {len(nc)} rows have no CARRY4 in the select cone (ucmpi0/ucmpi2 equality compares are LUT+MUXF7/F8, '
             'n>>1 is wiring, the merge index is a 1-bit latch)')
    plant_lines = []
    if not no_plant:
        L.append('')
        L.append('== SANITY: planted +2000 ps ICBUF (copy of netlist_baked.v, full re-parse) ==')
        plant_lines = plant_collatz(rows)
        L += plant_lines
    if notes:
        L.append('')
        L.append('== NOTES (pin mapping, launch discovery) ==')
        L += ['  ' + n for n in dict.fromkeys(notes)]
    open(os.path.join(H, 'sites_collatz_item22.txt'), 'w').write('\n'.join(L) + '\n')
    json.dump(dict(rows=rows, notes=notes, summary=summ), open(os.path.join(H, 'sites_collatz_item22.json'), 'w'),
              indent=1, default=str)
    print('\n'.join(L[L.index('== SUMMARY: minimum own margin per site and corner (over both gates and every launch) =='):]))


def plant_collatz(rows):
    """worst corner: the site gate/launch with the smallest own margin.  +2000 on an ICBUF of its critical select path
    (one not on the request path) must move own by exactly -2000; +2000 on its critical request path must raise own by
    (0, 2000]; +2000 on another site's select-pin ICBUF must change nothing."""
    ok = [r for r in rows if 'own' in r and r['corner'] == 'worst']
    D = {m[2]: int(m[1]) for m in re.finditer(r'ICBUF #\(\.D\((\d+)\)\) (\w+) ',
                                                open(DESIGNS['C']['work']['worst'] + '/netlist_baked.v').read())}
    def pick(ics):      # middle ICBUF of the path among those with a non-zero routed delay (a real wire)
        nz = [ic for ic in ics if D.get(ic, 0) > 0] or ics
        return nz[len(nz) // 2]
    tgt = min(ok, key=lambda r: r['own'])
    req_ics = set(tgt['req_crit_ic'])
    s_ics = [ic for ic in tgt['s_crit_ic'] if ic not in req_ics]
    s_ic = pick(s_ics)
    r_ic = tgt['req_crit_ic'][len(tgt['req_crit_ic']) // 2]
    # unrelated: the last ICBUF (into the s pin) of a different site's worst row whose select is not this one's
    other = next(r for r in sorted(ok, key=lambda r: -r['own']) if r['site'] != tgt['site']
                 and r['s_crit_ic'][-1] not in tgt['s_crit_ic'] and r['s_crit_ic'][-1] not in req_ics)
    far = other['s_crit_ic'][-1]
    base = dict(own=tgt['own'], orjoin=tgt['orjoin'], plain=tgt['plain'])
    g, s, l, tr = tgt['gate'], tgt['site'], tgt['launch'], tgt['transparent']
    cases = [(g, s, l, tr, base, s_ic, 'critical select path', -2000),
             (g, s, l, tr, base, r_ic, 'critical request path', +2000),
             (g, s, l, tr, base, far, f'unrelated ICBUF: {other["gate"]} s pin', 0)]
    # a second site, different kind, for coverage: the smallest-margin mux gate (or steer if the first was a mux)
    k2 = 'bd_mux' if tgt['kind'] == 'bd_steer' else 'bd_steer'
    t2 = min((r for r in ok if r['kind'] == k2), key=lambda r: r['own'], default=None)
    if t2:
        rq2 = set(t2['req_crit_ic']); s2 = [ic for ic in t2['s_crit_ic'] if ic not in rq2]
        cases.append((t2['gate'], t2['site'], t2['launch'], t2['transparent'],
                      dict(own=t2['own'], orjoin=t2['orjoin'], plain=t2['plain']), pick(s2), 'critical select path', -2000))
    return plant_run('C', 'worst', cases, '_plant_gen_c')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('which', choices=('collatz', 'xorshift'))
    ap.add_argument('--depth', type=int, default=2)
    ap.add_argument('--no-plant', action='store_true')
    a = ap.parse_args()
    if a.which == 'collatz': collatz_main(a.depth, a.no_plant)
    else: xorshift_main(a.depth, a.no_plant)


if __name__ == '__main__':
    main()
