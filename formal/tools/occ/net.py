"""Shard C (UNTRUSTED): Python re-implementation of huffx.cpp's machine (prep.txt reader, comb settle,
reset, latches-first moves), plus supports (storage/env leaves of the comb fan-in)."""
import sys, collections

class Net:
    def __init__(self, fn):
        f = open(fn); w, nn = f.readline().split(); nn = int(nn)
        self.names = [f.readline().rstrip("\n") for _ in range(nn)]
        def rg(st):
            t = f.readline().split(); out, k = int(t[0]), int(t[1]); ins = list(map(int, t[2:2 + k]))
            tt = int(t[2 + k], 16); latch = int(t[3 + k]) if st else 0
            return (out, k, ins, tt, latch)
        w, n = f.readline().split(); self.comb = [rg(False) for _ in range(int(n))]
        w, n = f.readline().split(); self.stor = [rg(True) for _ in range(int(n))]
        t = f.readline().split(); self.bnd = {kv.split("=")[0]: int(kv.split("=")[1]) for kv in t[1:]}
        self.AD = list(map(int, f.readline().split()[1:])); self.BD = list(map(int, f.readline().split()[1:]))
        self.OD = list(map(int, f.readline().split()[1:])); self.ENV = list(map(int, f.readline().split()[1:]))
        self.NN = nn
        self.combOf = {g[0]: i for i, g in enumerate(self.comb)}
        self.storOf = {g[0]: i for i, g in enumerate(self.stor)}
        rk = {}
        for g in self.comb:
            rk[g[0]] = max([rk[x] + 1 for x in g[2] if x in self.combOf] + [0])
        self.rank = rk; self.maxRank = max(rk.values())
        self.fanComb = collections.defaultdict(list); self.fanStor = collections.defaultdict(list)
        for i, g in enumerate(self.comb):
            for x in set(g[2]): self.fanComb[x].append(i)
        for i, g in enumerate(self.stor):
            for x in set(g[2]): self.fanStor[x].append(i)
        b = self.bnd
        self.RST, self.REQ, self.AACK, self.BACK, self.SACK = b["rst"], b["req"], b["a_ack"], b["b_ack"], b["start_ack"]
        self.OREQ, self.OACK, self.PACK = b["out0_req"], b["out0_ack"], b["pend_ack"]
        self.val = [0] * nn
        self._supp = {}

    def ev(self, g):
        a = 0
        for j, x in enumerate(g[2]):
            if self.val[x]: a |= 1 << j
        return (g[3] >> a) & 1

    def evv(self, g, val):
        a = 0
        for j, x in enumerate(g[2]):
            if val[x]: a |= 1 << j
        return (g[3] >> a) & 1

    def settle(self, changed):
        # event-driven by rank; returns list of comb nodes changed
        buckets = collections.defaultdict(set); lo = None
        for n in changed:
            for c in self.fanComb[n]:
                r = self.rank[self.comb[c][0]]; buckets[r].add(c); lo = r if lo is None else min(lo, r)
        if lo is None: return
        for r in range(lo, self.maxRank + 1):
            for c in buckets.pop(r, ()):
                g = self.comb[c]; nv = self.ev(g)
                if nv != self.val[g[0]]:
                    self.val[g[0]] = nv
                    for d in self.fanComb[g[0]]: buckets[self.rank[self.comb[d][0]]].add(d)

    def excited(self, s):
        g = self.stor[s]; return self.ev(g) != self.val[g[0]]

    def supp(self, n):
        """storage/env leaves of node n's comb fan-in (n itself if not a comb output)."""
        if n not in self.combOf: return frozenset([n])
        if n in self._supp: return self._supp[n]
        st = [n]; seen = set(); leaves = set()
        while st:
            x = st.pop()
            if x in seen: continue
            seen.add(x)
            if x in self.combOf: st.extend(self.comb[self.combOf[x]][2])
            else: leaves.add(x)
        r = frozenset(leaves); self._supp[n] = r; return r

    def gsupp(self, s):
        r = set()
        for x in self.stor[s][2]: r |= self.supp(x)
        return r

    def reset(self, a, b):
        val = self.val
        for g in self.comb: val[g[0]] = self.ev(g)
        for i, x in enumerate(self.AD): val[x] = (a >> i) & 1
        for i, x in enumerate(self.BD): val[x] = (b >> i) & 1
        self.settle(self.AD + self.BD)
        val[self.RST] = 1; self.settle([self.RST])
        def stab():
            for it in range(1000000):
                f = -1
                for s in range(len(self.stor)):
                    if self.excited(s): f = s; break
                if f < 0: return True
                o = self.stor[f][0]; val[o] ^= 1; self.settle([o])
            return False
        assert stab()
        val[self.RST] = 0; self.settle([self.RST])
        assert stab()
