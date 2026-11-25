#!/usr/bin/env python3
"""Shard C helper (UNTRUSTED): separations along the certificate's causes.
Sep(e0 -> T): longest path from e0 to T along causes, edge p -> e weighted lo'(node e, node p) (TimedOcc.SepOK's
justification; own previous event: lo of the feedback pin if the node reads itself, else 1; env events: 1).
Up(e0 -> T): upper bound on tau(T) - tau(e0): max over causes p of e of (Up(p) + hi'(e, p)), where a cause p that
precedes e0 (p <= e0 causally) counts as tau(p) <= tau(e0); a cause concurrent with e0, or an env event on the
path, makes Up infinite.  (Sound only given that every gate event fires as soon as all its certificate causes have
been read, i.e. assuming the certificate is followed: an untrusted, inductive use.)"""
import numpy as np
INF = float("inf")

class Tm:
    def __init__(self, K):
        self.K = K; el = K["elist"]; xi = K["xi"]
        self.enode = np.array([xi[n] for (n, k, t) in el], dtype=np.int32)
        self.ek = np.array([k for (n, k, t) in el], dtype=np.int32)
        self.et = np.array([t for (n, k, t) in el], dtype=np.int64)
        self.VC = K["VC"]; self.eid = K["eid"]; self.el = el
        self.Kxs = sorted(K["C"]["EXACT"])
        self.reads_self = {}
        C = K["C"]
        for v in C["EXACT"]:
            self.reads_self[v] = (v, v) in K["dl"]
        self.cz = {}
        for (n, k), cs in K["causes"].items():
            self.cz[K["eid"][(n, k)]] = [K["eid"][p] for p in cs]

    def wlo(self, e, p):
        n = self.el[e][0]; w = self.el[p][0]; K = self.K
        if n in K["envnode"]: return 1
        if n == w: return K["dl"][(n, n)][0] if self.reads_self[n] else 1
        return K["dl"][(n, w)][0]

    def whi(self, e, p):
        n = self.el[e][0]; w = self.el[p][0]; K = self.K
        if n in K["envnode"]: return INF
        if n == w: return K["dl"][(n, n)][1] if self.reads_self[n] else 1
        return K["dl"][(n, w)][1]

    def leq(self, a, b):
        """event a <= event b causally (a ancestor of or equal to b)"""
        return self.VC[b, self.enode[a]] > self.ek[a]

    def path_set(self, e0, T):
        an = self.VC[T][self.enode] > self.ek          # ancestors of T (incl. T)
        de = self.VC[:, self.enode[e0]] > self.ek[e0]   # descendants of e0 (incl. e0)
        idx = np.nonzero(an & de)[0]
        return idx[np.argsort(self.et[idx], kind="stable")], de

    def sep_up(self, e0, T, want_up=True):
        if not self.leq(e0, T): return None, None
        idx, de = self.path_set(e0, T)
        S = {}; U = {}
        for e in idx:
            e = int(e)
            if e == e0: S[e] = 0; U[e] = 0; continue
            s = None; u = 0
            for p in self.cz[e]:
                if p in S:
                    x = S[p] + self.wlo(e, p)
                    if s is None or x > s: s = x
                    if want_up: u = max(u, U[p] + self.whi(e, p))
                elif want_up:
                    if self.leq(p, e0): u = max(u, self.whi(e, p))
                    else: u = INF
            S[e] = s if s is not None else 0; U[e] = u
        return S.get(T), U.get(T)

    def sep(self, e0, T):
        return self.sep_up(e0, T, want_up=False)[0]

    def best_order(self, U, W, ncand=8):
        """lower bound on tau(W) - tau(U) for concurrent U, W: max over recent common ancestors e0 of
        Sep(e0 -> W) - Up(e0 -> U).  Returns (bound, e0)."""
        m = np.minimum(self.VC[U], self.VC[W])
        xs = np.nonzero(m)[0]
        evs = []
        for x in xs:
            node = self.Kxs[x]
            e0 = self.eid[(node, int(m[x]) - 1)]
            evs.append((self.et[e0], e0))
        evs.sort(reverse=True)
        best = (-INF, None)
        for _, e0 in evs[:ncand]:
            s, _u = self.sep_up(e0, W, want_up=False)
            if s is None: continue
            _s, u = self.sep_up(e0, U)
            if u is None or u == INF: continue
            if s - u > best[0]: best = (s - u, e0)
        return best
