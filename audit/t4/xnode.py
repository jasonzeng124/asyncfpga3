#!/usr/bin/env python3
"""xnode.py (audit T4): independent prjxray node resolution and site helpers.

Written by the auditor; does NOT import any formal/ code. Uses only prjxray-db JSON
(tilegrid.json, tileconn.json, tile_type_*.json, ppips_*.db, segbits_*.db names).

Node of (tile, wire): BFS over tileconn wire pairs in BOTH directions (prjxray
connections.py lists them one way). Node name convention for comparing with the
formal decoder's net.json: "tile/wire" of the lexicographically smallest (tile, wire).
"""
import json
import os
from collections import defaultdict

DB = os.environ.get("XDB", "/root/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7")


class XDB:
    def __init__(self):
        self.grid = json.load(open(os.path.join(DB, "xc7z010", "tilegrid.json")))
        self.pos = {}
        for t, g in self.grid.items():
            self.pos[(g["grid_x"], g["grid_y"])] = t
        self.conn = defaultdict(list)   # (ttype, wire) -> [(dx, dy, ttype2, wire2)]
        for c in json.load(open(os.path.join(DB, "xc7z010", "tileconn.json"))):
            (dx, dy), (ta, tb) = c["grid_deltas"], c["tile_types"]
            for wa, wb in c["wire_pairs"]:
                self.conn[(ta, wa)].append((dx, dy, tb, wb))
                self.conn[(tb, wb)].append((-dx, -dy, ta, wa))
        self._tt = {}
        self._node = {}
        self.site_tile = {}
        for t, g in self.grid.items():
            for s, st in g.get("sites", {}).items():
                self.site_tile[s] = (t, st)
        self._pp = {}

    def ttype(self, tile):
        return self.grid[tile]["type"]

    def tt(self, ttype):
        if ttype not in self._tt:
            p = os.path.join(DB, "tile_type_%s.json" % ttype)
            j = json.load(open(p)) if os.path.exists(p) else {"pips": {}, "sites": [], "wires": {}}
            j["_pip"] = {}
            for k, p in j["pips"].items():
                j["_pip"][(p["dst_wire"], p["src_wire"])] = (p, False)
            for k, p in j["pips"].items():
                if str(p.get("is_directional")) == "0":
                    j["_pip"].setdefault((p["src_wire"], p["dst_wire"]), (p, True))
            self._tt[ttype] = j
        return self._tt[ttype]

    def ppips(self, ttype):
        """{(dst, src): kind} from ppips_<ttype>.db (always / default / hint)."""
        if ttype not in self._pp:
            d = {}
            p = os.path.join(DB, "ppips_%s.db" % ttype.lower())
            if os.path.exists(p):
                for line in open(p):
                    f = line.split()
                    if len(f) == 2:
                        _, dst, src = f[0].split(".", 2)
                        d[(dst, src)] = f[1]
            self._pp[ttype] = d
        return self._pp[ttype]

    def node(self, tile, wire):
        k = (tile, wire)
        if k in self._node:
            return self._node[k]
        seen = {k}
        todo = [k]
        while todo:
            t, w = todo.pop()
            g = self.grid[t]
            for dx, dy, tb, wb in self.conn.get((g["type"], w), ()):
                t2 = self.pos.get((g["grid_x"] + dx, g["grid_y"] + dy))
                if t2 is None or self.grid[t2]["type"] != tb:
                    continue
                if (t2, wb) not in seen:
                    seen.add((t2, wb))
                    todo.append((t2, wb))
        fs = frozenset(seen)
        for x in seen:
            self._node[x] = fs
        return fs

    def nname(self, tile, wire):
        t, w = min(self.node(tile, wire))
        return "%s/%s" % (t, w)

    def slice_prefix(self, site):
        """'SLICE_X10Y67' -> ('CLBLL_L_X8Y67', 'SLICEL_X0', tile-type site dict). X0 = the slice
        with the smaller global X in its tile (prjxray FASM convention)."""
        tile, st = self.site_tile[site]
        sl = sorted((s for s, ty in self.grid[tile]["sites"].items() if ty.startswith("SLICE")),
                    key=lambda s: int(s.split("X")[1].split("Y")[0]))
        x = sl.index(site)
        tts = [s for s in self.tt(self.ttype(tile))["sites"] if s["type"].startswith("SLICE") and s["x_coord"] == x]
        assert len(tts) == 1 and tts[0]["type"] == st, (site, tile, st, tts)
        return tile, "%s_X%d" % (st, x), tts[0]
