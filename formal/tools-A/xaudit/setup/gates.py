"""gates.py -- the gate graph of Parse.buildDesign, rebuilt in Python (UNTRUSTED helper).

Gate names as Parse: "<cell>/O" for a LUT, "<cell>/I<k>" for the routed arc into pin k.
Bands as Parse with unit 1: lo = max 1 lo, hi = max lo hi (copied from selhold/crosscheck.py).
"""
import json


def steps(b):
    lo = max(1, b[0])
    return lo, max(lo, b[1])


class Gates:
    def __init__(self, skelp, bandp, top="gcd_ctl"):
        sk = json.load(open(skelp))["modules"][top]
        B = json.load(open(bandp))
        dlut = tuple(B.get("lut", [1, 1]))
        droute = tuple(B.get("route", [1, 1]))
        dfb = tuple(B["feedback"]) if B.get("feedback") else droute
        self.band, self.ins, self.outw, self.isbuf = {}, {}, {}, {}
        drv_net = {}
        for cn, c in sk["cells"].items():
            drv_net[c["connections"]["O"][0]] = cn
        for cn, c in sk["cells"].items():
            k = int(c["type"][3])
            o = c["connections"]["O"][0]
            g = f"{cn}/O"
            self.band[g] = steps(tuple(B["cells"].get(cn, dlut)))
            self.isbuf[g] = k == 1 and int(c["parameters"]["INIT"], 2) % 4 == 2
            self.outw[g] = ("net", o)
            gi = []
            for i in range(k):
                bit = c["connections"][f"I{i}"][0]
                if not isinstance(bit, int):
                    gi.append(("const", bit))
                    continue
                r = f"{cn}/I{i}"
                own = drv_net.get(bit) == cn
                self.band[r] = steps(tuple(B["arcs"].get(r, dfb if own else droute)))
                self.isbuf[r] = True
                self.outw[r] = ("pin", cn, i)
                self.ins[r] = [("net", bit)]
                gi.append(("pin", cn, i))
            self.ins[g] = gi
        self.drv = {w: g for g, w in self.outw.items()}

    def lo(self, g):
        return self.band[g][0]

    def hi(self, g):
        return self.band[g][1]

    def plo(self, path):
        return sum(self.lo(g) for g, _ in path)

    def phi(self, path):
        return sum(self.hi(g) for g, _ in path)

    def buf_down(self, gate, stop):
        """Follow input 0 of 1-input buffer gates from `gate` until a gate in `stop` is reached.
        Returns (path, stop gate) with path = [[gate, 0], ...] from `gate`'s output wire down to
        the stop gate's output wire ([] if gate in stop), or None."""
        path, g = [], gate
        for _ in range(10000):
            if g in stop:
                return path, g
            if not self.isbuf.get(g) or len(self.ins.get(g, [])) != 1:
                return None
            w = self.ins[g][0]
            path.append([g, 0])
            g = self.drv.get(w)
            if g is None:
                return None
        return None
