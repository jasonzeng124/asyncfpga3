"""netlib.py -- shared netlist helpers for the events4 control-skeleton analysis (UNTRUSTED).

Reads routed2x.py's xaudit netlist (yosys JSON, every cell a LUTk over its USED
physical pins, INIT re-encoded to that pin order) and its band file (ps).
"""
import itertools
import json


class Net:
    def __init__(self, net_path, bands_path=None, top="gcd_ctl"):
        d = json.load(open(net_path))
        m = d["modules"][top]
        self.cells = {}
        self.drv = {}
        self.readers = {}
        self.ports = m["ports"]
        for cn, c in m["cells"].items():
            k = int(c["type"][3])
            ins = [c["connections"][f"I{i}"][0] for i in range(k)]
            out = c["connections"]["O"][0]
            init = int(c["parameters"]["INIT"], 2)
            self.cells[cn] = dict(k=k, ins=ins, out=out, init=init)
            self.drv[out] = cn
            for i, b in enumerate(ins):
                if isinstance(b, int):
                    self.readers.setdefault(b, []).append((cn, i))
        self.rst = self.ports["rig_rst"]["bits"][0]
        self.inputs = {p["bits"][0]: n for n, p in self.ports.items() if p["direction"] == "input"}
        self.cellband = {}
        self.arc = {}
        if bands_path:
            b = json.load(open(bands_path))
            self.cellband = {k: tuple(v) for k, v in b["cells"].items()}
            self.arc = {k: tuple(v) for k, v in b["arcs"].items()}

    def f(self, cn, bits):
        """LUT function at pin values `bits` (list of 0/1, physical order)."""
        a = sum(b << i for i, b in enumerate(bits))
        return (self.cells[cn]["init"] >> a) & 1

    def arcband(self, cn, i):
        return self.arc.get(f"{cn}/I{i}")

    def lutband(self, cn):
        return self.cellband.get(cn)


def cel_spec(vals, roles, v):
    """C-element spec. roles[i] in ('r', 'q', 'p+', 'p-', ('f', ctlpin_pol, selpattern...)).
    vals: dict pin->0/1."""
    raise NotImplementedError
