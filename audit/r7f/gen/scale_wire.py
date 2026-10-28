"""Auditor probe: is GLS_SCALE_INST applied to INTERCONNECT arcs under
GLS_SCATTER_MODE=wire?  Imports the research gen.py (path argv[1]) with env
set before import, stubs the wire model to factor 1.0 (exact sigma-0-like pip
factors) so any change can only come from GLS_SCALE_INST."""
import importlib.util, os, sys
def load(env):
    for k in ("GLS_SCALE_INST","GLS_SCATTER","GLS_SCATTER_MODE","GLS_DELAY_SCALE"):
        os.environ.pop(k, None)
    os.environ.update(env)
    spec = importlib.util.spec_from_file_location("gen_%d" % len(env), sys.argv[1])
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
class Stub:
    def factor(self, dst): return 1.0
for label, env in [("arc mode", {"GLS_SCALE_INST":"uut.x:3","GLS_SCATTER":"0.05","GLS_SCATTER_MODE":"arc"}),
                   ("no scatter", {"GLS_SCALE_INST":"uut.x:3"}),
                   ("wire mode", {"GLS_SCALE_INST":"uut.x:3","GLS_SCATTER":"0.05","GLS_SCATTER_MODE":"wire"})]:
    g = load(env); g._wire = Stub()
    ic = g.perturb_ic(1000, "uut.y/O", "uut.x/I0")
    cell = g.perturb(1000, "uut.x")
    print("%-10s interconnect into uut.x: 1000 -> %5d   cell arc of uut.x: 1000 -> %5d   n_scaled_inst=%d"
          % (label, ic, cell, g.n_scaled_inst))
