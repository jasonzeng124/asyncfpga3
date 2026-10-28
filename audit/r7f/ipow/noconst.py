"""Auditor: run research tighten.py (path argv[1]) on SDF argv[2] with
cell_boundary() wrapped to drop $PACKER_GND_DRV/$PACKER_VCC_DRV sources --
the one-line fix the formal finding proposes.  Everything else is tighten's own code."""
import importlib.util, sys, os
tpath, sdf = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
sys.argv = [tpath, sdf]
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(tpath))))
spec = importlib.util.spec_from_file_location("tighten", tpath)
t = importlib.util.module_from_spec(spec); spec.loader.exec_module(t)
orig = t.cell_boundary
dropped = []
def cb(edges, back, stops, parent):
    s = orig(edges, back, stops, parent)
    c = {p for p in s if t.is_const(p)}
    if c: dropped.append((parent if isinstance(parent, str) else parent[0], sorted(c)))
    return s - c
t.cell_boundary = cb
rc = t.main()
print("NOCONST: cell_boundary calls that contained a tie-off source:", len(dropped))
print("NOCONST rc", rc)
