"""Auditor: load the BRKH_INT pip timings through prjxray's own API, pass
them through research xray_delay.py's d4()/add4() as its route walk does."""
import importlib.util, sys
from prjxray.db import Database
xd_path, db, part = sys.argv[1:4]
spec = importlib.util.spec_from_file_location("xd", xd_path); xd = importlib.util.module_from_spec(spec)
sys.argv = [xd_path]; spec.loader.exec_module(xd)
d = Database(db, part)
tt = d.get_tile_type("BRKH_INT")
inv = [p for p in tt.get_pips() if p.timing and p.timing.delays and xd.d4(p.timing.delays)[0] > xd.d4(p.timing.delays)[1]]
print("BRKH_INT pips with d4 FAST_MIN > FAST_MAX:", len(inv))
p = inv[0]; a = xd.d4(p.timing.delays); print(p.name, "d4 =", a)
q = next(x for x in d.get_tile_type("INT_L").get_pips() if x.timing and x.timing.delays and x.timing.delays is not None)
b = xd.d4(q.timing.delays); s = xd.add4(xd.add4(b, a), b)
print("INT_L pip", q.name, b); print("route sum INT+BRKH+INT =", s, " fast_min - fast_max = %.3f ns" % (s[0] - s[1]))
