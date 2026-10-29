import sys, os, types, importlib.util, shutil
spec = importlib.util.spec_from_file_location("s", sys.argv[1]); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
m.sh = lambda *a, **k: 0
for hw, logs, tag in zip(sys.argv[2::3], sys.argv[3::3], sys.argv[4::3]):
    out = "/root/r7work/apply_" + tag; shutil.rmtree(out, ignore_errors=True)
    os.makedirs(out + "/x/" + tag); os.symlink(logs, out + "/x/" + tag + "/sweep")
    print(tag, end=" "); m.sim(types.SimpleNamespace(out=out), "x", hw, tag, None)
