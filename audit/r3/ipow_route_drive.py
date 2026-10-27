# route ipow T9 (BD_DSP=1) seed 29 with flow.sh only (no sims), mirroring fusion_bench.measure_kernel's env
import os, sys, shutil, subprocess
from pathlib import Path
R = Path("/home/user/wt-r3"); sys.path.insert(0, str(R / "bdc"))
import fusion_bench as fb
from fusion_bench import emit, parse
out = Path("/home/user/wt-r3/build/r3_ipow"); p = out / "input.mlir"
shutil.copy2(R / "build/frontend/ipow/comp/handshake_transformed.mlir", p)
name = parse.parse_module(p.read_text())[0].name
(out / "top.v").write_text(emit.generate(str(p))[0])
env = os.environ.copy(); env.pop("BD_NO_TIGHTEN", None)
env.update(BD_TOP_V=str(out / "top.v"), BD_TOP_M=f"bdc_{name}_top", BD_SIZES=str(R / "research/data/ipow_dsp1_sizes_T9.vh"),
           BD_OUT=str(out / "seed29/pnr"), NEXTPNR_SEED="29", BD_DSP="1")
(out / "seed29").mkdir(exist_ok=True)
r = subprocess.run([str(fb.CELLS / "flow.sh")], env=env, stdout=open(out / "seed29/route.log", "w"), stderr=subprocess.STDOUT)
print("flow.sh rc", r.returncode)
