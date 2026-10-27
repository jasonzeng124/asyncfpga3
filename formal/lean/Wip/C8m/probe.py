import os, sys
HERE=os.path.dirname(os.path.abspath(__file__))
ROOT=os.path.abspath(os.path.join(HERE,"..","..","..",".."))
sys.path.insert(0, os.path.join(ROOT,"formal","tools","dfimport"))
for k in ["BDC_OP_FUSION","BDC_CONST_FOLD","BDC_FORK_FUSION","BDC_MAX_FUSE_NODES","BDC_PROBE","BDC_RING_PAD","BDC_LINK_FASTFALL","BDC_SELECT_PAD"]:
    os.environ.pop(k,None)
import mlir2lean
g=mlir2lean.Graph(mlir2lean.default_mlir())
ctl=[c for c,v in enumerate(g.chname) if g.is_ctl(v)]
print("N",g.N,"ctl",len(ctl))
print(ctl)
print(g.rules[:3])
