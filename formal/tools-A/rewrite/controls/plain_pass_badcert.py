import sys
sys.path.insert(0, '/home/user/asyncfpga3/formal/tools-A/rewrite')
import gen_plain_gen as G, plain_pass as PP
orig = G.analyse
def bad(*a, **k):
    A = orig(*a, **k); A['cert']['c2'] = []; return A
G.analyse = bad
sys.argv = ['plain_pass.py', '/tmp/claude-0/pp/countloop.mlir', '/tmp/claude-0/pp/cl_bad_out.mlir', '--keep', '/tmp/claude-0/pp/cl_bad']
sys.exit(PP.main())
