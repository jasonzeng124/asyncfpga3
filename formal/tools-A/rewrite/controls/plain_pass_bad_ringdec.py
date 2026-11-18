import sys, subprocess
sys.path.insert(0, '/home/user/asyncfpga3/formal/tools-A/rewrite')
import plain_pass as PP
orig_run = subprocess.run
def run(cmd, *a, **k):
    r = orig_run(cmd, *a, **k)
    if isinstance(cmd, list) and any(str(c).endswith('ring_dec.py') for c in cmd):
        out = cmd[3]; s = open(out).read()
        assert 'value = -1 : i32' in s
        open(out, 'w').write(s.replace('value = -1 : i32', 'value = -2 : i32', 1))
    return r
PP.subprocess.run = run
sys.argv = ['plain_pass.py', '/tmp/claude-0/pp/countloop.mlir', '/tmp/claude-0/pp/cl_badrd_out.mlir', '--keep', '/tmp/claude-0/pp/cl_badrd']
sys.exit(PP.main())
