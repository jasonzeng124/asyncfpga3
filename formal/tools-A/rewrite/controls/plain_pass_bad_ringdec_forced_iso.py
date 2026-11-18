import sys, subprocess, shutil
sys.path.insert(0, '/home/user/asyncfpga3/formal/tools-A/rewrite')
import plain_pass as PP
orig_run = subprocess.run
class R:  # a fake "accepted" rules_iso result
    returncode = 0; stdout = 'ISOMORPHIC (forced)'; stderr = ''
def run(cmd, *a, **k):
    if isinstance(cmd, list) and any(str(c).endswith('rules_iso.py') for c in cmd):
        shutil.copyfile('/tmp/claude-0/pp/census/countloop/maps.json', cmd[4]); return R()
    r = orig_run(cmd, *a, **k)
    if isinstance(cmd, list) and any(str(c).endswith('ring_dec.py') for c in cmd):
        out = cmd[3]; s = open(out).read()
        open(out, 'w').write(s.replace('value = -1 : i32', 'value = -2 : i32', 1))
    return r
PP.subprocess.run = run
sys.argv = ['plain_pass.py', '/tmp/claude-0/pp/countloop.mlir', '/tmp/claude-0/pp/cl_badrd2_out.mlir', '--keep', '/tmp/claude-0/pp/cl_badrd2']
sys.exit(PP.main())
