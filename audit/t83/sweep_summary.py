# T86: summarise a monitor log: final report's minima per kind, violations, oracle
import re, sys, subprocess
for f, k, o in [a.split(':') for a in sys.argv[1:]]:
    L = open(f).read().splitlines()
    end = [l for l in L if re.search(r't=\d+ DONE', l)]
    tl = max((int(m[1]) for l in L for m in [re.match(r'(?:STEERMON|MUXMON|LATCHMON) t=(\d+) ', l)] if m), default=0)
    last = [l for l in L if re.match(rf'(STEERMON|MUXMON|LATCHMON) t={tl} ', l)]
    def mins(tag, key):
        v = [(int(re.search(key + r'=(\d+)', l)[1]), l.split()[2]) for l in last if l.startswith(tag)]
        return min(v) if v else None
    viol = sum(1 for l in L if 'VIOLATION' in l)
    orc = subprocess.run([sys.executable, '-I', f'/home/user/asyncfpga3/audit/t65/oracle_{o}.py', 'check', f'/home/user/asyncfpga3/audit/t65/{k}', f, '2'], capture_output=True, text=True).stdout.strip().splitlines()
    orc = [x for x in orc if 'agreement' in x]
    e = re.search(r't=(\d+) DONE', end[-1])[1] if end else '?'
    print(f"{f.split('/')[-1]}: end {e} last report {tl}; "
          f"steer min {mins('STEERMON', 'min_rise_margin_ps')}; mux min {mins('MUXMON', 'min_sel_to_zreq_ps')}; "
          f"latch min setup {mins('LATCHMON', 'min_setup_ps')}; violation lines {viol}; {orc[0] if orc else 'no oracle'}")
