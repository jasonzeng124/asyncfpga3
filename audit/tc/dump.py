import sys; sys.path.insert(0, '/home/user/asyncfpga3/audit/tc')
import xrc
def dump(R, cn, port):
    n, s = R.sink_of_cellpin(cn, port)
    print(cn, port, 'outs', [(o[0], o[1]) for o in n.outs], 'sink', s and (s['pin'], s['tilewire']))
    if not s: return
    for i in s['path']:
        e = n.elems[i]; k = e['kind']
        if k == 'wire': print('  wire', sorted(e['node'])[:3], 'R%.0f C%.1f dcap%.1f rc=%.0f' % (e['r'], e['c'], e['dcap'], e['r']*e['dcap']*xrc.RCU))
        elif k in ('buf', 'pt'): print(' ', k, e['name'], 'd', [round(x) for x in e['d']], 'R%.0f dcap%.1f rc=%.0f' % (e['res'], e['dcap'], e['res']*e['dcap']*xrc.RCU))
        else: print('  in', e['pin'], [round(x) for x in e['d']], 'cap', e['cap'])
    print('  total', [round(x) for x in s['d']])
if __name__ == '__main__':
    R = xrc.Route(sys.argv[1])
    for a in sys.argv[2:]:
        cn, p = a.rsplit(':', 1); dump(R, cn, p)
