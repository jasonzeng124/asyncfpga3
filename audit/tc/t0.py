import sys, time; sys.path.insert(0, '/home/user/asyncfpga3/audit/tc')
import xrc
t=time.time(); R=xrc.Route(sys.argv[1]); print('load', time.time()-t)
cn='urig.udut.ucontrol_merge6.uarb1.ua2.u'
for p in ('A1','A2','A3','A4','A5','A6'):
    if p in R.cells[cn]['connections']:
        n,s=R.sink_of_cellpin(cn,p); b=R.cells[cn]['connections'][p][0]; dc,dp=R.driver[b]
        print(p, dc, dp, R.ic.get((f'{dc}/{dp}', f'{cn}/{p}')), s and (s['pin'], s['sitewire'], [round(x) for x in s['d']], [round(x) for x in s['sitepin']]), n and n.why, R.lut_arc(cn,p))
