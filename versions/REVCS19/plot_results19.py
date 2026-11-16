"""رسم خروجی‌های واقعی نسخهٔ ۱۸؛ دادهٔ مقاله یا جواب بهینه در این فایل درج نشده است."""
from pathlib import Path
import argparse
import csv
from collections import defaultdict
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

parser=argparse.ArgumentParser()
parser.add_argument('directory',type=Path)
args=parser.parse_args()
folder=args.directory

def rows(name):
    path=folder/name
    if not path.exists() or not path.stat().st_size:
        return []
    with path.open() as handle:
        return list(csv.DictReader(handle))

conv=rows('convergence.csv')
if conv:
    fig,ax=plt.subplots(figsize=(8,4))
    for key in ('lower','upper'):
        pairs=[(int(r['iteration']),float(r[key])) for r in conv if math.isfinite(float(r[key]))]
        if pairs:
            ax.plot(*zip(*pairs),marker='o',label=key)
    ax.set(xlabel='RDDP iteration',ylabel='Discounted horizon cost',title='Computed bounds; finite values only')
    ax.legend();fig.tight_layout();fig.savefig(folder/'convergence.png',dpi=180);plt.close(fig)

capacity=rows('forward_capacities.csv')
if capacity:
    stages=sorted({int(r['stage']) for r in capacity})
    fig,axes=plt.subplots(len(stages),3,figsize=(14,3*len(stages)),squeeze=False)
    for i,t in enumerate(stages):
        rs=sorted((r for r in capacity if int(r['stage'])==t),key=lambda r:int(r['road']))
        for j,(key,label) in enumerate((('charging_kw','Charging (kW)'),('storage_kwh','Battery energy (kWh)'),('pv_kw','Onsite PV (kW)'))):
            ax=axes[i,j];ax.bar([int(r['road']) for r in rs],[float(r[key]) for r in rs])
            ax.set(xlabel='Road',ylabel=label,title=f'Forward sample, stage {t}')
    fig.tight_layout();fig.savefig(folder/'computed_capacities.png',dpi=180);plt.close(fig)

dispatch=rows('forward_dispatch.csv')
if dispatch:
    totals=defaultdict(lambda:defaultdict(float))
    for r in dispatch:
        key=r['variable'];idx=r['index'].split(':')
        if key in ('Pb_u','Pwt','Ppv_pdn','Pcs','Rv','Pe_Ec','Pe_Ed','Pn'):
            totals[(int(r['stage']),key)][int(idx[-1])]+=float(r['value'])
    stages=sorted({t for t,_ in totals})
    fig,axes=plt.subplots(len(stages),1,figsize=(12,3.5*len(stages)),squeeze=False)
    for i,t in enumerate(stages):
        ax=axes[i,0]
        for key in ('Pb_u','Pwt','Ppv_pdn','Pcs','Rv','Pe_Ec','Pe_Ed'):
            series=totals.get((t,key),{})
            if series: ax.plot(sorted(series),[series[h] for h in sorted(series)],label=key)
        ax.set(xlabel='Typical operating hour',ylabel='kW',title=f'Computed forward dispatch, stage {t}')
        ax.legend(ncol=4)
    fig.tight_layout();fig.savefig(folder/'computed_dispatch.png',dpi=180);plt.close(fig)

evaluations=rows('policy_evaluation.csv')
costs=[float(r['cost']) for r in evaluations if r['complete'].lower()=='true' and math.isfinite(float(r['cost']))]
if costs:
    fig,ax=plt.subplots(figsize=(7,4))
    ax.hist(costs,bins='auto');ax.set(xlabel='Discounted realized cost',ylabel='Completed paths',
        title=f'User-supplied evaluation paths: {len(costs)}/{len(evaluations)} completed')
    fig.tight_layout();fig.savefig(folder/'evaluation_costs.png',dpi=180);plt.close(fig)
print('Plots written only for available computed records in',folder)
