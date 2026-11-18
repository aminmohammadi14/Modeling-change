"""مقایسهٔ ایستای آرایه‌های عددی؛ کد ارسالی اجرا یا حل نمی‌شود."""
from pathlib import Path
import re, tomllib, json, hashlib
base=Path(__file__).resolve().parent
s=(base/'CODE_REFERENCE_received.jl').read_text()
d=tomllib.loads((base.parents[1]/'versions/REBUILD_S01/data/tables.toml').read_text())
checks=[]
for name,n,skip in [('wt_pu_days',3,1),('pv_pu_days',5,1),('Df_initial',2,1),('Load_P_days',8,1),('PDN_lines_data',11,0)]:
 m=re.search(r'^'+name+r'\s*=\s*\[(.*?)\]',s,re.M|re.S)
 rows=[[float(x) for x in r.split()] for r in re.sub(r'#.*','',m[1]).strip().split(';') if r.strip()]
 expected=[r[skip:] for r in d['table'+str(n)]['rows']]
 checks.append(dict(array=name,table=n,cells=sum(map(len,rows)),match=rows==expected))
for name,n,col in [('phi_b',1,1),('h0_b',1,2),('wt_capacities',4,2),('pv_pdn_capacities',6,2)]:
 m=re.search(r'^'+name+r'\s*=\s*\[(.*?)\]',s,re.M|re.S)
 vals=[float(x) for x in m[1].replace(',',' ').split()]
 checks.append(dict(array=name,table=n,cells=len(vals),match=vals==[r[col] for r in d['table'+str(n)]['rows']]))
result=dict(source_sha256=hashlib.sha256((base/'CODE_REFERENCE_received.jl').read_bytes()).hexdigest(),checks=checks,total_cells=sum(c['cells'] for c in checks),solver_run=False)
(base/'data_comparison.json').write_text(json.dumps(result,indent=2)+'\n')
assert all(c['match'] for c in checks)
print('All',result['total_cells'],'numeric entries in nine arrays match the sourced tables.')
