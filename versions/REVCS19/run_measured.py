"""Run a Julia entry point and record measured process resources (Linux)."""
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

root=Path(__file__).resolve().parent
entry=Path(sys.argv[1])
if not entry.is_absolute():
    entry=root/entry
stem=entry.stem+('_'+sys.argv[2] if len(sys.argv)>2 else '')
julia=os.environ.get('JULIA_BIN','julia')
start=time.monotonic()
with (root/(stem+'.log')).open('w') as log:
    result=subprocess.run([julia,'--project='+str(root),str(entry),*sys.argv[2:]],stdout=log,stderr=subprocess.STDOUT)
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
report=dict(entry=entry.name,args=sys.argv[2:],exit_code=result.returncode,
    wall_seconds=time.monotonic()-start,user_cpu_seconds=usage.ru_utime,
    system_cpu_seconds=usage.ru_stime,maximum_process_rss_bytes=usage.ru_maxrss*1024,
    memory_measurement='Linux ru_maxrss: entire child process including Julia/JIT/solver',
    soc_min=os.environ.get('REVCS_SOC_MIN','0.1'),soc_initial=os.environ.get('REVCS_SOC_INITIAL','0.5'),
    soc_max=os.environ.get('REVCS_SOC_MAX','0.9'),cycle=os.environ.get('REVCS_BATTERY_CYCLE','daily_cyclic'))
(root/(stem+'_resources.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
raise SystemExit(result.returncode)
