"""Build a reproducible source ZIP from the committed tree, with provenance."""
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

root = Path(__file__).resolve().parents[1]
def git(*args):
    return subprocess.check_output(['git', '-C', str(root), *args])

sha = git('rev-parse', 'HEAD').decode().strip()
paths = git('ls-tree', '-rz', '--name-only', 'HEAD').decode().split('\0')
files = [(p, git('show', f'HEAD:{p}')) for p in paths if p]
manifest = ''.join(hashlib.sha256(data).hexdigest() + '  ' + p + '\n' for p, data in files)
info = json.dumps({'commit': sha, 'package': 'REVCS',
                   'scientific_reproduction_certified': False,
                   'validation': 'See separate GitHub Actions validation job and artifact'}, indent=2)+'\n'
files += [('PACKAGE_SHA256SUMS.txt', manifest.encode()), ('BUILD_INFO.json', info.encode())]
dist = root/'dist'
dist.mkdir(exist_ok=True)
target = dist/f'REVCS-{sha[:12]}.zip'
with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED) as archive:
    for name, data in files:
        item = zipfile.ZipInfo('REVCS/'+name, date_time=(2026, 1, 1, 0, 0, 0))
        item.compress_type = zipfile.ZIP_DEFLATED
        item.external_attr = 0o100644 << 16
        archive.writestr(item, data)
with zipfile.ZipFile(target) as archive:
    assert archive.testzip() is None
print(target)
