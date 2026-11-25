"""Build the standalone Gate 7.4.2 download and verify all member bytes."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

root = Path(__file__).resolve().parents[1] / "versions/G742_FIX20"
target = root / "REVCS19_FIX20_complete.zip"
sums = root / "SHA256SUMS.txt"
sources = sorted(
    path for path in root.rglob("*")
    if path.is_file() and path not in (target, sums) and path.name != "fix20-tests.log"
)
hashes = {p.relative_to(root).as_posix(): sha256(p.read_bytes()).hexdigest() for p in sources}
ledger = (root.parents[1] / "REUSE.md").read_bytes()
ledger_hash = sha256(ledger).hexdigest()
manifest = "".join(f"{digest}  {name}\n" for name, digest in hashes.items())
with ZipFile(target, "w") as package:
    for path in sources:
        name = path.relative_to(root).as_posix()
        entry = ZipInfo("REVCS19_FIX20/" + name, (2026, 1, 1, 0, 0, 0))
        entry.compress_type = ZIP_DEFLATED
        entry.external_attr = 0o100644 << 16
        package.writestr(entry, path.read_bytes())
    entry = ZipInfo("REVCS19_FIX20/REUSE.md", (2026, 1, 1, 0, 0, 0))
    entry.compress_type = ZIP_DEFLATED
    entry.external_attr = 0o100644 << 16
    package.writestr(entry, ledger)
    entry = ZipInfo("REVCS19_FIX20/SHA256SUMS.txt", (2026, 1, 1, 0, 0, 0))
    entry.compress_type = ZIP_DEFLATED
    entry.external_attr = 0o100644 << 16
    package.writestr(entry, manifest + f"{ledger_hash}  REUSE.md\n")
with ZipFile(target) as package:
    assert package.testzip() is None
    assert package.read("REVCS19_FIX20/REUSE.md") == ledger
    for name, digest in hashes.items():
        assert sha256(package.read("REVCS19_FIX20/" + name)).hexdigest() == digest
sums.write_bytes((manifest + f"{sha256(target.read_bytes()).hexdigest()}  {target.name}\n").encode())
