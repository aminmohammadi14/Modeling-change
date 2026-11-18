"""ساخت فایل اجرایی خودکفا از کد و داده‌های مستند؛ فقط ابزار توسعه است."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parents[1]
base = root / 'versions/REBUILD_S01'
source = (base / 'run_step01.jl').read_text()
source = source[:source.index('# ورود از خط فرمان')]
source = source.replace('module REVCSDataStep01', 'module REVCSStandaloneS01')
embedded = '\n# بخش دادهٔ مستند: متن TOML عیناً از ورودی ممیزی‌شده منتقل شده است.\n'
embedded += '# این اعداد پارامترهای ورودی‌اند، نه نتیجهٔ تحمیلی یا مقدار حدسی در منطق مدل.\n'
for name in ['tables','case','sources']:
    text = (base / 'data' / (name+'.toml')).read_text()
    assert '"""' not in text
    embedded += f'const DATA_{name.upper()} = raw"""\n{text}"""\n'
    embedded += f'const HASH_{name.upper()} = "{hashlib.sha256(text.encode()).hexdigest()}"\n\n'
source = source.replace('export load_case, profiles, require_optimization_ready\n',
                        'export load_case, profiles, require_optimization_ready\n'+embedded)
a = source.index('function verify_checksums(root)')
b = source.index('# کنترل شکل جدول',a)
source = source[:a]+'''function verify_checksums(root)
    # ورودی‌ها در همین فایل‌اند؛ هیچ پوشهٔ data یا فایل همراه خوانده نمی‌شود.
    for (name, payload, expected) in (("tables", DATA_TABLES, HASH_TABLES),
                                     ("case", DATA_CASE, HASH_CASE),
                                     ("sources", DATA_SOURCES, HASH_SOURCES))
        demand(bytes2hex(sha256(payload)) == expected, "دادهٔ درون فایل تغییر کرده است: $name")
    end
end

'''+source[b:]
for name in ['tables','case','sources']:
    source = source.replace(f'TOML.parsefile(joinpath(root,"data","{name}.toml"))',
                            f'TOML.parse(DATA_{name.upper()})')
source = source.replace('خواننده مستقل از نسخهٔ ۱۹ است و از هیچ آرایهٔ جاسازی‌شده در کد قدیمی استفاده نمی‌کند.',
                        'خوانندهٔ دادهٔ مستند همین فایل؛ هیچ داده‌ای از کد نسخهٔ ۱۹ خوانده نمی‌شود.')
header = '''# REVCS S01 — فایل یکپارچهٔ اجرایی | CHG-0006
# فقط همین فایل را ذخیره و اجرا کنید؛ فایل داده یا فایل آزمون جدا لازم نیست.
# PowerShell: julia revcs_step01_integrated.jl
# Julia REPL: include(raw"E:\\112\\revcs_step01_integrated.jl")
# فقط کتابخانه‌های استاندارد Julia استفاده می‌شوند؛ نصب حل‌گر لازم نیست.
# خروجی: پوشهٔ results_S01 کنار همین فایل؛ چهار نمودار ورودی و گزارش اعتبارسنجی.
# مرز کار: این گام فقط بررسی داده است؛ مدل بهینه‌سازی و نتایج مقاله هنوز تولید نشده‌اند.
# پارامترها در بخش DATA از منطق برنامه جدا هستند؛ موارد نامشخص در readiness باقی‌اند.

'''
# ابهام‌های مدل در خود فایل نیز قابل خواندن‌اند؛ گزارش بیرونی برای اجرا لازم نیست.
notes = (base / 'ISSUES_FA.md').read_text()
assert '=#' not in notes
footer = '''
# اجرای مستقیم هم در PowerShell و هم با include در Julia.
# این فراخوانی در سطح بالاست تا مشکل world age در Julia جدید ایجاد نشود.
REVCSStandaloneS01.run(@__DIR__, joinpath(@__DIR__, "results_S01"))
println("مسیر خروجی: ", joinpath(@__DIR__, "results_S01"))
'''
target = base / 'revcs_step01_integrated.jl'
target.write_text(header+'#=\n'+notes+'\n=#\n\n'+source+footer)
print(target)
