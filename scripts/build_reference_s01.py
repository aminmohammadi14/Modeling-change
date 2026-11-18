"""بازنویسی گام اول بر پایهٔ آرایه‌های فایل ارسالی، بدون اجرای مدل قدیمی."""
from pathlib import Path
import re, json, hashlib, tomllib
root=Path(__file__).resolve().parents[1]
old=root/'reports/CHG-0007/CODE_REFERENCE_received.jl'
text=old.read_text(); prev=root/'versions/REBUILD_S01'
data=tomllib.loads((prev/'data/tables.toml').read_text())
# نام و متن آرایه‌های درستِ فایل کاربر حفظ می‌شوند.
names=['phi_b','h0_b','wt_buses','pv_pdn_buses','wt_capacities','pv_pdn_capacities','wt_pu_days','pv_pu_days','Df_initial','PDN_lines_data','Load_P_days']
arrays='\n# بخش اول — آرایه‌های مستند حفظ‌شده از فایل ارسالی کاربر\n'
for name in names:
 m=re.search(r'^'+name+r'\s*=\s*\[(.*?)\]',text,re.M|re.S)
 assert m,name
 arrays+='const '+m[0]+'\n\n'
# جدول‌هایی که از آرایه‌ها ساخته می‌شوند، دوباره به‌صورت عددی جاسازی نمی‌شوند.
rebuilt={1,2,3,4,5,6,8,11}
meta=['source_id = "supplement"',f'source_sha256 = "{data["source_sha256"]}"']
for n in range(1,12):
 tab=data[f'table{n}'];meta.append(f'\n[table{n}]')
 for key in ['pages','columns','units_as_printed']:
  meta.append(key+' = '+json.dumps(tab[key]))
 if n not in rebuilt:meta.append('rows = '+json.dumps(tab['rows']))
embedded=''
for name,payload in [('TABLES','\n'.join(meta)+'\n'),('CASE',(prev/'data/case.toml').read_text()),('SOURCES',(prev/'data/sources.toml').read_text())]:
 embedded+=f'const DATA_{name} = raw"""\n{payload}"""\n'
 embedded+=f'const HASH_{name} = "{hashlib.sha256(payload.encode()).hexdigest()}"\n'
expected={str(n):hashlib.sha256(','.join(f'{float(v):.8f}' for row in data[f'table{n}']['rows'] for v in row).encode()).hexdigest() for n in sorted(rebuilt)}
embedded+='const TABLE_HASHES = Dict('+','.join(k+'=>"'+v+'"' for k,v in expected.items())+')\n'
assemble='''
# وضعیت موجود مطابق جدول ۱؛ هنوز به تصمیم سرمایه‌گذاری تبدیل نمی‌شود.
const existing_station_roads = [2,3,10,14,16]
const num_days = TOML.parse(DATA_CASE)["scope"]["typical_days"]
const num_tau = size(wt_pu_days,1) * num_days
# ضریب سهم شارژ، آخرین ستون جدول ۱۰ است؛ ضریب راکتیو باتری نیست.
const gamma_factor = TOML.parse(DATA_TABLES)["table10"]["rows"][1][8]
# هر چهار روز حفظ می‌شود؛ فقط تقاضای ترافیک طبق عنوان جدول ۲ تکرار می‌شود.
const wt_profile = vec(wt_pu_days)
const pv_profile = vec(pv_pu_days)
const Total_Load_P = vec(Load_P_days)
const Df_period = repeat(Df_initial,num_days,1)

function assembled_tables()
    d=TOML.parse(DATA_TABLES)
    d["table1"]["rows"]=[Any[i,phi_b[i],h0_b[i],i in existing_station_roads] for i in eachindex(phi_b)]
    for (n,arr) in ((2,Df_initial),(3,wt_pu_days),(5,pv_pu_days),(8,Load_P_days))
        d["table$n"]["rows"]=[Any[h,arr[h,:]...] for h in axes(arr,1)]
    end
    d["table4"]["rows"]=[Any[i,wt_buses[i],wt_capacities[i]] for i in eachindex(wt_buses)]
    d["table6"]["rows"]=[Any[i,pv_pdn_buses[i],pv_pdn_capacities[i]] for i in eachindex(pv_pdn_buses)]
    d["table11"]["rows"]=[Any[Int(r[1]),Int(r[2]),r[3:end]...] for r in eachrow(PDN_lines_data)]
    # اثر انگشت عددی از جدول PDF ممیزی‌شده، مستقل از فاصله‌گذاری و شکل نوشتن اعشار.
    for (n,expected) in TABLE_HASHES
        payload=join([@sprintf("%.8f",Float64(v)) for row in d["table$n"]["rows"] for v in row],",")
        demand(bytes2hex(sha256(payload))==expected,"اختلاف با جدول منبع: $n")
    end
    return d
end
'''
source=(prev/'run_step01.jl').read_text();source=source[:source.index('# ورود از خط فرمان')]
source=source.replace('module REVCSDataStep01','module ReferenceRewriteS01')
source=source.replace('export load_case, profiles, require_optimization_ready\n','export load_case, profiles, require_optimization_ready\n'+arrays+embedded+assemble)
a=source.index('function verify_checksums(root)');b=source.index('# کنترل شکل جدول',a)
source=source[:a]+'''function verify_checksums(root)
    for (payload,expected) in ((DATA_TABLES,HASH_TABLES),(DATA_CASE,HASH_CASE),(DATA_SOURCES,HASH_SOURCES))
        demand(bytes2hex(sha256(payload))==expected,"تغییر در بخش دادهٔ مستند")
    end
end

'''+source[b:]
source=source.replace('TOML.parsefile(joinpath(root,"data","tables.toml"))','assembled_tables()')
for name in ['case','sources']:source=source.replace(f'TOML.parsefile(joinpath(root,"data","{name}.toml"))',f'TOML.parse(DATA_{name.upper()})')
source=source.replace('"step"=>"S01"','"step"=>"REFERENCE_S01", "base_code_sha256"=>"'+hashlib.sha256(old.read_bytes()).hexdigest()+'"')
header='''# CODE_REFERENCE.jl — بازنویسی گام اول روی فایل ارسالی کاربر | CHG-0008
# اجرا در PowerShell: julia CODE_REFERENCE.jl
# اجرا در Julia: include(raw"E:\\112\\CODE_REFERENCE.jl")
# این یک فایل خودکفاست؛ فقط کتابخانه‌های استاندارد Julia لازم است.
# خروجی در results_REFERENCE_S01 کنار فایل ساخته می‌شود.
# آرایه‌های تأییدشدهٔ فایل اولیه حفظ شده‌اند؛ منطق اعتبارسنجی S01 به آن‌ها افزوده شده است.
# مدل و نمودارهای مصنوعی نسخهٔ اولیه فعال نیستند و در این نسخه وجود ندارند.
# گام جاری فقط داده است؛ حل و نمودارهای نتایج در گام‌های بعد افزوده می‌شوند.
# ابهام‌های واحد، SOC، مسیر، تنزیل و روش حل با عدد حدسی پر نمی‌شوند.
'''
footer='''
# فراخوانی در سطح بالا برای سازگاری world age در Julia جدید.
ReferenceRewriteS01.run(@__DIR__,joinpath(@__DIR__,"results_REFERENCE_S01"))
println("مسیر خروجی: ",joinpath(@__DIR__,"results_REFERENCE_S01"))
'''
(root/'versions/REFERENCE_S01/CODE_REFERENCE.jl').write_text(header+source+footer)
