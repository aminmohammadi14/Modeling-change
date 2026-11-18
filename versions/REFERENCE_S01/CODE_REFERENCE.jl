# CODE_REFERENCE.jl — بازنویسی گام اول روی فایل ارسالی کاربر | CHG-0008
# اجرا در PowerShell: julia CODE_REFERENCE.jl
# اجرا در Julia: include(raw"E:\112\CODE_REFERENCE.jl")
# این یک فایل خودکفاست؛ فقط کتابخانه‌های استاندارد Julia لازم است.
# خروجی در results_REFERENCE_S01 کنار فایل ساخته می‌شود.
# آرایه‌های تأییدشدهٔ فایل اولیه حفظ شده‌اند؛ منطق اعتبارسنجی S01 به آن‌ها افزوده شده است.
# مدل و نمودارهای مصنوعی نسخهٔ اولیه فعال نیستند و در این نسخه وجود ندارند.
# گام جاری فقط داده است؛ حل و نمودارهای نتایج در گام‌های بعد افزوده می‌شوند.
# ابهام‌های واحد، SOC، مسیر، تنزیل و روش حل با عدد حدسی پر نمی‌شوند.
# گام اول بازنویسی: خواندن و کنترل داده‌های مستند، بدون ساخت مدل یا جواب بهینه‌سازی.
module ReferenceRewriteS01
using TOML, SHA, Printf
export load_case, profiles, require_optimization_ready

# بخش اول — آرایه‌های مستند حفظ‌شده از فایل ارسالی کاربر
const phi_b = [
    3528.00, 3920.00, 3332.00, 1920.80, 1548.40, 1666.00, 2646.00, 1607.20, 3724.00, 2744.00, 
    2704.80, 3920.00, 1744.40, 2587.20, 1792.00, 3430.00, 1912.40, 1758.40, 3567.20, 3920.00
]

const h0_b = [
    6.0, 10.0, 6.5, 5.0, 5.5, 6.0, 12.0, 6.5, 10.2, 11.5, 
    12.5, 10.5, 5.8, 11.0, 5.9, 6.3, 5.7, 5.8, 6.1, 9.8
]

const wt_buses       = [4, 13, 22, 27, 31]

const pv_pdn_buses   = [7, 11, 17, 19, 25]

const wt_capacities     = [263.50, 395.00, 395.00, 197.50, 461.00]

const pv_pdn_capacities = [253.00, 184.00, 276.50, 138.00, 322.50]

const wt_pu_days = [
    0.8588  0.8520  0.8481  0.8448;
    0.8458  0.8381  0.8372  1.0000;
    0.7924  0.8957  0.8522  0.8887;
    0.6601  0.6704  0.7389  0.5758;
    0.6009  0.6534  0.6621  0.5688;
    0.7847  0.7136  0.8577  0.6335;
    0.6124  0.6442  0.6007  0.6831;
    0.6896  0.5872  0.6726  0.7205;
    0.5393  0.5263  0.5964  0.5916;
    0.6109  0.5272  0.5340  0.5445;
    0.4547  0.4455  0.5373  0.4693;
    0.4324  0.3816  0.4442  0.4655;
    0.5005  0.5012  0.4932  0.4883;
    0.4435  0.4446  0.4271  0.4159;
    0.4701  0.4660  0.4064  0.4484;
    0.4992  0.4726  0.4543  0.5192;
    0.5410  0.5127  0.5210  0.4581;
    0.4736  0.5237  0.4258  0.4602;
    0.6532  0.6919  0.6954  0.5859;
    0.7407  0.7837  0.7431  0.7010;
    0.7549  0.7233  0.7103  0.6786;
    0.7734  0.7204  0.7257  0.7012;
    0.8414  0.7655  0.9142  0.8269;
    0.6960  0.7364  0.7508  0.6094
]

const pv_pu_days = [
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.1495  0.1309  0.1545  0.1497;
    0.4539  0.4829  0.4907  0.4471;
    0.7976  0.7449  0.7228  0.7925;
    0.8365  0.7433  0.8568  0.8111;
    0.8365  0.9471  0.9049  0.8050;
    0.5854  0.6032  0.5801  0.5447;
    0.6320  0.6173  0.6019  0.6579;
    0.7100  0.6858  0.6483  0.6458;
    0.9526  0.9114  0.7914  1.0000;
    0.7700  0.8474  0.8300  0.8318;
    0.8675  0.8602  0.8063  0.9632;
    0.8088  0.7378  0.8746  0.7704;
    0.5153  0.5726  0.5725  0.5068;
    0.3538  0.3563  0.3661  0.3291;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000;
    0.0000  0.0000  0.0000  0.0000
]

const Df_initial = [
    558.88  688.21  783.89  766.87  851.40  417.42  872.69  750.69  505.26;
    498.51  566.25  937.52  797.87  812.26  520.54  878.34  674.65  520.45;
    557.05  701.05  857.45  660.37  867.99  542.61 1006.78  769.34  494.21;
    536.30  567.19  710.54  730.44  712.53  503.96  825.72  578.77  527.67;
    517.37  610.26  873.81  617.45  761.54  498.60  971.65  673.01  514.91;
    460.46  543.88  776.02  785.49  878.85  494.07  900.00  772.60  444.14;
    501.22  581.35  874.49  638.59  779.24  432.01  874.86  688.93  480.72;
    550.13  703.24  834.43  706.61  745.39  424.46  836.58  731.23  439.48;
    500.88  560.02  919.41  715.41  689.61  522.24  922.71  742.75  437.30;
    511.81  610.18  812.58  820.06  736.62  571.48 1022.81  680.23  547.11;
    425.77  508.37  769.34  788.10  843.90  461.13  827.25  674.86  421.16;
    488.33  567.57  795.04  731.88  863.26  499.23  937.99  620.42  485.07;
    562.87  641.87  787.79  653.38  731.54  528.54  874.87  755.18  552.29;
    501.21  589.32  853.83  662.79  922.20  451.49  978.38  681.19  494.84;
    503.18  559.43  798.52  752.81  781.37  496.79  857.54  599.31  484.41;
    443.50  624.35  806.49  679.25  716.55  567.49  988.93  609.26  534.21;
    536.92  541.77  697.29  623.58  798.96  487.10  892.18  569.52  574.63;
    508.93  581.53  818.08  720.55  875.49  488.72  898.31  726.70  516.36;
    485.71  578.51  775.14  677.81  851.99  569.09  855.15  570.80  450.45;
    500.93  628.45  785.22  579.14  686.29  483.14  984.78  707.47  542.84;
    512.17  598.03  893.31  701.43  842.22  508.93  858.59  721.66  508.43;
    438.12  634.90  918.74  758.52  818.60  491.59  837.34  714.12  469.08;
    509.93  579.14  818.08  707.48  912.95  492.19  822.95  772.18  578.51;
    528.37  656.26  848.97  667.47  763.86  501.35  783.92  745.68  425.11
]

const PDN_lines_data = [
    1   2   0.0922  0.0470  3047.13;  2   3   0.4930  0.2511  2549.40;  3   4   0.3660  0.1864  2164.76;
    4   5   0.3811  0.1941  2668.01;  5   6   0.8190  0.7070  2457.81;  6   7   0.1872  0.6188  2300.48;
    7   8   0.7114  0.2351  2048.59;  8   9   1.0300  0.7400  2966.33;  9  10   1.0440  0.7400  2688.23;
   10  11   0.1966  0.0650  2851.36; 11  12   0.3744  0.1238  2355.47; 12  13   1.4680  1.1550  2705.91;
   13  14   0.5416  0.7129  2541.76; 14  15   0.5910  0.5260  2520.55; 15  16   0.7463  0.5450  2286.02;
   16  17   1.2890  1.7210  2613.39; 17  18   0.7320  0.5740  2402.82;  2  19   0.1640  0.1565  2596.22;
   19  20   1.5042  1.3554  2438.83; 20  21   0.4095  0.4784  2673.81; 21  22   0.7089  0.9373  2590.52;
    3  23   0.4512  0.3083  2336.64; 23  24   0.8980  0.7091  2808.84; 24  25   0.8960  0.7011  2707.61;
    6  26   0.2030  0.1034  2543.83; 26  27   0.2842  0.1447  2296.86; 27  28   1.0590  0.9337  2302.25;
   28  29   0.8042  0.7006  2497.54; 29  30   0.5075  0.2585  2507.18; 30  31   0.9744  0.9630  2243.74;
   31  32   0.3105  0.3619  2413.65; 32  33   0.3410  0.5302  2596.15; 21   8   2.0000  2.0000  2379.71;
    9  15   2.0000  2.0000  2427.50; 12  22   2.0000  2.0000  2767.34; 18  33   0.5000  0.5000  2756.41;
   25  29   0.5000  0.5000  2776.44
]

const Load_P_days = [
    2194.56  2395.75  2073.62  2270.24;
    2318.93  2516.61  2239.78  2492.41;
    2179.02  2129.65  2091.06  2038.34;
    2390.44  2165.43  2199.35  2403.66;
    2723.11  2564.21  2650.42  2436.52;
    3857.93  3596.55  4542.53  3680.43;
    4013.38  3885.87  3662.91  3951.70;
    4168.84  4161.07  3971.99  4962.07;
    4231.02  4260.52  4735.59  4936.19;
    4308.75  4327.83  4294.56  3941.05;
    4595.23  4124.76  4178.37  5037.70;
    4712.93  5124.41  4902.02  4920.10;
    4977.20  4570.90  5217.84  4819.68;
    4782.88  5451.13  5019.09  4628.25;
    4184.38  4594.85  4774.17  4472.51;
    3857.93  4003.67  3492.06  3442.31;
    4161.06  4013.64  3833.31  4527.05;
    4122.20  4178.10  3610.70  4421.45;
    3811.29  3787.13  3884.27  3606.98;
    3307.62  2915.05  3411.45  3372.55;
    2793.06  3158.99  2579.75  2775.14;
    2629.84  2623.20  2476.20  2701.17;
    2468.16  2312.76  2464.55  2247.30;
    2381.11  2560.89  2391.62  2246.39
]

const DATA_TABLES = raw"""
source_id = "supplement"
source_sha256 = "7401f1110de37bf64e9649e055e7092f2cc6038a2b97437e45c919b11d8791a2"

[table1]
pages = [1]
columns = ["road", "capacity", "free_time_min", "existing_revcs"]
units_as_printed = ["id", "not_printed", "min", "boolean"]

[table2]
pages = [2]
columns = ["hour", "T1_T6", "T1_T10", "T1_T12", "T3_T6", "T3_T12", "T3_T11", "T4_T9", "T4_T10", "T4_T12"]
units_as_printed = ["hour", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed"]

[table3]
pages = [2]
columns = ["hour", "day1", "day2", "day3", "day4"]
units_as_printed = ["hour", "p.u.", "p.u.", "p.u.", "p.u."]

[table4]
pages = [2]
columns = ["id", "bus", "capacity"]
units_as_printed = ["id", "id", "kW"]

[table5]
pages = [3]
columns = ["hour", "day1", "day2", "day3", "day4"]
units_as_printed = ["hour", "p.u.", "p.u.", "p.u.", "p.u."]

[table6]
pages = [3]
columns = ["id", "bus", "capacity"]
units_as_printed = ["id", "id", "kW"]

[table7]
pages = [3]
columns = ["FCS", "BESS", "onsite_PV"]
units_as_printed = ["kW", "kW_as_printed", "kW"]
rows = [[200.0, 40.0, 60.0]]

[table8]
pages = [3, 4]
columns = ["hour", "day1", "day2", "day3", "day4"]
units_as_printed = ["hour", "not_printed_in_table", "not_printed_in_table", "not_printed_in_table", "not_printed_in_table"]

[table9]
pages = [4]
columns = ["device", "upper", "lower", "ramp", "charge_efficiency", "discharge_efficiency"]
units_as_printed = ["name", "kW", "kW", "kWh_as_printed", "ratio", "ratio"]
rows = [["FCS", 200.0, 0.0, "/", "/", "/"], ["BESS", 40.0, 0.0, 20.0, 0.95, 0.9], ["Onsite PV", 60.0, 0.0, "/", "/", "/"]]

[table10]
pages = [4]
columns = ["Pbu_upper", "V_upper", "V_lower", "V_hat", "tan_phi", "Sw", "reactive_factor", "gamma1_gamma2"]
units_as_printed = ["kW", "not_printed", "not_printed", "not_printed", "ratio", "not_printed", "ratio", "ratio"]
rows = [[4800.0, 1.05, 0.93, 1.03, 0.2, 468.0, 0.3, 0.24]]

[table11]
pages = [4]
columns = ["from_bus", "to_bus", "r", "x", "active_capacity"]
units_as_printed = ["id", "id", "not_printed", "not_printed", "kW"]
"""
const HASH_TABLES = "430580dbe6698c04fef7adf6faea0d7f10d25b301d1624377e2d0226ba18f90e"
const DATA_CASE = raw"""
# فقط مقادیر مستند مقاله؛ تغییر پارامترها از فایل داده انجام می‌شود.
[scope]
case_id = "33P-12U"
buses = 33
transport_nodes = 12
periods = 3
years_per_period = 1
hours_per_day = 24
typical_days = 4
source = "paper: PDF page 9 (printed page 3765), IV.A-B"

[traffic]
# عنوان جدول ۲ تکرار دقیق روز اول در سه روز دیگر را تصریح می‌کند.
repeat_first_day = true
source = "supplement: Table 2, page 2, caption"

[costs]
construction_USD = 110000.0
maintenance_USD = 20000.0
onsite_PV_expansion_USD_per_kW = 1000.0
FCS_expansion_USD_per_kW = 200.0
BESS_expansion_USD_per_kW_as_printed = 600.0
WT_curtailment_USD_per_kWh = 2.0
PV_curtailment_USD_per_kWh = 2.0
imbalance_USD_per_kWh = 10.0
substation_USD_per_kWh = 0.3
free_travel_USD_per_min = 0.012
delayed_travel_USD_per_min = 0.04
source = "paper: PDF page 9 (printed page 3765), IV.A"

[uncertainty]
# ضرایب نسبت به سال اولیه‌اند؛ این مرحله هیچ رشد مرکب دوره‌به‌دوره‌ای نمی‌سازد.
periods_with_growth = [2, 3]
DRE_capacity_multiplier_intervals = [[1.3, 1.5], [1.8, 2.0]]
traffic_multiplier_intervals = [[1.3, 1.5], [1.7, 2.0]]
WT_forecast_multiplier_interval = [0.75, 1.25]
PV_forecast_multiplier_interval = [0.9, 1.1]
source = "paper: IV.B page 9; initial-year formulation equations 48-52"

[readiness]
# این‌ها پیش‌فرض عددی ندارند؛ تا بررسی علمی، ورود خودکار به مدل ممنوع است.
optimization_ready = false
unresolved = ["UTN_direction_and_candidate_paths", "road_to_bus_mapping_review", "BESS_energy_power_SOC_boundaries", "voltage_impedance_units_and_base", "charging_energy_Delta_p", "discount_sigma", "annual_TOI_weighting", "load_bus_set_and_reactive_load", "existing_station_initial_state", "Eq33_vs_Eq41", "state_discretization_and_upper_penalty"]
"""
const HASH_CASE = "6e3b66fa45f0cc0873695ca002d80a45633dec1f5a78ff88863671f915a9ccc5"
const DATA_SOURCES = raw"""
# شناسهٔ نسخهٔ منابع ارسال‌شده؛ خود PDFها بازنشر نشده‌اند.

[paper]
filename = "sim 00.pdf"
sha256 = "1bcb339d9ccc17fe97cd1d65052173acbc9386f451feffacc72b7a607b1f6b88"
pages = 16

[supplement]
filename = "Data of 33P-12U and 54P-25U systems (1).pdf"
sha256 = "7401f1110de37bf64e9649e055e7092f2cc6038a2b97437e45c919b11d8791a2"
pages = 8
"""
const HASH_SOURCES = "aa27c5f7172fb91868b387e02d0ebaa19b739b64ef8c58f3028cf9c06d6b162d"
const TABLE_HASHES = Dict(1=>"de6fef93b0120197ae3ea6240dbe1ffeeef90b5c4950586eff9de67cb2514dec",2=>"8ab94ea09a73d1b81217d50bd5f2ddc58c8e5a1c9602d161713cab72b850040c",3=>"627fb18a0f319edd3805f531aee28aab1aa2d7b8b6b429065880047e26afb24c",4=>"1b07b6604f1ca8e86a2b05bbef9a3f53446e7290be8f8f0994a3dfa9ede4a247",5=>"af5094445a00cfdc29109da5ba8f0d162607c88e8d179b17708b4dbc54e5d40f",6=>"6c4c2d86d5371c7e1e7c713c976f7fd1c422eaaa267efdda88da9e4fef679515",8=>"3e017deb116dc80e0bee7ba81cee2164bf1154115ccb6077edfd82be0d6d629c",11=>"cf97e672087c4f00f24060c3ffb949bfc66e141996a1a85bb070308ebb36b9b9")

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

# خطای داده باید روشن و فوری باشد؛ هیچ مقدار پیش‌فرضی جایگزین دادهٔ مفقود نمی‌شود.
function demand(condition::Bool, message::String)
    condition || throw(ArgumentError(message))
end

# اثر انگشت فایل‌های داده، تغییر ناخواستهٔ ورودی پس از استخراج را آشکار می‌کند.
function verify_checksums(root)
    for (payload,expected) in ((DATA_TABLES,HASH_TABLES),(DATA_CASE,HASH_CASE),(DATA_SOURCES,HASH_SOURCES))
        demand(bytes2hex(sha256(payload))==expected,"تغییر در بخش دادهٔ مستند")
    end
end

# کنترل شکل جدول و نوع داده، پیش از هر تبدیل به ماتریس انجام می‌شود.
function check_table(table, rows, columns, label)
    demand(length(table["rows"]) == rows, "تعداد سطر نامعتبر: $label")
    demand(length(table["columns"]) == columns, "تعداد ستون نامعتبر: $label")
    demand(length(table["units_as_printed"]) == columns, "واحد ستون‌ها ناقص است: $label")
    demand(all(length(row) == columns for row in table["rows"]), "سطر ناقص: $label")
    demand(all(!(v isa Real) || isfinite(v) for row in table["rows"] for v in row), "مقدار نامتناهی: $label")
end

# کنترل اتصال بدون فرض شعاعی بودن؛ تمام خطوط چاپ‌شده، از جمله خطوط اتصال، حفظ می‌شوند.
function connected(lines, n)
    seen = Set([first(lines)[1]])
    changed = true
    while changed
        before = length(seen)
        for row in lines
            u,v = row[1:2]
            if u in seen || v in seen
                push!(seen,u); push!(seen,v)
            end
        end
        changed = length(seen) != before
    end
    return length(seen) == n
end

# خواننده مستقل از نسخهٔ ۱۹ است و از هیچ آرایهٔ جاسازی‌شده در کد قدیمی استفاده نمی‌کند.
function load_case(root=@__DIR__)
    verify_checksums(root)
    data = assembled_tables()
    case = TOML.parse(DATA_CASE)
    sources = TOML.parse(DATA_SOURCES)
    demand(data["source_sha256"] == sources["supplement"]["sha256"], "منبع جدول‌ها متفاوت است")
    scope = case["scope"]
    hours, days = scope["hours_per_day"], scope["typical_days"]
    n = scope["buses"]
    # تعدادهای زیر قرارداد جدول‌های منبع هستند، نه پارامتر حل یا نتیجهٔ تحمیلی.
    sizes = Dict(1=>(20,4), 2=>(hours,10), 3=>(hours,days+1), 4=>(5,3),
                 5=>(hours,days+1), 6=>(5,3), 7=>(1,3), 8=>(hours,days+1),
                 9=>(3,6), 10=>(1,8), 11=>(37,5))
    for (number,(nr,nc)) in sizes
        check_table(data["table$number"],nr,nc,"جدول $number")
    end
    # ساعت‌ها باید دقیقاً به ترتیب منبع باشند؛ جابه‌جایی روز و ساعت پذیرفته نمی‌شود.
    for number in (2,3,5,8)
        rows = data["table$number"]["rows"]
        demand([r[1] for r in rows] == collect(1:hours), "ترتیب ساعت جدول $number نادرست است")
        demand(all(v isa Real && !(v isa Bool) && v >= 0 for r in rows for v in r[2:end]), "پروفایل منفی/غیرعددی")
    end
    for number in (3,5)
        demand(all(v <= 1 for r in data["table$number"]["rows"] for v in r[2:end]), "پروفایل پیش‌بینی خارج [۰،۱]")
    end
    # این محدودیت تنها برای پیش‌بینی اولیه است؛ تحقق نامطمئن WT ممکن است از یک بزرگ‌تر باشد.
    for number in (4,6)
        rows = data["table$number"]["rows"]
        demand(length(unique(r[2] for r in rows)) == length(rows), "باس تولید تکراری")
        demand(all(r[2] isa Integer && 1 <= r[2] <= n && r[3] > 0 for r in rows), "ظرفیت یا باس تولید نامعتبر")
    end
    roads = data["table1"]["rows"]
    demand([r[1] for r in roads] == collect(1:length(roads)), "شناسهٔ راه نامعتبر")
    demand(all(r[2] > 0 && r[3] > 0 && r[4] isa Bool for r in roads), "پارامتر راه نامعتبر")
    lines = data["table11"]["rows"]
    demand(all(all(b isa Integer && 1 <= b <= n for b in r[1:2]) && r[1] != r[2] for r in lines), "انتهای خط نامعتبر")
    demand(length(unique(Tuple(sort(r[1:2])) for r in lines)) == length(lines), "خط تکراری")
    demand(all(all(v > 0 for v in r[3:5]) for r in lines), "پارامتر خط غیرمثبت")
    demand(connected(lines,n), "شبکهٔ برق گسسته است")
    demand(case["traffic"]["repeat_first_day"] === true, "تکرار روز ترافیک باید مستند باشد")
    return (;data,case,sources)
end

# سطر ماتریس حاصل ساعت پیوستهٔ روزهاست: ابتدا ۲۴ ساعت روز اول، سپس روز دوم و ... .
function profiles(bundle)
    data, case = bundle.data, bundle.case
    days = case["scope"]["typical_days"]
    hours = case["scope"]["hours_per_day"]
    # آرایه‌های WT و PV هر چهار روز را مستقلاً از منبع می‌خوانند.
    flatten(number) = [Float64(data["table$number"]["rows"][h][d+1]) for d in 1:days for h in 1:hours]
    # فقط تقاضای O-D مطابق عنوان جدول ۲ در چهار روز تکرار می‌شود.
    od = [Float64(row[j]) for row in data["table2"]["rows"], j in 2:length(data["table2"]["columns"])]
    return (;wind=flatten(3), solar=flatten(5), load=flatten(8), traffic=repeat(od,days,1))
end

# گیت صریح: این مرحله مجاز نیست با حدس دربارهٔ دادهٔ مفقود، حل مدل را آغاز کند.
function require_optimization_ready(bundle)
    pending = bundle.case["readiness"]["unresolved"]
    demand(isempty(pending) && bundle.case["readiness"]["optimization_ready"],
           "مدل برای حل آماده نیست؛ موارد باز: " * join(pending, ", "))
    return true
end

# رسم SVG بدون وابستگی خارجی؛ ثابت‌های این بخش فقط رنگ و اندازهٔ تصویر هستند.
# این نمودارها دادهٔ ورودی‌اند و عنوان شکلِ نتایج مقاله به آن‌ها داده نمی‌شود.
function plot_profile(path, rows, title, ylabel, labels)
    width,height = 900,420
    left,right,top,bottom = 85,710,65,350
    count,nseries = size(rows)
    ymax = maximum(rows)
    demand(ymax > 0, "مقیاس نمودار صفر است")
    colors = ["#1f77b4","#d95f02","#2ca02c","#9467bd","#8c564b","#e377c2","#17becf","#bcbd22","#555555"]
    x(i) = left+(right-left)*(i-1)/max(count-1,1)
    y(v) = bottom-(bottom-top)*v/ymax
    open(path,"w") do io
        println(io,"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"$width\" height=\"$height\" viewBox=\"0 0 $width $height\">")
        println(io,"<rect width=\"100%\" height=\"100%\" fill=\"white\"/><g font-family=\"sans-serif\" font-size=\"13\">")
        println(io,"<text x=\"85\" y=\"27\">$title</text><text x=\"85\" y=\"48\">$ylabel — input data, not optimization results</text>")
        for ratio in range(0,1;length=5)
            yy=y(ratio*ymax)
            println(io,"<path d=\"M $left $yy H $right\" stroke=\"#dddddd\"/>")
            println(io,"<text x=\"75\" y=\"$(yy+4)\" text-anchor=\"end\">$(@sprintf("%.2f",ratio*ymax))</text>")
        end
        for i in unique(round.(Int,range(1,count;length=7)))
            println(io,"<text x=\"$(x(i))\" y=\"373\" text-anchor=\"middle\">$i</text>")
        end
        println(io,"<text x=\"360\" y=\"400\">Hour within typical day</text>")
        for j in 1:nseries
            color=colors[mod1(j,length(colors))]
            points=join(["$(x(i)),$(y(rows[i,j]))" for i in 1:count]," ")
            println(io,"<polyline points=\"$points\" fill=\"none\" stroke=\"$color\" stroke-width=\"2\"/>")
            yy=top+22j
            println(io,"<text x=\"730\" y=\"$yy\" fill=\"$color\">$(labels[j])</text>")
        end
        println(io,"</g></svg>")
    end
end

# اجرای کامل گام اول و ثبت گزارش قابل خواندن توسط انسان و ماشین.
function run(root=@__DIR__, output=joinpath(root,"results"))
    b=load_case(root)
    p=profiles(b)
    mkpath(output)
    for (number,name,label) in [(3,"wind","WT forecast (p.u.)"),(5,"solar","PV forecast (p.u.)"),
                               (8,"load","Aggregated load (unit not printed in Table 8)"),
                               (2,"traffic","O-D demand (flow unit not printed)")]
        table=b.data["table$number"]
        rows=[Float64(r[j]) for r in table["rows"],j in 2:length(table["columns"])]
        plot_profile(joinpath(output,name*".svg"),rows,"Supplement Table $number",label,table["columns"][2:end])
    end
    report=Dict("step"=>"REFERENCE_S01", "base_code_sha256"=>"03200963774b72792b1eac302e165e5da34724dcfa989d93a8b4b055b8af6761", "input_validation"=>"passed", "optimization_run"=>false,
        "paper_results_reproduced"=>false, "buses"=>b.case["scope"]["buses"],
        "lines"=>length(b.data["table11"]["rows"]),"roads"=>length(b.data["table1"]["rows"]),
        "hours_per_period"=>length(p.wind), "unresolved"=>b.case["readiness"]["unresolved"],
        "sources"=>b.sources)
    open(joinpath(output,"validation.toml"),"w") do io
        TOML.print(io,report)
    end
    println("گام اول موفق: خواندن ۱۱ جدول، کنترل داده‌ها و تولید ۴ نمودار ورودی. مدل بهینه‌سازی اجرا نشده است.")
    return report
end
end


# فراخوانی در سطح بالا برای سازگاری world age در Julia جدید.
ReferenceRewriteS01.run(@__DIR__,joinpath(@__DIR__,"results_REFERENCE_S01"))
println("مسیر خروجی: ",joinpath(@__DIR__,"results_REFERENCE_S01"))
