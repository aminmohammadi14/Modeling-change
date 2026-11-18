# REVCS S01 — فایل یکپارچهٔ اجرایی | CHG-0006
# فقط همین فایل را ذخیره و اجرا کنید؛ فایل داده یا فایل آزمون جدا لازم نیست.
# PowerShell: julia revcs_step01_integrated.jl
# Julia REPL: include(raw"E:\112\revcs_step01_integrated.jl")
# فقط کتابخانه‌های استاندارد Julia استفاده می‌شوند؛ نصب حل‌گر لازم نیست.
# خروجی: پوشهٔ results_S01 کنار همین فایل؛ چهار نمودار ورودی و گزارش اعتبارسنجی.
# مرز کار: این گام فقط بررسی داده است؛ مدل بهینه‌سازی و نتایج مقاله هنوز تولید نشده‌اند.
# پارامترها در بخش DATA از منطق برنامه جدا هستند؛ موارد نامشخص در readiness باقی‌اند.

#=
# ابهام‌ها و مرز اعتبار گام اول

مبنای بازنویسی، دو PDF ارسالی در ۲۰۲۶-۱۱-۱۸ است. مقادیر جدول‌ها جدا از برنامه ذخیره شده‌اند؛ عدد مستند در فایل داده «هاردکد منطق مدل» نیست. کد حل در مراحل بعد باید همهٔ پارامترها را از همین ورودی‌ها بخواند. در این گام هیچ نتیجهٔ بهینه‌سازی تولید نشده است.

| موضوع | شواهد و تصمیم فعلی |
|---|---|
| شبکهٔ برق | جدول ۱۱، ۳۷ خط برای ۳۳ باس دارد. هر ۳۷ خط حفظ شده‌اند؛ وضعیت باز/بستهٔ کلید یا شعاعی بودن تحمیل نشده است. اتصال گراف بدون جهت کنترل می‌شود؛ این کنترل، اثبات امکان‌پذیری پخش بار نیست. |
| جهت راه‌ها و مسیرهای مجاز | بخش II.B.1 از گراف جهت‌دار سخن می‌گوید، ولی در تصویر صفحهٔ اول داده، جهت راه‌ها صریح نیست. جهت، مجموعهٔ مسیرهای کاندید و نگاشت راه به باس باید در گام بعد از تصویر بررسی شوند. فعلاً هیچ مسیر یا جهت حدسی ساخته نشده است. |
| واحدهای برق | واحد r و x و مبنای تبدیل ولتاژ/توان در جدول ۱۱ چاپ نشده است. فرض استاندارد 12.66kV یا تبدیل امپدانس از حافظه وارد نشده است. مقدار V_hat=1.03 در جدول ۱۰ حفظ می‌شود ولی معنای مبنا باید با روابط ۲۶–۲۷ روشن شود. |
| باتری | ظرفیت در جدول ۷ و کران گسترش در جدول ۹ با kW، ولی Ramp با kWh چاپ شده است. تبدیل خودکار ۴۰ به ظرفیت انرژی، یا ۲۰ به توان شارژ، مجاز نیست. رابطهٔ ۲۰ به ظرفیت و SOC وابسته است؛ مرز SOC، شرایط اول/آخر روز و ارتباط چهار روز باید صریح تعیین شوند. |
| بار | عنوان جدول ۸ می‌گوید بار تجمیعی به‌طور مساوی میان باس‌ها توزیع می‌شود. مجموعهٔ باس‌های بار و سهم باس پست باید پیش از تقسیم بر ۳۲ یا ۳۳ روشن شود. واحد در عنوان جدول چاپ نشده؛ جدول ۱۰ نیز به‌تنهایی نسبت Q/P بار را بدون بررسی مدل تعیین نمی‌کند. فعلاً بار تجمیعی عیناً نگه داشته شده است. |
| شارژ و زمان | مقدار انرژی/ضریب Δp در رابطهٔ ۳۲، نرخ تنزیل σ در رابطهٔ ۱ و وزن سالانهٔ چهار روز نمونه برای محاسبهٔ هزینه نیاز به تعیین مستند دارند. ۳۶۵/۴ یا نرخ تنزیل دلخواه وارد نشده است. |
| ایستگاه موجود | جدول ۱ راه‌های ۲،۳،۱۰،۱۴،۱۶ را دارای ایستگاه می‌داند. متن روابط ۳۷–۴۳ حالت اولیهٔ صفر را توصیف می‌کند. قرارداد مقداردهی اولیه برای ایستگاه‌های موجود باید آشکارا حل شود. |
| ظرفیت شارژ ایستگاه جدید | رابطهٔ ۳۳، Cc_previous+Ec را محدودیت قرار می‌دهد ولی رابطهٔ ۴۱ ظرفیت پایهٔ ساخت را اضافه می‌کند و رابطهٔ ۴۰ گسترش هم‌زمان با ساخت را منع می‌کند. این اختلاف باید پیش از مدل‌سازی ایستگاه حل/به‌عنوان فرض ثبت شود. |
| ابهام نمادها | رابطهٔ ۱۶ دو بار μ_ch را چاپ کرده و رابطهٔ ۳۱ آخرین متغیر را با برچسب p− تکرار کرده است. اصلاح به μ_un یا q− باید به‌عنوان تفسیر ثبت شود، نه نقل عین مقاله. |
| حالت و تقریب بالا | متن بخش III.A تبدیل دودویی را ارجاع می‌دهد اما گام گسسته‌سازی، کران‌ها و تعداد بیت اجرایی را کامل مشخص نمی‌کند. شیب تطبیقی بیرون پوش محدب رابطهٔ ۶۱ نیز نیاز به بررسی روش ارجاعی دارد. هیچ مقدار دلخواهی به نام نویسندگان پذیرفته نمی‌شود. |
| نتایج و شکل‌ها | سری خام خروجی شکل‌های مقاله در دو فایل موجود ارائه نشده است. بازسازی نوع شکل از خروجی حل ممکن است؛ برابری عددی با تصویر بدون تنظیمات و داده‌های تکمیلی تضمین‌پذیر نیست. مقادیر جدول نتایج مقاله نباید ورودی حل یا خروجی ازپیش‌تعیین‌شده باشند. |

## اصلاح صرفاً تایپی هنگام استخراج

در متن استخراج‌شدهٔ جدول ۴، پس از ظرفیت 197.50 علامت `\` دیده می‌شود. تصویر صفحهٔ ۲ مقدار 197.50 را تأیید می‌کند. فقط همین علامت حذف شده؛ هیچ عددی تغییر نکرده است. علامت `/` جدول ۹ به صورت رشته باقی مانده و به صفر تبدیل نشده است.

این فهرست مقدماتی است؛ مرور هر معادله در مرحلهٔ اجرای همان بخش تکمیل می‌شود. موارد باز به معنی ناممکن بودن مدل نیستند و نباید با پیش‌فرض خاموش پوشانده شوند.

=#

# گام اول بازنویسی: خواندن و کنترل داده‌های مستند، بدون ساخت مدل یا جواب بهینه‌سازی.
module REVCSStandaloneS01
using TOML, SHA, Printf
export load_case, profiles, require_optimization_ready

# بخش دادهٔ مستند: متن TOML عیناً از ورودی ممیزی‌شده منتقل شده است.
# این اعداد پارامترهای ورودی‌اند، نه نتیجهٔ تحمیلی یا مقدار حدسی در منطق مدل.
const DATA_TABLES = raw"""
# داده‌های چاپ‌شده؛ ابهام واحدها در ISSUES_FA.md ثبت شده است.
source_id = "supplement"
source_sha256 = "7401f1110de37bf64e9649e055e7092f2cc6038a2b97437e45c919b11d8791a2"

[table1]
pages = [1]
columns = ["road", "capacity", "free_time_min", "existing_revcs"]
units_as_printed = ["id", "not_printed", "min", "boolean"]
rows = [
  [1, 3528.0, 6.0, false],
  [2, 3920.0, 10.0, true],
  [3, 3332.0, 6.5, true],
  [4, 1920.8, 5.0, false],
  [5, 1548.4, 5.5, false],
  [6, 1666.0, 6.0, false],
  [7, 2646.0, 12.0, false],
  [8, 1607.2, 6.5, false],
  [9, 3724.0, 10.2, false],
  [10, 2744.0, 11.5, true],
  [11, 2704.8, 12.5, false],
  [12, 3920.0, 10.5, false],
  [13, 1744.4, 5.8, false],
  [14, 2587.2, 11.0, true],
  [15, 1792.0, 5.9, false],
  [16, 3430.0, 6.3, true],
  [17, 1912.4, 5.7, false],
  [18, 1758.4, 5.8, false],
  [19, 3567.2, 6.1, false],
  [20, 3920.0, 9.8, false],
]

[table2]
pages = [2]
columns = ["hour", "T1_T6", "T1_T10", "T1_T12", "T3_T6", "T3_T12", "T3_T11", "T4_T9", "T4_T10", "T4_T12"]
units_as_printed = ["hour", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed", "traffic_flow_unit_not_printed"]
rows = [
  [1, 558.88, 688.21, 783.89, 766.87, 851.4, 417.42, 872.69, 750.69, 505.26],
  [2, 498.51, 566.25, 937.52, 797.87, 812.26, 520.54, 878.34, 674.65, 520.45],
  [3, 557.05, 701.05, 857.45, 660.37, 867.99, 542.61, 1006.78, 769.34, 494.21],
  [4, 536.3, 567.19, 710.54, 730.44, 712.53, 503.96, 825.72, 578.77, 527.67],
  [5, 517.37, 610.26, 873.81, 617.45, 761.54, 498.6, 971.65, 673.01, 514.91],
  [6, 460.46, 543.88, 776.02, 785.49, 878.85, 494.07, 900.0, 772.6, 444.14],
  [7, 501.22, 581.35, 874.49, 638.59, 779.24, 432.01, 874.86, 688.93, 480.72],
  [8, 550.13, 703.24, 834.43, 706.61, 745.39, 424.46, 836.58, 731.23, 439.48],
  [9, 500.88, 560.02, 919.41, 715.41, 689.61, 522.24, 922.71, 742.75, 437.3],
  [10, 511.81, 610.18, 812.58, 820.06, 736.62, 571.48, 1022.81, 680.23, 547.11],
  [11, 425.77, 508.37, 769.34, 788.1, 843.9, 461.13, 827.25, 674.86, 421.16],
  [12, 488.33, 567.57, 795.04, 731.88, 863.26, 499.23, 937.99, 620.42, 485.07],
  [13, 562.87, 641.87, 787.79, 653.38, 731.54, 528.54, 874.87, 755.18, 552.29],
  [14, 501.21, 589.32, 853.83, 662.79, 922.2, 451.49, 978.38, 681.19, 494.84],
  [15, 503.18, 559.43, 798.52, 752.81, 781.37, 496.79, 857.54, 599.31, 484.41],
  [16, 443.5, 624.35, 806.49, 679.25, 716.55, 567.49, 988.93, 609.26, 534.21],
  [17, 536.92, 541.77, 697.29, 623.58, 798.96, 487.1, 892.18, 569.52, 574.63],
  [18, 508.93, 581.53, 818.08, 720.55, 875.49, 488.72, 898.31, 726.7, 516.36],
  [19, 485.71, 578.51, 775.14, 677.81, 851.99, 569.09, 855.15, 570.8, 450.45],
  [20, 500.93, 628.45, 785.22, 579.14, 686.29, 483.14, 984.78, 707.47, 542.84],
  [21, 512.17, 598.03, 893.31, 701.43, 842.22, 508.93, 858.59, 721.66, 508.43],
  [22, 438.12, 634.9, 918.74, 758.52, 818.6, 491.59, 837.34, 714.12, 469.08],
  [23, 509.93, 579.14, 818.08, 707.48, 912.95, 492.19, 822.95, 772.18, 578.51],
  [24, 528.37, 656.26, 848.97, 667.47, 763.86, 501.35, 783.92, 745.68, 425.11],
]

[table3]
pages = [2]
columns = ["hour", "day1", "day2", "day3", "day4"]
units_as_printed = ["hour", "p.u.", "p.u.", "p.u.", "p.u."]
rows = [
  [1, 0.8588, 0.852, 0.8481, 0.8448],
  [2, 0.8458, 0.8381, 0.8372, 1.0],
  [3, 0.7924, 0.8957, 0.8522, 0.8887],
  [4, 0.6601, 0.6704, 0.7389, 0.5758],
  [5, 0.6009, 0.6534, 0.6621, 0.5688],
  [6, 0.7847, 0.7136, 0.8577, 0.6335],
  [7, 0.6124, 0.6442, 0.6007, 0.6831],
  [8, 0.6896, 0.5872, 0.6726, 0.7205],
  [9, 0.5393, 0.5263, 0.5964, 0.5916],
  [10, 0.6109, 0.5272, 0.534, 0.5445],
  [11, 0.4547, 0.4455, 0.5373, 0.4693],
  [12, 0.4324, 0.3816, 0.4442, 0.4655],
  [13, 0.5005, 0.5012, 0.4932, 0.4883],
  [14, 0.4435, 0.4446, 0.4271, 0.4159],
  [15, 0.4701, 0.466, 0.4064, 0.4484],
  [16, 0.4992, 0.4726, 0.4543, 0.5192],
  [17, 0.541, 0.5127, 0.521, 0.4581],
  [18, 0.4736, 0.5237, 0.4258, 0.4602],
  [19, 0.6532, 0.6919, 0.6954, 0.5859],
  [20, 0.7407, 0.7837, 0.7431, 0.701],
  [21, 0.7549, 0.7233, 0.7103, 0.6786],
  [22, 0.7734, 0.7204, 0.7257, 0.7012],
  [23, 0.8414, 0.7655, 0.9142, 0.8269],
  [24, 0.696, 0.7364, 0.7508, 0.6094],
]

[table4]
pages = [2]
columns = ["id", "bus", "capacity"]
units_as_printed = ["id", "id", "kW"]
rows = [
  [1, 4, 263.5],
  [2, 13, 395.0],
  [3, 22, 395.0],
  [4, 27, 197.5],
  [5, 31, 461.0],
]

[table5]
pages = [3]
columns = ["hour", "day1", "day2", "day3", "day4"]
units_as_printed = ["hour", "p.u.", "p.u.", "p.u.", "p.u."]
rows = [
  [1, 0.0, 0.0, 0.0, 0.0],
  [2, 0.0, 0.0, 0.0, 0.0],
  [3, 0.0, 0.0, 0.0, 0.0],
  [4, 0.0, 0.0, 0.0, 0.0],
  [5, 0.0, 0.0, 0.0, 0.0],
  [6, 0.0, 0.0, 0.0, 0.0],
  [7, 0.1495, 0.1309, 0.1545, 0.1497],
  [8, 0.4539, 0.4829, 0.4907, 0.4471],
  [9, 0.7976, 0.7449, 0.7228, 0.7925],
  [10, 0.8365, 0.7433, 0.8568, 0.8111],
  [11, 0.8365, 0.9471, 0.9049, 0.805],
  [12, 0.5854, 0.6032, 0.5801, 0.5447],
  [13, 0.632, 0.6173, 0.6019, 0.6579],
  [14, 0.71, 0.6858, 0.6483, 0.6458],
  [15, 0.9526, 0.9114, 0.7914, 1.0],
  [16, 0.77, 0.8474, 0.83, 0.8318],
  [17, 0.8675, 0.8602, 0.8063, 0.9632],
  [18, 0.8088, 0.7378, 0.8746, 0.7704],
  [19, 0.5153, 0.5726, 0.5725, 0.5068],
  [20, 0.3538, 0.3563, 0.3661, 0.3291],
  [21, 0.0, 0.0, 0.0, 0.0],
  [22, 0.0, 0.0, 0.0, 0.0],
  [23, 0.0, 0.0, 0.0, 0.0],
  [24, 0.0, 0.0, 0.0, 0.0],
]

[table6]
pages = [3]
columns = ["id", "bus", "capacity"]
units_as_printed = ["id", "id", "kW"]
rows = [
  [1, 7, 253.0],
  [2, 11, 184.0],
  [3, 17, 276.5],
  [4, 19, 138.0],
  [5, 25, 322.5],
]

[table7]
pages = [3]
columns = ["FCS", "BESS", "onsite_PV"]
units_as_printed = ["kW", "kW_as_printed", "kW"]
rows = [
  [200.0, 40.0, 60.0],
]

[table8]
pages = [3, 4]
columns = ["hour", "day1", "day2", "day3", "day4"]
units_as_printed = ["hour", "not_printed_in_table", "not_printed_in_table", "not_printed_in_table", "not_printed_in_table"]
rows = [
  [1, 2194.56, 2395.75, 2073.62, 2270.24],
  [2, 2318.93, 2516.61, 2239.78, 2492.41],
  [3, 2179.02, 2129.65, 2091.06, 2038.34],
  [4, 2390.44, 2165.43, 2199.35, 2403.66],
  [5, 2723.11, 2564.21, 2650.42, 2436.52],
  [6, 3857.93, 3596.55, 4542.53, 3680.43],
  [7, 4013.38, 3885.87, 3662.91, 3951.7],
  [8, 4168.84, 4161.07, 3971.99, 4962.07],
  [9, 4231.02, 4260.52, 4735.59, 4936.19],
  [10, 4308.75, 4327.83, 4294.56, 3941.05],
  [11, 4595.23, 4124.76, 4178.37, 5037.7],
  [12, 4712.93, 5124.41, 4902.02, 4920.1],
  [13, 4977.2, 4570.9, 5217.84, 4819.68],
  [14, 4782.88, 5451.13, 5019.09, 4628.25],
  [15, 4184.38, 4594.85, 4774.17, 4472.51],
  [16, 3857.93, 4003.67, 3492.06, 3442.31],
  [17, 4161.06, 4013.64, 3833.31, 4527.05],
  [18, 4122.2, 4178.1, 3610.7, 4421.45],
  [19, 3811.29, 3787.13, 3884.27, 3606.98],
  [20, 3307.62, 2915.05, 3411.45, 3372.55],
  [21, 2793.06, 3158.99, 2579.75, 2775.14],
  [22, 2629.84, 2623.2, 2476.2, 2701.17],
  [23, 2468.16, 2312.76, 2464.55, 2247.3],
  [24, 2381.11, 2560.89, 2391.62, 2246.39],
]

[table9]
pages = [4]
columns = ["device", "upper", "lower", "ramp", "charge_efficiency", "discharge_efficiency"]
units_as_printed = ["name", "kW", "kW", "kWh_as_printed", "ratio", "ratio"]
rows = [
  ["FCS", 200.0, 0.0, "/", "/", "/"],
  ["BESS", 40.0, 0.0, 20.0, 0.95, 0.9],
  ["Onsite PV", 60.0, 0.0, "/", "/", "/"],
]

[table10]
pages = [4]
columns = ["Pbu_upper", "V_upper", "V_lower", "V_hat", "tan_phi", "Sw", "reactive_factor", "gamma1_gamma2"]
units_as_printed = ["kW", "not_printed", "not_printed", "not_printed", "ratio", "not_printed", "ratio", "ratio"]
rows = [
  [4800.0, 1.05, 0.93, 1.03, 0.2, 468.0, 0.3, 0.24],
]

[table11]
pages = [4]
columns = ["from_bus", "to_bus", "r", "x", "active_capacity"]
units_as_printed = ["id", "id", "not_printed", "not_printed", "kW"]
rows = [
  [1, 2, 0.0922, 0.047, 3047.13],
  [2, 3, 0.493, 0.2511, 2549.4],
  [3, 4, 0.366, 0.1864, 2164.76],
  [4, 5, 0.3811, 0.1941, 2668.01],
  [5, 6, 0.819, 0.707, 2457.81],
  [6, 7, 0.1872, 0.6188, 2300.48],
  [7, 8, 0.7114, 0.2351, 2048.59],
  [8, 9, 1.03, 0.74, 2966.33],
  [9, 10, 1.044, 0.74, 2688.23],
  [10, 11, 0.1966, 0.065, 2851.36],
  [11, 12, 0.3744, 0.1238, 2355.47],
  [12, 13, 1.468, 1.155, 2705.91],
  [13, 14, 0.5416, 0.7129, 2541.76],
  [14, 15, 0.591, 0.526, 2520.55],
  [15, 16, 0.7463, 0.545, 2286.02],
  [16, 17, 1.289, 1.721, 2613.39],
  [17, 18, 0.732, 0.574, 2402.82],
  [2, 19, 0.164, 0.1565, 2596.22],
  [19, 20, 1.5042, 1.3554, 2438.83],
  [20, 21, 0.4095, 0.4784, 2673.81],
  [21, 22, 0.7089, 0.9373, 2590.52],
  [3, 23, 0.4512, 0.3083, 2336.64],
  [23, 24, 0.898, 0.7091, 2808.84],
  [24, 25, 0.896, 0.7011, 2707.61],
  [6, 26, 0.203, 0.1034, 2543.83],
  [26, 27, 0.2842, 0.1447, 2296.86],
  [27, 28, 1.059, 0.9337, 2302.25],
  [28, 29, 0.8042, 0.7006, 2497.54],
  [29, 30, 0.5075, 0.2585, 2507.18],
  [30, 31, 0.9744, 0.963, 2243.74],
  [31, 32, 0.3105, 0.3619, 2413.65],
  [32, 33, 0.341, 0.5302, 2596.15],
  [21, 8, 2.0, 2.0, 2379.71],
  [9, 15, 2.0, 2.0, 2427.5],
  [12, 22, 2.0, 2.0, 2767.34],
  [18, 33, 0.5, 0.5, 2756.41],
  [25, 29, 0.5, 0.5, 2776.44],
]
"""
const HASH_TABLES = "70b9f1b02a0b4ff2e0944cbbb84f483eaf0dbcf723e88169e7005d0789ab2833"

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


# خطای داده باید روشن و فوری باشد؛ هیچ مقدار پیش‌فرضی جایگزین دادهٔ مفقود نمی‌شود.
function demand(condition::Bool, message::String)
    condition || throw(ArgumentError(message))
end

# اثر انگشت فایل‌های داده، تغییر ناخواستهٔ ورودی پس از استخراج را آشکار می‌کند.
function verify_checksums(root)
    # ورودی‌ها در همین فایل‌اند؛ هیچ پوشهٔ data یا فایل همراه خوانده نمی‌شود.
    for (name, payload, expected) in (("tables", DATA_TABLES, HASH_TABLES),
                                     ("case", DATA_CASE, HASH_CASE),
                                     ("sources", DATA_SOURCES, HASH_SOURCES))
        demand(bytes2hex(sha256(payload)) == expected, "دادهٔ درون فایل تغییر کرده است: $name")
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

# خوانندهٔ دادهٔ مستند همین فایل؛ هیچ داده‌ای از کد نسخهٔ ۱۹ خوانده نمی‌شود.
function load_case(root=@__DIR__)
    verify_checksums(root)
    data = TOML.parse(DATA_TABLES)
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
    report=Dict("step"=>"S01", "input_validation"=>"passed", "optimization_run"=>false,
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


# اجرای مستقیم هم در PowerShell و هم با include در Julia.
# این فراخوانی در سطح بالاست تا مشکل world age در Julia جدید ایجاد نشود.
REVCSStandaloneS01.run(@__DIR__, joinpath(@__DIR__, "results_S01"))
println("مسیر خروجی: ", joinpath(@__DIR__, "results_S01"))
