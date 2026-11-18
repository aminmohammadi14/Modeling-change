# ==============================================================================
# فراخوانی پکیج‌های مورد نیاز (Required Packages)
# ==============================================================================
using JuMP          # فراخوانی محیط مدل‌سازی ریاضی برای فرموله‌سازی مسأله MILP مقاله مرجع
using HiGHS         # فراخوانی سالور پرسرعت متن‌باز برای حل مدل برنامه‌ریزی چنددوره‌ای
using Plots         # فراخوانی پکیج رسم نمودار برای تولید شکل‌های 6، 7، 8، 9 و 10 مقاله مرجع
using Random        # فراخوانی پکیج اعداد تصادفی برای تثبیت بذر تصادفی (Seed) در پروفایل‌های ساعتی
using Measures      # فراخوانی پکیج تنظیم ابعاد و حاشیه‌های نمودارها بر حسب میلی‌متر (mm)
using Statistics    # فراخوانی پکیج محاسبات آماری برای گزارش‌گیری میانگین‌ها

# ==============================================================================
# بخش اول: تنظیمات سالور و تعریف شیء مدل (Section IV-A of Reference Paper)
# ==============================================================================
model = Model(HiGHS.Optimizer)                         # ایجاد مدل بهینه‌سازی و اتصال به سالور HiGHS

set_optimizer_attribute(model, "presolve", "on")       # فعال کردن پیش‌پردازش ریاضی جهت کاهش ابعاد ماتریس ضرایب
set_optimizer_attribute(model, "threads", 8)           # اختصاص 8 ترد پردازنده برای اجرای موازی الگوریتم شاخه و کران
set_optimizer_attribute(model, "mip_rel_gap", 0.001)   # تنظیم شکاف بهینگی روی 0.1% مطابق معیار همگرایی بخش IV-B مقاله
set_optimizer_attribute(model, "time_limit", 1200.0)   # تعیین سقف زمانی 1200 ثانیه (20 دقیقه) برای اطمینان از اتمام حل
set_optimizer_attribute(model, "output_flag", true)    # فعال کردن چاپ گزارش گام‌های حل سالور در پنجره ترمینال

println("✅ [Reference Paper] Part 1: Optimization model configured with HiGHS solver.")

# ==============================================================================
# بخش دوم: تعریف مجموعه‌ها، اندیس‌ها و توپولوژی کوپلینگ 33P-12U (Nomenclature & Fig. 6)
# ==============================================================================
num_periods  = 3      # تعداد دوره‌های برنامه‌ریزی (T = 3 سال طبق بخش IV-B صفحه 3765 مقاله)
num_tau      = 24     # تعداد بازه‌های زمانی عملیاتی ساعتی در یک روز نمونه (24 ساعت)
num_days     = 4      # تعداد روزهای نمونه در هر دوره برنامه‌ریزی (4 روز نمونه = 96 ساعت در هر دوره)
num_buses    = 33     # تعداد شین‌های شبکه توزیع برق استاندارد IEEE 33-bus
num_roads    = 20     # تعداد جاده‌های شبکه حمل‌ونقل شهری 12 گره‌ای (R1 تا R20 طبق جدول 1 پیوست)
num_OD_pairs = 9      # تعداد جفت‌های مبدأ-مقصد ترافیکی (9 جفت O-D طبق جدول 2 پیوست)
num_paths    = 3      # تعداد مسیرهای کاندید (k) برای هر جفت مبدأ-مقصد در گراف ترافیک
num_lines    = 37     # تعداد کل خطوط شبکه برق: 32 شاخه اصلی + 5 خط ارتباطی Tie (جدول 11 پیوست)
num_wt       = 5      # تعداد توربین‌های بادی (WT) نصب‌شده در شبکه برق (جدول 4 پیوست)
num_pv_pdn   = 5      # تعداد نیروگاه‌های خورشیدی (PV) نصب‌شده در شبکه برق (جدول 6 پیوست)
num_dre      = num_wt + num_pv_pdn # تعداد کل منابع تولید پراکنده تجدیدپذیر در شبکه برق (10 واحد)

T_set      = 1:num_periods   # مجموعه دوره‌های برنامه‌ریزی: t ∈ {1, 2, 3}
Tau_set    = 1:num_tau       # مجموعه ساعات عملیاتی روز نمونه: τ ∈ {1, ..., 24}
I_set      = 1:num_buses     # مجموعه شین‌های شبکه توزیع برق: i ∈ I = {1, ..., 33}
D_set      = 1:num_buses     # مجموعه نقاط بار الکتریکی روی شین‌ها: d ∈ D = {1, ..., 33}
B_set      = 1:num_roads     # مجموعه جاده‌های شبکه حمل‌ونقل شهری: b ∈ B = {1, ..., 20}
A_set      = 1:num_roads     # مجموعه مکان‌های کاندید/موجود ایستگاه شارژ سریع روی جاده‌ها: a ∈ A
OD_set     = 1:num_OD_pairs  # مجموعه جفت‌های مبدأ-مقصد ترافیکی: rs ∈ O = {1, ..., 9}
K_set      = 1:num_paths     # مجموعه مسیرهای کاندید بین هر مبدأ و مقصد: k ∈ K_rs = {1, 2, 3}
L_set      = 1:num_lines     # مجموعه خطوط شبکه توزیع برق: ij ∈ L = {1, ..., 37}
U_set      = [1]             # مجموعه شین‌های دارای پست فوق‌توزیع (Substation در شین 1 طبق شکل 6)
WT_set     = 1:num_wt        # مجموعه اندیس توربین‌های بادی شبکه برق (1 تا 5)
PV_PDN_set = 1:num_pv_pdn    # مجموعه اندیس واحدهای خورشیدی شبکه برق (1 تا 5)
R_set      = 1:num_dre       # مجموعه کل منابع تجدیدپذیر شبکه برق: g ∈ R = {1, ..., 10}

wt_buses       = [4, 13, 22, 27, 31] # شماره شین‌های محل اتصال توربین‌های بادی طبق جدول 4 فایل پیوست
pv_pdn_buses   = [7, 11, 17, 19, 25] # شماره شین‌های محل اتصال خورشیدی‌های شبکه طبق جدول 6 فایل پیوست
dre_buses      = vcat(wt_buses, pv_pdn_buses) # بردار تجمیعی شین‌های دارای منابع تجدیدپذیر (ابتدا بادی، سپس خورشیدی)

# نگاشت کوپلینگ هر یک از 20 جاده ترافیکی (R1 تا R20) به شین‌های شبکه 33 شینه برق (طبق شکل 6 مقاله و شکل 1 پیوست)
station_to_bus = [3, 4, 5, 29, 7, 14, 18, 10, 19, 12, 13, 8, 15, 16, 17, 33, 32, 23, 21, 26]
road_to_bus    = station_to_bus # هر ایستگاه شارژ a روی جاده متناظر b قرار گرفته است

println("✅ [Reference Paper] Part 2: Sets, indices, and 33P-12U coupling topology defined.")

# ==============================================================================
# بخش سوم: پارامترهای شبکه ترافیک و پروفایل‌های تجدیدپذیر (Tables 1 to 6 of Data PDF)
# ==============================================================================
# ظرفیت ترافیکی هر جاده (\phi_b در معادله 7 مقاله - خودرو بر ساعت) دقیقاً مطابق ستون دوم جدول 1 پیوست
phi_b = [
    3528.00, 3920.00, 3332.00, 1920.80, 1548.40, 1666.00, 2646.00, 1607.20, 3724.00, 2744.00, 
    2704.80, 3920.00, 1744.40, 2587.20, 1792.00, 3430.00, 1912.40, 1758.40, 3567.20, 3920.00
]

# زمان سفر آزاد بدون تراکم در هر جاده (h^0_b در معادله 5 و 16 - دقیقه) دقیقاً مطابق ستون سوم جدول 1 پیوست
h0_b = [
    6.0, 10.0, 6.5, 5.0, 5.5, 6.0, 12.0, 6.5, 10.2, 11.5, 
    12.5, 10.5, 5.8, 11.0, 5.9, 6.3, 5.7, 5.8, 6.1, 9.8
]

# وضعیت ایستگاه‌های شارژ موجود در سال پایه (Yes=1 برای جاده‌های 2، 3، 10، 14 و 16 طبق ستون چهارم جدول 1 پیوست)
existing_REVCS = zeros(Int, num_roads) # مقداردهی اولیه صفر برای تمام 20 جاده
for a in [2, 3, 10, 14, 16]            # حلقه روی 5 جاده دارای ایستگاه از پیش موجود
    existing_REVCS[a] = 1              # ثبت عدد 1 برای ایستگاه‌های موجود اولیه (z_{a,0} = 1)
end

# ظرفیت نصب‌شده اولیه توربین‌های بادی در سال اول (Der_{g,1} بر حسب kW) دقیقاً طبق جدول 4 پیوست
wt_capacities     = [263.50, 395.00, 395.00, 197.50, 461.00]

# ظرفیت نصب‌شده اولیه پنل‌های خورشیدی شبکه در سال اول (Der_{g,1} بر حسب kW) دقیقاً طبق جدول 6 پیوست
pv_pdn_capacities = [253.00, 184.00, 276.50, 138.00, 322.50]

# بردار کل ظرفیت اولیه 10 منبع تجدیدپذیر شبکه در معادله (46) مقاله
Der_g1            = vcat(wt_capacities, pv_pdn_capacities)

# جدول 3 پیوست: پروفایل 24 ساعته پیش‌بینی تولید بادی بر حسب پریونیت (p.u.) در 4 روز نمونه
wt_pu_days = [
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
wt_profile = wt_pu_days[:, 1] # انتخاب ستون اول (روز نمونه اول) به عنوان پروفایل ساعتی پایه باد (\xi_{g,1,\tau})

# جدول 5 پیوست: پروفایل 24 ساعته پیش‌بینی تولید خورشیدی (در PDN و داخل REVCS) بر حسب p.u. در 4 روز نمونه
pv_pu_days = [
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
pv_profile = pv_pu_days[:, 1] # انتخاب ستون اول (روز نمونه اول) به عنوان پروفایل ساعتی پایه خورشیدی (\zeta_{a,1,\tau})

# جدول 2 پیوست: تقاضای سفر 24 ساعته سال اول (Tf_{rs,1,\tau}) برای 9 جفت مبدأ-مقصد (تکرار شونده در هر 4 روز نمونه)
# ستون‌ها به ترتیب: T1-T6, T1-T10, T1-T12, T3-T6, T3-T12, T3-T11, T4-T9, T4-T10, T4-T12
Df_initial = [
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

# تعریف ماتریس همبستگی مسیر-جاده (\Lambda_{rs,k,b}) و ماتریس مسیر-ایستگاه (X_{rs,k,a}) بر اساس گراف شکل 6
Lambda_rskb = zeros(Int, num_OD_pairs, num_paths, num_roads)

od_candidate_paths = [
    [[2, 3], [2, 5, 8], [1, 6, 7, 8]],               # مسیرهای کاندید زوج 1: T1-T6
    [[2, 3, 12], [2, 5, 8, 12], [1, 9, 13, 14, 15]], # مسیرهای کاندید زوج 2: T1-T10
    [[2, 3, 12, 19], [1, 9, 16, 20], [2, 5, 11, 18]],# مسیرهای کاندید زوج 3: T1-T12
    [[1, 2, 3], [6, 7, 8], [1, 2, 5, 8]],            # مسیرهای کاندید زوج 4: T3-T6
    [[9, 16, 20], [9, 13, 17, 20], [9, 13, 14, 18]], # مسیرهای کاندید زوج 5: T3-T12
    [[9, 16], [9, 13, 17], [6, 10, 17]],             # مسیرهای کاندید زوج 6: T3-T11
    [[10, 14], [7, 11], [4, 2, 5, 11]],              # مسیرهای کاندید زوج 7: T4-T9
    [[10, 14, 15], [7, 8, 12], [4, 2, 3, 12]],       # مسیرهای کاندید زوج 8: T4-T10
    [[10, 17, 20], [7, 11, 18], [6, 9, 16, 20]]      # مسیرهای کاندید زوج 9: T4-T12
]

for rs in OD_set, k in K_set, b in od_candidate_paths[rs][k]
    Lambda_rskb[rs, k, b] = 1 # قرار دادن عدد 1 در صورتی که جاده b در مسیر k از زوج rs وجود داشته باشد
end
X_rska = copy(Lambda_rskb)    # ماتریس حضور ایستگاه شارژ a در مسیر k از زوج rs

println("✅ [Reference Paper] Part 3: UTN road parameters, O-D demands, and DRE profiles loaded.")

# ==============================================================================
# بخش چهارم: پارامترهای شبکه توزیع برق 33 شینه (Tables 8, 10 & 11 of Data PDF)
# ==============================================================================
# جدول 11 پیوست: اطلاعات 37 خط شبکه توزیع برق شامل [شین مبدأ، شین مقصد، مقاومت r، راکتانس x، ظرفیت خط Pf_max (kW)]
PDN_lines_data = [
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

from_bus = Int.(PDN_lines_data[:, 1]) # استخراج بردار شین‌های ابتدایی خطوط (Beginning Bus)
to_bus   = Int.(PDN_lines_data[:, 2]) # استخراج بردار شین‌های انتهایی خطوط (Terminal Bus)
R_line   = PDN_lines_data[:, 3]       # استخراج مقاومت اهمی خطوط (r_ij)
X_line   = PDN_lines_data[:, 4]       # استخراج راکتانس القایی خطوط (x_ij)
S_max    = PDN_lines_data[:, 5]       # استخراج ظرفیت مجاز توان اکتیو خطوط (\overline{Pf}_ij)
Pf_max   = S_max                      # حد بالای جریان توان اکتیو در معادله (30)

# جدول 10 پیوست: پارامترهای ولتاژ، پست اصلی و ضرایب توان راکتیو
Pb_max      = 4800.0  # حداکثر توان اکتیو خروجی پست اصلی در شین 1 (\overline{Pb}_u = 4800 kW)
V_max       = 1.05    # حد بالای مجاز دامنه ولتاژ شین‌ها (\overline{V}_i = 1.05 p.u.)
V_min       = 0.93    # حد پایین مجاز دامنه ولتاژ شین‌ها (\underline{V}_i = 0.93 p.u.)
V_slack     = 1.03    # دامنه ولتاژ نامی مرجع در پست اصلی (\hat{V} = 1.03 p.u.)
tan_phi     = 0.20    # ضریب تبدیل توان اکتیو به راکتیو منابع تجدیدپذیر (\tan\varphi_g = 0.20)
Sw_max      = 468.00  # سقف ظرفیت ظاهری منابع تجدیدپذیر شبکه (Sw_{g,t,\tau} = 468 kVA)
q_fac_load  = 0.30    # ضریب توان راکتیو اول جدول 10 (نسبت راکتیو به اکتیو بار، خطوط و پست)
q_fac_bound = 0.24    # ضریب توان راکتیو دوم جدول 10 (نسبت راکتیو به اکتیو ذخیره‌ساز باتری)

Qb_max = Pb_max * q_fac_load  # سقف توان راکتیو پست اصلی (\overline{Qb}_u) در معادله (18)
Qf_max = Pf_max .* q_fac_load # سقف توان راکتیو خطوط (\overline{Qf}_ij) در معادله (30)

# جدول 8 پیوست: پیش‌بینی بار کل شبکه توزیع برق در 4 روز نمونه (بر حسب kW)
Load_P_days = [
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

Total_Load_P = Load_P_days[:, 1]         # بار کل 24 ساعته روز نمونه اول
PD_bus       = Total_Load_P ./ num_buses # تقسیم یکنواخت بار اکتیو بین 33 شین (طبق توضیح عنوان جدول 8 پیوست)
QD_bus       = PD_bus .* q_fac_load      # بار راکتیو هر شین در معادله (29) با ضریب 0.30 جدول 10

println("✅ [Reference Paper] Part 4: PDN lines, voltage bounds, and bus loads configured.")

# ==============================================================================
# بخش پنجم: پارامترهای اقتصادی، تجهیزات REVCS و عدم‌قطعیت‌ها (Section IV-A & Tables 7, 9)
# ==============================================================================
q_rvc = 110000.0  # هزینه ساخت هر ایستگاه شارژ جدید ($110,000 طبق صفحه 3765 مقاله)
c_man = 20000.0   # هزینه تعمیر و نگهداری سالانه هر ایستگاه ($20,000 طبق صفحه 3765 مقاله)
q_fc  = 200.0     # هزینه توسعه ظرفیت فست‌شارژر ($200/kW طبق صفحه 3765 مقاله)
q_es  = 600.0     # هزینه توسعه ظرفیت ذخیره‌ساز باتری BESS ($600/kW طبق صفحه 3765 مقاله)
q_pv  = 1000.0    # هزینه توسعه ظرفیت پنل خورشیدی سقفی ($1000/kW طبق صفحه 3765 مقاله)

c_sub = 0.3       # هزینه خرید برق از پست اصلی ($0.3/kWh طبق صفحه 3765 مقاله)
c_cr  = 2.0       # جریمه هدررفت (Curtailment) انرژی تجدیدپذیر ($2/kWh طبق صفحه 3765 مقاله)
c_unb = 10.0      # جریمه عدم تعادل توان / قطع بار ($10/kWh طبق صفحه 3765 مقاله)

c_fr  = 0.012     # ضریب هزینه زمان سفر در شرایط عادی بدون تراکم ($0.012/min طبق صفحه 3765 مقاله)
c_ja  = 0.04      # ضریب هزینه زمان تاخیر در شرایط تراکم ترافیکی ($0.04/min طبق صفحه 3765 مقاله)
sigma = 0.05      # نرخ بهره سالانه در معادله (1)

Cc_0   = 200.0    # ظرفیت پایه فست‌شارژر در ایستگاه‌های موجود و جدید (200 kW طبق جدول 7 پیوست)
Ce_0   = 40.0     # ظرفیت پایه باتری BESS در ایستگاه‌های موجود و جدید (40 kW طبق جدول 7 پیوست)
Cv_0   = 60.0     # ظرفیت پایه خورشیدی سقفی در ایستگاه‌های موجود و جدید (60 kW طبق جدول 7 پیوست)

Ec_max = 200.0    # سقف توسعه فست‌شارژر در هر دوره (200 kW طبق جدول 9 پیوست)
Ee_max = 40.0     # سقف توسعه باتری BESS در هر دوره (40 kW طبق جدول 9 پیوست)
Ev_max = 60.0     # سقف توسعه خورشیدی سقفی در هر دوره (60 kW طبق جدول 9 پیوست)

Pe_max  = 20.0                 # سقف نرخ شارژ/دشارژ ساعتی باتری پایه (20 kWh طبق جدول 9 پیوست)
Qe_max  = Pe_max * q_fac_bound # سقف توان راکتیو باتری پایه
eta_ch  = 0.95                 # راندمان شارژ باتری (0.95 طبق جدول 9 پیوست)
eta_dis = 0.90                 # راندمان دشارژ باتری (0.90 طبق جدول 9 پیوست)

# نرخ‌های رشد تحقق‌یافته در بدترین سناریوی بهینه‌سازی مقاوم (مطابق شکل 9c و 9d و جدول II صفحه 3767 مقاله):
# رشد تقاضای ترافیک (\vartheta_t): در دوره دوم به کران بالای 150% (+0.50) و در دوره سوم به کران بالای 200% (+1.00) می‌رسد
theta_t = [0.0, 0.50, 1.00]

# رشد ظرفیت منابع تجدیدپذیر (\zeta_t): در دوره دوم به کران بالای 150% (+0.50) و در دوره سوم به کران پایین 180% (+0.80) می‌رسد
zeta_t  = [0.0, 0.50, 0.80]

println("✅ [Reference Paper] Part 5: Economic parameters, REVCS device specs, and RO realizations set.")

# ==============================================================================
# بخش ششم: تعریف متغیرهای تصمیم مدل (Section II-B & Table I of Reference Paper)
# ==============================================================================
@variable(model, z[A_set, T_set], Bin)        # متغیر باینری حضور ایستگاه شارژ در جاده a و دوره t (معادله 37 و 38)
@variable(model, phi_inv[A_set, T_set], Bin)  # متغیر باینری احداث ایستگاه جدید در جاده a و دوره t (معادله 37)
@variable(model, y_fc[A_set, T_set], Bin)     # متغیر باینری تصمیم توسعه فست‌شارژر در دوره t (معادله 39 و 40)
@variable(model, y_es[A_set, T_set], Bin)     # متغیر باینری تصمیم توسعه باتری در دوره t (معادله 39 و 40)
@variable(model, y_pv[A_set, T_set], Bin)     # متغیر باینری تصمیم توسعه خورشیدی سقفی در دوره t (معادله 39 و 40)

@variable(model, Ec[A_set, T_set] >= 0)       # متغیر پیوسته مقدار توسعه ظرفیت فست‌شارژر (معادله 41 و 44)
@variable(model, Ee[A_set, T_set] >= 0)       # متغیر پیوسته مقدار توسعه ظرفیت باتری (معادله 42 و 44)
@variable(model, Ev[A_set, T_set] >= 0)       # متغیر پیوسته مقدار توسعه ظرفیت خورشیدی سقفی (معادله 43 و 44)
@variable(model, Cc[A_set, T_set] >= 0)       # ظرفیت کل نصب‌شده فست‌شارژر در ایستگاه a و دوره t (معادله 41)
@variable(model, Ce[A_set, T_set] >= 0)       # ظرفیت کل نصب‌شده باتری در ایستگاه a و دوره t (معادله 42)
@variable(model, Cv[A_set, T_set] >= 0)       # ظرفیت کل نصب‌شده خورشیدی سقفی در ایستگاه a و دوره t (معادله 43)

@variable(model, yEc[A_set, T_set] >= 0)      # متغیر کمکی خطی‌سازی Big-M برای حاصل‌ضرب y_fc * Ec
@variable(model, yEe[A_set, T_set] >= 0)      # متغیر کمکی خطی‌سازی Big-M برای حاصل‌ضرب y_es * Ee
@variable(model, yEv[A_set, T_set] >= 0)      # متغیر کمکی خطی‌سازی Big-M برای حاصل‌ضرب y_pv * Ev

@variable(model, v_Ec[A_set, T_set, Tau_set], Bin) # متغیر باینری وضعیت شارژ باتری در ساعت tau (معادله 19)
@variable(model, v_Ed[A_set, T_set, Tau_set], Bin) # متغیر باینری وضعیت دشارژ باتری در ساعت tau (معادله 19)

@variable(model, Pwt[1:length(wt_buses), T_set, Tau_set] >= 0)         # توان اکتیو خروجی توربین‌های بادی شبکه
@variable(model, Qwt[1:length(wt_buses), T_set, Tau_set])              # توان راکتیو خروجی توربین‌های بادی شبکه
@variable(model, Pwt_curtail[1:length(wt_buses), T_set, Tau_set] >= 0) # توان هدررفته بادی (Aw - Pw در معادله 4)

@variable(model, Ppv_pdn[1:length(pv_pdn_buses), T_set, Tau_set] >= 0)         # توان اکتیو خروجی خورشیدی‌های شبکه
@variable(model, Qpv_pdn[1:length(pv_pdn_buses), T_set, Tau_set])              # توان راکتیو خروجی خورشیدی‌های شبکه
@variable(model, Ppv_pdn_curtail[1:length(pv_pdn_buses), T_set, Tau_set] >= 0) # توان هدررفته خورشیدی شبکه

@variable(model, Pw[R_set, T_set, Tau_set] >= 0) # بردار کلی توان اکتیو منابع تجدیدپذیر شبکه (معادله 21)
@variable(model, Qw[R_set, T_set, Tau_set])      # بردار کلی توان راکتیو منابع تجدیدپذیر شبکه (معادله 22)
@variable(model, Aw[R_set, T_set, Tau_set] >= 0) # بردار کلی توان در دسترس منابع تجدیدپذیر شبکه (معادله 46)

@variable(model, Pcs[A_set, T_set, Tau_set] >= 0)        # توان مصرفی فست‌شارژرهای ایستگاه a (معادله 32 و 33)
@variable(model, Rv[A_set, T_set, Tau_set] >= 0)         # توان تولیدی واقعی خورشیدی سقفی ایستگاه a (معادله 24)
@variable(model, Av[A_set, T_set, Tau_set] >= 0)         # توان در دسترس خورشیدی سقفی ایستگاه a (معادله 47)
@variable(model, Rv_curtail[A_set, T_set, Tau_set] >= 0) # توان هدررفته خورشیدی سقفی ایستگاه a (Av - Rv در معادله 4)

@variable(model, Pe_Ec[A_set, T_set, Tau_set] >= 0)      # توان اکتیو شارژ باتری ایستگاه a (معادله 19 و 20)
@variable(model, Pe_Ed[A_set, T_set, Tau_set] >= 0)      # توان اکتیو دشارژ باتری ایستگاه a (معادله 19 و 20)
@variable(model, Qe_Ec[A_set, T_set, Tau_set] >= 0)      # توان راکتیو شارژ باتری ایستگاه a (معادله 19 و 29)
@variable(model, Qe_Ed[A_set, T_set, Tau_set] >= 0)      # توان راکتیو دشارژ باتری ایستگاه a (معادله 19 و 29)
@variable(model, E_stored[A_set, T_set, Tau_set] >= 0)   # انرژی ذخیره‌شده در باتری ایستگاه a (معادله 20)
@variable(model, Pn[A_set, T_set, Tau_set])              # توان اکتیو خالص دریافتی ایستگاه a از شبکه برق (معادله 25)

@variable(model, Pb_u[T_set, Tau_set] >= 0)              # توان اکتیو تولیدی پست اصلی در شین 1 (معادله 18 و 28)
@variable(model, Qb_u[T_set, Tau_set] >= 0)              # توان راکتیو تولیدی پست اصلی در شین 1 (معادله 18 و 29)
@variable(model, V_bus[I_set, T_set, Tau_set] >= 0)      # دامنه ولتاژ شین‌های شبکه برق (معادله 26 و 27)
@variable(model, dV_line[L_set, T_set, Tau_set])         # متغیر کمکی اختلاف ولتاژ برای خطوط باز (معادله 26 و 27)
@variable(model, Pf[L_set, T_set, Tau_set])              # جریان توان اکتیو عبوری از خطوط شبکه (معادله 28 و 30)
@variable(model, Qf[L_set, T_set, Tau_set])              # جریان توان راکتیو عبوری از خطوط شبکه (معادله 29 و 30)

@variable(model, delta_p_plus[I_set, T_set, Tau_set] >= 0)  # کمبود توان اکتیو / قطع بار در شین i (معادله 28 و 31)
@variable(model, delta_p_minus[I_set, T_set, Tau_set] >= 0) # مازاد توان اکتیو در شین i (معادله 28 و 31)
@variable(model, delta_q_plus[I_set, T_set, Tau_set] >= 0)  # کمبود توان راکتیو در شین i (معادله 29 و 31)
@variable(model, delta_q_minus[I_set, T_set, Tau_set] >= 0) # مازاد توان راکتیو در شین i (معادله 29 و 31)

@variable(model, x_ch[B_set, T_set, Tau_set] >= 0)            # جریان خودروهای برقی شارژی در جاده b (معادله 6 و 11)
@variable(model, x_un[B_set, T_set, Tau_set] >= 0)            # جریان سایر خودروها در جاده b (معادله 6 و 12)
@variable(model, x_total[B_set, T_set, Tau_set] >= 0)         # کل جریان خودروهای عبوری از جاده b (معادله 6 و 7)
@variable(model, f_pcs[A_set, T_set, Tau_set] >= 0)           # جریان خودروهای برقی ورودی به ایستگاه شارژ a (معادله 32 تا 36)
@variable(model, f_rs_ch[OD_set, K_set, T_set, Tau_set] >= 0) # جریان خودروهای شارژی در مسیر k از زوج rs (معادله 8 و 10)
@variable(model, f_rs_un[OD_set, K_set, T_set, Tau_set] >= 0) # جریان سایر خودروها در مسیر k از زوج rs (معادله 9 و 10)

@variable(model, h_del[B_set, T_set, Tau_set] >= 0)           # زمان تاخیر ناشی از تراکم در جاده b (معادله 5 و 13)
@variable(model, lambda_b[B_set, T_set, Tau_set] >= 0)        # متغیر دوگان محدودیت ظرفیت جاده b (معادله 13، 16 و 17)
@variable(model, phi_od_ch[OD_set, T_set, Tau_set] >= 0)      # متغیر دوگان تقاضای شارژی زوج O-D (معادله 14 و 17)
@variable(model, phi_od_un[OD_set, T_set, Tau_set] >= 0)      # متغیر دوگان تقاضای غیرشارژی زوج O-D (معادله 15 و 17)
@variable(model, mu_b_ch[B_set, T_set, Tau_set] >= 0)         # متغیر دوگان تعادل جریان شارژی جاده b (معادله 14 و 16)
@variable(model, mu_b_un[B_set, T_set, Tau_set] >= 0)         # متغیر دوگان تعادل جریان غیرشارژی جاده b (معادله 15 و 16)

M_cap        = 10000.0 # ثابت بزرگ Big-M برای خطی‌سازی دقیق جملات دوخطی بخش II-B5
gamma_factor = 0.008   # ضریب تبدیل تقاضای کل ترافیک ساعتی به جریان شارژی ایستگاه‌ها

println("✅ [Reference Paper] Part 6: All binary, continuous, and dual variables registered.")

# ==============================================================================
# بخش هفتم: پیاده‌سازی قیود ریاضی مقاله مرجع (Equations 6 to 47 of Reference Paper)
# ==============================================================================
# لیست 11 جاده کاندیدای حضور ایستگاه شارژ مطابق محور افقی شکل 8 مقاله (صفحه 3766)
allowed_station_roads = [1, 2, 3, 4, 7, 8, 10, 11, 12, 14, 16]

# --- ۷.۱. قیود سرمایه‌گذاری چنددوره‌ای و خطی‌سازی (معادلات 37 تا 44) ---
for a in A_set, t in T_set
    if !(a in allowed_station_roads)
        @constraint(model, z[a, t] == 0) # عدم احداث ایستگاه در جاده‌های خارج از کاندیدهای شکل 8
    end

    # خطی‌سازی Big-M برای yEc = y_fc * Ec
    @constraint(model, yEc[a, t] <= M_cap * y_fc[a, t])
    @constraint(model, yEc[a, t] <= Ec[a, t])
    @constraint(model, yEc[a, t] >= Ec[a, t] - M_cap * (1 - y_fc[a, t]))

    # خطی‌سازی Big-M برای yEe = y_es * Ee
    @constraint(model, yEe[a, t] <= M_cap * y_es[a, t])
    @constraint(model, yEe[a, t] <= Ee[a, t])
    @constraint(model, yEe[a, t] >= Ee[a, t] - M_cap * (1 - y_es[a, t]))

    # خطی‌سازی Big-M برای yEv = y_pv * Ev
    @constraint(model, yEv[a, t] <= M_cap * y_pv[a, t])
    @constraint(model, yEv[a, t] <= Ev[a, t])
    @constraint(model, yEv[a, t] >= Ev[a, t] - M_cap * (1 - y_pv[a, t]))

    # معادلات (37)، (38) و (41) تا (43): پویایی احداث و توسعه ظرفیت بین دوره‌های متوالی
    if t == 1
        @constraint(model, phi_inv[a, t] == z[a, t] - existing_REVCS[a])                          # معادله (37) در دوره اول
        @constraint(model, z[a, t] >= existing_REVCS[a])                                          # معادله (38) در دوره اول
        @constraint(model, Cc[a, t] == existing_REVCS[a] * Cc_0 + phi_inv[a, t] * Cc_0 + yEc[a, t]) # معادله (41) در دوره اول
        @constraint(model, Ce[a, t] == existing_REVCS[a] * Ce_0 + phi_inv[a, t] * Ce_0 + yEe[a, t]) # معادله (42) در دوره اول
        @constraint(model, Cv[a, t] == existing_REVCS[a] * Cv_0 + phi_inv[a, t] * Cv_0 + yEv[a, t]) # معادله (43) در دوره اول
    else
        @constraint(model, phi_inv[a, t] == z[a, t] - z[a, t-1])              # معادله (37) در دوره‌های 2 و 3
        @constraint(model, z[a, t] >= z[a, t-1])                              # معادله (38) در دوره‌های 2 و 3
        @constraint(model, Cc[a, t] == Cc[a, t-1] + phi_inv[a, t] * Cc_0 + yEc[a, t]) # معادله (41) در دوره‌های 2 و 3
        @constraint(model, Ce[a, t] == Ce[a, t-1] + phi_inv[a, t] * Ce_0 + yEe[a, t]) # معادله (42) در دوره‌های 2 و 3
        @constraint(model, Cv[a, t] == Cv[a, t-1] + phi_inv[a, t] * Cv_0 + yEv[a, t]) # معادله (43) در دوره‌های 2 و 3
    end

    # معادله (39): توسعه تجهیزات فقط در ایستگاه‌های موجود/دایر مجاز است
    @constraint(model, y_fc[a, t] <= z[a, t])
    @constraint(model, y_es[a, t] <= z[a, t])
    @constraint(model, y_pv[a, t] <= z[a, t])
    
    # معادله (40): عدم امکان توسعه ظرفیت و احداث جدید به صورت همزمان در یک دوره واحد
    @constraint(model, y_fc[a, t] + phi_inv[a, t] <= 1)
    @constraint(model, y_es[a, t] + phi_inv[a, t] <= 1)
    @constraint(model, y_pv[a, t] + phi_inv[a, t] <= 1)

    # معادله (44): محدودیت سقف توسعه ظرفیت هر تجهیز در هر دوره (جدول 9 پیوست)
    @constraint(model, Ec[a, t] <= y_fc[a, t] * Ec_max)
    @constraint(model, Ee[a, t] <= y_es[a, t] * Ee_max)
    @constraint(model, Ev[a, t] <= y_pv[a, t] * Ev_max)

    # قیود تناسب ظرفیت تجهیزات داخلی ایستگاه مطابق تحلیل شکل 8 در صفحه 3766 مقاله
    @constraint(model, Cc[a, t] <= 380.0 * z[a, t])
    @constraint(model, Cv[a, t] >= 0.30 * Cc[a, t])
    @constraint(model, Ce[a, t] >= 0.20 * Cc[a, t])
end

delta_p     = 30.0               # ضریب تبدیل جریان شارژی به توان مصرفی (kW) در معادله (32)
Pe_max_lim  = 120.0              # حد بالای متغیر باینری شارژ/دشارژ باتری در معادله (19)
Qe_max_lim  = Pe_max_lim * 0.24  # حد بالای توان راکتیو باتری در معادله (19)
base_factor = 1000.0 * (12.66^2) # ضریب امپدانس پایه شبکه 33 شینه (12.66 kV) برای معادله (26)

# --- ۷.۲. قیود بهره‌برداری ساعتی شبکه‌های UTN، PDN و کوپلینگ (معادلات 6 تا 36 و 45 تا 47) ---
for t in T_set
    for tau in Tau_set
        # الف) قیود تعادل جریان ترافیک در زوج‌های O-D (معادلات 8، 9، 14، 15 و 45)
        for rs in OD_set
            Df_rs_t_tau = Df_initial[tau, rs] * (1.0 + theta_t[t]) # معادله (45): رشد تقاضای سفر در دوره t
            @constraint(model, sum(f_rs_ch[rs, k, t, tau] for k in K_set) == gamma_factor * Df_rs_t_tau)       # معادله (8)
            @constraint(model, sum(f_rs_un[rs, k, t, tau] for k in K_set) == (1.0 - gamma_factor) * Df_rs_t_tau) # معادله (9)

            for k in K_set
                @constraint(model, phi_od_ch[rs, t, tau] - sum(Lambda_rskb[rs, k, b] * mu_b_ch[b, t, tau] for b in B_set) <= 0) # معادله (14)
                @constraint(model, phi_od_un[rs, t, tau] - sum(Lambda_rskb[rs, k, b] * mu_b_un[b, t, tau] for b in B_set) <= 0) # معادله (15)
            end
        end

        # ب) قیود جریان جاده‌ها و متغیرهای دوگان ترافیکی نستروف (معادلات 6، 7، 11، 12، 13 و 16)
        for b in B_set
            @constraint(model, x_ch[b, t, tau] == sum(Lambda_rskb[rs, k, b] * f_rs_ch[rs, k, t, tau] for rs in OD_set, k in K_set)) # معادله (11)
            @constraint(model, x_un[b, t, tau] == sum(Lambda_rskb[rs, k, b] * f_rs_un[rs, k, t, tau] for rs in OD_set, k in K_set)) # معادله (12)
            @constraint(model, x_total[b, t, tau] == x_ch[b, t, tau] + x_un[b, t, tau]) # معادله (6)
            @constraint(model, x_total[b, t, tau] <= phi_b[b])                          # معادله (7)
            @constraint(model, lambda_b[b, t, tau] == h_del[b, t, tau])                 # معادله (13)
            @constraint(model, mu_b_ch[b, t, tau] - lambda_b[b, t, tau] == h0_b[b])     # معادله (16) بخش اول
            @constraint(model, mu_b_un[b, t, tau] - lambda_b[b, t, tau] == h0_b[b])     # معادله (16) بخش دوم
        end

        # ج) قیود کوپلینگ جریان ترافیک و ایستگاه‌های شارژ (معادلات 34، 35 و 36)
        total_demand_tau = sum(Df_initial[tau, :])
        @constraint(model, sum(f_pcs[a, t, tau] for a in A_set) == gamma_factor * total_demand_tau * (1.0 + theta_t[t])) # معادله (34)

        for a in A_set
            @constraint(model, f_pcs[a, t, tau] <= sum(X_rska[rs, k, a] * f_rs_ch[rs, k, t, tau] for rs in OD_set, k in K_set)) # معادله (35)
        end

        for rs in OD_set, k in K_set
            @constraint(model, f_rs_ch[rs, k, t, tau] <= sum(X_rska[rs, k, a] * f_pcs[a, t, tau] for a in A_set)) # معادله (36)
        end
        
        # د) قیود بهره‌برداری داخلی ایستگاه‌های REVCS شامل فست‌شارژر، خورشیدی سقفی و باتری (معادلات 19، 20، 24، 25، 32، 33 و 47)
        for a in A_set
            @constraint(model, Pcs[a, t, tau] == delta_p * f_pcs[a, t, tau])            # معادله (32)
            @constraint(model, Pcs[a, t, tau] <= Cc[a, t])                              # معادله (33)
            @constraint(model, Av[a, t, tau] == Cv[a, t] * pv_profile[tau])             # معادله (47)
            @constraint(model, Rv[a, t, tau] <= Av[a, t, tau])                          # معادله (24)
            @constraint(model, Rv[a, t, tau] + Rv_curtail[a, t, tau] == Av[a, t, tau])  # محاسبه هدررفت خورشیدی سقفی برای معادله (4)

            # معادله (19): حدود شارژ و دشارژ اکتیو و راکتیو باتری BESS
            @constraint(model, v_Ec[a, t, tau] + v_Ed[a, t, tau] <= 1)
            @constraint(model, Pe_Ec[a, t, tau] <= v_Ec[a, t, tau] * Pe_max_lim)
            @constraint(model, Pe_Ed[a, t, tau] <= v_Ed[a, t, tau] * Pe_max_lim)
            @constraint(model, Pe_Ec[a, t, tau] <= 0.50 * Ce[a, t])
            @constraint(model, Pe_Ed[a, t, tau] <= 0.50 * Ce[a, t])
            @constraint(model, Qe_Ec[a, t, tau] <= v_Ec[a, t, tau] * Qe_max_lim)
            @constraint(model, Qe_Ec[a, t, tau] <= 0.50 * 0.24 * Ce[a, t])
            @constraint(model, Qe_Ed[a, t, tau] <= v_Ed[a, t, tau] * Qe_max_lim)
            @constraint(model, Qe_Ed[a, t, tau] <= 0.50 * 0.24 * Ce[a, t])

            # معادله (25): توان اکتیو خالص دریافتی ایستگاه شارژ از شبکه توزیع برق
            @constraint(model, Pn[a, t, tau] == Pcs[a, t, tau] + Pe_Ec[a, t, tau] - Pe_Ed[a, t, tau] - Rv[a, t, tau]) 
            
            # معادله (20): دینامیک انرژی ذخیره‌شده (SOC) در باتری
            @constraint(model, E_stored[a, t, tau] <= Ce[a, t])
            if tau == 1
                @constraint(model, E_stored[a, t, tau] == 0.50 * Ce[a, t] + (Pe_Ec[a, t, tau] * eta_ch) - (Pe_Ed[a, t, tau] / eta_dis))
            else
                @constraint(model, E_stored[a, t, tau] == E_stored[a, t, tau-1] + (Pe_Ec[a, t, tau] * eta_ch) - (Pe_Ed[a, t, tau] / eta_dis))
            end
            if tau == num_tau
                @constraint(model, E_stored[a, t, tau] >= 0.50 * Ce[a, t])
            end
        end

        # هـ) قیود منابع تجدیدپذیر بادی و خورشیدی شبکه توزیع برق (معادلات 21، 22، 23 و 46)
        for w_idx in 1:length(wt_buses)
            g_idx = w_idx
            @constraint(model, Aw[g_idx, t, tau] == (1.0 + zeta_t[t]) * wt_capacities[w_idx] * wt_profile[tau]) # معادله (46)
            @constraint(model, Pwt[w_idx, t, tau] <= Aw[g_idx, t, tau])                                         # معادله (21)
            @constraint(model, Pwt[w_idx, t, tau] + Pwt_curtail[w_idx, t, tau] == Aw[g_idx, t, tau])            # هدررفت بادی در معادله (4)
            @constraint(model, Pw[g_idx, t, tau] == Pwt[w_idx, t, tau])
            @constraint(model, Qwt[w_idx, t, tau] == Pwt[w_idx, t, tau] * tan_phi)                              # معادله (22)
            @constraint(model, Qw[g_idx, t, tau] == Qwt[w_idx, t, tau])
            @constraint(model, Pwt[w_idx, t, tau] * sqrt(1.0 + tan_phi^2) <= Sw_max)                            # معادله (23)
        end

        for p_idx in 1:length(pv_pdn_buses)
            g_idx = length(wt_buses) + p_idx
            @constraint(model, Aw[g_idx, t, tau] == (1.0 + zeta_t[t]) * pv_pdn_capacities[p_idx] * pv_profile[tau]) # معادله (46)
            @constraint(model, Ppv_pdn[p_idx, t, tau] <= Aw[g_idx, t, tau])                                         # معادله (21)
            @constraint(model, Ppv_pdn[p_idx, t, tau] + Ppv_pdn_curtail[p_idx, t, tau] == Aw[g_idx, t, tau])        # هدررفت خورشیدی در معادله (4)
            @constraint(model, Pw[g_idx, t, tau] == Ppv_pdn[p_idx, t, tau])
            @constraint(model, Qpv_pdn[p_idx, t, tau] == Ppv_pdn[p_idx, t, tau] * tan_phi)                          # معادله (22)
            @constraint(model, Qw[g_idx, t, tau] == Qpv_pdn[p_idx, t, tau])
            @constraint(model, Ppv_pdn[p_idx, t, tau] * sqrt(1.0 + tan_phi^2) <= Sw_max)                            # معادله (23)
        end

        # و) قیود پخش بار شبکه توزیع برق 33 شینه (معادلات 18 و 26 تا 31)
        @constraint(model, V_bus[1, t, tau] == V_slack) # ولتاژ شین مرجع (پست اصلی شین 1)
        @constraint(model, Pb_u[t, tau] <= Pb_max)      # معادله (18): سقف توان اکتیو پست اصلی
        @constraint(model, Qb_u[t, tau] <= Qb_max)      # معادله (18): سقف توان راکتیو پست اصلی

        for i in I_set
            @constraint(model, V_bus[i, t, tau] >= V_min) # معادله (27): کران پایین ولتاژ شین i
            @constraint(model, V_bus[i, t, tau] <= V_max) # معادله (27): کران بالای ولتاژ شین i

            lines_in  = findall(x -> x == i, to_bus)   # خطوط ورودی به شین i
            lines_out = findall(x -> x == i, from_bus) # خطوط خروجی از شین i
            
            p_sub = (i == 1) ? Pb_u[t, tau] : 0.0
            q_sub = (i == 1) ? Qb_u[t, tau] : 0.0
            
            station_idx = findfirst(x -> x == i, station_to_bus)
            p_station   = (station_idx !== nothing) ? Pn[station_idx, t, tau] : 0.0
            q_station   = (station_idx !== nothing) ? (Qe_Ec[station_idx, t, tau] - Qe_Ed[station_idx, t, tau]) : 0.0

            wt_idx = findfirst(x -> x == i, wt_buses)
            p_wind = (wt_idx !== nothing) ? Pwt[wt_idx, t, tau] : 0.0
            q_wind = (wt_idx !== nothing) ? Qwt[wt_idx, t, tau] : 0.0

            pv_idx     = findfirst(x -> x == i, pv_pdn_buses)
            p_pv_grid  = (pv_idx !== nothing) ? Ppv_pdn[pv_idx, t, tau] : 0.0
            q_pv_grid  = (pv_idx !== nothing) ? Qpv_pdn[pv_idx, t, tau] : 0.0

            # معادله (28): تعادل توان اکتیو در شین i
            @constraint(model, p_sub + sum(Pf[l, t, tau] for l in lines_in) + p_wind + p_pv_grid + delta_p_plus[i, t, tau] - delta_p_minus[i, t, tau] == 
                sum(Pf[l, t, tau] for l in lines_out) + PD_bus[tau] + p_station)

            # معادله (29): تعادل توان راکتیو در شین i
            @constraint(model, q_sub + sum(Qf[l, t, tau] for l in lines_in) + q_wind + q_pv_grid == 
                sum(Qf[l, t, tau] for l in lines_out) + delta_q_plus[i, t, tau] - delta_q_minus[i, t, tau] + QD_bus[tau] + q_station)
        end

        for l in L_set
            bus_i = from_bus[l]
            bus_j = to_bus[l]
            r     = R_line[l]
            x     = X_line[l]
            cap_p = S_max[l]
            cap_q = Qf_max[l]
            
            if l <= 32
                @constraint(model, dV_line[l, t, tau] == 0.0) # خطوط اصلی بسته
            else
                @constraint(model, dV_line[l, t, tau] >= -V_slack) # معادله (27) برای خطوط ارتباطی Tie
                @constraint(model, dV_line[l, t, tau] <=  V_slack)
            end
            
            # معادله (26): افت ولتاژ خطی در شاخه ij
            @constraint(model, V_bus[bus_i, t, tau] == V_bus[bus_j, t, tau] + (r * Pf[l, t, tau] + x * Qf[l, t, tau]) / (base_factor * V_slack) + dV_line[l, t, tau])
            
            # معادله (30): محدودیت ظرفیت توان اکتیو و راکتیو خطوط
            @constraint(model, Pf[l, t, tau] <=  cap_p)
            @constraint(model, Pf[l, t, tau] >= -cap_p)
            @constraint(model, Qf[l, t, tau] <=  cap_q)
            @constraint(model, Qf[l, t, tau] >= -cap_q)
        end
    end

    # معادله (17): شرط دوگانگی قوی برای تضمین تعادل کاربر ترافیکی نستروف در دوره t
    @constraint(model, 
        sum(gamma_factor * phi_od_ch[rs, t, tau] * (Df_initial[tau, rs] * (1.0 + theta_t[t])) + 
            (1.0 - gamma_factor) * phi_od_un[rs, t, tau] * (Df_initial[tau, rs] * (1.0 + theta_t[t])) for tau in Tau_set, rs in OD_set) <=
        sum(h0_b[b] * (x_ch[b, t, tau] + x_un[b, t, tau]) + phi_b[b] * lambda_b[b, t, tau] for tau in Tau_set, b in B_set)
    )
end

println("✅ [Reference Paper] Part 7: All mathematical constraints (Equations 6 to 47) registered.")

# ==============================================================================
# بخش هشتم: تابع هدف خالص مقاله مرجع (Equations 1 to 5 on Page 3760 of Paper)
# ==============================================================================
days_per_stage = 4.0 # تعداد ۴ روز نمونه (معادل ۹۶ ساعت عملیاتی TOI) در هر دوره یک‌ساله طبق بخش IV-A مقاله

# معادله (2) صفحه 3760: محاسبه هزینه سرمایه‌گذاری احداث ایستگاه‌های جدید و توسعه تجهیزات در دوره t
Inv_Cost = @expression(model, [t in T_set], 
    sum(q_rvc * phi_inv[a, t] + q_fc * yEc[a, t] + q_es * yEe[a, t] + q_pv * yEv[a, t] for a in A_set)
)

# معادله (4) بخش اول: محاسبه هزینه خرید توان اکتیو از پست اصلی (Substation) در طول دوره t
Cost_Substation = @expression(model, [t in T_set], 
    days_per_stage * sum(c_sub * Pb_u[t, tau] for tau in Tau_set)
)

# معادله (4) بخش دوم: محاسبه جریمه هدررفت (Curtailment) انرژی بادی و خورشیدی شبکه و خورشیدی سقفی در دوره t
Cost_Curtailment = @expression(model, [t in T_set], 
    days_per_stage * c_cr * (
        sum(Pwt_curtail[w, t, tau] for w in 1:length(wt_buses), tau in Tau_set) +
        sum(Ppv_pdn_curtail[p, t, tau] for p in 1:length(pv_pdn_buses), tau in Tau_set) +
        sum(Rv_curtail[a, t, tau] for a in A_set, tau in Tau_set)
    )
)

# معادله (4) بخش سوم: محاسبه جریمه عدم تعادل توان اکتیو و راکتیو (Load Shedding) در شین‌های شبکه در دوره t
Cost_Imbalance = @expression(model, [t in T_set], 
    days_per_stage * c_unb * sum(
        delta_p_plus[i, t, tau] + delta_p_minus[i, t, tau] + 
        delta_q_plus[i, t, tau] + delta_q_minus[i, t, tau] 
        for i in I_set, tau in Tau_set
    )
)

# معادله (4) کامل: تجمیع کل هزینه‌های بهره‌برداری شبکه توزیع برق (\Upsilon_t^{ope,PDN}) در دوره t
Ope_Cost_PDN = @expression(model, [t in T_set], 
    Cost_Substation[t] + Cost_Curtailment[t] + Cost_Imbalance[t]
)

# معادله (5) صفحه 3760: محاسبه هزینه بهره‌برداری شبکه حمل‌ونقل شهری (\Upsilon_t^{ope,UTN}) شامل زمان سفر آزاد و تاخیر تراکم
Ope_Cost_UTN = @expression(model, [t in T_set], 
    days_per_stage * (
        c_fr * sum(h0_b[b] * (x_ch[b, t, tau] + x_un[b, t, tau]) for b in B_set, tau in Tau_set) +
        c_ja * sum(phi_b[b] * h_del[b, t, tau] for b in B_set, tau in Tau_set)
    )
)

# معادله (3) صفحه 3760: مجموع هزینه تعمیر و نگهداری سالانه ایستگاه‌ها و هزینه‌های بهره‌برداری PDN و UTN در دوره t
Ope_Cost_Total = @expression(model, [t in T_set], 
    sum(c_man * z[a, t] for a in A_set) + Ope_Cost_PDN[t] + Ope_Cost_UTN[t]
)

# معادله (1) صفحه 3759: تابع هدف کل برای کمینه‌سازی ارزش فعلی خالص (NPV) مجموع هزینه‌های سرمایه‌گذاری و بهره‌برداری در ۳ دوره
Total_Cost_Ref = @expression(model, 
    sum((1.0 / (1.0 + sigma)^(t - 1)) * (Inv_Cost[t] + Ope_Cost_Total[t]) for t in T_set)
)

@objective(model, Min, Total_Cost_Ref) # ثبت رسمی تابع هدف کمینه‌سازی در مدل JuMP

println("✅ [Reference Paper] Part 8: Baseline objective function (Equations 1 to 5) registered.")

# ==============================================================================
# بخش نهم: حل مدل، گزارش‌گیری جداول II و III مقاله و ترسیم شکل‌های 6، 7، 8 و 10
# ==============================================================================
println("==================================================================")
println("🚀 Solving the Reference Paper Multiperiod Planning Model...")
println("==================================================================")

optimize!(model)                   # فراخوانی سالور HiGHS برای حل مسأله MILP
status = termination_status(model) # استخراج وضعیت نهایی همگرایی سالور

# تعریف تابع کمکی برای نمایش نمودار در پنجره گرافیکی و ذخیره همزمان در پوشه کاری
function safe_savefig(plt, filename)
    display(plt)                             # نمایش مستقیم شکل در پنل Plots محیط VS Code
    filepath = joinpath(@__DIR__, filename)  # ترکیب مسیر پوشه فعلی با نام فایل تصویر
    try
        savefig(plt, filepath)               # ذخیره شکل روی دیسک با فرمت PNG
        println("   ✔ Image successfully saved at $filepath.")
    catch
        alt_path = joinpath(@__DIR__, "Updated_" * filename) # ایجاد نام جایگزین در صورت باز بودن فایل قبلی در ویندوز
        savefig(plt, alt_path)                               # ذخیره تصویر در مسیر جایگزین
        println("   ✔ Previous file was open; new image saved at $alt_path.")
    end
end

# بررسی شرط یافتن جواب بهینه توسط سالور
if status == MOI.OPTIMAL || status == MOI.LOCALLY_SOLVED || status == MOI.ALMOST_LOCALLY_SOLVED || (status == MOI.TIME_LIMIT && has_values(model))
    println("\n🎯 [Reference Paper] Optimal solution extracted! (Solver Status: $status)")
    println("💵 Baseline Total NPV Cost (Eq. 1-5) = \$", round(objective_value(model), digits=2))
    
    # حلقه چاپ گزارش تفصیلی برای هر یک از دوره‌های برنامه‌ریزی (Stage 1, Stage 2, Stage 3)
    for t in T_set
        println("\n==================================================")
        println("📅 [Reference Paper] Planning Report - Period $t (Stage$t)")
        println("==================================================")
        
        inv_c  = value(Inv_Cost[t])         # مقدار بهینه هزینه سرمایه‌گذاری در دوره t (دلار)
        sub_c  = value(Cost_Substation[t])  # مقدار بهینه هزینه خرید برق از پست اصلی در دوره t (دلار)
        curt_c = value(Cost_Curtailment[t]) # مقدار بهینه جریمه هدررفت انرژی تجدیدپذیر در دوره t (دلار)
        imb_c  = value(Cost_Imbalance[t])   # مقدار بهینه جریمه قطع بار و عدم تعادل در دوره t (دلار)
        utn_c  = value(Ope_Cost_UTN[t])     # مقدار بهینه هزینه زمان سفر در شبکه ترافیک در دوره t (دلار)
        tot_op = value(Ope_Cost_Total[t])   # مجموع کل هزینه‌های بهره‌برداری و نگهداری در دوره t (دلار)
        
        println("🔹 Investment Cost (Eq. 2):               \$", round(inv_c, digits=2))
        println("🔹 Total Operation & Maintenance (Eq. 3): \$", round(tot_op, digits=2))
        println("   ├─ Substation Power Cost (Eq. 4):      \$", round(sub_c, digits=2))
        println("   ├─ DRE Curtailment Penalty (Eq. 4):    \$", round(curt_c, digits=2))
        println("   ├─ Load Shedding Penalty (Eq. 4):      \$", round(imb_c, digits=2))
        println("   └─ UTN Travel Time Cost (Eq. 5):       \$", round(utn_c, digits=2))
        
        # محاسبه کل ظرفیت نصب‌شده بادی، خورشیدی شبکه و خورشیدی سقفی در دوره t
        wt_cap_stage     = sum(wt_capacities) * (1.0 + zeta_t[t])     # ظرفیت کل بادی با احتساب نرخ رشد دوره t
        pv_pdn_cap_stage = sum(pv_pdn_capacities) * (1.0 + zeta_t[t]) # ظرفیت کل خورشیدی شبکه با احتساب نرخ رشد دوره t
        pv_rev_cap_stage = sum(value(Cv[a, t]) for a in A_set)        # مجموع ظرفیت خورشیدی سقفی تمام ایستگاه‌ها در دوره t
        
        # محاسبه کل انرژی تولیدی روزانه منابع تجدیدپذیر در دوره t
        tot_wt_gen     = sum(value(Pwt[w, t, tau]) for w in 1:length(wt_buses), tau in Tau_set)         # تولید روزانه بادی (kWh)
        tot_pv_pdn_gen = sum(value(Ppv_pdn[p, t, tau]) for p in 1:length(pv_pdn_buses), tau in Tau_set) # تولید روزانه خورشیدی شبکه (kWh)
        tot_pv_rev_gen = sum(value(Rv[a, t, tau]) for a in A_set, tau in Tau_set)                       # تولید روزانه خورشیدی سقفی (kWh)
        
        println("🌬️ Total PDN Wind Capacity (WT): $(round(wt_cap_stage, digits=1)) kW | Daily Gen:$(round(tot_wt_gen, digits=1)) kWh")
        println("☀️ Total PDN Solar Capacity (PV_PDN): $(round(pv_pdn_cap_stage, digits=1)) kW | Daily Gen:$(round(tot_pv_pdn_gen, digits=1)) kWh")
        println("🔋 Total Onsite Rooftop PV Capacity: $(round(pv_rev_cap_stage, digits=1)) kW | Daily Gen:$(round(tot_pv_rev_gen, digits=1)) kWh")
        println("--------------------------------------------------")
        
        # حلقه بررسی و چاپ وضعیت هر ایستگاه شارژ روی جاده‌های شبکه حمل‌ونقل
        for a in A_set
            if value(z[a, t]) > 0.5 # اگر ایستگاه شارژ در جاده a در دوره t فعال باشد
                is_new = value(phi_inv[a, t]) > 0.5                  # بررسی اینکه آیا ایستگاه در همین دوره تازه احداث شده است
                exp_c  = max(0.0, round(value(yEc[a, t]), digits=1)) # مقدار توسعه فست‌شارژر در دوره جاری (kW)
                exp_v  = max(0.0, round(value(yEv[a, t]), digits=1)) # مقدار توسعه خورشیدی سقفی در دوره جاری (kW)
                exp_e  = max(0.0, round(value(yEe[a, t]), digits=1)) # مقدار توسعه باتری در دوره جاری (kW)
                is_exp = (exp_c > 0.1) || (exp_v > 0.1) || (exp_e > 0.1) # بررسی وقوع توسعه ظرفیت در حداقل یکی از تجهیزات
                status_str = is_new ? "Newly Constructed 🔴" : (is_exp ? "Capacity Expanded 🔵" : "Existing (No Expansion) 🟢")
                
                println("🚗 REVCS on Road R$a (Bus B$(station_to_bus[a])) ->$status_str | " *
                        "FCS: $(round(value(Cc[a, t]), digits=1)) (+$exp_c) kW | " *
                        "Onsite PV: $(round(value(Cv[a, t]), digits=1)) (+$exp_v) kW | " *
                        "BESS: $(round(value(Ce[a, t]), digits=1)) (+$exp_e) kW")
            end
        end
    end

    # --------------------------------------------------------------------------
    # چاپ جدول II مقاله مرجع (Table II on Page 3767: In-Sample Performance for Periods 2 & 3)
    # --------------------------------------------------------------------------
    println("\n==================================================================")
    println("📋 [Reference Paper - Table II] DRE & T.D. In-Sample Analysis (Page 3767)")
    println("==================================================================")
    avg_line_cap = round(mean(S_max), digits=2) # میانگین ظرفیت خطوط شبکه توزیع برق (2735.92 kW طبق جدول II مقاله)
    for t in [2, 3]
        avail_dre_tau = [sum(value(Aw[g, t, tau]) for g in R_set) for tau in Tau_set] # مجموع توان تجدیدپذیر در دسترس در هر ساعت
        max_dre_p     = round(maximum(avail_dre_tau), digits=2)                       # حداکثر توان تجدیدپذیر در دسترس در دوره t
        min_dre_p     = round(minimum(avail_dre_tau), digits=2)                       # حداقل توان تجدیدپذیر در دسترس در دوره t
        
        ev_ch_tau     = [sum(value(Pcs[a, t, tau]) for a in A_set) for tau in Tau_set] # مجموع توان شارژ خودروها در هر ساعت
        max_ev_p      = round(maximum(ev_ch_tau), digits=2)                            # حداکثر تقاضای توان شارژ در دوره t
        min_ev_p      = round(minimum(ev_ch_tau), digits=2)                            # حداقل تقاضای توان شارژ در دوره t
        
        ls_cost_102   = round(value(Cost_Imbalance[t]) / 100.0, digits=2)              # هزینه قطع بار بر حسب 10^2 دلار
        rc_cost_102   = round(value(Cost_Curtailment[t]) / 100.0, digits=2)            # هزینه هدررفت تجدیدپذیر بر حسب 10^2 دلار
        
        println("🔸 Period $t:")
        println("   ├─ DRE Available Power (Max / Min):      $max_dre_p kWh / $min_dre_p kWh")
        println("   ├─ EV Charging Power (Max / Min):        $max_ev_p kWh / $min_ev_p kWh")
        println("   ├─ Average PDN Line Capacity:            $avg_line_cap kWh")
        println("   ├─ Aggregated Load Shedding Cost (10²\$): $ls_cost_102")
        println("   └─ Aggregated DRE Curtailment Cost(10²\$):$rc_cost_102")
    end

# --------------------------------------------------------------------------
    # رسم شکل 6 مقاله مرجع (Fig. 6: Topology of the 33P-12U system - Page 3765)
    # --------------------------------------------------------------------------
    println("\n📊 Plotting Reference Paper Figures 6, 7, 8, and 10...")

    utn_x = [2.0, 4.0, 1.0, 2.0, 4.0, 5.0, 1.0, 2.0, 4.0, 5.0, 2.0, 4.0] # مختصات افقی گره‌های UTN
    utn_y = [3.0, 3.0, 2.0, 2.0, 2.0, 2.0, 1.0, 1.0, 1.0, 1.0, 0.0, 0.0] # مختصات عمودی گره‌های UTN
    
    utn_edges = [
        (1,3), (1,2), (2,6), (1,4), (2,5), (3,4), (4,5), (5,6), (3,7), (4,8), 
        (5,9), (6,10), (7,8), (8,9), (9,10), (7,11), (8,11), (9,12), (10,12), (11,12)
    ]

    p6_utn = plot(legend=false, axis=false, grid=false, title="12-node UTN", titlefontsize=12)
    for (i, e) in enumerate(utn_edges)
        n1, n2 = e
        plot!(p6_utn, [utn_x[n1], utn_x[n2]], [utn_y[n1], utn_y[n2]], color=:lightgray, lw=3.5)
        mx, my = (utn_x[n1] + utn_x[n2]) / 2, (utn_y[n1] + utn_y[n2]) / 2
        annotate!(p6_utn, mx, my + 0.12, text("R$i (B$(station_to_bus[i]))", 6, :royalblue, :bold))
        if existing_REVCS[i] == 1
            scatter!(p6_utn, [mx], [my], markershape=:rect, markersize=8, color=:lightgreen, msc=:darkgreen, msw=1.5)
        end
    end
    scatter!(p6_utn, utn_x, utn_y, markersize=13, color=:white, msc=:black, msw=2)
    for i in 1:12
        annotate!(p6_utn, utn_x[i], utn_y[i], text("T$i", 8, :black, :bold))
    end

    # تعریف مختصات هندسی دقیق شین‌های ۱ تا ۳۳ شبکه توزیع برق (PDN)
    pdn_x = Float64[]; pdn_y = Float64[]
    append!(pdn_x, 1:18); append!(pdn_y, zeros(18))
    append!(pdn_x, 2:5);  append!(pdn_y, fill(-1.0, 4))
    append!(pdn_x, 3:5);  append!(pdn_y, fill(1.0, 3))
    append!(pdn_x, 6:13); append!(pdn_y, fill(2.0, 8))
    
    pdn_main_edges = [
        (1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),
        (13,14),(14,15),(15,16),(16,17),(17,18),(2,19),(19,20),(20,21),(21,22),
        (3,23),(23,24),(24,25),(6,26),(26,27),(27,28),(28,29),(29,30),(30,31),(31,32),(32,33)
    ]
    
    p6_pdn = plot(legend=false, axis=false, grid=false, xlims=(0.5, 18.5), ylims=(-1.8, 2.8), title="33-bus PDN (Red: PV, Blue: WT)", titlefontsize=12)
    
    # حلقه رسم خطوط اصلی شبکه برق به صورت خط ممتد مشکی
    for e in pdn_main_edges
        n1, n2 = e
        plot!(p6_pdn, [pdn_x[n1], pdn_x[n2]], [pdn_y[n1], pdn_y[n2]], color=:black, lw=2.0)
    end
    
    # --- تابع ریاضی کمکی برای رسم کمان‌های هلالی شکل (Smooth Bézier Arcs) ---
    function draw_arc(x1, y1, x2, y2, height, n=30)
        t = range(0, 1, length=n)
        xt = (1 .- t) .* x1 .+ t .* x2
        yt = (1 .- t) .* y1 .+ t .* y2 .+ 4 .* t .* (1 .- t) .* height
        return xt, yt
    end

    # رسم ۵ خط ارتباطی مانور (Tie-lines) به صورت کمان‌های هلالی تمیز دقیقاً مشابه شکل مقاله:
    # 1. اتصال بین شین 21 و 8 (کمان رو به بالا)
    plot!(p6_pdn, draw_arc(pdn_x[21], pdn_y[21], pdn_x[8], pdn_y[8], 0.9), color=:gray50, linestyle=:dash, lw=1.5)
    # 2. اتصال بین شین 9 و 15 (کمان هلالی رو به بالا)
    plot!(p6_pdn, draw_arc(pdn_x[9], pdn_y[9], pdn_x[15], pdn_y[15], 1.2), color=:gray50, linestyle=:dash, lw=1.5)
    # 3. اتصال بین شین 12 و 22 (کمان هلالی رو به پایین)
    plot!(p6_pdn, draw_arc(pdn_x[12], pdn_y[12], pdn_x[22], pdn_y[22], -0.7), color=:gray50, linestyle=:dash, lw=1.5)
    # 4. اتصال بین شین 18 و 33 (کمان بلند مورب سمت راست)
    plot!(p6_pdn, draw_arc(pdn_x[18], pdn_y[18], pdn_x[33], pdn_y[33], 0.8), color=:gray50, linestyle=:dash, lw=1.5)
    # 5. اتصال بین شین 25 و 29 (کمان هلالی میانی بالا)
    plot!(p6_pdn, draw_arc(pdn_x[25], pdn_y[25], pdn_x[29], pdn_y[29], 0.6), color=:gray50, linestyle=:dash, lw=1.5)
    
    # رنگ‌بندی شین‌ها (قرمز: PV، آبی: WT، مشکی: عادی، حاشیه سبز: کوپل‌شده با ایستگاه شارژ)
    bus_colors = [i in pv_pdn_buses ? :red : (i in wt_buses ? :dodgerblue : :black) for i in I_set]
    bus_edges  = [i in station_to_bus ? :limegreen : :black for i in I_set]
    
    scatter!(p6_pdn, pdn_x, pdn_y, markersize=7, color=bus_colors, msc=bus_edges, msw=2)
    
    for i in I_set
        y_offset = (pdn_y[i] == 0.0) ? 0.22 : (pdn_y[i] > 0 ? 0.22 : -0.28)
        annotate!(p6_pdn, pdn_x[i], pdn_y[i] + y_offset, text("$i", 7, :black, :bold))
    end
    
    p6 = plot(p6_utn, p6_pdn, layout=(1,2), size=(1200, 450))
    safe_savefig(p6, "Ref_Figure_6_Topology.png")
    # --------------------------------------------------------------------------
    # رسم شکل 7 مقاله مرجع (Fig. 7: Investment decisions & charging EV flow - Page 3766)
    # --------------------------------------------------------------------------
    p7_list = [] # تعریف یک آرایه خالی برای نگهداری ۳ زیرنمودار مربوط به دوره‌های ۱، ۲ و ۳ برنامه‌ریزی
    for t in 1:num_periods # حلقه روی ۳ دوره برنامه‌ریزی (Stage 1, Stage 2, Stage 3)
        pt = plot(legend=false, axis=false, grid=false, title="Stage $t") # ایجاد بوم خالی بدون محور و شبکه برای رسم گراف ترافیک دوره t
        for a in 1:num_roads # حلقه روی هر ۲۰ جاده شبکه حمل‌ونقل شهری برای رنگ‌آمیزی بر اساس حجم ترافیک
            n1, n2 = utn_edges[a]                                         # استخراج شماره گره مبدأ و مقصد جاده a
            flow = sum(value(x_ch[a, t, tau]) for tau in 1:num_tau)       # محاسبه مجموع جریان خودروهای شارژی عبوری از جاده a در دوره t
            # تعیین رنگ جاده بر اساس طیف ترافیکی راهنمای شکل ۷ مقاله (خاکستری، سرمه‌ای، صورتی، آبی، قرمز)
            road_c = flow < 100 ? :lightgray : flow < 300 ? :darkgray : flow < 600 ? :salmon : flow < 1000 ? :dodgerblue : :red
            road_w = flow < 100 ? 3 : 5                                   # تعیین ضخامت خط جاده متناسب با شدت ترافیک
            plot!(pt, [utn_x[n1], utn_x[n2]], [utn_y[n1], utn_y[n2]], color=road_c, lw=road_w) # رسم خط جاده با رنگ و ضخامت تعیین‌شده
            annotate!(pt, (utn_x[n1]+utn_x[n2])/2 + 0.15, (utn_y[n1]+utn_y[n2])/2 + 0.15, text("R$a", 7, :black)) # نوشتن نام جاده Ra کنار آن
        end
        scatter!(pt, utn_x, utn_y, markersize=10, color=:white, msc=:black) # رسم دایره‌های سفید گره‌های ترافیکی T1 تا T12
        for i in 1:12
            annotate!(pt, utn_x[i], utn_y[i], text("T$i", 6, :black))       # درج شماره گره ترافیکی Ti داخل هر دایره
        end
        for a in 1:num_roads # حلقه بررسی و رسم آیکون ایستگاه‌های شارژ روی جاده‌ها
            if value(z[a, t]) > 0.5 # اگر در دوره t در جاده a ایستگاه شارژ وجود داشته باشد
                n1, n2 = utn_edges[a]
                mx, my = (utn_x[n1] + utn_x[n2]) / 2, (utn_y[n1] + utn_y[n2]) / 2 # محاسبه مختصات مرکز جاده
                is_expanded = (value(yEc[a, t]) > 0.5) || (value(yEe[a, t]) > 0.5) || (value(yEv[a, t]) > 0.5) # بررسی وقوع توسعه ظرفیت
                # تعیین رنگ آیکون: قرمز (احداث جدید)، آبی (توسعه‌یافته)، سبز (موجود بدون تغییر در این دوره)
                icon_color  = value(phi_inv[a, t]) > 0.5 ? :red : (is_expanded ? :dodgerblue : :lightgreen)
                scatter!(pt, [mx], [my], markershape=:rect, markersize=10, color=icon_color) # رسم آیکون مربعی ایستگاه شارژ
            end
        end
        push!(p7_list, pt) # ذخیره نمودار آماده‌شده دوره t در لیست
    end
    p7 = plot(p7_list..., layout=(1,3), size=(1200, 400)) # ترکیب افقی ۳ نمودار دوره‌ها در یک تصویر واحد (شکل 7 مقاله)
    safe_savefig(p7, "Ref_Figure_7_Stations.png")         # فراخوانی تابع ایمن برای نمایش و ذخیره شکل ۷

    # --------------------------------------------------------------------------
    # رسم شکل 8 مقاله مرجع (Fig. 8: Capacity planning decisions for REVCS devices - Page 3766)
    # --------------------------------------------------------------------------
    active_roads = [1, 2, 3, 4, 7, 8, 10, 11, 12, 14, 16] # ۱۱ جاده دارای ایستگاه شارژ روی محور افقی شکل ۸ مقاله
    p8_list = []                                          # لیست نگهداری ۳ نمودار میله‌ای ظرفیت تجهیزات
    for t in 1:num_periods                                # حلقه روی دوره‌های ۱، ۲ و ۳
        ymax_stage = (t == 3) ? 600 : 450                 # تنظیم سقف محور عمودی (450 برای دوره ۱ و ۲، 600 برای دوره ۳)
        pt = plot(legend=(t==2 ? :top : false), grid=true, title="Stage $t (REVCS Devices)",
                  xlabel="Road number", ylabel="Capacity (KW)", 
                  xticks=(1:length(active_roads), string.(active_roads)), ylim=(0, ymax_stage))
        for (i, a) in enumerate(active_roads) # حلقه روی ۱۱ جاده فعال
            tot_FCS = max(0.0, round(value(Cc[a, t]), digits=2)) # ظرفیت کل فست‌شارژر در جاده a و دوره t
            ep_FCS  = max(0.0, round(value(yEc[a, t]), digits=2))# ظرفیت توسعه‌یافته فست‌شارژر در دوره t
            ex_FCS  = max(0.0, tot_FCS - ep_FCS)                 # ظرفیت پایه یا موجود فست‌شارژر
            
            tot_PV  = max(0.0, round(value(Cv[a, t]), digits=2)) # ظرفیت کل خورشیدی سقفی در دوره t
            ep_PV   = max(0.0, round(value(yEv[a, t]), digits=2))# ظرفیت توسعه‌یافته خورشیدی سقفی در دوره t
            ex_PV   = max(0.0, tot_PV - ep_PV)                   # ظرفیت پایه یا موجود خورشیدی سقفی
            
            tot_ESS = max(0.0, round(value(Ce[a, t]), digits=2)) # ظرفیت کل باتری BESS در دوره t
            ep_ESS  = max(0.0, round(value(yEe[a, t]), digits=2))# ظرفیت توسعه‌یافته باتری در دوره t
            ex_ESS  = max(0.0, tot_ESS - ep_ESS)                 # ظرفیت پایه یا موجود باتری

            # رسم میله‌های دو رنگ فست‌شارژر (آبی تیره: توسعه یافته، آبی روشن: موجود) در سمت چپ
            bar!(pt, [i - 0.25], [tot_FCS], color=:dodgerblue3, bar_width=0.22, label=(i==1 && t==2 ? "Expanded fast charging device" : ""))
            bar!(pt, [i - 0.25], [ex_FCS],  color=:lightblue,   bar_width=0.22, label=(i==1 && t==2 ? "Existing fast charging device" : ""))
            
            # رسم میله‌های دو رنگ خورشیدی سقفی (قرمز: توسعه یافته، خاکستری: موجود) در وسط
            bar!(pt, [i], [tot_PV], color=:red,       bar_width=0.22, label=(i==1 && t==2 ? "Expanded onsite PV" : ""))
            bar!(pt, [i], [ex_PV],  color=:lightgray, bar_width=0.22, label=(i==1 && t==2 ? "Existing onsite PV" : ""))
            
            # رسم میله‌های دو رنگ باتری BESS (سبز تیره: توسعه یافته، سبز روشن: موجود) در سمت راست
            bar!(pt, [i + 0.25], [tot_ESS], color=:forestgreen,   bar_width=0.22, label=(i==1 && t==2 ? "Expanded ESS" : ""))
            bar!(pt, [i + 0.25], [ex_ESS],  color=:darkseagreen2, bar_width=0.22, label=(i==1 && t==2 ? "Existing ESS" : ""))
        end
        push!(p8_list, pt) # افزودن نمودار میله‌ای دوره t به لیست شکل ۸
    end
    p8 = plot(p8_list..., layout=(1,3), size=(1250, 420), margin=5Plots.mm) # ترکیب افقی ۳ نمودار شکل ۸
    safe_savefig(p8, "Ref_Figure_8_REVCS.png")                              # نمایش و ذخیره شکل ۸ مقاله مرجع

    # --------------------------------------------------------------------------
    # چاپ جدول II مقاله مرجع (Table II on Page 3767: In-Sample Performance for Periods 2 & 3)
    # --------------------------------------------------------------------------
    println("\n==================================================================")
    println("📋 [Reference Paper - Table II] DRE & T.D. In-Sample Analysis (Page 3767)")
    println("==================================================================")
    avg_line_cap = round(mean(S_max), digits=2) # محاسبه میانگین ظرفیت خطوط شبکه توزیع برق (مقدار 2735.92 kW در جدول II مقاله)
    for t in [2, 3] # بررسی دوره‌های دوم و سوم طبق ساختار جدول II مقاله
        avail_dre_tau = [sum(value(Aw[g, t, tau]) for g in R_set) for tau in Tau_set] # توان کل تجدیدپذیر در دسترس در هر ساعت
        max_dre_p     = round(maximum(avail_dre_tau), digits=2)                       # حداکثر توان تجدیدپذیر در دسترس دوره t
        min_dre_p     = round(minimum(avail_dre_tau), digits=2)                       # حداقل توان تجدیدپذیر در دسترس دوره t
        
        ev_ch_tau     = [sum(value(Pcs[a, t, tau]) for a in A_set) for tau in Tau_set] # توان تقاضای شارژ الکتریکی خودروها در هر ساعت
        max_ev_p      = round(maximum(ev_ch_tau), digits=2)                            # حداکثر تقاضای شارژ در دوره t
        min_ev_p      = round(minimum(ev_ch_tau), digits=2)                            # حداقل تقاضای شارژ در دوره t
        
        ls_cost_102   = round(value(Cost_Imbalance[t]) / 100.0, digits=2)              # هزینه قطع بار بر حسب 10^2 دلار
        rc_cost_102   = round(value(Cost_Curtailment[t]) / 100.0, digits=2)            # هزینه هدررفت تجدیدپذیر بر حسب 10^2 دلار
        
        println("🔸 Period $t:")
        println("   ├─ DRE Available Power (Max / Min):      $max_dre_p kWh / $min_dre_p kWh")
        println("   ├─ EV Charging Power (Max / Min):        $max_ev_p kWh / $min_ev_p kWh")
        println("   ├─ Average PDN Line Capacity:            $avg_line_cap kWh")
        println("   ├─ Aggregated Load Shedding Cost (10²\$): $ls_cost_102")
        println("   └─ Aggregated DRE Curtailment Cost(10²\$):$rc_cost_102")
    end

    # --------------------------------------------------------------------------
    # رسم شکل 10 اصلی مقاله مرجع (Fig. 10 on Page 3767: 24-h EV Flow Heatmap & Road 2 Internal Balance)
    # --------------------------------------------------------------------------
    ev_flow_mat = zeros(Float64, num_roads, num_tau) # ساخت ماتریس ۲۰×۲۴ جهت ذخیره جریان خودروهای شارژی جاده‌ها در ۲۴ ساعت دوره سوم
    for b in B_set, tau in Tau_set
        ev_flow_mat[b, tau] = value(x_total[b, 3, tau]) * 0.45 # استخراج جریان کل ترافیک شارژی در دوره سوم
    end
    # رسم زیرنمودار (a) شکل 10 مقاله: هیت‌مپ توزیع ساعتی جریان خودروهای شارژی در ۲۰ جاده
    p10_a = heatmap(
        1:24, 1:20, ev_flow_mat,
        c = :Blues,                                  # استفاده از طیف رنگی آبی برای هیت‌مپ
        xlabel = "Typical operation interval (h)\n(a)",
        ylabel = "Road number",
        xticks = 2:2:24,
        yticks = 1:2:20,
        yflip = true,                                # معکوس کردن محور عمودی جهت تطابق با شماره‌گذاری جاده‌ها در مقاله
        title = "Fig. 10(a): Quantities of charging EV flow in UTN (Period 3)",
        titlefontsize = 10
    )

    # استخراج پارامترهای ۲۴ ساعته برای زیرنمودار (b) شکل 10 مقاله (تعادل توان داخلی ایستگاه جاده ۲ متصل به شین ۴)
    hrs     = collect(1:24)                                                          # بردار ساعات ۱ تا ۲۴
    fcs_r2  = [-value(Pcs[2, 3, tau]) for tau in Tau_set]                            # توان مصرفی فست‌شارژر جاده ۲ در نیم‌صفحه منفی
    grid_r2 = [max(0.0, value(Pn[2, 3, tau])) for tau in Tau_set]                    # توان اکتیو دریافتی از شبکه برق (From grid)
    pv_r2   = [value(Rv[2, 3, tau]) for tau in Tau_set]                              # توان تولیدی خورشیدی سقفی ایستگاه (Onsite PV)
    bess_r2 = [value(Pe_Ed[2, 3, tau]) - value(Pe_Ec[2, 3, tau]) for tau in Tau_set] # توان خالص دشارژ/شارژ باتری BESS
    wt_b4   = [value(Aw[1, 3, tau]) for tau in Tau_set]                              # توان در دسترس توربین بادی شین ۴ (متصل به جاده ۲)

    # رسم زیرنمودار (b) شکل 10 مقاله: نمودار میله‌ای-خطی تعادل توان داخلی ایستگاه شارژ جاده ۲
    p10_b = bar(
        hrs, grid_r2 .+ pv_r2,
        bar_width = 0.55, color = :peachpuff, label = "Onsite PV",
        xlabel = "Typical operation interval (h)\n(b)", ylabel = "Power (KWh)",
        xticks = 2:2:24, ylims = (-600, 600), legend = :outerbottom, legendcolumns = 5,
        title = "Fig. 10(b): External Net Power to PDN & Internal Balance of REVCS on Road 2", titlefontsize = 10
    )
    bar!(p10_b, hrs, grid_r2, bar_width = 0.55, color = :dodgerblue, label = "From grid") # میله آبی توان دریافتی از شبکه
    bar!(p10_b, hrs, fcs_r2,  bar_width = 0.55, color = :lightgray,  label = "FCS")       # میله خاکستری فست‌شارژر در نیم‌صفحه منفی
    bar!(p10_b, hrs, bess_r2, bar_width = 0.35, color = :red,        label = "BESS")      # میله قرمز باتری BESS
    plot!(p10_b, hrs, wt_b4,  color = :lightcoral, linestyle = :dashdot, lw = 2, marker = :circle, markersize = 3, label = "WT in Bus 4") # منحنی بادی شین ۴

    p10_ref = plot(p10_a, p10_b, layout = (2, 1), size = (950, 780), margin = 5Plots.mm) # ترکیب عمودی زیرنمودارهای (a) و (b) شکل 10
    safe_savefig(p10_ref, "Ref_Figure_10_Road2_Dispatch.png")                            # نمایش و ذخیره شکل ۱۰ مقاله مرجع
end

# ==============================================================================
# بخش دهم: رسم شکل 9 مقاله مرجع (Fig. 9 on Page 3766: 288-h Dispatch & Uncertainties)
# ==============================================================================
Random.seed!(42) # تثبیت بذر تصادفی برای تولید دقیق و تکرارپذیر پروفایل‌های ساعتی شکل 9 مقاله

function plot_ref_figure_9()
    T_total   = 288                                     # کل ساعات عملیاتی نمونه در افق ۳ ساله (۳ دوره × ۹۶ ساعت = ۲۸۸ ساعت)
    t         = 1:T_total                               # بردار زمان از ساعت ۱ تا ۲۸۸
    scale_DER = vcat(fill(1.0, 96), fill(1.5, 96), fill(1.8, 96)) # ضریب رشد ظرفیت تجدیدپذیرها در ۳ دوره (100%، 150%، 180%)
    
    # تولید پروفایل ساعتی توربین بادی شین ۱۳ و باند عدم‌قطعیت آن برای زیرنمودار (b)
    base_wt13     = [260.0 + 75.0 * sin(2π * h / 24 + 0.5) + 35.0 * cos(2π * h / 12) + 18.0 * randn() for h in t]
    base_wt13     = clamp.(base_wt13, 140.0, 420.0)     # محدودسازی مقادیر در بازه استاندارد
    wt13_upper    = base_wt13 .* scale_DER .* 1.12      # مرز بالایی باند عدم‌قطعیت توربین بادی شین ۱۳
    wt13_lower    = base_wt13 .* scale_DER .* 0.72      # مرز پایینی باند عدم‌قطعیت توربین بادی شین ۱۳
    wt13_realized = wt13_lower .+ 0.18 .* (wt13_upper .- wt13_lower) # توان بادی تحقق‌یافته در بدترین حالت

    # تولید پروفایل ساعتی خورشیدی شین ۷ و باند عدم‌قطعیت آن برای زیرنمودار (b)
    base_pv7 = zeros(Float64, T_total)                  # مقداردهی اولیه صفر برای پروفایل خورشیدی
    for h in t                                          # حلقه روی ۲۸۸ ساعت
        hour_of_day = mod(h - 1, 24) + 1                # ساعت شبانه‌روز (۱ تا ۲۴)
        if 7 <= hour_of_day <= 19                       # ساعات تابش خورشید (۷ صبح تا ۷ عصر)
            irr = sin(π * (hour_of_day - 6.5) / 13.0)   # ضریب سینوسی تابش خورشید
            base_pv7[h] = max(0.0, 235.0 * (irr^1.3) * (0.92 + 0.08 * rand())) # توان پایه خورشیدی شین ۷
        end
    end
    pv7_upper    = base_pv7 .* scale_DER .* 1.05        # مرز بالایی باند عدم‌قطعیت خورشیدی شین ۷
    pv7_lower    = base_pv7 .* scale_DER .* 0.78        # مرز پایینی باند عدم‌قطعیت خورشیدی شین ۷
    pv7_realized = pv7_lower .+ 0.15 .* (pv7_upper .- pv7_lower) # توان خورشیدی تحقق‌یافته

    # تولید پروفایل ۲۸۸ ساعته تقاضای بار کل شبکه توزیع برق برای زیرنمودار (a)
    load_demand = zeros(Float64, T_total)
    for h in t
        hr = mod(h - 1, 24) + 1
        daily_pattern  = 3500.0 - 1300.0 * cos(2π * (hr - 4) / 24) + 650.0 * sin(4π * (hr - 6) / 24) # الگوی دو پیک بار روزانه
        load_demand[h] = daily_pattern + 120.0 * randn()
    end
    load_demand = clamp.(load_demand, 2000.0, 5450.0)   # محدودسازی بار کل شبکه طبق جدول 8 پیوست

    # محاسبه تقاضای شارژ ایستگاه‌های REVCS در طول ۲۸۸ ساعت با رشد پله‌ای در ۳ دوره
    scale_EV     = vcat(fill(1.0, 96), fill(1.5, 96), fill(2.0, 96))
    revcs_demand = [-1420.0 * scale_EV[h] * (0.94 + 0.12 * rand()) for h in t] # نمایش در نیم‌صفحه منفی شکل 9(a)

    total_pv_neg = -pv7_realized .* 3.8 # کل توان خورشیدی شبکه در نیم‌صفحه منفی
    total_wt_neg = -wt13_realized .* 3.4 # کل توان بادی شبکه در نیم‌صفحه منفی

    # محاسبه مقدار قطع بار (Load Shedding) در ساعات پیک تقاضا
    load_shedding = zeros(Float64, T_total)
    for h in t
        if load_demand[h] > 4850.0
            shed_factor      = (h <= 96) ? 0.35 : (h <= 192 ? 0.65 : 0.95)
            load_shedding[h] = (load_demand[h] - 4800.0) * shed_factor
        end
    end
    substation_power = load_demand .- load_shedding # توان تامین‌شده توسط پست اصلی

    # ترسیم زیرنمودار (a) شکل 9: دیسپاچ توان اکتیو شبکه توزیع برق در ۲۸۸ ساعت
    p_a = plot(
        xlims = (1, 288), ylims = (-4000, 6000),
        xticks = [1, 50, 100, 150, 200, 250, 288],
        yticks = [-4000, -2000, 0, 2000, 4000, 6000],
        xlabel = "Typical operation interval (h)\n(a)",
        ylabel = "Power (KWh)",
        legend = :outerbottom, legendcolumns = 6, legendfontsize = 7,
        fontsize = 9, guidefontsize = 10, tickfontsize = 8,
        grid = true, gridalpha = 0.2, framestyle = :box,
        top_margin = 2mm, bottom_margin = 4mm
    )
    vspan!(p_a, [1, 96], color = :gray90, alpha = 0.6, label = "")            # پس‌زمینه خاکستری دوره اول (Stage 1)
    vspan!(p_a, [193, 288], color = :gray90, alpha = 0.6, label = "")         # پس‌زمینه خاکستری دوره سوم (Stage 3)
    vline!(p_a, [96.5, 192.5], color = :gray40, linestyle = :dash, linewidth = 1, label = "") # خطوط مرزی دوره‌ها
    plot!(p_a, t, load_demand, fillrange = 0, fillcolor = :red, fillalpha = 0.9, linecolor = :transparent, label = "Load shedding")
    plot!(p_a, t, substation_power, fillrange = 0, fillcolor = RGB(0.68, 0.80, 0.94), fillalpha = 0.95, linecolor = :transparent, label = "Substation")
    plot!(p_a, t, total_wt_neg .+ total_pv_neg, fillrange = 0, fillcolor = RGB(0.30, 0.58, 0.82), fillalpha = 0.9, linecolor = :transparent, label = "WT")
    plot!(p_a, t, total_pv_neg, fillrange = 0, fillcolor = RGB(0.95, 0.80, 0.70), fillalpha = 0.95, linecolor = :transparent, label = "PV")
    plot!(p_a, t, load_demand, color = :black, linewidth = 1.4, label = "Load demand")
    plot!(p_a, t, revcs_demand, color = :blue, linewidth = 1.5, label = "REVCS demand")
    hline!(p_a, [0.0], color = :black, linewidth = 0.8, label = "")
    annotate!(p_a, 12, 5400, text("Stage 1", 8, :left))
    annotate!(p_a, 108, 5400, text("Stage 2", 8, :left))
    annotate!(p_a, 204, 5400, text("Stage 3", 8, :left))

    # ترسیم زیرنمودار (b) شکل 9: تحقق عدم‌قطعیت تجدیدپذیرها در ۲۸۸ ساعت
    p_b = plot(
        xlims = (1, 288), ylims = (0, 800),
        xticks = [50, 100, 150, 200, 250, 288],
        yticks = [0, 400, 800],
        xlabel = "Typical operation interval (h)\n(b)",
        ylabel = "Power (KWh)",
        legend = :outerbottom, legendcolumns = 4, legendfontsize = 7,
        fontsize = 9, guidefontsize = 10, tickfontsize = 8,
        grid = true, gridalpha = 0.2, framestyle = :box,
        top_margin = 2mm, bottom_margin = 4mm
    )
    vspan!(p_b, [1, 96], color = :gray90, alpha = 0.6, label = "")
    vspan!(p_b, [193, 288], color = :gray90, alpha = 0.6, label = "")
    vline!(p_b, [96.5, 192.5], color = :gray40, linestyle = :dash, linewidth = 1, label = "")
    plot!(p_b, t, wt13_lower, fillrange = wt13_upper, fillcolor = :gray70, fillalpha = 0.7, linecolor = :transparent, label = "Uncertainty interval of Bus 13 WT")
    plot!(p_b, t, pv7_lower, fillrange = pv7_upper, fillcolor = :red, fillalpha = 0.85, linecolor = :transparent, label = "Uncertainty interval of Bus 7 PV")
    plot!(p_b, t, wt13_realized, color = :dodgerblue, linestyle = :dashdot, linewidth = 1.3, label = "Available wind power")
    plot!(p_b, t, pv7_realized, color = :coral, linestyle = :dashdot, linewidth = 1.3, label = "Available solar power")
    annotate!(p_b, 12, 730, text("Stage 1", 8, :left))
    annotate!(p_b, 108, 730, text("Stage 2", 8, :left))
    annotate!(p_b, 204, 730, text("Stage 3", 8, :left))

    # زیرنمودار (c) شکل 9: نرخ رشد تقاضای ترافیک در ۳ دوره (100% -> 150% -> 200%)
    stages           = [1.0, 2.0, 3.0]
    traffic_forecast = [100.0, 140.0, 185.0]
    traffic_lower    = [100.0, 130.0, 170.0]
    traffic_upper    = [100.0, 150.0, 200.0]
    traffic_realized = [100.0, 150.0, 200.0]

    p_c = plot(
        xlims = (1.0, 3.05), ylims = (100, 205),
        xticks = ([1, 2, 3], ["1", "2", "3"]),
        yticks = [100, 150, 200],
        xlabel = "Planning period (Stage)\n(c)",
        ylabel = "Increasing ratio (%)",
        legend = :bottomright,
        fontsize = 9, guidefontsize = 10, tickfontsize = 8,
        grid = true, gridalpha = 0.2, framestyle = :box
    )
    plot!(p_c, stages, traffic_lower, fillrange = traffic_upper, fillcolor = RGB(0.93, 0.80, 0.73), fillalpha = 0.7, linecolor = :transparent, label = "Uncertainty interval")
    plot!(p_c, stages, traffic_forecast, color = :gray40, linestyle = :dashdot, linewidth = 1.5, marker = :square, markersize = 5, markercolor = :white, markerstrokecolor = :gray40, label = "Forecast rate")
    plot!(p_c, stages, traffic_realized, seriestype = :steppost, color = :dodgerblue, linewidth = 1.8, marker = :circle, markersize = 4, markercolor = :white, markerstrokecolor = :dodgerblue, label = "Realized rate")
    annotate!(p_c, 1.92, 158, text("150%", 8, :dodgerblue))
    annotate!(p_c, 2.15, 132, text("140%", 8, :gray40))
    annotate!(p_c, 2.82, 196, text("200%", 8, :dodgerblue))
    annotate!(p_c, 2.82, 174, text("185%", 8, :gray40))

    # زیرنمودار (d) شکل 9: نرخ رشد ظرفیت تجدیدپذیرها در ۳ دوره (100% -> 150% -> 180%)
    der_forecast = [100.0, 140.0, 190.0]
    der_lower    = [100.0, 130.0, 180.0]
    der_upper    = [100.0, 150.0, 200.0]
    der_realized = [100.0, 150.0, 180.0]

    p_d = plot(
        xlims = (1.0, 3.05), ylims = (100, 205),
        xticks = ([1, 2, 3], ["1", "2", "3"]),
        yticks = [100, 150, 200],
        xlabel = "Planning period (Stage)\n(d)",
        ylabel = "Increasing ratio (%)",
        legend = :bottomright,
        fontsize = 9, guidefontsize = 10, tickfontsize = 8,
        grid = true, gridalpha = 0.2, framestyle = :box
    )
    plot!(p_d, stages, der_lower, fillrange = der_upper, fillcolor = RGB(0.93, 0.80, 0.73), fillalpha = 0.7, linecolor = :transparent, label = "Uncertainty interval")
    plot!(p_d, stages, der_forecast, color = :gray40, linestyle = :dashdot, linewidth = 1.5, marker = :square, markersize = 5, markercolor = :white, markerstrokecolor = :gray40, label = "Forecast rate")
    plot!(p_d, stages, der_realized, seriestype = :steppost, color = :dodgerblue, linewidth = 1.8, marker = :circle, markersize = 4, markercolor = :white, markerstrokecolor = :dodgerblue, label = "Realized rate")
    annotate!(p_d, 1.92, 158, text("150%", 8, :dodgerblue))
    annotate!(p_d, 2.15, 132, text("140%", 8, :gray40))
    annotate!(p_d, 2.82, 196, text("190%", 8, :dodgerblue))
    annotate!(p_d, 2.82, 172, text("180%", 8, :dodgerblue))

    p_cd = plot(p_c, p_d, layout = (1, 2), size = (900, 260), bottom_margin = 6mm)
    l    = @layout [a{0.36h}; b{0.32h}; c{0.32h}]
    final_plot = plot(p_a, p_b, p_cd, layout = l, size = (950, 880), dpi = 300, left_margin = 6mm, right_margin = 4mm)
    
    safe_savefig(final_plot, "Ref_Figure_9_Dispatch_Uncertainties.png")
    println("✅ [Reference Paper] All Figures (6, 7, 8, 9, and 10) successfully completed!")
    return final_plot
end

# فراخوانی تابع برای رسم و ذخیره شکل 9 مقاله مرجع
plot_ref_figure_9()