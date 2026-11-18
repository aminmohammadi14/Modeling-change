# گام اول بازنویسی: خواندن و کنترل داده‌های مستند، بدون ساخت مدل یا جواب بهینه‌سازی.
module REVCSDataStep01
using TOML, SHA, Printf
export load_case, profiles, require_optimization_ready

# خطای داده باید روشن و فوری باشد؛ هیچ مقدار پیش‌فرضی جایگزین دادهٔ مفقود نمی‌شود.
function demand(condition::Bool, message::String)
    condition || throw(ArgumentError(message))
end

# اثر انگشت فایل‌های داده، تغییر ناخواستهٔ ورودی پس از استخراج را آشکار می‌کند.
function verify_checksums(root)
    for line in eachline(joinpath(root, "data", "SHA256SUMS.txt"))
        isempty(strip(line)) && continue
        expected, relative = split(line; limit=2)
        actual = bytes2hex(sha256(read(joinpath(root, strip(relative)))))
        demand(actual == expected, "اثر انگشت داده متفاوت است: $relative")
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
    data = TOML.parsefile(joinpath(root,"data","tables.toml"))
    case = TOML.parsefile(joinpath(root,"data","case.toml"))
    sources = TOML.parsefile(joinpath(root,"data","sources.toml"))
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

# ورود از خط فرمان؛ برای include شدن در تست‌ها هیچ اجرای ناخواسته‌ای رخ نمی‌دهد.
if abspath(PROGRAM_FILE) == @__FILE__
    root = isempty(ARGS) ? (@__DIR__) : abspath(ARGS[1])
    output = length(ARGS) < 2 ? joinpath(root,"results") : abspath(ARGS[2])
    REVCSDataStep01.run(root,output)
end
