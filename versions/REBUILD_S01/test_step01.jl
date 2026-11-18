# تست‌های این فایل، کنترل نرم‌افزار و انتقال داده‌اند؛ نتیجهٔ مقاله محسوب نمی‌شوند.
using Test, TOML, SHA
include("run_step01.jl")
using .REVCSDataStep01

@testset "S01: source data and time indexing" begin
    b=load_case()
    p=profiles(b)
    @test length(p.wind) == length(p.solar) == length(p.load) == 96
    @test size(p.traffic) == (96,9)
    # نقاط شاهد از جدول‌های چاپ‌شده: ابتدا، مرز روز، انتها و سطر ادامهٔ صفحهٔ بعد.
    @test p.wind[[1,24,25,96]] == [0.8588,0.6960,0.8520,0.6094]
    @test p.solar[[7,20,31,96]] == [0.1495,0.3538,0.1309,0.0]
    @test p.load[[20,21,24,25,96]] == [3307.62,2793.06,2381.11,2395.75,2246.39]
    @test p.traffic[1,:] == [558.88,688.21,783.89,766.87,851.40,417.42,872.69,750.69,505.26]
    for day in 2:4
        @test p.traffic[(day-1)*24+1:day*24,:] == p.traffic[1:24,:]
    end
    @test count(>(0),p.solar) == 56
    @test [r[1] for r in b.data["table1"]["rows"] if r[4]] == [2,3,10,14,16]
    @test sum(r[3] for r in b.data["table4"]["rows"]) == 1712.0
    @test sum(r[3] for r in b.data["table6"]["rows"]) == 1174.0
    @test b.data["table11"]["rows"][end] == [25,29,0.5,0.5,2776.44]
    @test length(b.data["table11"]["rows"]) - b.case["scope"]["buses"] + 1 == 5
    @test b.data["table9"]["rows"][1][4:end] == ["/","/","/"]
    @test_throws ArgumentError require_optimization_ready(b)
    # خرابی مصنوعی فقط در پوشهٔ موقت برای اطمینان از توقف روی ورودی تغییرکرده است.
    mktempdir() do dir
        cp(joinpath(@__DIR__,"data"),joinpath(dir,"data"))
        open(joinpath(dir,"data","tables.toml"),"a") do io
            write(io,"\n# intentional corruption test\n")
        end
        @test_throws ArgumentError load_case(dir)
        # بدون GC اجباری، حذف فوری باید ممکن باشد؛ ویندوز فایل باز را قفل می‌کند.
        checksum = joinpath(dir,"data","SHA256SUMS.txt")
        rm(checksum)
        @test !isfile(checksum)
    end
    mktempdir() do dir
        report=REVCSDataStep01.run(@__DIR__,dir)
        @test report["optimization_run"] === false
        @test report["paper_results_reproduced"] === false
        @test sort(readdir(dir)) == ["load.svg","solar.svg","traffic.svg","validation.toml","wind.svg"]
    end
    # حذف یال و شکستن اتصال، آزمون مستقل کنترل گراف است و دادهٔ مسئله را تغییر نمی‌دهد.
    lines=b.data["table11"]["rows"]
    @test !REVCSDataStep01.connected([r for r in lines if !(1 in r[1:2])],33)
end
