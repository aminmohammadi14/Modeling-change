# همهٔ گام‌ها و فرض‌های این فایل تنظیم آزمایش نرم‌افزارند؛ عدد جدیدی به مقاله نسبت داده نمی‌شود.
include(joinpath(@__DIR__,"revcs_planning19.jl"))
out=joinpath(@__DIR__,"physical_studies");mkpath(out)
specs=[(;charging_kw=100.,storage_kwh=40.,pv_kw=60.),
       (;charging_kw=50.,storage_kwh=20.,pv_kw=30.),
       (;charging_kw=20.,storage_kwh=10.,pv_kw=15.)]
study=root_grid_study(specs;capacity_mode=:installed_capacity,seconds=30.,output_dir=out)
println("ROOT_SENSITIVITY=",study.rows)
GC.gc()
started=time()
lower=continuous_path_lower_bound(;capacity_mode=:installed_capacity,seconds=60.)
println("THREE_PERIOD_CONTINUOUS_LP=",lower)
open(joinpath(out,"continuous_lower.toml"),"w") do io
    TOML.print(io,Dict("lower"=>lower.lower,"horizon"=>lower.horizon,"scope"=>lower.scope,
        "status"=>lower.status,"integer_relaxation"=>lower.integer_relaxation,
        "seconds"=>time()-started,"path"=>"nominal forecasts from supplied data",
        "robust_upper"=>Inf,"finite_total_error_certificate"=>false,
        "capacity_mode"=>"installed_capacity","soc_initial"=>SOC_INITIAL,
        "soc_min"=>SOC_MIN,"soc_max"=>SOC_MAX,"battery_cycle"=>string(BATTERY_CYCLE_MODE)))
end
write_rows(joinpath(out,"solver_trace.csv"),RC.SOLVER_TRACE)
