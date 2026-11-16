# برای هر مجموعه فرض در فرآیند مستقل اجرا شود؛ ثابت‌های محیط پیش از include خوانده می‌شوند.
include(joinpath(@__DIR__,"revcs_planning19.jl"))
id=isempty(ARGS) ? "baseline" : only(ARGS)
out=joinpath(@__DIR__,"physical_studies");mkpath(out)
rows=NamedTuple[]
for mode in (:printed_eq33,:installed_capacity)
    started=time()
    bound=continuous_path_lower_bound(;path=[nominal_scenario(1)],capacity_mode=mode,seconds=30.)
    push!(rows,(;study=id,capacity_mode=string(mode),soc_min=SOC_MIN,soc_initial=SOC_INITIAL,
        soc_max=SOC_MAX,cycle=string(BATTERY_CYCLE_MODE),root_lp_lower=bound.lower,
        status=bound.status,seconds=time()-started,robust_policy_claim=false))
    GC.gc()
end
write_rows(joinpath(out,"assumptions_"*id*".csv"),rows)
println(rows)
