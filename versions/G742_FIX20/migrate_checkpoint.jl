# انتقال داده‌های قابل‌اثبات یک پوشهٔ قدیمی یا نسل جاری به یک پوشهٔ جدید، بدون حل مستر
include("REVCS19_FIX20.jl")
const F=REVCSFix20
function migrate(source,destination)
    src=abspath(source);out=abspath(destination)
    isdir(src) || error("Source directory missing")
    mkdir(out)
    o=F.g742_args(["--output=$out"])
    cfg=F.g742_config(o);F.G7_ACTIVE[]=cfg
    g=F.state_grids(;charging_kw=100.0,storage_kwh=20.0,pv_kw=30.0)
    st,z0,h=F.g742_state(o,g)
    domain,scope=F.g742_domain(o,g,st,z0,h)
    build=u->first(F.build_certified_stage(3,st,u,g;direction=:lower,seconds=o.seconds,
        capacity_mode=cfg.capacity_mode,initial_station_state=z0))
    F.FIX20_RESUME[]=src
    cols,u,lo=F.pool20(o,build,domain,h,scope)
    F.commitstate(o,cols,u;candidate=F.pending[])
    println("MIGRATION_COMPLETE  columns=$(length(cols))  lower=$lo  scenario=$(F.udigest(u))")
end
length(ARGS)==2 || error("migrate_checkpoint.jl SOURCE NEW_DESTINATION")
migrate(ARGS...)
