include("REVCS19_FIX20.jl")
using Test
const F=REVCSFix20
# بازیابی سه ستون ذخیره‌شده، بازحل ستون سوم و آزمون رد فایل آسیب‌دیده
source=isempty(ARGS) ? joinpath(@__DIR__,"results","real_run") : abspath(ARGS[1])
out=length(ARGS)<2 ? mktempdir() : abspath(ARGS[2])
o=F.g742_args(["--mode=full-phi3","--threads=2","--seconds-per-solve=60","--output="*out])
mkpath(o.output)
cfg=F.g742_config(o)
F.G7_ACTIVE[]=cfg
g=F.state_grids(;charging_kw=100.0,storage_kwh=20.0,pv_kw=30.0)
st,z0,sha=F.g742_state(o,g)
dom,scope=F.g742_domain(o,g,st,z0,sha)
builder=u->first(F.build_certified_stage(3,st,u,g;direction=:lower,seconds=o.seconds,capacity_mode=cfg.capacity_mode,initial_station_state=z0))
F.FIX20_RESUME[]=source
cols,u,lower=F.pool20(o,builder,dom,sha,scope)
@test length(cols)==3
p=last(cols)
m=builder(first(F.candidates20()))
F.Core20.fix_pattern!(m,p)
F.Core20.solve_tracked!(m;context="independent_saved_column_lp")
row=F.Core20.min_bounds(m)
println("VERIFIED_SAVED_COLUMN status=",row.status," cost=",row.upper)
@test row.feasible && isapprox(row.upper,1704104.948319438;rtol=1e-8)
@test first(F.feasible_audit(m,o.tol))
@test lower==F.validate_lb(F.ledger["lb"],u)
@test isapprox(lower,1682535.613777655;rtol=1e-10)
F.write_rows(joinpath(o.output,"COLUMN_REPLAY.csv"),[row])
# دو نسل پی‌درپی برای آزمون بازیابی و بازگشت به نسل معتبر قبلی
F.commitstate(o,cols,u)
F.commitstate(o,cols,u)
vars=filter(v->F.is_binary(v)||F.is_integer(v),F.all_variables(builder(first(dom.factory()))))
ident=F.ledger["identity"]
d,again,best,_=F.restoredir(o.output,ident,vars)
@test d["lb"]["bound"]==lower && F.udigest(best)==F.udigest(u)
@test F.colid.(again)==F.colid.(cols)
mkdir(joinpath(o.output,".pending-orphan"))
@test F.readgeneration(o.output,"CURRENT",ident,vars)[1]["lb"]==d["lb"]
for key in ("stage","predecessor","domain","layout","grid","scope","topology","algorithm")
    @test_throws ErrorException F.readgeneration(o.output,"CURRENT",merge(ident,Dict(key=>"different")),vars)
end
id,h=split(strip(read(joinpath(o.output,"CURRENT"),String)))
statefile=joinpath(o.output,id,"state.toml")
original=read(statefile)
function replace_state(data)
    F.tablefile(statefile,data)
    write(joinpath(o.output,"CURRENT"),id*" "*F.digestfile(statefile)*"\n")
end
for change in (x->(x["lb"]["bound"]+=1),x->(x["upper"]=0.0),x->push!(x["columns"],first(x["columns"])),
               x->(x["candidate_file"]="missing"),x->(x["phase"]="unknown"),x->(x["witness_file"]="bad"))
    data=deepcopy(d)
    change(data);replace_state(data)
    @test_throws Exception F.readgeneration(o.output,"CURRENT",ident,vars)
end
write(statefile,original);write(joinpath(o.output,"CURRENT"),id*" "*h*"\n")
write(joinpath(o.output,id,"column_3.tsv"),"damaged")
@test F.restoredir(o.output,ident,vars)[1]["generation"]!=id
@test F.restoredir(o.output,ident,vars)[1]["lb"]["bound"]==lower
mktempdir() do dir
    for f in ["POOL.tsv"; ["column_$i.tsv" for i in 1:3]]
        cp(joinpath(source,f),joinpath(dir,f))
    end
    open(joinpath(dir,"column_3.tsv"),"a") do io
        write(io,"x")
    end
    F.FIX20_RESUME[]=dir
    @test_throws "Damaged resume column" F.pool20(o,builder,dom,sha,scope)
end
println("RECOVERY_AND_CORRUPTION_CHECK_PASS")
