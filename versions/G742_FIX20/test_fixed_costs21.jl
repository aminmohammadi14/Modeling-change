# ممیزی هزینهٔ LP و دوگانِ هر سه ستون در سناریوهای بررسی ماتریس
using Test,JuMP,HiGHS
include("REVCS19_FIX20.jl")
const F=REVCSFix20
const C=F.Core20
function run_checks(out)
    mkpath(out)
    o=F.g742_args(["--threads=1","--seconds-per-solve=90","--output=$out"])
    cfg=F.g742_config(o);F.G7_ACTIVE[]=cfg
    g=F.state_grids(;charging_kw=100.0,storage_kwh=20.0,pv_kw=30.0)
    state,z0,sha=F.g742_state(o,g);dom,scope=F.g742_domain(o,g,state,z0,sha)
    builder=u->first(F.build_certified_stage(3,state,u,g;direction=:lower,seconds=o.seconds,capacity_mode=cfg.capacity_mode,initial_station_state=z0))
    F.FIX20_RESUME[]=joinpath(@__DIR__,"results","real_run")
    cols,_,_=F.pool20(o,builder,dom,sha,scope)
    us=F.candidates20()
    h=deepcopy(us[end]);l=us[2]
    for k in ("beta_wt","beta_pv","psi"),sgn in ("_plus","_minus")
        k2=k*sgn;h[k2][:,1:2:end].=l[k2][:,1:2:end]
    end
    push!(us,F.create_uncertainty_scenario("alternating hours",3,1.,0.,0.,1.,
        [h[k] for k in ("beta_wt_plus","beta_wt_minus","beta_pv_plus","beta_pv_minus","psi_plus","psi_minus")]...))
    rows=NamedTuple[]
    for (j,u) in enumerate(us), (i,p) in enumerate(cols)
        m=builder(u);C.fix_pattern!(m,p);optimize!(m)
        st=termination_status(m)
        ok,err=F.feasible_audit(m,o.tol)
        obj=ok ? objective_value(m) : Inf
        dual=has_duals(m) && st==F.MOI.OPTIMAL ? dual_objective_value(m) : -Inf
        ray=st==F.MOI.INFEASIBLE ? F.g742_fix14_ray_audit(m) : nothing
        status=if st==F.MOI.OPTIMAL && ok && isapprox(obj,dual;rtol=1e-7)
            "MATCHED_PRIMAL_DUAL"
        elseif ray!==nothing && ray.certificate_numerically_validated
            "VALIDATED_INFEASIBILITY_RAY"
        else
            "UNRESOLVED"
        end
        println("scenario=$j pattern=$i status=$st validation=$status")
        flush(stdout)
        push!(rows,(;scenario=F.udigest(u),column=F.colid(p),termination=string(st),primal=obj,
            dual,residual=err,validation=status))
        F.write_rows(joinpath(out,"COST_LP_AUDIT.csv"),rows)
        @test st!=F.MOI.OPTIMAL || status=="MATCHED_PRIMAL_DUAL"
    end
end
@testset "fixed physical cost replays" run_checks(isempty(ARGS) ? mktempdir() : abspath(ARGS[1]))
