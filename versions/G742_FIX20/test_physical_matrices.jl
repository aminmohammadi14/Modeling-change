# مقایسهٔ تمام سطرها و تابع هدف پیش از تثبیت الگو، شامل حدود و مجموعه‌های صحیح
using Test, JuMP, SHA
include("REVCS19_FIX20.jl")
const F=REVCSFix20
const C=F.Core20
const MOI=F.MOI
function indicator_values(u)
    z=Float64[u["omega_u_plus"],u["omega_u_minus"],u["omega_p_plus"],u["omega_p_minus"]]
    for (rows,k,profile) in ((F.WT_set,"beta_wt",F.wt_profile),(F.PV_PDN_set,"beta_pv",F.pv_profile),
                             (1:F.num_roads,"psi",F.pv_profile))
        for i in rows,h in F.Tau_set
            profile[h]>0 || continue
            push!(z,u[k*"_plus"][i,h],u[k*"_minus"][i,h])
        end
    end
    return z
end
function fingerprint(m,z,uz,excluded)
    ids=Dict(v=>j for (j,v) in enumerate(z))
    xs=filter(v->!haskey(ids,v),all_variables(m))
    ord=Dict(v=>i for (i,v) in enumerate(xs));cont=Set(xs);ints=Dict{VariableRef,Int}()
    evaluate(poly)=sum((a*prod((uz[i] for i in k);init=1.0) for (k,a) in poly);init=0.0)
    fmt(x)=iszero(round(x;digits=8)) ? 0.0 : round(x;digits=8)
    function row(f,set)
        off,A=C.split_parametric_expression(f,ids,ints,cont)
        c=evaluate(off)
        terms=sort([(ord[v],fmt(evaluate(p))) for (v,p) in A if fmt(evaluate(p))!=0])
        sides=if set isa MOI.EqualTo
            (:eq,fmt(set.value-c))
        elseif set isa MOI.GreaterThan
            (:ge,fmt(set.lower-c))
        elseif set isa MOI.LessThan
            (:le,fmt(set.upper-c))
        elseif set isa MOI.Interval
            (:interval,fmt(set.lower-c),fmt(set.upper-c))
        else
            (string(typeof(set)),fmt(c))
        end
        return bytes2hex(sha256(string(sides,terms)))
    end
    hashes=sort([row(constraint_object(r).func,constraint_object(r).set) for r in
        all_constraints(m;include_variable_in_set_constraints=true) if !(r in excluded)])
    return length(xs),length(hashes),bytes2hex(sha256(Vector{UInt8}(codeunits(join(hashes))))),row(objective_function(m),:objective)
end
function check()
    o=F.g742_args(["--threads=1","--output="*mktempdir()])
    cfg=F.g742_config(o); F.G7_ACTIVE[]=cfg
    g=F.state_grids(;charging_kw=100.0,storage_kwh=20.0,pv_kw=30.0)
    st,z0,_=F.g742_state(o,g)
    build(u,m)=F.build_certified_stage(3,st,u,g;direction=:lower,seconds=30.,
        capacity_mode=cfg.capacity_mode,initial_station_state=z0,shared_model=m)
    sym=Model();z,u,_=F.symbolic_uncertainty(sym,3)
    excluded=Set(all_constraints(sym;include_variable_in_set_constraints=true))
    build(u,sym)
    us=F.candidates20()
    h=deepcopy(us[end]); l=us[2]
    for k in ("beta_wt","beta_pv","psi"),sgn in ("_plus","_minus")
        k2=k*sgn
        h[k2][:,1:2:end].=l[k2][:,1:2:end]
    end
    push!(us,F.create_uncertainty_scenario("alternating hours",3,1.,0.,0.,1.,
        [h[k] for k in ("beta_wt_plus","beta_wt_minus","beta_pv_plus","beta_pv_minus","psi_plus","psi_minus")]...))
    for u in us
        F.validate_scenario(3,u)
        num=first(build(u,nothing))
        bits=indicator_values(u)
        @test length(bits)==length(z)
        a=fingerprint(sym,z,bits,excluded);b=fingerprint(num,[],[],Set())
        println(u["name"]," symbolic=",a," numerical=",b)
        flush(stdout)
        @test a==b
    end
end
@testset "frozen physical matrix and objective equivalence to eight decimal places" check()
