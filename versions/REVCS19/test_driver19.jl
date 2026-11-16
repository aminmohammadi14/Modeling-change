using Test, JuMP, HiGHS, SCIP
import MathOptInterface as MOI
include(joinpath(@__DIR__,"revcs_planning19.jl"))

@testset "Farkas gate rejects an unfinished nonpositive witness" begin
    for st in (MOI.TIME_LIMIT,MOI.ITERATION_LIMIT,MOI.OTHER_ERROR,MOI.INTERRUPTED)
        @test RC.farkas_gate(st,true,0.,1.)==:unresolved
        @test RC.farkas_gate(st,false,NaN,Inf)==:unresolved
        @test RC.farkas_gate(st,true,0.2,1.)==:witness
    end
    @test RC.farkas_gate(MOI.OPTIMAL,true,0.,0.)==:covered
    @test RC.farkas_gate(MOI.OPTIMAL,true,0.,0.01)==:unresolved
    @test RC.farkas_gate(MOI.OPTIMAL,false,NaN,0.)==:unresolved
end

# آزمون الگوریتم روی مسئلهٔ مصنوعی کوچک؛ این اعداد داده یا نتیجهٔ مقاله نیستند.
function toy_block(m,t,previous,u;direction=:lower,lower_cuts=RC.BinaryCut[],
        upper_samples=RC.UpperSample[],upper_certificate=nothing)
    x=@variable(m,binary=true)
    y=@variable(m,lower_bound=0.,upper_bound=1.)
    a=@variable(m,lower_bound=0.)
    @constraint(m,x>=previous)
    @constraint(m,y>=u-x)
    cost=@expression(m,2*(x-previous)+10y)
    if t==3
        fix(a,0.;force=true)
    elseif direction==:lower
        for c in lower_cuts;@constraint(m,a>=c.intercept+c.slope[1]*x);end
    else
        RC.attach_upper!(m,[x],a,upper_samples,upper_certificate)
    end
    @objective(m,Min,cost+a)
    return x,cost
end
function toy_build(t,prev,u;seconds=30.,kwargs...)
    m=RC.new_model(;seconds)
    x,cost=toy_block(m,t,prev,u;kwargs...)
    return m,capture->(;state=round(Int,value(x)),immediate=value(cost),operations=Dict{String,Any}())
end
function toy_oracle(t,prev;seconds=30.,max_iters=20,rtol=1e-8,kwargs...)
    builder=u->first(toy_build(t,prev,u;seconds,kwargs...))
    role=t==3 ? :exact : kwargs[:direction]
    if t==1
        m=builder(0.);RC.solve_tracked!(m);r=RC.min_bounds(m)
        return RC.CCGResult(r.lower,r.upper,RC.gap_closed(r.lower,r.upper,rtol),false,0.,
            [RC.integer_pattern(m)],NamedTuple[],"toy Q1",:root,role)
    end
    factory=m->begin
        z=@variable(m,binary=true)
        ([z],z,()->Float64(round(value(z))))
    end
    block=(m,u)->toy_block(m,t,prev,u;kwargs...)
    RC.solve_native_ccg(builder,factory,block,0.;optimizer=SCIP.Optimizer,
        scope="toy Q$t",seconds,max_iters,rtol,bound_role=role)
end
function toy_cut(t,prev,u;lower_cuts,seconds,max_iters,rtol)
    builder=()->begin
        m=RC.new_model(;seconds);b=@variable(m,binary=true)
        toy_block(m,t,b,u;lower_cuts)
        (m,[b])
    end
    RC.lagrangian_cut(builder,[prev];seconds,max_iters,rtol,scope="toy Q$t")
end
toy=PlanningProblem(3,0,x->[x],t->"toy Q$t",toy_oracle,toy_build,toy_cut,
    (t,u)->(u in (0.,1.) && (t!=1 || u==0.) || error("invalid toy uncertainty")),b->only(b))

function exact_toy(t,prev)
    t==4 && return 0.
    return maximum(minimum(2*(x-prev)+10max(0.,u-x)+exact_toy(t+1,x)
        for x in prev:1) for u in (t==1 ? (0.,) : (0.,1.)))
end
@testset "Whole-horizon forward/backward versus exhaustive dynamic programming" begin
    exact=exact_toy(1,0)
    @test exact==2.
    result=run_improved_rddp(toy;iterations=5,seconds=20.,rtol=1e-5,
        output_dir=joinpath(@__DIR__,"toy_results"))
    @test result.converged
    @test result.lower≈exact atol=1e-5
    @test RC.gap_closed(result.lower,result.upper,1e-5)
    @test result.upper≈exact atol=1e-6
    @test result.best_policy!==nothing
    @test length(result.path)==3
    @test any(r.phase=="backward"&&r.stage==3 for r in result.phase_log)
    @test all(r.lower<=exact+1e-6 && r.upper>=exact-1e-6 for r in result.history)
    @test !isempty(result.solver_trace)
    for t in 2:3,c in result.archive.cuts[t],b in 0:1
        @test c.intercept+c.slope[1]*b<=exact_toy(t,b)+1e-6
    end
    for t in 2:3,s in values(result.archive.upper[t])
        @test s.value>=exact_toy(t,only(s.bits))-1e-6
    end
    paths=[[0.,u,v] for u in (0.,1.) for v in (0.,1.)]
    ev=evaluate_policy(toy,result.best_policy,paths;seconds=20.,output_dir=joinpath(@__DIR__,"toy_results"))
    @test ev.summary.failed==0
    @test ev.summary.maximum<=result.upper+1e-6
    @test ev.summary.robust_upper_claim==false
    # یک پیشوند یکسان، بدون دریافت مشاهدهٔ آینده، همان تصمیم را بازمی‌گرداند.
    d1=planning_decision(toy,result.best_policy,1,0,0.;direction=:upper)
    d2=planning_decision(toy,result.best_policy,1,0,0.;direction=:upper)
    @test d1.state==d2.state
    restored=load_policy(joinpath(@__DIR__,"toy_results","certified_policy.toml"),toy)
    @test restored isa UnverifiedPolicyImport
    @test_throws MethodError evaluate_policy(toy,restored,paths)
    checked=revalidate_policy(toy,restored;seconds=20.,rtol=1e-8)
    @test checked.verified
    @test checked.upper≈result.upper atol=1e-6
    ev2=evaluate_policy(toy,checked.archive,paths;seconds=20.)
    @test [r.cost for r in ev2.rows]≈[r.cost for r in ev.rows]
    @test ev2.summary.portfolio_lp_successes==12
end

@testset "Audit data corrections and explicit-grid validation" begin
    @test count(>(0.),pv_profile)==56
    @test full_uncertainty_domain(2).cardinality==big(3)^1882
    m=Model();z,u,extract=symbolic_uncertainty(m,2)
    @test length(z)==3764
    @test sum(PD_bus_96)*num_buses≈sum(Total_Load_P_96)
    @test_throws ErrorException main(["--mode=plan"])
    @test_throws ErrorException main(["--unknown=x"])
end

@testset "Full binary-domain upper extrapolation without codebook restriction" begin
    target="global binary toy"
    exact=b->RC.CCGResult(7sum(b),7sum(b),true,false,nothing,RC.IntegerPattern[],NamedTuple[],target,:exact,:exact)
    cert=RC.certify_full_binary_upper(2,exact)
    @test cert.bound==14
    samples=[RC.UpperSample([0,0],exact([0,0]))]
    for b in ([0,0],[1,0],[0,1],[1,1])
        m=RC.new_model();@variable(m,x[1:2],Bin);@variable(m,a>=0)
        RC.attach_upper!(m,x,a,samples,cert)
        for (v,k) in zip(x,b);fix(v,k;force=true);end
        @objective(m,Min,a);optimize!(m)
        @test termination_status(m)==MOI.OPTIMAL
        @test objective_value(m)>=7sum(b)-1e-7
    end
    @test_throws ErrorException RC.certify_full_binary_upper(220,exact)
    bad=b->RC.CCGResult(-Inf,Inf,false,false,nothing,RC.IntegerPattern[],NamedTuple[],target,:unresolved,:upper)
    @test_throws ErrorException RC.certify_full_binary_upper(2,bad)
end
