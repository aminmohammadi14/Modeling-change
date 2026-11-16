using Test, JuMP, HiGHS, SCIP
import MathOptInterface as MOI
include(joinpath(@__DIR__,"test_driver19.jl"))

# دادهٔ زیر فقط مثال شمارش‌پذیر آزمون ریاضی است و هیچ ورودی مقاله را جایگزین نمی‌کند.
function audit_block(m,u)
    n=length(u)
    y=@variable(m,[1:n],Bin)
    x=@variable(m,[1:n],lower_bound=0.,upper_bound=2.)
    w=@variable(m,[1:n],lower_bound=0.,upper_bound=2.)
    for i in 1:n
        j=mod1(i+1,n)
        @constraint(m,x[i]>=u[i]*(1-u[j]))
        @constraint(m,x[i]>=0.4u[j])
        @constraint(m,x[i]<=(1+u[i])*y[i])
        @constraint(m,w[i]+x[i]==1+u[i])
        @constraint(m,(1+u[j])*x[i]<=1+u[i]+0.5u[j])
    end
    @objective(m,Min,sum(2y[i]+i/length(u)*x[i]+0.2w[i]+0.1u[i] for i in eachindex(u)))
end
function audit_factory(m,n)
    z=@variable(m,[1:n],Bin)
    return z,z,()->round.(Int,value.(z))
end
@testset "2–6 uncertainty bits: native versus reference CCG and independent exhaustive solves" begin
    rows=NamedTuple[]
    for n in 2:6
        points=[digits(k;base=2,pad=n) for k in 0:2^n-1]
        builder=u->begin m=RC.new_model(;seconds=20.);audit_block(m,u);m end
        values=Float64[]
        for b in points
            m=builder(b);optimize!(m)
            @test termination_status(m)==MOI.OPTIMAL
            push!(values,objective_value(m))
        end
        exact=maximum(values)
        domain=RC.UncertaintyDomain(()->points,length(points),"audit $n bits")
        reference=RC.solve_ccg(builder,domain;rtol=1e-7,max_iters=100)
        native=RC.solve_native_ccg(builder,m->audit_factory(m,n),audit_block,zeros(Int,n);
            optimizer=SCIP.Optimizer,scope=domain.scope,rtol=1e-7,max_iters=100,seconds=20.)
        @test reference.converged
        @test native.converged
        @test native.lower≈exact atol=1e-5
        @test native.upper≈exact atol=1e-5
        @test reference.lower≈exact atol=1e-5
        @test reference.upper≈exact atol=1e-5
        @test all(h.lower<=exact+1e-5 && h.upper>=exact-1e-5 for h in native.history)
        push!(rows,(;bits=n,scenarios=length(points),enumerated=exact,
            native_lower=native.lower,native_upper=native.upper,
            reference_lower=reference.lower,reference_upper=reference.upper,
            native_columns=length(native.columns)))
    end
    write_rows(joinpath(@__DIR__,"native_exhaustive_comparison.csv"),rows)
end

@testset "Disk costs and cuts cannot become certificates" begin
    original=joinpath(@__DIR__,"toy_results","certified_policy.toml")
    doc=TOML.parsefile(original)
    for stage in values(doc["stages"])
        for sample in stage["samples"];sample["value"]=-1e15;sample["scope"]="forged";end
        for cut in stage["cuts"];cut["intercept"]=1e15;cut["slope"].=1e15;end
    end
    # حتی scope یکسان هم اعداد و برش‌های ویرایش‌شده را معتبر نمی‌کند.
    doc["root_scope"]=toy.scope(1)
    path=joinpath(@__DIR__,"toy_results","tampered_test_only.toml")
    open(path,"w") do io;TOML.print(io,doc);end
    imported=load_policy(path,toy)
    @test imported isa UnverifiedPolicyImport
    @test_throws MethodError planning_oracle(toy,imported,1,0,:upper)
    @test_throws MethodError planning_decision(toy,imported,1,0,0.;direction=:upper)
    checked=revalidate_policy(toy,imported;seconds=20.,rtol=1e-8,
        output_dir=joinpath(@__DIR__,"toy_results"))
    @test checked.verified
    @test checked.upper≈2. atol=1e-6
    @test all(isempty,checked.archive.cuts)
    @test all(s.value>=0 for stage in checked.archive.upper for s in values(stage))
    @test any(!isempty,checked.archive.responders)
    doc["stages"]["1"]["samples"][1]["bits"]=[2]
    open(path,"w") do io;TOML.print(io,doc);end
    @test_throws ErrorException load_policy(path,toy)
end

@testset "Signed indicator products and an actual SCIP time limit" begin
    for constant in (-7.,0.,7.),bit in (0,1)
        m=Model(SCIP.Optimizer);set_silent(m)
        z=@variable(m,binary=true);lambda=@variable(m)
        product=RC.indicator_product!(m,z,lambda,Dict())
        @constraint(m,lambda==constant);fix(z,bit;force=true)
        @objective(m,Min,product);optimize!(m)
        @test termination_status(m)==MOI.OPTIMAL
        @test value(product)≈bit*constant atol=1e-7
    end
    m=RC.new_model();audit_block(m,zeros(Int,4));optimize!(m)
    columns=[RC.integer_pattern(m)]
    fm,_=RC.symbolic_master(columns,m->audit_factory(m,4),audit_block,SCIP.Optimizer;
        ray=true,seconds=1e-9)
    optimize!(fm)
    @test termination_status(fm)==MOI.TIME_LIMIT
    feasible=has_values(fm)&&primal_status(fm)==MOI.FEASIBLE_POINT
    incumbent=feasible ? objective_value(fm) : NaN
    bound=try objective_bound(fm) catch; Inf end
    @test RC.farkas_gate(termination_status(fm),feasible,incumbent,bound)!=:covered
end

@testset "Portfolio fallback, nonanticipation, failures, and explicit seeded sampling" begin
    imported=load_policy(joinpath(@__DIR__,"toy_results","certified_policy.toml"),toy)
    checked=revalidate_policy(toy,imported;seconds=20.,rtol=1e-8)
    a=checked.archive
    paths=[[0.,u,v] for u in (0.,1.) for v in (0.,1.)]
    ev=evaluate_policy(toy,a,paths;response_order=:portfolio_only,seconds=20.)
    @test ev.summary.failed==0
    @test ev.summary.portfolio_lp_successes==12
    @test ev.summary.unconditional_mean<=checked.upper+1e-6
    @test all(s.method=="portfolio_lp" for s in ev.stage_rows)
    # یک ستون ناممکن ابتدا آزموده می‌شود؛ ستون بعدی باید پاسخ بودجه‌پذیر بدهد.
    key=RC.binary_key(toy.encode(toy.initial))
    pat=first(a.responders[1][key])
    bad=RC.IntegerPattern(copy(pat.indices),1 .- pat.values)
    pushfirst!(a.responders[1][key],bad)
    d=planning_decision(toy,a,1,0,0.;direction=:upper,response_order=:portfolio_only)
    @test d.feasible
    @test length(d.attempts)==2
    @test !first(d.attempts).accepted
    # حذف همه پاسخ‌ها با حالت portfolio_only باید شکست صریح و میانگین نامتناهی بدهد.
    broken=deepcopy(a);empty!(broken.responders[1][key])
    failed=evaluate_policy(toy,broken,paths;response_order=:portfolio_only)
    @test failed.summary.failed==4
    @test failed.summary.failure_rate==1.
    @test failed.summary.unconditional_mean==Inf
    @test isnan(failed.summary.conditional_mean)
    sampler=(rng,i)->[0.,Float64(rand(rng,Bool)),Float64(rand(rng,Bool))]
    one=evaluate_sampled_policy(toy,a,sampler;count=20,seed=42,
        distribution_label="explicit test-only independent Bernoulli(0.5)",response_order=:portfolio_only)
    two=evaluate_sampled_policy(toy,a,sampler;count=20,seed=42,
        distribution_label="explicit test-only independent Bernoulli(0.5)",response_order=:portfolio_only)
    @test [r.cost for r in one.rows]==[r.cost for r in two.rows]
    @test !one.sampling.paper_distribution_claim
    @test one.summary.failed==0
end

@testset "Codebook effect is an upper restriction; global bound covers every tiny state" begin
    target="audit codebook"
    exact=b->RC.CCGResult(3sum(b),3sum(b),true,false,nothing,RC.IntegerPattern[],NamedTuple[],target,:exact,:exact)
    global_cert=RC.certify_full_binary_upper(3,exact)
    allbits=[digits(k;base=2,pad=3) for k in 0:7]
    for b in allbits
        m=RC.new_model();x=@variable(m,[1:3],Bin);v=@variable(m,lower_bound=0.)
        RC.attach_upper!(m,x,v,[RC.UpperSample([0,0,0],exact([0,0,0]))],global_cert)
        for (z,k) in zip(x,b);fix(z,k;force=true);end
        @objective(m,Min,v);optimize!(m)
        @test termination_status(m)==MOI.OPTIMAL
        @test objective_value(m)>=3sum(b)-1e-6
    end
    function restricted_value(book)
        m=RC.new_model();x=@variable(m,[1:3],Bin);v=@variable(m,lower_bound=0.)
        samples=[RC.UpperSample(b,exact(b)) for b in book]
        cert=RC.DomainUpperCertificate(book,maximum(s.value for s in samples),target)
        RC.attach_upper!(m,x,v,samples,cert)
        @objective(m,Min,10sum(1-x[i] for i in 1:3)+v);optimize!(m)
        objective_value(m)
    end
    @test restricted_value([[0,0,0]])≈30.
    @test restricted_value([[0,0,0],[1,1,1]])≈9.
    @test restricted_value(allbits)≈9.
end

@testset "Finite-resolution capacity error and physical state decoding" begin
    # مقدار پیوستهٔ مثال ۰٫۳۷ است؛ شبکه‌های تو در تو به آن نزدیک می‌شوند.
    rows=NamedTuple[]
    for h in (0.5,0.25,0.1,0.05,0.01)
        m=RC.new_model();g=RC.BinaryGrid(0.,1.,h);b,x=RC.grid_variables!(m,g)
        @constraint(m,x>=0.37);@objective(m,Min,x);optimize!(m)
        @test termination_status(m)==MOI.OPTIMAL
        @test 0.37-1e-8<=objective_value(m)<0.37+h+1e-8
        push!(rows,(;step=h,continuous_optimum=0.37,grid_optimum=objective_value(m),
            total_error_bound=objective_value(m)-0.37))
    end
    write_rows(joinpath(@__DIR__,"toy_capacity_sensitivity.csv"),rows)
    for h in ((100.,40.,60.),(50.,20.,30.),(20.,10.,15.))
        g=state_grids(charging_kw=h[1],storage_kwh=h[2],pv_kw=h[3])
        p=physical_problem(g;capacity_mode=:installed_capacity)
        b=p.encode(p.initial)
        @test p.encode(p.decode(b))==b
        @test_throws ErrorException p.decode(b[1:end-1])
        onlyroot=ContinuousLowerBound(0.,1,continuous_scope(:installed_capacity),"test",true)
        @test_throws ErrorException capacity_error_bound(g,PlanningArchive(3),onlyroot;capacity_mode=:installed_capacity)
    end
end
