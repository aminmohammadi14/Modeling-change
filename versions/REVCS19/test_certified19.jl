using Test
include(joinpath(@__DIR__,"revcs_planning19.jl"))
const C=REVCSCertifiedCore
domain(values;scope="toy exact problem")=C.UncertaintyDomain(()->values,length(values),scope)

@testset "Binary state representation with explicit precision" begin
    g=C.BinaryGrid(0,10,2)
    @test length(g.weights)==3
    for x in 0:2:10
        @test C.decode(g,C.encode(g,x))==x
    end
    @test_throws ErrorException C.encode(g,3)
    @test_throws ErrorException C.decode(g,[1,1,1])
    @test_throws ErrorException C.BinaryGrid(0,10,3)
    @test_throws ErrorException C.BinaryGrid(0,10,0)
    m=C.new_model()
    b,x=C.grid_variables!(m,g)
    @constraint(m,x>=9)
    @objective(m,Min,x)
    optimize!(m)
    @test objective_value(m)≈10
    @test all(is_binary,b)
    # Thousands of operational binaries must not create giant tuple TYPES.
    large=C.IntegerPattern(collect(1:5000),zeros(Int,5000))
    @test C.pattern_key(large) isa String
    @test length(Set([C.pattern_key(large),C.pattern_key(large)]))==1
end

function recourse(u)
    m=C.new_model()
    @variable(m,y,Bin)
    @variable(m,0<=x<=1)
    @constraint(m,x>=u)
    @constraint(m,x<=y)
    @objective(m,Min,y)
    return m
end

@testset "Recourse-column C&CG versus complete enumeration" begin
    d=domain([0.,1.])
    exact=Float64[]
    for u in d.factory()
        m=recourse(u);optimize!(m)
        push!(exact,objective_value(m))
    end
    r=C.solve_ccg(recourse,d;rtol=1e-8)
    @test r.converged
    @test r.lower≈maximum(exact)
    @test r.upper≈maximum(exact)
    @test length(r.columns)==2
    @test length(r.history)==2
    @test all(h.lower<=maximum(exact)+1e-7<=h.upper+1e-7 for h in r.history)
    @test all(h.master_complete for h in r.history)
    truncated=C.solve_ccg(recourse,d;max_master_scenarios=1)
    @test !truncated.converged
    @test truncated.upper==Inf
    @test truncated.reason==:master_scan_budget
    @test !truncated.history[end].master_complete
    @test_throws ErrorException C.solve_ccg(recourse,C.UncertaintyDomain(()->[0.],2,"wrong count"))
    # State-independent columns but an interior worst uncertainty point.
    f=u->begin
        m=C.new_model();@variable(m,x>=2-abs(u));@objective(m,Min,x);m
    end
    r2=C.solve_ccg(f,domain([-1.,0.,1.]);rtol=1e-8)
    @test r2.converged && r2.lower≈2 && r2.upper≈2
end

@testset "Pattern fixing preserves uncertainty-dependent bounds" begin
    builder=u->begin
        m=C.new_model();@variable(m,y,Bin)
        set_upper_bound(y,u)
        @constraint(m,y>=u)
        @objective(m,Min,2-y)
        m
    end
    r=C.solve_ccg(builder,domain([1.,0.]);rtol=1e-8)
    @test r.converged
    @test r.lower≈2 && r.upper≈2
    @test length(r.columns)==2
end

@testset "Infeasibility is not an artificial penalty" begin
    builder=u->begin
        m=C.new_model();@variable(m,0<=x<=1);@constraint(m,x>=u);@objective(m,Min,x);m
    end
    r=C.solve_ccg(builder,domain([0.,2.]);rtol=1e-8)
    @test r.infeasible
    @test !r.converged
    @test r.lower==Inf && r.upper==Inf
end

function binary_recourse()
    m=C.new_model()
    @variable(m,b[1:2],Bin)
    @variable(m,y,Bin)
    @constraint(m,y>=(b[1]+b[2])/2)
    @objective(m,Min,5y)
    return m,b
end
const points=[[0,0],[0,1],[1,0],[1,1]]
@testset "Integer Lagrangian level dual in binary space" begin
    for anchor in points
        c=C.lagrangian_cut(binary_recourse,anchor;rtol=1e-7,max_iters=60)
        exact=anchor==[0,0] ? 0. : 5.
        @test c.converged
        @test c.anchor_lower≈exact atol=1e-6
        for b in points
            q=b==[0,0] ? 0. : 5.
            @test c.intercept+dot(c.slope,b)<=q+1e-6
        end
    end
    @test_throws ErrorException C.lagrangian_cut(binary_recourse,[0.5,1.])
end

function future_value(b;role=:exact,scope="future Q")
    builder=u->begin
        m=C.new_model();@variable(m,y,Bin)
        @constraint(m,y>=(b[1]+b[2])/2)
        @objective(m,Min,5y+u*(2-b[1]))
        m
    end
    return C.solve_ccg(builder,domain([0.,1.];scope);rtol=1e-8,bound_role=role)
end

@testset "Certified Eq61 upper envelope and provenance" begin
    results=[future_value(b) for b in points]
    cert=C.certify_upper_domain(points,future_value)
    @test cert.bound≈7
    samples=[C.UpperSample(points[1],results[1]),C.UpperSample(points[2],results[2])]
    function hull_value(b,samples,certificate)
        m=C.new_model();@variable(m,x[1:2],Bin);@variable(m,alpha>=0)
        data=C.attach_upper!(m,x,alpha,samples,certificate)
        for (v,k) in zip(x,b);fix(v,k;force=true);end
        @objective(m,Min,alpha);optimize!(m)
        return objective_value(m),data.penalty
    end
    for (b,r) in zip(points,results)
        val,penalty=hull_value(b,samples,cert)
        @test val>=r.upper-1e-7
        @test penalty≈cert.bound-minimum(s.value for s in samples)
    end
    all_samples=[C.UpperSample(b,r) for (b,r) in zip(points,results)]
    for (b,r) in zip(points,results)
        val,_=hull_value(b,all_samples,cert)
        @test val≈r.upper
    end
    @test_throws ErrorException C.UpperSample([0,0],future_value([0,0];role=:lower))
    @test_throws ErrorException C.certify_upper_domain(points,b->future_value(b;role=:lower))
    low=future_value([0,0];role=:lower)
    up=future_value([0,0];role=:upper)
    @test C.certified_gap(low,up).converged
    @test_throws ErrorException C.certified_gap(up,low)
    @test_throws ErrorException C.certified_gap(low,future_value([0,0];scope="other target"))
    @test_throws ErrorException C.certify_upper_domain(points,future_value;max_states=2)
    bad=[C.UpperSample([0,0],future_value([0,0];scope="other target"))]
    @test_throws ErrorException hull_value([0,0],bad,cert)
    # A domain certificate over a subset is enforced, never extrapolated.
    small_cert=C.certify_upper_domain(points[1:2],future_value)
    m=C.new_model();@variable(m,x[1:2],Bin);@variable(m,a>=0)
    C.attach_upper!(m,x,a,samples,small_cert)
    fix(x[1],1.;force=true);fix(x[2],0.;force=true)
    @objective(m,Min,a);optimize!(m)
    @test termination_status(m)==MOI.INFEASIBLE
end

@testset "Full uncertainty representation and physical-state integration" begin
    d=full_uncertainty_domain(2)
    @test d.cardinality==big(3)^1882
    it=d.factory()
    first,st=iterate(it);second,_=iterate(it,st)
    @test validate_scenario(2,first)
    @test validate_scenario(2,second)
    @test first["theta_t"]!=second["theta_t"]
    @test first["zeta_t"]==second["zeta_t"]
    grids=state_grids(charging_kw=100.,storage_kwh=40.,pv_kw=60.)
    prev=StageState(Float64.(existing_REVCS),existing_REVCS.*Cc_0,
        existing_REVCS.*Ce_0,existing_REVCS.*Cv_0)
    anchor=encode_state(prev,grids)
    @test length(anchor)==220
    @test_throws ErrorException build_certified_stage(2,prev,first,grids;direction=:upper)
    wrong=C.BinaryCut(0.0,zeros(length(anchor)),0.0,0.0,true,"wrong future scope")
    @test_throws ErrorException build_certified_stage(1,prev,first,grids;lower_cuts=[wrong])
    m,beta=binary_predecessor_builder(2,prev,first,grids)
    @test length(beta)==length(anchor)
    @test all(is_binary,beta)
    @test num_variables(m)>length(beta)
end
