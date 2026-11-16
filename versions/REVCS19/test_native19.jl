using Test, JuMP, HiGHS, SCIP
import MathOptInterface as MOI
include(joinpath(@__DIR__,"revcs_planning19.jl"))
const N=REVCSCertifiedCore

function one_binary_uncertainty(m)
    z=@variable(m,binary=true)
    return [z],z,()->Float64(round(value(z)))
end
function two_binary_uncertainty(m)
    z=@variable(m,[1:2],Bin)
    return z,(z[1],z[2]),()->(Float64(round(value(z[1]))),Float64(round(value(z[2]))))
end

function coverage_block(m,u)
    @variable(m,y,Bin)
    @variable(m,0<=x<=1)
    @constraint(m,x>=u)
    @constraint(m,x<=y)
    @objective(m,Min,y)
end
coverage=u->begin m=N.new_model();coverage_block(m,u);m;end

@testset "Native indicator products with unbounded dual variables" begin
    m=Model(SCIP.Optimizer);set_silent(m)
    @variable(m,z,Bin);@variable(m,lambda)
    w=N.indicator_product!(m,z,lambda,Dict())
    fix(z,1.;force=true);@constraint(m,lambda==7)
    @objective(m,Min,w);optimize!(m)
    @test termination_status(m)==MOI.OPTIMAL
    @test value(w)≈7
    unfix(z);fix(z,0.;force=true);optimize!(m)
    @test value(w)≈0
end

@testset "Farkas and optimality masters versus enumeration" begin
    result=N.solve_native_ccg(coverage,one_binary_uncertainty,coverage_block,0.;
        optimizer=SCIP.Optimizer,scope="native coverage",rtol=1e-8,seconds=30.)
    @test result.converged
    @test result.lower≈1 && result.upper≈1
    @test length(result.columns)==2
    @test any(h.phase==:feasibility for h in result.history)
    @test any(h.phase==:optimality for h in result.history)
    @test all(h.lower<=1+1e-7<=h.upper+1e-7 for h in result.history)
end

function matrix_block(m,u)
    @variable(m,0<=x<=2)
    @constraint(m,(1+u)*x>=1)
    @objective(m,Min,x)
end
matrix_builder=u->begin m=N.new_model();matrix_block(m,u);m;end
@testset "Uncertainty in recourse matrix, not only RHS" begin
    r=N.solve_native_ccg(matrix_builder,one_binary_uncertainty,matrix_block,1.;
        optimizer=SCIP.Optimizer,scope="uncertain matrix",rtol=1e-8,seconds=30.)
    @test r.converged
    @test r.lower≈1 && r.upper≈1
    @test r.scenario≈0
end

function quadratic_rhs_block(m,u)
    @variable(m,0<=x<=4)
    @constraint(m,x>=(1+u[1])*(1+u[2]))
    @objective(m,Min,x)
end
quadratic_builder=u->begin m=N.new_model();quadratic_rhs_block(m,u);m;end
@testset "Eq53 binary products and symbolic dual RHS" begin
    r=N.solve_native_ccg(quadratic_builder,two_binary_uncertainty,quadratic_rhs_block,(0.,0.);
        optimizer=SCIP.Optimizer,scope="quadratic RHS",rtol=1e-8,seconds=30.)
    @test r.converged
    @test r.lower≈4 && r.upper≈4
    @test r.scenario==(1.,1.)
    vals=Float64[]
    for i in (0.,1.),j in (0.,1.)
        m=quadratic_builder((i,j));optimize!(m);push!(vals,objective_value(m))
    end
    @test r.lower≈maximum(vals)
end

@testset "Complete Eq61 -> integer recourse -> native adversary chain" begin
    states=[[0],[1]]
    function future(b)
        builder=u->begin
            m=N.new_model();@variable(m,x>=3b[1]);@objective(m,Min,x);m
        end
        N.solve_ccg(builder,N.UncertaintyDomain(()->(0.,),1,"future one-bit Q");rtol=1e-8)
    end
    cert=N.certify_upper_domain(states,future)
    samples=[N.UpperSample(b,future(b)) for b in states]
    function block(m,u)
        @variable(m,b,Bin);@variable(m,x>=0);@variable(m,alpha>=0)
        @constraint(m,x>=10*(1+u)*(1-b))
        N.attach_upper!(m,[b],alpha,samples,cert)
        @objective(m,Min,b+x+alpha)
    end
    builder=u->begin m=N.new_model();block(m,u);m;end
    r=N.solve_native_ccg(builder,one_binary_uncertainty,block,0.;
        optimizer=SCIP.Optimizer,scope="combined upper stage",bound_role=:upper,rtol=1e-8,seconds=30.)
    @test r.converged
    @test r.lower≈4 && r.upper≈4
    sample=N.UpperSample([1],r)
    @test sample.value≈4
end

@testset "Constant recourse and empty dual-column rows" begin
    function block(m,u)
        @objective(m,Min,1+u)
    end
    builder=u->begin m=N.new_model();block(m,u);m;end
    r=N.solve_native_ccg(builder,one_binary_uncertainty,block,0.;
        optimizer=SCIP.Optimizer,scope="constant recourse",rtol=1e-8,seconds=30.)
    @test r.converged
    @test r.lower≈2 && r.upper≈2
end

@testset "Native infeasible and unbounded responses are not finite costs" begin
    function infeasible_block(m,u)
        @variable(m,0<=x<=0)
        @constraint(m,x>=u)
        @objective(m,Min,x)
    end
    builder=u->begin m=N.new_model();infeasible_block(m,u);m;end
    r=N.solve_native_ccg(builder,one_binary_uncertainty,infeasible_block,0.;
        optimizer=SCIP.Optimizer,scope="infeasible test",seconds=20.)
    @test r.infeasible
    @test r.lower==Inf && r.upper==Inf
    @test r.reason==:robust_infeasible
    m=N.new_model();@variable(m,x>=0);@objective(m,Min,-x);optimize!(m)
    @test_throws ErrorException N.min_bounds(m)
end
