using Test
include(joinpath(@__DIR__,"revcs_planning19.jl"))
const P=REVCSCertifiedCore

@testset "Symbolic extraction of actual 96-hour REVCS constraints" begin
    grids=state_grids(charging_kw=100.,storage_kwh=40.,pv_kw=60.)
    prev=StageState(Float64.(existing_REVCS),existing_REVCS.*Cc_0,
        existing_REVCS.*Ce_0,existing_REVCS.*Cv_0)
    pm=Model()
    z,unc,_=symbolic_uncertainty(pm,2)
    snapshot=Set(all_constraints(pm;include_variable_in_set_constraints=true))
    m,v=build_certified_stage(2,prev,unc,grids;shared_model=pm)
    @test m===pm
    @test length(z)==3764
    uset=Set(z)
    primal=filter(x->!(x in uset),all_variables(pm))
    iv=filter(x->is_binary(x)||is_integer(x),primal)
    ints=Dict(x=>0 for x in iv)
    cont=Set(filter(x->!haskey(ints,x),primal))
    ui=Dict(x=>i for (i,x) in enumerate(z))
    # Algebraic test assignments, not power-system input data or fabricated
    # solutions. No feasibility or optimality claim is made for these points.
    assignment=Dict(x=>(isodd(i) ? 0.0 : 1.0) for (i,x) in enumerate(z))
    merge!(assignment,Dict(x=>Float64(k) for (x,k) in ints))
    merge!(assignment,Dict(x=>0.25 for x in cont))
    evalpoly(p)=sum(a*prod(assignment[z[i]] for i in key;init=1.0) for (key,a) in p;init=0.0)
    rows=0;matrix_uncertainty=0;quadratic_uncertainty=0
    for con in all_constraints(pm;include_variable_in_set_constraints=true)
        con in snapshot && continue
        obj=constraint_object(con)
        obj.set isa MOI.ZeroOne && continue
        obj.set isa MOI.Integer && continue
        off,A=P.split_parametric_expression(obj.func,ui,ints,cont)
        reconstructed=evalpoly(off)+sum(evalpoly(a)*assignment[x] for (x,a) in A;init=0.0)
        raw=obj.func isa VariableRef ? assignment[obj.func] : obj.func isa Number ? Float64(obj.func) : value(x->assignment[x],obj.func)
        @test isapprox(reconstructed,raw;atol=1e-7,rtol=1e-9)
        rows+=1
        any(any(!isempty(key)&&a!=0 for (key,a) in p) for p in values(A)) && (matrix_uncertainty+=1)
        any(length(key)==2&&a!=0 for (key,a) in off) && (quadratic_uncertainty+=1)
    end
    @test rows>10000
    @test matrix_uncertainty>0
    @test quadratic_uncertainty>0
    @test length(v["state_bits"])==220
    println("ACTUAL_PHYSICAL_ROWS=",rows)
    println("UNCERTAIN_MATRIX_ROWS=",matrix_uncertainty)
    println("QUADRATIC_UNCERTAINTY_ROWS=",quadratic_uncertainty)
end
